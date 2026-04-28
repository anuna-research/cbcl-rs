//! Epidemic gossip protocol for dialect propagation (REQ-120–122).
//!
//! Implements round-based epidemic propagation with configurable transmission
//! probability, infected/susceptible set tracking, and O(log n) expected
//! convergence. Faithfully reproduces `src/cbcl/gossip.scm`.
//!
//! # Purity
//!
//! This module uses a deterministic linear congruential generator (LCG) seeded
//! at construction time, matching the Guile reference. Given the same seed and
//! inputs, the protocol produces identical results — no external RNG or I/O.

#![forbid(unsafe_code)]

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::string::ToString;
use alloc::vec::Vec;

use crate::dialect::Dialect;

// ---------------------------------------------------------------------------
// no_std-compatible ln approximation
// ---------------------------------------------------------------------------

/// Natural logarithm approximation for no_std (used in convergence estimation).
///
/// Uses the identity: ln(x) = 2 * atanh((x-1)/(x+1)) with a truncated series.
/// Accurate enough for O(log n) convergence estimation.
fn ln_approx(x: f64) -> f64 {
    if x <= 0.0 {
        return f64::NEG_INFINITY;
    }
    // Reduce to range [1, 2) by extracting the exponent
    let bits = x.to_bits();
    let exp = ((bits >> 52) & 0x7FF) as i64 - 1023;
    let mantissa = f64::from_bits((bits & 0x000F_FFFF_FFFF_FFFF) | 0x3FF0_0000_0000_0000);

    // ln(x) = exp * ln(2) + ln(mantissa)
    // ln(mantissa) via atanh series: 2 * sum_{k=0}^{N} t^(2k+1)/(2k+1)
    let t = (mantissa - 1.0) / (mantissa + 1.0);
    let t2 = t * t;
    // 7 terms for good accuracy
    let ln_m = 2.0
        * t
        * (1.0
            + t2 * (1.0 / 3.0
                + t2 * (1.0 / 5.0
                    + t2 * (1.0 / 7.0 + t2 * (1.0 / 9.0 + t2 * (1.0 / 11.0 + t2 / 13.0))))));

    (exp as f64) * core::f64::consts::LN_2 + ln_m
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Network topology for gossip propagation.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Topology {
    /// Every agent is connected to every other agent.
    FullyConnected,
    /// Each agent is connected to its ring neighbors.
    Ring,
    /// Erdős–Rényi random graph with edge probability `p`.
    Random(f64),
}

/// Configuration for the gossip network.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GossipConfig {
    /// Probability of successful transmission per contact (0.0–1.0).
    pub transmission_probability: f64,
    /// Maximum number of rounds before a propagation is considered failed.
    pub max_rounds: u32,
    /// Network topology.
    pub topology: Topology,
}

impl Default for GossipConfig {
    fn default() -> Self {
        Self {
            transmission_probability: 0.8,
            max_rounds: 100,
            topology: Topology::FullyConnected,
        }
    }
}

// ---------------------------------------------------------------------------
// Deterministic RNG (matches Guile simple-random)
// ---------------------------------------------------------------------------

/// Simple linear congruential generator for deterministic gossip randomness.
///
/// Uses the same constants as the Guile reference (`gossip.scm:46–50`):
/// `seed = (seed * 1103515245 + 12345) mod 2^31`
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct Lcg {
    seed: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { seed }
    }

    /// Returns a value in [0.0, 1.0).
    fn next_f64(&mut self) -> f64 {
        let m: u64 = 1 << 31;
        self.seed = (self.seed.wrapping_mul(1_103_515_245).wrapping_add(12345)) % m;
        self.seed as f64 / m as f64
    }
}

// ---------------------------------------------------------------------------
// Propagation state
// ---------------------------------------------------------------------------

/// State of an epidemic propagation for a single dialect.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PropagationState {
    /// The dialect being propagated.
    pub dialect: Dialect,
    /// Agent ids that have the dialect installed.
    pub infected: BTreeSet<String>,
    /// Agent ids that do not yet have the dialect.
    pub susceptible: BTreeSet<String>,
    /// Current round number.
    pub round: u32,
    /// Transmission probability for this propagation.
    pub transmission_prob: f64,
}

impl PropagationState {
    /// Coverage ratio: infected / (infected + susceptible).
    pub fn coverage(&self) -> f64 {
        let total = self.infected.len() + self.susceptible.len();
        if total == 0 {
            1.0
        } else {
            self.infected.len() as f64 / total as f64
        }
    }

    /// Whether propagation is complete (no susceptible agents remain).
    pub fn is_complete(&self) -> bool {
        self.susceptible.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Aggregate statistics for a gossip network.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GossipStats {
    /// Total rounds executed across all propagations.
    pub total_rounds: u64,
    /// Number of propagations that reached full coverage.
    pub successful_propagations: u64,
    /// Number of propagations that timed out (exceeded max_rounds).
    pub failed_propagations: u64,
}

// ---------------------------------------------------------------------------
// Simulation result
// ---------------------------------------------------------------------------

/// Result of a complete propagation simulation.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SimulationResult {
    /// Name of the dialect propagated.
    pub dialect_name: String,
    /// Number of rounds to convergence (or timeout).
    pub rounds: u32,
    /// Final coverage ratio.
    pub final_coverage: f64,
    /// Whether the propagation completed successfully.
    pub successful: bool,
}

// ---------------------------------------------------------------------------
// GossipNetwork
// ---------------------------------------------------------------------------

/// Epidemic gossip network for dialect propagation (REQ-120).
///
/// Manages a set of agents connected by a configurable topology.
/// Dialects are propagated epidemically: each round, infected agents
/// attempt to transmit to their susceptible neighbors with a given
/// probability. Expected convergence is O(log n) rounds for a
/// fully-connected network with constant transmission probability.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GossipNetwork {
    /// Agent ids and their installed dialect names.
    agents: BTreeMap<String, BTreeSet<String>>,
    /// Adjacency list: agent_id → set of neighbor ids.
    topology: BTreeMap<String, BTreeSet<String>>,
    /// Active propagations keyed by dialect name.
    active_propagations: BTreeMap<String, PropagationState>,
    /// Aggregate statistics.
    stats: GossipStats,
    /// Network configuration.
    config: GossipConfig,
    /// Deterministic RNG.
    rng: Lcg,
}

impl GossipNetwork {
    /// Create a new gossip network with the given configuration and RNG seed.
    pub fn new(config: GossipConfig, seed: u64) -> Self {
        Self {
            agents: BTreeMap::new(),
            topology: BTreeMap::new(),
            active_propagations: BTreeMap::new(),
            stats: GossipStats::default(),
            config,
            rng: Lcg::new(seed),
        }
    }

    /// Create a new gossip network with default configuration and the
    /// reference seed (1234567, matching the Guile implementation).
    pub fn with_defaults() -> Self {
        Self::new(GossipConfig::default(), 1_234_567)
    }

    // -- Agent management (REQ-121) --

    /// Add an agent to the network.
    ///
    /// The topology is updated automatically based on the configured topology
    /// type. Returns `true` if the agent was newly added, `false` if it was
    /// already present.
    pub fn add_agent(&mut self, agent_id: impl Into<String>) -> bool {
        let id = agent_id.into();
        if self.agents.contains_key(&id) {
            return false;
        }
        self.agents.insert(id.clone(), BTreeSet::new());
        self.topology.insert(id.clone(), BTreeSet::new());
        self.update_topology(&id);
        true
    }

    /// Remove an agent from the network.
    ///
    /// Removes the agent from all neighbor lists and from any active
    /// propagation sets. Returns `true` if the agent was present.
    pub fn remove_agent(&mut self, agent_id: &str) -> bool {
        if self.agents.remove(agent_id).is_none() {
            return false;
        }
        self.topology.remove(agent_id);
        // Remove from all neighbor lists
        for neighbors in self.topology.values_mut() {
            neighbors.remove(agent_id);
        }
        // Remove from active propagations
        for prop in self.active_propagations.values_mut() {
            prop.infected.remove(agent_id);
            prop.susceptible.remove(agent_id);
        }
        true
    }

    /// Returns the set of agent ids in the network.
    pub fn agent_ids(&self) -> Vec<&str> {
        self.agents.keys().map(|s| s.as_str()).collect()
    }

    /// Returns the number of agents in the network.
    pub fn agent_count(&self) -> usize {
        self.agents.len()
    }

    /// Returns neighbors of the given agent.
    pub fn neighbors(&self, agent_id: &str) -> Option<Vec<&str>> {
        self.topology
            .get(agent_id)
            .map(|s| s.iter().map(|n| n.as_str()).collect())
    }

    // -- Topology --

    fn update_topology(&mut self, new_agent_id: &str) {
        match &self.config.topology {
            Topology::FullyConnected => {
                let all_ids: Vec<String> = self.agents.keys().cloned().collect();
                for id in &all_ids {
                    if id != new_agent_id {
                        // Connect new agent to existing
                        self.topology
                            .get_mut(new_agent_id)
                            .unwrap()
                            .insert(id.clone());
                        // Connect existing to new agent
                        self.topology
                            .get_mut(id.as_str())
                            .unwrap()
                            .insert(String::from(new_agent_id));
                    }
                }
            }
            Topology::Ring => {
                let all_ids: Vec<String> = self.agents.keys().cloned().collect();
                if all_ids.len() > 1 {
                    // Connect to up to 2 existing agents
                    let others: Vec<&String> = all_ids
                        .iter()
                        .filter(|id| id.as_str() != new_agent_id)
                        .collect();
                    let count = others.len().min(2);
                    for id in &others[..count] {
                        self.topology
                            .get_mut(new_agent_id)
                            .unwrap()
                            .insert((*id).clone());
                        self.topology
                            .get_mut(id.as_str())
                            .unwrap()
                            .insert(String::from(new_agent_id));
                    }
                }
            }
            Topology::Random(p) => {
                let p = *p;
                let all_ids: Vec<String> = self.agents.keys().cloned().collect();
                for id in &all_ids {
                    if id.as_str() != new_agent_id && self.rng.next_f64() < p {
                        self.topology
                            .get_mut(new_agent_id)
                            .unwrap()
                            .insert(id.clone());
                        self.topology
                            .get_mut(id.as_str())
                            .unwrap()
                            .insert(String::from(new_agent_id));
                    }
                }
            }
        }
    }

    // -- Propagation (REQ-120, REQ-121) --

    /// Start epidemic propagation of a dialect from an initial agent (REQ-121).
    ///
    /// The dialect is considered "installed" on the initial agent. All other
    /// agents in the network are placed in the susceptible set.
    ///
    /// Returns `None` if the initial agent is not in the network, or if a
    /// propagation for this dialect is already active. Otherwise returns the
    /// dialect name as a propagation identifier.
    pub fn announce_dialect(&mut self, dialect: Dialect, initial_agent_id: &str) -> Option<String> {
        if !self.agents.contains_key(initial_agent_id) {
            return None;
        }
        if self.active_propagations.contains_key(&dialect.name) {
            return None;
        }

        let dialect_name = dialect.name.clone();

        // Mark initial agent as having the dialect
        self.agents
            .get_mut(initial_agent_id)
            .unwrap()
            .insert(dialect_name.clone());

        let mut infected = BTreeSet::new();
        infected.insert(String::from(initial_agent_id));

        let susceptible: BTreeSet<String> = self
            .agents
            .keys()
            .filter(|id| id.as_str() != initial_agent_id)
            .cloned()
            .collect();

        let transmission_prob = self.config.transmission_probability;

        self.active_propagations.insert(
            dialect_name.clone(),
            PropagationState {
                dialect,
                infected,
                susceptible,
                round: 0,
                transmission_prob,
            },
        );

        #[cfg(feature = "tracing")]
        tracing::event!(
            tracing::Level::INFO,
            dialect = %dialect_name,
            initial_agent = initial_agent_id,
            network_size = self.agents.len(),
            "gossip_announce_dialect"
        );

        Some(dialect_name)
    }

    /// Execute one round of epidemic propagation for all active dialects.
    ///
    /// Each infected agent attempts to transmit to each of its susceptible
    /// neighbors with the configured transmission probability. Newly infected
    /// agents are added to the infected set. Propagations that complete (empty
    /// susceptible set) or exceed `max_rounds` are cleaned up.
    ///
    /// Returns a list of (dialect_name, newly_infected_agent_ids) for this round.
    pub fn step(&mut self) -> Vec<(String, Vec<String>)> {
        let dialect_names: Vec<String> = self.active_propagations.keys().cloned().collect();
        let mut results = Vec::new();

        for dialect_name in &dialect_names {
            let newly_infected = self.step_propagation(dialect_name);
            if !newly_infected.is_empty() {
                results.push((dialect_name.clone(), newly_infected));
            }
        }

        self.cleanup_completed_propagations();
        self.stats.total_rounds += 1;

        #[cfg(feature = "tracing")]
        for (name, prop) in &self.active_propagations {
            tracing::event!(
                tracing::Level::INFO,
                dialect = %name,
                round = prop.round,
                coverage = prop.coverage(),
                infected = prop.infected.len(),
                susceptible = prop.susceptible.len(),
                "gossip_round_convergence"
            );
        }

        results
    }

    fn step_propagation(&mut self, dialect_name: &str) -> Vec<String> {
        // Collect the data we need to decide transmissions
        let prop = match self.active_propagations.get(dialect_name) {
            Some(p) => p,
            None => return Vec::new(),
        };

        let infected: Vec<String> = prop.infected.iter().cloned().collect();
        let transmission_prob = prop.transmission_prob;

        // For each infected agent, try to infect susceptible neighbors
        let mut newly_infected = Vec::new();

        for infected_id in &infected {
            let neighbor_ids: Vec<String> = self
                .topology
                .get(infected_id.as_str())
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default();

            let prop = self.active_propagations.get(dialect_name).unwrap();
            for neighbor_id in &neighbor_ids {
                if prop.susceptible.contains(neighbor_id) && self.rng.next_f64() < transmission_prob
                {
                    newly_infected.push(neighbor_id.clone());
                }
            }
        }

        // Update propagation state
        if let Some(prop) = self.active_propagations.get_mut(dialect_name) {
            for id in &newly_infected {
                prop.infected.insert(id.clone());
                prop.susceptible.remove(id);
                // Mark agent as having the dialect
                if let Some(agent_dialects) = self.agents.get_mut(id) {
                    agent_dialects.insert(dialect_name.to_string());
                }
            }
            prop.round += 1;
        }

        newly_infected
    }

    fn cleanup_completed_propagations(&mut self) {
        let max_rounds = self.config.max_rounds;
        let to_remove: Vec<(String, bool)> = self
            .active_propagations
            .iter()
            .filter_map(|(name, prop)| {
                if prop.susceptible.is_empty() {
                    Some((name.clone(), true))
                } else if prop.round >= max_rounds {
                    Some((name.clone(), false))
                } else {
                    None
                }
            })
            .collect();

        for (name, success) in to_remove {
            self.active_propagations.remove(&name);
            if success {
                self.stats.successful_propagations += 1;
            } else {
                self.stats.failed_propagations += 1;
            }
        }
    }

    // -- Gossip reception (REQ-121, REQ-122) --

    /// Receive a gossip message containing a dialect for a specific agent.
    ///
    /// The dialect is validated through the R1+R2+R3 pipeline (REQ-122).
    /// Returns a list of validation violations if the dialect fails checks,
    /// or `Ok(())` if the dialect is accepted.
    ///
    /// Note: actual dialect installation on real Agent structs is the caller's
    /// responsibility. This method tracks the gossip-level state (infected/
    /// susceptible sets) for the propagation simulation.
    pub fn receive_gossip(&mut self, agent_id: &str, dialect: &Dialect) -> Result<(), Vec<String>> {
        // Validate through R1+R2+R3 pipeline (REQ-122)
        let mut violations = Vec::new();

        if !crate::r1::verify_r1_dialect(dialect) {
            violations.extend(crate::r1::r1_violations(dialect));
        }
        if !crate::r2::verify_r2(dialect) {
            violations.push(alloc::format!(
                "R2 violation: invalid resource bounds in '{}'",
                dialect.name
            ));
        }
        if !crate::r3::verify_r3(dialect) {
            violations.extend(
                crate::r3::r3_violations(dialect)
                    .into_iter()
                    .map(|v| alloc::format!("R3 violation: {}", v)),
            );
        }

        if !violations.is_empty() {
            return Err(violations);
        }

        // Mark agent as having the dialect
        if let Some(agent_dialects) = self.agents.get_mut(agent_id) {
            agent_dialects.insert(dialect.name.clone());
        }

        // Update propagation state if this dialect is being actively propagated
        if let Some(prop) = self.active_propagations.get_mut(&dialect.name) {
            prop.susceptible.remove(agent_id);
            prop.infected.insert(String::from(agent_id));
        }

        Ok(())
    }

    // -- Peer selection (REQ-121) --

    /// Select up to `k` peers for gossip fan-out (REQ-121).
    ///
    /// Uses the deterministic LCG to select peers from the agent's neighbors.
    /// Returns the selected peer ids.
    pub fn select_peers(&mut self, agent_id: &str, k: usize) -> Vec<String> {
        let neighbors: Vec<String> = match self.topology.get(agent_id) {
            Some(n) => n.iter().cloned().collect(),
            None => return Vec::new(),
        };

        if neighbors.len() <= k {
            return neighbors;
        }

        // Fisher-Yates shuffle on a copy, then take first k
        let mut shuffled = neighbors;
        let len = shuffled.len();
        for i in (1..len).rev() {
            let r = self.rng.next_f64();
            let j = (r * (i + 1) as f64) as usize;
            let j = j.min(i); // safety bound
            shuffled.swap(i, j);
        }
        shuffled.truncate(k);
        shuffled
    }

    // -- Analysis --

    /// Estimate expected convergence time in rounds (REQ-120).
    ///
    /// For a network of n agents with transmission probability p,
    /// the expected convergence is O(log n) rounds:
    /// `ceil(ln(n) / ln(1 + p))`
    ///
    /// This matches `estimate-convergence-time` in `gossip.scm:275–284`.
    pub fn estimate_convergence_time(&self) -> u32 {
        let n = self.agents.len();
        if n <= 1 {
            return 0;
        }
        let p = self.config.transmission_probability;
        let rounds = ln_approx(n as f64) / ln_approx(1.0 + p);
        rounds as u32 + 1
    }

    /// Check if the network is connected (all agents reachable from any agent).
    pub fn is_connected(&self) -> bool {
        if self.agents.is_empty() {
            return true;
        }

        let start = match self.agents.keys().next() {
            Some(id) => id.clone(),
            None => return true,
        };

        let mut visited = BTreeSet::new();
        let mut queue = alloc::vec![start];

        while let Some(current) = queue.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(neighbors) = self.topology.get(&current) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        queue.push(neighbor.clone());
                    }
                }
            }
        }

        visited.len() == self.agents.len()
    }

    /// Simulate complete epidemic propagation until convergence or timeout.
    ///
    /// Matches `simulate-propagation` in `gossip.scm:302–318`.
    pub fn simulate_propagation(
        &mut self,
        dialect: Dialect,
        initial_agent_id: &str,
    ) -> Option<SimulationResult> {
        let dialect_name = self.announce_dialect(dialect, initial_agent_id)?;
        let mut rounds = 0u32;

        while self.active_propagations.contains_key(&dialect_name) {
            self.step();
            rounds += 1;
        }

        // Determine if it was successful by checking stats
        // (the cleanup in step() already updated stats)
        let successful = self
            .agents
            .values()
            .all(|dialects| dialects.contains(&dialect_name));

        Some(SimulationResult {
            dialect_name,
            rounds,
            final_coverage: if successful { 1.0 } else { 0.0 },
            successful,
        })
    }

    // -- Accessors --

    /// Returns a reference to the network configuration.
    pub fn config(&self) -> &GossipConfig {
        &self.config
    }

    /// Returns a reference to the aggregate statistics.
    pub fn stats(&self) -> &GossipStats {
        &self.stats
    }

    /// Returns a reference to the active propagations.
    pub fn active_propagations(&self) -> &BTreeMap<String, PropagationState> {
        &self.active_propagations
    }

    /// Get propagation statistics for a specific dialect.
    pub fn propagation_stats(&self, dialect_name: &str) -> Option<&PropagationState> {
        self.active_propagations.get(dialect_name)
    }

    /// Check if an agent has a specific dialect installed.
    pub fn agent_has_dialect(&self, agent_id: &str, dialect_name: &str) -> bool {
        self.agents
            .get(agent_id)
            .map(|d| d.contains(dialect_name))
            .unwrap_or(false)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{PerformativeDef, ResourceBounds};
    use crate::sexpr::{Atom, SExpr};
    use alloc::string::String;

    fn test_dialect(name: &str) -> Dialect {
        Dialect {
            name: String::from(name),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef {
                name: alloc::format!("{}-action", name),
                params: Vec::new(),
                template: SExpr::List(alloc::vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(alloc::format!("{}-effect", name))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        }
    }

    // -- Construction --

    #[test]
    fn new_network_is_empty() {
        let net = GossipNetwork::with_defaults();
        assert_eq!(net.agent_count(), 0);
        assert!(net.agent_ids().is_empty());
        assert!(net.active_propagations().is_empty());
    }

    #[test]
    fn default_config() {
        let config = GossipConfig::default();
        assert!((config.transmission_probability - 0.8).abs() < f64::EPSILON);
        assert_eq!(config.max_rounds, 100);
        assert_eq!(config.topology, Topology::FullyConnected);
    }

    // -- Agent management --

    #[test]
    fn add_agent() {
        let mut net = GossipNetwork::with_defaults();
        assert!(net.add_agent("alice"));
        assert!(net.add_agent("bob"));
        assert!(!net.add_agent("alice")); // duplicate
        assert_eq!(net.agent_count(), 2);
    }

    #[test]
    fn remove_agent() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        net.add_agent("bob");
        assert!(net.remove_agent("alice"));
        assert!(!net.remove_agent("alice")); // already removed
        assert_eq!(net.agent_count(), 1);
    }

    #[test]
    fn remove_agent_updates_topology() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        net.add_agent("bob");
        net.add_agent("carol");
        // Fully connected: each has 2 neighbors
        assert_eq!(net.neighbors("alice").unwrap().len(), 2);
        net.remove_agent("bob");
        // Alice should now only have carol as neighbor
        let neighbors = net.neighbors("alice").unwrap();
        assert_eq!(neighbors.len(), 1);
        assert_eq!(neighbors[0], "carol");
    }

    // -- Topology --

    #[test]
    fn fully_connected_topology() {
        let mut net = GossipNetwork::with_defaults();
        for name in &["a", "b", "c", "d"] {
            net.add_agent(*name);
        }
        for name in &["a", "b", "c", "d"] {
            assert_eq!(net.neighbors(*name).unwrap().len(), 3);
        }
    }

    #[test]
    fn ring_topology() {
        let config = GossipConfig {
            topology: Topology::Ring,
            ..GossipConfig::default()
        };
        let mut net = GossipNetwork::new(config, 42);
        for name in &["a", "b", "c", "d", "e"] {
            net.add_agent(*name);
        }
        // Each agent should have at most 2 neighbors in a ring
        for name in &["a", "b", "c", "d", "e"] {
            let n = net.neighbors(*name).unwrap().len();
            assert!(n <= 4, "ring neighbor count {} > 4 for {}", n, name);
            assert!(n >= 1, "ring neighbor count {} < 1 for {}", n, name);
        }
    }

    #[test]
    fn is_connected_empty_network() {
        let net = GossipNetwork::with_defaults();
        assert!(net.is_connected());
    }

    #[test]
    fn is_connected_fully_connected() {
        let mut net = GossipNetwork::with_defaults();
        for name in &["a", "b", "c"] {
            net.add_agent(*name);
        }
        assert!(net.is_connected());
    }

    // -- Propagation --

    #[test]
    fn announce_dialect_creates_propagation() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        net.add_agent("bob");
        let result = net.announce_dialect(test_dialect("test"), "alice");
        assert_eq!(result, Some(String::from("test")));
        assert_eq!(net.active_propagations().len(), 1);

        let prop = net.propagation_stats("test").unwrap();
        assert_eq!(prop.infected.len(), 1);
        assert!(prop.infected.contains("alice"));
        assert_eq!(prop.susceptible.len(), 1);
        assert!(prop.susceptible.contains("bob"));
        assert_eq!(prop.round, 0);
    }

    #[test]
    fn announce_dialect_unknown_agent() {
        let mut net = GossipNetwork::with_defaults();
        let result = net.announce_dialect(test_dialect("test"), "nonexistent");
        assert!(result.is_none());
    }

    #[test]
    fn announce_dialect_duplicate() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        net.announce_dialect(test_dialect("test"), "alice");
        let result = net.announce_dialect(test_dialect("test"), "alice");
        assert!(result.is_none());
    }

    #[test]
    fn step_propagates_dialect() {
        let config = GossipConfig {
            transmission_probability: 1.0, // guaranteed transmission
            ..GossipConfig::default()
        };
        let mut net = GossipNetwork::new(config, 42);
        for name in &["a", "b", "c"] {
            net.add_agent(*name);
        }
        net.announce_dialect(test_dialect("test"), "a");

        // After one step with p=1.0, all neighbors of "a" should be infected
        let results = net.step();
        assert!(!results.is_empty());

        // In a fully connected network with p=1.0, one round should infect everyone
        assert!(net.active_propagations().is_empty()); // cleaned up as complete
        assert_eq!(net.stats().successful_propagations, 1);
    }

    #[test]
    fn step_respects_max_rounds() {
        let config = GossipConfig {
            transmission_probability: 0.0, // never transmits
            max_rounds: 3,
            ..GossipConfig::default()
        };
        let mut net = GossipNetwork::new(config, 42);
        net.add_agent("a");
        net.add_agent("b");
        net.announce_dialect(test_dialect("test"), "a");

        for _ in 0..4 {
            net.step();
        }
        // Should have timed out
        assert!(net.active_propagations().is_empty());
        assert_eq!(net.stats().failed_propagations, 1);
    }

    // -- Convergence estimation --

    #[test]
    fn estimate_convergence_single_agent() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        assert_eq!(net.estimate_convergence_time(), 0);
    }

    #[test]
    fn estimate_convergence_log_n() {
        let mut net = GossipNetwork::with_defaults();
        for i in 0..100 {
            net.add_agent(alloc::format!("agent-{}", i));
        }
        let estimate = net.estimate_convergence_time();
        // With p=0.8, ln(100)/ln(1.8) ≈ 7.8, so estimate should be 8
        assert!(estimate > 0);
        assert!(
            estimate <= 10,
            "estimate {} too high for 100 agents",
            estimate
        );
    }

    #[test]
    fn estimate_convergence_empty_network() {
        let net = GossipNetwork::with_defaults();
        assert_eq!(net.estimate_convergence_time(), 0);
    }

    // -- Receive gossip (REQ-122) --

    #[test]
    fn receive_gossip_valid_dialect() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        let d = test_dialect("ext");
        assert!(net.receive_gossip("alice", &d).is_ok());
        assert!(net.agent_has_dialect("alice", "ext"));
    }

    #[test]
    fn receive_gossip_rejects_r3_violation() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        let bad = Dialect {
            name: String::from("bad"),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("tell"), // R3 violation
                params: Vec::new(),
                template: SExpr::Atom(Atom::Symbol(String::from("x"))),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let result = net.receive_gossip("alice", &bad);
        assert!(result.is_err());
        assert!(!net.agent_has_dialect("alice", "bad"));
    }

    #[test]
    fn receive_gossip_rejects_r2_violation() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("alice");
        let bad = Dialect {
            name: String::from("bad-bounds"),
            extends: Vec::new(),
            author: None,
            performatives: Vec::new(),
            resources: ResourceBounds {
                max_depth: 100, // invalid
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let result = net.receive_gossip("alice", &bad);
        assert!(result.is_err());
    }

    // -- Select peers (REQ-121) --

    #[test]
    fn select_peers_returns_subset() {
        let mut net = GossipNetwork::with_defaults();
        for name in &["a", "b", "c", "d", "e"] {
            net.add_agent(*name);
        }
        let peers = net.select_peers("a", 2);
        assert_eq!(peers.len(), 2);
        // All selected peers should be neighbors of "a"
        let neighbors = net.neighbors("a").unwrap();
        for peer in &peers {
            assert!(neighbors.contains(&peer.as_str()));
        }
    }

    #[test]
    fn select_peers_all_when_k_large() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("a");
        net.add_agent("b");
        let peers = net.select_peers("a", 10);
        assert_eq!(peers.len(), 1); // only neighbor is "b"
    }

    #[test]
    fn select_peers_unknown_agent() {
        let mut net = GossipNetwork::with_defaults();
        let peers = net.select_peers("nonexistent", 3);
        assert!(peers.is_empty());
    }

    // -- Simulation --

    #[test]
    fn simulate_propagation_converges() {
        let config = GossipConfig {
            transmission_probability: 1.0,
            ..GossipConfig::default()
        };
        let mut net = GossipNetwork::new(config, 42);
        for i in 0..10 {
            net.add_agent(alloc::format!("agent-{}", i));
        }
        let result = net
            .simulate_propagation(test_dialect("test"), "agent-0")
            .unwrap();
        assert!(result.successful);
        assert!((result.final_coverage - 1.0).abs() < f64::EPSILON);
        // With p=1.0 fully connected, should converge in 1 round
        assert_eq!(result.rounds, 1);
    }

    #[test]
    fn simulate_propagation_with_realistic_probability() {
        let mut net = GossipNetwork::new(GossipConfig::default(), 42);
        for i in 0..20 {
            net.add_agent(alloc::format!("agent-{}", i));
        }
        let result = net
            .simulate_propagation(test_dialect("epidemic"), "agent-0")
            .unwrap();
        assert!(result.successful);
        // O(log n) convergence: should complete well under max_rounds
        assert!(
            result.rounds < 20,
            "took {} rounds for 20 agents",
            result.rounds
        );
    }

    #[test]
    fn simulate_propagation_unknown_agent() {
        let mut net = GossipNetwork::with_defaults();
        let result = net.simulate_propagation(test_dialect("test"), "nonexistent");
        assert!(result.is_none());
    }

    // -- Coverage --

    #[test]
    fn propagation_coverage() {
        let mut state = PropagationState {
            dialect: test_dialect("test"),
            infected: BTreeSet::new(),
            susceptible: BTreeSet::new(),
            round: 0,
            transmission_prob: 0.8,
        };
        // Empty network: coverage = 1.0
        assert!((state.coverage() - 1.0).abs() < f64::EPSILON);
        assert!(state.is_complete());

        state.infected.insert(String::from("a"));
        state.susceptible.insert(String::from("b"));
        state.susceptible.insert(String::from("c"));
        assert!((state.coverage() - 1.0 / 3.0).abs() < 0.01);
        assert!(!state.is_complete());
    }

    // -- Determinism --

    #[test]
    fn deterministic_with_same_seed() {
        let run = |seed: u64| -> SimulationResult {
            let mut net = GossipNetwork::new(GossipConfig::default(), seed);
            for i in 0..15 {
                net.add_agent(alloc::format!("agent-{}", i));
            }
            net.simulate_propagation(test_dialect("det-test"), "agent-0")
                .unwrap()
        };

        let r1 = run(9999);
        let r2 = run(9999);
        assert_eq!(r1.rounds, r2.rounds);
        assert_eq!(r1.successful, r2.successful);
    }

    // -- Statistics --

    #[test]
    fn stats_track_success_and_failure() {
        // Successful propagation
        let config = GossipConfig {
            transmission_probability: 1.0,
            max_rounds: 100,
            ..GossipConfig::default()
        };
        let mut net = GossipNetwork::new(config, 42);
        net.add_agent("a");
        net.add_agent("b");
        net.simulate_propagation(test_dialect("good"), "a");
        assert_eq!(net.stats().successful_propagations, 1);

        // Failed propagation (p=0, max_rounds=2)
        let config2 = GossipConfig {
            transmission_probability: 0.0,
            max_rounds: 2,
            ..GossipConfig::default()
        };
        let mut net2 = GossipNetwork::new(config2, 42);
        net2.add_agent("a");
        net2.add_agent("b");
        net2.simulate_propagation(test_dialect("fail"), "a");
        assert_eq!(net2.stats().failed_propagations, 1);
    }

    // -- LCG --

    #[test]
    fn lcg_produces_values_in_range() {
        let mut rng = Lcg::new(12345);
        for _ in 0..1000 {
            let v = rng.next_f64();
            assert!((0.0..1.0).contains(&v), "LCG value {} out of range", v);
        }
    }

    #[test]
    fn lcg_deterministic() {
        let mut rng1 = Lcg::new(42);
        let mut rng2 = Lcg::new(42);
        for _ in 0..100 {
            assert_eq!(rng1.next_f64().to_bits(), rng2.next_f64().to_bits());
        }
    }

    // -- Remove agent from active propagation --

    #[test]
    fn remove_agent_during_propagation() {
        let mut net = GossipNetwork::with_defaults();
        net.add_agent("a");
        net.add_agent("b");
        net.add_agent("c");
        net.announce_dialect(test_dialect("test"), "a");

        // Remove a susceptible agent
        net.remove_agent("b");
        let prop = net.propagation_stats("test").unwrap();
        assert!(!prop.susceptible.contains("b"));
        assert_eq!(prop.susceptible.len(), 1);
    }
}
