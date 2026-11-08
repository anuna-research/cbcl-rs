-- CBCL: Formally Verified Agent-Communication Language
-- Lean 4 formalization of the CBCL reference implementation
--
-- This library provides:
--   1. Inductive types modeling CBCL's core data structures
--   2. Verified S-expression parser and serializer
--   3. CBCL message parser with grammar validation
--   4. Verified implementations of safety constraints R1–R4
--   5. Complete pipeline: String → Verified Message
--   6. Proofs of key properties: soundness, completeness, termination

import LeanCbcl.SExpr
import LeanCbcl.Message
import LeanCbcl.Dialect
import LeanCbcl.Agent
import LeanCbcl.Parser
import LeanCbcl.Serializer
import LeanCbcl.MessageParser
import LeanCbcl.PatternMatch
import LeanCbcl.DialectParser
import LeanCbcl.R1NoRecursion
import LeanCbcl.R2ResourceBounds
import LeanCbcl.R3CorePreservation
import LeanCbcl.Pipeline
import LeanCbcl.TemplateExpansion
import LeanCbcl.Lattice.Store
import LeanCbcl.Lattice.Result
import LeanCbcl.Lattice.KnowledgeOrder
import LeanCbcl.DCFLPreservation
import LeanCbcl.R6DCFLPreservation
import LeanCbcl.Verify
import LeanCbcl.VerifyKnowledge
import LeanCbcl.R5
import LeanCbcl.EPP
import LeanCbcl.EPPCompletion
import LeanCbcl.Projectability
import LeanCbcl.ProtocolProjection
import LeanCbcl.ConcreteProjection
import LeanCbcl.Splice
import LeanCbcl.Bridge
import LeanCbcl.FiniteDPDA
import LeanCbcl.FiniteForest
import LeanCbcl.FiniteForestTests
import LeanCbcl.InstalledSyntaxTests
import LeanCbcl.InstalledLexerTests
import LeanCbcl.State
import LeanCbcl.AdmissionStratification
import LeanCbcl.StateRefinement
import LeanCbcl.StateLift
import LeanCbcl.StateLVar
import LeanCbcl.StateContext

import LeanCbcl.Repeat

import LeanCbcl.StateProgress
import LeanCbcl.MonitoredDCFL
import LeanCbcl.FiniteMonitorTests

import LeanCbcl.BoundedCounter

import LeanCbcl.ValidatorBudget

import LeanCbcl.ValidatorBudgetRefutation

import LeanCbcl.SealedCheckpoint

import LeanCbcl.AbortableHandoff

import LeanCbcl.ConsensusFree
import LeanCbcl.ConsensusFree.Tests
import LeanCbcl.ConsensusFree.Liveness
import LeanCbcl.ConsensusFree.Scheduler

import LeanCbcl.ConsensusFree.OwnedLifecycle

import LeanCbcl.ConsensusFree.OwnedProgress

import LeanCbcl.ConsensusFree.OwnerFunding

import LeanCbcl.ConsensusFree.OwnerProduct
import LeanCbcl.ConsensusFree.OwnerTermination
import LeanCbcl.ConsensusFree.OwnerProductWitness

import LeanCbcl.HlcRegister

import LeanCbcl.StateKernelClause
import LeanCbcl.StateKernelTests

import LeanCbcl.StateKernelSECTests

import LeanCbcl.CheckpointKernelTests
import LeanCbcl.CheckpointAllTests

import LeanCbcl.StateResourceTests

import LeanCbcl.StateNativeRefinementTests

import LeanCbcl.StateResourceKahnTests

import LeanCbcl.StateResourceCache

import LeanCbcl.StateResourceCacheTests
import LeanCbcl.StateResourceStructure

import LeanCbcl.StateResourceCones

import LeanCbcl.StateResourceFrontier

import LeanCbcl.StateResourcePartition

import LeanCbcl.StateResourceBudget

import LeanCbcl.StateResourceDependency

import LeanCbcl.StateResourceOwnPrefix

import LeanCbcl.StateResourceOutgoing

import LeanCbcl.StateResourceLocalBudget

import LeanCbcl.StateResourceWitness

import LeanCbcl.StateResourceMachine

import LeanCbcl.StateResourceAuthorization

import LeanCbcl.StateResourceCounters

import LeanCbcl.StateResourceRecordBounds

import LeanCbcl.StateResourceGraph

import LeanCbcl.StateResourceCoupling

import LeanCbcl.StateResourceWorklist

import LeanCbcl.StateResourceAggregate

import LeanCbcl.StateResourceAccounting

import LeanCbcl.StateResourceSolvency

import LeanCbcl.StateResourceFinalize

import LeanCbcl.StateResourceValidated

import LeanCbcl.StateResourceAggregateTests

import LeanCbcl.StateResourcePreflight

import LeanCbcl.StateResourceVerifier

import LeanCbcl.StateResourceVerifierTests

import LeanCbcl.StateInstalledCompiler

import LeanCbcl.StateInstalledClause

import LeanCbcl.StateInstalledCompilerTests

import LeanCbcl.StateInstalledLattice

import LeanCbcl.StateInstalledLowering

import LeanCbcl.StateInstalledLoweringTests

import LeanCbcl.StateResourceCompletion

import LeanCbcl.StateResourceReadEquivalence

import LeanCbcl.StateInstalledLegacy

import LeanCbcl.StateInstalledResource

import LeanCbcl.StateInstalledLegacyTests

import LeanCbcl.StateInstalledTerm

import LeanCbcl.StateContextEvidence

import LeanCbcl.StateInstalledContext

import LeanCbcl.StateInstalledDomains

import LeanCbcl.StateFiniteTable

import LeanCbcl.StateFiniteProjection

import LeanCbcl.StateFiniteProjectionTests

import LeanCbcl.StateInstalledFinite

import LeanCbcl.StateFiniteRead

import LeanCbcl.StateFiniteReadTests

import LeanCbcl.StateObservation

import LeanCbcl.StateObservationPlan

import LeanCbcl.StateAuthoredBindings

import LeanCbcl.StateAuthoredBindingsTests

import LeanCbcl.StateFreezeGrowth

import LeanCbcl.StateFreezeScopes

import LeanCbcl.StateCompiledFreezeGrowth

import LeanCbcl.StateNativeReader

import LeanCbcl.StateFiniteUpperCache

import LeanCbcl.StateFinitePairLoop

import LeanCbcl.StateInstalledRecognition

import LeanCbcl.StateAuthoredCompletion

import LeanCbcl.StateExecutableFreeze

import LeanCbcl.StateExecutableObservation

import LeanCbcl.StateExecutableContext

import LeanCbcl.StateMemoizedReaderTests

import LeanCbcl.StateReaderIndices

import LeanCbcl.StateAuthoredDependencies

import LeanCbcl.StateReaderValuesTests

import LeanCbcl.StateReaderReachabilityTests

import LeanCbcl.StateCompiledFieldEquationsTests

import LeanCbcl.StateFrozenBodyEquationsTests

import LeanCbcl.StateCausalRank

import LeanCbcl.StateThresholdDispatchTests

import LeanCbcl.StatePreparedOutputsTests

import LeanCbcl.StateOutputCompilerTests

import LeanCbcl.StateCausalRankIntegrationTests

import LeanCbcl.StateCausalCheckCompleteTests

import LeanCbcl.StateOpenerLocalityTests

import LeanCbcl.StateDomainSupportLocalityTests

import LeanCbcl.StateFiniteFreezePolicyTests

import LeanCbcl.StateFiniteOutputStabilityTests

import LeanCbcl.StateAuthoredSourceProvenanceTests

import LeanCbcl.StateAuthoredFiniteStabilityTests

import LeanCbcl.StateAuthoredFinitePreservationTests

import LeanCbcl.StateNativeDataPoliciesTests

import LeanCbcl.StateAuthoredDataPreservationTests

import LeanCbcl.StateAuthoredMembershipTests

import LeanCbcl.StateAuthoredEventMembershipTests

import LeanCbcl.StateEventMapTotalTests

import LeanCbcl.StateAuthoredEventSumTests

import LeanCbcl.StateNonnegativeAdmissionTests

import LeanCbcl.StateAuthoredSumTrace

import LeanCbcl.StateProgressStoreTests

import LeanCbcl.StateProgressFreezeTests

import LeanCbcl.StateAuthoredProgressTests
