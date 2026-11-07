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
