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
import LeanCbcl.DetParser
import LeanCbcl.DeterministicUnion
import LeanCbcl.Lattice.Store
import LeanCbcl.Lattice.Result
import LeanCbcl.DCFLPreservation
import LeanCbcl.Verify
import LeanCbcl.R5
import LeanCbcl.EPP
import LeanCbcl.EPPCompletion
