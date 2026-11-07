import LeanCbcl.Verify
import LeanCbcl.Lattice.KnowledgeOrder

/-!
# `verify` is monotone in the knowledge order (SPEC-003 REQ-302)

`Verify.lean` proves `verify_monotone` under the valid-is-sticky preorder `⊑`,
which records only that `valid` persists. SPEC-003 REQ-302 states the stronger
property over the flat knowledge order `kle`: once a
verdict is terminal, `valid` or `violation`, it is unchanged by store growth,
and only `unknown` can move. This file proves that statement for the same
`verify`.

The proof has the shape of `verify_monotone`. The one store-sensitive branch
is `.single` with a successful lookup: `lookup_monotone` carries the same
witness to the larger store, so the verdict is literally equal. Fan-in and
fan-out use `meet_knowledge_mono` / `join_knowledge_mono`.

Mirrors: SPEC-003 REQ-302 and `crates/cbcl-core/tests/monotonicity_tests.rs`.
-/

namespace CBCL

open VerificationResult

/-- **REQ-302:** `verify` is monotone under the knowledge order. A terminal
    verdict on `S₁` is the verdict on every `S₂ ⊇ S₁`; an `unknown` may
    resolve either way. -/
theorem verify_knowledge_monotone (M : Message) :
    ∀ (P : CausalProtocol) (S₁ S₂ : MessageStore), S₁ ⊆ S₂ →
    kle (verify M P S₁) (verify M P S₂)
  | .begin, _, _, _ => by
      simp only [verify]
      cases Message.causedBy M with
      | none => exact kle_refl _
      | some c => cases c <;> exact kle_refl _
  | .single perf, S₁, S₂, hSub => by
      simp only [verify]
      cases Message.causedBy M with
      | none => exact kle_refl _
      | some c =>
          cases c with
          | begin => exact kle_refl _
          | multiple _ => exact kle_refl _
          | single h =>
              dsimp only
              cases hL1 : MessageStore.lookup h S₁ with
              | some pred₁ =>
                  have hL2 : MessageStore.lookup h S₂ = some pred₁ :=
                    MessageStore.lookup_monotone hSub h pred₁ hL1
                  rw [hL2]
                  dsimp only
                  exact kle_refl _
              | none =>
                  dsimp only
                  cases hL2 : MessageStore.lookup h S₂ with
                  | none => dsimp only; exact kle_refl _
                  | some pred₂ => dsimp only; split <;> exact unknown_kle _
  | .any [], _, _, _ => by
      simp only [verify, List.foldr]; exact kle_refl _
  | .any (p :: rest), S₁, S₂, hSub => by
      have eq1 :
          verify M (.any (p :: rest)) S₁
            = (verify M p S₁).join (verify M (.any rest) S₁) := by
        simp only [verify, List.foldr]
      have eq2 :
          verify M (.any (p :: rest)) S₂
            = (verify M p S₂).join (verify M (.any rest) S₂) := by
        simp only [verify, List.foldr]
      rw [eq1, eq2]
      exact join_knowledge_mono
        (verify_knowledge_monotone M p S₁ S₂ hSub)
        (verify_knowledge_monotone M (.any rest) S₁ S₂ hSub)
  | .all [], _, _, _ => by
      simp only [verify, List.foldr]; exact kle_refl _
  | .all (p :: rest), S₁, S₂, hSub => by
      have eq1 :
          verify M (.all (p :: rest)) S₁
            = (verify M p S₁).meet (verify M (.all rest) S₁) := by
        simp only [verify, List.foldr]
      have eq2 :
          verify M (.all (p :: rest)) S₂
            = (verify M p S₂).meet (verify M (.all rest) S₂) := by
        simp only [verify, List.foldr]
      rw [eq1, eq2]
      exact meet_knowledge_mono
        (verify_knowledge_monotone M p S₁ S₂ hSub)
        (verify_knowledge_monotone M (.all rest) S₁ S₂ hSub)
termination_by P _ _ _ => sizeOf P
decreasing_by all_goals (simp_wf; omega)

/-- A `violation` verdict is permanent under store growth. -/
theorem verify_violation_stable (M : Message) (P : CausalProtocol)
    {S₁ S₂ : MessageStore} (hSub : S₁ ⊆ S₂) (h : verify M P S₁ = .violation) :
    verify M P S₂ = .violation := by
  have hk := verify_knowledge_monotone M P S₁ S₂ hSub
  rw [h] at hk
  cases hv : verify M P S₂ <;> simp_all [kle]

/-- A `valid` verdict is permanent under store growth (the knowledge-order
    reading of `verify_monotone`). -/
theorem verify_valid_stable (M : Message) (P : CausalProtocol)
    {S₁ S₂ : MessageStore} (hSub : S₁ ⊆ S₂) (h : verify M P S₁ = .valid) :
    verify M P S₂ = .valid := by
  have hk := verify_knowledge_monotone M P S₁ S₂ hSub
  rw [h] at hk
  cases hv : verify M P S₂ <;> simp_all [kle]

end CBCL
