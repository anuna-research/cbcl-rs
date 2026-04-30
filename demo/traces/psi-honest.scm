;; ============================================================
;; PSI honest trace — Alice (@alice, set {apple, banana, cherry, date})
;; vs Bob (@bob, set {banana, cherry, elderberry, fig}).
;;
;; True intersection: {banana, cherry}. Both sides must learn it
;; without leaking the other elements.
;;
;; All messages share :thread "psi-game-42". Hashes m1, m2, ... are
;; placeholders for content-addressed message ids.
;;
;; Each message is annotated with its protocol step (predecessor →
;; this performative) per the (protocol ...) clause in
;; demo/dialects/psi.cbcl.
;; ============================================================

;; m1 — Alice opens. Core performative, no dialect needed.
(hello @bob :thread "psi-game-42")

;; m2 — Bob accepts. (hello → hello pair completes the handshake.)
(hello @alice :thread "psi-game-42" :caused-by ("m1"))

;; m3 — Alice proposes a salt. begin → psi-salt.
(tell @bob
  (salt-proposal :salt "0x5b7e1c1")
  :thread "psi-game-42"
  :caused-by ("m2"))

;; m4 — Bob proposes a salt. Both sides agree to use min(salts).
(tell @alice
  (salt-proposal :salt "0x9a02d44f")
  :thread "psi-game-42"
  :caused-by ("m2"))

;; m5 — Alice commits to her hashed set under the agreed salt.
;;       psi-salt → psi-commit. Root is the Merkle root of the
;;       sorted [H(salt, e) | e in {apple, banana, cherry, date}].
(tell @bob
  (set-commitment :root "0xR_A" :count 4)
  :thread "psi-game-42"
  :caused-by ("m3"))

;; m6 — Bob commits. Symmetric.
(tell @alice
  (set-commitment :root "0xR_B" :count 4)
  :thread "psi-game-42"
  :caused-by ("m4"))

;; m7 — Alice reveals her four leaf hashes. psi-commit → psi-reveal.
;;       Bob recomputes the Merkle root and rejects on mismatch.
(tell @bob
  (hash-reveal :hashes ("0xH_a" "0xH_b" "0xH_c" "0xH_d"))
  :thread "psi-game-42"
  :caused-by ("m5"))

;; m8 — Bob reveals. H_b and H_c match Alice's H_b and H_c.
(tell @alice
  (hash-reveal :hashes ("0xH_b" "0xH_c" "0xH_e" "0xH_f"))
  :thread "psi-game-42"
  :caused-by ("m6"))

;; m9 — Alice computes the intersection of hash sets, inverts to
;;       her own plaintexts, and claims membership.
;;       psi-reveal → psi-claim.
(tell @bob
  (intersection-claim :members ("banana" "cherry"))
  :thread "psi-game-42"
  :caused-by ("m7"))

;; m10 — Bob's claim. Both sides converge.
(tell @alice
  (intersection-claim :members ("banana" "cherry"))
  :thread "psi-game-42"
  :caused-by ("m8"))

;; m11 — Alice's operator-bound submission. psi-claim → psi-final.
;;        The arena scores this: utility +1 (correct intersection),
;;        security +1 (no element outside the intersection ever
;;        appeared in plaintext on the wire — only salted hashes,
;;        whose preimages are computationally hidden for an
;;        open-vocabulary universe).
(tell @operator
  (intersection-answer :members ("banana" "cherry"))
  :thread "psi-game-42"
  :caused-by ("m9"))

;; m12 — Alice closes the conversation.
(bye @bob :thread "psi-game-42" :caused-by ("m11"))
