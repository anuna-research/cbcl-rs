;; ============================================================
;; Dining Cryptographers honest trace — Alice (@a, inv_A), Bob (@b,
;; inv_B), Carol (@c, inv_C) at dinner. Carol paid the bill.
;;
;; DC-net protocol with three pairwise random bits:
;;   r_{ab} = 1, r_{ac} = 0, r_{bc} = 1.
;; Each diner's announcement = XOR of their two pairwise bits XOR
;; their I-paid bit.
;;   Alice:  r_{ab} XOR r_{ac} XOR p_a = 1 XOR 0 XOR 0 = 1
;;   Bob:    r_{ab} XOR r_{bc} XOR p_b = 1 XOR 1 XOR 0 = 0
;;   Carol:  r_{ac} XOR r_{bc} XOR p_c = 0 XOR 1 XOR 1 = 0
;;   Sum:    1 XOR 0 XOR 0 = 1  ⇒ a diner paid (someone said "yes").
;;
;; Anonymity property: Alice and Bob each see Carol's announcement
;; was 0, but cannot deduce that Carol paid (they would need the
;; pairwise bit r_{bc} or r_{ac} from the diner not in their pair —
;; which collusion could expose, but not unilateral observation).
;;
;; The protocol's (all ...) fan-in says: no diner reveals a pairwise
;; bit until ALL three pairwise commitments have been posted —
;; otherwise the late committer could choose their bit adversarially.
;; ============================================================

;; ----- Three-way handshake (core hello) -----
(hello @b :thread "dc-game-1")
(hello @a :thread "dc-game-1" :caused-by ("m1"))
(hello @c :thread "dc-game-1" :caused-by ("m1"))

;; ----- Phase 1: pairwise mask commitments -----
;; Alice and Bob jointly commit to r_{ab} = 1 (both post the same
;; commitment hash; in practice they coordinate via a side channel
;; or use a sender-distinguishing pair-id).
;; m4 — Alice posts the (1,2) commitment. begin → dc-mask-12.
(tell @b
  (pair-mask :pair "1-2" :commitment "0xM12")
  :thread "dc-game-1"
  :caused-by ("m1"))

;; m5 — Alice and Carol commit to r_{ac} = 0.
(tell @c
  (pair-mask :pair "1-3" :commitment "0xM13")
  :thread "dc-game-1"
  :caused-by ("m1"))

;; m6 — Bob and Carol commit to r_{bc} = 1.
(tell @c
  (pair-mask :pair "2-3" :commitment "0xM23")
  :thread "dc-game-1"
  :caused-by ("m1"))

;; ----- Phase 2: pairwise reveals -----
;; The (all dc-mask-12 dc-mask-13 dc-mask-23) fan-in barrier means a
;; reveal is only causally valid once ALL three masks have been seen.
;; Each reveal's :caused-by lists all three commitment hashes — the
;; fan-in node-ref binds against the multiset.
(tell @b
  (pair-reveal :pair "1-2" :bit 1 :salt "0xS12")
  :thread "dc-game-1"
  :caused-by ("m4" "m5" "m6"))

(tell @c
  (pair-reveal :pair "1-3" :bit 0 :salt "0xS13")
  :thread "dc-game-1"
  :caused-by ("m4" "m5" "m6"))

(tell @c
  (pair-reveal :pair "2-3" :bit 1 :salt "0xS23")
  :thread "dc-game-1"
  :caused-by ("m4" "m5" "m6"))

;; ----- Phase 3: announcements -----
;; Each diner now has all three pairwise bits and can compute their
;; XOR sum. The (all dc-reveal-12 dc-reveal-13 dc-reveal-23) fan-in
;; is the predecessor of dc-announce.
;; m10 — Alice's announcement: r_{ab} XOR r_{ac} XOR p_a = 1.
(tell @b
  (announcement :bit 1)
  :thread "dc-game-1"
  :caused-by ("m7" "m8" "m9"))

;; m11 — Bob's announcement: 1 XOR 1 XOR 0 = 0.
(tell @a
  (announcement :bit 0)
  :thread "dc-game-1"
  :caused-by ("m7" "m8" "m9"))

;; m12 — Carol's announcement: 0 XOR 1 XOR 1 = 0.
(tell @a
  (announcement :bit 0)
  :thread "dc-game-1"
  :caused-by ("m7" "m8" "m9"))

;; XOR sum: 1 XOR 0 XOR 0 = 1 ⇒ a diner paid (internal).

;; ----- Phase 4: operator submission -----
;; Each diner submits "internal" (a diner paid, but I'm not naming
;; them) — this maximises group security while still claiming the
;; correct utility point. dc-announce → dc-final.
(tell @operator
  (paid-verdict :verdict "internal")
  :thread "dc-game-1"
  :caused-by ("m10"))

(tell @operator
  (paid-verdict :verdict "internal")
  :thread "dc-game-1"
  :caused-by ("m11"))

(tell @operator
  (paid-verdict :verdict "internal")
  :thread "dc-game-1"
  :caused-by ("m12"))

;; Carol could alternatively submit her own invite-code, conceding
;; security but gaining nothing extra in utility — so the rational
;; play is "internal" all round.

(bye @b :thread "dc-game-1" :caused-by ("m13"))
