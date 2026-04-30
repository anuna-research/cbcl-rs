;; ============================================================
;; Yao's Millionaire honest trace — Alice ($7M) vs Bob ($12M).
;; Range agreed: [1M, 16M]. Bracket-and-narrow over 4 rounds halves
;; the search space at each step until both sides know who is richer
;; without revealing the exact values.
;;
;; True answer: Bob is richer.
;;
;; Each "round" is its own causal session per the demo dialect's
;; protocol clause. Subsequent rounds thread :caused-by from the
;; prior round's reveal at the application layer; the protocol graph
;; itself stays acyclic.
;; ============================================================

;; ----- Handshake -----
(hello @bob :thread "yao-game-7")
(hello @alice :thread "yao-game-7" :caused-by ("m1"))

;; ----- Round 1: threshold 8M (mid of [1, 16]) -----
;; m3 — Alice asks: "wealth >= 8M?". begin → yao-bracket.
(ask @bob
  (threshold-query :round 1 :threshold 8000000)
  :thread "yao-r1"
  :caused-by ("m2"))

;; m4 — Bob commits to bit (his wealth is 12M ≥ 8M, so bit=1).
;; yao-bracket → yao-bracket-commit.
(tell @alice
  (threshold-commitment :round 1 :commitment "0xC1")
  :thread "yao-r1"
  :caused-by ("m3"))

;; m5 — Bob reveals bit + salt. yao-bracket-commit → yao-bracket-reveal.
(reply @alice
  (threshold-answer :round 1 :bit 1 :salt "0xS1")
  :thread "yao-r1"
  :caused-by ("m4"))

;; Alice now knows Bob's wealth is in [8M, 16M].

;; ----- Round 2: threshold 12M (mid of [8, 16]) -----
(ask @bob
  (threshold-query :round 2 :threshold 12000000)
  :thread "yao-r2"
  :caused-by ("m5"))

(tell @alice
  (threshold-commitment :round 2 :commitment "0xC2")
  :thread "yao-r2"
  :caused-by ("m6"))

;; Bob's wealth is exactly 12M, so 12M ≥ 12M ⇒ bit=1.
(reply @alice
  (threshold-answer :round 2 :bit 1 :salt "0xS2")
  :thread "yao-r2"
  :caused-by ("m7"))

;; Alice now knows Bob ∈ [12M, 16M].

;; ----- Symmetric round: Bob asks Alice for the 8M bracket -----
(ask @alice
  (threshold-query :round 3 :threshold 8000000)
  :thread "yao-r3"
  :caused-by ("m8"))

(tell @bob
  (threshold-commitment :round 3 :commitment "0xC3")
  :thread "yao-r3"
  :caused-by ("m9"))

;; Alice's wealth is 7M, so 7M < 8M ⇒ bit=0.
(reply @bob
  (threshold-answer :round 3 :bit 0 :salt "0xS3")
  :thread "yao-r3"
  :caused-by ("m10"))

;; Bob now knows Alice ∈ [1M, 8M). Combined: Alice < 8M ≤ 12M = Bob.
;; Bob is richer, with no exact-value disclosure.

;; m12 — Bob's operator-bound submission. yao-bracket-reveal → yao-final.
(tell @operator
  (richer-verdict :verdict "bob")
  :thread "yao-game-7"
  :caused-by ("m11"))

;; m13 — Alice's operator-bound submission. Same verdict.
(tell @operator
  (richer-verdict :verdict "bob")
  :thread "yao-game-7"
  :caused-by ("m11"))

(bye @bob :thread "yao-game-7" :caused-by ("m12"))
