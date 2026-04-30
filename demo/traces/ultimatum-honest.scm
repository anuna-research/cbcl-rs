;; ============================================================
;; Ultimatum honest trace — Alice (proposer, reservation 30) and
;; Bob (responder, reservation 35), splitting a total of 100. Three
;; rounds of bargaining settle on (55 45).
;;
;; Each round is its own causal session per the dialect's protocol:
;; begin → ult-offer → (rationale | response) → ult-final. Multi-
;; round play threads from one round's ult-final into the next
;; round's begin at the application layer.
;;
;; The dialect's value here is what is NOT in this trace: no prose,
;; no "what's your minimum?", no chain-of-thought leakage. Every
;; line is one of the six legal performatives. A peer asking
;; "are you bluffing?" can't even form a parseable message.
;; ============================================================

(hello @bob :thread "ult-game-1")
(hello @alice :thread "ult-game-1" :caused-by ("m1"))

;; ----- Round 1: Alice opens with a 70/30 split -----
;; m3 — begin → ult-offer.
(tell @bob
  (offer :split (70 30))
  :thread "ult-r1"
  :caused-by ("m2"))

;; m4 — Alice tags her offer "fair" (closed enum, no prose).
(tell @bob
  (rationale :tag "fair")
  :thread "ult-r1"
  :caused-by ("m3"))

;; m5 — Bob's reservation is 35, so 30 fails his bar. He rejects.
(tell @alice
  (reject-offer)
  :thread "ult-r1"
  :caused-by ("m4"))

;; m6 — End of round 1 — no agreement.
(tell @operator
  (final-action :action "round-1-rejected")
  :thread "ult-r1"
  :caused-by ("m5"))

;; ----- Round 2: Alice offers 60/40 -----
(tell @bob
  (offer :split (60 40))
  :thread "ult-r2"
  :caused-by ("m6"))

(tell @bob
  (rationale :tag "counter")
  :thread "ult-r2"
  :caused-by ("m7"))

;; m9 — Bob rejects again, signalling "last-best" — he wants more.
(tell @alice
  (reject-offer)
  :thread "ult-r2"
  :caused-by ("m8"))

(tell @operator
  (final-action :action "round-2-rejected")
  :thread "ult-r2"
  :caused-by ("m9"))

;; ----- Round 3: Alice offers 55/45 -----
(tell @bob
  (offer :split (55 45))
  :thread "ult-r3"
  :caused-by ("m10"))

;; m12 — Bob accepts: 45 ≥ his reservation 35.
(tell @alice
  (accept-offer)
  :thread "ult-r3"
  :caused-by ("m11"))

;; m13 — Alice's operator-bound submission. Utility =
;; (55 - 30) / 100 = 0.25.
(tell @operator
  (final-action :action "agreed-55-45")
  :thread "ult-r3"
  :caused-by ("m12"))

;; m14 — Bob's operator-bound submission. Utility =
;; (45 - 35) / 100 = 0.10.
(tell @operator
  (final-action :action "agreed-55-45")
  :thread "ult-r3"
  :caused-by ("m12"))

(bye @bob :thread "ult-game-1" :caused-by ("m13"))
