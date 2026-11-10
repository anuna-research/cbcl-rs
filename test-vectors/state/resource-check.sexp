(resource-check ; Bounded-counter example. Amounts are integer base units, not decimals.
; Hosts authenticate acts and serialize issuance per account before publication.
(define example-coin (cbcl) @coin-author
  (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000)))
  (:roles (issuer (* holder)))
  (extend open (to name allocations) :from issuer :to (issuer holder)
    (tell to :name name :allocations allocations))
  (extend mint (to amount) :from issuer :to (issuer holder)
    (tell to :amount amount))
  (extend burn (to amount) :from holder :to (issuer holder)
    (tell to :amount amount))
  (extend pay (to recipient amount) :from holder :to (issuer holder)
    (tell to :recipient recipient :amount amount))
  (shape open (require :name string) (require :allocations list))
  (shape mint (require :amount integer))
  (shape burn (require :amount integer))
  (shape pay (require :recipient symbol) (require :amount integer))
  (protocol (then begin open) (then open mint) (then open burn) (then open pay))
  (state
    (name (initial open :name))
    (coins (bounded-counter
      (floor 0)
      (initial-rights open :allocations)
      (issuers issuer)
      (increment mint :amount)
      (decrement burn :amount)
      (transfer pay :recipient :amount)))))
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-coin (open (@alice @bob @treasury) () :name "Example Coin" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread "coin-1" :caused-by f122067bb33cf1e30749bc9175826525393ce0a0f4a45315c94338714edb31a8849c6)))) (@treasury (signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :amount 100 :recipient @alice :escrow-prev f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f :escrow-deps () :from @treasury :thread "coin-1" :caused-by f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f)))) (@alice (signed @alice (lang example-coin (pay (@alice @bob @treasury) () :amount 25 :recipient @bob :escrow-prev f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f :escrow-deps (f122031662c15f7bd725c2e714cc9b7392d28c2d549a3fe9b5ef0c3cc81307c2c438c) :from @alice :thread "coin-1" :caused-by f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f)))) (@bob (signed @bob (lang example-coin (burn (@alice @bob @treasury) () :amount 5 :escrow-prev f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f :escrow-deps (f122031662c15f7bd725c2e714cc9b7392d28c2d549a3fe9b5ef0c3cc81307c2c438c f12207ec9cafff4631ae7f4554aa3f7b7f0c5bf561679240199c8f9d158d8d083e18f) :from @bob :thread "coin-1" :caused-by f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f))))) (@treasury (signed @treasury (lang example-coin (mint (@alice @bob @treasury) () :amount 250 :escrow-prev f122031662c15f7bd725c2e714cc9b7392d28c2d549a3fe9b5ef0c3cc81307c2c438c :escrow-deps (f12207ec9cafff4631ae7f4554aa3f7b7f0c5bf561679240199c8f9d158d8d083e18f f12209fe370fb05d86ef857123ab96d4ddeae5bcc8402c750318b7de8090c81298d2e) :from @treasury :thread "coin-1" :caused-by f12206cb665125c407ef5b342519f806c8ded7e05efcd26aa5501d620b5b3f0829e4f)))))
