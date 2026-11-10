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
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-coin (open (@alice @bob @treasury) () :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :name "Example Coin" :thread "coin-1" :caused-by f122067bb33cf1e30749bc9175826525393ce0a0f4a45315c94338714edb31a8849c6)))) (@treasury (signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :amount 100 :escrow-deps () :escrow-prev f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963 :from @treasury :recipient @alice :thread "coin-1" :caused-by f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963)))) (@alice (signed @alice (lang example-coin (pay (@alice @bob @treasury) () :amount 25 :escrow-deps (f1220de5e5d7d66a0e12c00785cbeb8e6fe12b851c5b4f3c45596e702622532be70b2) :escrow-prev f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963 :from @alice :recipient @bob :thread "coin-1" :caused-by f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963)))) (@bob (signed @bob (lang example-coin (burn (@alice @bob @treasury) () :amount 5 :escrow-deps (f1220a421729c7c48a026038c056228c84f31677ec5d0ef055b53f36bc412b829e8c5 f1220de5e5d7d66a0e12c00785cbeb8e6fe12b851c5b4f3c45596e702622532be70b2) :escrow-prev f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963 :from @bob :thread "coin-1" :caused-by f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963))))) (@treasury (signed @treasury (lang example-coin (mint (@alice @bob @treasury) () :amount 250 :escrow-deps (f1220a421729c7c48a026038c056228c84f31677ec5d0ef055b53f36bc412b829e8c5 f1220e865d90099100d749df293b72500184673916ca9f1e868522dd7408746c19bde) :escrow-prev f1220de5e5d7d66a0e12c00785cbeb8e6fe12b851c5b4f3c45596e702622532be70b2 :from @treasury :thread "coin-1" :caused-by f1220400baa8fa18604fedff1606554d3d3fc922b89391f627640a4d7a749ba482963)))))
