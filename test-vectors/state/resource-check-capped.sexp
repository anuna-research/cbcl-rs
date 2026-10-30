(resource-check ; Capped profile: initial allocations sum to 4, initial :space sums to 6.
; Example cast: issuer={@treasury,@alice}, holder={@treasury,@alice,@bob}.
; Bounded-counter example. Amounts are integer base units, not decimals.
; Hosts authenticate acts and serialize issuance per account before publication.
(define example-capped-coin (cbcl) @coin-author
  (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000)))
  (:roles ((* issuer) (* holder)))
  (extend open (to name allocations space) :from issuer :to (issuer holder)
    (tell to :name name :allocations allocations :space space))
  (extend mint (to amount) :from issuer :to (issuer holder)
    (tell to :amount amount))
  (extend burn (to amount) :from holder :to (issuer holder)
    (tell to :amount amount))
  (extend pay (to recipient amount) :from holder :to (issuer holder)
    (tell to :recipient recipient :amount amount))
  (shape open (require :name string) (require :allocations list) (require :space list))
  (shape mint (require :amount number))
  (shape burn (require :amount number))
  (shape pay (require :recipient symbol) (require :amount number))
  (extend share-space (to recipient amount) :from holder :to (issuer holder)
    (tell to :recipient recipient :amount amount))
  (shape share-space (require :recipient symbol) (require :amount number))
  (protocol (then open share-space) (then begin open) (then open mint) (then open burn) (then open pay))
  (state
    (name (last open :name))
    (coins (bounded-counter
      (floor 0)
      (ceiling 10)
      (initial-headroom open :space)
      (transfer-headroom share-space :recipient :amount)
      (initial-rights open :allocations)
      (issuers issuer)
      (increment mint :amount)
      (decrement burn :amount)
      (transfer pay :recipient :amount)))))
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury @alice) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-capped-coin (open (@alice @bob @treasury) () :name "Capped" :allocations ((@treasury 2) (@alice 2) (@bob 0)) :space ((@treasury 3) (@alice 3) (@bob 0)) :from @treasury :thread "coin-1" :caused-by sha256-6655c6fbcd385dd84414cad93d6cad9a1ed650f4c2834790d9043f543051d407)))) (@treasury (signed @treasury (lang example-capped-coin (mint (@alice @bob @treasury) () :amount 3 :escrow-prev sha256-26e0e8161d624375c59a70d05103cf571d66bf2d24615d34d5608cb5267a5ffc :escrow-deps () :from @treasury :thread "coin-1" :caused-by sha256-26e0e8161d624375c59a70d05103cf571d66bf2d24615d34d5608cb5267a5ffc))))) (@alice (signed @alice (lang example-capped-coin (mint (@alice @bob @treasury) () :amount 3 :escrow-prev sha256-26e0e8161d624375c59a70d05103cf571d66bf2d24615d34d5608cb5267a5ffc :escrow-deps () :from @alice :thread "coin-1" :caused-by sha256-26e0e8161d624375c59a70d05103cf571d66bf2d24615d34d5608cb5267a5ffc)))))
