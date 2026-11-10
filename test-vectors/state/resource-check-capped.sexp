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
  (shape mint (require :amount integer))
  (shape burn (require :amount integer))
  (shape pay (require :recipient symbol) (require :amount integer))
  (extend share-space (to recipient amount) :from holder :to (issuer holder)
    (tell to :recipient recipient :amount amount))
  (shape share-space (require :recipient symbol) (require :amount integer))
  (protocol (then open share-space) (then begin open) (then open mint) (then open burn) (then open pay))
  (state
    (name (initial open :name))
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
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury @alice) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-capped-coin (open (@alice @bob @treasury) () :name "Capped" :allocations ((@treasury 2) (@alice 2) (@bob 0)) :space ((@treasury 3) (@alice 3) (@bob 0)) :from @treasury :thread "coin-1" :caused-by sha256-00e5135405fae01e3135ee94a3a7e57f1f35fe19de5203d42462307db3585131)))) (@treasury (signed @treasury (lang example-capped-coin (mint (@alice @bob @treasury) () :amount 3 :escrow-prev sha256-184bec2b98c9abd34da10df8b4a124de53da54c94e9617cda20885b9c842aeaa :escrow-deps () :from @treasury :thread "coin-1" :caused-by sha256-184bec2b98c9abd34da10df8b4a124de53da54c94e9617cda20885b9c842aeaa))))) (@alice (signed @alice (lang example-capped-coin (mint (@alice @bob @treasury) () :amount 3 :escrow-prev sha256-184bec2b98c9abd34da10df8b4a124de53da54c94e9617cda20885b9c842aeaa :escrow-deps () :from @alice :thread "coin-1" :caused-by sha256-184bec2b98c9abd34da10df8b4a124de53da54c94e9617cda20885b9c842aeaa)))))
