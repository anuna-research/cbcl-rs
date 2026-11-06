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
  (shape mint (require :amount number))
  (shape burn (require :amount number))
  (shape pay (require :recipient symbol) (require :amount number))
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
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-coin (open (@alice @bob @treasury) () :name "Example Coin" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread "coin-1" :caused-by sha256-6655c6fbcd385dd84414cad93d6cad9a1ed650f4c2834790d9043f543051d407)))) (@treasury (signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :amount 100 :recipient @alice :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5 :escrow-deps () :from @treasury :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))) (@alice (signed @alice (lang example-coin (pay (@alice @bob @treasury) () :amount 25 :recipient @bob :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5 :escrow-deps (sha256-fb89b8805e64de1ea5696aabe3462339a1ead4a68a10948754161ab403859162) :from @alice :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))) (@bob (signed @bob (lang example-coin (burn (@alice @bob @treasury) () :amount 5 :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5 :escrow-deps (sha256-a9e0a928c5277a5abf400eb0f7b4cfd60cc0018d42ba06453e9e9a070fdb1524 sha256-fb89b8805e64de1ea5696aabe3462339a1ead4a68a10948754161ab403859162) :from @bob :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5))))) (@treasury (signed @treasury (lang example-coin (mint (@alice @bob @treasury) () :amount 250 :escrow-prev sha256-fb89b8805e64de1ea5696aabe3462339a1ead4a68a10948754161ab403859162 :escrow-deps (sha256-a9e0a928c5277a5abf400eb0f7b4cfd60cc0018d42ba06453e9e9a070fdb1524 sha256-b54e8b73521dfb9d711119806450b914d2b31ef5dd4df5566b977a072dcb1722) :from @treasury :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))))
