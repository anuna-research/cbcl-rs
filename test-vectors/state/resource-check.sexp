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
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-coin (open (@alice @bob @treasury) () :name "Example Coin" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread "coin-1" :caused-by sha256-6655c6fbcd385dd84414cad93d6cad9a1ed650f4c2834790d9043f543051d407)))) (@treasury (signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 100 :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5 :escrow-deps () :from @treasury :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))) (@alice (signed @alice (lang example-coin (pay (@alice @bob @treasury) () :recipient @bob :amount 25 :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5 :escrow-deps (sha256-0f0749d941068822bf56bcc463af8d31de5bcaf3acadbd1b6b4feab7ad59d911) :from @alice :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))) (@bob (signed @bob (lang example-coin (burn (@alice @bob @treasury) () :amount 5 :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5 :escrow-deps (sha256-0f0749d941068822bf56bcc463af8d31de5bcaf3acadbd1b6b4feab7ad59d911 sha256-89f6c96de94e9155e763efc872145dc4273af9d5f827fc1e0c099d9ccdf2777f) :from @bob :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5))))) (@treasury (signed @treasury (lang example-coin (mint (@alice @bob @treasury) () :amount 250 :escrow-prev sha256-0f0749d941068822bf56bcc463af8d31de5bcaf3acadbd1b6b4feab7ad59d911 :escrow-deps (sha256-89f6c96de94e9155e763efc872145dc4273af9d5f827fc1e0c099d9ccdf2777f sha256-cf33780b6a9cb166169d412b2256035012fb745c1f4963927fc566564c272a76) :from @treasury :thread "coin-1" :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))))
