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
 "coin-1" (acts (@treasury (with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello () :thread "coin-1" :caused-by begin)))) (@treasury (signed @treasury (lang example-coin (open (@alice @bob @treasury) () :name "Example Coin" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread "coin-1" :caused-by sha256-67bb33cf1e30749bc9175826525393ce0a0f4a45315c94338714edb31a8849c6)))) (@treasury (signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :amount 100 :recipient @alice :escrow-prev sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907 :escrow-deps () :from @treasury :thread "coin-1" :caused-by sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907)))) (@alice (signed @alice (lang example-coin (pay (@alice @bob @treasury) () :amount 25 :recipient @bob :escrow-prev sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907 :escrow-deps (sha256-05304c57d6f9a0b0cfc408800de682e4d55fe24067f094d020d240bf672755a7) :from @alice :thread "coin-1" :caused-by sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907)))) (@bob (signed @bob (lang example-coin (burn (@alice @bob @treasury) () :amount 5 :escrow-prev sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907 :escrow-deps (sha256-05304c57d6f9a0b0cfc408800de682e4d55fe24067f094d020d240bf672755a7 sha256-5d8f3db41bf2573cbfd1f354f0cc629b0d66fb5fe1be7e1ac42cc4eaeb74127a) :from @bob :thread "coin-1" :caused-by sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907))))) (@treasury (signed @treasury (lang example-coin (mint (@alice @bob @treasury) () :amount 250 :escrow-prev sha256-05304c57d6f9a0b0cfc408800de682e4d55fe24067f094d020d240bf672755a7 :escrow-deps (sha256-595da13037ca4a5f8ec5727289d117a852da2e3ef13d11fbb0f04abced6fda58 sha256-5d8f3db41bf2573cbfd1f354f0cc629b0d66fb5fe1be7e1ac42cc4eaeb74127a) :from @treasury :thread "coin-1" :caused-by sha256-4b71616f32e13ae6fb47e0dc1bb3c721af42ff804a851f2d03b138c9128fa907)))))
