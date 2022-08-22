#lang racket

(require
  json
  net/url)

(define/contract (network-info url-string)
  (-> string? hash?)
  (define url (string->url url-string))
  (define resp (get-pure-port url #:redirections 5))
  (read-json resp))

(define (top-tier-orgs info top-tier-org-names)
  (define orgs (hash-ref info 'organizations))
  (for/list
    ([o orgs]
     #:when (member (hash-ref o 'name) top-tier-org-names))
    o))

(define (top-tier-nodes info top-tier-org-names)
  (define orgs
    (top-tier-orgs info top-tier-org-names))
  (apply
    set-union
    (for/list
      ([o orgs])
      (hash-ref o 'validators))))

(define (quorum-sets info)
  (for/hash ([n (hash-ref info 'nodes)])
    (values (hash-ref n 'publicKey) (hash-ref n 'quorumSet))))

;(define (top-tier-nodes info top-tier-org-names)
  ;(hash-ref response 'nodes))

(define (stellar-top-tier-quorumSets)
  (define stellarbeat-url-string
    "https://api.stellarbeat.io/v1")
  (define current-top-tier-org-names
    '("Stellar Development Foundation" "Wirex Limited" "Public Node" "COINQVEST LLC" "SatoshiPay" "LOBSTR" "Blockdaemon Inc."))
  (define info
    (network-info stellarbeat-url-string))
  (define current-top-tier-nodes
    (top-tier-nodes info current-top-tier-org-names))
  (for/hash ([n current-top-tier-nodes])
    (values n (hash-ref (quorum-sets info) n))))
