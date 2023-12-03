#lang racket

(require
  json
  net/url
  (only-in "qset.rkt" qset qset-kw qset-validators qset-threshold qset-inner-qsets qset-members)
  (rename-in "qset.rkt" [expand expand-qset])
  (only-in "nomination.rkt" weight))
(provide
  get-stellar-conf
  get-stellar-top-tier-conf
  get-stellar-top-tier-qsets
  hash->conf)

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
  (for/hash ([n (hash-ref info 'nodes)]
             #:when (and
                      (hash-has-key? n 'publicKey)
                      (hash-has-key? n 'quorumSet)
                      (not (equal? (hash-ref n 'quorumSet) null))))
    (values (hash-ref n 'publicKey) (hash-ref n 'quorumSet))))

(define stellarbeat-url-string
  "https://api.stellarbeat.io/v1")

(define (get-stellar-top-tier-qsets)
  (define info
    (network-info stellarbeat-url-string))
  (define current-top-tier-org-names
  '("Stellar Development Foundation" "Public Node" "COINQVEST LLC" "SatoshiPay" "LOBSTR" "Blockdaemon Inc." "Franklin Templeton"))
  (define current-top-tier-nodes
    (top-tier-nodes info current-top-tier-org-names))
  (for/hash ([n current-top-tier-nodes])
    (values n (hash-ref (quorum-sets info) n))))

(define (get-stellar-top-tier-conf)
  (hash->conf (get-stellar-top-tier-qsets)))

(define (get-stellar-conf)
  (define info
    (network-info stellarbeat-url-string))
  (hash->conf (quorum-sets info)))

(define (hash->qset h)
  (qset-kw
    #:threshold (hash-ref h 'threshold)
    #:validators (map string->symbol (hash-ref h 'validators))
    #:inner (for/list ([q (hash-ref h 'innerQuorumSets)])
              (hash->qset q))))

(define (hash->conf h)
  (for/hasheqv ([(n q) (in-hash h)])
    (values (string->symbol n) (hash->qset q))))

; convert a qset to nested hashmaps
(define (to-jsexpr sqs)
  (define (qset-to-jsexpr qs)
    (hash
      'threshold (qset-threshold qs)
      'validators (map symbol->string (qset-validators qs))
      'inner-qsets (map qset-to-jsexpr (qset-inner-qsets qs))))
  (for/hash ([(val qs) (in-hash sqs)])
    (values val (qset-to-jsexpr qs))))

(define (to-slice-system sqs)
  (for/hash ([(val qs) (in-hash sqs)])
    (values
      val
      (for/list ([ss (in-set (expand-qset qs))])
        (for/list ([s ss])
          (symbol->string s))))))

(define (to-weighted-graph sqs)
  (for/hash ([(val qs) (in-hash sqs)])
    (define peers
      (qset-members qs))
    (values
      val
      (for/hash ([p peers])
        (values p (weight qs p))))))

(define (to-weighted-graph-2 sqs)
  (for*/list ([(val qs) (in-hash sqs)]
              [p (qset-members qs)])
    (list
      (list (symbol->string val) (symbol->string p))
      (exact->inexact (weight qs p)))))

(module+ test
  (require rackunit)

  (define stellar-qsets
    (get-stellar-conf))

  (test-case
    "to-jsexpr"
    (check-true
      (jsexpr? (to-jsexpr stellar-qsets)))
    (check-not-exn
      (thunk
        (to-jsexpr stellar-qsets))))
  (test-case
    "to-slice-system"
    (check-true
      (jsexpr? (to-slice-system stellar-qsets))))
  'todo)
