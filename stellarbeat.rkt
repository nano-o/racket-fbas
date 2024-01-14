#lang racket

(require
  json
  net/url
  "qset2.rkt"
  #;racket/trace)

(provide
  get-stellar-network
  get-stellar-top-tier)

(define/contract (network-info url-string)
  (-> string? hash?)
  (define url (string->url url-string))
  (define resp (get-pure-port url #:redirections 5))
  (read-json resp))

(define (quorum-sets info)
  (for/hash
    ([n (hash-ref info 'nodes)]
     #:when (and
              (hash-has-key? n 'publicKey)
              (hash-has-key? n 'quorumSet)
              (not (equal? (hash-ref n 'quorumSet) 'null))))
    (values (hash-ref n 'publicKey) (hash-ref n 'quorumSet))))

(define stellarbeat-url-string
  "https://api.stellarbeat.io/v1")

(define (get-stellar-network)
  (define info
    (network-info stellarbeat-url-string))
  (hash->conf (quorum-sets info)))

(define (hash->qset h)
  (qset/kw
    #:threshold (hash-ref h 'threshold)
    #:validators (list->seteqv (map string->symbol (hash-ref h 'validators)))
    #:inner-qsets (for/set ([q (hash-ref h 'innerQuorumSets)])
              (hash->qset q))))

(define (hash->conf h)
  ; we return an alist
  (for/list ([(n q) (in-hash h)])
    (cons (string->symbol n) (hash->qset q))))

;; Top tier

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

(define (get-stellar-top-tier-qsets)
  (define info
    (network-info stellarbeat-url-string))
  (define current-top-tier-org-names
  '("Stellar Development Foundation" "Public Node" "Whalestack LLC" "SatoshiPay" "LOBSTR" "Blockdaemon Inc." "Franklin Templeton"))
  (define current-top-tier-nodes
    (top-tier-nodes info current-top-tier-org-names))
  (for/hash ([n current-top-tier-nodes])
    (values n (hash-ref (quorum-sets info) n))))

(define (get-stellar-top-tier)
  (hash->conf (get-stellar-top-tier-qsets)))

; convert a qset to nested hashmaps
#;(define (to-jsexpr sqs)
  (define (qset-to-jsexpr qs)
    (hash
      'threshold (qset-threshold qs)
      'validators (map symbol->string (qset-validators qs))
      'inner-qsets (map qset-to-jsexpr (qset-inner-qsets qs))))
  (for/hash ([(val qs) (in-hash sqs)])
    (values val (qset-to-jsexpr qs))))

(module+ test
  (require rackunit)

  (check-not-exn get-stellar-network)
  (check-not-exn get-stellar-top-tier)

  #;(test-case
    "to-jsexpr"
    (check-true
      (jsexpr? (to-jsexpr stellar-qsets)))
    (check-not-exn
      (thunk
        (to-jsexpr stellar-qsets)))))
