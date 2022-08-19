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


; quorumSets
; a quorumSet is a hashmap with keys innerQuorumSets, threshold, and validators.
; validators is a list of public keys.

; TODO it might be easier to calculate a node's weight (in nomination) using quorumSets...

(define/contract (cartesian-product ss)
  (-> list? list?)
  (match ss
    [(list s1) s1]
    [(list s1 s2)
     (apply
       append
       (for/list ([e1 s1])
         (for/list ([e2 s2])
           (list e1 e2))))]
    [(cons s1 ss)
     (define ts (cartesian-product ss))
     (apply
       append
       (for/list ([e s1])
         (for/list ([t ts])
           (cons e t))))]))

(module+ test
  (require rackunit)
  (test-case
    "cartesian-product"
    (check-equal?
      (cartesian-product '((a b)))
      '(a b))
    (check-equal?
      (cartesian-product '((a b) ()))
      empty)
    (check-equal?
      (cartesian-product '((a b) (1 2)))
      '((a 1) (a 2) (b 1) (b 2)))
    (check-equal?
      (cartesian-product '((a b) (1 2) (x y)))
      '((a 1 x) (a 1 y) (a 2 x) (a 2 y) (b 1 x) (b 1 y) (b 2 x) (b 2 y)))))

(define (quorumSet->slices qs)
  ; TODO might fail if some nodes appear multiple times
  (define es
    (append (hash-ref qs 'innerQuorumSets) (hash-ref qs 'validators)))
  (define es-refined
    ; list of sets of sets
    (for/list ([e es])
      (cond
        [(hash? e) (quorumSet->slices e)]
        [else (list (list e))])))
  (define cs
    (combinations es-refined (hash-ref qs 'threshold)))
  (apply
    append
    (for/list ([c cs])
      (for/list ([t (cartesian-product c)])
        (apply append t)))))

(module+ test
  (define qset-1
    (hash 'threshold 2 'validators '(1 2 3) 'innerQuorumSets empty))
  (define qset-2
    (hash 'threshold 2 'validators empty 'innerQuorumSets empty))
  (define qset-3
    (hash 'threshold 2 'validators '(a b c) 'innerQuorumSets empty))
  (define qset-4
    (hash 'threshold 2 'validators '(x y z) 'innerQuorumSets empty))
  (define qset-5
    (hash 'threshold 2 'validators empty 'innerQuorumSets (list qset-1 qset-3 qset-4)))
  (define qset-6
    (hash 'threshold 2 'validators (list 'A) 'innerQuorumSets (list qset-1 qset-3 qset-4)))
  (test-case
    "quorumSet->slices"
    (check-equal?
      (quorumSet->slices qset-1)
      '((1 2) (1 3) (2 3)))
    (check-equal?
      (quorumSet->slices qset-2)
      empty))
    (check-equal?
      (quorumSet->slices qset-5)
      '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z)))
    (check-equal?
      (quorumSet->slices qset-6)
      '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (1 2 A) (1 3 A) (2 3 A) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z) (a b A) (a c A) (b c A) (x y A) (x z A) (y z A))))
