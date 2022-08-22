#lang racket

(provide
  quorum?
  quorum-of?
  weight
  nomination-votes
  accepted-nominated?)

(define (zip l1 l2)
  (map cons l1 l2))

; a node is something for which eqv? is semantic equivalence, i.e. interned symbols, numbers, and characters.
(define node/c
  (or/c (and/c symbol? symbol-interned?) number? char?))

; A FBAS is a map from nodes to sets of slices
(define fbas/c
  (and/c
    immutable?
    (hash/c node/c (listof (listof node/c)))))

; A quorum-set represents sets of sets of nodes using thresholds
; This is what is used on the wire in the Stellar network
(define-struct qset (threshold validators inner-qsets))

; The quorum-set generation tool included in core uses validators array
(struct validator-description (quality home-domain))
(define validatos-array/c
  (hash/c any/c validator-description?))

; We will use cartesian-product to transform a qset into an fbas
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

(define (expand-qset qs)
  (define es
    (append (hash-ref qs 'innerQuorumSets) (hash-ref qs 'validators)))
  (define es-refined
    ; list of sets of sets
    (for/list ([e es])
      (cond
        [(hash? e) (expand-qset e)]
        [else (list (list e))])))
  (define cs
    (combinations es-refined (hash-ref qs 'threshold)))
  (apply
    append
    (for/list ([c cs])
      (for/list ([t (cartesian-product c)])
        (apply append t)))))

(module+ test
  (require rackunit)
  (provide (all-defined-out))

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
      (expand-qset qset-1)
      '((1 2) (1 3) (2 3)))
    (check-equal?
      (expand-qset qset-2)
      empty))
    (check-equal?
      (expand-qset qset-5)
      '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z)))
    (check-equal?
      (expand-qset qset-6)
      '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (1 2 A) (1 3 A) (2 3 A) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z) (a b A) (a c A) (b c A) (x y A) (x z A) (y z A))))

(module+ test

  (define (threshold-fbas t n)
    fbas/c
    (define nodes
      (range 1 (add1 n)))
    (define slices
      (combinations nodes t))
    (make-immutable-hash (zip nodes (make-list n slices))))

  (define fbas-1
    (threshold-fbas 3 4))

  (define fbas-2
    (let ([slices
            (combinations '(1 2 3) 2)])
      (hash-set fbas-1 1 slices)))

  (define fbas-3
    (let ([slices-1
            (combinations '(1 2 3) 2)]
          [slices-2
            (combinations '(3 4 5) 2)])
      (hash-set (hash-set (threshold-fbas 4 5) 1 slices-1) 5 slices-2))))

(define/contract (has-slice-in? fbas p Q)
  (-> fbas/c node/c list? boolean?)
  (define slices
    (hash-ref fbas p))
  (for/or ([s slices])
    (subset? s Q)))

(define (quorum? fbas Q)
  (-> fbas/c list? boolean?)
    (for/and ([q Q])
      (has-slice-in? fbas q Q)))

(define (quorum-of? fbas p Q)
  (-> fbas/c node/c list? boolean?)
  (and
    (has-slice-in? fbas p Q)
    (quorum? fbas Q)))

(module+ test
  (test-case
    "quorum-of?"
    (check-true (quorum-of? fbas-1 1 (list 1 2 3)))
    (check-true (quorum-of? fbas-1 1 (list 1 2 3 4)))
    (check-true (quorum-of? fbas-1 1 (list 2 3 4)))
    (check-false (quorum-of? fbas-1 1 (list 1 2)))))

; nomination protocol

(define/contract (weight fbas p q)
  (-> fbas/c node/c node/c number?)
  (define slices
    (invariant-assertion
      (λ (s) (not (empty? s)))
      (hash-ref fbas p)))
  (define appearances
    (count
      (λ (l) (member q l))
      slices))
  (/ appearances (length slices)))

(module+ test
  (test-case
    "weight"
    (check-equal?
      (weight fbas-1 1 2) (/ 3 4))
    (check-equal?
      (weight fbas-2 1 4) 0)
    (check-equal?
      (weight fbas-1 1 1) (/ 3 4))))

; TODO define a nomination module that uses this as interface (and attach a contract to it):
(struct nomination-parameters (peers weight quorums))

(define/contract (neighbors fbas N n)
  (-> fbas/c (hash/c node/c number?) node/c list?)
  ; second parameter assign a number between 0 and 1 to each node
  (define peers
    (apply set-union (hash-ref fbas n)))
  (for/list
    ([m peers]
     #:when (< (hash-ref N m) (weight fbas n m)))
    m))

(module+ test
  (define N-1 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.1) (4 . 0.1))))
  (test-case
    "neighbors"
    (check-true
      (set=?
        (neighbors fbas-1 N-1 1)
        '(1 2 3 4)))))

(define/contract (leader fbas N P n)
  (-> fbas/c (hash/c node/c number?) (hash/c node/c number?) node/c node/c)
  (define neighbors-weights
    (for/list
      ([m (neighbors fbas N n)])
      `(,m . ,(hash-ref P m))))
  (if (empty? (neighbors fbas N n))
    -1
    (car
      (argmax
        cdr
        neighbors-weights))))

(module+ test
  (define P-1 (make-immutable-hash '((1 . 1) (2 . 2) (3 . 3) (4 . 4))))
  (test-case
    "leader"
    (check-equal?
      (leader fbas-1 N-1 P-1 1)
      4)
    (check-equal?
      (leader fbas-1 N-1 P-1 4)
      4)))

(define/contract (nomination-step fbas N P s)
  (-> fbas/c (hash/c node/c number?) (hash/c node/c number?) (hash/c node/c node/c) (hash/c node/c node/c))
  (for/hash ([(n v) (in-hash s)])
    (cond
      [(not (equal? v -1)) (values n v)]
      [(equal? (leader fbas N P n) n) (values n n)]
      [(equal? (leader fbas N P n) -1) (values n -1)]
      [else (values n (hash-ref s (leader fbas N P n)))])))

(define (s-0 fbas)
  (make-immutable-hash
    (zip (hash-keys fbas) (make-list (hash-count fbas) -1))))

(module+ test
  (test-case
    "nomination-step"
    (check-equal?
      (nomination-step fbas-1 N-1 P-1 (s-0 fbas-1))
      (make-immutable-hash '((1 . -1) (2 . -1) (3 . -1) (4 . 4))))))

(define (until-fixpoint f)
  (define (fixpoint-f v)
    (let ([fv (f v)])
      (if (equal? fv v)
        fv
        (fixpoint-f fv))))
  fixpoint-f)

(define (nomination-votes fbas N P)
  ((until-fixpoint (λ (t) (nomination-step fbas N P t))) (s-0 fbas)))

(module+ test
  (test-case
    "nomination"
    (check-equal?
      (nomination-votes fbas-1 N-1 P-1)
      (make-immutable-hash (zip (hash-keys fbas-1) (make-list 4 4))))))

; check whether a value has been accepted as nominated
(define/contract (accepted-nominated? fbas s)
  (-> fbas/c hash? boolean?)
  (define (voted-for v)
    (for/list
      ([(n w) (in-hash s)]
       #:when (equal? v w))
      n))
  (for/or ([v (hash-values s)])
    (and
      (not (equal? v -1))
      (quorum? fbas (voted-for v)))))

(module+ test
  (test-case
    "accepted-nominated?"
    (check-false
      (accepted-nominated? fbas-1 (nomination-step fbas-1 N-1 P-1 (s-0 fbas-1))))
    (check-true
      (accepted-nominated? fbas-1 (nomination-votes fbas-1 N-1 P-1)))))

; TODO multiple rounds of nomination
