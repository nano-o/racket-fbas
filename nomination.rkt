#lang racket

(require "qset.rkt")
(provide
  nomination-votes
  accepted-nominated?
  weight
  num-leaders)

; nomination protocol

; weight in a qset

; This is how core computes weights, but it's not how it's defined in the
; whitepaper (see tests)

; NOTE the sum of the node's weights can be bigger than 1, but individual
; weights are between 0 and 1.

; The weight of a node is the probability of picking a node if we recursively
; pick a number of nodes/qsets equal to the qset threshold uniformly at
; random.
(define (weight q p)
  ;(-> qset? node/c number?)
  (define es
    (elems q))
  (define (contains-p? e)
    (cond
      [(qset? e) (qset-member? e p)]
      [else (eqv? p e)]))
  (define e ; element in which p first occurs
    (findf contains-p? es))
  (define r
    (/ (qset-threshold q) (length es)))
  (cond
    [(qset? e)
     (* (weight e p) r)]
    [(not e) 0] ; node is not in the qset
    [else r]))

; This is how the weight of a node is defined in the whitepaper: we count the
; number of slices in which the node appears, and we divide by the total number
; of slices.
(define (whitepaper-weight qs p)
  (define expanded (expand qs))
  (define n-in
    (length (filter (λ (s) (set-member? s p)) (set->list expanded))))
  (define total (length (set->list expanded)))
  (/ n-in total))

; Note that the two weight computations may give different results.
; If one counts as in the whitepaper, a deeply nested qset may give rise to a
; lot of slices, which will decrease the weight of another non-deeply nested
; qset at the same level.
(module+ test
  (require
    (submod "qset.rkt" test)
    rackunit)
  (provide
    (all-defined-out)
    (all-from-out (submod "qset.rkt" test)))
  (test-case
    "weight"
    (check-equal? (weight qset-1 '1) (/ 2 3))
    (check-equal? (weight qset-1 '1) (whitepaper-weight qset-1 '1))
    (check-equal? (weight qset-5 '1) (/ 4 9))
    (check-equal? (weight qset-5 '1) (whitepaper-weight qset-5 '1))
    (check-equal? (weight qset-6 '1) (/ 1 3))
    ; NOTE the two computations do not agree here:
    (check-not-equal? (weight qset-6 '1) (whitepaper-weight qset-6 '1))
    (check-equal? (weight qset-6 'A) (/ 1 2))
    ; NOTE the two computations do not agree here:
    (check-not-equal? (weight qset-6 'A) (whitepaper-weight qset-6 'A))
    (check-equal? (weight qset-6 'A) (/ 1 2))
    (check-equal? (whitepaper-weight qset-6 'A) (/ 1 4))))

; a draw associates numbers between 0 and 1 to nodes
(define draw/c
  (hash/c node/c number?))

(define/contract (neighbors n qset N)
  (-> node/c qset? draw/c set?)
  (set-union
    (set n) ; a node is always in its neighbors set (it has weight 1 implicitly)
    (for/set
      ([m (qset-members qset)]
       #:when (< (hash-ref N m) (weight qset m)))
      m)))

(module+ test
  (define N1 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.1))))
  (define N2 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.9))))
  (test-case
    "neighbors"
    (check-true
      (set=?
        (neighbors 1 qset-1 N1)
        (set 1 2 3)))
    (check-true
      (set=?
        (neighbors 1 qset-1 N2)
        (set 1 2)))))

(define/contract (leader n qset N P)
  (-> node/c qset? draw/c draw/c node/c)
  (define ns (neighbors n qset N))
  (cond
    [(set-empty? ns) #f] ; never happens if a node is always in its own neighbors set
    [else
      (define priority
        (for/list
          ([m ns])
          `(,m . ,(hash-ref P m))))
      (car
        (argmax
          cdr
          priority))]))

(define/contract (num-leaders conf N P)
  (-> conf/c draw/c draw/c number?)
  (for/fold ([num 0]) ([(n qset) (in-hash conf)])
    (if (eqv? n (leader n qset N P))
      (+ num 1)
      num)))

(module+ test
  (define P1 (make-immutable-hash '((1 . 0.1) (2 . 0.2) (3 . 0.3))))
  (test-case
    "leader"
    (check-equal?
      (leader 1 qset-1 N1 P1)
      3)
    (check-equal?
      (leader 1 qset-1 N2 P1)
      2)))

(define state/c
  (hash/c node/c node/c))

(define/contract (nomination-step conf N P s)
  (-> conf/c draw/c draw/c state/c state/c)
  (for/hasheqv ([(n v) (in-hash s)])
    (cond
      [(not (equal? v #f)) (values n v)]
      [(not (hash-has-key? conf n)) (values n v)]
      [else
        (define l (leader n (hash-ref conf n) N P))
        (cond
          [(equal? l n) (values n n)]
          [(not l) (values n #f)]
          [else (values n (hash-ref s l))])])))

(define (zip l1 l2)
  (map cons l1 l2))

(define (s-0 conf)
  (define members
    (set->list (conf-members conf)))
  (make-immutable-hasheqv
    (zip members (make-list (length members) #f))))

(module+ test
  (define conf0
    (make-immutable-hasheqv
      (zip '(1 2 3) (make-list 3 qset-1))))
  (test-case
    "nomination-step"
    (check-equal?
      (nomination-step conf0 N1 P1 (s-0 conf0))
      (make-immutable-hasheqv '((1 . #f) (2 . #f) (3 . 3))))))

(define (until-fixpoint f)
  (define (fixpoint-f v)
    (let ([fv (f v)])
      (if (equal? fv v)
        fv
        (fixpoint-f fv))))
  fixpoint-f)

; The votes that are cast in the first round of nomination, assuming the network is perfect.
(define (nomination-votes conf N P)
  ((until-fixpoint (λ (s) (nomination-step conf N P s))) (s-0 conf)))

(module+ test
  (test-case
    "nomination"
    (check-equal?
      (nomination-votes conf0 N1 P1)
      (make-immutable-hasheqv (zip (hash-keys conf0) (make-list 3 3))))))

; Whether a value has been accepted as nominated at the end of the first round of nomination.
(define/contract (accepted-nominated? conf s)
  (-> conf/c state/c boolean?)
  (define (voted-for v)
    (for/set
      ([(n w) (in-hash s)]
       #:when (equal? v w))
      n))
  (for/or ([v (list->set (hash-values s))])
    (and
      (not (equal? v #f))
      (quorum? conf (voted-for v)))))

(module+ test
  (test-case
    "accepted-nominated?"
    (check-false
      (accepted-nominated? conf0 (nomination-step conf0 N1 P1 (s-0 conf0))))
    (check-true
      (accepted-nominated? conf0 (nomination-votes conf0 N1 P1)))))
