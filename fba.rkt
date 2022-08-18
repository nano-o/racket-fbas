#lang racket

(provide
  quorum-of?
  weight
  nomination)

(define (zip l1 l2)
  (map cons l1 l2))

; an FBAS is a map from nodes to sets of slices
; TODO: check there are no duplicate slices, at least one slice, etc.?
(define fbas/c
  (hash/c number? (*list/c (*list/c number?))))

(module+ test
  (require rackunit)
  (provide (all-defined-out))

  (define 3-out-of-4
    (combinations '(1 2 3 4) 3))

  (define/contract fbas-1
    fbas/c
    (make-immutable-hash (zip '(1 2 3 4) (make-list 4 3-out-of-4))))

  (define/contract fbas-2
    fbas/c
    (let ([slices
            (combinations '(1 2 3) 2)])
      (hash-set fbas-1 1 slices))))

(define/contract (has-slice-in? fbas p Q)
  (-> fbas/c number? list? boolean?)
  (define slices
    (hash-ref fbas p))
  (for/or ([s slices])
    (subset? s Q)))

(define (quorum-of? fbas p Q)
  (-> fbas/c number? list? boolean?)
  (and
    (has-slice-in? fbas p Q)
    (for/and ([q Q])
      (has-slice-in? fbas q Q))))

(module+ test
  (test-case
    "quorum-of?"
    (check-true (quorum-of? fbas-1 1 (list 1 2 3)))
    (check-true (quorum-of? fbas-1 1 (list 1 2 3 4)))
    (check-true (quorum-of? fbas-1 1 (list 2 3 4)))
    (check-false (quorum-of? fbas-1 1 (list 1 2)))))

(define/contract (weight fbas p q)
  (-> fbas/c number? number? number?)
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

; nomination protocol

(define/contract (neighbors fbas N n)
  (-> fbas/c (hash/c number? number?) number? list?)
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
  (-> fbas/c (hash/c number? number?) (hash/c number? number?) number? number?)
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
  (-> fbas/c (hash/c number? number?) (hash/c number? number?) (hash/c number? number?) (hash/c number? number?))
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

(define (nomination fbas N P)
  ((until-fixpoint (λ (t) (nomination-step fbas N P t))) (s-0 fbas)))

(module+ test
  (test-case
    "nomination"
    (check-equal?
      (nomination fbas-1 N-1 P-1)
      (make-immutable-hash (zip (hash-keys fbas-1) (make-list 4 4))))))
