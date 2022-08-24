#lang racket

; TODO using list sets is a bit confusing, especially since the library
; functions don't check that the representation invariant is satisfied

(provide
  node/c
  fbas/c
  quorum?
  quorum-of?
  ;nomination-votes
  ;accepted-nominated?
  )

(define (zip l1 l2)
  (map cons l1 l2))

; a node is something for which eqv? is semantic equivalence, i.e. interned symbols, numbers, and characters.
(define node/c
  (or/c (and/c symbol? symbol-interned?) number? char?))

; A FBAS is a map from nodes to sets of slices
(define fbas/c
  (and/c
    immutable?
    hash?))

(module+ test
  (require rackunit)

  ; examples of fbas

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
      (hash-set (hash-set (threshold-fbas 4 5) 1 slices-1) 5 slices-2)))

  (test-case
    "fbas/c"
    (for ([f (list fbas-1 fbas-2 fbas-3)])
      (fbas/c f))))

; The quorum-set generation tool included in core uses validators array
; TODO: check what the tool in core actually does...
; The core tool first sorts validators by quality (first) and home domain (second)
; Validators of the same home domain cannot have a different quality, and they are grouped as if their home domain had the quality.
(define (quality/c c)
  (case c
    [('critical 'high 'med 'low) #t]
    [else #f]))
(struct validator-description (quality home-domain))
(define validators-array/c
  (hash/c node/c validator-description?))

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
