#lang racket

(define (zip l1 l2)
  (map cons l1 l2))
; an FBAS is a set of nodes along with their slices
; example:

(define (fbas-1)
  (define 3-out-of-4
    (list->set
      (map list->set
           (combinations '(1 2 3 4) 3))))
  (make-hash (zip '(1 2 3 4) (make-list 4 3-out-of-4))))

(define/contract (has-slice-in? fbas p Q)
  (-> hash? number? set? boolean?)
  (define slices
    (hash-ref fbas p))
  (for/or ([s slices])
    (subset? s Q)))

(define (quorum-of? fbas p Q)
  (-> hash? number? set? boolean?)
  (and
    (has-slice-in? fbas p Q)
    (for/and ([q Q])
      (has-slice-in? fbas q Q))))

(define (weight fbas p q)
  (define slices
    (hash-ref fbas p))
  (define appearances
    (count
      (λ (s) (set-member? s q))
      (set->list slices)))
  (/ appearances (set-count slices)))
