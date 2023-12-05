#lang rosette

(require rosette/lib/synthax)
(require "tvl.rkt")
(require rackunit)

(define-symbolic x y (bitvector 2))

; let's sythesize expressions
; as we can check, diamond and box cannot be expressed in terms of and, or, and not

(define-grammar (basic-expr/1 x)
  [expr
    (choose
      x
      (and/tvl (expr) (expr))
      (or/tvl (expr) (expr))
      (not/tvl (expr))
      (box (expr)))]) ; NOTE we need diamond or box as primitive

(define-grammar (basic-expr/2 x y)
  [expr
    (choose
      x y
      (and/tvl (expr) (expr))
      (or/tvl (expr) (expr))
      (not/tvl (expr))
      (box (expr)))]) ; NOTE we need diamond or box as primitive

(module+ diamond
  (define (my-diamond x)
    (basic-expr/1 x #:depth 4))

  (define (check-diamond f x)
    (assert
      (eq?
        (f x)
        (diamond x))))

  (define sol-diamond
    (synthesize
      #:forall (list x)
      #:guarantee (check-diamond my-diamond (bv-to-3 x))))

  (check-true (sat? sol-diamond)))

(module+ box

  (define-grammar (box-expr x)
    [expr
      (choose
        x 't 'f
        (and/tvl (expr) (expr))
        (or/tvl (expr) (expr))
        (dimp (expr) (expr))
        (not/tvl (expr))
        ; (box (expr))
        (box (expr)))])

  (define (my-box x)
    (box-expr x #:depth 2))

  (define (check-box f x)
    (assert
      (eq?
        (f x)
        (box x))))

  (define sol-box
    (synthesize
      #:forall (list x)
      #:guarantee (check-box my-box (bv-to-3 x))))

  (check-true (sat? sol-box))
  (print-forms sol-box))

(module+ dimp
  (define (my-dimp x y)
    (basic-expr/2 x y #:depth 3))

  (define (check-dimp f x y)
    (assert
      (eq?
        (f x y)
        (dimp x y))))

  (define sol-dimp
    (synthesize
      #:forall (list x y)
      #:guarantee (check-dimp my-dimp (bv-to-3 x) (bv-to-3 y))))

  (check-true (sat? sol-dimp)))

(module+ cimp

  (define-grammar (cimp-expr x y)
    [expr
      (choose
        x y
        (and/tvl (expr) (expr))
        ; (or/tvl (expr) (expr))
        ; (dimp (expr) (expr))
        (not/tvl (expr))
        (box (expr))
        #; (box (expr)))])

  (define (my-cimp x y)
    (cimp-expr x y #:depth 3))

  (define (check-cimp f x y)
    (assert
      (eq?
        (f x y)
        (cimp x y))))

  (define sol-cimp
    (synthesize
      #:forall (list x y)
      #:guarantee (check-cimp my-cimp (bv-to-3 x) (bv-to-3 y))))

  (check-true (sat? sol-cimp))
  (print-forms sol-cimp))


(module+ diff

  (define (check-diff f x y)
    (assert
      (eq?
        (f x y)
        (diff x y))))

  (define-grammar (diff-expr x y)
    [expr
      (choose
        x y
        (and/tvl (expr) (expr))
        ; (or/tvl (expr) (expr))
        (dimp (expr) (expr))
        #; (not/tvl (expr))
        ; (box (expr))
        #; (box (expr)))])

  (define (my-diff x y)
    (diff-expr x y #:depth 2))

  (define sol-diff
    (synthesize
      #:forall (list x y)
      #:guarantee (check-diff my-diff (bv-to-3 x) (bv-to-3 y))))

  (check-true (sat? sol-diff))
  (print-forms sol-diff)

  (define (check-diff-impl x y)
    (define vx (bv-to-3 x))
    (define vy (bv-to-3 y))
    (assert
      (eq?
        (diff vx vy)
        (and/tvl (dimp vx vy) (dimp vy vx)))))

  (check-true
    (unsat?
      (verify (check-diff-impl x y)))))

(module+ ciff
  (define (check-ciff f x y)
    (assert
      (eq?
        (f x y)
        (ciff x y))))

  (define-grammar (ciff-expr x y)
    [expr
      (choose
        x y
        (and/tvl (expr) (expr))
        ; (or/tvl (expr) (expr))
        ; (dimp (expr) (expr))
        (cimp (expr) (expr))
        ; (not/tvl (expr))
        ; (box (expr))
        #;(diamond (expr)))])

  (define (my-ciff x y)
    (ciff-expr x y #:depth 2))

  (define sol-ciff
    (synthesize
      #:forall (list x y)
      #:guarantee (check-ciff my-ciff (bv-to-3 x) (bv-to-3 y))))

  (check-true (sat? sol-ciff))
  (print-forms sol-ciff))

(module+ equiv
  (define (check-equiv f x y)
    (assert
      (eq?
        (f x y)
        (equiv x y))))

  (define-grammar (equiv-expr x y)
    [expr
      (choose
        x y
        (and/tvl (expr) (expr))
        (or/tvl (expr) (expr))
        ; (dimp (expr) (expr))
        ; (cimp (expr) (expr))
        (not/tvl (expr))
        ; (box (expr))
        (diamond (expr)))])

  (define (my-equiv x y)
    ; no solution with depth 4
    ; did not terminate in a reasonable time with depth 5
    (equiv-expr x y #:depth 5))

  (define sol-equiv
    (synthesize
      #:forall (list x y)
      #:guarantee (check-equiv my-equiv (bv-to-3 x) (bv-to-3 y))))

  (check-true (sat? sol-equiv))
  (print-forms sol-equiv))
