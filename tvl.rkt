#lang racket/base
(require rosette/safe)

(provide and/tvl or/tvl not/tvl equiv dimp cimp diff ciff diamond box dbimp bv-to-3)

;; We start by defining the truth tables
;; Our logical values are 't, 'b, and 'f

(define (and/tvl a b)
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 'b]
    [((b . b)) 'b]
    [((b . f)) 'f]
    [((f . t)) 'f]
    [((f . b)) 'f]
    [((f . f)) 'f]))

(define (or/tvl a b)
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 't]
    [((t . f)) 't]
    [((b . t)) 't]
    [((b . b)) 'b]
    [((b . f)) 'b]
    [((f . t)) 't]
    [((f . b)) 'b]
    [((f . f)) 'f]))

(define (dimp a b)
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 't]
    [((b . b)) 'b]
    [((b . f)) 'f]
    [((f . b)) 't]
    [((f . t)) 't]
    [((f . f)) 't]))

(define (cimp a b)
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 't]
    [((b . b)) 'b]
    [((b . f)) 'b]
    [((f . t)) 't]
    [((f . b)) 't]
    [((f . f)) 't]))

(define (diff a b) ; double equivalence
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 'b]
    [((b . b)) 'b]
    [((b . f)) 'f]
    [((f . t)) 'f]
    [((f . b)) 'f]
    [((f . f)) 't]))

(define (ciff a b) ; curly equivalence
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 'b]
    [((b . b)) 'b]
    [((b . f)) 'b]
    [((f . t)) 'f]
    [((f . b)) 'b]
    [((f . f)) 't]))

(define (dbimp a b) ; double overbar implication
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'f]
    [((t . f)) 'f]
    [((b . t)) 't]
    [((b . b)) 't]
    [((b . f)) 'f]
    [((f . t)) 't]
    [((f . b)) 't]
    [((f . f)) 't]))

(define (equiv a b)
  (case `(,a . ,b)
    [((t . t)) 't]
    [((t . b)) 'f]
    [((t . f)) 'f]
    [((b . t)) 'f]
    [((b . b)) 't]
    [((b . f)) 'f]
    [((f . t)) 'f]
    [((f . b)) 'f]
    [((f . f)) 't]))

(define (not/tvl a)
  (case a
    [(t) 'f]
    [(b) 'b]
    [(f) 't]))

(define (box a)
  (case a
    [(t) 't]
    [(b) 'f]
    [(f) 'f]))

(define (diamond a)
  (case a
    [(t) 't]
    [(b) 't]
    [(f) 'f]))

;; we use 2 bits to represent a value in our logic:
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b10 2)) 't] ; #b10 is 't
    [(or (bveq b (bv #b00 2)) (bveq b (bv #b11 2))) 'b] ; #b11 and #b00 both represent 'b
    [(bveq b (bv #b01 2)) 'f])) ; #b01 is 'f

(define (designated-value v)
  (member v '(t b)))

(module+ test
  (require rackunit)

  (define-symbolic x y (bitvector 2))
  (define vx (bv-to-3 x))
  (define vy (bv-to-3 y))

  (define (check-cimp a b)
    (assert
      (eq?
        (cimp a b)
        (or/tvl (not/tvl a) b))))

  (check-true
    (unsat?
      (verify (check-cimp vx vy))))

  (define (check-dimp a b)
    (assert
      (eq?
        (dimp a b)
        (cimp (diamond a) b))))

  (check-true
    (unsat?
      (verify (check-dimp vx vy))))

  (define (check-ciff a b)
    (assert
      (eq?
        (ciff a b)
        (and/tvl (cimp a b) (cimp b a)))))

  (check-true
    (unsat?
      (verify (check-ciff vx vy))))

  (define (modus-ponens p q r)
    (eq?
      (designated-value (dimp (and/tvl p q) r))
      (designated-value (dimp p (dimp q r)))))

  (define-symbolic bvp bvq bvr (bitvector 2))
  (define p (bv-to-3 bvp))
  (define q (bv-to-3 bvq))
  (define r (bv-to-3 bvr))
  (check-true
    (unsat?
      (verify
        (assert (modus-ponens p q r))))))
