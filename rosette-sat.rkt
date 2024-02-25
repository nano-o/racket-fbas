#lang rosette

(require
  "truth-tables.rkt"
  syntax/parse/define)

(provide
  valid/3?
  SAT)

;; We provide a validity checker for tvl formulas.

; we use 2 bits to represent a tvl value as a bitvector
; we can think of this as first bit for false and second bit for true
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b01 2)) 't]
    [(or (bveq b (bv #b11 2)) (bveq b (bv #b00 2))) 'b]
    [(bveq b (bv #b10 2)) 'f]))

(define (3-to-bv v)
  (case v
    [(t) (bv #b01 2)]
    [(f) (bv #b10 2)]
    [(b) (bv #b11 2)]))

; interprets a formula as a Rosette term
(define-syntax-parser make-interpreter
  [(_
     #:name f
     #:unary (uo ...)
     #:binary (bo ...)
     #:nary (no ...))
  #`(define (f fmla)
      (match fmla
        [`(uo ,e) (uo (f e))]
        ...
        [`(bo ,e1 ,e2) (bo (f e1) (f e2))]
        ...
        [`(no ,e (... ...)) (no (map f e))] ; NOTE (... ...) is a quoted ellipsis
        ...
        [v
          #:when (member v truth-values)
          (3-to-bv v)]
        [v
          #:when (symbol? v)
          (bv-to-3 (constant v (bitvector 2)))]))])

(make-interpreter
  #:name interpret/3
  #:unary (¬ ◇ □ B)
  #:binary (∧ ∨ ¬ ⇒ ⊃ ⇔ ≡ ◇ □ B)
  #:nary (∧* ∨* ≡*))

(define (valid/3? fmla)
  (begin
    ; (gc-terms!)
    (clear-vc!)
    (clear-terms!)
    (verify (assert (designated-value? (interpret/3 fmla))))))

; (interpret '(¬ p))
; (with-vc (interpret '(¬ p)))
; (valid/3? '(∨ p (¬ p)))
; (valid/3? '(∨ p p))
; (vc)
; (terms)

; This is the example from https://emina.github.io/rosette/
(define (interpret/2 formula)
  (match formula
    [`(∧ ,expr ...) (apply && (map interpret/2 expr))]
    [`(∨ ,expr ...) (apply || (map interpret/2 expr))]
    [`(¬ ,expr)     (! (interpret/2 expr))]
    [lit            (constant lit boolean?)]))

(define (SAT formula)
  (begin
    (clear-vc!)
    (clear-terms!)
    (solve (assert (interpret/2 formula)))))

; (SAT '(¬ q))
; (SAT 'p)
; (SAT `(∧ r o (∨ s e (¬ t)) t (¬ e)))
