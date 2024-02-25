#lang rosette

(require
  "truth-tables.rkt"
  syntax/parse/define)

(provide
  valid/3?
  SAT)

;; We provide a validity checker for tvl formulas.

; we use 2 bits to represent a tvl value as a bitvector
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b11 2)) 't] ; #b11 is 't
    [(or (bveq b (bv #b01 2)) (bveq b (bv #b10 2))) 'b] ; #b01 and #b10 both represent 'b
    [(bveq b (bv #b00 2)) 'f])) ; #b00 is 'f

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
