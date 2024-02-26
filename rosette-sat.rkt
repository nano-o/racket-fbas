#lang rosette

(require
  ; racket/trace
  "truth-tables.rkt"
  syntax/parse/define)

(provide
  valid/3?
  interpret/3
  SAT?)

;; We provide a validity checker for tvl formulas.

; we use 2 bits to represent a tvl value as a bitvector
; we can think of this as first bit for false and second bit for true
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b01 2)) 't]
    [(|| (bveq b (bv #b11 2)) (bveq b (bv #b00 2))) 'b]
    [(bveq b (bv #b10 2)) 'f]))

; interprets a formula as a Rosette term
(define-syntax-parser make-interpreter
  [(_
     #:name f
     #:unary (uo ...)
     #:binary (bo ...)
     #:nary (no ...))
  #`(define (f fmla)
      (match fmla
        [`(eq? ,e1 ,e2) (if (equal? (f e1) (f e2)) 't 'f)] ; TODO is that okay?
        [`(uo ,e) (uo (f e))]
        ...
        [`(bo ,e1 ,e2) (bo (f e1) (f e2))]
        ...
        [`(no ,e (... ...)) (apply no (map f e))] ; NOTE (... ...) is a quoted ellipsis
        ...
        [v #:when (member v truth-values)
          v]
        [v #:when (symbol? v)
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

; This is the example from https://emina.github.io/rosette/
(define (interpret/2 formula)
  (match formula
    [`(&& ,expr ...) (apply && (map interpret/2 expr))]
    [`(|| ,expr ...) (apply || (map interpret/2 expr))]
    [`(=> ,e1 ,e2) (=> (interpret/2 e1) (interpret/2 e2))]
    [`(<=> ,e1 ,e2) (<=> (interpret/2 e1) (interpret/2 e2))]
    [`(! ,expr)     (! (interpret/2 expr))]
    [lit #:when (boolean? lit) lit]
    [lit            (constant lit boolean?)]))

(define (SAT? formula)
  (begin
    (clear-vc!)
    (clear-terms!)
    (solve (assert (interpret/2 formula)))))

; (SAT? '(¬ q))
; (SAT? 'p)
; (SAT? `(∧ r o (∨ s e (¬ t)) t (¬ e)))
