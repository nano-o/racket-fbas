; We use the rosette/safe language to enable symbolic execution
; We use the sweet-exp adapter to enable infix syntax when we write logical formulas
#lang sweet-exp rosette/safe

(require
  syntax/parse/define
  "truth-tables.rkt"
  (for-syntax
    racket/syntax))

(provide
  verify-with-tvl-args
  verify-valid/tvl
  bv-to-3)

; we use 2 bits to represent a tvl value as a bitvector
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b11 2)) 't] ; #b11 is 't
    [(or (bveq b (bv #b01 2)) (bveq b (bv #b10 2))) 'b] ; #b01 and #b10 both represent 'b
    [(bveq b (bv #b00 2)) 'f])) ; #b00 is 'f

; given a function which accepts tvl values as argument and returns a Racket boolean truth value (i.e. #t or #r), verify that the function always returns #t
; this expands to code that returns a Rosette "solution"
(define-syntax-parser verify-with-tvl-args
  [(_ (f:id arg ...))
   (with-syntax
     ([(arg/bv ...) ; symbols for tvl symbolic variables
       (for/list ([arg (syntax->list #'(arg ...))])
         (format-id #'arg "~a/bv" (syntax->datum arg)))])
     #'(let () ; we use let to hide the following definitions from the outer scope
         (define-symbolic arg/bv ... (bitvector 2))
         (define arg (bv-to-3 arg/bv)) ...
         (verify
           (assert
             (f arg ...)))))])

(module+ test
  (require rackunit)
  (define (eq-1 p)
    (eq? (¬ (¬ p)) p))
  (define (eq-2 p)
    (eq? (¬ p) p))
  (check-false
    (sat?
      (verify-with-tvl-args (eq-1 p))))
  (check-true
    (sat?
      (verify-with-tvl-args (eq-2 p))))
  (define (eq-3 a b)
    (eq?
      {a ⊃ b}
      {(¬ a) ∨ b}))
  (define (eq-4 a b)
    (eq?
      {a ⊃ b}
      {(¬ b) ∨ a}))
  (check-false
    (sat?
      (verify-with-tvl-args (eq-3 p q))))
  (check-true
    (sat?
      (verify-with-tvl-args (eq-4 a b)))))

(define-syntax-parser verify-valid/tvl
  [(_ (f:id arg ...))
   #'(let ()
       ; TODO: is it to reuse arg like that?
       (define (g arg ...)
         (designated-value (f arg ...)))
       (verify-with-tvl-args (g arg ...)))])

(module+ test
  (define (f-1 p)
    {p ∨ (¬ p)}) ; valid
  (define (f-2 p)
    p) ; invalid
  (check-false
    (sat?
      (verify-valid/tvl (f-1 p))))
  (check-true
    (sat?
      (verify-valid/tvl (f-2 p)))))
