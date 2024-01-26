; We use the rosette language to enable symbolic execution
; We use the sweet-exp adapter to enable infix syntax when we write logical formulas
#lang sweet-exp rosette

(require
  syntax/parse/define
  "truth-tables.rkt"
  (for-syntax
    racket/syntax))

(provide
  verify-with-tvl-args
  verify-valid/tvl
  bv-to-3
  verify-valid/at-runtime)

; we use 2 bits to represent a tvl value as a bitvector
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b11 2)) 't] ; #b11 is 't
    [(or (bveq b (bv #b01 2)) (bveq b (bv #b10 2))) 'b] ; #b01 and #b10 both represent 'b
    [(bveq b (bv #b00 2)) 'f])) ; #b00 is 'f

(define-namespace-anchor anchor)
(define ns (namespace-anchor->namespace anchor))

; given a function which accepts tvl values as argument and returns a Racket boolean truth value (i.e. #t or #r), verify that the function always returns #t
; this expands to code that returns a Rosette "solution"
(define-syntax-parser verify-with-tvl-args
  [(_ (f:id arg ...))
   (with-syntax
     ([(arg/bv ...) ; symbols for tvl symbolic variables
       (generate-temporaries #'(arg ...))])
     #'(let () ; we use let to hide the following definitions from the outer scope
         (define-symbolic arg/bv ... (bitvector 2))
         (define arg (bv-to-3 arg/bv)) ...
         (verify
           (assert
             (f arg ...)))))])

; version that's not a macro
(define (verify-with-tvl-args/at-runtime vars eqn)
  (define bv-vars
    (for/list ([v vars]) (string->symbol (format "~a/bv" v))))
  (define code
    `(begin
       (define-symbolic ,@bv-vars (bitvector 2))
       (define-values
         ,vars
         (values ,@(for/list ([v bv-vars]) `(bv-to-3 ,v))))
       (verify (assert ,eqn))))
  (eval code ns))

(define (verify-valid/at-runtime vars fmla)
  (define bv-vars
    (for/list ([v vars]) (string->symbol (format "~a/bv" v))))
  (define code
    `(begin
       (define-symbolic ,@bv-vars (bitvector 2))
       (define-values
         ,vars
         (values ,@(for/list ([v bv-vars]) `(bv-to-3 ,v))))
       (define fmla ,fmla)
       (verify (assert (|| (eq? fmla 't) (eq? fmla 'b))))))
  ; (pretty-print code)
  (eval code ns))

(module+ test-runtime
  (require rackunit)
  (check-false
    (sat?
      (verify-with-tvl-args/at-runtime '(p) '(eq? (¬ (¬ p)) p))))
  (check-true
    (sat?
      (verify-with-tvl-args/at-runtime '(p) '(eq? (¬ p) p))))
  (check-false
    (sat?
      (verify-with-tvl-args/at-runtime '(a b)
        '(eq?
           (⊃ a b)
           (∨ (¬ a) b))))))

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
