#lang sweet-exp racket/base
(require rosette/safe
         rosette/lib/synthax
         syntax/parse/define)
(require
  (for-syntax
    racket/syntax
    syntax/to-string))

(provide
  bv-to-3
  ∧ ∨ ¬ ⇒ ⊃ ⇔ ≡ ◇ □)

;; We start by defining the truth tables
;; Our logical values are 't, 'b, and 'f

;; First we create a macro to make it easier to write down truth tables

(begin-for-syntax
  (define-syntax-class tvl-value
    #:description "a three-valued logic value (either 't, 'b, or 'f)"
    (pattern (~or* (~literal t) (~literal f) (~literal b)))))

(define-syntax (define-truth-table stx)
  (syntax-parse stx
    [(_ operation:id
        [value:tvl-value ... result:tvl-value] ...)
     #:do [(define rows/datum
             (for/list ([l (syntax->list #'((value ...) ...))])
               (for/list ([e (syntax->list l)])
                 (syntax->datum e))))
           (define num-inputs
             (length (car rows/datum)))
           (define num-inputs-in-each-row
             (for/and ([l rows/datum])
               (equal? (length l) num-inputs)))
           (define combinations
             (apply cartesian-product
                    (make-list num-inputs '(t b f))))
           (define has-all-combinations
             (set=? combinations rows/datum))]
     #:fail-when (not num-inputs-in-each-row) "some rows have different sizes"
     #:fail-when (not has-all-combinations) (format "missing combinations of inputs: ~a" (set-subtract combinations rows/datum))
     (with-syntax
         ([(arg ...)
           (for/list ([i (in-range num-inputs)])
             (format-id #'operation "arg-~a" i))])
       #'(define (operation arg ...)
         (case (list arg ...)
           [((value ...)) (quote result)] ...
           [else 'error])))]))

;; Now we define the truth tables

(define-truth-table ∧
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f f])

(define-truth-table ∨
  [t t t]
  [t b t]
  [t f t]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b b]
  [f f f])

(define-truth-table ⇒
  [t t t]
  [t b b]
  [t f f]
  [b t t]
  [b b b]
  [b f f]
  [f b t]
  [f t t]
  [f f t])

(define-truth-table ⊃ ; material implication
  [t t t]
  [t b b]
  [t f f]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b t]
  [f f t])

(define-truth-table ⇔
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f t])

(define-truth-table ≡ ; equivalence based on material implication
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f b]
  [f t f]
  [f b b]
  [f f t])

(define-truth-table ¬
  [t f]
  [b b]
  [f t])

(define-truth-table □
  [t t]
  [b f]
  [f f])

(define-truth-table ◇
  [t t]
  [b t]
  [f f])

(define-truth-table B
  [t f]
  [b t]
  [f f])

;; Now we define a series of equivalences taken from the book

;; We first define a macro to define and check an equivalence at once

; We create the test module
(module+ test
  (require rackunit))

; we use 2 bits to represent a tvl value as a bitvector
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b11 2)) 't] ; #b11 is 't
    [(or (bveq b (bv #b01 2)) (bveq b (bv #b10 2))) 'b] ; #b01 and #b10 both represent 'b
    [(bveq b (bv #b00 2)) 'f])) ; #b00 is 'f

(define-syntax-parser check-equivalence
  [(_ (eq-to-check:id arg ...) lhs:expr rhs:expr)
   (with-syntax
     ([(arg/bv ...) ; symbols for symbolic variables
       (for/list ([arg (syntax->list #'(arg ...))])
         (format-id #'eq-to-check "~a/bv" (syntax->datum arg)))])
       #`(module+ test
         (let () ; we use let to hide the following definitions from the outer scope
           (define (eq-to-check arg ...) (eq? lhs rhs))
           (define-symbolic arg/bv ... (bitvector 2))
           (define arg (bv-to-3 arg/bv)) ...
           (define result
             (verify
               (assert
                 (eq-to-check arg ...))))
           (define cex
             (begin
               (if (sat? result)
                 (model result)
                 #f)))
           (define msg
             (if (sat? result)
               (format
                 #,(format "~a is falsified by the valuation ~~a" (syntax->string #'(eq-to-check)))
                 cex)
               #f))
           (check-true (unsat? result) msg))))])

;; Figure 18.3

; note that, below, using curly braces instead of parentheses enable infix syntax

(check-equivalence (eq-18.3.1 p)
    (¬ (¬ p))
    p)

(check-equivalence (eq-18.3.2 p q)
    {p ∨ q}
    (¬ {(¬ p) ∧ (¬ q)}))

(check-equivalence (eq-18.3.3 p q)
    {p ∧ q}
    (¬ {(¬ p) ∨ (¬ q)}))

(check-equivalence (eq-18.3.4 a b)
    {a ⊃ b}
    {(¬ a) ∨ b})

(check-equivalence (eq-18.3.5 p)
    {p ⊃ 'f}
    (¬ p))

(check-equivalence (eq-18.3.6.1 p q)
    {p ≡ q}
    {{p ⊃ q} ∧ {q ⊃ p}})
(check-equivalence (eq-18.3.6.2 p q)
    {p ≡ q}
    {{(¬ p) ∨ q} ∧ {p ∨ (¬ q)}})

(check-equivalence (eq-18.3.7.1 p q)
    {p ⇒ q}
    {(◇ p) ⊃ q})
(check-equivalence (eq-18.3.7.2 p q)
    {p ⇒ q}
    {(□ (¬ p)) ∨ q})

(check-equivalence (eq-18.3.8 p q)
    {p ⇔ q}
    {{p ⇒ q} ∧ {q ⇒ p}})

(check-equivalence (eq-18.3.9.1 p)
    (□ p)
    (¬ (◇ (¬ p))))
(check-equivalence (eq-18.3.9.2 p)
    (□ p)
    {(¬ p) ⇒ 'f})

(check-equivalence (eq-18.3.10.1 p)
    (◇ p)
    (¬ (□ (¬ p))))
(check-equivalence (eq-18.3.10.2 p)
    (◇ p)
    (¬ {p ⇒ 'f}))
(check-equivalence (eq-18.3.10.3 p)
    (◇ p)
    {{p ⇒ 'f} ⇒ 'f})

(check-equivalence (eq-18.3.11.1 p)
    (B p)
    (◇ {p ∧ (¬ p)}))
(check-equivalence (eq-18.3.11.2 p)
    (B p)
    {(◇ p) ∧ (◇ (¬ p))})
(check-equivalence (eq-18.3.11.3 p)
    (B p)
    {(◇ p) ∧ (¬ (□ p))})

(check-equivalence (eq-18.3.12 p)
    (□ (◇ p))
    (◇ p))

(check-equivalence (eq-18.3.13 p q)
    (◇ {p ⇒ q})
    {(◇ p) ⇒ (◇ q)})

(check-equivalence (eq-18.3.13.1 p q)
    (□ {p ∧ q})
    {(□ p) ∧ (□ q)})
(check-equivalence (eq-18.3.13.2 p q)
    (□ {p ∨ q})
    {(□ p) ∨ (□ q)})
(check-equivalence (eq-18.3.13.3 p q)
    (◇ {p ∧ q})
    {(◇ p) ∧ (◇ q)})
(check-equivalence (eq-18.3.13.4 p q)
    (◇ {p ∨ q})
    {(◇ p) ∨ (◇ q)})

(check-equivalence (eq-19.2.7.1 p q)
    {p ⊃ q}
    {(¬ q) ⊃ (¬ p)})

;; Now we check whether we can construct ⊃ from ⇒ and other modalities (see the discussion in Section 18.2.3) using an expression of fixed maximum depth

(module+ test
  (define-grammar (dimp-and-modalities p q)
    [expr
      (choose
        p q 'f
        {(expr) ⇒ (expr)}
        (¬ (expr)) ; we also throw in negation, which does not seem to help
        (◇ (expr))
        (□ (expr)))])

  (define (my-mimp p q)
    (dimp-and-modalities p q #:depth 4))

  (define (check-is-mimp expr p q)
    (assert
      (eq?
        (expr p q)
        (⊃ p q))))

  (define-symbolic p/bv q/bv (bitvector 2))

  (define my-mimp-solution
    (synthesize
      #:forall (list p/bv q/bv)
      #:guarantee (check-is-mimp my-mimp (bv-to-3 p/bv) (bv-to-3 q/bv))))

  ;; We cannot construct ⊃ using expression generated by the grammar with depth at most 4:
  (check-false (sat? my-mimp-solution)))
