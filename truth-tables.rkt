;; In this file we define the semantics of logical operations of the three-valued logic by giving their truth tables

; We use the rosette/safe language to enable symbolic execution
; We use the sweet-exp adapter to enable infix syntax when we write logical formulas
#lang sweet-exp rosette/safe

(require
  syntax/parse/define
  (for-syntax racket/syntax))

; these are the logical connectives
(provide
  ∧ ∨ ¬ ⇒ ⊃ ⇔ ≡ ◇ □ B
  and/tvl* or/tvl*
  designated-value)

; The logical values are 't, 'b, and 'f (true, both, and false)
(define truth-values
  '(t b f))

; Next we write a macro to make is easier to define truth tables
; We start with a syntax class for tvl values
(begin-for-syntax
  (define-syntax-class tvl-value
    #:description "a three-valued logic value (either 't, 'b, or 'f)"
    (pattern (~or* (~literal t) (~literal f) (~literal b)))))

; 't and 'b are the designated values
(define (designated-value v)
  (define (to-bool v)
    (if v #t #f))
  (to-bool (member v '(t b))))

; the macro
(define-syntax (define-truth-table stx)
  (syntax-parse stx
    [(_ (operation:id _ ...)
        [value:tvl-value ... result:tvl-value] ...)
     #:do [(define rows/datum
             (for/list ([l (syntax->list #'((value ...) ...))])
               (for/list ([e (syntax->list l)])
                 (syntax->datum e))))
           (define num-inputs
             (length (car rows/datum)))
           (define combinations
             (apply cartesian-product
                    (make-list num-inputs '(t b f))))
           (define has-all-combinations
             (set=? combinations rows/datum))]
     #:fail-when
       (not (for/and ([l rows/datum])
              (equal? (length l) num-inputs)))
       "some rows have different sizes"
     #:fail-when
       (not has-all-combinations)
       (format "missing combinations of inputs: ~a" (set-subtract combinations rows/datum))
     (with-syntax
         ([(arg ...)
           (for/list ([i (in-range num-inputs)])
             (format-id #'operation "arg-~a" i))])
       #'(define (operation arg ...)
         (case (list arg ...)
           [((value ...)) (quote result)] ...
           [else 'error])))]))

; Now we define the truth tables

(define-truth-table {p ∧ q}
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f f])

; a shorthand for writing big conjunctions
(define (and/tvl* . vs)
  (cond
    [(member 'f vs) 'f]
    [(member 'b vs) 'b]
    [else 't]))

(module+ test
  (require rackunit)
  (require (only-in racket for/and))
  (check-true
    (for/and ([p truth-values]
              [q truth-values]
              [r truth-values])
      (eq?
        {p ∧ {q ∧ r}}
        (and/tvl* p q r)))))

(define-truth-table {p ∨ q}
  [t t t]
  [t b t]
  [t f t]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b b]
  [f f f])

; a shorthand for writing big disjunctions
(define (or/tvl* . vs)
  (cond
    [(member 't vs) 't]
    [(member 'b vs) 'b]
    [else 'f]))

(module+ test
  (check-true
    (for/and ([p truth-values]
              [q truth-values]
              [r truth-values])
      (eq?
        {p ∨ {q ∨ r}}
        (or/tvl* p q r)))))

(define-truth-table {p ⇒ q}
  [t t t]
  [t b b]
  [t f f]
  [b t t]
  [b b b]
  [b f f]
  [f b t]
  [f t t]
  [f f t])

; material implication
(define-truth-table {p ⊃ q}
  [t t t]
  [t b b]
  [t f f]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b t]
  [f f t])

(define-truth-table {p ⇔ q}
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f t])

; equivalence based on material implication
(define-truth-table {p ≡ q}
  ; if one is both then both
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f b]
  [f t f]
  [f b b]
  [f f t])

(module+ test
  (check-true
    (for/and ([p truth-values]
              [q truth-values]
              [r truth-values])
      (eq?
        {{p ≡ q} ∧ {q ≡ r}}
        {{p ⊃ q} ∧ {{q ⊃ r} ∧ {r ⊃ p}}}))))

(define-truth-table (¬ p)
  [t f]
  [b b]
  [f t])

(define-truth-table (□ p)
  [t t]
  [b f]
  [f f])

(define-truth-table (◇ p)
  [t t]
  [b t]
  [f f])

(define-truth-table (B p)
  [t f]
  [b t]
  [f f])
