;; In this file we define functions (∧, ∨, ¬, etc.) that implement the logical operations of the three-valued logic

; We use the rosette/safe language to enable symbolic execution
; We use the sweet-exp language mixin to enable infix operators in logical formulas
#lang sweet-exp rosette/safe

(require
  syntax/parse/define
  (only-in racket for*/and)
  racket/local
  (for-syntax
    racket/syntax))

(provide
  ∧ ∨ ¬ ⇒ ⊃ ⇔ ≡ ◇ □ B ; These are the logical connectives
  ∧* ∨* ≡* ; versions of the connectives that take lists of logical values
  truth-values
  designated-value?)

; NOTE => (rosette) is not ⇒
; NOTE <=> (rosette) is not ⇔

; The logical values are 't, 'b, and 'f (true, both, and false)
(define truth-values '(t b f))

; 't and 'b are the designated values
(define (designated-value? v)
  (if (member v '(t b)) #t #f))

; Next we write a macro to make is easier to define truth tables
; We start with a syntax class for tvl values
(begin-for-syntax
  (define-syntax-class tvl-value
    #:description "a three-valued logic value (either 't, 'b, or 'f)"
    (pattern (~or* (~literal t) (~literal f) (~literal b)))))

; A macro to define truth tables:
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

; A macro to check an equivalence by exhaustive enumeration
(define-syntax-parser always-#t?
  [(_ (f:id arg ...))
   #`(for*/and ([arg truth-values] ...) ; NOTE the * in for* is crucial here
       (f arg ...))])

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

; A shorthand for writing big conjunctions:
(define (∧* . vs)
  (cond
    [(member 'f vs) 'f]
    [(member 'b vs) 'b]
    [else 't]))

(module+ test
  (require rackunit)

  (local
    [(define (test-eq p q r)
      (eq?
        {p ∧ {q ∧ r}}
        (∧* p q r)))]
    (check-true
      (always-#t? (test-eq p q r))))

  ; the empty conjunction:
  (check-equal? (∧*) 't))

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
(define (∨* . vs)
  (cond
    [(member 't vs) 't]
    [(member 'b vs) 'b]
    [else 'f]))

(module+ test
  (local
    [(define (test-eq p q r)
      (eq?
        {p ∨ {q ∨ r}}
        (∨* p q r)))]
    (check-true
      (always-#t? (test-eq p q r))))

  ; empty disjunction is 'f:
  (check-equal? (∨*) 'f))

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

; equivalence based on material implication
(define-truth-table {p ≡ q}
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f b]
  [f t f]
  [f b b]
  [f f t])

(define (≡* . vs)
  (cond
    [(and (member 't vs) (member 'f vs)) 'f]
    [(member 'b vs) 'b]
    [else 't]))

(module+ test
  (local
    [(define (test-expr-1 p q r)
       (eq? ; NOTE this is not true!
         (designated-value? (∧* {p ≡ q} {q ≡ r} {r ≡ p}))
         (designated-value? (∧* {p ⊃ q} {q ⊃ r} {r ⊃ p}))))
     (define (test-expr-2 p q r)
       (eq?
         (∧* {p ≡ q} {q ≡ r} {r ≡ p})
         (≡* p q r)))
     (define (test-expr-3 p q r)
       (or
         (not (designated-value? {{p ≡ q} ∧ {q ≡ r}}))
         (designated-value? {p ≡ r})))
     (define (test-expr-4 p q r s)
       (eq?
         (∧* {p ≡ q} {p ≡ s} {p ≡ r} {q ≡ r} {q ≡ s}  {r ≡ s})
         (≡* p q r s)))]
    (check-false
      (always-#t? (test-expr-1 p q r)))
    (check-true
      (always-#t? (test-expr-2 p q r)))
    (check-false
      (always-#t? (test-expr-3 p q r)))
    (check-true
      (always-#t? (test-expr-4 p q r s)))))

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

;; We now check some equation given in the book

(module+ test

; TODO: look at https://stackoverflow.com/questions/16571447/using-one-set-of-unit-tests-on-many-different-files-in-racket to run the same tests on both the rosette checker and the exhaustive checker

  (define-syntax-parser define-and-check-by-enumeration
    ; TODO: problem with that is `raco test` reports wrong line number
    [(_ (f:id arg ...) body:expr)
     #'(begin
         (define (f arg ...) body)
         (check-true
           (always-#t?
               (f arg ...))))])


  (define-and-check-by-enumeration (eq-18.3.1 p)
      (eq?
        (¬ (¬ p))
        p))
  (define-and-check-by-enumeration (eq-18.3.2 p q)
      (eq?
        {p ∨ q}
        (¬ {(¬ p) ∧ (¬ q)})))
  (define-and-check-by-enumeration (eq-18.3.3 p q)
      (eq?
        {p ∧ q}
        (¬ {(¬ p) ∨ (¬ q)})))
  (define-and-check-by-enumeration (eq-18.3.4 a b)
      (eq?
        {a ⊃ b}
        {(¬ a) ∨ b}))
  (define-and-check-by-enumeration (eq-18.3.5 p)
      (eq?
        {p ⊃ 'f}
        (¬ p)))
  (define-and-check-by-enumeration (eq-18.3.6.1 p q)
      (eq?
        {p ≡ q}
        {{p ⊃ q} ∧ {q ⊃ p}}))
  (define-and-check-by-enumeration (eq-18.3.6.2 p q)
      (eq?
        {p ≡ q}
        {{(¬ p) ∨ q} ∧ {p ∨ (¬ q)}}))

  (define-and-check-by-enumeration (eq-18.3.7.1 p q)
      (eq?
        {p ⇒ q}
        {(◇ p) ⊃ q}))
  (define-and-check-by-enumeration (eq-18.3.7.2 p q)
      (eq?
        {p ⇒ q}
        {(□ (¬ p)) ∨ q}))

  (define-and-check-by-enumeration (eq-18.3.8 p q)
      (eq?
        {p ⇔ q}
        {{p ⇒ q} ∧ {q ⇒ p}}))

  (define-and-check-by-enumeration (eq-18.3.9.1 p)
      (eq?
        (□ p)
        (¬ (◇ (¬ p)))))
  (define-and-check-by-enumeration (eq-18.3.9.2 p)
      (eq?
        (□ p)
        {(¬ p) ⇒ 'f}))

  (define-and-check-by-enumeration (eq-18.3.10.1 p)
      (eq?
        (◇ p)
        (¬ (□ (¬ p)))))
  (define-and-check-by-enumeration (eq-18.3.10.2 p)
      (eq?
        (◇ p)
        (¬ {p ⇒ 'f})))
  (define-and-check-by-enumeration (eq-18.3.10.3 p)
      (eq?
        (◇ p)
        {{p ⇒ 'f} ⇒ 'f}))

  (define-and-check-by-enumeration (eq-18.3.11.1 p)
      (eq?
        (B p)
        (◇ {p ∧ (¬ p)})))
  (define-and-check-by-enumeration (eq-18.3.11.2 p)
      (eq?
        (B p)
        {(◇ p) ∧ (◇ (¬ p))}))
  (define-and-check-by-enumeration (eq-18.3.11.3 p)
      (eq?
        (B p)
        {(◇ p) ∧ (¬ (□ p))}))

  (define-and-check-by-enumeration (eq-18.3.12 p)
      (eq?
        (□ (◇ p))
        (◇ p)))

  (define-and-check-by-enumeration (eq-18.3.13 p q)
      (eq?
        (◇ {p ⇒ q})
        {(◇ p) ⇒ (◇ q)}))

  (define-and-check-by-enumeration (eq-18.3.13.1 p q)
      (eq?
        (□ {p ∧ q})
        {(□ p) ∧ (□ q)}))
  (define-and-check-by-enumeration (eq-18.3.13.2 p q)
      (eq?
        (□ {p ∨ q})
        {(□ p) ∨ (□ q)}))
  (define-and-check-by-enumeration (eq-18.3.13.3 p q)
      (eq?
        (◇ {p ∧ q})
        {(◇ p) ∧ (◇ q)}))
  (define-and-check-by-enumeration (eq-18.3.13.4 p q)
      (eq?
        (◇ {p ∨ q})
        {(◇ p) ∨ (◇ q)}))

  (define-and-check-by-enumeration (eq-18.2.7.1 p q)
      (eq?
        {p ⊃ q}
        {(¬ q) ⊃ (¬ p)}))

  (define-and-check-by-enumeration (eq-18.4.12.1 p q r)
      (eq?
        {p ⊃ {q ⊃ r}}
        {{p ∧ q} ⊃ r}))
  (define-and-check-by-enumeration (eq-18.4.12.2 p q r)
      (eq?
        {p ⇒ {q ⇒ r}}
        {{p ∧ q} ⇒ r})))
