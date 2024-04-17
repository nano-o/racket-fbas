;; In this file we define functions (∧, ∨, ¬, etc.) that implement the logical operations of the three-valued logic

; We use the rosette language to enable symbolic execution
; We use the sweet-exp language mixin to enable infix operators in logical formulas
#lang sweet-exp rosette

(require
  syntax/parse/define
  (only-in racket for*/and)
  racket/stream
  racket/local
  (for-syntax
    racket/syntax))

(provide
  truth-values ; 't, 'b, and 'f
  ∧ ∨ ⇒ ⊃ ⇔ ≡ ; binary logical operations
  ¬ ◇ □ B ; unary logical operations
  ∧* ∨* ≡* ; nary logical operations
  designated-value? ; 't and 'b
  eval/3 ; evaluate a formula in an environment
  free-vars ; the set of free variables in a formula
  interpretations ; lazy stream of all possible assignements to the provided variables
  (for-syntax uops))

; NOTE => (defined by rosette) is not ⇒
; NOTE <=> (defined by rosette) is not ⇔

; The logical values are 't, 'b, and 'f (true, both, and false)
(define truth-values '(t b f))

(define uops '(¬ ◇ □ B))
(define bops '(∧ ∨ ¬ ⇒ ⊃ ⇔ ≡))
(define nops '(∧* ∨* ≡*))
; We also make the lists of operations available for macros:
(begin-for-syntax
  (define uops (list #'¬ #'◇ #'□ #'B))
  (define bops (list #'∧ #'∨ #'⇒ #'≡ #'⊃ #'⇔))
  (define nops (list #'∧* #'∨* #'≡*)))

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
             (length (car rows/datum)))]
     (with-syntax
         ([(arg ...)
           (for/list ([i (in-range num-inputs)])
             (format-id #'operation "arg-~a" i))])
       #'(define (operation arg ...)
         (case (list arg ...)
           [((value ...)) (quote result)] ...)))]))

; A macro to check that a procedure returns true no matter what 3vl values it's given
; Use e.g. like this for a function f that takes two arguments: (always-#t? f p q)
(define-syntax-parser for-3values*/and
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
      (for-3values*/and (test-eq p q r))))

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
      (for-3values*/and (test-eq p q r))))

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
      (for-3values*/and (test-expr-1 p q r)))
    (check-true
      (for-3values*/and (test-expr-2 p q r)))
    (check-false
      (for-3values*/and (test-expr-3 p q r)))
    (check-true
      (for-3values*/and (test-expr-4 p q r s)))))

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

;; Evaluator for formulas
;; TODO move to separate file?
#;(define (eval/3 env fmla)
  (match fmla
    [`(,uop ,subfmla) ((eval uop) (eval/3 env subfmla))]
    [`(,bop ,sub1 ,sub2) ((eval bop) (eval/3 env sub1) (eval/3 env sub2))]
    [`(,nop ,subfmlas ...) (apply (eval nop) (map (λ (f) (eval/3 env f)) subfmlas))]
    [v #:when (member v truth-values) v]
    [v #:when (symbol? v) (dict-ref env v)]))

; TODO does this need to be a macro?
(define-syntax make-evaluator
  (λ (stx)
   (with-syntax ([(uop ...) uops]
                 [(bop ...) bops]
                 [(nop ...) nops]
                 [eval-proc (format-id stx "~a" "eval/3")])
     #`(define (eval-proc env fmla)
         (match fmla
           [`(uop ,e) (uop (eval-proc env e))]
           ...
           [`(bop ,e1 ,e2) (bop (eval-proc env e1) (eval-proc env e2))]
           ...
           [`(nop ,e (... ...)) (apply nop (map (λ (e) (eval-proc env e)) e))] ; NOTE (... ...) is a quoted ellipsis
           ...
           [v #:when (member v truth-values)
              v]
           [v #:when (symbol? v)
              (dict-ref env v)])))))
(make-evaluator)

; (make-evaluator eval/3)

(define (free-vars fmla)
  (match fmla
    [`(,uop ,e) #:when (member uop uops)
                (free-vars e)]
    [`(,bop ,e1 ,e2) #:when (member bop bops)
                     (set-union (free-vars e1) (free-vars e2))]
    [`(,nop ,e ...) #:when (member nop nops)
                    (apply set-union (map free-vars e))]
    [v #:when (member v truth-values)
       (set)]
    [v #:when (symbol? v)
       (set v)]))

(module+ test
  (check-equal?
    (free-vars 'p)
    (set 'p))
  (check-equal?
    (free-vars '(∨ p q))
    (set 'p 'q))
  (check-equal?
    (free-vars '(∧* p q r))
    (set 'p 'q 'r))
  (check-equal?
    (free-vars '(∧ q (∨ p q)))
    (set 'p 'q))
  (check-equal?
    (free-vars '(∧ q (∨ p t)))
    (set 'p 'q))
  (check-equal?
    (free-vars '(∧ q (∨ p b)))
    (set 'p 'q))
  (check-equal?
    (free-vars '(∧ (¬ q) (∨ p t)))
    (set 'p 'q)))

(define (explore-stream f s)
  ; given an element of s, f must produce a stream
  (if (! (stream-empty? s))
    (stream-append
      (f (stream-first s))
      (stream-lazy (explore-stream f (stream-rest s))))
    (stream)))

; TODO why do we need this when we have always-#t? streams are very slow anyway
(define (interpretations vars)
  ; creates a lazy stream of all possible interpretations of the variables
  (define (cases v inter)
    (for/stream ([3val truth-values])
                (hash-set inter v 3val)))
  (match vars
    [`(,v)
      (cases v (hash))]
    [`(,v ,vars ...)
      (explore-stream ((curry cases) v) (interpretations vars))]))

; TODO stream of models, SAT, validity, equivalence of fmlas
