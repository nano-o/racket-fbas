#lang racket/base
(require rosette/safe)
(require (for-syntax racket/syntax))
(require syntax/parse/define)
(require (for-syntax syntax/to-string))

(provide and/tvl or/tvl not/tvl equiv dimp mimp diff miff diamond box/tvl dbimp bv-to-3)

;; We start by defining the truth tables
;; Our logical values are 't, 'b, and 'f

; Something is valid if it's 't or 'b in all interpretations
(define (designated-value v)
  (member v '(t b)))

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

(define-truth-table and/tvl
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f f])

(define-truth-table or/tvl
  [t t t]
  [t b t]
  [t f t]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b b]
  [f f f])

(define-truth-table dimp
  ; this is ⇒
  [t t t]
  [t b b]
  [t f f]
  [b t t]
  [b b b]
  [b f f]
  [f b t]
  [f t t]
  [f f t])

(define-truth-table mimp
  ; this is ⊃, i.e. material implication
  [t t t]
  [t b b]
  [t f f]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b t]
  [f f t])

(define-truth-table diff ; double equivalence
  ; this is ⇔
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f t])

(define-truth-table miff ; equivalence using material implication
  ; this is ≡
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f b]
  [f t f]
  [f b b]
  [f f t])

(define-truth-table dbimp ; double overbar implication
  [t t t]
  [t b f]
  [t f f]
  [b t t]
  [b b t]
  [b f f]
  [f t t]
  [f b t]
  [f f t])

(define-truth-table equiv
  [t t t]
  [t b f]
  [t f f]
  [b t f]
  [b b t]
  [b f f]
  [f t f]
  [f b f]
  [f f t])

(define-truth-table not/tvl
  [t f]
  [b b]
  [f t])

(define-truth-table box/tvl
  [t t]
  [b f]
  [f f])

(define-truth-table diamond
  [t t]
  [b t]
  [f f])

(define-truth-table B
  [t f]
  [b t]
  [f f])

;; Now we define a series of equivalences taken from the book

;; We define a macro to define and check an equivalence at once

; We create the test module
(module+ test
  (require rackunit))

; we use 2 bits to represent a tvl value as a bitvector
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b10 2)) 't] ; #b10 is 't
    [(or (bveq b (bv #b00 2)) (bveq b (bv #b11 2))) 'b] ; #b11 and #b00 both represent 'b
    [(bveq b (bv #b01 2)) 'f])) ; #b01 is 'f

(define-syntax-parser define-and-check
  [(_ (eq-to-check:id arg ...) body:expr)
   (with-syntax
     ([(arg/bv ...)
       (for/list ([arg (syntax->list #'(arg ...))])
         (format-id #'eq-to-check "~a/bv" (syntax->datum arg)))])
       #`(module+ test
         (define (eq-to-check arg ...) body)
         (let () ; we use let to hide the following definitions from the outer scope
           (define-symbolic arg/bv ... (bitvector 2))
           (define arg (bv-to-3 arg/bv)) ...
           (define result
             (verify
               (assert
                 (eq-to-check arg ...))))
           (define cex
             (begin
               (if (sat? result)
                 (for/hash ([(k v) (in-hash (model result))])
                   (values k (bv-to-3 v)))
                 #f)))
           (define msg
             (if (sat? result)
               (format
                 #,(format "(~a does not hold. ~~a falsifies (~a))" (syntax->string #'(eq-to-check)) (syntax->string #'body))
                 cex)
               #f))
           (check-true (unsat? result) msg))))])

;; Figure 25

;; TODO: a reader to read in equations formatted as in the book?

(define-and-check (eq-25.1 p)
  (eq? (not/tvl (not/tvl p)) p))

(define-and-check (eq-25.2 p q)
  (eq? (or/tvl p q) (not/tvl (and/tvl (not/tvl p) (not/tvl q)))))

(define-and-check (eq-25.3 p q)
  (eq? (and/tvl p q) (not/tvl (or/tvl (not/tvl p) (not/tvl q)))))

(define-and-check (eq-25.4 a b)
  (eq? (mimp a b) (or/tvl (not/tvl a) b)))

(define-and-check (eq-25.5 p)
  (eq? (mimp p 'f) (not/tvl p)))

(define-and-check (eq-25.6 p q)
  (eq? (miff p q) (and/tvl (mimp p q) (mimp q p))))

(define-and-check (eq-25.7.1 p q)
  (eq? (dimp p q) (mimp (diamond p) q)))
(define-and-check (eq-25.7.2 p q)
  (eq? (dimp p q) (or/tvl (box/tvl (not/tvl p)) q)))

(define-and-check (eq-25.8 p q)
  (eq? (diff p q) (and/tvl (dimp p q) (dimp q p))))

(define-and-check (eq-25.9.1 p)
  (eq? (box/tvl p) (not/tvl (diamond (not/tvl p)))))
(define-and-check (eq-25.9.2 p)
  (eq? (box/tvl p) (dimp (not/tvl p) 'f)))

(define-and-check (eq-25.10.1 p)
  (eq? (diamond p) (not/tvl (box/tvl (not/tvl p)))))
(define-and-check (eq-25.10.2 p)
  (eq? (diamond p) (not/tvl (dimp p 'f))))
(define-and-check (eq-25.10.3 p)
  (eq? (diamond p) (dimp (dimp p 'f) 'f)))

(define-and-check (eq-25.11.1 p)
  (eq? (B p) (diamond (and/tvl p (not/tvl p)))))
(define-and-check (eq-25.11.2 p)
  (eq? (B p) (and/tvl (diamond p) (diamond (not/tvl p)))))
(define-and-check (eq-25.11.3 p)
  (eq? (B p) (and/tvl (diamond p) (not/tvl (box/tvl p)))))

(define-and-check (eq-25.12 p)
  (eq? (box/tvl (diamond p)) (diamond p)))

(define-and-check (eq-25.13 p q)
  (eq? (diamond (dimp p q)) (dimp (diamond p) (diamond q))))
