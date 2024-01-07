#lang racket/base
(require rosette/safe)
(require (for-syntax racket/syntax))
(require syntax/parse/define)

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

;; Now we define a series of equivalences taken from the book

(define (mimp-is-not-a-or-b a b)
  (eq?
    (mimp a b)
    (or/tvl (not/tvl a) b)))

(define (dimp-using-mimp a b)
  (eq?
    (dimp a b)
    (mimp (diamond a) b)))

;; We now verify those equivalences using Rosette

; we use 2 bits to represent a tvl value as a bitvector:
(define (bv-to-3 b)
  (cond
    [(bveq b (bv #b10 2)) 't] ; #b10 is 't
    [(or (bveq b (bv #b00 2)) (bveq b (bv #b11 2))) 'b] ; #b11 and #b00 both represent 'b
    [(bveq b (bv #b01 2)) 'f])) ; #b01 is 'f

(module+ test
  (require rackunit)

  ;; first we define a macro to simplify writing checks

  (define-syntax-parser check
    [(_ (eq-to-check:id arg ...))
     (with-syntax
       ([(arg/bv ...)
         (for/list ([arg (syntax->list #'(arg ...))])
           (format-id #'eq-to-check "~a/bv" (syntax->datum arg)))])
       #`(let () ; we use let to hide the following definitions from the outer scope
           (define-symbolic arg/bv ... (bitvector 2))
           (define arg (bv-to-3 arg/bv)) ...
           (check-true
             (unsat?
               (verify
                 (assert
                   (eq-to-check arg ...)))))))])

  ;; now the checks

  (check (mimp-is-not-a-or-b a b))
  (check (dimp-using-mimp a b)))


; (module+ test

  ; (define-symbolic x y (bitvector 2))
  ; (define vx (bv-to-3 x))
  ; (define vy (bv-to-3 y))

  ; ; TODO: macro for this stuff?

  ; (define (check-mimp a b)
    ; (assert
      ; (mimp-is-not-a-or-b a b)))

  ; (check-true
    ; (unsat?
      ; (verify (check-mimp vx vy))))

  ; (define (check-dimp a b)
    ; (assert
      ; (eq?
        ; (dimp a b)
        ; (mimp (diamond a) b))))

  ; (check-true
    ; (unsat?
      ; (verify (check-dimp vx vy))))

  ; (define (check-miff a b)
    ; (assert
      ; (eq?
        ; (miff a b)
        ; (and/tvl (mimp a b) (mimp b a)))))

  ; (check-true
    ; (unsat?
      ; (verify (check-miff vx vy))))

  ; (define (check-8.2.3.6 p q)
    ; ; this Item 6 of Remark 8.2.3 in three.pdf
    ; (assert
      ; (eq?
        ; (diamond (dimp p q))
        ; (dimp (diamond p) (diamond q)))))

  ; (check-true
    ; (unsat?
      ; (verify (check-8.2.3.6 vx vy))))

  ; (define (check-8.2.7.1 x y)
    ; (assert
      ; (eq?
        ; (mimp x y)
        ; (mimp (not/tvl y) (not/tvl x)))))

  ; (check-true
    ; (unsat?
      ; (verify (check-8.2.7.1 vx vy))))

  ; (define (check-8.2.7.2 x y)
    ; (assert
      ; (eq?
        ; (dimp x y)
        ; (dimp (not/tvl y) (not/tvl x)))))

  ; (check-true
    ; (sat?
      ; (verify (check-8.2.7.2 vx vy))))

  ; ; with 3 variables

  ; (define-symbolic bvp bvq bvr (bitvector 2))
  ; (define p (bv-to-3 bvp))
  ; (define q (bv-to-3 bvq))
  ; (define r (bv-to-3 bvr))

  ; ; modus-ponens

  ; (define (modus-ponens p q r)
    ; ; TODO is this modus-ponens?
    ; (eq?
      ; (designated-value (dimp (and/tvl p q) r))
      ; (designated-value (dimp p (dimp q r)))))

  ; (check-true
    ; (unsat?
      ; (verify
        ; (assert (modus-ponens p q r)))))

  ; (define (check-8.4.12.1 p q r)
    ; (assert
      ; (eq?
        ; (mimp (and/tvl p q) r)
        ; (mimp p (mimp q r)))))

  ; (check-true
    ; (unsat?
      ; (verify
        ; (check-8.4.12.1 p q r))))

  ; (define (check-8.4.12.2 p q r)
    ; (assert
      ; (eq?
        ; (dimp (and/tvl p q) r)
        ; (dimp p (dimp q r)))))

  ; (check-true
    ; (unsat?
      ; (verify
        ; (check-8.4.12.2 p q r)))) )


