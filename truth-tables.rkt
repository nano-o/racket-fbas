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

;; First we create a macro to make it easier to write down truth tables

;; The logical values are 't, 'b, and 'f (true, both, and false)
(begin-for-syntax
  (define-syntax-class tvl-value
    #:description "a three-valued logic value (either 't, 'b, or 'f)"
    (pattern (~or* (~literal t) (~literal f) (~literal b)))))

(define (to-bool v)
  (if v #t #f))

;; 't and 'b are the designated values
(define (designated-value v)
  (to-bool (member v '(t b))))

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

;; Now we define the truth tables

; TODO: and/tvl*, or/tvl* (might help Rosette not to have huge nested conjuctions and disjunctions)
; TODO: add tests for and/tvl* and or/tvl*

(define-truth-table {p ∧ q}
  ; if one if 'f, then 'f
  ; else if one if 'b, then 'b
  ; else 't
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f f]
  [f t f]
  [f b f]
  [f f f])

(define (and/tvl* . vs)
  (cond
    [(member 'f vs) 'f]
    [(member 'b vs) 'b]
    [else 't]))

(module+ test
  ; we use 2 bits to represent a tvl value as a bitvector
  (define (bv-to-3 b)
    (cond
      [(bveq b (bv #b11 2)) 't] ; #b11 is 't
      [(or (bveq b (bv #b01 2)) (bveq b (bv #b10 2))) 'b] ; #b01 and #b10 both represent 'b
      [(bveq b (bv #b00 2)) 'f])) ; #b00 is 'f
  (define-symbolic p/bv q/bv r/bv (bitvector 2))
  (define p (bv-to-3 p/bv))
  (define q (bv-to-3 q/bv))
  (define r (bv-to-3 r/bv))
  (define sol
    (verify
      (assert
        (eq?
          {p ∧ {q ∧ r}}
          (and/tvl* p q r)))))
  (if (sat? sol)
    (println sol)
    (println "unsat")))

(define-truth-table {p ∨ q}
  ; if one if 'f, then 'f
  ; else if one if 'b, then 'b
  ; else 't
  [t t t]
  [t b t]
  [t f t]
  [b t t]
  [b b b]
  [b f b]
  [f t t]
  [f b b]
  [f f f])

(define (or/tvl* . vs)
  (cond
    [(member 't vs) 't]
    [(member 'b vs) 'b]
    [else 'f]))

(module+ test
  (define sol2
    (verify
      (assert
        (eq?
          {p ∨ {q ∨ r}}
          (or/tvl* p q r)))))
  (if (sat? sol2)
    (println sol2)
    (println "unsat")))

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
  [t t t]
  [t b b]
  [t f f]
  [b t b]
  [b b b]
  [b f b]
  [f t f]
  [f b b]
  [f f t])

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
