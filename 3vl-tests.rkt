#lang sweet-exp racket

;; Examples from the book

(require
  "truth-tables.rkt"
  "rosette-sat.rkt"
  "3to2.rkt"
  racket/local
  (only-in rosette unsat?)
  syntax/parse/define)

(define (check-eq-by-enumeration f1 f2)
  (define (eq-in-env? env)
    (eq? (eval/3 env f1) (eval/3 env f2)))
  (define vars (set->list (set-union (free-vars f1) (free-vars f2))))
  (stream-andmap eq-in-env? (interpretations vars)))

(module+ test
  (require rackunit))

(define-syntax-parser check-equation
; we need this to be a macro to get the line numbers right in the output of `raco test`
  [(stx (~optional (~and #:invalid (~bind [invalid #t]))) f1 f2)
     (with-syntax ([check (if (attribute invalid) #'check-false #'check-true)])
       #`(module+ test
           (local [(define lhs f1) (define rhs f2)]
             #,(syntax/loc #'stx (check (check-eq-by-enumeration lhs rhs) "check failed according to eval/3"))
             #,(syntax/loc #'stx (check (unsat? (SAT? `(! ,(equiv-fmlas? lhs rhs)))) "check failed according to SAT?"))
             #,(syntax/loc #'stx (check (unsat? (valid/3? `(eq? ,lhs ,rhs))) "check failed according to valid/3")))))])

; TODO check-valid

(check-equation
  '{p ∧ q}
  '(∧* p q))

(check-equation
  '{p ∧ {q ∧ r}}
  '(∧* p q r))

(check-equation
  '{{p ∧ {q ∧ r}} ∧ s}
  '(∧* p q r s))

(check-equation
  '{{p ≡ q} ∧ {{p ≡ r} ∧ {q ≡ r}}}
  '(≡* p q r))

(check-equation
  '{p ∨ {q ∨ r}}
  '(∨* p q r))

(check-equation ; eq-18.3.1
  '(¬ (¬ p))
  'p)

(check-equation ; eq-18.3.2
  '{p ∨ q}
  '(¬ {(¬ p) ∧ (¬ q)}))
(check-equation ; eq-18.3.3
  '{p ∧ q}
  '(¬ {(¬ p) ∨ (¬ q)}))
(check-equation ; eq-18.3.4
  '{a ⊃ b}
  '{(¬ a) ∨ b})
(check-equation ; eq-18.3.5
  '{p ⊃ f}
  '(¬ p))
(check-equation ; eq-18.3.6.1
  '{p ≡ q}
  '{{p ⊃ q} ∧ {q ⊃ p}})
(check-equation ; eq-18.3.6.2
  '{p ≡ q}
  '{{(¬ p) ∨ q} ∧ {p ∨ (¬ q)}})

(check-equation ; eq-18.3.7.1
  '{p ⇒ q}
  '{(◇ p) ⊃ q})
(check-equation ; eq-18.3.7.2
  '{p ⇒ q}
  '{(□ (¬ p)) ∨ q})

(check-equation ; eq-18.3.8
  '{p ⇔ q}
  '{{p ⇒ q} ∧ {q ⇒ p}})

(check-equation ; eq-18.3.9.1
  '(□ p)
  '(¬ (◇ (¬ p))))
(check-equation ; eq-18.3.9.2
  '(□ p)
  '{(¬ p) ⇒ f})

(check-equation ; eq-18.3.10.1
  '(◇ p)
  '(¬ (□ (¬ p))))
(check-equation ; eq-18.3.10.2
  '(◇ p)
  '(¬ {p ⇒ f}))
(check-equation ; eq-18.3.10.3
  '(◇ p)
  '{{p ⇒ f} ⇒ f})

(check-equation ; eq-18.3.11.1
  '(B p)
  '(◇ {p ∧ (¬ p)}))
(check-equation ; eq-18.3.11.2
  '(B p)
  '{(◇ p) ∧ (◇ (¬ p))})
(check-equation ; eq-18.3.11.3
  '(B p)
  '{(◇ p) ∧ (¬ (□ p))})

(check-equation ; eq-18.3.12
  '(□ (◇ p))
  '(◇ p))

(check-equation ; eq-18.3.13
  '(◇ {p ⇒ q})
  '{(◇ p) ⇒ (◇ q)})

(check-equation ; eq-18.3.13.1
  '(□ {p ∧ q})
  '{(□ p) ∧ (□ q)})
(check-equation ; eq-18.3.13.2
  '(□ {p ∨ q})
  '{(□ p) ∨ (□ q)})
(check-equation ; eq-18.3.13.3
  '(◇ {p ∧ q})
  '{(◇ p) ∧ (◇ q)})
(check-equation ; eq-18.3.13.4
  '(◇ {p ∨ q})
  '{(◇ p) ∨ (◇ q)})

(check-equation ; eq-18.2.7.1
  '{p ⊃ q}
  '{(¬ q) ⊃ (¬ p)})
(check-equation #:invalid ; eq-18.2.7.2
  '{p ⇒ q}
  '{(¬ q) ⇒ (¬ p)})

(check-equation ; eq-18.4.12.1
  '{p ⊃ {q ⊃ r}}
  '{{p ∧ q} ⊃ r})
(check-equation ; eq-18.4.12.2
  '{p ⇒ {q ⇒ r}}
  '{{p ∧ q} ⇒ r})

(check-equation #:invalid
  '{{p ≡ q} ∧ {q ≡ r}}
  '{{{p ⇒ q} ∧ {q ⇒ r}} ∧ {r ⇒ p}})
(check-equation #:invalid
  '{{p ≡ q} ∧ {q ≡ r}}
  '(∧* {p ⇒ q} {q ⇒ r} {r ⇒ p}))
(check-equation #:invalid
  '{{p ≡ q} ∧ {q ≡ r}}
  '{{{p ⊃ q} ∧ {q ⊃ r}} ∧ {r ⊃ p}})
(check-equation #:invalid
  '{{p ≡ q} ∧ {q ≡ r}}
  '(∧* {p ⊃ q} {q ⊃ r} {r ⊃ p}))

; TODO
; check validity:
  ; (check-true (valid? '(≡ p (¬ (¬ p)))))

  ; (define test-fmla-2 '(≡ (∨ p q) (¬ (∧ (¬ p) (¬ q)))))
  ; (check-true (valid? test-fmla-2))

  ; (define test-fmla-3 '(≡ (∧ p q) (¬ (∨ (¬ p) (¬ q)))))
  ; (check-true (valid? test-fmla-3))

  ; (define test-fmla-4 '(∧ (∨ (¬ p) p) (∨ p (¬ p))))
  ; (check-true (valid? test-fmla-4))

  ; (define test-fmla-5 '(∨ p (¬ p)))
  ; (check-true (valid? test-fmla-5))

  ; (define test-fmla-6 '(∧ p (¬ p)))
  ; (check-false (valid? test-fmla-6))

  ; (define test-fmla-7 '(∧* (∨* (¬ p) p) (∨* p (¬ p))))
  ; (check-true (valid? test-fmla-7))

  ; (check-true (equiv? '{≡ p  q} '{∧ {∨ (¬ p)  q} {∨ p (¬ q)}})))

;; Now we check whether we can construct ⊃ from ⇒ and other modalities using an expression of fixed maximum depth
(module+ dimp-from-mimp-test
  (require
    rosette
    rosette/lib/synthax
    (only-in "rosette-sat.rkt" bv-to-3)
    rackunit)

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

  (define dimp-from-mimp-solution
    (synthesize
      #:forall (list p/bv q/bv)
      #:guarantee (check-is-mimp my-mimp (bv-to-3 p/bv) (bv-to-3 q/bv))))

  ;; We cannot construct ⊃ using expression generated by the grammar with depth at most 4:
  (check-false (sat? dimp-from-mimp-solution)))

; (module+ test
  ; (require (submod ".." dimp-from-mimp-test)))
