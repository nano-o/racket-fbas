#lang sweet-exp racket

;; Examples from the book

(require
  (for-syntax
    racket/set
    (only-in "truth-tables.rkt" free-vars))
  "truth-tables.rkt"
  syntax/parse/define)

;; Those formulas should be equivalent (in the sense of evaluating to the same thing in all environments):

(define-for-syntax eqs
  (make-hash))

(define-syntax-parser check-eq-by-enumeration
  [(_ f1 f2)
   (define vars
     (set->list
       (set-union
         (free-vars (eval (syntax->datum #'f1)))
         (free-vars (eval (syntax->datum #'f2))))))
   (with-syntax
     ([(v ...) vars]
      [(3val ...) (generate-temporaries vars)])
     #'(for*/and ([3val truth-values] ...)
                 (define env
                   (make-hash `((v . ,3val) ...)))
                 (eq?
                   (eval/3 env f1)
                   (eval/3 env f2))))])

(module+ test
  (require rackunit)
  (check-true (check-eq-by-enumeration '(¬ (¬ p)) 'p))
  (check-false (check-eq-by-enumeration '(¬ (¬ q)) 'p)))

(define-syntax-parser define-equiv-fmlas
  [(stx name f1 f2)
   #;(hash-set!
     eqs
     (syntax->datum #'name)
     (cons (eval (syntax->datum #'f1)) (eval (syntax->datum #'f2))))
     #`(begin
       (define name
         (cons f1 f2))
       (module+ test
         #,(syntax/loc #'stx (check-true (check-eq-by-enumeration f1 f2)))))])

(define-equiv-fmlas eq-18.3.1
                    '(¬ (¬ p))
                    'p)

(define-equiv-fmlas eq-18.3.2
                    '{p ∨ q}
                    '(¬ {(¬ p) ∧ (¬ q)}))
(define-equiv-fmlas eq-18.3.3
                    '{p ∧ q}
                    '(¬ {(¬ p) ∨ (¬ q)}))
(define-equiv-fmlas eq-18.3.4
                    '{a ⊃ b}
                    '{(¬ a) ∨ b})
(define-equiv-fmlas eq-18.3.5
                    '{p ⊃ f}
                    '(¬ p))
(define-equiv-fmlas eq-18.3.6.1
                    '{p ≡ q}
                    '{{p ⊃ q} ∧ {q ⊃ p}})
(define-equiv-fmlas eq-18.3.6.2
                    '{p ≡ q}
                    '{{(¬ p) ∨ q} ∧ {p ∨ (¬ q)}})

(define-equiv-fmlas eq-18.3.7.1
                    '{p ⇒ q}
                    '{(◇ p) ⊃ q})
(define-equiv-fmlas eq-18.3.7.2
                    '{p ⇒ q}
                    '{(□ (¬ p)) ∨ q})

(define-equiv-fmlas eq-18.3.8
                    '{p ⇔ q}
                    '{{p ⇒ q} ∧ {q ⇒ p}})

(define-equiv-fmlas eq-18.3.9.1
                    '(□ p)
                    '(¬ (◇ (¬ p))))
(define-equiv-fmlas eq-18.3.9.2
                    '(□ p)
                    '{(¬ p) ⇒ f})

(define-equiv-fmlas eq-18.3.10.1
                    '(◇ p)
                    '(¬ (□ (¬ p))))
(define-equiv-fmlas eq-18.3.10.2
                    '(◇ p)
                    '(¬ {p ⇒ f}))
(define-equiv-fmlas eq-18.3.10.3
                    '(◇ p)
                    '{{p ⇒ f} ⇒ f})

(define-equiv-fmlas eq-18.3.11.1
                    '(B p)
                    '(◇ {p ∧ (¬ p)}))
(define-equiv-fmlas eq-18.3.11.2
                    '(B p)
                    '{(◇ p) ∧ (◇ (¬ p))})
(define-equiv-fmlas eq-18.3.11.3
                    '(B p)
                    '{(◇ p) ∧ (¬ (□ p))})

(define-equiv-fmlas eq-18.3.12
                    '(□ (◇ p))
                    '(◇ p))

(define-equiv-fmlas eq-18.3.13
                    '(◇ {p ⇒ q})
                    '{(◇ p) ⇒ (◇ q)})

(define-equiv-fmlas eq-18.3.13.1
                    '(□ {p ∧ q})
                    '{(□ p) ∧ (□ q)})
(define-equiv-fmlas eq-18.3.13.2
                    '(□ {p ∨ q})
                    '{(□ p) ∨ (□ q)})
(define-equiv-fmlas eq-18.3.13.3
                    '(◇ {p ∧ q})
                    '{(◇ p) ∧ (◇ q)})
(define-equiv-fmlas eq-18.3.13.4
                    '(◇ {p ∨ q})
                    '{(◇ p) ∨ (◇ q)})

(define-equiv-fmlas eq-18.2.7.1
                    '{p ⊃ q}
                    '{(¬ q) ⊃ (¬ p)})

(define-equiv-fmlas eq-18.4.12.1
                    '{p ⊃ {q ⊃ r}}
                    '{{p ∧ q} ⊃ r})
(define-equiv-fmlas eq-18.4.12.2
                    '{p ⇒ {q ⇒ r}}
                    '{{p ∧ q} ⇒ r})
