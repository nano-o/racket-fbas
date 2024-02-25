#lang sweet-exp racket

;; Examples from the book

;; Those formulas should be equivalent (in the sense of evaluating to the same thing in all environments):

(define eq-18.3.1
  (cons '(¬ (¬ p))
        'p))

(define eq-18.3.2
    (cons
      '{p ∨ q}
      '(¬ {(¬ p) ∧ (¬ q)})))
(define eq-18.3.3
    (cons
      '{p ∧ q}
      '(¬ {(¬ p) ∨ (¬ q)})))
(define eq-18.3.4
    (cons
      '{a ⊃ b}
      '{(¬ a) ∨ b}))
(define eq-18.3.5
    (cons
      '{p ⊃ 'f}
      '(¬ p)))
(define eq-18.3.6.1
    (cons
      '{p ≡ q}
      '{{p ⊃ q} ∧ {q ⊃ p}}))
(define eq-18.3.6.2
    (cons
      '{p ≡ q}
      '{{(¬ p) ∨ q} ∧ {p ∨ (¬ q)}}))

(define eq-18.3.7.1
    (cons
      '{p ⇒ q}
      '{(◇ p) ⊃ q}))
(define eq-18.3.7.2
    (cons
      '{p ⇒ q}
      '{(□ (¬ p)) ∨ q}))

(define eq-18.3.8
    (cons
      '{p ⇔ q}
      '{{p ⇒ q} ∧ {q ⇒ p}}))

(define eq-18.3.9.1
    (cons
      '(□ p)
      '(¬ (◇ (¬ p)))))
(define eq-18.3.9.2
    (cons
      '(□ p)
      '{(¬ p) ⇒ 'f}))

(define eq-18.3.10.1
    (cons
      '(◇ p)
      '(¬ (□ (¬ p)))))
(define eq-18.3.10.2
    (cons
      '(◇ p)
      '(¬ {p ⇒ 'f})))
(define eq-18.3.10.3
    (cons
      '(◇ p)
      '{{p ⇒ 'f} ⇒ 'f}))

(define eq-18.3.11.1
    (cons
      '(B p)
      '(◇ {p ∧ (¬ p)})))
(define eq-18.3.11.2
    (cons
      '(B p)
      '{(◇ p) ∧ (◇ (¬ p))}))
(define eq-18.3.11.3
    (cons
      '(B p)
      '{(◇ p) ∧ (¬ (□ p))}))

(define eq-18.3.12
    (cons
      '(□ (◇ p))
      '(◇ p)))

(define eq-18.3.13
    (cons
      '(◇ {p ⇒ q})
      '{(◇ p) ⇒ (◇ q)}))

(define eq-18.3.13.1
    (cons
      '(□ {p ∧ q})
      '{(□ p) ∧ (□ q)}))
(define eq-18.3.13.2
    (cons
      '(□ {p ∨ q})
      '{(□ p) ∨ (□ q)}))
(define eq-18.3.13.3
    (cons
      '(◇ {p ∧ q})
      '{(◇ p) ∧ (◇ q)}))
(define eq-18.3.13.4
    (cons
      '(◇ {p ∨ q})
      '{(◇ p) ∨ (◇ q)}))

(define eq-18.2.7.1
    (cons
      '{p ⊃ q}
      '{(¬ q) ⊃ (¬ p)}))

(define eq-18.4.12.1
    (cons
      '{p ⊃ {q ⊃ r}}
      '{{p ∧ q} ⊃ r}))
(define eq-18.4.12.2
    (cons
      '{p ⇒ {q ⇒ r}}
      '{{p ∧ q} ⇒ r}))
