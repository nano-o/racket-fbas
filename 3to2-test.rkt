#lang sweet-exp racket

(require
  "3to2.rkt"
  racket/syntax
  rosette)

(define (verify/syntax fmla)
  ; TODO: how to get syntax context right?
  (match-define `(,vars . ,constraint)
    (valid?/3to2 fmla))
  (with-syntax
    ([(v ...) (for/list ([v vars]) (format-id #'() "~a" v))])
    #`(begin
        (define-symbolic v ... boolean?)
      #,(datum->syntax #'() constraint))))

(define (verify/datum fmla)
  (match-define `(,vars . ,constraint)
    (parameterize ([debug #t]) (valid?/3to2 fmla)))
  `(begin
     (define-symbolic ,@(set->list vars) boolean?)
     (verify (assert ,constraint))))

(define (verify-solver/datum fmla)
  (match-define `(,vars . ,constraint)
    (parameterize ([debug #f]) (valid?/3to2 fmla)))
  `(begin
     (define-symbolic ,@(set->list vars) boolean?)
     (define solver (current-solver))
     (solver-assert solver (list (! ,constraint)))
     (define sol (solver-check solver))
     (solver-clear solver)
     sol))

(module+ test
  (require rackunit)
  (define (valid? f)
      (not
        (sat?
          (eval (verify-solver/datum f) (module->namespace 'rosette)))))

  (define test-fmla-1 '(≡ p (¬ (¬ p))))
  (check-true (valid? test-fmla-1))

  (define test-fmla-2 '(≡ (∨ p q) (¬ (∧ (¬ p) (¬ q)))))
  (check-true (valid? test-fmla-2))

  (define test-fmla-3 '(≡ (∧ p q) (¬ (∨ (¬ p) (¬ q)))))
  (check-true (valid? test-fmla-3))

  (define test-fmla-4 '(∧ (∨ (¬ p) p) (∨ p (¬ p))))
  (check-true (valid? test-fmla-4))

  (define test-fmla-5 '(∨ p (¬ p)))
  (check-true (valid? test-fmla-5))

  (define test-fmla-6 '(∧ p (¬ p)))
  (check-false (valid? test-fmla-6))

  (define test-fmla-7 '(∧* (∨* (¬ p) p) (∨* p (¬ p))))
  (check-true (valid? test-fmla-7)))

  #;(with-output-to-file #:exists 'replace "debug.txt"
  (thunk
    (pretty-write
      (model
        (eval
          (verify/datum test-fmla-1)
          (module->namespace 'rosette))))))

#;(with-output-to-file #:exists 'replace "debug.txt"
(thunk
  (pretty-write
    (eval
      (verify-solver/datum test-fmla-1)
      (module->namespace 'rosette)))))
