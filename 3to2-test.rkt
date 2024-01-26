#lang sweet-exp racket

(require
  "3to2.rkt"
  racket/syntax
  rosette)

(define (verify/syntax fmla)
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
    (parameterize ([debug #t]) (valid?/3to2 fmla)))
  `(begin
     (define-symbolic ,@(set->list vars) boolean?)
     (define solver (current-solver))
     (solver-assert solver (list (! ,constraint)))
     (solver-check solver)))

(define test-fmla-1 '(≡* p (¬ (¬ p))))
(define test-fmla-2 '(≡* (∨* p q) (¬ (∧* (¬ p) (¬ q)))))
(define test-fmla-3 '(≡* (∧* p q) (¬ (∨* (¬ p) (¬ q)))))
(define test-fmla-4 '(∧* (∨* (¬ p) p) (∨* p (¬ p))))
#;(with-output-to-file #:exists 'replace "debug.txt"
  (thunk
    (pretty-write
      (model
        (eval
          (verify/datum test-fmla-1)
          (module->namespace 'rosette))))))
(with-output-to-file #:exists 'replace "debug.txt"
  (thunk
    (pretty-write
        (eval
          (verify-solver/datum test-fmla-4)
          (module->namespace 'rosette)))))
