#lang racket
; #lang errortrace racket

(require
  "3to2.rkt"
  "rosette-sat.rkt"
  "characteristic-fmla.rkt"
  "stellarbeat.rkt"
  (only-in rosette sat? solution? model)
  (only-in "qset.rkt"
           fbas-intertwined?/incomplete
           flatten-qsets
           qset-fbas->slices-fbas)
  racket/cmdline)

(provide
  check-intertwined/sat)

(define (check-valid-using-3to2 fmla)
  (SAT? `(! ,(t-or-b? fmla))))

(define (check-intertwined/sat method fbas)
  ; (define char-fmla (qset-characteristic-fmla fbas))
  (define char-fmla
    (characteristic-fmla
      (qset-fbas->slices-fbas (flatten-qsets fbas))
      (dict-keys fbas)))
  (define sol (method char-fmla))
  (unless (solution? sol) (error "Failed to run the validity check; something's wrong."))
  (if (sat? sol)
    (begin
      (println "not intertwined!")
      (with-output-to-file #:exists 'replace "./model" (thunk (write (model sol)))))
    (println "all intertwined"))
  sol)

(module+ main

  (define method (make-parameter check-valid-using-3to2))

  (define file
    (command-line
      #:once-any
      [("--3to2") "check validity by translating to boolean logic"
                  (method ((curry check-intertwined/sat) check-valid-using-3to2))]
      [("--symex") "check validity by symbolically executing the 3-valued logic interpreter"
                   (method ((curry check-intertwined/sat) valid/3?))]
      [("--fast") "use incomplete heuristic and fall-back on 3to2"
                  (method (λ (fbas) (or (fbas-intertwined?/incomplete fbas) (check-intertwined/sat check-valid-using-3to2 fbas))))]
      #:args ([filename #f]) filename))

  (if file
    ((method) (get-fbas-from-file file))
    (begin
      (displayln "no file provided, getting data from stellarbeat")
      ((method) (get-stellar-fbas)))))

; a few simple tests
(module+ test
  ; TODO a macro like in 3vl-tests.rkt
  (require rackunit "qset.rkt")
  ; (define method check-valid-using-3to2)
  (define method valid/3?)
  (check-true
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv 'p) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'p) (set)))))))
  (check-true
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'r) (set)))))))
  (check-true
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (a . ,(qset 1 (seteqv 'b) (set)))
        (b . ,(qset 1 (seteqv 'b) (set)))
        (x . ,(qset 2 (seteqv 'p 'a) (set)))))))
  (check-false
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 1 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 1 (seteqv 1 2 3) (set)))))))
  (check-false
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined/sat method
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set))))))))
