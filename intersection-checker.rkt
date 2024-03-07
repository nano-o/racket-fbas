#lang racket
; #lang errortrace racket

(require
  "3to2.rkt"
  "rosette-sat.rkt"
  "characteristic-fmla.rkt"
  "stellarbeat.rkt"
  (only-in rosette sat? solution? model)
  racket/cmdline)

(provide
  check-intertwined)

(define (check-valid-using-3to2 fmla)
  (SAT? `(! ,(cdr (t-or-b? fmla)))))

(define (check-intertwined method network)
  (define char-fmla (qset-characteristic-fmla network))
  (define sol (method char-fmla))
  (unless (solution? sol) (error "Failed to run the validity check; something's wrong."))
  (if (sat? sol)
    (begin
      (println "not intertwined!")
      (with-output-to-file #:exists 'replace "./model" (thunk (write (model sol)))))
    (println "all intertwined"))
  sol)

(module+ main

  (define method (make-parameter valid/3?))

  (define file
    (command-line
      #:once-any
      [("--3to2") "check validity by translating to boolean logic"
                  (method check-valid-using-3to2)]
      [("--symex") "check validity by symbolically executing the 3-valued logic interpreter"
                   (method valid/3?)]
      #:args ([filename #f]) filename))

  (if file
    (check-intertwined (method) (get-network-from-file file))
    (begin
      (displayln "no file provided, getting data from stellarbeat")
      (check-intertwined (get-stellar-network)))))

; a few simple tests
(module+ test
  (require rackunit "qset.rkt")
  ; (define method check-valid-using-3to2)
  (define method valid/3?)
  (check-true
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv 'p) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'p) (set)))))))
  (check-true
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'r) (set)))))))
  (check-true
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (a . ,(qset 1 (seteqv 'b) (set)))
        (b . ,(qset 1 (seteqv 'b) (set)))
        (x . ,(qset 2 (seteqv 'p 'a) (set)))))))
  (check-false
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 1 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 1 (seteqv 1 2 3) (set)))))))
  (check-false
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined method
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set))))))))
