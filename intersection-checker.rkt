#lang racket

(require
  "3to2.rkt"
  "rosette-sat.rkt"
  "characteristic-fmla.rkt"
  "stellarbeat.rkt"
  (only-in rosette sat? solution? model)
  racket/cmdline)

(provide
  check-intertwined)

; TODO use a "main" module

(define (check-valid-using-3to2 fmla)
  (SAT? `(! ,(cdr (t-or-b? fmla)))))

(define method (make-parameter valid/3?))

(define file
  (command-line
    #:once-any
    [("--3to2") "check validity by translating to boolean logic"
                (method check-valid-using-3to2)]
    [("--symex") "check validity by symbolically executing the 3-valued logic interpreter"
                (method valid/3?)]
    #:args ([filename #f]) filename))

(define (check-intertwined network)
  (define char-fmla (qset-characteristic-fmla network))
  (define sol ((method) char-fmla))
  (unless (solution? sol) (error "Failed to run the validity check; something's wrong."))
  (if (sat? sol)
    (begin
      (println "not intertwined!")
      (with-output-to-file #:exists 'replace "./model" (thunk (write (model sol)))))
    (println "all intertwined")))

(if file
  (check-intertwined (get-network-from-file file))
  (begin
    (displayln "no file provided, getting data from stellarbeat")
    (check-intertwined (get-stellar-network))))
