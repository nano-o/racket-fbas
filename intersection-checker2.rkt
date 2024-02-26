#lang racket

(require
  ; "tvl-verification.rkt"
  ; (submod "3to2.rkt" verification)
  "3to2.rkt"
  "rosette-sat.rkt"
  "characteristic-fmla.rkt"
  "stellarbeat.rkt"
  racket/pretty
  (only-in rosette sat? model)
  racket/cmdline
  racket/match)

(provide
  check-intertwined)

; TODO disagreement on almost_symmetric_13
(define (check-intertwined network)
  (match-define `(,vars . ,char-fmla) (characteristic-fmla network))
  ; (pretty-print (3to2 char-fmla))
  ; (define sol (SAT? `(! ,(cdr (t-or-b? char-fmla)))))
  (define sol (valid/3? char-fmla))
  (if (sat? sol)
    (with-output-to-file #:exists 'replace "./model" (thunk (write (model sol))))
    (println "all intertwined")))

(define file
  (command-line #:args ([filename #f]) filename))

(if file
  (check-intertwined (get-network-from-file file))
  (begin
    (displayln "no file provided, getting data from stellarbeat")
    (check-intertwined (get-stellar-network))))
