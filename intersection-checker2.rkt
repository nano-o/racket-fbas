#lang racket

(require
  ; "tvl-verification.rkt"
  ; (submod "3to2.rkt" verification)
  "rosette-sat.rkt"
  "characteristic-fmla.rkt"
  "stellarbeat.rkt"
  (only-in rosette sat? model)
  racket/cmdline
  racket/match)

(provide
  check-intertwined)

(define (check-intertwined network)
  (match-define `(,vars . ,char-fmla) (characteristic-fmla network))
  (define sol (valid/3? char-fmla))
  (if (sat? sol)
    (with-output-to-file #:exists 'replace "./model" (thunk (write (model sol))))
    (println "all intertwined")))
  #;(verify-valid/at-runtime vars char-fmla)

(define file
  (command-line #:args ([filename #f]) filename))

(if file
  (check-intertwined (get-network-from-file file))
  (begin
    (displayln "no file provided, getting data from stellarbeat")
    (check-intertwined (get-stellar-network))))
