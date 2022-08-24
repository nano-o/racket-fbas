#lang gamble

(require
  (only-in "qset.rkt" qset)
  "nomination.rkt"
  (submod "nomination.rkt" test)
  "stellar-network.rkt")

(define (assign-random-vals conf)
  (for/hash ([n (hash-keys conf)])
    (values n (sample (uniform-dist 0 1)))))

(define (run-nomination conf)
  (define N
    (assign-random-vals conf))
  (define P
    (assign-random-vals conf))
  (define s
    (nomination-votes conf N P))
  (define failed?
    (for/and ([n (hash-keys s)])
      (equal? (hash-ref s n ) #f)))
  (define accepted?
    (accepted-nominated? conf s))
  accepted?)

(define (my-sampler conf)
  (rejection-sampler
    (run-nomination conf)))

(define (get-distribution num-samples conf)
  (sampler->discrete-dist (my-sampler conf) num-samples))

; to get the current top-tier config:
;(define stellar-conf (hash->conf (get-stellar-top-tier-qsets)))
; to run the sampling:
;(get-distribution 1000 stellar-conf)
