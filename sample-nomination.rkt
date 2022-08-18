#lang gamble

(require
  "fba.rkt"
  (submod "fba.rkt" test))

(define (assign-random-vals fbas)
  (for/hash ([n (hash-keys fbas)])
    (values n (sample (uniform-dist 0 1)))))

(define (run-nomination fbas)
  (define N
    (assign-random-vals fbas))
  (define P
    (assign-random-vals fbas))
  (define s
    (nomination-votes fbas N P))
  (define accepted?
    (accepted-nominated? fbas s))
  accepted?)

(define (my-sampler fbas)
  (rejection-sampler
    (run-nomination fbas)))

(define (get-distribution num-samples fbas)
  (sampler->discrete-dist (my-sampler fbas) num-samples))

; TODO generate more complex intact fbas
; TODO try the current top-tier configuration
