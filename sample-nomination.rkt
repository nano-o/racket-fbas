#lang gamble

(require
  "fba.rkt"
  (only-in racket count set-union set->list for/set in-set argmax set-count remove-duplicates empty? set-empty?)
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
    (nomination fbas N P))
  (define agreement?
    (and
      (equal?
        (length (remove-duplicates (hash-values s)))
        1)
      (not (member -1 (hash-values s)))))
  agreement?)

(define (my-sampler fbas)
  (rejection-sampler
    (run-nomination fbas)))

(sampler->discrete-dist (my-sampler fbas-1) 100)
