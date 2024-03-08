#lang racket/base

;; copied from https://github.com/alphajuliet/graph-ext/blob/master/main.rkt
;; TODO not sure this is correct

(require
  racket/set
  graph)

(provide find-maximal-cliques)

(define (find-maximal-cliques G)
  ; NOTE this is an exponential algorithm
  ; TODO we really want just one clique at a time, not all at once

  (define (bron-kerbosch G acc r p x)
    (if (and (set-empty? p)
             (set-empty? x))
        (append acc (list (set->list r)))
        ;else
        (begin
          (for* ([v (in-set p)])
            (define nv (list->set (get-neighbors G v)))
            (set! acc (bron-kerbosch G
                                     acc
                                     (set-add r v)
                                     (set-intersect p nv)
                                     (set-intersect x nv)))
            (set! p (set-remove p v))
            (set! x (set-add x v)))
          acc)))

  (define R (set))
  (define P (list->set (get-vertices G)))
  (define X (set))
  (define accum '())

  (bron-kerbosch G accum R P X))

(module+ test
  (require rackunit)
  (define g0
    (unweighted-graph/undirected
      '((a b)
        (a c)
        (b c))))
  (define g1
    (unweighted-graph/undirected
      '((a b)
        (a c)
        (b c)
        (x y)
        (y z)
        (z u)
        (u y))))
  (check-equal? (find-maximal-cliques g0) '((a b c)))
  (check-equal? (find-maximal-cliques g1) '((a b c) (y z u) (x y))))
