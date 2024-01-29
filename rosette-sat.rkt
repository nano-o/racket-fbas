#lang rosette

(define (interpret formula)
  (match formula
    [`(∧ ,expr ...) (apply && (map interpret expr))]
    [`(∨ ,expr ...) (apply || (map interpret expr))]
    [`(¬ ,expr)     (! (interpret expr))]
    [lit            (constant lit boolean?)]))

; This implements a SAT solver.
(define (SAT formula)
  (solve (assert (interpret formula))))

(SAT `(∧ r o (∨ s e (¬ t)) t (¬ e)))

(solve (assert (&& (! (constant 'y boolean?)) (constant 'x boolean?))))
