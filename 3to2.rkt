#lang racket
; #lang errortrace racket

(require
  "truth-tables.rkt"
  (only-in sugar define/caching)
  ; racket/trace
  racket/match)

(provide
  3to2
  t-or-b?
  equiv-fmlas?)

 ; given a tvl formula, generates a boolean formula that is valid if and only if the original tvl formula is valid

; The idea is that, for each sub-formula f, we create two boolean variables f- and f+ that encode the tvl truth value of the formula (i.e. 00 is 'f, 01 and 10 is 'b, and 11 is 't). Then we follow the truth tables to express the truth value of a formula in terms of the truth value of its subformulas.

; We encode 3vl values as pairs of booleans
(define (is-f p) ; f is 10
  `(&& ,(car p) (! ,(cdr p))))
(define (is-t p) ; t is 01
  `(&& (! ,(car p)) ,(cdr p)))
(define (is-b p) ; b is 00 or 11
  `(|| (&& (! ,(car p)) (! ,(cdr p))) (&& ,(car p) ,(cdr p))))

(module+ test
  (require rackunit)
  (check-equal?
    (is-f '(p . q))
    '(&& p (! q))))

; returns a function that checks whether its encoded 3vl argument (a pair) corresponds to the 3vl value v
(define (is-tv v)
  (case v
    [(t) is-t]
    [(b) is-b]
    [(f) is-f]))

(module+ test
  (check-equal?
    ((is-tv 'f) '(p . q))
    '(&& p (! q))))

(define (eval-truth-table op)
  (eval op (module->namespace "truth-tables.rkt")))

(define/caching (3to2 fmla)
    (define f-+ ; this is a pair of symbols
      (cond
        [(symbol? fmla) ; f is a variable; we use the original name. We rely on this when checking equivalence of two formulas
         `(,(string->symbol (format "~a-" fmla)) . ,(string->symbol (format "~a+" fmla)))]
        [else `(,(gensym) . ,(gensym))]))
    (define constraints
      (match fmla
        [(? ((curryr member) truth-values)) (set ((is-tv fmla) f-+))]
        [(? symbol?) (set)] ; symbol that's not a 3vl truth value; no constraint in that case
        [`(∧*) (set (is-t f-+))]
        [`(∨*) (set (is-f f-+))]
        [`(,uop ,subf) ; unary operation
          (match-define `(,subf-+ ,sub-constraints) (3to2 subf))
          (define new-constraint
            `(||
            ,@(for/list ([v truth-values])
                `(&& ,((is-tv v) subf-+) ,((is-tv ((eval-truth-table uop) v)) f-+)))))
          (set-add sub-constraints new-constraint)]
        ; We do something a bit ad-hoc for the * operations
        ; This improves performance a lot compared to first rewriting the big ops
        [`(∧* ,subf ...)
          (match-define `((,subf-+ ,sub-constraints) ...) (map 3to2 subf))
          (define one-f
            `(|| ,@(map is-f subf-+)))
          (define one-b
            `(|| ,@(map is-b subf-+)))
          (define new-constraint
            `(||
               (&& ,one-f ,(is-f f-+))
               (&& (! ,one-f) ,one-b ,(is-b f-+))
               (&& (! ,one-f) (! ,one-b) ,(is-t f-+))))
          (set-add (apply set-union sub-constraints) new-constraint)]
        [`(∨* ,subf ...)
          (match-define `((,subf-+ ,sub-constraints) ...) (map 3to2 subf))
          (define one-t
            `(|| ,@(map is-t subf-+)))
          (define one-b
            `(|| ,@(map is-b subf-+)))
          (define new-constraint
            `(||
               (&& ,one-t ,(is-t f-+))
               (&& (! ,one-t) ,one-b ,(is-b f-+))
               (&& (! ,one-t) (! ,one-b) ,(is-f f-+))))
          (set-add (apply set-union sub-constraints) new-constraint)]
        [`(≡* ,subf ...)
          (match-define `((,subf-+ ,sub-constraints) ...) (map 3to2 subf))
          (define one-t-one-f
            `(&& (|| ,@(map is-f subf-+)) (|| ,@(map is-t subf-+))))
          (define one-b
            `(|| ,@(map is-b subf-+)))
          (define new-constraint
            `(||
               (&& ,one-t-one-f ,(is-f f-+))
               (&& (! ,one-t-one-f) ,one-b ,(is-b f-+))
               (&& (! ,one-t-one-f) (! ,one-b) ,(is-t f-+))))
          (set-add (apply set-union sub-constraints) new-constraint)]
        [`(,bop ,subf1 ,subf2) ; binary operation
          (match-define `(,subf1-+ ,sub-constraints1) (3to2 subf1))
          (match-define `(,subf2-+ ,sub-constraints2) (3to2 subf2))
          ; TODO seems like using the same encoding as for the * bops above would produce smaller formulas
          (define new-constraint
            `(||
               ,@(for*/list ([v1 truth-values]
                             [v2 truth-values])
                   `(&& ,((is-tv v1) subf1-+) ,((is-tv v2) subf2-+) ,((is-tv ((eval-truth-table bop) v1 v2)) f-+)))))
          (set-add (set-union sub-constraints1 sub-constraints2) new-constraint)]))
    `(,f-+ ,constraints))

(module+ test
  (check-equal?
    (set-count (cadr (3to2 '(∧ (¬ (B p)) (¬ (B p))))))
    3))

(define (constraints-to-fmla cs)
  (if (set-empty? cs)
    #t
    `(&& ,@(set->list cs))))

(define (t-or-b? fmla) ; validity test
  (match-define `(,p ,c) (3to2 fmla))
  `(=> ,(constraints-to-fmla c) (|| ,(is-t p) ,(is-b p))))

(define (equiv-fmlas? f1 f2)
  (match-define `(,p1 ,c1) (3to2 f1))
  (match-define `(,p2 ,c2) (3to2 f2))
  ; NOTE this relies on the fact that the boolean variables representing the base tvl variable are the same in both c1 and c2
  `(=>
     (&& ,(constraints-to-fmla c1) ,(constraints-to-fmla c2))
     (&&
       (<=> ,(is-t p1) ,(is-t p2))
       (<=> ,(is-f p1) ,(is-f p2))
       (<=> ,(is-b p1) ,(is-b p2)))))

(define (rewrite-big-ops f)
  ; a drawback of this is that it increases the number of subformulas, and thus the number of variables and constraints that will be produced by 3to2 below, which results in (very) bad performance
  (match f
    [`(∧* ,q ...)
      #:when (> (length q) 2)
      `(∧ ,(rewrite-big-ops (car q)) ,(rewrite-big-ops `(∧* ,@(cdr q))))]
    [`(∧* ,q1 ,q2)
      `(∧ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    ['(∧*) 't]
    [`(∨* ,q ...)
      #:when (> (length q) 2)
      `(∨ ,(rewrite-big-ops (car q)) ,(rewrite-big-ops `(∨* ,@(cdr q))))]
    [`(∨* ,q1 ,q2)
      `(∨ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    ['(∨*) 'f]
    [`(≡* ,q ...)
      #:when (> (length q) 2)
      (define subfs (map rewrite-big-ops q))
      (define head-eqs
        (for/fold
          ([acc 't])
          ([f (cdr subfs)])
          `(∧ (≡ ,(car subfs) ,f) ,acc)))
      `(∧ ,head-eqs ,(rewrite-big-ops `(≡* ,@(cdr subfs))))] ; TODO is this even correct?
    [`(≡* ,q1 ,q2)
      `(≡ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    ['(≡*) (error "empty equivalence")]
    [`(,bop ,q1 ,q2)
      `(,bop ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(,uop ,q)
      `(,uop ,(rewrite-big-ops q))]
    [(and sym (? symbol?)) sym]
    [x (error (format "unhandled case: ~a" x))]))

