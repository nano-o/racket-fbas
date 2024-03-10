#lang racket

(require
  "truth-tables.rkt"
  (only-in sugar define/caching)
  racket/match)

(provide
  3to2
  t-or-b?
  equiv-fmlas?)

 ; given a tvl formula, generates a boolean formula that is valid if and only if the original tvl formula is valid

; The idea is that, for each sub-formula f, we create two boolean variables f- and f+ that encode the tvl truth value of the formula (i.e. 00 is 'f, 01 and 10 is 'b, and 11 is 't). Then we just apply the truth tables to express the truth value of a formula in terms of the truth value of its subformulas.

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

(define (3to2 fmla)
  ; TODO make functional?
  (define cs (mutable-set)) ; we'll collect the constraints here
  (define vars (mutable-set)) ; we'll collect boolean variables here TODO why?
  (define (truth-tables-eval op)
    (eval op (module->namespace "truth-tables.rkt"))) ; TODO would using a macro be more performant?
  (define/caching (3to2-rec f)
    ; Here we want to create a 3vl variable for f and relate it the the 3vl variable corresponding to its constituant subformulas
    ; We'll return the two 3vl variable f- and f+ and the constraint
    (define f-+
      (cond
        [(symbol? f) ; f is a variable; it has no subformulas
         (cons (string->symbol (format "~a-" f)) (string->symbol (format "~a+" f)))]
        [else (cons (gensym) (gensym))]))
    (set-add! vars (car f-+))
    (set-add! vars (cdr f-+))
    (define constraint
      (match f
        [(? symbol?) #:when (member f truth-values) ((is-tv f) f-+)]
        [(? symbol?) #t]
        [`(,uop ,subf)
          (define subf-+ (3to2-rec subf))
          `(||
            ,@(for/list ([v truth-values])
                `(&& ,((is-tv v) subf-+) ,((is-tv ((truth-tables-eval uop) v)) f-+))))]
        [`(,bop ,subf1 ,subf2)
          (define subf1-+ (3to2-rec subf1))
          (define subf2-+ (3to2-rec subf2))
          `(||
            ,@(for*/list ([v1 truth-values]
                         [v2 truth-values])
                `(&& ,((is-tv v1) subf1-+) ,((is-tv v2) subf2-+) ,((is-tv ((truth-tables-eval bop) v1 v2)) f-+))))]
        ; We do something a bit ad-hoc for the * operations
        ; TODO does it have any advantage over translating to bops?
        [`(∧* ,subf ...)
          (define subf-+ (map 3to2-rec subf))
          (define one-f
            `(|| ,@(map is-f subf-+)))
          (define one-b
            `(|| ,@(map is-b subf-+)))
          `(||
             (&& ,one-f ,(is-f f-+))
             (&& (! ,one-f) ,one-b ,(is-b f-+))
             (&& (! ,one-f) (! ,one-b) ,(is-t f-+)))]
        [`(∨* ,subf ...)
          (define subf-+ (map 3to2-rec subf))
          (define one-t
            `(|| ,@(map is-t subf-+)))
          (define one-b
            `(|| ,@(map is-b subf-+)))
          `(||
             (&& ,one-t ,(is-t f-+))
             (&& (! ,one-t) ,one-b ,(is-b f-+))
             (&& (! ,one-t) (! ,one-b) ,(is-f f-+)))]
        [`(≡* ,subf ...)
          (define subf-+ (map 3to2-rec subf))
          (define one-t-one-f
            `(&& (|| ,@(map is-f subf-+)) (|| ,@(map is-t subf-+))))
          (define one-b
            `(|| ,@(map is-b subf-+)))
          `(||
             (&& ,one-t-one-f ,(is-f f-+))
             (&& (! ,one-t-one-f) ,one-b ,(is-b f-+))
             (&& (! ,one-t-one-f) (! ,one-b) ,(is-t f-+)))]))
    (set-add! cs constraint)
    f-+)
  (define p (3to2-rec fmla))
  (define constraint
    `(&& ,@(set->list cs)))
  `(,p ,vars . ,constraint))

(module+ test
  (3to2 '(B p)))

(define (t-or-b? fmla)
  (match-define `(,p ,vars . ,c) (3to2 fmla))
  ; finally, return the variables and the constraint
  (define constraint
    `(=> ,c (|| ,(is-t p) ,(is-b p))))
  `(,vars . ,constraint)) ; TODO vars not needed

(define (equiv-fmlas? f1 f2)
  (match-define `(,p1 ,vars1 . ,c1) (3to2 f1))
  (match-define `(,p2 ,vars2 . ,c2) (3to2 f2))
  (define constraint
    `(=>
       (&& ,c1 ,c2)
       (&&
         (<=> ,(is-t p1) ,(is-t p2))
         (<=> ,(is-f p1) ,(is-f p2))
         (<=> ,(is-b p1) ,(is-b p2)))))
 ; NOTE this relies on the fact that the boolean variables representing the base tvl variable are the same in both c1 and c2
 ; TODO vars not needed
  `(,(set-union (set) vars1 vars2) . ,constraint)) ; (set) because of https://github.com/racket/racket/issues/2583

#;(module+ verification

  ; TODO: translate diretly to smtlib instead of using eval...

  (require rosette)
  (provide
    verify-valid
    verify-equiv-fmlas)

  (define (make-verify-encoded-fmla vars constraints)
    ; this is meant to be evaluated in the context of the rosette module
    `(begin
       (define-symbolic ,@(set->list vars) boolean?)
       (define solver (current-solver))
       (solver-assert solver (list (! ,constraints)))
       (define sol (solver-check solver))
       (solver-clear solver)
       sol))

  (define (verify-valid fmla)
    (match-define `(,vars . ,constraints)
      (parameterize ([debug #f]) (t-or-b? fmla)))
    (eval (make-verify-encoded-fmla vars constraints) (module->namespace 'rosette)))

  (define (verify-equiv-fmlas f1 f2)
    (match-define `(,vars . ,constraints)
      (parameterize ([debug #f]) (equiv-fmlas? f1 f2)))
    (eval (make-verify-encoded-fmla vars constraints) (module->namespace 'rosette))))


#;(module+ test
  (require
    (submod ".." verification)
    rosette)

  (define (equiv? f1 f2)
    (not (sat? (verify-equiv-fmlas f1 f2))))
  (define (valid? f)
    (not (sat? (verify-valid f))))

  (check-true (valid? '(≡ p (¬ (¬ p)))))
  (check-true (equiv? 'p '(¬ (¬ p))))

  (define test-fmla-2 '(≡ (∨ p q) (¬ (∧ (¬ p) (¬ q)))))
  (check-true (valid? test-fmla-2))

  (define test-fmla-3 '(≡ (∧ p q) (¬ (∨ (¬ p) (¬ q)))))
  (check-true (valid? test-fmla-3))

  (define test-fmla-4 '(∧ (∨ (¬ p) p) (∨ p (¬ p))))
  (check-true (valid? test-fmla-4))

  (define test-fmla-5 '(∨ p (¬ p)))
  (check-true (valid? test-fmla-5))

  (define test-fmla-6 '(∧ p (¬ p)))
  (check-false (valid? test-fmla-6))

  (define test-fmla-7 '(∧* (∨* (¬ p) p) (∨* p (¬ p))))
  (check-true (valid? test-fmla-7))

  (check-true (equiv? '{≡ p  q} '{∧ {∨ (¬ p)  q} {∨ p (¬ q)}})))
