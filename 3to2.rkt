#lang racket

(require
  "truth-tables.rkt"
  racket/trace
  racket/generator
  racket/match)

(provide
  3to2
  t-or-b?
  equiv-fmlas?
  debug)

 ; given a tvl formula, generates a boolean formula that is valid if and only if the original tvl formula is valid

; The idea is that, for each sub-formula f, we create two boolean variables f- and f+ that encode the tvl truth value of the formula (i.e. 00 is 'f, 01 and 10 is 'b, and 11 is 't). Then we just apply the truth tables to express the truth value of a formula in terms of the truth value of its subformulas.
; TODO if we go with the terminology f- and f+ then we should have 10 is f, 01 is t, and 11/00 is b

; NOTE we better use rosette's &&, ||, etc. (and not `and`, `or`, etc) to get the classical logical operations

(define debug (make-parameter #f))

(define (is-f p)
  `(&& ,(car p) (! ,(cdr p))))
(define (is-t p)
  `(&& (! ,(car p)) ,(cdr p)))
(define (is-b p)
  `(|| (&& (! ,(car p)) (! ,(cdr p))) (&& ,(car p) ,(cdr p))))

(module+ test
  (require rackunit)
  (check-equal?
    (is-f '(p . q))
    '(&& p (! q))))

; returns a function that checks whether its argument (a pair) is the 3vl value v
(define (is-tv v)
  (case v
    [(t) is-t]
    [(b) is-b]
    [(f) is-f]))

(module+ test
  (check-equal?
    ((is-tv 'f) '(p . q))
    '(&& p (! q))))

; TODO macro based on trugh tables...
(define (encode-¬ p q)
  `(||
     (&& ,(is-f q) ,(is-t p))
     (&& ,(is-b q) ,(is-b p))
     (&& ,(is-t q) ,(is-f p)))) ; encodes "p is not q"

(define (encode-□ p q)
  `(||
     (&& ,(is-f q) ,(is-f p))
     (&& ,(is-b q) ,(is-f p))
     (&& ,(is-t q) ,(is-t p))))

(define (encode-◇ p q)
  `(||
     (&& ,(is-f q) ,(is-f p))
     (&& ,(is-b q) ,(is-t p))
     (&& ,(is-t q) ,(is-t p))))

(define (encode-B p q)
  `(||
     (&& ,(is-f q) ,(is-f p))
     (&& ,(is-b q) ,(is-t p))
     (&& ,(is-t q) ,(is-f p))))

(module+ test
  (check-equal?
    (encode-¬ '(f1+ . f1-) '(f2+ . f2-))
    'todo))

; TODO macro
(define (encode-∧ p q1 q2) ; encodes "p is the conjunction of q1 and q2"
  `(|| ,@(for*/list ([v1 truth-values]
                     [v2 truth-values])
           `(&& ,((is-tv v1) q1) ,((is-tv v2) q2) ,((is-tv (∧ v1 v2)) p)))))
(define (encode-∨ p q1 q2)
  `(|| ,@(for*/list ([v1 truth-values]
                     [v2 truth-values])
           `(&& ,((is-tv v1) q1) ,((is-tv v2) q2) ,((is-tv (∨ v1 v2)) p)))))
(define (encode-⇒ p q1 q2)
  `(|| ,@(for*/list ([v1 truth-values]
                     [v2 truth-values])
           `(&& ,((is-tv v1) q1) ,((is-tv v2) q2) ,((is-tv (⇒ v1 v2)) p)))))
(define (encode-≡ p q1 q2)
  `(|| ,@(for*/list ([v1 truth-values]
                     [v2 truth-values])
           `(&& ,((is-tv v1) q1) ,((is-tv v2) q2) ,((is-tv (≡ v1 v2)) p)))))
(define (encode-⊃ p q1 q2)
  `(|| ,@(for*/list ([v1 truth-values]
                     [v2 truth-values])
           `(&& ,((is-tv v1) q1) ,((is-tv v2) q2) ,((is-tv (⊃ v1 v2)) p)))))
(define (encode-⇔ p q1 q2)
  `(|| ,@(for*/list ([v1 truth-values]
                     [v2 truth-values])
           `(&& ,((is-tv v1) q1) ,((is-tv v2) q2) ,((is-tv (⇔ v1 v2)) p)))))

#;(define (rewrite-big-ops f)
  ; TODO there seems to be a problem (disagreement with other metdhos on almost_sym_13)
  ; rewrite the * ops
  ; looks like something for nanopass
  (match f
    [`(∧ ,q1 ,q2)
      `(∧ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(∨ ,q1 ,q2)
      `(∨ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(⇒ ,q1 ,q2)
      `(⇒ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(≡ ,q1 ,q2)
      `(≡ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(⇔ ,q1 ,q2)
      `(⇔ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(⊃ ,q1 ,q2)
      `(⊃ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
    [`(□ ,q)
      `(□ ,(rewrite-big-ops q))]
    [`(◇ ,q)
      `(◇ ,(rewrite-big-ops q))]
    [`(¬ ,q)
      `(¬ ,(rewrite-big-ops q))]
    [`(B ,q)
      `(B ,(rewrite-big-ops q))]
    [(and sym (? symbol?)) sym]
    [`(∧* ,q ...)
      (match q
        [`(,qs ...) #:when (> (length qs) 2)
                    `(∧ ,(rewrite-big-ops (car qs)) ,(rewrite-big-ops `(∧* ,@(cdr qs))))]
        [`(,q1 ,q2) `(∧ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
        [`(,q1) (rewrite-big-ops q1)])]
        ['() #t]
    [`(∨* ,q ...)
      (match q
        [`(,qs ...) #:when (> (length qs) 2)
                    `(∨ ,(rewrite-big-ops (car qs)) ,(rewrite-big-ops `(∨* ,@(cdr qs))))]
        [`(,q1 ,q2) `(∨ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
        [`(,q1) (rewrite-big-ops q1)])]
        ['() #f]
    [`(≡* ,q ...)
      (match q
        [`(,qs ...) #:when (> (length qs) 2)
                    `(≡ ,(rewrite-big-ops (car qs)) ,(rewrite-big-ops `(≡* ,@(cdr qs))))]
        [`(,q1 ,q2) `(≡ ,(rewrite-big-ops q1) ,(rewrite-big-ops q2))]
        [`(,q1) (rewrite-big-ops q1)])]
        ['() (raise (error "empty equivalence is not supported"))] ; TODO: what should this be?
    [x (error (format "unhandled case: ~a" x))]))

(define (encode-∧* p qs) ; encodes "p is the conjunction of all the qs"
  (define one-f
    `(|| ,@(map is-f qs)))
  (define one-b
    `(|| ,@(map is-b qs)))
  `(||
     (&& ,one-f ,(is-f p))
     (&& (! ,one-f) ,one-b ,(is-b p))
     (&& (! ,one-f) (! ,one-b) ,(is-t p))))
     ; (&& (! ,one-f)
         ; (|| (&& ,one-b ,(is-b p))
             ; (&& (! ,one-b) ,(is-t p))))))

(define (encode-∨* p qs) ; encodes "p is the disjunction of all the qs"
  (define one-t
    `(|| ,@(map is-t qs)))
  (define one-b
    `(|| ,@(map is-b qs)))
  `(||
     (&& ,one-t ,(is-t p))
     (&& (! ,one-t) ,one-b ,(is-b p))
     (&& (! ,one-t) (! ,one-b) ,(is-f p))))
     ; (&& (! ,one-t)
         ; (|| (&& ,one-b ,(is-b p))
             ; (&& (! ,one-b) ,(is-f p))))))

(define (encode-≡* p qs) ; encodes "p is the equivalence of all the qs"
  (define one-t-one-f
    `(&& (|| ,@(map is-f qs)) (|| ,@(map is-t qs))))
  (define one-b
    `(|| ,@(map is-b qs)))
  `(||
     (&& ,one-t-one-f ,(is-f p))
     (&& (! ,one-t-one-f) ,one-b ,(is-b p))
     (&& (! ,one-t-one-f) (! ,one-b) ,(is-t p))))
     ; (&& (! ,one-t-one-f)
         ; (|| (&& ,one-b ,(is-b p))
             ; (&& (! ,one-b) ,(is-t p))))))

; TODO: we should probably avoid creating boolean variables for formulas we have seen already
; TODO: could be done tail recursive: create vars for subformulas, create constraint, pass vars to recursive call
(define (3to2 fmla)
  (define cs (mutable-set)) ; we'll collect the constraints here
  (define vars (mutable-set)) ; we'll collect boolean variables here
  (define (3to2-rec f)
    ; first we generate symbols f+ and f-
    (define f-+
      (if (debug)
        `(,(string->symbol (format "~a-" f)) . ,(string->symbol (format "~a+" f)))
        (if (symbol? f)
          `(,(string->symbol (format "~a-" f)) . ,(string->symbol (format "~a+" f)))
          `(,(gensym) . ,(gensym)))))
    (set-add! vars (car f-+))
    (set-add! vars (cdr f-+))
    (define constraint
      (match f
        [(? symbol?) #:when (member f truth-values) ((is-tv f) f-+)]
        [(? symbol?) #t]
        [`(∧ ,q1 ,q2)
          (encode-∧ f-+ (3to2-rec q1) (3to2-rec q2))]
        [`(∨ ,q1 ,q2)
          (encode-∨ f-+ (3to2-rec q1) (3to2-rec q2))]
        [`(⊃ ,q1 ,q2)
          (encode-⊃ f-+ (3to2-rec q1) (3to2-rec q2))]
        [`(⇒ ,q1 ,q2)
          (encode-⇒ f-+ (3to2-rec q1) (3to2-rec q2))]
        [`(≡ ,q1 ,q2)
          (encode-≡ f-+ (3to2-rec q1) (3to2-rec q2))]
        [`(⇔ ,q1 ,q2)
          (encode-⇔ f-+ (3to2-rec q1) (3to2-rec q2))]
        [`(◇ ,q)
          (encode-◇ f-+ (3to2-rec q))]
        [`(□ ,q)
          (encode-□ f-+ (3to2-rec q))]
        [`(¬ ,q)
          (encode-¬ f-+ (3to2-rec q))]
        [`(B ,q)
          (encode-B f-+ (3to2-rec q))]
        [`(∧* ,q ...)
          (encode-∧* f-+ (map 3to2-rec q))]
        [`(∨* ,q ...)
          (encode-∨* f-+ (map 3to2-rec q))]
        [`(≡* ,q ...)
          (encode-≡* f-+ (map 3to2-rec q))]))
    (set-add! cs constraint)
    f-+)
  ; (define p (3to2-rec (rewrite-big-ops fmla)))
  (define p (3to2-rec fmla))
  (define constraint
    `(&& ,@(set->list cs)))
  ; (println "finished generating fmla")
  `(,p ,vars . ,constraint))

(define (t-or-b? fmla)
  (match-define `(,p ,vars . ,c) (3to2 fmla))
  ; finally, return the variables and the constraint
  (define constraint
    `(=> ,c (|| ,(is-t p) ,(is-b p))))
  `(,vars . ,constraint))

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
