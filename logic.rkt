#lang rosette

(require nanopass/base)
(require rosette/lib/synthax)

; we start by defining a syntax of formulas

(define-language L-full
  (terminals
    (variable (x))
    (value (v)))
  (Formula (fm)
    x
    v
    (and fm1 fm2)
    (or fm1 fm2)
    (not fm)
    (dimp fm1 fm2) ; double implication =>
    (cimp fm1 fm2) ; curly implication
    (box fm)
    (diamond fm)))

(define (variable? x) (and (symbol? x) (not (value? x))))
(define (value? v) (memq v '(t b f)))

(define-parser parse-L-full L-full)

(module+ test
  (parse-L-full '(and t (and a b)))

  (define-pass test-pass : L-full (ir) -> L-full ()
    (Formula : Formula (ir) -> Formula ()
       [,x `,x]
       [,v 't] ; all values become 't
       [(and ,[fm1] ,[fm2]) `(and ,fm1 ,fm2)])
    (Formula ir))

  (test-pass (parse-L-full 'x))
  (test-pass (parse-L-full 'f))
  (test-pass (parse-L-full '(and t (and a b)))))

; truth table semantics
; given a map from variable to value, evaluate a formula
; NOTE rosette does not support match
(define-pass eval : L-full (ir h) -> * (val)
  (Formula : Formula (ir) -> * (val)
    [,x (if (hash-has-key? h x)
          (hash-ref h x)
          (error (format "variable ~a is not assigned a value" x)))]
    [,v v]
    [(and ,[fm1] ,[fm2])
     (match `(,fm1 . ,fm2)
       ['(t . t) 't]
       ['(t . b) 'b]
       ['(t . f) 'f]
       ['(b . t) 'b]
       ['(b . b) 'b]
       ['(b . f) 'f]
       ['(f . t) 'f]
       ['(f . b) 'f]
       ['(f . f) 'f])]
    [(or ,[fm1] ,[fm2])
     (match `(,fm1 . ,fm2)
       ['(t . t) 't]
       ['(t . b) 't]
       ['(t . f) 't]
       ['(b . t) 't]
       ['(b . b) 'b]
       ['(b . f) 'b]
       ['(f . t) 't]
       ['(f . b) 'b]
       ['(f . f) 'f])]
    [(not ,[fm])
     (match fm
       ['t 'f]
       ['b 'b]
       ['f 't])]
    [(dimp ,[fm1] ,[fm2])
     (match `(,fm1 . ,fm2)
       ['(t . t) 't]
       ['(t . b) 'b]
       ['(t . f) 'f]
       ['(b . t) 't]
       ['(b . b) 'b]
       ['(b . f) 'f]
       ['(f . t) 't]
       ['(f . b) 't]
       ['(f . f) 't])]
    [(cimp ,[fm1] ,[fm2])
     (match `(,fm1 . ,fm2)
       ['(t . t) 't]
       ['(t . b) 'b]
       ['(t . f) 'f]
       ['(b . t) 't]
       ['(b . b) 'b]
       ['(b . f) 'b]
       ['(f . t) 't]
       ['(f . b) 't]
       ['(f . f) 't])]
    [(box ,[fm])
     (match fm
       ['t 't]
       ['b 'f]
       ['f 'f])]
    [(diamond ,[fm])
     (match fm
       ['t 't]
       ['b 't]
       ['f 'f])])
  (Formula ir))

(define-pass eval-case : L-full (ir h) -> * (val)
  (Formula : Formula (ir) -> * (val)
    [,x (if (hash-has-key? h x)
          (hash-ref h x)
          (error (format "variable ~a is not assigned a value" x)))]
    [,v v]
    [(and ,[fm1] ,[fm2])
     (case `(,fm1 . ,fm2)
       [((t . t)) 't]
       [((t . b)) 'b]
       [((t . f)) 'f]
       [((b . t)) 'b]
       [((b . b)) 'b]
       [((b . f)) 'f]
       [((f . t)) 'f]
       [((f . b)) 'f]
       [((f . f)) 'f])]
    [(or ,[fm1] ,[fm2])
     (case `(,fm1 . ,fm2)
       [((t . t)) 't]
       [((t . b)) 't]
       [((t . f)) 't]
       [((b . t)) 't]
       [((b . b)) 'b]
       [((b . f)) 'b]
       [((f . t)) 't]
       [((f . b)) 'b]
       [((f . f)) 'f])]
    [(not ,[fm])
     (case fm
       [(t) 'f]
       [(b) 'b]
       [(f) 't])]
    [(dimp ,[fm1] ,[fm2])
     (case `(,fm1 . ,fm2)
       [((t . t)) 't]
       [((t . b)) 'b]
       [((t . f)) 'f]
       [((b . t)) 't]
       [((b . b)) 'b]
       [((b . f)) 'f]
       [((f . t)) 't]
       [((f . b)) 't]
       [((f . f)) 't])]
    [(cimp ,[fm1] ,[fm2])
     (case `(,fm1 . ,fm2)
       [((t . t)) 't]
       [((t . b)) 'b]
       [((t . f)) 'f]
       [((b . t)) 't]
       [((b . b)) 'b]
       [((b . f)) 'b]
       [((f . t)) 't]
       [((f . b)) 't]
       [((f . f)) 't])]
    [(box ,[fm])
     (case fm
       [(t) 't]
       [(b) 'f]
       [(f) 'f])]
    [(diamond ,[fm])
     (case fm
       [(t) 't]
       [(b) 't]
       [(f) 'f])])
  (Formula ir))

; we need to write a plain-racket evaluator to be able to do synthesis with rosette
(define (eval-plain f h)
  (match f
    [x #:when (variable? x) (hash-ref h x)]
    [v #:when (value? v) v]
    [`(and ,f1 ,f2)
      (case `(,(eval-plain f1 h) . ,(eval-plain f2 h))
        [((t . t)) 't]
        [((t . b)) 'b]
        [((t . f)) 'f]
        [((b . t)) 'b]
        [((b . b)) 'b]
        [((b . f)) 'f]
        [((f . t)) 'f]
        [((f . b)) 'f]
        [((f . f)) 'f])]
    [`(or ,f1 ,f2)
      (case `(,(eval-plain f1 h) . ,(eval-plain f2 h))
        [((t . t)) 't]
        [((t . b)) 't]
        [((t . f)) 't]
        [((b . t)) 't]
        [((b . b)) 'b]
        [((b . f)) 'b]
        [((f . t)) 't]
        [((f . b)) 'b]
        [((f . f)) 'f])]
    [`(dimp ,f1 ,f2)
      (case `(,(eval-plain f1 h) . ,(eval-plain f2 h))
        [((t . t)) 't]
        [((t . b)) 'b]
        [((t . f)) 'f]
        [((b . t)) 't]
        [((b . b)) 'b]
        [((b . f)) 'f]
        [((f . t)) 't]
        [((f . b)) 't]
        [((f . f)) 't])]
    [`(cimp ,f1 ,f2)
      (case `(,(eval-plain f1 h) . ,(eval-plain f2 h))
        [((t . t)) 't]
        [((t . b)) 'b]
        [((t . f)) 'f]
        [((b . t)) 't]
        [((b . b)) 'b]
        [((b . f)) 'b]
        [((f . t)) 't]
        [((f . b)) 't]
        [((f . f)) 't])]
    [`(not ,f)
      (case (eval-plain f h)
        [(t) 'f]
        [(b) 'b]
        [(f) 't])]
    [`(box ,f)
      (case (eval-plain f h)
        [(t) 't]
        [(b) 'f]
        [(f) 'f])]
    [`(diamond ,f)
      (case (eval-plain f h)
        [(t) 't]
        [(b) 't]
        [(f) 'f])]))

(module+ test
  (eval (parse-L-full '(or p (and t b))) (make-hash '((p . f)))))

; with plain functions
(define (and/3 fm1 fm2)
  (case `(,fm1 . ,fm2)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 'b]
    [((b . b)) 'b]
    [((b . f)) 'f]
    [((f . t)) 'f]
    [((f . b)) 'f]
    [((f . f)) 'f]))

(define (or/3 fm1 fm2)
  (case `(,fm1 . ,fm2)
    [((t . t)) 't]
    [((t . b)) 't]
    [((t . f)) 't]
    [((b . t)) 't]
    [((b . b)) 'b]
    [((b . f)) 'b]
    [((f . t)) 't]
    [((f . b)) 'b]
    [((f . f)) 'f]))

(define (dimp/3 fm1 fm2)
  (case `(,fm1 . ,fm2)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 't]
    [((b . b)) 'b]
    [((b . f)) 'f]
    [((f . t)) 't]
    [((f . b)) 't]
    [((f . f)) 't]))

(define (cimp/3 fm1 fm2)
  (case `(,fm1 . ,fm2)
    [((t . t)) 't]
    [((t . b)) 'b]
    [((t . f)) 'f]
    [((b . t)) 't]
    [((b . b)) 'b]
    [((b . f)) 'b]
    [((f . t)) 't]
    [((f . b)) 't]
    [((f . f)) 't]))

(define (not/3 fm)
  (case fm
    [(t) 'f]
    [(b) 'b]
    [(f) 't]))

(define (box/3 fm)
  (case fm
    [(t) 't]
    [(b) 'f]
    [(f) 'f]))

(define (diamond/3 fm)
  (case fm
    [(t) 't]
    [(b) 't]
    [(f) 'f]))

; now let's use Rosette to find if we can encode all the connectives in terms of and, or, and not

; to get a symbolic 3-value, we use a bitvector of size 2
(define (bv-to-3 b)
  (cond
    [(bvule b (bv 1 2)) 't]
    [(bveq b (bv 2 2)) 'b]
    [(bveq b (bv 3 2)) 'f]))

(define-symbolic x y (bitvector 2))
(define x/3 (bv-to-3 x))
(define y/3 (bv-to-3 y))

(eval-case (parse-L-full `(not x)) (make-hash `((x . ,(bv-to-3 x)))))
(eval-plain '(not x) (make-hash `((x . ,(bv-to-3 x)))))

(define sol
  (solve
    (assert (eq? (eval-plain '(not x) (make-hash `((x . ,x/3)))) 't))))

sol ; should be 'f, i.e. #b11

(define sol-3
  (solve
    (assert (eq? (not/3 x/3) 'f))))

(println (format "(eq? (not/3 x/3) 'b): ~a" sol-3))

(define-grammar (and-or-not x)
  [expr
    (choose
      x
      (list 'and (expr) (expr))
      (list 'or (expr) (expr))
      (list 'not (expr)))])

; (define-grammar (and-or-not-2 x y)
  ; [expr
    ; (choose
      ; x y
      ; (list 'and (expr) (expr))
      ; (list 'or (expr) (expr))
      ; (list 'not (expr)))])


(define (my-not x)
  (and-or-not x #:depth 0))
; (define (my-diamond x)
  ; (and-or-not x #:depth 5))
; (define (my-cimp x y)
  ; (and-or-not-2 x y #:depth 6))

; TODO: (parse-L-full (my-not 'x)) fails and it's going to be hard to fix that...
; so we have to write an evaluator in plain racket

; (define (is-not f x)
  ; (eq?
    ; (eval-plain (f x) (hash))
    ; (eval-plain `(not ,x) (hash))))

(define (is-not f x)
  (eq?
    (f x)
    (not/3 x)))

; (define (is-diamond f x)
  ; (eq?
    ; (eval (f x) (hash))
    ; (eval `(diamond ,x) (hash))))

; (define (is-cimp f x y)
  ; (eq?
    ; (eval (f x y) (hash))
    ; (eval `(cimp ,x ,y) (hash))))

(define sol-2
  (synthesize
    #:forall (list x)
    #:guarantee (is-not my-not x/3)))

sol-2

(print-forms sol-2)

; TODO does not seem to work... error tracer show errors...
; maybe just define and, or, etc as functions
