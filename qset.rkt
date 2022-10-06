#lang scribble/lp2

@title{Federated Byzantine Agreement Systems in racket}

@section{Overview}

This library consists of basic definitions, a function that computes a qset's
corresponding slices, and tests.

@chunk[<*>
(require racket)
<basic-qset-defs>
<slices>
<tests>]

@section{Quorum sets}

@chunk[<basic-qset-defs>
<node-contract>
<qset-struct>
<qset-keyword-constructor>
<elems>]

A quorum set is a data structure used in practice by Stellar to describe the
set of quorum slices of a node. In this file we provide functionality related
to quorum sets.

@margin-note{Not sure anymore why we have this requirement. Maybe we want to
use @racket[hasheqv]?}

Nodes can be booleans, symbols, numbers, of chars; essentially, something for
which @racket[eqv?] is semantic equivalence.

@chunk[<node-contract>
(define node/c
  (or/c boolean? (and/c symbol? symbol-interned?) number? char?))]

A quorum set consists of a threshold, a list of validators, and a list of inner
quorum sets.

@chunk[<qset-struct>
(define-struct qset (threshold validators inner-qsets) #:transparent)]

We also provide a keyword constructor.

@chunk[<qset-keyword-constructor>
(define (qset-kw #:threshold t #:validators vs #:inner qs)
  (qset t vs qs))]

This allows to define qsets as follows.

@chunk[<test-qset-examples>
(module+ test
  (require rackunit)

  (define qset-1
    (qset-kw #:threshold 2 #:validators '(1 2 3) #:inner empty))
  (define qset-2
    (qset-kw #:threshold 2 #:validators empty #:inner empty))
  (define qset-3
    (qset-kw #:threshold 2 #:validators '(a b c) #:inner empty))
  (define qset-4
    (qset-kw #:threshold 2 #:validators '(x y z) #:inner empty))
  (define qset-5
    (qset-kw #:threshold 2 #:validators empty #:inner (list qset-1 qset-3 qset-4)))
  (define qset-6
    (qset-kw #:threshold 2 #:validators (list 'A) #:inner (list qset-1 qset-3 qset-4))))]

Next we define a simple function @code{elems} that returns the concatenation of the
validators and inner fields of a qset:

@chunk[<elems>
(define (elems qs)
  (append (qset-validators qs) (qset-inner-qsets qs)))]

@subsection{From quorum sets to slices}

A quorum set corresponds to a set of quorum slices. Next we define a function
that, given a quorum set, returns the set of quorum slices corresponding to
this quorum set. The function is defined recursively. As base case, we take the
set of slices corresponding to a node n as the singleton set \{\{n\}\}. Now to
compute the set of quorum slices of a qset q with m elements and threshold k,
we take all combinations c of k-out-of-m elements, and then we take the
cartesian product of the corresponding sets of quorum slices.

@chunk[<slices-def>
(define (slices qs)
  (define (slices-rec qs)
    (define elem-slices
      (for/list ([e (elems qs)])
        (cond
          [(qset? e) (slices-rec e)]
          [else (list (list e))])))
    (define cs
      (combinations elem-slices (qset-threshold qs)))
    (apply
      set-union
      (for/list ([c cs])
        (for/list ([tuple (apply cartesian-product c)])
          (apply set-union tuple)))))
  (cond
    [(empty? (elems qs))
     (set)]
    [else (ll->ss (slices-rec qs))]))]

In the above, @code{ll->ss} is a convenience function that converts a list of
lists into a set of sets.

@chunk[<ll->ss>
(define (ll->ss ll)
  (list->set (map list->set ll)))]

@chunk[<slices>
<ll->ss>
<slices-def>]

Now a few tests:

@chunk[<test-slices>
(module+ test
  (test-case
    "slices"
    (check-equal?
      (slices qset-1)
      (ll->ss '((1 2) (1 3) (2 3))))
    (check-equal?
      (slices qset-2)
      (set))
    (check-equal?
      (slices qset-5)
      (ll->ss '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z))))
    (check-equal?
      (slices qset-6)
      (ll->ss '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (1 2 A) (1 3 A) (2 3 A) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z) (a b A) (a c A) (b c A) (x y A) (x z A) (y z A))))))]

@chunk[<tests>
<test-qset-examples>
<test-slices>]
