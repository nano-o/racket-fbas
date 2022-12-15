#lang scribble/lp2

@title{Racket implementation of quorum sets}

@section{Overview}

In this file, we provide some functions related to Stellar's quorum sets. In
particular, we define a struct to represent quorum sets, and, given a set of
nodes and a quorum set for each node, the function @code{quorum?} cheks whether
a set of nodes is a quorum.

The program consists of a set of exported bindings, a data structure to
represent quorum sets, a function to compute the set of slices corresponding to
a quorum set, the function @code{sat?}, which computes whether a set of nodes
satisfies a quorum set, a notion of quorum system (or configuration), the
function @code{quorum?}, which cheks whether a set of nodes is a quorum in a
quorum system, and some tests:

@chunk[<qset-main>
(require racket)
<provide>
<basic-qset-defs>
<slices>
<sat?>
<system>
<qset-tests>]

@chunk[<provide>
(provide
  node/c
  conf/c
  (contract-out
    [struct qset
      ((threshold exact-positive-integer?)
       (validators (listof node/c))
       (inner-qsets (listof qset?)))]
    [qset-kw
      (->
        #:threshold exact-positive-integer?
        #:validators (listof node/c)
        #:inner (listof qset?)
        qset?)]
    [elems (-> qset? list?)]
    [slices (-> qset? (set/c set?))]
    [qset-member? (-> qset? node/c boolean?)]
    [qset-members (-> qset? set?)]
    [sat? (-> qset? set? boolean?)]
    [quorum? (-> conf/c set? boolean?)]))]

@section{Basic quorum set definitions}

@chunk[<basic-qset-defs>
<node-contract>
<qset-struct>
<qset-keyword-constructor>
<qset-aux-functions>]

@margin-note{Not sure anymore why we have this requirement. Maybe we want to
use @racket[hasheqv]?}

We start with the contract @code{node/c}, which indicates what kind of datum we
can use to represent nodes. This can be booleans, symbols, numbers, of chars;
essentially, something for which @racket[eqv?] is semantic equivalence.

@chunk[<node-contract>
(define node/c
  (or/c boolean? (and/c symbol? symbol-interned?) number? char?))]

A quorum set is a data structure used in practice by Stellar to describe the
set of quorum slices of a node. A quorum set consists of a threshold, a list of
validators, and a list of inner quorum sets.

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
  (provide (all-defined-out))

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

Next we define a simple function @code{elems} that returns the concatenation of
the validators and inner fields of a qset, a function @code{qset-empty?} that
checks whether a qset is empty, @code{qset-mebmer?}, which checks whether a
node appears anywhere in a qset, and @code{qset-members}, which returns all the
nodes appearing anywhere in a qset.

@chunk[<qset-aux-functions>

(define (elems qs)
  (append (qset-validators qs) (qset-inner-qsets qs)))

(define (qset-empty? qs)
  (empty? (elems qs)))

(define (qset-member? qs p)
  (define in-inner-qsets
    (for/or ([q (qset-inner-qsets qs)])
      (qset-member? q p)))
  (define in-validators
    (and (member p (qset-validators qs)) #t))
  (or in-inner-qsets in-validators))

(define (qset-members qs)
  (apply
    set-union
    (cons
      (list->set (qset-validators qs))
      (for/list ([inn (qset-inner-qsets qs)])
        (qset-members inn)))))]

@chunk[<test-qset-members>
(module+ test
  (test-case
    "qset-members"
    (check-true (qset-member? qset-1 3))
    (check-false (qset-member? qset-1 4))
    (check-true (qset-member? qset-6 'z))
    (check-equal?
      (qset-members qset-1)
      (set 1 2 3))
    (check-equal?
      (qset-members qset-6)
      (set 'A 1 2 3 'a 'b 'c 'x 'y 'z))))]

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
    [(qset-empty? qs)
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

@subsection{Satisfying a quorum set}

A set of nodes satisfies a quorum set when it contains at least one of the
quorum set's slices. The function @code{sat?} checks that a set of nodes
@code{s} satisfies @code{qs} by checking that at least @code{k} elements of
@code{qs}, where @code{k} is the threshold of @code{qs}, are recursively
satisfied.

@chunk[<sat?>
(define (sat? qs s)
  (define t
    (for/fold
      ([n 0])
      ([e (elems qs)])
      (cond
        [(and (node/c e) (set-member? s e))
         (+ n 1)]
        [(and (qset? e) (sat? e s))
         (+ n 1)]
        [else n])))
  (>= t (qset-threshold qs)))]

@chunk[<test-sat?>
(module+ test
  (test-case
    "sat?"
    (check-true (sat? qset-1 (set 1 2)))
    (check-false (sat? qset-1 (set 1)))
    (check-true (sat? qset-5 (set 1 2 'x 'z)))
    (check-true (sat? qset-6 (set 'A 'x 'z)))
    (check-false (sat? qset-6 (set 'A 'a 'y)))))]

We can also check that if @code{sat? qs s} then @code{s} contains a slice of @code{qs}:

@chunk[<test-sat?-contains-slice>
(module+ test
  (test-case
    "sat?-contains-slice"
    (define nodes
      (set->list (qset-members qset-6)))
    (for ([s (map list->set (combinations nodes))])
      (check-equal?
        (sat? qset-6 s)
        (for/or ([sl (slices qset-6)])
          (subset? sl s))))))]

@subsection{System configurations}

A system configuration consists of a set of nodes and a quorum set for each
node.

@chunk[<conf/c>
(define conf/c
  (hash/c node/c qset?))]

A set of nodes is a quorum when it is a non-empty set that satisfies the qsets
of each of its members.

@chunk[<quorum?>
(define (quorum? conf q)
  (and
    (not (set-empty? q))
    (for/and ([n q])
      (sat? (hash-ref conf n) q))))]

@chunk[<system>
<conf/c>
<quorum?>]

@subsection{Minimal quorums}

@chunk[<minimal-quorum?>
(define (minimal-quorum? conf q)
  (not
    (for/or ([s (combinations (set->list q))])
      (quorum? conf (list->seteqv s)))))]

@chunk[<qset-tests>
<test-qset-examples>
<test-qset-members>
<test-slices>
<test-sat?-contains-slice>
<test-sat?>]
