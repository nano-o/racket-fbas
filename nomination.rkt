#lang scribble/lp2

@title{The nomination protocol}

@chunk[<nomination-main>
(require racket "qset.rkt")
(provide
  weight
  nomination-votes
  accepted-nominated?)
<nomination-votes>
<check-success>
<tests>]

@(require scribble/example racket/sandbox)
@(define my-eval
   (make-base-eval '(require racket "qset.rkt" (submod "qset.rkt" test))))

@section{The high-level protocol}

The nomination protocol is a protocol whose goal is to agree on a proposed
block (see the Stellar Whitepaper for a full description). Nodes use federated
voting to nominate blocks and a node stops voting for new blocks as soon as it
has confirmed a block. Thus, nomination is guaranteed to converge to a fixed
set of confirmed blocks, which can then be combined deterministically to form
the nominated block. The problem is that there's no way to tell when nomination
has converged, and so there is no way to guarantee that all nodes nominate the
same value; that's why we need the balloting protocol after nomination.
However, in normal circumstances, we should expect nomination to produce a
single nominated value, which is then fed to the balloting protocol.

Nomination proceeds in rounds. In each round, each node picks a leader and
votes for a value voted for by the leader, and a node that picks itself as
leader votes for a value of its choice.

In this file, we are interested in estimating the probability that, assuming no
failures and that the network is as fast as need be, a quorum of nodes votes
for the same value in the first round. A priori, it seems that, in some
not-very-symmetric configurations, the probability of success would be small,
and this would be bad in practice.

@section{Casting votes}

To represent the votes cast by the nodes, we use a hashmap that maps a node
either to its vote or to @racket[#f] if it has not voted. Initially, nobody has
voted. Then, nodes that think they are leaders vote for their own identifier.
Once those votes are cast, each node whose leader has now cast a vote casts a
vote too, and so on until we reach a fixed point. Each step of this process is
accomplished using the function @code{nomination-step}.

First we define the initial state, where all nodes are assigned @racket[#f].

@chunk[<init-state>
(define (s-0 conf)
  (make-immutable-hash
    (zip (hash-keys conf) (make-list (hash-count conf) #f))))
<zip>]

And then the votes are obtained by applying the @code{nomination-step}
function, starting from the initial state, until we reach a fixed point.

@chunk[<nomination-votes>
(define (nomination-votes conf leader-of)
  ((until-fixpoint (λ (s) (nomination-step leader-of s))) (s-0 conf)))
<init-state>
<fixedpoint>]

And the step function follows the explanation above:

@chunk[<nomination-votes>
(define (nomination-step leader-of s)
  (for/hash ([(n v) (in-hash s)])
    (cond
      [(not (equal? v #f)) (values n v)]
      [else
        (cond
          [(not (leader-of n)) (values n #f)]
          [(equal? (leader-of n) n) (values n n)]
          [else (values n (hash-ref s (leader-of n)))])])))
<leader-of>]

In the code above, the @code{leader-of} is a parameter. @code{(leader-of n)}
should return the leader of node @code{n}.

@section{Picking a leader}

To pick a leader, a node first computes its set of neighbors for the round. A
node is a neighbor if its weight (as described below) is larger than a
pseudo-random value, that we'll call the the node's threshold, assigned to the
node (obtained using a round-specific hash function). So, the higher its weight
the more likely a node is a neighbor. There is just one special case: a node
always considers itself a neighbor.

@chunk[<neighbors>
(define (neighbors n qset T) (code:comment "T associates its threshold (a number between 0 and 1) to each node")
  (set-union
    (set n) (code:comment "a node is always in its neighbors set (it has weight 1 implicitly)")
    (for/set
      ([m (qset-members qset)]
       #:when (< (hash-ref T m) (weight qset m)))
      m)))
<weight>]

Note that the set of neighbors of a node n may consist of only n when every
node has a threshold higher than its weight.

A few basic tests, remembering that:
@examples[#:label #f #:eval my-eval qset-1]

@chunk[<test-neighbors>
(module+ test
  (define T1 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.1))))
  (define T2 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.9))))
  (test-case
    "neighbors"
    (check-true
      (set=?
        (neighbors 1 qset-1 T1)
        (set 1 2 3)))
    (check-true
      (set=?
        (neighbors 1 qset-1 T2)
        (set 1 2)))))]

Once the neighors set is computed, a node assigns a second pseudo-random value
to each neighbor, called priority and noted P, also using a round-specific hash function,
and picks the neighbor with highest priority as the leader.

@chunk[<leader-of>
(define (leader n qset T P)
  (define ns (neighbors n qset T))
  (cond
    [(set-empty? ns) #f]
    [else
      (define neighbors-priorities
        (for/list
          ([m ns])
          `(,m . ,(hash-ref P m))))
      (car
        (argmax
          cdr
          neighbors-priorities))]))
<neighbors>]

A few tests:

@chunk[<test-leader>
(module+ test
  (define P1 (make-immutable-hash '((1 . 0.1) (2 . 0.2) (3 . 0.3))))
  (test-case
    "leader"
    (check-equal?
      (leader 1 qset-1 T1 P1)
      3)
    (check-equal?
      (leader 1 qset-1 T2 P1)
      2)))]

@subsection{Computing a node's weight}

The weight of a node m from the point of view of node n depends on n's quorum
set. The weight of m in a qset Q that consists of N validators (among which
m) and threshold K is K/N (the probability of picking m if we pick K out of N
at random). If m is not in Q, it's 0. The weight of m in a qset Q
consisting of N inner qsets and threshold K, assuming m appears in only one
inner qset Q', is K/N multiplied by the weight of m in Q'. This generalizes
easily to mixed validator/inner-qset quorum sets.

@chunk[<weight>
(define (weight qs p)
  (define (contains-p? e)
    (cond
      [(qset? e) (qset-member? e p)]
      [else (eqv? p e)]))
  (define e (code:comment "the element in which p first occurs")
    (findf contains-p? (elems qs)))
  (define r (code:comment "K/N")
    (/ (qset-threshold qs) (length (elems qs))))
  (cond
    [(qset? e)
     (* (weight e p) r)]
    [(not e) 0] (code:comment "p is not in the qset qs")
    [else r]))]

Note that the code above only makes sense when a node appears in at most one
element of a qset.

Now a few tests, remembering that:
@examples[#:label #f #:eval my-eval
    qset-1
    qset-5
    qset-6
]

@chunk[<test-weight>
(module+ test
  (test-case
    "weight"
    (check-equal? (weight qset-1 '1) (/ 2 3))
    (check-equal? (weight qset-5 '1) (/ 4 9))
    (check-equal? (weight qset-6 '1) (/ 1 3))
    (check-equal? (weight qset-6 'A) (/ 1 2))))]

An important thing to note is that, in the real protocol, all nodes agree on
the threshold and priority of a given node (because they all use the same hash
function). So, if two nodes assign the same weight to a third node, then either
both count it as a neighbor or none does. This implies that, in highly
symmetric configurations, nodes will have similar neighbor sets. If all nodes
have the same quorum set, the only reason for which neighbor sets may be
different is that a node includes itself by default in its neighbor set.

@section{Checking whether a quorum voted unanimously}

We next define, given a configuration and a state, whether there is a quorum
that has voted for the same value. In this case, we say that the value is accepted nominated (this is the terminology used in the federated voting algorithm).

We just test, for each value voted for at least once, whether a quorum has voted for it:

@chunk[<accepted?>
(define (accepted-nominated? conf s)
  (for/or ([v (list->set (hash-values s))])
    (and
      (not (equal? v #f))
      (quorum? conf (voted-for s v)))))
<voted-for>]

Given a state and a value, @code{voted-for} computes the set of nodes which has
voted for the value:

@chunk[<voted-for>
  (define (voted-for s v)
    (for/set
      ([(n w) (in-hash s)]
       #:when (equal? v w))
      n))]

@section{Putting it all together}

We are now ready to define, given a configuration, neighbor-thresholds, and
priorities, whether there is a quorum that will vote for the same value. We
just compute the votes and then use @code{accepted-nominated?}.

@chunk[<check-success>
(define (check-success conf T P)
  (define (leader-of n)
   (leader n (hash-ref conf n) T P))
  (define votes
   (nomination-votes conf leader-of))
  (accepted-nominated? conf votes))
<accepted?>]

And we conclude with a few tests.

@chunk[<test-check-success>
(module+ test
  (define conf0
    (make-immutable-hash
      (zip '(1 2 3) (make-list 3 qset-1))))
  (test-case
    "accepted-nominated?"
    (check-true
      (check-success conf0 T1 P1))))]

@section{Auxiliary functions}

@chunk[<fixedpoint>
(define (until-fixpoint f)
  (define (go v)
    (let ([fv (f v)])
      (if (equal? fv v)
        fv
        (go fv))))
  go)]

@chunk[<zip>
(define (zip l1 l2)
  (map cons l1 l2))]

@subsection{The tests}

@chunk[<tests>
(module+ test
  (require
    (submod "qset.rkt" test)
    rackunit)
  (provide
    (all-defined-out)
    (all-from-out (submod "qset.rkt" test))))
<test-weight>
<test-neighbors>
<test-leader>
<test-check-success>]
