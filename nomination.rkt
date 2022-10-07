#lang scribble/lp2

@title{The nomination protocol}

@chunk[<nomination-main>
(require racket "qset.rkt")
(provide
  weight
  nomination-votes
  accepted-nominated?)
<weight>
<rest>]

@section{The high-level protocol}

The nomination protocol is a protocol whose goal is to agree on a proposed
block (see the Stellar Whitepaper for a full description). Nodes use federated
voting to nominate blocks and a node stops voting for new blocks as soon as it
has confirmed a block. Thus, nomination is guaranteed to converge to a fixed
set of confirmed blocks, which can then be combined deterministically to form
the nominated block. The problem is that there's no way to tell when nomination
has converged, and that's why we need the balloting protocol. However, in
normal circumstances, we should expect nomination to produce a single nominated
value, which is then fed to the balloting protocol.

Nomination proceeds in rounds. In each round, each node picks a leader and
votes for a value voted for by the leader, and a node that picks itself as
leader votes for a value of its choice.

In this file, we are interested in estimating the probability that, assuming no
failures and that the network is as fast as need be, a quorum of nodes votes
for the same value.

To represent the votes cast by the nodes, we use a hashmap that maps a node
either to its vote or to @racket[#f] if it has not voted. Initially, nodes that
think they are leaders vote for their own identifier. Once those votes are
cast, each node whose leader has now cast a vote casts a vote too, and so on
until we reach a fixpoint. Each step of this process is accomplished using the
function @code{nomination-step}.

@chunk[<nomination-step>
(define (nomination-step leader-of s)
  (for/hash ([(n v) (in-hash s)])
    (cond
      [(not (equal? v #f)) (values n v)]
      [else
        (define l (leader n (hash-ref conf n) N P))
        (cond
          [(not l) (values n #f)]
          [(equal? (leader-of n) n) (values n n)]
          [else (values n (hash-ref s (leader-of n)))])])))]

In the code above, @code{(leader-of n)} returns the leader of node @code{n}.

To pick a leader, a node first computes its set of neighbors for the round. A
node is a neighbor if its weight (as described below) is larger than a
pseudo-random value, that we'll call the threshold, assigned to the node
(obtained using a round-specific has function). So, the higher its weight the
more likely a node is a neighbor. Moreover, a node always considers itself a
neighbor.

@chunk[<neighbors>
(define (neighbors n qset T) (code:comment "T associates its threshold (a number between 0 and 1) to each node")
  (set-union
    (set n) (code:commentl "a node is always in its neighbors set (it has weight 1 implicitly)")
    (for/set
      ([m (qset-members qset)]
       #:when (< (hash-ref T m) (weight qset m)))
      m)))]

Once the neighors set is computed, a node assigns a second pseudo-random value
to each neighbor, called priority, also using a round-specific hash function,
and picks the neighbor with highest priority as the leader.

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

An important thing to note that all nodes agree on the threshold and priority
of a given node (because they all use the same hash function). So, if two nodes
assign the same weight to a third node, then either both count it as a neighbor
or none does. This implies that, in highly symmetric configurations, nodes will
have similar neighbor sets. If all nodes have the same quorum set, the only
reason for which neighbor sets may be different is that a node includes itself
by default in its neighbor set.

Here we are interested in estimating the probability that, in a given
configuration, at least a quorum votes to nominate the same block in the first
round. For this, we model the first nomination round in racket and then sample
the resulting distribution.

@chunk[<rest>
(define nomination-votes null)
(define accepted-nominated? null)]
