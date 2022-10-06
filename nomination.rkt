#lang scribble/lp2

@title{The nomination protocol}

The nomination protocol is a protocol whose goal is to agree on a proposed
block (see the Stellar Whitepaper for a full description). Nodes use federated
voting to nominate blocks and a node stops voting for new blocks as soon as it
has confirmed a block. Thus, nomination is guaranteed to converge to a fixed
set of confirmed blocks, which can then be combined deterministically to form
the nominated block. The problem is that there's no way to tell when nomination
has converged, and that's why we need the balloting protocol.

Nomination proceeds in rounds. In each round, nodes pick a leader and vote for
the leader's block (and a node that picks itself as leader votes for a block of
its choice). Nodes use a local (pseudo-random) procedure to determine the round
leader, and it is not guaranteed that all nodes pick the same leader.

To pick a leader, a node first computes its set of neighbors for the round. A
node is a neighbor if its weight (as described below) is larger than a
pseudo-random value, that we'll call the threshold, assigned to the node
(obtained using a round-specific has function). So, the higher its weight the
more likely a node is a neighbor. Moreover, a node always considers itself a
neighbor. Then, a node assigns a second pseudo-random value to each neighbor,
called priority, also using a round-specific hash function, and picks the
neighbor with highest priority as the leader.

The weight of a node n' from the point of view of node n depends on n's quorum
set. The weight of n' in a qset Q that consists of N validators (among which
n') and threshold K is K/N (the probability of picking n' if we pick K out of N
at random). If n' is not in Q, it's 0. Now the weight of n' in a qset Q
consisting of N inner qsets and threshold K, assuming n' appears in only one
inner qset Q', is K/N multiplied by the weight of n' in Q'. This generalizes
easily to mixed validator/inner-qset quorum sets.

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

@chunk[<*>
(require racket "qset.rkt")]
