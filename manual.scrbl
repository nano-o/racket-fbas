#lang scribble/manual

@(require
   scribble/eval
   (for-label
     racket
     @; (only-in gamble rejection-sampler sampler->discrete-dist)
     @; (rename-in "qset.rkt" [expand expand-qset])
     "qset.rkt"))

@title{The racket-fbas library}

Welcome to the documentation of the racket-fbas library.

@section{Quorum sets}

@defmodule[racket-fbas/qset]

@defproc[(node/c [x any/c]) boolean?]{
    A contract identifying datums that can be nodes, that is something for which @racket[eqv?] is semantic equivalence, i.e. interned symbols, numbers, and characters.
}

@defstruct[qset ([threshold exact-positive-integer?] [validators (listof node/c)] [inner-qsets (listof qset?)])]{
    A structure type for quorum sets.
}

@defproc[(qset-kw [#:threshold t exact-positive-integer?] [#:validators vs (listof node/c)] [#:inner is (listof qset?)]) qset?]{
    Keyword constructor for qset structures.
}

@(define my-eval (make-base-eval))
@interaction-eval[#:eval my-eval (require racket "qset.rkt")]

@defproc[(sat? [q qset?] [s (set/c node/c)]) boolean?]{
    Whether the set of nodes @racket[s] satisfies the quorum set @racket[q].
}

@examples[
    #:eval my-eval
    (define qset-1
      (qset-kw #:threshold 2 #:validators '(1 2 3) #:inner empty))
    qset-1
    (define qset-2
      (qset-kw #:threshold 2 #:validators '(a b c) #:inner empty))
    (define qset-3
      (qset-kw #:threshold 2 #:validators '(x y z) #:inner empty))
    (define qset-4
      (qset-kw #:threshold 3 #:validators (list 'A 'B 'C) #:inner (list qset-1 qset-2 qset-3)))
    qset-4
    (sat? qset-1 (set 1))
    (sat? qset-1 (set 1 2))
    (sat? qset-2 (set 'b 'c))
    (sat? qset-4 (set 'A 'B 1 2))
    (sat? qset-4 (set 'A 'B 1 'a))
    (sat? qset-4 (set 'A 1 2 'y 'z))
    (sat? qset-4 (set 'A 'B 'C))]

@defproc[(conf/c [x any/c]) boolean?]{
    Contract that recognizes an fbas configuration, i.e. a hash map associating nodes to qsets.
}

@defproc[(quorum? [c conf/c] [s (set/c node/c)]) boolean?]{
    Whether the set of nodes @racket[s] is a quorum in configuration @racket[c]
}

@examples[
    #:eval my-eval
    qset-1
    (define my-conf
      (code:comment @#,elem{we give every node the same quorum set, namely qset-1})
      (make-immutable-hash (map cons '(1 2 3) (make-list 3 qset-1))))
    my-conf
    (quorum? my-conf (set 1 2))
    (quorum? my-conf (set 3))
    (quorum? my-conf (set 1 2 3))
    (quorum? my-conf (set))]
