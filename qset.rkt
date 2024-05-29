#lang racket
; #lang errortrace racket

; TODO can we analyze the effect of malicious activity by splitting some points into two? Then how do we modify qsets/slices?

(require
  graph ; for computing strongly connected components
  syntax/parse/define
  sugar
  racket/random
  ; racket/trace
  ; racket/pretty
  ; sugar/debug
  "cliques.rkt")

; TODO projection onto a set
; TODO intersection check and quorum check when all orgs can be collapsed and all validators have qset that's a threshold of orgs (easy in that case...). Also easy to compute resilience bounds. Even whether the network is "resilient".
; TODO good-case check: find maximal scc, check closure is whole network; find maximal clique of intertwined members of the scc (with heuristic); if not the whole scc, check closure of the clique is the whole network; if failure we can try another clique (we expect to have a big maximal clique that should be easy to hit).
; TODO non-intersection good case? If closure of scc is not whole set, can we find a quorum in its complement? Not necessarily. We can if it is a quorum. A pair of nodes may fail the cheap intertwinedness check; then we do a more thourough direct intertwinedness check (essentially enumerating their slices). Any other easy cases?

(provide
  (contract-out
    [node/c contract?]
    [qset/c contract?]
    [stellar-network/c contract?]
    [struct qset ; TODO: why not qset/c?
      ((threshold exact-positive-integer?)
       (validators (set/c node/c #:cmp 'eqv))
       (inner-qsets (set/c any/c #:cmp 'equal)))]
    [qset/kw
      (->
        #:threshold exact-positive-integer?
        #:validators (set/c node/c #:cmp 'eqv)
        #:inner-qsets (set/c any/c #:cmp 'equal)
        qset?)]
    [flatten-qsets (-> stellar-network/c stellar-network/c)]
    [collapse-qsets (-> stellar-network/c stellar-network/c)])
  invert-qset-map
  nodes-without-qset
  add-missing-qsets
  qset-network->slices-network
  network-intertwined?/incomplete
  quorums->slices)

(module+ test
  (require rackunit))

; a node is something for which eqv? is semantic equivalence, i.e. symbols, numbers, and characters.
(define node/c
  (or/c symbol? number? char?))

; validators must be a seteqv
; inner-qsets must be a set
; TODO why not just an assoc list?
(define-struct qset (threshold validators inner-qsets) #:prefab) ; prefab to simplify serialization/deserialization

; contract for qsets
(define qset/c
  (flat-rec-contract c
    (struct/dc qset
               [threshold (validators inner-qsets) #:flat (and/c ((curry <) 0) ((curry >=) (+ (set-count validators) (set-count inner-qsets))))]
               [validators (set/c node/c #:cmp 'eqv)]
               [inner-qsets (set/c c #:cmp 'equal)])))


(define (qset/kw #:threshold t #:validators [vs (seteqv)] #:inner-qsets [iqs (set)])
  (qset t vs iqs))

(define-syntax-parser mk-qset ; TOTO simplify this
  [(_ t (v ...) (iq ...)) #'(qset t (seteqv v ...) (set iq ...))]
  [(_ #:threshold t #:validators v ... #:inner-qsets iq ...)
   #'(qset t (seteqv v ...) (set iq ...))]
  [(_ #:threshold t #:validators v ...)
   #'(qset t (seteqv v ...) (set))]
  [(_ #:threshold t #:inner-qsets iq ...)
   #'(qset t (seteqv) (set iq ...))])

(module+ test
  (check-true (qset/c (mk-qset 1 (1 2 3) ())))
  (check-true (qset/c (mk-qset #:threshold 1 #:validators 1 2 3 #:inner-qsets (mk-qset 1 (1 2 3) ()))))
  (check-true (qset/c (mk-qset #:threshold 1 #:validators 1 2 3))))

; TODO macro to create qsets without specifying seteqv and set

(module+ test
  (define qset-1
    (mk-qset #:threshold 2 #:validators 1 2 3))
  (check-true (qset/c qset-1))
  (define qset-2
    (mk-qset #:threshold 2 #:validators #:inner-qsets))
  (check-false (qset/c qset-2))
  (define qset-3
    (mk-qset #:threshold 2 #:validators 'a 'b 'c))
  (check-true (qset/c qset-3))
  (define qset-4
    (mk-qset #:threshold 2 #:validators 'x 'y 'z))
  (check-true (qset/c qset-4))
  (define qset-5
    (mk-qset #:threshold 2 #:inner-qsets qset-1 qset-3 qset-4))
  (check-true (qset/c qset-5))
  (define qset-6
    (mk-qset #:threshold 2 #:validators 'A #:inner-qsets qset-1 qset-3 qset-4))
  (check-true (qset/c qset-6))

  ; we now check that equal? on qsets behaves as we expect:
  (check-true
    (equal?
      qset-1
      (qset/kw #:threshold 2 #:validators (seteqv 2 1 3 1) #:inner-qsets (set))))
  (check-true
    (equal?
      qset-6
      (qset/kw
        #:threshold 2
        #:validators (seteqv 'A)
        #:inner-qsets
        (set
          qset-4
          qset-3
          (qset/kw #:threshold 2 #:validators (seteqv 2 1 3 1) #:inner-qsets (set)))))))

(define (qset-elements q)
  (set-union
    (apply set (set->list (qset-validators q))) ; just because qset-validators is a seteqv...
    (qset-inner-qsets q)))

(module+ test
  (check-equal?
    (qset-elements
      (qset/kw
        #:threshold 2
        #:validators (seteqv 1 2 3)
        #:inner-qsets (set)))
    (set 1 2 3))
  (check-equal?
    (qset-elements
      (qset/kw
        #:threshold 2
        #:validators (seteqv 'A)
        #:inner-qsets (set (qset/kw #:threshold 2 #:validators (seteqv 1 2 3) #:inner-qsets (set)))))
    (set 'A (qset 2 (seteqv 1 2 3) (set))))
  (check-equal?
    (qset-elements
      (qset/kw
        #:threshold 2
        #:validators (seteqv)
        #:inner-qsets (set (qset/kw #:threshold 2 #:validators (seteqv 1 2 3) #:inner-qsets (set)))))
    (set (qset 2 (seteqv 1 2 3) (set)))))

(define (qset-members q)
  (set-union
    (qset-validators q)
    (apply set-union
           (cons (seteqv) ; set-union cannot handle an empty list
                 (for/list ([iq (qset-inner-qsets q)])
                   (qset-members iq))))))

(module+ test
  (check-equal?
    (qset-members
      (qset/kw
        #:threshold 2
        #:validators (seteqv 1 2 3)
        #:inner-qsets (set)))
    (seteqv 1 2 3))
  (check-equal?
    (qset-members
      (qset/kw
        #:threshold 2
        #:validators (seteqv 'A)
        #:inner-qsets (set (qset/kw #:threshold 2 #:validators (seteqv 1 2 3) #:inner-qsets (set)))))
    (seteqv 'A 1 2 3))
  (check-equal?
    (qset-members
      (qset/kw
        #:threshold 2
        #:validators (seteqv)
        #:inner-qsets (set (qset/kw #:threshold 2 #:validators (seteqv 1 2 3) #:inner-qsets (set)))))
    (seteqv 1 2 3)))

(define (reachable-inner-qsets q)
  (define iqs
    (qset-inner-qsets q))
  (set-union
    iqs
    (for/fold
      ([acc (set)])
      ([iq (in-set iqs)])
      (set-union acc (reachable-inner-qsets iq)))))

(module+ test
  (check-equal?
    (reachable-inner-qsets
      (qset/kw
        #:threshold 2
        #:validators (seteqv)
        #:inner-qsets
          (set
            (qset/kw
              #:threshold 2
              #:validators (seteqv 'x 'y 'z)
              #:inner-qsets (set))
            (qset/kw
              #:threshold 2
              #:validators (seteqv 1 2 3)
              #:inner-qsets
                (set
                  (qset/kw
                    #:threshold 2
                    #:validators (seteqv 'a 'b 'c)
                    #:inner-qsets
                      (set)))))))
    (set
      (qset 2 (seteqv 1 2 3) (set (qset 2 (seteqv 'c 'b 'a) (set))))
      (qset 2 (seteqv 'z 'y 'x) (set))
      (qset 2 (seteqv 'c 'b 'a) (set)))))

(define (qset-empty? qs)
  (empty? (qset-elements qs)))

(define (ll->ss ll)
  (list->set (map list->set ll)))

; computes the set of slices corresponding to a qset
(define (slices q)
  (define (slices-rec qs)
    (define elem-slices
      (for/list ([e (qset-elements qs)])
        (cond
          [(qset? e) (slices-rec e)]
          [else (list (list e))])))
    (define cs
      (combinations elem-slices (qset-threshold qs)))
    (apply
      set-union
      (cons null ; set-union fails with no arguments
            (for/list ([c cs])
              (for/list ([tuple (apply cartesian-product c)])
                (apply set-union tuple))))))
  (cond
    [(qset-empty? q)
     (set)]
    [else (ll->ss (slices-rec q))]))

(define (qset-network->slices-network network)
  (for/list ([(p q) (in-dict network)])
    (cons p (slices q))))

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
      (ll->ss '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (1 2 A) (1 3 A) (2 3 A) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z) (a b A) (a c A) (b c A) (x y A) (x z A) (y z A))))))

; given a set of quorums, assigns to each point the set of quorums that contain it
(define (quorums->slices qs)
  (define ps
    (apply set-union (cons (set) (set->list qs))))
  (define (slices-of p)
    (for/set ([q qs] #:when (set-member? q p))
      q))
  (for/list ([p ps])
    (cons p (slices-of p))))

(module+ test
  (check-equal?
    (dict-ref (quorums->slices (set (set 1 2) (set 2 3))) 1)
    (set (set 1 2)))
  (check-equal?
    (dict-ref (quorums->slices (set (set 1 2) (set 2 3))) 2)
    (set (set 1 2) (set 2 3))))

(define (slices->quorumset ss)
  (define iqs
    (for/set ([s ss])
      (qset/kw
        #:threshold (set-count s)
        #:validators (apply seteqv (set->list s))
        #:inner-qsets (set))))
  (qset/kw
    #:threshold 1
    #:validators (seteqv)
    #:inner-qsets iqs))

(module+ test
  (check-equal?
    (slices->quorumset (list (set 1 2) (set 2 3)))
    (mk-qset
      #:threshold 1
      #:validators
      #:inner-qsets (qset 2 (seteqv 1 2) (set)) (qset 2 (seteqv 2 3) (set)))))

(define (fixpoint f v)
  (if (equal? (f v) v)
    v
    (fixpoint f (f v))))

(module+ test
  (define (f v) (if (< v 42) (+ 1 v) v))
  (check-equal? (fixpoint f 0) 42))

(define (blocked? q P)
  (define (directly-blocked q blocked-set)
    (>
      (+
        (set-count (set-intersect (qset-elements q) blocked-set))
        (qset-threshold q))
      (set-count (qset-elements q))))
  (define qs
    (set-union (set q) (reachable-inner-qsets q)))
  (define (compute-blocked blocked-set)
    (set-union
      blocked-set
      (for/set ([q qs] #:when (directly-blocked q blocked-set))
        q)))
  (set-member? (fixpoint compute-blocked P) q))

(module+ test
  (check-true
    (blocked?
      (qset/kw
        #:threshold 2
        #:validators (seteqv 1 2 3)
        #:inner-qsets (set))
      (set 1 2)))
  (check-false
    (blocked?
      (qset/kw
        #:threshold 2
        #:validators (seteqv 1 2 3)
        #:inner-qsets (set))
      (set 2)))
  (check-false
    (blocked?
      (qset/kw
        #:threshold 2
        #:validators (seteqv 'u)
        #:inner-qsets
        (set
          (qset/kw
            #:threshold 2
            #:validators (seteqv 'x 'y 'z)
            #:inner-qsets (set))
          (qset/kw
            #:threshold 2
            #:validators (seteqv 1 2)
            #:inner-qsets
            (set
              (qset/kw
                #:threshold 2
                #:validators (seteqv 'a 'b 'c)
                #:inner-qsets
                (set))))))
      (set 'u 'x 2 'c)))
  (check-true
    (blocked?
      (qset/kw
        #:threshold 2
        #:validators (seteqv 'u)
        #:inner-qsets
        (set
          (qset/kw
            #:threshold 2
            #:validators (seteqv 'x 'y 'z)
            #:inner-qsets (set))
          (qset/kw
            #:threshold 2
            #:validators (seteqv 1 2)
            #:inner-qsets
            (set
              (qset/kw
                #:threshold 2
                #:validators (seteqv 'a 'b 'c)
                #:inner-qsets
                (set))))))
      (set 'u 2 'b 'c))))

(define (closure P network)
  (define (blocked-set P)
    (set-union
      P
      (for/set ([(p q) (in-dict network)]
                #:when (blocked? q P))
        p)))
  (fixpoint blocked-set P))

(module+ test
  (check-equal?
    (closure
      (set 'q)
      (list
        (cons 'q (qset 1 (seteqv 'q) (set)))
        (cons 'r (qset 1 (seteqv 'p) (set)))
        (cons 'p (qset 1 (seteqv 'q) (set)))))
    (set 'p 'q 'r))
  (check-equal?
    (closure
      (set 'p)
      (list
        (cons 'q (qset 1 (seteqv 'q) (set)))
        (cons 'r (qset 1 (seteqv 'p) (set)))
        (cons 'p (qset 1 (seteqv 'q) (set)))))
    (set 'p 'r)))

(define (network-members network)
  (apply
    set-union
    (cons (seteqv) ; to avoid an empty list
          (for/list ([(_ q) (in-dict network)])
            (qset-members q)))))

(define (nodes-without-qset network)
  (set-subtract
    (network-members network)
    (apply seteqv (dict-keys network))))

(define (no-orphans? network)
  (set-empty? (nodes-without-qset network)))

(define stellar-network/c
  (and/c
    (listof (cons/c node/c qset/c)) ; TODO association list; why not hash?
    no-orphans?))

(module+ test
  (check-false
    (stellar-network/c `((p . ,qset-1)))))

; add empty qsets to nodes that have a missing qset
(define (add-missing-qsets network)
  (append
    network
    (for/list ([n (nodes-without-qset network)])
      (cons
        n
        (qset/kw
          #:threshold 1
          #:validators (seteqv n)
          #:inner-qsets (set))))))

(define (flatten-qsets network)
  ; builds a new qset configuration that has quorum-intersection if and only if the original one has it, and where no quorumset has any inner quorum sets.
  ; (define sym-gen (make-sym-gen))
  ; TODO is the following guaranteed to cache stuff? this is crucial for correctness here
  (define sym-gen (make-caching-proc (λ (_) (gensym "qset-proxy"))))
  ; (define sym-gen (my-sym-gen "flatten-qsets" 0 null))
  (define inner-qsets
    (apply
      set-union
      (set)
      (for/list ([q (apply set (dict-values network))])
        (reachable-inner-qsets q))))
  (define (flatten q)
    (define new-validators
      (for/seteqv ([iq (qset-inner-qsets q)])
        (sym-gen iq)))
    (qset/kw
      #:threshold (qset-threshold q)
      #:validators (set-union (qset-validators q) new-validators)
      #:inner-qsets (set)))
  (define existing
    (for/list ([(p q) (in-dict network)])
      (cons p (flatten q))))
  (define new
    (for/list ([q inner-qsets])
      (cons (sym-gen q) (flatten q))))
  (append existing new))

(module+ test
  (check-true
    (for/and ([q (dict-values (flatten-qsets `((p . ,qset-6))))])
      (set-empty? (qset-inner-qsets q)))))

; collapse some qsets to a single point, e.g. orgs whose validators only ever appear as the same org in other qsets (and whose threshold is > 1/2)
; NOTE marginal utility... inner qsets are small
(define (collapse-qsets network)
  ; (define sym-gen (make-sym-gen))
  (define sym-gen (make-caching-proc (λ (_) (gensym "flattened-qset"))))
  (define qsets ; all the qsets (including inner ones)
    (set-union
      (apply set (dict-values network))
      (apply
        set-union
        (cons
          (set)
          (for/list ([q (dict-values network)])
            (reachable-inner-qsets q))))))
  (define (collapsible? q)
    ; a qset can be collapsed to a point when:
    ;   * it does not have inner qsets
    ;   * its threshold is greater than 1/2
    ;   * its members do not appear anywhere except in this very qset
    ;   * its members all have the same qset
    (and
      (for/and ([v (qset-validators q)])
        (and
          (dict-has-key? network v)
          (equal?
            (dict-ref network v)
            (dict-ref network (car (set->list (qset-validators q)))))))
      (set-empty? (qset-inner-qsets q))
      (> (* 2 (qset-threshold q)) (set-count (qset-validators q)))
      (for/and ([q2 (in-set qsets)])
        (or (equal? q q2)
            (set-empty? (set-intersect (qset-validators q) (qset-validators q2)))))
      (> (set-count (qset-validators q)) 1)))
  ; first, identify all the qsets to collapse
  ; second, collapse their occurences
  ; finally, give the new points their qsets
  (define to-collapse
    (apply set (filter collapsible? (set->list qsets))))
  (define (collapse q)
    (if (set-member? to-collapse q)
      (begin
        (qset/kw
          #:threshold 1
          #:validators (seteqv (sym-gen q))
          #:inner-qsets (set)))
      (let ()
        (define collapsed
          (qset/kw
            #:threshold (qset-threshold q)
            #:validators (set-union
                           (qset-validators q)
                           (for/seteqv ([q2 (in-set (set-intersect (qset-inner-qsets q) to-collapse))])
                                       (sym-gen q2)))
            #:inner-qsets (for/set
                            ([q2 (in-set
                                   (set-subtract
                                     (qset-inner-qsets q)
                                     to-collapse))])
                            (collapse q2))))
          collapsed)))
  (define existing-points
    (for/list ([(p q) (in-dict network)])
      (cons p (collapse q))))
  (define new-points
    (for/list ([q to-collapse])
      (cons
        (sym-gen q)
        ; we give the new validator, which corresponds to an old qset q, the qsets of the validators in q (they all have the same qset)
        (dict-ref existing-points (car (set->list (qset-validators q)))))))
  (append new-points existing-points))

(module+ test
  (check-not-exn (thunk (collapse-qsets `(,(cons 'p qset-6))))))

(define (invert-qset-map qset-map)
  ; assumes flat qsets
  (for/fold
    ([acc null])
    ([(p q) (in-dict qset-map)])
    (if (dict-has-key? acc q)
      (dict-set acc q (cons p (dict-ref acc q)))
      (dict-set acc q (list p)))))

(module+ test

  (define conf-1
    (list
      (cons 'q (qset 1 (seteqv 'q) (set)))
      (cons 'r (qset 1 (seteqv 'p) (set)))
      (cons 'p (qset 1 (seteqv 'q) (set)))))

  ; (invert-qset-map conf-1)

  (check-equal?
    (invert-qset-map `(,(cons 'q qset-1) ,(cons 'p qset-1)))
    (list (list (qset 2 (seteqv 1 2 3) (set)) 'p 'q))))

;; Nice networks
; TODO submodule?

(define (flat-qsets? network) ; TODO
  (for/and ([q (dict-values network)])
    (set-empty? (qset-inner-qsets q))))

(define (blocked q P) ; q must no have inner qsets
  (>
    (+
      (set-count (set-intersect (qset-validators q) P))
      (qset-threshold q))
    (set-count (qset-validators q))))

(define (flat-closure P qset-map)
  (define to-add
    (for/seteqv ([p (network-members qset-map)]
              #:when (blocked (dict-ref qset-map p) P))
      p))
  (if (set-empty? (set-subtract to-add P))
    P
    (flat-closure (set-union P to-add) qset-map)))

(module+ test
  (define network-1
    (for/list ([p '(1 2 3)])
      (cons p qset-1)))
  (check-equal?
    (flat-closure (seteqv 1) network-1)
    (seteqv 1))
  (check-equal?
    (flat-closure (seteqv 1 2) network-1)
    (seteqv 1 2 3))
  (check-equal?
    (flat-closure (seteqv 1 3) network-1)
    (seteqv 1 2 3)))

(define (network-to-graph net)
  (define edges
    (for*/list ([p (network-members net)]
                [q (network-members net)]
                #:when (set-member? (qset-members (dict-ref net p)) q))
      (list p q)))
  (unweighted-graph/directed edges))

; heuristic that is sound (i.e. if it returns true, then the qsets are intertwined) but not complete
; results are cached (NOTE the cache uses `equal?`)
(define/caching (intertwined?/incomplete q1 q2)
  (define inter
    (set-intersect
      (qset-elements q1) (qset-elements q2)))
  (and
    (>
      (+ (qset-threshold q1) (qset-threshold q2) (set-count inter))
      (+ (set-count (qset-elements q1)) (set-count (qset-elements q2))))
    (for/and ([e inter])
      (or
        (not (qset? e))
        (and
          (set-empty? (qset-inner-qsets e))
          (> (* 2 (qset-threshold e)) (set-count (qset-validators e))))))))

(module+ test
  (check-true
    (intertwined?/incomplete
      (mk-qset
        #:threshold 2
        #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))
      (mk-qset
        #:threshold 2
        #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))))
    (check-false
      (intertwined?/incomplete
        (mk-qset
          #:threshold 2
          #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))
        (mk-qset
          #:threshold 2
          #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 1
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))))
    (check-true
      (intertwined?/incomplete
        (mk-qset
          #:threshold 2
          #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))
        (mk-qset
          #:threshold 3
          #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 100 101 102)
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))))
    (check-false
      (intertwined?/incomplete
        (mk-qset
          #:threshold 2
          #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 'a 'b 'c)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3))
        (mk-qset
          #:threshold 3
          #:inner-qsets
          (mk-qset
            #:threshold 2
            #:validators 100 101 102)
          (mk-qset
            #:threshold 3
            #:validators 'a 'b 'c 'd)
          (mk-qset
            #:threshold 2
            #:validators 'x 'y 'z)
          (mk-qset
            #:threshold 2
            #:validators 1 2 3)))))

(define (intertwined-graph P net)
  (define edges
    (for*/list ([p1 P] [p2 P]
                #:when (intertwined?/incomplete (dict-ref net p1) (dict-ref net p2)))
      (list p1 p2)))
  (unweighted-graph/undirected edges))

; TODO: only for flat networks:
(define (non-transitive-intersection? ps network)
  (unless (for/and ([p ps])
            (set-empty? (qset-inner-qsets (dict-ref network p))))
    (error "all qsets must be flat"))
    (for*/and ([(p1 q1) (in-dict network)]
               #:when (set-member? ps p1)
               [(p2 q2) (in-dict network)]
               #:when (set-member? ps p2))
      (define inter (set-intersect (qset-validators q1) (qset-validators q2)))
      (>
        (+ (qset-threshold q1) (qset-threshold q2) (set-count inter))
        (+ (set-count (qset-validators q1)) (set-count (qset-validators q2))))))

(define (max-scc g)
    (car (sort (scc g) (λ (l1 l2) (> (length l1) (length l2))))))

(define (all-pairs-intertwined?/incomplete P network)
  (for*/and ([p1 P] [p2 P])
    (intertwined?/incomplete (dict-ref network p1) (dict-ref network p2))))

(define (shows-intertwined P network)
  (define nodes (apply set (dict-keys network)))
  (cond
    [(not (set=? (closure P network) nodes))
     (displayln "Closure does not cover the whole network")
     #f]
    [(all-pairs-intertwined?/incomplete P network)
     #t]
    [else
      (for/or ([_ (range 1 10)]) ; we'll try 10 random cliques
        (set=? (closure (random-clique P network) network) nodes))]))

(define (random-clique P network)
  (for/fold ([rejected (set)]
             [clique (set)]
             #:result clique)
            ([p (shuffle (set->list P))])
    (define in-clique?
      (for/and ([p2 clique])
        (intertwined?/incomplete (dict-ref network p) (dict-ref network p2))))
    (values
      (if in-clique? rejected (set-add rejected p))
      (if in-clique? (set-add clique p) clique))))

; (module+ test
  ; (random-seed (integer-bytes->integer (crypto-random-bytes 2) #f))
  ; (random-clique
    ; '(1 2 3 a b c)
    ; (append
      ; (for/list ([p '(1 2 3)]) (cons p (mk-qset #:threshold 2 #:validators 1 2 3)))
      ; (for/list ([p '(a b c)]) (cons p (mk-qset #:threshold 2 #:validators 'a 'b 'c))))))

(define (network-intertwined?/incomplete network)
  (define mscc
    (apply set (max-scc (network-to-graph network))))
  (cond
    [(shows-intertwined mscc network) #t]
    [else #f]
    #;[else
      ; TODO this is useless in its current form (it's too expensive to compute all cliques upfront)
      ; What we need is a heuristic to efficiently compute an on-demand stream of large cliques
      ; Since we expect a big clique, pick a node, compute a clique, and if it doesn't work pick a node in the complement of the clique and try again; maybe then give up if that does not work.
      (displayln "WARNING: taking exponential branch")
      (define max-cliques (find-maximal-cliques (intertwined-graph mscc network)))
      (for/or ([mc max-cliques])
        (shows-intertwined mc network))]))

; TODO test network with 4 orgs, global threshold 3, inner 2/3; play with variations
; TODO bigger network to test having some orgs that screw up their config

(module+ test
  (define g1 (network-to-graph network-1))
  (check-equal? (length (get-edges g1)) 9))

(module+ test
  (require racket/serialize)
  (define stellar-network
    (with-input-from-file
      "./stellarbeat.data"
      (thunk (deserialize (read)))))
  (network-intertwined?/incomplete stellar-network)

  ; (define bscc ; biggest scc
    ; (car (sort (scc (network-to-graph stellar-network)) (λ (l1 l2) (> (length l1) (length l2))))))
  ; (define bscc-network
    ; (for/list ([(p q) (in-dict stellar-network)]
               ; #:when (set-member? bscc p))
      ; (cons p q)))

  ; (set-count (apply set (dict-values bscc-network)))
  ; (set-count (reachable-inner-qsets (car (dict-values bscc-network))))

  ; (define collapsed-bscc-network (collapse-qsets bscc-network))
  ; (check-true (flat-qsets? collapsed-bscc-network))
  ; (check-true (non-transitive-intersection? (dict-keys bscc-network) collapsed-bscc-network))

  ; (define flattened-stellar-network (flatten-qsets stellar-network))
  ; (check-true (flat-qsets? flattened-stellar-network))
  #;(set-count (flat-closure (apply seteqv biggest-scc) flattened-stellar-network))
  #;(set-count (closure (apply set biggest-scc) stellar-network))
  #;(set-count (network-members flattened-stellar-network)))

; TODO find small quorum (use SSCs), check intersection, check closure covers network
; Use unweighted-graph/directed
