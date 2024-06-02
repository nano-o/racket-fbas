#lang racket

;; quorumsets and operations on them
;; for practical purposes in stellar-core or for stellarbeat, the most important functions are fbas-intertwined?/incomplete and fbas-failure-bound.

(require
  graph ; for computing strongly connected components
  syntax/parse/define
  sugar ; for caching procedures
  )

(provide
  (contract-out
    [node/c contract?]
    [qset/c contract?]
    [stellar-fbas/c contract?]
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
    [flatten-qsets (-> stellar-fbas/c stellar-fbas/c)]
    [collapse-qsets (-> stellar-fbas/c stellar-fbas/c)])
  qset-elements
  qset-members
  qset-member?
  quorum?
  invert-qset-map
  nodes-without-qset
  add-missing-qsets
  qset-fbas->slices-fbas
  fbas-intertwined?/incomplete
  quorums->slices-fbas
  resilient/incomplete
  fbas-failure-bound)

(module+ test
  (require rackunit))

;; we have a set of nodes, also called points
;; a node is something for which eqv? is semantic equivalence, i.e. symbols, numbers, and characters.
;; we're using eqv? for performance reasons, which is probably misguided...
(define node/c
  (or/c symbol? number? char?))

; validators must be a seteqv
; inner-qsets must be a set
(struct qset (threshold validators inner-qsets) #:prefab) ; prefab to simplify serialization/deserialization
; note that this is an immutable struct so we cannot construct circular ones

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
  ; TODO must check that we are not passed sets as elements (confusing with qset/kw...)
  ; but we can't really know before evaluation
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

;; returns the set of elements (validators and inner qsets) of q
(define (qset-elements q)
  (set-union
    (apply set (set->list (qset-validators q))) ; transform the seteqv into a set
    (qset-inner-qsets q)))

; tests whether p appears anywhere in the qset:
(define (qset-member? qs p)
  (define in-inner-qsets
    (for/or ([q (qset-inner-qsets qs)])
      (qset-member? q p)))
  (define in-validators
    (and (member p (qset-validators qs)) #t))
  (or in-inner-qsets in-validators))

;; one way to see a quorumset is as encoding agreement requirements
;; e.g. a node n with quorumset (qset 2 (seteqv 'a 'b 'c) (set)) requires agreement from 2 nodes out of 'a, 'b, and 'c
;; In general, we can determine whether a set P satisfies the requirements of the qset q as follows:
(define (sat? q P)
  ; first we (recursively) compute how many of q's elements are satisfied
  (define t
    (for/fold
      ([n 0])
      ([e (qset-elements q)])
      (cond
        ; if e is a node and it's in P, then it's counted as satisfied:
        [(and (node/c e) (set-member? P e))
         (+ n 1)]
        ; if e is a qset and P satisfies it, then it's counted as satisfied:
        [(and (qset? e) (sat? e P))
         (+ n 1)]
        [else n])))
  ; then we check whether qset-threshold or more are satisfied
  (>= t (qset-threshold q)))

(module+ test
  (check-true (sat? qset-1 (set 1 2)))
  (check-false (sat? qset-1 (set 1)))
  (check-true (sat? qset-5 (set 1 2 'x 'z)))
  (check-true (sat? qset-6 (set 'A 'x 'z)))
  (check-false (sat? qset-6 (set 'A 'a 'y))))

;; (loose) definition
;; ==================
;; a federated Byzantine agreement system (FBAS) is a set of nodes (also called points) each of which has a quorumset (or, alternatively, a set of slices)
(define (no-orphans? fbas)
  (set-empty? (nodes-without-qset fbas)))

(define stellar-fbas/c
  (and/c
    (listof (cons/c node/c qset/c)) ; association list; why not hash?
    no-orphans?))

;; a quorum is a set that satisfies the requirements of all its members
(define (quorum? fbas Q)
  (for/and ([n Q])
    (sat? (dict-ref fbas n) Q)))

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
  (set-empty? (qset-elements qs)))

;; list of lists to set of sets
(define (ll->ss ll)
  (list->set (map list->set ll)))

;; set of sets to list of lists
(define (ss->ll ss)
  (set->list (map set->list ss)))

;; computes the set of slices corresponding to a qset
;; returns a set of sets
(define (slices q)
  (cond
    [(qset-empty? q) (set)]
    [else
      ; recall that the elements of a qset are its validators and immediate inner qsets
      ; each of those elements corresponds to a set of slices:
      (define/caching (elem-slices e)
        (cond
          [(qset? e) (slices e)]
          [else (set (set e))]))
      ; now we obtain each slice of q by picking a number (qset-threshold q) of elements of q and picking one slice of each element
      (apply set-union
        (for/list ([c (combinations (set->list (qset-elements q)) (qset-threshold q))])
          (for/set ([c-slices (apply cartesian-product (ss->ll (map elem-slices c)))])
            (apply set-union c-slices))))]))

;; transforms qsets into sets of slices
(define (qset-fbas->slices-fbas fbas)
  (for/list ([(p q) (in-dict fbas)])
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

;; given a set of quorums, assigns to each point the set of quorums that contain it
(define (quorums->slices-fbas qs)
  (define ps
    (apply set-union (cons (set) (set->list qs))))
  (define (slices-of p)
    (for/set ([q qs] #:when (set-member? q p))
      q))
  (for/list ([p ps])
    (cons p (slices-of p))))

(module+ test
  (check-equal?
    (dict-ref (quorums->slices-fbas (set (set 1 2) (set 2 3))) 1)
    (set (set 1 2)))
  (check-equal?
    (dict-ref (quorums->slices-fbas (set (set 1 2) (set 2 3))) 2)
    (set (set 1 2) (set 2 3))))

;; (trivially) transforms a set of slices into a quorumset
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

;; utility function: recursively apply f until a fixpoint is reached, starting with (f v)
(define (fixpoint f v)
  (if (equal? (f v) v)
    v
    (fixpoint f (f v))))

(module+ test
  (define (f v) (if (< v 42) (+ 1 v) v))
  (check-equal? (fixpoint f 0) 42))

;; whether the set P intersects all slices of the qset q
(define (blocked? q P)
  ; we first mark every inner quorumset iq which has at least (qset-threshold iq) validators in P
  ; then we mark every inner quorumset iq which has at least (qset-threshold iq) elements in P or marked already
  ; etc. until a fixpoint
  ; now if q has been marked then it's blocked (return #t) and otherwise not (return #f)
  (define (mark? q marked)
    (>
      (+
        (set-count (set-intersect (qset-elements q) marked))
        (qset-threshold q))
      (set-count (qset-elements q))))
  (define qs
    (set-union (set q) (reachable-inner-qsets q)))
  (define (new-marked marked)
    (set-union
      marked
      (for/set ([q qs] #:when (mark? q marked))
        q)))
  (set-member? (fixpoint new-marked P) q))

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

;; the topological closure of the set P (thinking of quorums as open sets)
;; that's everything that's recursively blocked by P
;; equivalently, that's all points whose quorums all intersect P
(define (closure P fbas)
  (define (blocked-set P)
    (set-union
      P
      (for/set ([(p q) (in-dict fbas)]
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

(define (fbas-members fbas)
  (apply
    set-union
    (cons (seteqv) ; to avoid an empty list
          (for/list ([(_ q) (in-dict fbas)])
            (qset-members q)))))

(define (nodes-without-qset fbas)
  (set-subtract
    (fbas-members fbas)
    (apply seteqv (dict-keys fbas))))

(module+ test
  (check-false
    (stellar-fbas/c `((p . ,qset-1)))))

;; add self (singleton) qsets to nodes that have a missing qset
(define (add-missing-qsets fbas)
  (append
    fbas
    (for/list ([n (nodes-without-qset fbas)])
      (cons
        n
        (qset/kw
          #:threshold 1
          #:validators (seteqv n)
          #:inner-qsets (set))))))

;; builds a new qset configuration that has quorum-intersection if and only if the original one has it, and where no quorumset has any inner quorumset; we obtain what we call a flat FBAS
(define (flatten-qsets fbas)
  (define/caching (gensym/caching _)  ; NOTE caching behavior is crucial for correctness
    (gensym "qset-proxy"))
  (define inner-qsets
    (apply
      set-union
      (set)
      (for/list ([q (apply set (dict-values fbas))])
        (reachable-inner-qsets q))))
  (define (flatten q)
    (define new-validators
      (for/seteqv ([iq (qset-inner-qsets q)])
        (gensym/caching iq)))
    (qset/kw
      #:threshold (qset-threshold q)
      #:validators (set-union (qset-validators q) new-validators)
      #:inner-qsets (set)))
  (define existing
    (for/list ([(p q) (in-dict fbas)])
      (cons p (flatten q))))
  (define new
    (for/list ([q inner-qsets])
      (cons (gensym/caching q) (flatten q))))
  (append existing new))

(module+ test
  (check-true
    (for/and ([q (dict-values (flatten-qsets `((p . ,qset-6))))])
      (set-empty? (qset-inner-qsets q))))
  ; for an example:
  (flatten-qsets
    `((p . ,(qset/kw
              #:threshold 1
              #:validators (seteqv)
              #:inner-qsets (set (qset/kw
                                   #:threshold 2
                                   #:validators (seteqv 'a 'b 'c)
                                   #:inner-qsets (set))))))))

;; collapse some qsets to a single point, e.g. orgs whose validators only ever appear as the same org in other qsets and whose threshold is > 1/2
; NOTE marginal utility... inner qsets are small anyway
(define (collapse-qsets fbas)
  (define/caching (gensym/caching _)  ; NOTE caching behavior is crucial for correctness
    (gensym "collapsed-qset"))
  (define qsets ; all the qsets (including inner ones)
    (set-union
      (apply set (dict-values fbas))
      (apply
        set-union
        (cons
          (set)
          (for/list ([q (dict-values fbas)])
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
          (dict-has-key? fbas v)
          (equal?
            (dict-ref fbas v)
            (dict-ref fbas (car (set->list (qset-validators q)))))))
      (set-empty? (qset-inner-qsets q))
      (> (* 2 (qset-threshold q)) (set-count (qset-validators q)))
      (for/and ([q2 (in-set qsets)])
        (or (equal? q q2)
            (set-empty? (set-intersect (qset-validators q) (qset-validators q2)))))
      (> (set-count (qset-validators q)) 1)))
  ; first, identify all the qsets to collapse
  ; second, collapse all their occurences
  ; finally, give the new points their qsets
  (define to-collapse
    (apply set (filter collapsible? (set->list qsets))))
  (define (collapse q)
    (if (set-member? to-collapse q)
      (begin
        (qset/kw
          #:threshold 1
          #:validators (seteqv (gensym/caching q))
          #:inner-qsets (set)))
      (let ()
        (define collapsed
          (qset/kw
            #:threshold (qset-threshold q)
            #:validators (set-union
                           (qset-validators q)
                           (for/seteqv ([q2 (in-set (set-intersect (qset-inner-qsets q) to-collapse))])
                                       (gensym/caching q2)))
            #:inner-qsets (for/set
                            ([q2 (in-set
                                   (set-subtract
                                     (qset-inner-qsets q)
                                     to-collapse))])
                            (collapse q2))))
          collapsed)))
  (define existing-points
    (for/list ([(p q) (in-dict fbas)])
      (cons p (collapse q))))
  (define new-points
    (for/list ([q to-collapse])
      (cons
        (gensym/caching q)
        ; we give the new point which corresponds to an old qset q, the qsets of the points in q (they all have the same qset)
        (dict-ref existing-points (car (set->list (qset-validators q)))))))
  (append new-points existing-points))

(module+ test
  (check-not-exn (thunk (collapse-qsets `(,(cons 'p qset-6)))))
  ; here's an example:
  (local
    [(define o1 (qset 2 (seteqv 'o11 'o12 'o13) (set)))
     (define o2 (qset 2 (seteqv 'o21 'o22 'o23) (set)))
     (define o3 (qset 2 (seteqv 'o31 'o32 'o33) (set)))
     (define q (qset 2 (seteqv) (set o1 o2 o3)))
     (define fbas
       (for/list ([p '(o11 o12 o13 o21 o22 o23 o31 o32 o33)])
         `(,p . ,q)))]
    (pretty-print (collapse-qsets fbas))))

;; produces a map from qset to list of points that have the qset
(define (invert-qset-map qset-fbas)
  (for/fold ([acc null]) ([(p q) (in-dict qset-fbas)])
    (if (dict-has-key? acc q)
      (dict-set acc q (cons p (dict-ref acc q)))
      (dict-set acc q (list p)))))

(module+ test
  (check-equal?
    (invert-qset-map `(,(cons 'q qset-1) ,(cons 'p qset-1)))
    `((,(qset 2 (seteqv 1 2 3) (set)) . (p q)))))

(define (flat-fbas? fbas)
  (for/and ([q (dict-values fbas)])
    (set-empty? (qset-inner-qsets q))))

(module+ flat-fbas
  ;; functions applying only to flat FBAS configurations
  (define (blocked q P) ; q must no have inner qsets
    (>
      (+
        (set-count (set-intersect (qset-validators q) P))
        (qset-threshold q))
      (set-count (qset-validators q))))

  (define (flat-closure P qset-map)
    (define to-add
      (for/seteqv ([p (fbas-members qset-map)]
                   #:when (blocked (dict-ref qset-map p) P))
                  p))
    (if (set-empty? (set-subtract to-add P))
      P
      (flat-closure (set-union P to-add) qset-map)))

  #;(module+ test
    (define fbas-1
      (for/list ([p '(1 2 3)])
        (cons p qset-1)))
    (check-equal?
      (flat-closure (seteqv 1) fbas-1)
      (seteqv 1))
    (check-equal?
      (flat-closure (seteqv 1 2) fbas-1)
      (seteqv 1 2 3))
    (check-equal?
      (flat-closure (seteqv 1 3) fbas-1)
      (seteqv 1 2 3))))

;; directed graph where there is an edge from p to q when q appears in p's quorumset
(define (fbas-to-graph net)
  (define edges
    (for*/list ([p (fbas-members net)]
                [q (fbas-members net)]
                #:when (set-member? (qset-members (dict-ref net p)) q))
      (list p q)))
  (unweighted-graph/directed edges))

;; Next we will provide procedures to approximately check (variants of) intertwinedness or compute failure bounds.
;; The general idea for tractable approximation is to check whether qsets requirements "intersecgt" (and not quorum intersection). If the qsets of nodes p1 and p2 "intersect", then p1 and p2's quorums intersect. However if the qsets of p1 and p2 do not intersect, then it's still not clear whether their quorums intersect or not.

;; checks whether every two slices of qsets q1 and q2 intersect
;; heuristic that is sound (i.e. if it returns true, then the qsets are intertwined) but not complete
;; results are cached (NOTE the cache uses `equal?`)
(define (intertwined?/incomplete q1 q2)
  (define t1 (qset-threshold q1))
  (define n1 (set-count (qset-elements q1)))
  (define t2 (qset-threshold q2))
  (define n2 (set-count (qset-elements q2)))
  (define inter ; elements that the two qsets have in common
    (set-intersect
      (qset-elements q1) (qset-elements q2)))
  (define ni (set-count inter))
  (and
    (> (+ t1 t2 ni) (+ n1 n2))
    (for/and ([e inter])
      ; common inner qsets must be flat and have a threshold of more than half
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

;; graph where there is an edge between two points when the heuristic intertwinedness check succeeds
(define (intertwined-graph P net)
  (define edges
    (for*/list ([p1 P] [p2 P]
                #:when (intertwined?/incomplete (dict-ref net p1) (dict-ref net p2)))
      (list p1 p2)))
  (unweighted-graph/undirected edges))

;; a maximal strongly-connected component of the directed graph g
(define (max-scc g)
  (define (longer l1 l2)
    (> (length l1) (length l2)))
  (car (sort (scc g) longer)))

(define (all-pairs-intertwined?/incomplete P fbas)
  (for*/and ([p1 P] [p2 P])
    (intertwined?/incomplete (dict-ref fbas p1) (dict-ref fbas p2))))

;; A set of points P show the fbas is intertwined when:
;; a) the closure of P is the whole fbas
;; b) P is intertwined
(define (shows-intertwined P fbas)
  (define nodes (apply set (dict-keys fbas)))
  (cond
    [(not (set=? (closure P fbas) nodes))
     (displayln "Closure does not cover the whole fbas")
     #f]
    [(all-pairs-intertwined?/incomplete P fbas)
     #t]
    [else
      (for/or ([_ (range 1 10)]) ; let's try 10 random max intertwined sets
        (set=? (closure (random-max-intertwined P fbas) fbas) nodes))]))

;; produces a maximal set of points that are intertwined according to the intertwined?/incomplete
(define (random-max-intertwined P fbas)
  ; this is just building a max clique randomly
  (for/fold ([rejected (set)]
             [clique (set)]
             #:result clique)
            ([p (shuffle (set->list P))])
    (define in-clique?
      (for/and ([p2 clique])
        (intertwined?/incomplete (dict-ref fbas p) (dict-ref fbas p2))))
    (if in-clique?
      (values rejected (set-add clique p))
      (values (set-add rejected p) clique))))

(define (max-fbas-scc fbas)
  (apply set (max-scc (fbas-to-graph fbas))))

;; our main fast and incomplete quorum-intersection check
(define (fbas-intertwined?/incomplete fbas)
  (shows-intertwined (max-fbas-scc fbas) fbas))

(module+ test
  (define fbas-1
    (for/list ([p '(1 2 3)])
      (cons p qset-1)))
  (define g1 (fbas-to-graph fbas-1))
  (check-equal? (length (get-edges g1)) 9))

(module+ test
  (require racket/serialize)
  (define stellar-fbas
    (with-input-from-file
      "./stellarbeat.data"
      (thunk (deserialize (read)))))
  (fbas-intertwined?/incomplete stellar-fbas))

; TODO when the heuristic fails we could nevertheless simplify the problem further to the pass it to the SAT-based checker
; for example, any two points that are known intertwined can be "fused" into one single point

;; q1 and q2 are resiliently-intertwined when they are still intertwined after failures that satisfy both their assumptions
;; we assume that, for each inner quorumset, if one member fails maliciously then all do
(define (resiliently-intertwined/incomplete q1 q2)
  (define t1 (qset-threshold q1))
  (define n1 (set-count (qset-elements q1)))
  (define t2 (qset-threshold q2))
  (define n2 (set-count (qset-elements q2)))
  (define inter ; elements that the two qsets have in common
    (set-intersect
        (qset-elements q1) (qset-elements q2)))
  (define ni ; number of elements that the two qsets have in common
    (set-count inter))
  (define m1 (- (+ t1 ni) n1)) ; worst-case number of common points used by party 1
  (define m2 (- (+ t2 ni) n2)) ; worst-csae number of common points used by party 2
  ; even in the worst case, possible failures cannot affect all common points:
  (and
    (>
      (- (+ m1 m2) ni)
      (min (- ni m1) (- ni m2)))
    (for/and ([e inter])
      ; common inner qsets must be flat and have a threshold of more than half
      (or
        (not (qset? e))
        (and
          (set-empty? (qset-inner-qsets e))
          (> (* 2 (qset-threshold e)) (set-count (qset-validators e))))))))

(define (resilient/incomplete fbas)
  (define mscc (max-fbas-scc fbas))
  (for*/and ([p1 mscc] [p2 mscc])
    (resiliently-intertwined/incomplete
      (dict-ref fbas p1)
      (dict-ref fbas p2))))

(module+ test
  ; traditional BFT quorum systems:
  (check-true ; 3 out of 4 (1 tolerated failure)
    (resiliently-intertwined/incomplete
      (qset 3 (seteqv 'a 'b 'c 'd) (set))
      (qset 3 (seteqv 'a 'b 'c 'd) (set))))
  (check-true ; 4 out of 5 (1 tolerated failure)
    (resiliently-intertwined/incomplete
      (qset 4 (seteqv 'a 'b 'c 'd 'e) (set))
      (qset 4 (seteqv 'a 'b 'c 'd 'e) (set))))
  (check-true ; 5 out of 7 (2 tolerated failures)
    (resiliently-intertwined/incomplete
      (qset 5 (seteqv 'a 'b 'c 'd 'e 'f 'g) (set))
      (qset 5 (seteqv 'a 'b 'c 'd 'e 'f 'g) (set))))
  ; that also works:
  (check-true
    (resiliently-intertwined/incomplete
      (qset 2 (seteqv 'a 'b 'c 'd) (set))
      (qset 4 (seteqv 'a 'b 'c 'd) (set))))
  ; non-resilient cases:
  (check-false ; 2 out of 3 (split-brain when the lone intersection lies)
    (resiliently-intertwined/incomplete
      (qset 2 (seteqv 'a 'b 'c) (set))
      (qset 2 (seteqv 'a 'b 'c) (set))))
  (check-false ; 4 out of 7
    (resiliently-intertwined/incomplete
      (qset 4 (seteqv 'a 'b 'c 'd 'e 'f 'g) (set))
      (qset 4 (seteqv 'a 'b 'c 'd 'e 'f 'g) (set))))
  ; non-symmetric cases:
  (check-false
    (resiliently-intertwined/incomplete
      (qset 3 (seteqv 'a 'b 'c 'd) (set))
      (qset 2 (seteqv 'a 'b 'c 'd) (set))))
  (check-true
    (resiliently-intertwined/incomplete
      (qset 5 (seteqv 'a 'b 'c 'd 'e 'f) (set))
      (qset 3 (seteqv 'a 'b 'c 'd) (set))))
  ; now with inner qsets
  (local
    [(define o1 (qset 2 (seteqv 'o11 'o12 'o13) (set)))
     (define o2 (qset 2 (seteqv 'o21 'o22 'o23) (set)))
     (define o3 (qset 2 (seteqv 'o31 'o32 'o33) (set)))
     (define o4 (qset 2 (seteqv 'o41 'o42 'o43) (set)))
     (define q1 (qset 3 (seteqv) (set o1 o2 o3 o4)))
     (define q2 (qset 1 (seteqv) (set o1 o2 o3)))]
     (check-true ; 3 out of 4
       (resiliently-intertwined/incomplete q1 q1))
     (check-false ; 2 out of 3
       (resiliently-intertwined/incomplete q2 q2))))

;; computes a bound b such that at least b failures can occur without dis-intertwining q1 and q2
;; not guaranteed to be the best bound
(define (failure-bound q1 q2)
  (define t1 (qset-threshold q1))
  (define n1 (set-count (qset-elements q1)))
  (define t2 (qset-threshold q2))
  (define n2 (set-count (qset-elements q2)))
  (define inter ; elements that the two qsets have in common
    (set-intersect
        (qset-elements q1) (qset-elements q2)))
  (define ni ; number of elements that the two qsets have in common
    (set-count inter))
  (define m1 (- (+ t1 ni) n1)) ; worst-case number of common points used by party 1
  (define m2 (- (+ t2 ni) n2)) ; worst-case number of common points used by party 2
  (define inner-qsets-okay
    (for/and ([e inter])
      ; common inner qsets must be flat and have a threshold of more than half
      (or
        (not (qset? e))
        (and
          (set-empty? (qset-inner-qsets e))
          (> (* 2 (qset-threshold e)) (set-count (qset-validators e)))))))
  ; NOTE: this is a number of qset elements (so e.g. orgs)
  (if inner-qsets-okay
    (- (+ m1 m2) ni 1)
    0))

;; computes a bound b such that no number b of failures can dis-intertwine the fbas
;; this is only a lower bound (i.e. it could be that more failures can be tolerated)
(define (fbas-failure-bound fbas)
  (define mscc (max-fbas-scc fbas))
  (for*/fold ([bound (set-count mscc)])
             ([p1 mscc]
              [p2 mscc])
    (define q1 (dict-ref fbas p1))
    (define q2 (dict-ref fbas p2))
    (define b (failure-bound q1 q2))
    #;(when (and (<= b 0) (> bound 0))
      (pretty-print (cons q1 q2)))
    (min b bound)))

(module+ test
  (check-equal?
    (failure-bound
      (qset 3 (seteqv 'a 'b 'c 'd) (set))
      (qset 3 (seteqv 'a 'b 'c 'd) (set)))
    1)
  (check-equal?
    (failure-bound
      (qset 2 (seteqv 'a 'b 'c 'd) (set))
      (qset 3 (seteqv 'a 'b 'c 'd) (set)))
    0)
  (check-equal?
    (failure-bound
      (qset 5 (seteqv 'a 'b 'c 'd 'e 'f 'g) (set))
      (qset 5 (seteqv 'a 'b 'c 'd 'e 'f 'g) (set)))
    2)
  (check-equal?
    (failure-bound
      (qset 5 (seteqv 'a 'b 'c 'd 'e 'f) (set))
      (qset 3 (seteqv 'a 'b 'c 'd) (set)))
    1)
  (local
    [(define o1 (qset 2 (seteqv 'o11 'o12 'o13) (set)))
     (define o2 (qset 2 (seteqv 'o21 'o22 'o23) (set)))
     (define o3 (qset 2 (seteqv 'o31 'o32 'o33) (set)))
     (define o4 (qset 2 (seteqv 'o41 'o42 'o43) (set)))
     (define q1 (qset 3 (seteqv) (set o1 o2 o3 o4)))
     (define q2 (qset 1 (seteqv) (set o1 o2 o3)))]
    (check-equal? ; 3 out of 4
      (failure-bound q1 q1)
      1)
    (check-true ; 2 out of 3
      (<= (failure-bound q2 q2) 0))))
