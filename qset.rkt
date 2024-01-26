#lang racket
(require
  (only-in racket/hash hash-union! hash-union)
  #;racket/trace
  racket/pretty
  racket/generic)

(provide
  (contract-out
    [node/c contract?]
    [qset/c contract?]
    [stellar-network/c contract?]
    [struct qset
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
  add-missing-qsets)

; a node is something for which eqv? is semantic equivalence, i.e. interned symbols, numbers, and characters.
(define node/c
  (or/c boolean? (and/c symbol? (or/c symbol-interned? symbol-unreadable?)) number? char?))

; validators must be a seteqv
; inner-qsets must be a set
(define-struct qset (threshold validators inner-qsets) #:transparent)

(define (qset/kw #:threshold t #:validators vs #:inner-qsets qs)
  (qset t vs qs))

(define (qset-elements q)
  (set-union
    (for/set ([v (qset-validators q)]) v)
    (qset-inner-qsets q)))

(define (qset/c q)
  (struct/dc qset
             [threshold (and/c (< 0 (qset-threshold q)) (<= (qset-threshold q) (set-count (qset-elements q))))]
             [validators (set/c node/c #:cmp 'eqv)]
             [inner-qsets (set/c qset/c #:cmp 'equal)]))

(module+ test
  (require rackunit)
  (define qset-1
    (qset/kw #:threshold 2 #:validators (seteqv 1 2 3) #:inner-qsets (set)))
  (define qset-2
    (qset/kw #:threshold 2 #:validators (seteqv) #:inner-qsets (set)))
  (define qset-3
    (qset/kw #:threshold 2 #:validators (seteqv 'a 'b 'c) #:inner-qsets (set)))
  (define qset-4
    (qset/kw #:threshold 2 #:validators (seteqv 'x 'y 'z) #:inner-qsets (set)))
  (define qset-5
    (qset/kw #:threshold 2 #:validators (set) #:inner-qsets (set qset-1 qset-3 qset-4)))
  (define qset-6
    (qset/kw #:threshold 2 #:validators (seteqv 'A) #:inner-qsets (set qset-1 qset-3 qset-4)))

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

(define (reachable-inner-qsets qset)
  (define iqs
    (qset-inner-qsets qset))
  (set-union
    iqs
    (for/fold
      ([acc (set)])
      ([iq (in-set iqs)])
      (set-union acc (reachable-inner-qsets iq)))))

(module+ test
  (check-equal?
    (qset-inner-qsets qset-6)
    (set (qset 2 (seteqv 'z 'y 'x) (set)) (qset 2 (seteqv 'a 'b 'c) (set)) (qset 2 (seteqv 1 2 3) (set)))))

(define (nodes-in-qset q)
  (set-union
    (qset-validators q)
    (apply
      set-union
      (cons (seteqv) ; to avoid an empty list
            (for/list ([iq (qset-inner-qsets q)])
              (nodes-in-qset iq))))))

(define (network-members network)
  (apply
    set-union
    (cons (seteqv) ; to avoid an empty list
          (for/list ([(_ q) (in-dict network)])
            (nodes-in-qset q)))))

(define (nodes-without-qset network)
  (set-subtract
    (network-members network)
    (apply seteqv (dict-keys network))))

(define (no-nodes-with-no-qset network)
  (set-empty? (nodes-without-qset network)))

(define stellar-network/c
  (and/c
    (listof (cons/c node/c qset/c)) ; association list; why not hash?
    no-nodes-with-no-qset))

(module+ test
  (check-false
    (stellar-network/c `((p . ,qset-1)))))

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

(define-generics symbol-generator
  (gen-get-symbol symbol-generator v))
(define-struct my-sym-gen (prefix [count #:mutable] [syms #:mutable])
  #:methods gen:symbol-generator
  [(define (gen-get-symbol g v)
     (if (dict-has-key? (my-sym-gen-syms g) v)
       (dict-ref (my-sym-gen-syms g) v)
       (begin
         (set-my-sym-gen-count! g (+ (my-sym-gen-count g) 1))
         (let ()
           (define sym (string->unreadable-symbol (format "~a-gen-sym-~a" (my-sym-gen-prefix g) (my-sym-gen-count g))))
           (set-my-sym-gen-syms! g (dict-set (my-sym-gen-syms g) v sym))
           sym))))])

(define (flatten-qsets network)
  ; builds a new qset configuration that has quorum-intersection if and only if the original one has it, and where no quorumset has any inner quorum sets.
  (define sym-gen (my-sym-gen "flatten-qsets" 0 null))
  (define inner-qsets
    (apply
      set-union
      (set)
      (for/list ([q (apply set (dict-values network))])
        (reachable-inner-qsets q))))
  (define (flatten q)
    (define new-validators
      (for/seteqv ([iq (qset-inner-qsets q)])
        (gen-get-symbol sym-gen iq)))
    (qset/kw
      #:threshold (qset-threshold q)
      #:validators (set-union (qset-validators q) new-validators)
      #:inner-qsets (set)))
  (define existing
    (for/list ([(p q) (in-dict network)])
      (cons p (flatten q))))
  (define new
    (for/list ([q inner-qsets])
      (cons (gen-get-symbol sym-gen q) (flatten q))))
  (append existing new))

(module+ test
  (check-true
    (for/and ([q (dict-values (flatten-qsets `((p . ,qset-6))))])
      (set-empty? (qset-inner-qsets q)))))

(define (collapse-qsets network)
  (define sym-gen (my-sym-gen "collapse-qsets" 0 null))
  (define qsets
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
          #:validators (seteqv (gen-get-symbol sym-gen q))
          #:inner-qsets (set)))
      (let ()
        (define collapsed
          (qset/kw
            #:threshold (qset-threshold q)
            #:validators (set-union
                           (qset-validators q)
                           (for/seteqv ([q2 (in-set (set-intersect (qset-inner-qsets q) to-collapse))])
                                       (gen-get-symbol sym-gen q2)))
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
        (gen-get-symbol sym-gen q)
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
