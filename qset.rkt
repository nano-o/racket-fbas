#lang racket

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
    [expand (-> qset? (set/c set?))]
    [qset-member? (-> qset? node/c boolean?)]
    [qset-members (-> qset? set?)]
    [sat? (-> qset? set? boolean?)]
    [quorum? (-> conf/c set? boolean?)]))

; a node is something for which eqv? is semantic equivalence, i.e. interned symbols, numbers, and characters.
(define node/c
  (or/c boolean? (and/c symbol? symbol-interned?) number? char?))

; A quorum-set represents sets of sets of nodes using thresholds
; This is what is used on the wire in the Stellar network
(define-struct qset (threshold validators inner-qsets) #:transparent)

(define (qset-kw #:threshold t #:validators vs #:inner qs)
  (qset t vs qs))

(module+ test
  (require rackunit)
  (provide (all-defined-out))

  ; examples of qsets

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
    (qset-kw #:threshold 2 #:validators (list 'A) #:inner (list qset-1 qset-3 qset-4))))

; We will use cartesian-product to transform a qset into an fbas
(define (cartesian-product ss)
  ;(-> (listof set?) set?)
  (match ss
    [(list s1) s1]
    [(list s1 s2)
     (list->set
       (apply
         append
         (for/list ([e1 s1])
           (for/list ([e2 s2])
             (list e1 e2)))))]
    [(cons s1 ss)
     (define ts (cartesian-product ss))
     (list->set
       (apply
         append
         (for/list ([e s1])
           (for/list ([t ts])
             (cons e t)))))]))

(module+ test
  (test-case
    "cartesian-product"
    (check-equal?
      (cartesian-product (list (set 'a 'b)))
      (set 'a 'b))
    (check-equal?
      (cartesian-product (list (set 'a 'b) (set)))
      (set))
    (check-equal?
      (cartesian-product (list (set 'a 'b) (set '1 '2)))
      (list->set '((a 1) (a 2) (b 1) (b 2))))
    (check-equal?
      (cartesian-product (list (set 'a 'b) (set '1 '2) (set 'x 'y)))
      (list->set '((a 1 x) (a 1 y) (a 2 x) (a 2 y) (b 1 x) (b 1 y) (b 2 x) (b 2 y))))))

; TODO use on qset struct:

(define (elems qs)
  (append (qset-validators qs) (qset-inner-qsets qs)))

(define (expand qs)
  ;(-> qset? (set/c set?))
  (define es
    (elems qs))
  (define es-expanded
    ; list of sets of sets
    (for/list ([e es])
      (cond
        [(qset? e) (expand e)]
        [else (set (set e))])))
  (define cs
    (combinations es-expanded (qset-threshold qs)))
  (cond
    [(empty? es) (set)]
    [(apply
       set-union
       (for/list ([c cs])
         (for/set ([t (cartesian-product c)])
                  (apply set-union t))))]))

(module+ test
  (test-case
    "expand"
    (check-equal?
      (expand qset-1)
      (list->set (map list->set '((1 2) (1 3) (2 3)))))
    (check-equal?
      (expand qset-2)
      (set))
    (check-equal?
      (expand qset-5)
      (list->set (map list->set '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z)))))
    (check-equal?
      (expand qset-6)
      (list->set (map list->set '((1 2 a b) (1 2 a c) (1 2 b c) (1 3 a b) (1 3 a c) (1 3 b c) (2 3 a b) (2 3 a c) (2 3 b c) (1 2 x y) (1 2 x z) (1 2 y z) (1 3 x y) (1 3 x z) (1 3 y z) (2 3 x y) (2 3 x z) (2 3 y z) (1 2 A) (1 3 A) (2 3 A) (a b x y) (a b x z) (a b y z) (a c x y) (a c x z) (a c y z) (b c x y) (b c x z) (b c y z) (a b A) (a c A) (b c A) (x y A) (x z A) (y z A)))))))

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
        (qset-members inn)))))

(module+ test
  (test-case
    "qset-members"
    (check-equal?
      (qset-members qset-1)
      (set 1 2 3))
    (check-equal?
      (qset-members qset-6)
      (set 'A 1 2 3 'a 'b 'c 'x 'y 'z))))

; whether s satisfies the requirements of the qset
(define (sat? q s)
  (define t
    (for/fold
      ([n 0])
      ([e (elems q)])
      (cond
        [(and (node/c e) (set-member? s e))
         (+ n 1)]
        [(and (qset? e) (sat? e s))
         (+ n 1)]
        [else n])))
  (>= t (qset-threshold q)))

(module+ test
  (test-case
    "sat?"
    (check-true (sat? qset-1 (set 1 2)))
    (check-false (sat? qset-1 (set 1)))
    (check-true (sat? qset-5 (set 1 2 'x 'z)))
    (check-true (sat? qset-6 (set 'A 'x 'z)))
    (check-false (sat? qset-6 (set 'A 'a 'y)))))

(define conf/c
  (hash/c node/c qset?))

(define/contract (quorum? conf q)
  (-> conf/c set? boolean?)
  (for/and ([n q])
    (sat? (hash-ref conf n) q)))

(define (quorum?-2 conf q)
  (define expanded
    (for/hash ([(k v) (in-hash conf)])
      (values k (expand v))))
  (for/and ([n q])
    (for/or ([s (hash-ref expanded n)])
      (subset? s q))))

(module+ test
  (define nodes
    '(A a b c x y z 1 2 3))
  (define conf
    (make-immutable-hash (map cons nodes (make-list 10 qset-6))))
  (for ([q (map list->set (combinations nodes))])
    (check-equal? (quorum? conf q) (quorum?-2 conf q))))
