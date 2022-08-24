#lang racket

(require
  (only-in "fba.rkt" node/c))
(provide
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
    [weight (-> qset? node/c number?)]))

; A quorum-set represents sets of sets of nodes using thresholds
; This is what is used on the wire in the Stellar network
(define-struct qset (threshold validators inner-qsets))

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

(define (elems qset)
  (append (qset-validators qset) (qset-inner-qsets qset)))

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

; wheight in a qset

(define (qset-member? qset p)
  (define in-inner-qsets
    (for/or ([q (qset-inner-qsets qset)])
      (qset-member? q p)))
  (define in-validators
    (member p (qset-validators qset)))
  (or in-inner-qsets in-validators))

(define (qset-members qset)
  (apply
    set-union
    (cons
      (list->set (qset-validators qset))
      (for/list ([inn (qset-inner-qsets qset)])
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

; This is how core computes weights, but it's not how it's defined in the whitepaper (see tests)
(define/contract (whitepaper-wheight qset p)
  (-> qset? node/c node/c)
  (define es
    (elems qset))
  (define (contains-p? e)
    (cond
      [(qset? e) (qset-member? qset p)]
      [else (eqv? p e)]))
  (define e
    (findf contains-p? es))
  (define r
    (/ (qset-threshold qset) (length es)))
  (cond
    [(qset? e)
     (* (whitepaper-wheight e p) r)]
    [(not e) 0]
    [else r]))

; This is how the weight of a node is defined in the whitepaper
(define (weight qset p)
  (define expanded (expand qset))
  (define n-in
    (length (filter (λ (s) (set-member? s p)) (set->list expanded))))
  (define total (length (set->list expanded)))
  (/ n-in total))

(module+ test
  (test-case
    "weight"
    (check-equal? (whitepaper-wheight qset-1 '1) (/ 2 3))
    (check-equal? (whitepaper-wheight qset-1 '1) (weight qset-1 '1))
    (check-equal? (whitepaper-wheight qset-5 '1) (/ 4 9))
    (check-equal? (whitepaper-wheight qset-5 '1) (weight qset-5 '1))
    (check-equal? (whitepaper-wheight qset-6 '1) (/ 1 3))
    ; NOTE the two computations do not agree here:
    (check-false (equal? (whitepaper-wheight qset-6 '1) (weight qset-6 '1)))
    (check-equal? (whitepaper-wheight qset-6 'A) (/ 1 2))
    ; NOTE the two computations do not agree here:
    (check-false (equal? (whitepaper-wheight qset-6 'A) (weight qset-6 'A)))))
