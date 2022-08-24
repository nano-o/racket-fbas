#lang racket

(require "qset.rkt")

; nomination protocol

; a draw associates numbers between 0 and 1 to nodes
(define draw/c
  (hash/c node/c number?))

(define conf/c
  (hash/c node/c qset?))

(define (quorum? conf q)
  (for/and ([n q])
    (sat? (hash-ref conf n) q)))

(define/contract (neighbors qset N)
  (-> qset? draw/c set?)
  (for/set
    ([n (qset-members qset)]
     #:when (< (hash-ref N n) (weight qset n)))
    n))

(module+ test
  (require
    (submod "qset.rkt" test)
    rackunit)
  (define N1 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.1))))
  (define N2 (make-immutable-hash '((1 . 0.1) (2 . 0.1) (3 . 0.9))))
  (test-case
    "neighbors"
    (check-true
      (set=?
        (neighbors qset-1 N1)
        (set 1 2 3)))
    (check-true
      (set=?
        (neighbors qset-1 N2)
        (set 1 2)))))

(define/contract (leader qset N P)
  (-> qset? draw/c draw/c node/c)
  (define neighbors-weights
    (for/list
      ([m (neighbors qset N)])
      `(,m . ,(hash-ref P m))))
  (cond
    [(empty? (neighbors qset N))
     #f]
    [else
      (car
        (argmax
          cdr
          neighbors-weights))]))

(module+ test
  (define P1 (make-immutable-hash '((1 . 0.1) (2 . 0.2) (3 . 0.3))))
  (test-case
    "leader"
    (check-equal?
      (leader qset-1 N1 P1)
      3)
    (check-equal?
      (leader qset-1 N2 P1)
      2)))

(define state/c
  (hash/c node/c node/c))

(define/contract (nomination-step conf N P s)
  (-> conf/c draw/c draw/c state/c state/c)
  (for/hash ([(n v) (in-hash s)])
    (cond
      [(not (equal? v #f)) (values n v)]
      [else
        (define l (leader (hash-ref conf n) N P))
        (cond
          [(equal? l n) (values n n)]
          [(not l) (values n #f)]
          [else (values n (hash-ref s l))])])))

(define (zip l1 l2)
  (map cons l1 l2))

(define (s-0 conf)
  (make-immutable-hash
    (zip (hash-keys conf) (make-list (hash-count conf) #f))))

(module+ test
  (define conf0
    (make-immutable-hash
      (zip '(1 2 3) (make-list 3 qset-1))))
  (test-case
    "nomination-step"
    (check-equal?
      (nomination-step conf0 N1 P1 (s-0 conf0))
      (make-immutable-hash '((1 . #f) (2 . #f) (3 . 3))))))

(define (until-fixpoint f)
  (define (fixpoint-f v)
    (let ([fv (f v)])
      (if (equal? fv v)
        fv
        (fixpoint-f fv))))
  fixpoint-f)

(define (nomination-votes conf N P)
  ((until-fixpoint (λ (s) (nomination-step conf N P s))) (s-0 conf)))

(module+ test
  (test-case
    "nomination"
    (check-equal?
      (nomination-votes conf0 N1 P1)
      (make-immutable-hash (zip (hash-keys conf0) (make-list 3 3))))))

; check whether a value has been accepted as nominated
(define/contract (accepted-nominated? conf s)
  (-> conf/c state/c boolean?)
  (define (voted-for v)
    (for/set
      ([(n w) (in-hash s)]
       #:when (equal? v w))
      n))
  (for/or ([v (list->set (hash-values s))])
    (and
      (not (equal? v #f))
      (quorum? conf (voted-for v)))))

(module+ test
  (test-case
    "accepted-nominated?"
    (check-false
      (accepted-nominated? conf0 (nomination-step conf0 N1 P1 (s-0 conf0))))
    (check-true
      (accepted-nominated? conf0 (nomination-votes conf0 N1 P1)))))

; TODO multiple rounds of nomination
