#lang racket
(require
  (only-in racket/hash hash-union!)
  #;racket/trace
  racket/pretty)

(provide
  (struct-out qset)
  qset/kw
  flatten-qsets
  collapse-orgs
  invert-qset-map)

(define-struct qset (threshold validators inner-qsets) #:prefab)

(define (qset/kw #:threshold t #:validators vs #:inner-qsets qs)
  (qset t vs qs))

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

(define (inner-qsets-rec qset)
  (define iqs
    (qset-inner-qsets qset))
  (set-union
    iqs
    (for/fold
      ([acc (set)])
      ([iq (in-set iqs)])
      (set-union acc (inner-qsets-rec iq)))))

(module+ test
  (check-equal?
    (qset-inner-qsets qset-6)
    (set (qset 2 (seteqv 'z 'y 'x) (set)) (qset 2 (seteqv 'a 'b 'c) (set)) (qset 2 (seteqv 1 2 3) (set)))))

(define (flatten-qsets qset-map)
  ; builds a new qset configuration that has quorum-intersection if and only if the original one has it, and where no quorumset has any inner quorum sets.
  (define (qset-symbol q)
    (string->unreadable-symbol (~v (equal-hash-code q))))
  (define new-qset-map
    (make-hash qset-map)) ; this is mutable
  (define (flatten q) ; NOTE: mutates new-qset-map!
    (define flattened-iqs
      (for/set ([iq (in-set (qset-inner-qsets q))])
        (flatten iq)))
    (define new-points
      (for/hash ([fiq flattened-iqs])
        (values (qset-symbol fiq) fiq))) ; it's okay if it already exists in new-qset-map
    (hash-union!
      new-qset-map
      new-points
      #:combine/key (λ (k v1 v2) v1)) ; NOTE: mutation!
    (qset/kw ; we remove the inner qsets and add corresponding points
      #:threshold (qset-threshold q)
      #:validators (set-union (qset-validators q) (apply seteqv (dict-keys new-points)))
      #:inner-qsets (set)))
  (for ([(p qset) (in-dict qset-map)])
    (hash-set! new-qset-map p (flatten qset))) ; NOTE: mutates new-qset-map!
  ; finally, return an alist:
  (for/list ([(q qs) (in-dict new-qset-map)])
    (cons q qs)))

(module+ test
  (check-true
    (for/and ([q (dict-values (flatten-qsets `((p . ,qset-6))))])
      (set-empty? (qset-inner-qsets q)))))

(define (collapse-orgs qset-map)
  (define (collapsible? q)
    ; a qset can be collapsed to a point when:
    ;   * it does not have inner qsets
    ;   * its threshold is greater than 1/2
    ;   * and its members do not appear anywhere except in this very qset
    ;   * its members all have the same qset
    (define (overlaps-q q2)
      (and
        (not (equal? q q2))
        (or
          (not
            (set-empty?
              (set-intersect (qset-validators q2) (qset-validators q))))
          (for/or ([q3 (qset-inner-qsets q2)])
            (overlaps-q q3)))))
    (and
      (for/and ([v (qset-validators q)])
        (equal?
          (dict-ref qset-map v)
          (dict-ref qset-map (car (set->list (qset-validators q))))))
      (set-empty? (qset-inner-qsets q))
      (> (* 2 (qset-threshold q)) (set-count (qset-validators q)))
      (not
        (for/or ([(_ q2) (in-dict qset-map)])
          (overlaps-q q2)))))
  ; first, identify all the qsets to collapse
  ; second, collapse their occurences
  ; finally, give the new points their qsets
  (define to-collapse
    (let ()
      (define (to-collapse q)
        (cond
          [(collapsible? q) (set q)]
          [(not (set-empty? (qset-inner-qsets q)))
           (apply
             set-union
             (for/list ([iq (in-set (qset-inner-qsets q))])
               (to-collapse iq)))]
          [else (set)]))
      (apply
        set-union
        (for/list ([q (dict-values qset-map)])
          (to-collapse q)))))
  (pretty-print (format "number of qsets to collapse: ~a" (set-count to-collapse)))
  (define result
    (make-hash qset-map)) ; mutable copy of qset-map
  (define (qset-symbol q) ; creats a symbol for a qset
    (string->unreadable-symbol (~v (equal-hash-code q))))
  (define (collapse q)
    (if (set-member? to-collapse q)
      (qset/kw
        #:threshold 1
        #:validators (seteqv (qset-symbol q))
        #:inner-qsets (set))
      (let ()
        (qset/kw
          #:threshold (qset-threshold q)
          #:validators (set-union
                         (qset-validators q)
                         (for/seteqv ([q2 (set-intersect (qset-inner-qsets q) to-collapse)])
                            (qset-symbol q2)))
          #:inner-qsets (set-subtract
                          (qset-inner-qsets q)
                          to-collapse)))))
  (for ([(p q) (in-hash result)])
    (hash-set! result p (collapse q)))
  ; it remains to give the new points their qsets
  (for ([q to-collapse])
    (hash-set!
      result
      (qset-symbol q)
      ; note it's important to use result:
      (dict-ref result (car (set->list (qset-validators q))))))
  ; finally, we return an alist:
  (for/list ([(p q) (in-hash result)])
    (cons p q)))

(module+ test
  (check-not-exn (thunk (collapse-orgs `(,(cons 'p qset-6)))))
  (define qset-7
    (qset/kw #:threshold 2 #:validators (seteqv 'a) #:inner-qsets (set qset-1 qset-3 qset-4)))
  (check-equal?
    ; qset-3 should not be collapsed
    (length (collapse-orgs `(,(cons 'v qset-7))))
    3))

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
