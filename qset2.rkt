#lang racket
(require
  (only-in racket/hash hash-union!)
  #;racket/trace)

(provide
  (struct-out qset)
  qset/kw
  flatten-qsets
  reduce-orgs)

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
  ; this might be premature optimization...
  (define (qset-symbol q)
    (string->unreadable-symbol (~v (equal-hash-code q))))
  (define new-qset-map
    (make-hash qset-map)) ; we want it mutable
  (define (flatten q) ; NOTE: has side-effects on new-qset-map!
    (define flattened-iqs
      (for/set ([iq (in-set (qset-inner-qsets q))])
        (flatten iq)))
    (define new-points
      (for/hash ([fiq flattened-iqs])
        (values (qset-symbol fiq) fiq))) ; it's okay if it already exists in new-qset-map
    (hash-union!
      new-qset-map
      new-points
      #:combine/key (λ (k v1 v2) v1)) ; NOTE: side-effect!
    (qset/kw ; we remove the inner qsets and add corresponding points
      #:threshold (qset-threshold q)
      #:validators (set-union (qset-validators q) (apply seteqv (dict-keys new-points)))
      #:inner-qsets (set)))
  (for ([(p qset) (in-dict qset-map)])
    (hash-set! new-qset-map p (flatten qset))) ; NOTE: side-effect on new-qset-map!
  ; finally, return an alist
  (for/list ([(q qs) (in-dict new-qset-map)])
    (cons q qs)))

(module+ test
  (check-true
    (for/and ([q (dict-values (flatten-qsets `((p . ,qset-6))))])
      (set-empty? (qset-inner-qsets q)))))

; TODO: single point for orgs that have >1/2 threshold
; NOTE: for now this is just a quick hack and is incorrect in general
(define (reduce-orgs qset-map)
  (define (qset-symbol q)
    (string->unreadable-symbol (~v (equal-hash-code q))))
  (define new-qset-map
    (make-hash qset-map)) ;mutable
  (for ([(p q) (in-dict qset-map)])
    (define new-points
      (for/seteqv ([iq (in-set (qset-inner-qsets q))])
                  (qset-symbol iq)))
    (for ([p (in-set new-points)]) ; new points get a singleton qset with just themselves
      (hash-set! new-qset-map p (qset 1 (seteqv p) (set))))
    ; remove the old points? no! what would remain?
    #;(for ([iq (in-set (qset-inner-qsets q))])
      (for ([p (in-set (qset-validators iq))])
        (hash-remove! new-qset-map p)))
    ; add the new points to this qset's validators:
    (hash-set!
      new-qset-map
      p
      (qset/kw
        #:threshold (qset-threshold q)
        #:inner-qsets (set)
        #:validators (set-union
                       (qset-validators q)
                       new-points))))
  (for/list ([(p q) (in-hash new-qset-map)])
    (cons p q)))

(module+ test
  (reduce-orgs `(,(cons 'a qset-6)))
  (check-not-exn (thunk (reduce-orgs `(,(cons 'p qset-6))))))
