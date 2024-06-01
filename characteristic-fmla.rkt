#lang racket
; #lang errortrace racket

; Functions to generate the formula that characterizes the intertwinedness of a qset configuration.

(require
  "qset.rkt"
  (only-in sugar ->string))

(provide
  characteristic-fmla)

(define (characteristic-fmla fbas [points-to-check (dict-keys fbas)])
  ; fbas maps points to sets of slices
  (define points (dict-keys fbas))
  (define symbols-map
    ; associate a symbol to each point
    (for/hash ([p points])
      ; we create symbols with $ at the beginning to avoid any clash with 3vl value ('t, 'b, and 'f).
      (values p (string->symbol (string-append "$" (->string p))))))
  (define (negate p)
    `(¬ ,p))
  (define (cax p1 polarity)
    (define blocked
      `(∧*
         ,@(for/list ([slice (dict-ref fbas p1)])
             `(∨*
                ,@(for/list ([p2 slice])
                    (polarity (dict-ref symbols-map p2)))))))
    `(⇒ ,blocked ,(polarity (dict-ref symbols-map p1))))
  (define closedAx
    `(∧*
       ,@(for*/list ([p points] [polarity (list identity negate)])
           (cax p polarity))))
  `(⇒ ,closedAx (≡* ,@(for/list ([p points-to-check]) (dict-ref symbols-map p)))))

;; generate a formula corresponding to extremal valuations (see the book)
;; the drawback is that it produces a much bigger formula
;; TODO factor out common stuff
(define (extremal-characteristic-fmla fbas [points-to-check (dict-keys fbas)])
  ; fbas maps points to sets of slices
  (define points (dict-keys fbas))
  (define symbols-map
    ; associate a symbol to each point
    (for/hash ([p points])
      ; we create symbols with $ at the beginning to avoid any clash with 3vl value ('t, 'b, and 'f).
      (values p (string->symbol (string-append "$" (->string p))))))
  (define (negate p)
    `(¬ ,p))
  (define (cax p1 polarity)
    (define blocked
      `(∧*
         ,@(for/list ([slice (dict-ref fbas p1)])
             `(∨*
                ,@(for/list ([p2 slice])
                    (polarity (dict-ref symbols-map p2)))))))
    `(⇒ ,blocked ,(polarity (dict-ref symbols-map p1))))
  (define closedAx
    `(∧*
       ,@(for*/list ([p points] [polarity (list identity negate)])
           (cax p polarity))))
  (define (cax-ex p1 polarity)
    (define rhs
      `(∧*
         ,@(for/list ([slice (dict-ref fbas p1)])
             `(∨*
                ,@(for/list ([p2 slice])
                    `(□ ,(polarity (dict-ref symbols-map p2))))))))
    `(⇒ ,(polarity (dict-ref symbols-map p1)) ,rhs))
  (define closedAx-ex
    `(∧*
       ,@(for*/list ([p points] [polarity (list identity negate)])
           (cax-ex p polarity))))
  `(⇒ (∧ ,closedAx ,closedAx-ex) (≡* ,@(for/list ([p points-to-check]) (dict-ref symbols-map p)))))

;; takes a qset fbas instead of a slices fbas
(define (qset-characteristic-fmla fbas)
  (define points-to-check (dict-keys fbas))
  ; first flatten the fbas
  (define flat-fbas
    (flatten-qsets (collapse-qsets fbas)))
  (define symbols-map
    (for/hash ([p (dict-keys flat-fbas)])
      ; we create symbols with $ at the beginning to avoid any clash with 3vl value ('t, 'b, and 'f).
      (values p (string->symbol (string-append "$" (->string p))))))
  (define (negate p)
    `(¬ ,p))
  (define (closedAx q ps polarity)
    (unless (set-empty? (qset-inner-qsets q))
      (raise (error "the qset must have an empty set of inner qsets")))
    (define n (set-count (qset-validators q)))
    (define k (qset-threshold q))
    (define bs (combinations (set->list (qset-validators q)) (+ (- n k) 1))) ; blocking sets
    (define (blocked-by b)
      `(∧* ,@(for/list ([p b]) (polarity (dict-ref symbols-map p)))))
    (define blocked
      `(∨* ,@(for/list ([b bs]) (blocked-by b))))
    `(⇒ ,blocked (∧* ,@(for/list ([p ps]) (polarity (dict-ref symbols-map p))))))
  (define ax
    `(∧*
       ,@(for*/list
           ([(q ps) (in-dict (invert-qset-map flat-fbas))]
            [polarity (list identity negate)])
           (closedAx q ps polarity))))
  (define fmla
    ; NOTE we only need to check equivalence of the original points, not the points introduced during flattening/collapsing
    `(⇒ ,ax (≡* ,@(for/list ([p points-to-check]) (dict-ref symbols-map p)))))
  fmla)

(module+ test
  (require
    rackunit
    racket/pretty
    (only-in "qset.rkt" quorums->slices-fbas)
    (only-in "rosette-sat.rkt" valid/3? SAT?)
    (only-in rosette sat? unsat?))

  (define qset-fbas-1
    `((p . ,(qset 1 (seteqv 'q) (set)))
      (q . ,(qset 1 (seteqv 'q) (set)))))
  (define qset-fbas-1-char-fmla
    (qset-characteristic-fmla
      qset-fbas-1))

  (check-equal?
    qset-fbas-1-char-fmla
    '(⇒
       (∧*
         (⇒
           (∨* (∧* $q))
           (∧* $q $p))
         (⇒
           (∨* (∧* (¬ $q)))
           (∧* (¬ $q) (¬ $p))))
       (≡* $p $q)))

  (check-true
    (unsat? (valid/3? qset-fbas-1-char-fmla)))

  ; now let's try fbass specified by sets of quorums

  (define (solve-fbas n)
    (valid/3? (characteristic-fmla n)))
  (define slices-fbas-1
    (quorums->slices-fbas (set (set 'p 'q))))
  (check-true
    (unsat? (solve-fbas slices-fbas-1)))

  ; examples from the book
  (define bn-1 ; Figure 2.1
    (quorums->slices-fbas (set (set 0 1) (set 1 2))))
  (check-true (unsat? (solve-fbas bn-1)))

  ; Figure 3.1
  (define bn-2
    (quorums->slices-fbas (set (set 0 1 2) (set 0) (set 2))))
  (check-true (sat? (solve-fbas bn-2)))
  (define bn-3
    (quorums->slices-fbas (set (set 0 1) (set 1 2) (set 0) (set 2))))
  (check-true (sat? (solve-fbas bn-3)))
  (define bn-4
    (quorums->slices-fbas (set (set 0 1 2 3 4) (set 0 1) (set 3 4) (set 1) (set 3))))
  (check-true (sat? (solve-fbas bn-4)))
  (define bn-5
    (quorums->slices-fbas (set (set 0) (set 1) (set 2) (set 0 1 '*) (set 1 2 '*))))
  (check-true (sat? (solve-fbas bn-5)))
  (define bn-6 ; extra test not in Figure 3.1
    (quorums->slices-fbas (set  (set 1)  (set 0 1 '*) (set 1 2 '*))))
  (check-true (unsat? (solve-fbas bn-6)))

  ; Figure 3.2
  (define bn-7
    (quorums->slices-fbas (set  (set 0 1) (set 1 2) (set 2 0))))
  (check-true (unsat? (solve-fbas bn-7)))
  (define bn-8
    (quorums->slices-fbas (set  (set 1) (set 0 1) (set 1 2))))
  (check-true (unsat? (solve-fbas bn-8)))

  ; Figure 4.1
  (define bn-9
    (quorums->slices-fbas (set (set 0 1 3) (set 0 2 4) (set 1 2))))
  (check-true (unsat? (solve-fbas bn-9)))
  (define bn-10
    (quorums->slices-fbas (set (set 0 1 2 3) (set 0 1 2 4) (set 1) (set 2))))
  (check-true (sat? (solve-fbas bn-10)))

  ; Figure 5.2
  (define bn-11
    (quorums->slices-fbas (set (set 0 1) (set 1 2) (set 2 3) (set 3 0))))
  (check-true (sat? (solve-fbas bn-11)))

  ; Figure 5.3
  (define bn-12
    (quorums->slices-fbas (set (set 0) (set 0 1))))
  (check-true (unsat? (solve-fbas bn-12)))

  ; Figure 6.1
  (define bn-13
    (quorums->slices-fbas (set (set 0) (set 0 1) (set 0 1 2 4) (set 1 2 3 4) (set 3 4) (set 4))))
  (check-true (sat? (solve-fbas bn-13)))

  ; Figure 6.1
  (define bn-14
    (quorums->slices-fbas (set (set 1) (set 2) (set '* 2))))
  (check-true (sat? (solve-fbas bn-14)))
  (define bn-15
    (quorums->slices-fbas (set (set 1) (set 2) (set '* 2) (set 3))))
  (check-true (sat? (solve-fbas bn-15)))

  ; Figure 9.1
  (define bn-16
    (quorums->slices-fbas (set (set 0 1) (set 1 2) (set 2 3) (set 3 0))))
  (check-true (sat? (solve-fbas (dict-set bn-16 '* (set)))))

  ; Figure 10.1
  (define bn-17
    (quorums->slices-fbas (set (set 0 1 3) (set 3) (set 0 2 4) (set 4) (set 1 2) (set -1 1 2))))
  (check-true (sat? (solve-fbas bn-17)))
  (define bn-18
    (quorums->slices-fbas (set (set 0 1 3)  (set 0 2 4) (set 4) (set 1 2) (set -1 1 2))))
  (check-true (sat? (solve-fbas bn-18)))

  ; Figure 10.2
  (define bn-19
    (quorums->slices-fbas (set (set 0 1) (set 1 2) (set 2 0) (set 2))))
  (check-true (sat? (solve-fbas bn-19)))
  (define bn-20
    (quorums->slices-fbas (set (set 0 1) (set 1 2) (set 2 3))))
  (check-true (sat? (solve-fbas bn-20))))
