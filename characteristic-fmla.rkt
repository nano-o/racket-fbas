#lang racket
; #lang errortrace racket

; Functions to generate the formula that characterizes the intertwinedness of a qset configuration.

; TODO try with the extremal val fmla (see 22.4 in the book); but, first naive try was unsound...
; TODO we need tests with interesting semitopologies; take examples from the book; for this we need to compute char fmlas using slices.

(require
  "qset.rkt"
  (only-in sugar ->string))

(provide
  characteristic-fmla
  qset-characteristic-fmla)

(define (characteristic-fmla network)
  (define points (dict-keys network))
  (define symbols-map
    (for/hash ([p points])
      ; we create symbols with $ at the beginning to avoid any clash with 3vl value ('t, 'b, and 'f).
      (values p (string->symbol (string-append "$" (->string p))))))
  (define (negate p)
    `(¬ ,p))
  (define (cax p1 polarity)
    (define blocked
      `(∧*
         ,@(for/list ([s (dict-ref network p1)])
             `(∨*
                ,@(for/list ([p2 s])
                    (polarity (dict-ref symbols-map p2)))))))
    `(⇒ ,blocked ,(polarity (dict-ref symbols-map p1))))
  (define closedAx
    `(∧*
       ,@(for*/list ([p points] [polarity (list identity negate)])
           (cax p polarity))))
  `(⇒ ,closedAx (≡* ,@(dict-values symbols-map))))

; TODO provide a set of points to check are intertwined; this might not be all points e.g. if some are deemed faulty
(define (qset-characteristic-fmla network)
  (define points-to-check (dict-keys network))
  ; first flatten the network
  (define flat-network
    (flatten-qsets (collapse-qsets network)))
  (define symbols-map
    (for/hash ([p (dict-keys flat-network)])
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
           ([(q ps) (in-dict (invert-qset-map flat-network))]
            [polarity (list identity negate)])
           (closedAx q ps polarity))))
  (define fmla
    ; NOTE we only need to check equivalence of the original points, not the points introduced during flattening/collapsing
    `(⇒ ,ax (≡* ,@(for/list ([p points-to-check]) (dict-ref symbols-map p)))))
  fmla)

(module+ test
  (require rackunit)

  (define network-1
    `((p . ,(qset 1 (seteqv 'q) (set)))
      (q . ,(qset 1 (seteqv 'q) (set)))))

  (check-equal?
    (qset-characteristic-fmla
      network-1)
    '(⇒
       (∧*
         (⇒
           (∨* (∧* $q))
           (∧* $q $p))
         (⇒
           (∨* (∧* (¬ $q)))
           (∧* (¬ $q) (¬ $p))))
       (≡* $p $q))))
