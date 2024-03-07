#lang racket
; #lang errortrace racket

; Functions to generate the formula that characterizes the intertwinedness of a qset configuration.

(require
  "qset.rkt")

(provide
  qset-characteristic-fmla)

; creates a datum representing the formula
(define (qset-characteristic-fmla network)
  (define points-to-check (dict-keys network))
  ; first flatten the network
  (define flat-network
    (flatten-qsets (collapse-qsets network)))
    ; (flatten-qsets network))
  (define symbols-map
    (for/hash ([p (dict-keys flat-network)])
      ; we create symbols with $ at the beginning to avoid any clash with 3vl value ('t, 'b, and 'f).
      (unless (node/c p) (error (format "cannot handle ~v" p)))
      (values p (string->symbol (format "$~a" (if (symbol? p) (symbol->string p) p))))))
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
       ,@(for/list
           ([(q ps) (in-dict (invert-qset-map flat-network))]
            #:when
            (not ; skip trivial qsets
              (and
                (equal? (qset-validators q) (seteqv (car ps)))
                (equal? (length ps) 1)))
            [polarity (list identity negate)])
           (closedAx q ps polarity))))
  (define fmla
    ; NOTE we only need to check equivalence of the original points, not the points introduced during flattening
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
