#lang errortrace rosette ; TODO: do we need this here?

(require
  "tvl-verification.rkt"
  "truth-tables.rkt"
  syntax/parse/define
  "qset.rkt"
  "stellarbeat.rkt"
  (for-syntax
    racket
    "qset.rkt"
    "stellarbeat.rkt"
    racket/syntax
    racket/pretty))

(provide
  check-intertwined
  check-intertwined/stellarbeat
  intertwined-characteristic-formula)

; TODO Bottleneck seems to be symbolic execution. So this leaves us Yoni's method.

; TODO might be easier just to produce a datum and then use datum->syntax

(define (intertwined-characteristic-formula network)
  (define points-to-check (dict-keys network))
  (define flattened-network
    (flatten-qsets (collapse-qsets network)))
  (define original-points
    (dict-keys flattened-network))
  (define symbols-map
    (for/hash ([p original-points])
      (if (symbol? p)
        (values p p)
        (values p (string->symbol (~v p))))))
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
    `(=> ,blocked (∧* ,@(for/list ([p ps]) (polarity (dict-ref symbols-map p))))))
  (define ax
    `(∧* ,@(for/list ([(q ps) (in-dict (invert-qset-map flattened-network))]
                          #:when (not ; skip trivial qsets
                                   (and
                                     (equal? (qset-validators q) (seteqv (car ps)))
                                     (equal? (length ps) 1)))
                          [polarity (list identity negate)])
                     (closedAx q ps polarity))))
  `(=> ,ax (≡* ,@(for/list ([p points-to-check]) (dict-ref symbols-map p)))))

(define-for-syntax (check-intertwined/datum network)
  ; TODO: display non-intertwined points if check fails
  (define points-to-check (dict-keys network))
  (define flattened-network
    (flatten-qsets (collapse-qsets network)))
  ; collect all points
  (define points
    (dict-keys flattened-network))
  ; now we need to create the formula
  (with-syntax
    ([fmla-fn (format-id #'name "~a-intertwined?" #'name)] ; symbol for the function we define
     [(p ...) ; symbols for the tvl variables
      (for/list ([p points])
        (format-id #'() "~a" p))])
    (define symbols-map
      (for/list ([p/datum points]
                 [p/syntax (syntax->list #'(p ...))])
        (cons p/datum p/syntax)))
    (define (negate p)
      (with-syntax ([p p])
        #'(¬ p)))
    ; NOTE: The following assumes the network is flat (no inner quorumsets)
    (define (closedAx q ps apply-polarity) ; all points in ps must have qset q
      (unless (set-empty? (qset-inner-qsets q))
        (raise (error "the qset must have an empty set of inner qsets")))
      (define n (set-count (qset-validators q)))
      (define k (qset-threshold q))
      (define bs (combinations (set->list (qset-validators q)) (+ (- n k) 1))) ; blocking sets
      (define (blocked-by b)
        (with-syntax
          ([(lit ...) (for/list ([p b]) (apply-polarity (dict-ref symbols-map p)))])
          #'(∧* lit ...)))
      (define blocked
        (with-syntax
          ([(bby ...) (for/list ([b bs]) (blocked-by b))])
          #'(∨* bby ...)))
      (define conj-blocked-points
        (with-syntax
          ([(lit ...) (for/list ([p ps]) (apply-polarity (dict-ref symbols-map p)))])
          #'(∧* lit ...)))
      #`(⇒ #,blocked #,conj-blocked-points))
    (with-syntax*
      ([(pt ...) (for/list ([p points-to-check])
                   (dict-ref symbols-map p))]
       [equivs
         ; NOTE: we _cannot_ use a cycle of ⊃ (it's unsound in tvl!)
         #'(≡* pt ...)]
       [(closedAx ...)
        (for*/list
          ([(q ps) (in-dict (invert-qset-map flattened-network))]
                   #:when (not ; skip trivial qsets
                            (and
                              (equal? (qset-validators q) (seteqv (car ps)))
                              (equal? (length ps) 1)))
           [polarity (list identity negate)])
          (closedAx q ps polarity))]
       [ax #'(∧* closedAx ...)]
       [fmla
         #'(⇒ ax equivs)])
      ; uncomment to print the final formula
      ; (println "done building fmla")
      ; (pretty-print (syntax->datum #'fmla))
      #'(begin
          #;(define name wst)
          (let ()
            (define (fmla-fn p ...) fmla)
            (verify-valid/tvl (fmla-fn p ...)))))))

(define-syntax (check-intertwined stx)
  (syntax-parse stx
    [(_ qsets:expr)
     ; NOTE we need a separate module to pass to eval-syntax
     #;(println "data:")
     (define data (eval-syntax #'qsets (module->namespace "qset.rkt")))
     #;(pretty-print data)
     (check-intertwined/datum data)]))

(define-syntax (check-intertwined/stellarbeat stx)
  (syntax-parse stx
    [(_)
     #;(define network (get-network-from-file "/home/nano/Documents/python-fbas/almost_symmetric_network_13_orgs.json"))
     (define network (get-network-from-file "test.json"))
     #;(define network (get-stellar-network))
     #;(define network (get-stellar-top-tier))
     (check-intertwined/datum network)]))
