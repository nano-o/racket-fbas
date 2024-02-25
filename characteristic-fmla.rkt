#lang rosette

; Functions to generate the formula that characterizes the intertwinedness of a qset configuration.

(require
  "tvl-verification.rkt"
  "truth-tables.rkt"
  syntax/parse/define
  "qset.rkt"
  racket/syntax
  syntax/datum
  racket/pretty)

(provide
  characteristic-fmla
  verify-characteristic-fmla/stx)

; creates a datum representing the formula
(define (characteristic-fmla network)
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
    `(⇒ ,blocked (∧* ,@(for/list ([p ps]) (polarity (dict-ref symbols-map p))))))
  (define ax
    `(∧*
       ,@(for/list
           ([(q ps) (in-dict (invert-qset-map flattened-network))]
            #:when
            (not ; skip trivial qsets
              (and
                (equal? (qset-validators q) (seteqv (car ps)))
                (equal? (length ps) 1)))
            [polarity (list identity negate)])
           (closedAx q ps polarity))))
  (define fmla
    `(⇒ ,ax (≡* ,@(for/list ([p points-to-check]) (dict-ref symbols-map p)))))
  `(,(dict-keys flattened-network) . ,fmla))

; If we want to generate the fmla in a separate module then we need to pass in the map from symbol to symbolic variables. Otherwise we cannot create symbolic variables with the right lexical context.
; should we eval this?
(define (verify-characteristic-fmla/stx network)
  ; TODO: display non-intertwined points if check fails
  (define points-to-check (dict-keys network))
  (define flattened-network
    (flatten-qsets (collapse-qsets network)))
  ; collect all points
  (define points
    (dict-keys flattened-network))
  ; now we need to create the formula
  (with-syntax
    ([fmla-fn (car (generate-temporaries '(fmla-fn)))] ; symbol for the function we define
     [(p ...) ; symbols for the tvl variables
      (generate-temporaries points)])
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
          (let ()
            (define (fmla-fn p ...) fmla)
            (verify-valid/tvl (fmla-fn p ...)))))))

(module+ test
  (require rackunit)

  (define network-1
    `((p . ,(qset 1 (seteqv 'q) (set)))
      (q . ,(qset 1 (seteqv 'q) (set)))))

  (check-equal?
    (characteristic-fmla
      network-1)
    '(⇒
       (∧*
         (⇒
           (∨* (∧* q))
           (∧* q p))
         (⇒
           (∨* (∧* (¬ q)))
           (∧* (¬ q) (¬ p))))
       (≡* p q)))

  (check-false
    (sat?
      (eval
        (verify-characteristic-fmla/stx
          network-1)))))
