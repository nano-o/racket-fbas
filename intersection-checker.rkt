#lang rosette/safe

(require
  "tvl-verification.rkt"
  "truth-tables.rkt"
  syntax/parse/define
  (for-syntax
    "qset2.rkt"
    "stellarbeat.rkt"
    racket/syntax
    racket/pretty))

(provide
  check-intertwined
  check-intertwined/stellarbeat)

(define-for-syntax (check-intertwined/datum data points-to-check)
  ; TODO: it seems that Rosette or Racket can't handle large syntax objects
  (define qset-map
    (flatten-qsets data))
  #;(println (format "there are ~v points" (length (dict-keys qset-map))))
  #;(println (format "there are ~v points to check are intertwined" (length points-to-check)))
  ; collect all points
  (define points
    (dict-keys qset-map))
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
    ; NOTE: The following only works if there are no inner quorumsets (it's okay since, above, we have flattened the qsets)
    (define (closedAx2 q ps polarity) ; all points must have qset q
      (define n (set-count (qset-validators q)))
      (define k (qset-threshold q))
      (define bs (combinations (set->list (qset-validators q)) (+ (- n k) 1))) ; blocking sets
      (define (blocking-fmla b polarity)
        (for/fold
          ([acc #''t])
          ([p b])
          #`(∧ #,acc #,(polarity (dict-ref symbols-map p)))))
      (define (blocked polarity)
        (for/fold
          ([acc #''f])
          ([b bs])
          #`(∨ #,acc #,(blocking-fmla b polarity))))
      (define conj-blocked-points
        (for/fold
          ([acc #''t])
          ([p ps])
          #`(∧ #,acc #,(polarity (dict-ref symbols-map p)))))
      #`(⇒ #,(blocked polarity) #,conj-blocked-points))
    #;(define (closedAx p polarity)
      (define q (dict-ref qset-map p))
      (define n (set-count (qset-validators q)))
      (define k (qset-threshold q))
      (define bs (combinations (set->list (qset-validators q)) (+ (- n k) 1))) ; blocking sets
      (define (blocking-fmla b polarity)
        (for/fold
          ([acc #''t])
          ([p b])
          #`(∧  #,acc #,(polarity (dict-ref symbols-map p)))))
      (define (blocked polarity)
        (for/fold
          ([acc #''f])
          ([b bs])
          #`(∨ #,acc #,(blocking-fmla b polarity))))
      #`(⇒ #,(blocked polarity) #,(polarity (dict-ref symbols-map p))))
    (with-syntax*
      ([equivs
         (for/fold
           ([acc #''t])
           ([pair (combinations points-to-check 2)])
           #`(∧  #,acc (≡ #,(dict-ref symbols-map (first pair)) #,(dict-ref symbols-map (second pair)))))]
       [ax
         (for/fold
           ([acc #''t])
           ([(q ps) (in-dict (invert-qset-map qset-map))]
            #:when (not
                     (and
                       (equal? (qset-validators q) (seteqv (car ps)))
                       (equal? (length ps) 1))))
           #;(pretty-print qset-map)
           #;(pretty-print (invert-qset-map qset-map))
           #`(∧  #,acc (∧ #,(closedAx2 q ps identity) #,(closedAx2 q ps negate))))]
       #;[ax
         (for/fold
           ([acc #''t])
           ([p points])
           #`(∧ (∧ #,(closedAx p identity) #,acc) (∧ #,(closedAx p negate) #,acc)))]
       [fmla
         #'(⇒ ax equivs)])
      ; uncomment to print the axioms
      #;(println "done building fmla")
      #;(pretty-print (syntax->datum #'fmla))
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
     (define data (eval-syntax #'qsets (module->namespace "qset2.rkt")))
     #;(pretty-print data)
     (check-intertwined/datum data (dict-keys data))]))

(define-syntax (check-intertwined/stellarbeat stx)
  (syntax-parse stx
    [(_)
     (define network (get-stellar-top-tier))
     (check-intertwined/datum (reduce-orgs network) (dict-keys network))]))
