#lang rosette/safe

(require
  "tvl-verification.rkt"
  "truth-tables.rkt"
  syntax/parse/define
  (for-syntax
    "qset2.rkt"
    "stellarbeat.rkt"
    racket/syntax
    #;racket/pretty))

(provide
  check-intertwined
  check-intertwined/stellarbeat)

(define-for-syntax (check-intertwined/datum data points-to-check)
  ; TODO: it seems that Rosette or Racket can't handle large syntax objects
  (define qset-map
    (flatten-qsets data))
  (println (format "there are ~v points" (length (dict-keys qset-map))))
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
    ; NOTE: the following only works if there are no inner quorumsets (it's okay since, above, we have flattened the qsets)
    (define (closedAx p polarity)
      (define q (dict-ref qset-map p))
      (define n (set-count (qset-validators q)))
      (define k (qset-threshold q))
      (define bs (combinations (set->list (qset-validators q)) (+ (- n k) 1))) ; blocking sets
      (define (blocking-fmla b polarity)
        (for/fold
          ([acc #''t])
          ([p b])
          #`(∧ #,(polarity (dict-ref symbols-map p)) #,acc)))
      (define (blocked polarity)
        (for/fold
          ([acc #''f])
          ([b bs])
          #`(∨ #,(blocking-fmla b polarity) #,acc)))
      #`(⇒ #,(blocked polarity) #,(polarity (dict-ref symbols-map p))))
    (with-syntax*
      ([equivs
         (for/fold
           ([acc #''t])
           ([pair (combinations points-to-check 2)])
           #`(∧ (≡ #,(dict-ref symbols-map (first pair)) #,(dict-ref symbols-map (second pair))) #,acc))]
       [ax
         (for/fold
           ([acc #''t])
           ([p points])
           #`(∧ (∧ #,(closedAx p identity) #,acc) (∧ #,(closedAx p negate) #,acc)))]
       [fmla
         #'(⇒ ax equivs)])
      ; uncomment to print the axioms
      (println "done building fmla")
      (println (syntax->datum #'fmla)) ; even that is not returning with stellarbeat data
      #'(begin
          #;(define name wst)
          (let ()
            (define (fmla-fn p ...) fmla)
            (verify-valid/tvl (fmla-fn p ...)))))))

(define-syntax (check-intertwined stx)
  (syntax-parse stx
    [(_ qsets:expr)
     ; NOTE we need a separate module to pass to eval-syntax
     (define data (eval-syntax #'qsets (module->namespace "qset2.rkt")))
     (check-intertwined/datum data (dict-keys data))]))

(define-syntax (check-intertwined/stellarbeat stx)
  (syntax-parse stx
    [(_)
     (define network (get-stellar-top-tier))
     (check-intertwined/datum (reduce-orgs network) (dict-keys network))]))
