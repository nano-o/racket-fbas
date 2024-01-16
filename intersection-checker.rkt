#lang racket

(require
  "tvl-verification.rkt"
  "truth-tables.rkt"
  syntax/parse/define
  (for-syntax
    racket
    "qset2.rkt"
    "stellarbeat.rkt"
    racket/syntax
    racket/pretty))

(provide
  check-intertwined
  check-intertwined/stellarbeat)

(define-for-syntax (check-intertwined/datum data)
  ; TODO: display non-intertwined points if check fails
  (define points-to-check (dict-keys data))
  (define qset-map
    (flatten-qsets (collapse-qsets data)))
  ; (println (format "there are ~v points" (length (dict-keys qset-map))))
  ; (println (format "there are ~v points to check are intertwined" (length points-to-check)))
  ; (pretty-print data)
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
        #`(and/tvl* ; TODO ellipsis
            #,@(for/fold
                 ([acc #'('t)])
                 ([p b])
                 #`(#,@acc #,(polarity (dict-ref symbols-map p))))))
      (define (blocked polarity)
        #`(or/tvl* ; TODO ellipsis
            #,@(for/fold
                 ([acc #'('f)])
                 ([b bs])
                 #`(#,@acc #,(blocking-fmla b polarity)))))
      (define conj-blocked-points
        #`(and/tvl* ; TODO ellipsis
           #,@(for/fold
                ([acc #'('t)])
                ([p ps])
                #`(#,@acc #,(polarity (dict-ref symbols-map p))))))
      #`(⇒ #,(blocked polarity) #,conj-blocked-points))
    (with-syntax*
      ([(pt ...) (for/list ([p points-to-check])
                   (dict-ref symbols-map p))]
       [equivs
         ; NOTE: we _cannot_ use a cycle of ⊃ (unsound!)
         #'(material-equiv/tvl* pt ...)]
       [ax ; TODO ellipsis
         #`(and/tvl*
             #,@(for/fold
                  ([acc #'('t)])
                  ([(q ps) (in-dict (invert-qset-map qset-map))]
                   #:when (not
                            (and
                              (equal? (qset-validators q) (seteqv (car ps)))
                              (equal? (length ps) 1))))
                  ; (pretty-print ps)
                  #`(#,@acc #,(closedAx2 q ps identity) #,(closedAx2 q ps negate))))]
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
     (define data (eval-syntax #'qsets (module->namespace "qset2.rkt")))
     #;(pretty-print data)
     (check-intertwined/datum data)]))

(define-syntax (check-intertwined/stellarbeat stx)
  (syntax-parse stx
    [(_)
     (define network (get-stellar-network))
     ; (define network (get-stellar-top-tier))
     (check-intertwined/datum network)
     #;(check-intertwined/datum network (dict-keys network))]))
