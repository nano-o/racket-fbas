#lang rosette/safe

(require
  (only-in "qset2.rkt" qset)
  "tvl-verification.rkt"
  "truth-tables.rkt"
  syntax/parse/define
  (for-syntax
    "qset2.rkt"
    racket/syntax
    racket/pretty))

(define-syntax (check-intertwined stx)
  (syntax-parse stx
    [(_ name:id qsets:expr)
     ; NOTE we need a separate module to pass to eval-syntax
     (define qset-map
       (flatten-qsets (eval-syntax #'qsets (module->namespace "qset2.rkt"))))
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
       ; TODO: the following only works if there are no inner quorumsets (it's okay since, above, we have flattened the qsets)
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
              ([pair (combinations points 2)])
              #`(∧ (≡ #,(dict-ref symbols-map (first pair)) #,(dict-ref symbols-map (second pair))) #,acc))]
          [ax
            (for/fold
              ([acc #''t])
              ([p points])
              #`(∧ (∧ #,(closedAx p identity) #,acc) (∧ #,(closedAx p negate) #,acc)))]
          [fmla
            #'(⇒ ax equivs)])
         ; uncomment to print the axioms
         ; (pretty-print (syntax->datum #'ax))
         #'(begin
             #;(define name wst)
             (let ()
               (define (fmla-fn p ...) fmla)
               (verify-valid/tvl (fmla-fn p ...))))))]))

(module+ test
  (require rackunit)
  (check-true
    (sat? (check-intertwined semitopo-1
      `((p . ,(qset 1 (seteqv 'p) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined semitopo-2
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined semitopo-3
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'p) (set)))))))
  (check-true
    (sat? (check-intertwined semitopo-4
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'r) (set)))))))
  (check-true
    (sat? (check-intertwined semitopo-5 ; here we have a confused point
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (a . ,(qset 1 (seteqv 'b) (set)))
        (b . ,(qset 1 (seteqv 'b) (set)))
        (x . ,(qset 2 (seteqv 'p 'a) (set)))))))
  (check-false
    (sat? (check-intertwined semitopo-6
      `((p . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined semitopo-7
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 1 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 1 (seteqv 1 2 3) (set)))))))
  (check-false
    (sat? (check-intertwined semitopo-8
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined semitopo-9
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set))))))))

; TODO: pull data from stellarbeat
