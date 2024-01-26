#lang racket

(require
  racket/generator)

(provide
  valid?/3to2) ; given a tvl formula, generates a boolean formula that is valid if and only if the original tvl formula is valid

; The idea is that, for each sub-formula f, we create two boolean variables f- and f+ that encode the tvl truth value of the formula (i.e. 00 is 'f, 01 and 10 is 'b, and 11 is 't). Then we just apply the truth tables to express the truth value of a formula in terms of the truth value of its subformulas.

; NOTE we better use rosette's &&, ||, etc. (and not `and`, `or`, etc) to get the classical logical operations

(define (is-f p)
  `(&& (! ,(car p)) (! ,(cdr p))))
(define (is-t p)
  `(&& ,(car p) ,(cdr p)))
(define (is-b p)
  `(|| (&& (! ,(car p)) ,(cdr p)) (&& ,(car p) (! ,(cdr p)))))

(define (encode-∧* p qs) ; encodes "p is the conjunction of all the qs"
  (define one-f
    `(|| ,@(map is-f qs)))
  (define one-b
    `(|| ,@(map is-b qs)))
  `(&&
     (=> ,one-f ,(is-f p))
     (=> (&& (! ,one-f) ,one-b) ,(is-b p))
     (=> (&& (! ,one-f) (! ,one-b)) ,(is-t p))))

(define (encode-∨* p qs) ; encodes "p is the disjunction of all the qs"
  (define one-t
    `(|| ,@(map is-t qs)))
  (define one-b
    `(|| ,@(map is-b qs)))
  `(&&
     (=> ,one-t ,(is-t p))
     (=> (&& (! ,one-t) ,one-b) ,(is-b p))
     (=> (&& (! ,one-t) (! ,one-b)) ,(is-t p))))

(define (encode-≡* p qs) ; encodes "p is the equivalence of all the qs"
  (define one-t-one-f
    `(&& (|| ,@(map is-f qs)) (|| ,@(map is-t qs))))
  (define one-b
    `(|| ,@(map is-b qs)))
  `(&&
     (=> ,one-t-one-f ,(is-f p))
     (=> (&& (! ,one-t-one-f) ,one-b) ,(is-b p))
     (=> (&& (! ,one-t-one-f) (! ,one-b)) ,(is-t p))))

(define (encode-¬ p q)
  `(&&
     (=> ,(is-f q) ,(is-t p))
     (=> ,(is-b q) ,(is-b p))
     (=> ,(is-t q) ,(is-f p)))) ; encodes "p is not q"

; TODO: we should probably avoid creating boolean variables for formulas we have seen already
(define (valid?/3to2 fmla)
  (define sym-gen
    (generator ()
      (let loop ([i 0])
        (yield (string->unreadable-symbol (~a i)))
        (loop (+ 1 i)))))
  (define (3to2-rec f)
    ; first we generate symbols f+ and f-
    (define f+- `(,(sym-gen) . ,(sym-gen)))
    (define constraints
      (match f
        [`(∧* ,q ...)
          (match (map 3to2-rec q)
            [`((,c . ,q) ...)
              `(&& ,(encode-∧* f+- q) ,@c)])]
        [`(∨* ,q ...)
          (match (map 3to2-rec q)
            [`((,c . ,q) ...)
              `(&& ,(encode-∨* f+- q) ,@c)])]
        [`(≡* ,q ...)
          (match (map 3to2-rec q)
            [`((,c . ,q) ...)
              `(&& ,(encode-≡* f+- q) ,@c)])]
        [`(¬ ,q)
         (define c+- (3to2-rec q))
         (define c (car c+-))
         (define q1 (cdr c+-))
         (define new-c (encode-¬ f+- q1))
         `(&& ,new-c ,c)]
        [(? symbol?) #t]))
    `(,constraints . ,f+-))
  (match (3to2-rec fmla) ; now we assert that we have a designated value ('t or 'b)
    [`(,c . ,q) `(&& ,c (|| ,(is-t q) ,(is-b q)))]))

; (valid?/3to2 '(∧* a b))
