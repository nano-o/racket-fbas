#lang racket

(require
  json
  net/url
  "qset.rkt"
  racket/trace)

(provide
  ; get-stellar-top-tier
  (contract-out
    [get-fbas-from-file (-> string? stellar-fbas/c)]
    [get-stellar-fbas (-> stellar-fbas/c)]))

(define/contract (fbas-info url-string)
  (-> string? hash?)
  (define url (string->url url-string))
  (define resp (get-pure-port url #:redirections 5))
  (read-json resp))

(define (get-fbas-from-file f)
  ; f must contain an array of nodes
  (define f-contents
    (with-input-from-file f read-json))
  (define nodes
    (if (hash? f-contents)
      (hash-ref f-contents 'nodes)
      f-contents))
  (define fbas
    (hash->conf (quorum-sets nodes)))
  (unless (set-empty? (nodes-without-qset fbas))
    (println (format "some nodes do not have a qset assigned: ~v" (nodes-without-qset fbas))))
  (add-missing-qsets fbas))

(define (quorum-sets nodes)
  (for/hash
    ([n nodes]
     #:when (and
              (hash-has-key? n 'publicKey)
              (hash-has-key? n 'quorumSet)
              (not (equal? (hash-ref n 'quorumSet) 'null))))
    (values (hash-ref n 'publicKey) (hash-ref n 'quorumSet))))

(define stellarbeat-url-string
  "https://api.stellarbeat.io/v1")

(define (get-stellar-fbas)
  (define info
    (fbas-info stellarbeat-url-string))
  (define fbas
    (hash->conf (quorum-sets (hash-ref info 'nodes))))
  (unless (set-empty? (nodes-without-qset fbas))
    (println (format "some nodes do not have a qset assigned: ~v" (nodes-without-qset fbas))))
  (add-missing-qsets fbas))

(define (hash->qset h)
  (qset/kw
    #:threshold (hash-ref h 'threshold)
    #:validators (list->seteqv (map string->symbol (hash-ref h 'validators)))
    #:inner-qsets (for/set ([q (hash-ref h 'innerQuorumSets)])
              (hash->qset q))))

(define (hash->conf h)
  ; we return an association list
  (for/list ([(n q) (in-hash h)])
    (cons (string->symbol n) (hash->qset q))))

(module+ test
  (require rackunit)
  (check-not-exn get-stellar-fbas))
