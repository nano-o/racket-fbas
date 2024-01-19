#lang rosette/safe

(require
  "intersection-checker.rkt"
  "qset2.rkt"
  (for-syntax "qset2.rkt"))

(module+ test
  (require rackunit)
  (check-true
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv 'p) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))))))
  (check-false
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'p) (set)))))))
  (check-true
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (r . ,(qset 1 (seteqv 'r) (set)))))))
  (check-true
    (sat? (check-intertwined ; here we have a confused point
      `((p . ,(qset 1 (seteqv 'q) (set)))
        (q . ,(qset 1 (seteqv 'q) (set)))
        (a . ,(qset 1 (seteqv 'b) (set)))
        (b . ,(qset 1 (seteqv 'b) (set)))
        (x . ,(qset 2 (seteqv 'p 'a) (set)))))))
  (check-false
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 2 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 1 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 1 (seteqv 1 2 3) (set)))))))
  (check-false
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 2 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set)))))))
  (check-true
    (sat? (check-intertwined
      `((p . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (q . ,(qset 1 (seteqv) (set (qset 1 (seteqv 1 2 3) (set)))))
        (1 . ,(qset 2 (seteqv 1 2 3) (set)))
        (2 . ,(qset 1 (seteqv 1 2 3) (set)))
        (3 . ,(qset 2 (seteqv 1 2 3) (set))))))))
