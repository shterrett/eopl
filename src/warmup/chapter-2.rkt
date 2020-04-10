#lang racket

(provide head)

(define head
  (λ (xs)
    (if (null? xs)
        '()
        (car xs))))

(module+ test
  (require rackunit)

  (check-equal? (head '(1 2 3 4)) 1)
)
