#lang racket

(provide just nothing maybe is-just is-nothing)

(define just
  (λ (x) (cons 'Just x)))

(define nothing (cons 'Nothing '()))

(define maybe
  (λ (n j m)
    (if (is-just m)
        (j (cdr m))
        n)))

(define is-just
  (λ (m)
    (eq? (car m) 'Just)))

(define is-nothing
  (λ (m)
    (eq? (car m) 'Nothing)))
