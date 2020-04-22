#lang racket

(provide just nothing is-just is-nothing)

(define just
  (λ (x) (cons 'Just x)))

(define nothing (cons 'Nothing '()))

(define is-just
  (λ (m)
    (eq? (car m) 'Just)))

(define is-nothing
  (λ (m)
    (eq? (car m) 'Nothing)))
