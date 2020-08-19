#lang racket

(provide flip id)

(define flip
  (λ (f)
    (λ (x y) (f y x))))

(define id
  (λ(x) x))
