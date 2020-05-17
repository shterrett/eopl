#lang racket

(provide flip)

(define flip
  (λ (f)
    (λ (x y) (f y x))))
