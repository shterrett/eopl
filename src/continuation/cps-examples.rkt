#lang racket

(require "../functions.rkt")

(define factorial
  (λ (n)
     (fact/k n id)))

(define fact/k
  (λ (n k)
     (if (zero? n)
       (k 1)
       (fact/k (- n 1) (λ(v) (k (* v n)))))))

(define fib
  (λ (n)
     (fib/k n id)))

(define fib/k
  (λ (n k)
     (if (< n 2)
       (k 1)
       (fib/k (- n 1)
              (λ (val1)
                (fib/k (- n 2)
                       (λ (val2)
                          (k (+ val1 val2)))))))))
