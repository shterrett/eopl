#lang racket

(provide new-alist add-alist find-alist remove-alist)

(require "maybe.rkt" "pair.rkt" "lists.rkt")

(define new-alist '())

(define add-alist
  (λ (as k v)
    (cons (pair k v) as)
  ))

(define find-alist
  (λ (as k)
    (cond ((null? as) nothing)
          ((eq? (fst (head as)) k) (just (snd (head as))))
          (true (find-alist (tail as) k)))))

(define remove-alist
  (λ (as k)
    (cond ((null? as) '())
          ((eq? (fst (head as)) k) (tail as))
          (true (cons (head as) (remove-alist (tail as) k))))))

(module+ test
  (require rackunit)
  (define as (add-alist new-alist 'x 5))
    (check-equal? (find-alist as 'x)
                  (just 5)
                  "Get what we added")
    (check-equal? (find-alist (remove-alist as 'x) 'x)
                  nothing
                  "Getting removed returns nothing")
    (check-equal? (find-alist (add-alist as 'x 7) 'x)
                  (just 7)
                  "Most recent wins")
)
