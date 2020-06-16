#lang racket

(require (lib "eopl.ss" "eopl"))
(require "store.rkt")

(provide mutpair? mk-pair left right setleft! setright!)

(define-datatype mutpair mutpair?
  (a-pair
    (left-loc reference?)
    (right-loc reference?)))

(define mk-pair
  (λ (l r)
     (a-pair (newref l) (newref r))))

(define left
  (λ (p)
    (cases mutpair p
      (a-pair (l r)
        (deref l)))))

(define right
  (λ (p)
    (cases mutpair p
      (a-pair (l r)
        (deref r)))))

(define setleft!
  (λ (p l)
    (cases mutpair p
      (a-pair (old-l r)
        (setref! old-l l)))))

(define setright!
  (λ (p r)
    (cases mutpair p
      (a-pair (l old-r)
        (setref! old-r r)))))

(module+ test
  (require rackunit)
  (initialize-store!)
  (check-equal? (left (mk-pair 3 5))
                3
                "mut-pair stores left")
  (check-equal? (right (mk-pair 3 5))
                5
                "mut-pair stores right")
  (check-equal? (let ((p (mk-pair 3 5)))
                  (setleft! p 7)
                  (left p))
                7
                "mut-pair sets left")
  (check-equal? (let ((p (mk-pair 3 5)))
                  (setleft! p 7)
                  (right p))
                5
                "mut-pair preserves right when setting left")
  (check-equal? (let ((p (mk-pair 3 5)))
                  (setright! p 9)
                  (right p))
                9
                "mut-pair sets right")
  (check-equal? (let ((p (mk-pair 3 5)))
                  (setleft! p 7)
                  (right p))
                  5
                  "mut-pair preserves left when setting right")
  )
