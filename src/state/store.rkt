#lang racket

(provide empty-store
         get-store
         initialize-store!
         reference?
         newref
         deref
         setref!)

(define the-store '())

(define empty-store (λ () '()))

(define get-store
  (λ () the-store))

(define initialize-store!
  (λ ()
     (set! the-store (empty-store))))

(define reference?
  (λ (v)
     (integer? v)))

(define newref
  (λ (val)
     (let ((next-ref (length the-store)))
       (set! the-store (append the-store (list val)))
       next-ref)))

(define deref
  (λ (ref)
     (list-ref the-store ref)))

(define setref!
  (λ (ref val)
     (set! the-store
       (letrec ((setref-inner
                  (λ (store1 ref1)
                     (cond
                       ((null? store1)
                        (report-invalid-reference ref the-store))
                       ((zero? ref1)
                        (cons val (cdr store1)))
                       (else
                         (cons
                           (car store1)
                           (setref-inner
                             (cdr store1) (- ref1 1))))))))
         (setref-inner the-store ref)))))

(define report-invalid-reference
  (λ (ref store)
    (raise-argument-error "reference not found" ref store)))

(module+ test
  (require rackunit)
  (initialize-store!)
  (check-equal? (deref (newref 5))
                5
                "deref newref")
  (check-equal? (let ((x (newref 3)))
                 (deref x))
               3
               "deref named newref")
  (check-equal? (let ((x (newref 3)))
                  (setref! x 5)
                  (deref x))
                5
                "deref after set"))
