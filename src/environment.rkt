#lang racket

(provide empty-env environment?
         push-scope pop-scope
         add-binding add-binding-recursive
         retrieve-binding)

(require "maybe.rkt" "pair.rkt" "lists.rkt" "alist.rkt")

(define environment?
  (λ (env)
    (if (null? env)
        true
        (list? (car env)))))

(define empty-env (list new-alist))

(define push-scope
  (λ (env) (cons new-alist env)))

(define pop-scope tail)

(define add-binding
  (λ (k v env)
    (cons (add-alist (head env) k v)
          (tail env))))

(define add-binding-recursive
  (λ (k fv env)
     (let* ((binding (pair k k))
            (al (cons binding (head env)))
            (new-env (cons al (tail env))))
       (set-mcdr! binding (fv new-env))
       new-env)))

(define retrieve-binding
  (λ (k env)
    (if (null? env)
        nothing
        (let ([val (find-alist (head env) k)])
          (if (is-just val)
              val
              (retrieve-binding k (tail env)))))))

(module+ test
  (require rackunit)
  (define env (add-binding 'x 5 empty-env))
  (check-equal? (retrieve-binding 'x env)
                (just 5)
                "lookup binding")
  (check-equal? (retrieve-binding 'x (add-binding 'y 6 (push-scope env)))
                (just 5)
                "lookup binding in higher scope")
  (check-equal? (retrieve-binding 'x (add-binding 'x 6 (push-scope env)))
                (just 6)
                "latest binding wins")
  (check-equal? (retrieve-binding 'x (pop-scope (add-binding 'x 6 (push-scope env))))
                (just 5)
                "push then pop is no-op")
  (check-equal? (environment? empty-env)
                #t
                "empty environment is an environment")
  (check-equal? (environment? (add-binding 'x 5 empty-env))
                #t
                "populated environment is an environment")
  (let ((e (add-binding-recursive 'f
                                 (λ(e) (cons 'e e))
                                 (add-binding 'x 6 empty-env))))
    (check-equal? (retrieve-binding 'f e)
                (just (cons 'e e))))
  )
