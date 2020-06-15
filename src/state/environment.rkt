#lang racket

(provide empty-env environment?
         push-scope pop-scope
         add-binding add-binding-recursive
         retrieve-binding
         retrieve-binding-ref)

(require
  "../maybe.rkt"
  "../pair.rkt"
  "../lists.rkt"
  "../alist.rkt"
  "store.rkt")

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
    (cons (add-alist (head env) k (newref v))
          (tail env))))

(define add-binding-recursive
  (λ (k fv env)
     (let* ((binding (pair k (newref k)))
            (al (cons binding (head env)))
            (new-env (cons al (tail env))))
       (setref! (snd binding) (fv new-env))
       new-env)))

(define retrieve-binding
  (λ (k env) (deref (retrieve-binding-ref k env))))

(define retrieve-binding-ref
  (λ (k env)
    (if (null? env)
      (report-env-lookup-error k)
      (let ([val (find-alist (head env) k)])
          (if (is-just val)
            (cdr val)
            (retrieve-binding-ref k (tail env)))))))

(define report-env-lookup-error
  (λ (var)
    (error "Undefined variable " var)))

(module+ test
  (require rackunit)
  (define env (add-binding 'x 5 empty-env))
  (check-equal? (retrieve-binding 'x env)
                5
                "lookup binding")
  (check-equal? (retrieve-binding 'x (add-binding 'y 6 (push-scope env)))
                5
                "lookup binding in higher scope")
  (check-equal? (retrieve-binding 'x (add-binding 'x 6 (push-scope env)))
                6
                "latest binding wins")
  (check-equal? (retrieve-binding 'x (pop-scope (add-binding 'x 6 (push-scope env))))
                5
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
                (cons 'e e)))
  )
