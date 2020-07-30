#lang racket

(require (lib "eopl.ss" "eopl"))
(require predicates)
(require "../state/environment.rkt")
(require "../maybe.rkt")
(require "../functions.rkt")
(require "../state/store.rkt")
(require "../lists.rkt")
(require "./scheduler.rkt")

(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (var-exp
   (var symbol?))
  (let-exp
   (var symbol?)
   (exp1 expression?)
   (body expression?))
  (proc-exp
    (vars list-of-symbols?)
    (body expression?))
  (procc-exp
    (var symbol?)
    (body expression?))
  (letrec-exp
    (name symbol?)
    (vars list-of-symbols?)
    (fn-body expression?)
    (let-body expression?))
  (call-exp
    (f expression?)
    (x list-of-expressions?))
  (callc-exp
    (f expression?)
    (x expression?))
  (assign-exp
    (var symbol?)
    (val expression?))
  (begin-exp
    (es list-of-expressions?))
  (spawn-exp
    (thd expression?))
  )

(define list-of-symbols?
  (λ (ls)
     (and  (list? ls)
           ((all? symbol?) ls))))

(define list-of-expressions?
  (λ (ls)
     (and (list? ls)
          ((all? expression?) ls))))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
    (proc proc?))
  (ref-val
    (ref reference?)))

(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (saved-env environment?)))

(define curry-proc-exp
  (λ (vars body)
     (foldr procc-exp body vars)))

(define curry-call-exp
  (λ (f xs)
     (foldl (flip callc-exp) f xs)
     ))

(define apply-procedure
  (λ (f val sch k)
    (cases proc f
           (procedure (var body saved-env)
                      (value-of body (add-binding var val saved-env) sch k)))))

(define lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (boolean) const-exp)
    (expression ("zero?(" expression ")") zero?-exp)
    (expression ("-(" expression "," expression ")") diff-exp)
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    (expression (identifier) var-exp)
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)
    (expression
     ("proc" "(" (arbno identifier) ")" expression)
     proc-exp)
    (expression
      ("letrec" identifier "(" (arbno identifier) ")" "=" expression "in" expression)
      letrec-exp)
    (expression
     ("(" expression (arbno expression) ")")
     call-exp)
    (expression ("set" identifier "=" expression ";")
     assign-exp)
    (expression ("begin" "(" (arbno expression) ")")
     begin-exp)
    (expression ("spawn" "(" expression ")" )
     spawn-exp)
    ))

(define scan&parse
  (sllgen:make-string-parser lexical-spec grammar))

(define expval->num
  (λ (val)
    (cases expval val
           (num-val (num) num)
           (else (report-expval-extractor-error 'num val)))))

(define expval->bool
  (λ (val)
    (cases expval val
           (bool-val (bool) bool)
           (else (report-expval-extractor-error 'bool val)))))

(define expval->proc
  (λ (val)
     (cases expval val
            (proc-val (f) f)
            (else (report-expval-extractor-error 'proc val)))))

(define expval->ref
  (λ (val)
     (cases expval val
            (ref-val (r) r)
            (else (report-expval-extractor-error 'ref val)))))

(define report-expval-extractor-error
  (λ (type val)
    (raise-argument-error "expval extraction" type val)))

(define report-env-lookup-error
  (λ (var)
    (error "Undefined variable " var)))

(define init-env
  (λ ()
       empty-env))

(define run
  (λ (s)
    (value-of-program (scan&parse s))))

(define value-of-program
  (λ (pgm)
    (initialize-store!)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 (init-env) (initialize-scheduler! 5) end-cont)))))

(define value-of
  (lambda (exp env sch k)
    (cases expression exp
           (const-exp (num) (k (num-val num)))
           (var-exp (var)
                    (k (retrieve-binding var env)))
           (diff-exp (exp1 exp2)
                     (value-of exp1 env sch (diff-arg-cont exp2 env sch k)))
           (zero?-exp (exp1)
                      (value-of exp1 env sch (zero-cont sch k)))
           (if-exp (exp1 exp2 exp3)
                   (value-of exp1 env sch (if-cont exp2 exp3 env sch k)))
           (let-exp (var exp1 body)
              (value-of exp1 env sch (let-cont var body env sch k)))
           (proc-exp (vars body)
                     (value-of (curry-proc-exp vars body) env sch k))
           (procc-exp (var body)
                      (k (proc-val (procedure var body env))))
           (letrec-exp (name vars fn-body let-body)
                       (let ((pv (λ(new-env)
                                   (let ((p (curry-proc-exp vars fn-body)))
                                     (cases expression p
                                            (procc-exp (var body)
                                               (proc-val (procedure var body
                                                                    new-env)))
                                            (else (error "curried procedure not
                                                         a procedure")))))))
                        (value-of let-body
                                  (add-binding-recursive name pv env)
                                  sch
                                  k)
                       ))
           (callc-exp (f x)
                      (value-of f env sch (callc-op-cont x env sch k)))
           (call-exp (f xs)
                     (value-of (curry-call-exp f xs) env sch k))
           (assign-exp (var val)
                     (value-of val env sch (assign-cont var env sch k)))
           (begin-exp (es)
                      (value-of (head es) env sch (begin-cont env (tail es) sch k)))
           (spawn-exp (thr) ;; thr should be a procedure of one ignored argument
                      (value-of thr env sch (spawn-cont sch k)))
            )))

(define end-cont
  (λ (v)
     (eopl:printf "End of computation.~%")
     v))

(define zero-cont
  (λ (sch k) (build-cont sch (λ (v)
    (k (bool-val (zero? (expval->num v))))))))

(define let-cont
  (λ (var body env sch k) (build-cont sch (λ (v)
    (value-of body (add-binding var v (push-scope env)) sch k)))))

(define if-cont
  (λ (t-exp f-exp env sch k) (build-cont sch (λ (v)
    (if (expval->bool v)
        (value-of t-exp env sch k)
        (value-of f-exp env sch k))))))

(define diff-arg-cont
  (λ (exp2 env sch k) (build-cont sch (λ (val1)
    (value-of exp2 env sch (diff-exp-cont val1 sch k))))))

(define diff-exp-cont
  (λ (val1 sch k) (build-cont sch (λ (val2)
    (let ((num1 (expval->num val1))
          (num2 (expval->num val2)))
      (k (num-val (- num1 num2))))))))

(define callc-op-cont
  (λ (arg env sch k) (build-cont sch (λ (f)
    (let ((fn (expval->proc f)))
      (value-of arg env sch (callc-arg-cont fn env sch k)))))))

(define callc-arg-cont
  (λ (fn env sch k) (build-cont sch (λ (arg)
    (apply-procedure fn arg sch k)))))

(define assign-cont
  (λ (var env sch k) (build-cont sch (λ (val)
    (begin
      (setref!  (retrieve-reference var env) val)
      (k (num-val 27)) ;; return value not important, so we pick a random one
      )))))

(define begin-cont
  (λ (env es sch k) (build-cont sch (λ (v)
    (if (null? es)
        v
        (value-of (begin-exp es) env sch k))))))

(define spawn-cont
  (λ (sch k) (build-cont sch (λ (v)
    (let ((thread-body (expval->proc v)))
      (place-on-ready-queue! sch
        (λ ()
           (apply-procedure thread-body (num-val 28) sch (end-subthread-cont sch)))))
    (k (num-val 73))))))

(define end-subthread-cont
  (λ (sch) (build-cont sch (λ (_)
    (run-next-thread sch)))))

(define end-main-thread-cont
  (λ (sch) (build-cont sch (λ (v)
    (set-final-answer! sch v)
     (run-next-thread sch)))))

(define build-cont
  (λ (sch f) (λ (v)
    (if (time-expired? sch)
      (begin
        (place-on-ready-queue! sch (λ () (f v)))
        (run-next-thread sch))
      (begin
        (decrement-timer! sch)
        (f v))))))

(module+ test
  (require rackunit)
  (check-equal? (run "5")
                (num-val 5)
                "constant number")
  (check-equal? (run "zero?(0)")
                (bool-val #t)
                "zero is zero")
  (check-equal? (run "zero?(1)")
                (bool-val #f)
                "one is not zero")
  (check-equal? (run "if zero?(0) then 3 else 4")
                (num-val 3)
                "true if")
  (check-equal? (run "if zero?(1) then 3 else 4")
                (num-val 4)
                "false if")
  (check-equal? (run "-(5, 3)")
                (num-val 2)
                "difference")
  (check-equal? (run "let x = 5 in x")
                (num-val 5)
                "constant let")
  (check-equal? (run "let x = 0 in if zero?(x) then x else 1")
                (num-val 0)
                "if in let")
  (check-equal? (run "let x = 0 in let x = 1 in x")
                (num-val 1)
                "nested let with shadowing")
  (check-equal? (run "let x = 1 in let y = 3 in if zero?(-(y, x)) then 10 else 20")
                (num-val 20)
                "nested let, if, and zero")
  (check-equal? (run "let f = proc (x) -(x, 5) in (f 7)")
                (num-val 2)
                "apply procedure 7 - 5")
  (check-equal? (run "let f = proc (x) if zero?(-(x, 5)) then x else 4 in (f 5)")
                (num-val 5)
                "apply procedure with nested if")
  (check-equal? (run "let f = proc (x) proc(y) -(x, y) in ((f 5) 3)")
                (num-val 2)
                "curried function")
  (check-equal? (run "let add = proc (x y) -(0, -( -(0, x), y)) in ((add 3) 4)")
                (num-val 7)
                "automatically curried function")
  (check-equal? (run "let add = proc (x y) -(0, -( -(0, x), y)) in (add 3 4)")
                (num-val 7)
                "automatically curried function application")
  (check-equal? (run "letrec tozero (x) = if zero?(x) then x else (tozero -(x, 1)) in (tozero 4)")
                  (num-val 0)
                  "recursion!")
  (check-equal? (run "letrec diff (x y) = if zero?(y) then x else (diff -(x, 1) -(y, 1)) in ((diff 5) 4)")
                (num-val 1)
                "curried recursion")
  (check-equal? (run "letrec diff (x y) = if zero?(y) then x else (diff -(x, 1) -(y, 1)) in (diff 5 4)")
                (num-val 1)
                "uncurried recursion")
  (check-equal? (run
                  "let x = 5 in
                    let y = 7 in
                      begin ( set x = 12;
                              set y = 10;
                              -(x, y)
                            )")
                (num-val 2)
                "set implicit refs")
  (check-equal? (run
                  "let x = 1
                    in letrec twoIfZero (dummy) =
                        if zero?(x) then (set x = 2;) else (twoIfZero 10)
                      in letrec whenTwo (dummy) =
                            if zero?(-(x, 2)) then 2 else (whenTwo dummy)
                        in begin ( spawn (twoIfZero)
                                    set x = 0;
                                    (whenTwo 10)
                                 )")
                (num-val 2)
                "spawning threads")
  )
