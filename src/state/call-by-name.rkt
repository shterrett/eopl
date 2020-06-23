#lang racket

(require (lib "eopl.ss" "eopl"))
(require predicates)
(require "./environment.rkt")
(require "../maybe.rkt")
(require "../functions.rkt")
(require "./store.rkt")
(require "./mutpair.rkt")

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
  (newpair-exp
    (l expression?)
    (r expression?))
  (left-exp
    (p expression?))
  (right-exp
    (p expression?))
  (setleft-exp
    (p expression?)
    (l expression?))
  (setright-exp
    (p expression?)
    (r expression?))
  (set-exp
    (ref expression?)
    (val expression?))
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
    (ref reference?))
  (pair-val
    (pair mutpair?)))

(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (saved-env environment?)))

(define-datatype thunk thunk?
  (a-thunk
    (exp1 expression?)
    (env environment?)))

(define curry-proc-exp
  (λ (vars body)
     (foldr procc-exp body vars)))

(define curry-call-exp
  (λ (f xs)
     (foldl (flip callc-exp) f xs)
     ))

(define apply-procedure
  (λ (f add-arg)
    (cases proc f
           (procedure (var body saved-env)
                      (value-of body (add-arg var saved-env))))))

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
    (expression ("begin" "(" (arbno expression) ")" )
      begin-exp)
    (expression ("mk-pair" "(" expression "," expression ")")
      newpair-exp)
    (expression ("left" "(" expression ")")
      left-exp)
    (expression ("right" "(" expression ")")
      right-exp)
    (expression ("setleft!" "(" expression "," expression ")")
      setleft-exp)
    (expression ("setright!" "(" expression "," expression ")")
      setright-exp)
    (expression ("set!" "(" expression "," expression ")" )
      set-exp)
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

(define expval->pair
  (λ (val)
     (cases expval val
            (pair-val (p) p)
            (else (report-expval-extractor-error 'pair val)))))

(define report-expval-extractor-error
  (λ (type val)
    (raise-argument-error "expval extraction" type val)))

(define report-env-lookup-error
  (λ (var)
    (error "Undefined variable " var)))

(define init-env
  (λ () empty-env))

(define run
  (λ (s)
    (value-of-program (scan&parse s))))

(define value-of-program
  (λ (pgm)
    (initialize-store!)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 (init-env))))))

(define value-of
  (lambda (exp env)
    (cases expression exp
           (const-exp (num) (num-val num))
           (var-exp (var)
                     (let ((val (retrieve-binding var env)))
                       (if (expval? val)
                         val
                         (value-of-thunk val))))
           (diff-exp (exp1 exp2)
                     (let ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env)))
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val2)))
                         (num-val (- num1 num2)))))
           (zero?-exp (exp1)
                      (let ((val1 (value-of exp1 env)))
                        (let ((num1 (expval->num val1)))
                          (bool-val (zero? num1)))))
           (if-exp (exp1 exp2 exp3)
                   (let ((val1 (value-of exp1 env)))
                     (if (expval->bool val1)
                         (value-of exp2 env)
                         (value-of exp3 env))))
           (let-exp (var exp1 body)
                    (let ((val1 (value-of exp1 env)))
                          (value-of body
                                    (add-binding var val1 (push-scope env)))))
           (proc-exp (vars body)
                     (value-of (curry-proc-exp vars body) env))
           (procc-exp (var body)
                      (proc-val (procedure var body env)))
           (letrec-exp (name vars fn-body let-body)
                       (let ((pv (λ(new-env) (value-of (curry-proc-exp vars fn-body) new-env))))
                        (value-of let-body
                                  (add-binding-recursive name pv env))
                       ))
           (callc-exp (f x)
                     (let ((proc (expval->proc (value-of f env)))
                           (add-arg (value-of-operand x env)))
                       (apply-procedure proc add-arg)))
           (call-exp (f xs)
                     (value-of (curry-call-exp f xs) env))
           (assign-exp (var val)
                     (begin
                       (setref!
                         (retrieve-reference var env)
                         (value-of val env))
                         (num-val 27) ;; return value is not important, so we
                                      ;; pick a random one
                       ))
           (begin-exp (es)
                      (sequence env es))
           (newpair-exp (l r) (pair-val (mk-pair (value-of l env) (value-of r env))))
           (left-exp (p)
                     (left (expval->pair (value-of p env))))
           (right-exp (p)
                      (right (expval->pair (value-of p env))))
           (setleft-exp (p l)
                        (setleft! (expval->pair (value-of p env)) (value-of l env)))
           (setright-exp (p r)
                         (setright! (expval->pair (value-of p env)) (value-of r env)))
           (set-exp (exp1 exp2)
                      (let ((ref
                              (cases expression exp1
                                (var-exp (var) (retrieve-reference var env))
                                (else (raise-argument-error "expected reference"
                                                            "exp-ref"
                                                            exp1))))

                            (val (value-of exp2 env)))
                        (begin
                          (setref! ref val)
                          (num-val 23)))) ;; we have to return a value and
                                          ;; don't have a nil or unit
           )))

(define value-of-operand
  (λ (arg env)
     (cases expression arg
            (var-exp (var)
                (λ (var-name new-env)
                  (add-reference var-name
                                 (retrieve-reference var env)
                                 new-env)))
            (else
                (λ (var-name new-env)
                   (add-binding var-name
                                (a-thunk arg env)
                                new-env))))))

(define value-of-thunk
  (λ (t)
     (cases thunk t
            (a-thunk (exp env)
                     (value-of exp env)))))

(define sequence
  (λ (env es)
     (foldl (λ (e _) (value-of e env))
            (const-exp 0)
            es)))

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
                  "left(mk-pair(3, 5))")
                (num-val 3)
                "pair stores left")
  (check-equal? (run
                  "right(mk-pair(3, 5))")
                (num-val 5)
                "pair stores right")
  (check-equal? (run
                  "let p = mk-pair(3, 5) in
                    begin ( setleft!(p, 7)
                            left(p))")
                (num-val 7)
                "pair sets left")
  (check-equal? (run
                  "let p = mk-pair(3, 5) in
                    begin ( setright!(p, 9)
                            right(p))")
                (num-val 9)
                "pair sets right")
  (check-equal? (run
                  "let x = 5 in
                    let p = proc (x) begin ( set!(x, 13) ) in
                      begin ( (p x)
                               x
                            )")
                (num-val 13)
                "set var from inside procedure")
  (check-equal?  (run "letrec forever (x) = (forever x) in let f = proc (z) 11 in (f 0)")
                (num-val 11)
                "lazy eval does not diverge")
  (check-equal? (run
                  "let p = mk-pair (3, 5) in
                    let f = proc (x) begin ( setleft!(x, -(left(x), 1)) x ) in
                      let g = proc (y) -(left(y), left(y)) in
                        (g (f p))")
                (num-val 1)
                "call-by-name evaluates argument each time it's used")
  )
