#lang racket

(require (lib "eopl.ss" "eopl"))
(require "../environment.rkt")
(require "../maybe.rkt")

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
    (var symbol?)
    (body expression?))
  (call-exp
    (f expression?)
    (x expression?)))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
    (proc proc?)))

(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (saved-env environment?)))

(define apply-procedure
  (λ (f val)
    (cases proc f
           (procedure (var body saved-env)
                      (value-of body (add-binding var val saved-env))))))

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
     ("proc" "(" identifier ")" expression)
     proc-exp)
    (expression
     ("(" expression expression ")")
     call-exp)))

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

(define report-expval-extractor-error
  (λ (type val)
    (raise-argument-error "expval extraction" type val)))

(define report-env-lookup-error
  (λ (var)
    (error "Undefined variable " var)))

(define init-env
  (λ ()
    (add-binding
     'i (num-val 1)
     (add-binding
      'v (num-val 5)
      (add-binding
       'x (num-val 10)
       empty-env)))))

(define run
  (λ (s)
    (value-of-program (scan&parse s))))

(define value-of-program
  (λ (pgm)
    (cases program pgm
           (a-program (exp1)
                      (value-of exp1 (init-env))))))

(define value-of
  (lambda (exp env)
    (cases expression exp
           (const-exp (num) (num-val num))
           (var-exp (var)
                    (let ((val (retrieve-binding var env)))
                      (if (is-just val)
                          (cdr val)
                          (report-env-lookup-error val))))
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
           (proc-exp (var body)
                     (proc-val (procedure var body env)))
           (call-exp (rator rand)
                     (let ((proc (expval->proc (value-of rator env)))
                           (arg (value-of rand env)))
                       (apply-procedure proc arg))))))

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
                "curried function"))

