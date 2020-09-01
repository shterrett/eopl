#lang racket

(require (lib "eopl.ss" "eopl"))
(require predicates)
(require "../environment.rkt")
(require "../maybe.rkt")
(require "../functions.rkt")

(define-datatype in-program in-program?
  (a-in-program
   (exp1 in-expression?)))

;; same expression as letrec

(define-datatype in-expression in-expression?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 in-expression?)
   (exp2 in-expression?))
  (zero?-exp
   (exp1 in-expression?))
  (if-exp
   (exp1 in-expression?)
   (exp2 in-expression?)
   (exp3 in-expression?))
  (var-exp
   (var symbol?))
  (let-exp
   (var symbol?)
   (exp1 in-expression?)
   (body in-expression?))
  (proc-exp
    (vars (list-of symbol?))
    (body in-expression?))
  (procc-exp
    (var symbol?)
    (body in-expression?))
  (letrec-exp
    (name symbol?)
    (vars (list-of? symbol?))
    (fn-body in-expression?)
    (let-body in-expression?))
  (call-exp
    (f in-expression?)
    (x (list-of? in-expression?)))
  (callc-exp
    (f in-expression?)
    (x in-expression?))
  )

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
   (body out-expression?)
   (saved-env environment?)))

(define-datatype simple-expression simple-expression?
  (cps-const-exp
    (num number?))
  (cps-var-exp
    (var symbol?))
  (cps-diff-exp
    (exp1 simple-expression?)
    (exp2 simple-expression?))
  (cps-zero?-exp
    (exp simple-expression?))
  (cps-procc-exp
    (var symbol?)
    (body out-expression?))
)

(define-datatype out-expression out-expression?
  (cps-simple-exp
    (exp simple-expression?))
  (cps-let-exp
    (var symbol?)
    (binding simple-expression?)
    (body out-expression?))
  (cps-letrec-exp
    (name symbol?)
    (vars (list-of? symbol?))
    (fn-body out-expression?)
    (let-body out-expression?))
  (cps-if-exp
    (exp1 simple-expression?)
    (exp2 out-expression?)
    (exp3 out-expression?))
  (cps-callc-exp
    (f simple-expression?)
    (x simple-expression?))
  (cps-call-cont-exp
    (f simple-expression?)
    (x simple-expression?)
    (k simple-expression?))

)

(define list-of?
  (λ (pred?)
    (λ (ls)
      (and (list? ls)
           ((all? pred?) ls)))))

(define cps-transform
  (λ (exp k)
    (cases in-expression exp
      (const-exp (e) (cps-callc-exp k (cps-const-exp e)))
      (var-exp (var) (cps-callc-exp k (cps-var-exp var)))
      (diff-exp (exp1 exp2)
        (let ((k-e1 (k-var))
              (k-e2 (k-var)))
          (cps-transform exp1
            (cps-procc-exp k-e1
              (cps-transform exp2
                (cps-procc-exp k-e2
                  (cps-callc-exp k (cps-diff-exp (cps-var-exp k-e1)
                                                (cps-var-exp k-e2)))))))))
      (zero?-exp (exp)
        (let ((k-zero-arg (k-var)))
          (cps-transform exp
            (cps-procc-exp k-zero-arg
              (cps-callc-exp k (cps-zero?-exp (cps-var-exp k-zero-arg)))))))
      (if-exp (tst ifE thenE)
        (let ((k-test (k-var)))
          (cps-transform tst
            (cps-procc-exp k-test
              (cps-if-exp (cps-var-exp k-test)
                  (cps-transform ifE k)
                  (cps-transform thenE k))))))
      (let-exp (var bind body)
        (let ((k-bind (k-var)))
          (cps-transform bind
            (cps-procc-exp k-bind
              (cps-let-exp var
                          (cps-var-exp k-bind)
                          (cps-transform body k))))))
      (proc-exp (vars body)
        (cps-transform (curry-proc-exp vars body) k))
      (procc-exp (var body)
        (cps-callc-exp k
          (cps-procc-exp var
            (cps-transform body id-k))))
      (letrec-exp (name vars fn-body let-body)
        (cps-letrec-exp name
                        vars
                        (cps-transform fn-body id-k)
                        (cps-transform let-body k)))
      (call-exp (f xs)
        (cps-transform (curry-call-exp f xs) k))
      (callc-exp (f x)
        (let ((k-fn (k-var))
              (k-arg (k-var)))
          (cps-transform f
            (cps-procc-exp k-fn
              (cps-transform x
                (cps-procc-exp k-arg
                  (cps-call-cont-exp (cps-var-exp k-fn)
                                    (cps-var-exp k-arg)
                                    k)))))))
)))

(define k-var-idx 0)

(define k-var
  (λ ()
  (let ((idx k-var-idx))
    (set! k-var-idx (+ 1 idx))
    (string->symbol
      (string-append "k-var-"
                    (number->string idx))))))

(define curry-proc-exp
  (λ (vars body)
     (foldr procc-exp body vars)))

(define curry-cps-proc-exp
  (λ (vars body)
     (foldr (λ(v b) (cps-procc-exp v (if (simple-expression? b)
                                         (cps-simple-exp b)
                                         b)))
                    body
                    vars)))

(define curry-call-exp
  (λ (f xs)
     (foldl (flip callc-exp) f xs)))

(define id-k
  (cps-procc-exp 'v (cps-simple-exp (cps-var-exp 'v))))

(define run
  (λ (s)
    (value-of-program (scan&parse s))))

(define value-of-program
  (λ (pgm)
    (cases in-program pgm
      (a-in-program (in-exp)
        (value-of
          (cps-transform in-exp id-k)
          (init-env))))))

(define value-of
  (λ (exp env)
    (cases out-expression exp
      (cps-simple-exp (s)
        (value-of-simple s env))
      (cps-let-exp (var bind body)
        (let ((val (value-of-simple bind env)))
          (value-of body
            (add-binding var val (push-scope env)))))
      (cps-letrec-exp (name vars fn-body let-body)
        (let* ((pv (λ(new-env)
                    (cases simple-expression (curry-cps-proc-exp vars fn-body)
                      (cps-procc-exp (var body)
                        (proc-val (procedure var body new-env)))
                      (else (error "letrec procedure is not a procedure"))))))
        (value-of let-body (add-binding-recursive name pv env))))
      (cps-if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of-simple exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (cps-callc-exp (f x)
        (let ((proc (expval->proc (value-of-simple f env)))
              (arg (value-of-simple x env)))
          (apply-procedure proc arg)))
      (cps-call-cont-exp (f x k)
        (let ((proc (expval->proc (value-of-simple f env)))
              (arg (value-of-simple x env))
              (cont (expval->proc (value-of-simple k env))))
          (apply-procedure cont
            (apply-procedure proc arg))))
      )))

(define value-of-simple
  (λ (exp env)
    (cases simple-expression exp
      (cps-const-exp (n) (num-val n))
      (cps-var-exp (var)
        (let ((val (retrieve-binding var env)))
          (if (is-just val)
              (cdr val)
              (report-env-lookup-error var))))
      (cps-diff-exp (e1 e2)
        (let ((v1 (value-of-simple e1 env))
              (v2 (value-of-simple e2 env)))
          (let ((num1 (expval->num v1))
                (num2 (expval->num v2)))
            (num-val (- num1 num2)))))
      (cps-zero?-exp (exp1)
        (let ((val1 (value-of-simple exp1 env)))
          (let ((num1 (expval->num val1)))
            (bool-val (zero? num1)))))
      (cps-procc-exp (var body)
        (proc-val (procedure var body env)))
  )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Copied from letrec
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-procedure
  (λ (f val)
    (cases proc f
      (procedure (var body saved-env)
        (value-of body (add-binding var val saved-env))))))

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

(define lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (in-expression) a-in-program)
    (in-expression (number) const-exp)
    (in-expression (boolean) const-exp)
    (in-expression ("zero?(" in-expression ")") zero?-exp)
    (in-expression ("-(" in-expression "," in-expression ")") diff-exp)
    (in-expression
     ("if" in-expression "then" in-expression "else" in-expression)
     if-exp)
    (in-expression (identifier) var-exp)
    (in-expression
     ("let" identifier "=" in-expression "in" in-expression)
     let-exp)
    (in-expression
     ("proc" "(" (arbno identifier) ")" in-expression)
     proc-exp)
    (in-expression
      ("letrec" identifier "(" (arbno identifier) ")" "=" in-expression "in" in-expression)
      letrec-exp)
    (in-expression
     ("(" in-expression (arbno in-expression) ")")
     call-exp)))

(define scan&parse
  (sllgen:make-string-parser lexical-spec grammar))

(define init-env
  (λ () empty-env))

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
  (check-equal? (run "let id = proc (x) x in 1")
                (num-val 1)
                "apply id function")
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
  )
