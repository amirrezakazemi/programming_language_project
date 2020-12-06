
#lang racket
(require (lib "eopl.ss" "eopl"))

; import library for parsing and lexing
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc)

;lexer implementation to identify tokens 
(define simple-math-lexer
           (lexer
            [digits (token-NUM (string->number lexeme))]
            [(:or (:seq (:? digits) "." digits)
                (:seq digits "."))
                (token-NUM (string->number lexeme))]
            [(:or "func") (token-func)]
            [(:or "+") (token-plus)]
            [(:or "-") (token-minus)]
            [(:or "*") (token-mul)]
            [(:or "/") (token-div)]
            [(:or ">") (token-grt)]
            [(:or "=") (token-eq)]
            [(:or "<") (token-les)]
            [(:or "!=") (token-neq)]
            [(:or "==") (token-eqq)]
            [(:or "false") (token-false)]
            [(:or "true") (token-true)]
            [(:or "return") (token-return)]
            [(:or "null") (token-null)]
            [(:or "do") (token-do)]
            [(:or "while") (token-while)]
            [(:or "end") (token-end)]
            [(:or "if") (token-if)]
            [(:or "else") (token-else)]
            [(:or "then") (token-then)]
            [(:or "endif") (token-endif)]
            [(:or "(") (token-left-par)]
            [(:or ")") (token-right-par)]
            [(:or "[") (token-left-brac)]
            [(:or "]") (token-right-brac)]
            [(:or "{") (token-left-curly)]
            [(:or "}") (token-right-curly)]
            [(:or ";") (token-semicol)]
            [(:or ",") (token-separ)]
            [(repetition 1 +inf.0 (union (char-range #\a #\z) (char-range #\A #\Z))) (token-variable lexeme)]
            [(:: "\"" my-any-string "\"") (token-string lexeme)]
            (whitespace (simple-math-lexer input-port))
            ((eof) (token-EOF))))

; define tokens used in the grammar
(define-tokens a (NUM))
(define-tokens b (string))
(define-tokens c (variable))
(define-empty-tokens g (EOF plus minus mul div grt eq les neq eqq true false null return while do end if endif then else left-par right-par
    left-brac right-brac semicol separ func left-curly right-curly)
)

; define abbreviation used in lexing process 
(define-lex-abbrevs
  (digits (:+ (char-set "0123456789")))
  (letter (:+ (union (char-range #\a #\z) (char-range #\A #\Z))))
  (alphabet (:+ alphabetic))
  (my-any-string (:* (char-complement "\"")))
)


;parser implementation for building a parser-tree
(define simple-math-parser
           (parser
            (start command)
            (end EOF)
            (error void)
            (tokens a b c g)
            (grammar
              (command ((unitcom) (a-program (single-command $1))) ((command semicol unitcom) (a-program (multi-command $1 $3))))
              (unitcom ((whilecom) $1) ((ifcom) $1)  ((assign) $1) ((ret) (return $1)))
              (whilecom ((while exp do command end) (while-com $2 $4)))
              (ifcom ((if exp then command else command endif) (if-com $2 $4 $6)))
              (assign ((variable eq exp) (assign-exp-com $1 $3)) ((variable eq function) (assign-func-com $1 $3)) ((variable eq call) (assign-call-com $1 $3)))
              (ret ((return exp) $2)) 
              (exp ((aexp) (aexpression $1)) ((aexp grt aexp) (grt $1 $3)) ((aexp les aexp) (les $1 $3)) ((aexp eqq aexp) (eqq $1 $3))
                  ((aexp neq aexp) (neq $1 $3))
              )
              (aexp ((bexp) (bexpression $1)) ((bexp minus aexp) (minus $1 $3)) ((bexp plus aexp) (plus $1 $3)))
              (bexp ((cexp) (cexpression $1)) ((cexp mul bexp) (mul $1 $3)) ((cexp div bexp) (div $1 $3)))
              (cexp ((minus cexp) (neg $2)) ((left-par exp right-par) (par $2)) ((NUM) (number $1)) ((null) (null)) ((variable) (vari $1)) ((true) (boolean #t))
                    ((false) (boolean #f)) ((string) (string $1)) ((list) (mk-list $1)) ((variable listmem) (indexing $1 $2)))
              (list ((left-brac listValues right-brac) (a-list $2)) ((left-brac right-brac) (empty-list)));list of racket doesn't infere with this list in grammar? // check outputs
              (listValues ((exp) (oneelement $1)) ((exp separ listValues) (nelement $1 $3)))
              (listmem ((left-brac exp right-brac) (oned $2)) ((left-brac exp right-brac listmem) (nd $2 $4)))
              (function ((func left-par vars right-par left-curly command right-curly) (proc-exp $3 $6)))
              (vars ((variable) (one-var $1)) ((variable separ vars) (multi-var $1 $3)))
              (call ((variable left-par args right-par) (call-exp $1 $3)))
              (args ((exp) (one-arg $1)) ((exp separ args) (multi-arg $1 $3)))
            )))




; ;; environment data type and all its related functions

(define-datatype env-type env?

  (empty-env); 1st variaant
  (extend-env [var string?] ; 2nd variant
              [val always?]
              [env env?])
  (extend-env-rec
   (pname string?)
   (b-var vars?)
   (body program?)
   (env env?))

  (extend-env-exp-thunk
    (thunk-name string?)
    (exp1 expression?)
    (env env?))
  (extend-env-func-thunk
    (thunk-name string?)
    (func1 function?)
    (env env?))
  (extend-env-call-thunk
    (thunk-name string?)
    (call1 call?)
    (env env?))
  (extend-env-library
    (pname string?)
    (rkt-proc procedure?)
    (env env?)))
  

; auxilary multi extend env
(define extend-env-auxilary
  (lambda (vars1 args1 env)
    (if (not (eq? (length vars1) (length args1))) (raise "expected different number of arguments")
        (if (eq? (length vars1) 1) (extend-env-exp-thunk (car vars1) (car args1) env) (extend-env-auxilary (cdr vars1) (cdr args1) (extend-env-exp-thunk (car vars1) (car args1) env))))))

; to make exntending multi var into environment easier, we defined 2 below functions 
(define vars->list
  (lambda (vars1)
    (cases vars vars1
      (one-var (first-var) (list first-var))
      (multi-var (first-var other-vars) (cons first-var (vars->list other-vars))))))

(define args->list
  (lambda (args1 env)
    (cases args args1
      (one-arg (exp1) (list exp1))
      (multi-arg (exp1 other-args) (cons exp1 (args->list other-args env))))))

(define args->list-temp
  (lambda (args1 env)
    (cases args args1
      (one-arg (exp1) (list (value-of-expression exp1 env)))
      (multi-arg (exp1 other-args) (cons (value-of-expression exp1 env) (args->list-temp other-args env))))))


(define apply-env
  (lambda (env search-var)
    (cases env-type env
      
      [empty-env () (raise (string-append "name " search-var " is not defined"))]
      [extend-env (var val env) (if (equal? var search-var)
                                    val
                                    (apply-env env search-var))]
      [extend-env-rec (pname b-var body env)
                      (if (equal? search-var pname) (procedure pname b-var body env) (apply-env env search-var))]

      [extend-env-exp-thunk (thunk-name exp1 env)
                        (if (equal? search-var thunk-name) (exp-thunk exp1 env) (apply-env env search-var))]
      [extend-env-func-thunk (thunk-name func1 env)
                        (if (equal? search-var thunk-name) (func-thunk func1 env) (apply-env env search-var))]
      [extend-env-call-thunk (thunk-name call1 env)
                        (if (equal? search-var thunk-name) (call-thunk call1 env) (apply-env env search-var))]
      [extend-env-library (pname rkt-proc env)
                           (if (equal? search-var pname) rkt-proc (apply-env env search-var))])))

(define init-env
  (lambda ()
    (extend-env-library "eval" my-eval
                        (extend-env-library "mergesort" my-mergesort
                                            (extend-env-library "merge" my-merge
                                                                (extend-env-library "set" my-set
                                                                                    (extend-env-library "reverseall" my-reverse-all
                                                                                                        (extend-env-library "reverse" my-reverse
                                                                                                                            (extend-env-library "makelist" my-make-list
                                                                                                                                                (extend-env-library "pow" my-pow (empty-env)))))))))))

(define my-pow
  (lambda (lst)
    (expt (car lst) (cadr lst))))


(define my-make-list
  (lambda (lst)
    (if (> (car lst) 0)
        (make-list (car lst) (cadr lst))
        (list))))

(define my-reverse
  (lambda (lst)
    (reverse (car lst))))

(define my-reverse-all
  (lambda (lst)
    (main (car lst))))

(define main
  (lambda (lst)
  (cond
    [(empty? lst) empty]
    [(not (cons? lst)) (list lst)]
    [else (cond
            [(cons? (car lst)) (append (main (cdr lst))  (list (main (car lst))))]
            [else (append (main (cdr lst))  (main (car lst)))])])))

(define my-set
  (lambda (lst)
    (let ([a (car lst)] [index (cadr lst)] [value (caddr lst)])
      (if (or (> index (length a)) (< index 0)) (raise "array out of bound") (list-set a index value)))))

(define my-merge
  (lambda (lst)
    (merge (car lst) (cadr lst))))
(define (merge L M)
	(if (null? L) M
		(if (null? M) L
			(if (< (car L) (car M))
				(cons (car L) (merge (cdr L) M))
				(cons (car M) (merge (cdr M) L))))))

;; split helper functions
(define (odd L)
	(if (null? L) '()
		(if (null? (cdr L)) (list (car L))
			(cons (car L) (odd (cddr L))))))
(define (even L)
	(if (null? L) '()
		(if (null? (cdr L)) '()
			(cons (cadr L) (even (cddr L))))))

;; Exp. (split '(a b c d e f g h i)) ==> ((a c e g i)(b d f h))
(define (split L)
	(cons (odd L) (cons (even L) `())))

;; Exp. (mergesort '(8 1 3 9 6 5 7 2 4 10)) ==> (1 2 3 4 5 6 7 8 9 10)

(define my-mergesort
  (lambda (lst)
    (mergesort (car lst))))
(define (mergesort L)
	(if (null? L) L
		(if (null? (cdr L)) L
			(merge
				(mergesort (car (split L)))
				(mergesort (cadr (split L)))))))


(define my-eval
  (lambda (lst)
    (let ([inp (car lst)])
      (let ([the-inp (substring inp 1 (- (string-length inp) 1))])
    (let ([my-lexer (lex-this simple-math-lexer (open-input-string the-inp))])
      
      (value-of-program (let((parser-res (simple-math-parser my-lexer))) parser-res) (init-env)))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

;;;;to make all data types , we followed what is written in grammar specificly.


; program datatype
(define-datatype program program?
  (a-program
   (exp1 command?)))
;;;;;;;

; command datatype
(define-datatype command command?
  (multi-command
   (exp1 program?)
   (exp2 unitcom?))
  (single-command
   (exp1 unitcom?))
)
;;;;;;;;;;;

;unitcom datatype 
(define-datatype unitcom unitcom?
  (if-com
   (cond expression?)
   (body program?)
   (else-body program?))
  (while-com
    (cond expression?)
    (body program?))
  (assign-exp-com
   (var string?)
   (exp1 expression?))
  (assign-func-com
   (var string?)
   (func1 function?))
  (assign-call-com
   (var string?)
   (call1 call?))
  (return
    (exp1 expression?)))
;;;;;;;;;;;;;;;;;;;

; expression datatype
(define-datatype expression expression?
  (aexpression
    (aexp aexp?))
  (grt
    (aexp1 aexp?)
    (aexp2 aexp?))
  (les
    (aexp1 aexp?)
    (aexp2 aexp?))
  (eqq
    (aexp1 aexp?)
    (aexp2 aexp?))
  (neq
    (aexp1 aexp?)
    (aexp2 aexp?)))
;;;;;;;;;;;;;;;;;;;;

; aexp datatype
(define-datatype aexp aexp?
  (bexpression
    (bexp bexp?))
  (plus
    (bexp bexp?)
    (aexp aexp?))
  (minus
    (bexp bexp?)
    (aexp aexp?)))
;;;;;;;;;;;;;;;;

; bexp datatype
(define-datatype bexp bexp?
  (cexpression
    (cexp cexp?))
  (mul
    (cexp cexp?)
    (bexp bexp?))
  (div
    (cexp cexp?)
    (bexp bexp?))
)
;;;;;;;;;;;;

;cexp datatype
(define-datatype cexp cexp?
  (number
    (num number?))
  (string
    (str string?))
  (null)
  (boolean
    (bool boolean?))
  (neg
    (exp1 cexp?))
  (par
    (exp1 expression?))
  (mk-list
    (l mylist?))
  (indexing
    (var string?)
    (index listmem?))
  (vari
    (var string?)))
;;;;;;;;;;;;;;;;;;

;mylist datatype
(define-datatype mylist mylist?
  (a-list
   (listvals listValues?))
  (empty-list))
;;;;;;;;;;;;;;;;

; listValues datatype
(define-datatype listValues listValues?
  (oneelement
    (exp1 expression?))
  (nelement
    (exp1 expression?)
    (values listValues?)))
;;;;;;;;;;;;;;;;;

; listmem datatype
(define-datatype listmem listmem?
  (oned 
    (exp1 expression?))
  (nd 
    (exp1 expression?)
    (exp2 listmem?)))
;;;;;;;;;;;;;;;;;;;;

; function datatype
(define-datatype function function?
  (proc-exp
   (arguments vars?)
    (body program?)))
;;;;;;;;;;;;;;;;;;;;

; vars datatype
(define-datatype vars vars?
  (one-var 
   (first-var string?))
  (multi-var
   (first-var string?)
   (other-vars vars?)))
;;;;;;;;;;;;;;;;;;;;

; call datatype
(define-datatype call call?
  (call-exp 
   (func-var string?)
   (arguments args?)))
;;;;;;;;;;;;;;;;;;;;

; args datatype
(define-datatype args args?
  (one-arg 
   (exp1 expression?))
  (multi-arg
   (exp1 expression?)
   (other-args args?)))
;;;;;;;;;;;;;;;;;;;;

; procedure datatype
(define-datatype proc proc?
  (procedure
   (pname string?)
   (bvar vars?)
   (body program?)
   (saved-env env?)))
;;;;;;;;;;;;;;;;;;;;
; a = 
; a = func(x){return x}
; b = a(2)

; thunk datatype using in lazey evaluation
(define-datatype thunk thunk?
  (exp-thunk
    (exp1 expression?)
    (env env?))
  (func-thunk
    (func1 function?)
    (env env?))
  (call-thunk
    (call1 call?)
    (env env?)))

(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (pname bvar body saved-env)
        (let ([the-env (extend-env-auxilary (vars->list bvar) (args->list val saved-env) saved-env)])           
          (value-of-program body (extend-env-rec pname bvar body the-env)))))))

;;;;;;;;;;;;;;;;;;;;

; evaluate a program
; program is a datatype wrapps command
(define value-of-program 
  (lambda (pgm env) 
    (cases program pgm 
      (a-program (exp1) 
        (value-of-command exp1 env)))))
;;;;;;;;;;;;;;;;;;

;evaluate a command
(define value-of-command
  (lambda(com env)
    (cases command com
      (single-command (exp1)
        (value-of-unitcom exp1 env))
      (multi-command (exp1 exp2)
        (let ([environment (value-of-program exp1 env)])
            (if (env? environment)
              (value-of-unitcom exp2 environment) environment)) ))))
              
;;;;;;;;;;;;;;;;

;evaluate a unitcom
(define value-of-unitcom
  (lambda(exp env)
    (cases unitcom exp
      (return (exp1)
        (value-of-expression exp1 env))
      (assign-exp-com (var exp1)
        (extend-env-exp-thunk var exp1 env))
      (if-com (exp pgm1 pgm2)
        (if (equal? (value-of-expression exp env) #t)
          (value-of-program pgm1 env)
          (value-of-program pgm2 env)))
      (while-com (exp pgm)
        (define a (equal? (value-of-expression exp env) #t))
        (if  a (value-of-unitcom (while-com exp pgm)  (value-of-program pgm env))  env))
      (assign-func-com (var func1)
        (extend-env-func-thunk var func1 env))
      (assign-call-com (var call1)
                       (cases call call1
                         (call-exp (func-var arguments)
                                   (let ([the-proc (apply-env env func-var)])
                                     (if (procedure? the-proc) (extend-env var (the-proc (args->list-temp arguments env)) env)
        (extend-env-call-thunk var call1 env)))))))))
;;;;;;;;;;;;;;;;;;;;;;

;;; value of thunk using to evaluate thunk datatype
;(define value-of-thunk
;  (lambda (th)
;    (cases thunk th
;      (exp-thunk (exp1 env)
;        (value-of-expression exp1 env))
;      (assign-exp-thunk var exp1)
;        ())))

;evaluate expression
(define value-of-expression
  (lambda(exp env)
    (cases expression exp
      (aexpression (exp1)
        (value-of-aexpression exp1 env))
      (grt (exp1 exp2)
        (let ([val1 (value-of-aexpression exp1 env)] [val2 (value-of-aexpression exp2 env)])
          (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
          (cases expval type-val1
            (num-val (num) 
              (cases expval type-val2
                (num-val (num) (if (> val1 val2) #t #f))
                (string-val (str) (raise "'>' not supported between instances of 'num' and 'str'"))
                (list-val (l) (if (equal? (andmap number? l) #t) (if (andmap (lambda (i)(> val1 i)) l) #t #f) (raise "'>' not supported between instances of 'num' and non-num 'list'")))
                (else (raise "unsupported type(s) for '>'"))))
            (string-val (str)
              (cases expval type-val2
                (num-val (num) (raise "'>' not supported between instances of 'str' and 'num'"))
                (string-val (str) (if (string>? val1 val2) #t #f))
                (list-val (l) (if (equal? (andmap string? l) #t) (if (andmap (lambda (i)(string>? val1 i)) l) #t #f) (raise "'>' not supported between instances of 'str' and non-str 'list'")))
                (else (raise "unsupported type(s) for '>'"))))
            (list-val (l)
              (cases expval type-val2
                (num-val (num) (if (equal? (andmap number? l) #t) (if (andmap (lambda (i)(> i val2)) l) #t #f) (raise "'>' not supported between instances of non-num 'list' and 'num'")))
                (string-val (str) (if (equal? (andmap string? l) #t) (if (andmap (lambda (i)(string>? i val2)) l) #t #f) (raise "'>' not supported between instances of non-str 'list' and 'str'")))
                (list-val (l) (raise " '>' not supported for instances of list"))
                (else (raise "unsupported type(s) for '>'"))))
            (else 'error)))))
      (les (exp1 exp2)
        (let ([val1 (value-of-aexpression exp1 env)] [val2 (value-of-aexpression exp2 env)])
          (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
          (cases expval type-val1
            (num-val (num) 
              (cases expval type-val2
                (num-val (num) (if (< val1 val2) #t #f))
                (string-val (str) (raise "'<' not supported between instances of 'num' and 'str'"))
                (list-val (l) (if (equal? (andmap number? l) #t) (if (andmap (lambda (i)(< val1 i)) l) #t #f) (raise "'<' not supported between instances of 'num' and non-num 'list'")))
                (else (raise "unsupported type(s) for '<'"))))
            (string-val (str)
              (cases expval type-val2
                (num-val (num) (raise "'<' not supported between instances of 'str' and 'num'"))
                (string-val (str) (if (string<? val1 val2) #t #f))
                (list-val (l) (if (equal? (andmap string? l) #t) (if (andmap (lambda (i)(string<? val1 i)) l) #t #f) (raise "'<' not supported between instances of 'str' and non-str 'list'")))
                (else (raise "unsupported type(s) for '<'"))))
            (list-val (l)
              (cases expval type-val2
                (num-val (num) (if (equal? (andmap number? l) #t) (if (andmap (lambda (i)(< i val2)) l) #t #f) (raise "'>' not supported between instances of non-num 'list' and 'num'")))
                (string-val (str) (if (equal? (andmap string? l) #t) (if (andmap (lambda (i)(string<? i val2)) l) #t #f) (raise "'>' not supported between instances of non-str 'list' and 'str'")))
                (list-val (l) (raise " '>' not supported for instances of list"))
                (else (raise "unsupported type(s) for '<'"))))
            (else 'error)))))
      (eqq (exp1 exp2)
        (let ([val1 (value-of-aexpression exp1 env)] [val2 (value-of-aexpression exp2 env)])
          (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
            (cases expval type-val1
              (num-val (num)
                (cases expval type-val2
                  (num-val (num) (if (equal? val1 val2) #t #f))
                  (list-val (l) (if (equal? (andmap number? l) #t) (if (andmap (lambda (i)(equal? val1 i)) l) #t #f) #f))
                  (else #f)))
              (string-val (str)
                (cases expval type-val2
                  (string-val (str) (if (string=? val1 val2) #t #f))
                  (list-val (l) (if (equal? (andmap string? l) #t) (if (andmap (lambda (i)(string=? val1 i)) l) #t #f) #f))
                  (else #f)))
              (list-val (l)
                (cases expval type-val2
                  (num-val (num) (if (equal? (andmap number? l) #t) (if (andmap (lambda (i)(equal? val2 i)) l) #t #f) #f))
                  (string-val (str) (if (equal? (andmap string? l) #t) (if (andmap (lambda (i)(string=? val2 i)) l) #t #f) #f))
                  (list-val (l) (if (equal? (length val1) (length val2)) (if (equal? val1 val2) #t #f) #f))
                  (bool-val (bool) (if (equal? (andmap boolean? l) #t) (if (andmap (lambda (i)(equal? val2 i)) l) #t #f) #f))
                  (null-val () (if (equal? (andmap null? l) #t) (if (andmap (lambda (i)(null? i)) l) #t #f) #f))
                  ))
              (bool-val (bool)
                (cases expval type-val2
                  (bool-val (bool) (if (equal? val1 val2) #t #f))
                  (list-val (l) (if (equal? (andmap boolean? l) #t) (if (andmap (lambda (i)(equal? val1 i)) l) #t #f) #f))
                  (else #f)))
              ;(null-val)
              (else #f)))))

      (neq (exp1 exp2)
        (let ([val1 (value-of-aexpression exp1 env)] [val2 (value-of-aexpression exp2 env)])
          (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
            (cases expval type-val1
              (num-val (num)
                (cases expval type-val2
                  (num-val (num) (if (equal? val1 val2) #f #t))
                  (list-val (l) (if (equal? (andmap number? l) #f) (if (andmap (lambda (i)(equal? val1 i)) l) #f #t) #t))
                  (else #t)))
              (string-val (str)
                (cases expval type-val2
                  (string-val (str) (if (string=? val1 val2) #f #t))
                  (list-val (l) (if (equal? (andmap string? l) #f) (if (andmap (lambda (i)(string=? val1 i)) l) #f #t) #t))
                  (else #t)))
              (list-val (l)
                (cases expval type-val2
                  (num-val (num) (if (equal? (andmap number? l) #f) (if (andmap (lambda (i)(equal? val2 i)) l) #f #t) #t))
                  (string-val (str) (if (equal? (andmap string? l) #f) (if (andmap (lambda (i)(string=? val2 i)) l) #f #t) #t))
                  (list-val (l) (if (equal? (length val1) (length val2)) (if (equal? val1 val2) #f #t) #t))
                  (bool-val (bool) (if (equal? (andmap boolean? l) #f) (if (andmap (lambda (i)(equal? val2 i)) l) #f #t) #t))
                  (null-val () (if (equal? (andmap null? l) #f) (if (andmap (lambda (i)(null? i)) l) #f #t) #t))
                  ))
              (bool-val (bool)
                (cases expval type-val2
                  (bool-val (bool) (if (equal? val1 val2) #f #t))
                  (list-val (l) (if (equal? (andmap boolean? l) #f) (if (andmap (lambda (i)(equal? val1 i)) l) #f #t) #t))
                  (else #t)))
              ;(null-val)
              (else #t))))))))
;;;;;;;;;;;;;;;;;;;;

;evaluate aexp
(define value-of-aexpression
  (lambda(exp env)
    (cases aexp exp
      (bexpression (exp1)
        (value-of-bexpression exp1 env))
      (plus (exp1 exp2)
            (let ([val1 (value-of-bexpression exp1 env)] [val2 (value-of-aexpression exp2 env)])
              (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
                (cases expval type-val1
                  (num-val (num1)
                           (cases expval type-val2
                             (num-val (num2) (+ num1 num2))
                             (list-val (l)
                                       (if (andmap number? l) (map (lambda (listnum) (+ num1 listnum)) l) (raise "unsupported operand type(s) for + : number and non-number list")))
                             (else (raise "unsupported operand type(s) for +"))))
                  (list-val (l1)
                            (cases expval type-val2
                              (num-val (num1)
                                       (if (andmap number? l1) (map (lambda (listnum) (+ num1 listnum)) l1) (raise "unsupported operand type(s) for + : non-number list and number")))
                              (list-val (l2) (append l1 l2))
                              (bool-val (bool1)
                                        (if (andmap boolean? l1) (map (lambda (listbool) (or bool1 listbool)) l1) (raise "unsupported operand type(s) for or: non-bool list and bool")))
                              (string-val (str1)
                                          (if (andmap string? l1) (map (lambda (liststr) (string-append liststr str1)) l1) (raise "unsupported operand type(s) for +: non-string list and string")))
                              (else (raise "unsupported operand type(s) for +"))))
                  (bool-val (bool1)
                            (cases expval type-val2
                              (list-val (l1)
                                        (if (andmap boolean? l1) (map (lambda (listbool) (or bool1 listbool)) l1) (raise "unsupported operand type(s) for or: bool and non-bool list")))
                              (else (raise "unsupported operand type(s) for +"))))
                  (string-val (str1)
                              (cases expval type-val2
                                (string-val (str2) (string-append (substring str1 1 (- (string-length str1) 1)) (substring str2 1 (- (string-length str2) 1))))
                                
                                (list-val (l1)
                                          (if (andmap string? l1) (map (lambda (liststr) (string-append str1 liststr)) l1) (raise "unsupported operand type(s) for +: string and non-string list")))
                                (else (raise "unsupported operand type(s) for +"))))
                  (else (raise "unsupported operand type(s) for +"))))))
        ;(+ (value-of-bexpression exp1 env) (value-of-aexpression exp2 env)))
      (minus (exp1 exp2)
             (let ([val1 (value-of-bexpression exp1 env)] [val2 (value-of-aexpression exp2 env)])
               (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
                 (cases expval type-val1
                   (num-val (num1)
                            (cases expval type-val2
                              (num-val (num2) (- num1 num2))
                              (list-val (l)
                                        (if (andmap number? l) (map (lambda (listnum) (- num1 listnum)) l) (raise "unsupported operand type(s) for - : number and non-number list")))
                              (else (raise "unsupported operand type(s) for -"))))
                   (list-val (l1)
                             (cases expval type-val2
                               (num-val (num1)
                                        (if (andmap number? l1) (map (lambda (listnum) (- listnum num1)) l1) (raise "unsupported operand type(s) for - : non-number list and number")))
                               (else (raise "unsupported operand type(s) for -"))))
                   (else (raise "unsupported operand type(s) for -")))))))))
;;;;;;;;;;;;;;;;

; evaluate bexp
(define value-of-bexpression
  (lambda(exp env)
    (cases bexp exp
      (cexpression (exp1)
        (value-of-cexpression exp1 env))
      (mul (exp1 exp2)
            (let ([val1 (value-of-cexpression exp1 env)] [val2 (value-of-bexpression exp2 env)])
              (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
                (cases expval type-val1
                  (num-val (num1)
                           (if (eq? num1 0) 0
                           (cases expval type-val2
                             (num-val (num2) (* num1 num2))
                             (list-val (l)
                                       (if (andmap number? l) (map (lambda (listnum) (* num1 listnum)) l) (raise "unsupported operand type(s) for * : number and non-number list")))
                             (else (raise "unsupported type(s) for *")))))
                  (list-val (l1)
                            (cases expval type-val2
                              (num-val (num1)
                                       (if (eq? num1 0) 0
                                       (if (andmap number? l1) (map (lambda (listnum) (* num1 listnum)) l1) (raise "unsupported operand type(s) for * : non-number list and number"))))
                              (bool-val (bool1)
                                        (if (andmap boolean? l1) (map (lambda (listbool) (and bool1 listbool)) l1) (raise "unsupported operand type(s) for and : non-bool list and bool")))            
                              (else (raise "unsupported type(s) for *"))))
                  (bool-val (bool1)
                            (if (eq? #f bool1) #f
                            (cases expval type-val2
                              (list-val (l1)
                                        (if (andmap boolean? l1) (map (lambda (listbool) (and bool1 listbool)) l1) (raise "unsupported operand type(s) for and : bool and non-bool list")))
                              (else (raise "unsupported type(s) for *")))))
                  (else (raise "unsupported type(s) for *"))))))

      (div (exp1 exp2)
            (let ([val1 (value-of-cexpression exp1 env)] [val2 (value-of-bexpression exp2 env)])
              (let ([type-val1 (type-check val1)] [type-val2 (type-check val2)])
                (cases expval type-val1
                  (num-val (num1)
                           (cases expval type-val2
                             (num-val (num2) (if (zero? num2) (raise "Division by zero") (/ num1 num2)))
                             (list-val (l)
                                       (if (andmap number? l) (if (ormap zero? l) (raise "Division by zero") (map (lambda (listnum) (/ num1 listnum)) l)) (raise "unsupported operand type(s) for / : number and non-number list")))
                             (else (raise "unsupported type(s) for /"))))
                  (list-val (l1)
                            (cases expval type-val2
                              (num-val (num1)
                                       (if (andmap number? l1) (if (zero? num1) (raise "Division by zero") (map (lambda (listnum) (/ listnum num1)) l1)) (raise "unsupported operand type(s) for / : non-number list and number")))            
                              (else (raise "unsupported type(s) for /"))))
                  (else (raise "unsupported type(s) for /")))))))))


;;;;;;;;;;;;;;;;;;;;
; a = f(x){return x}
; b = a
;evaluate cexp
(define value-of-cexpression
  (lambda(exp env)
    (cases cexp exp
      (neg (exp1)
           (let ([val1 (value-of-cexpression exp1 env)])
             (let ([type-val1 (type-check val1)])
               (cases expval type-val1
                 (num-val (num) (- num))
                 (bool-val (bool) (not bool))
                 (list-val (l)
                           (if (andmap number? l) (map - l) (if (andmap boolean? l) (map not l) (raise "unsupported type(s) for - (neg) : non-number list"))))
                 (else (raise "unsupported type(s) for - (neg)"))))))
      (number (num)
        num)
      (null () void) ; is void a good choice?
      (string (str)
        str)
      (vari (var)
        (let ([var1 (apply-env env var)])
          
          (if (thunk? var1)
            (cases thunk var1
              (exp-thunk (exp1 env)
                (value-of-expression exp1 env))
              (func-thunk (func1 env)
                (cases function func1
                  (proc-exp (arguments body)
                    (procedure var arguments body env))))
              (call-thunk (call1 env)
                (cases call call1 
                  (call-exp (func-var arguments)
                    (apply-procedure (value-of-cexpression (vari func-var) env) arguments)))))
              var1
          )))
       
      (boolean (bool)
               bool)
      (mk-list (l)
               (value-of-mylist l env))
      (indexing (var index)
                (let ([the-thunk-var (apply-env env var)])
                  (if (thunk? the-thunk-var)
                  (cases thunk the-thunk-var
                    (exp-thunk (exp1 env)
                               (let ([the-evaluated-var (value-of-expression exp1 env)])
                                 (value-of-listmem index env the-evaluated-var)))
                    (else (display ''mehrdad:/)))
                  (value-of-listmem index env the-thunk-var))))
      (else (display "")))))
;;;;;;;;;;;;;;;;;;;;;;;;;



(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (string-val
   (str string?))
  (null-val)
  (list-val
   (l list?)))

(define type-check
  (lambda (exp)
    (cond
      [(number? exp) (num-val exp)]
      [(boolean? exp) (bool-val exp)]
      [(string? exp) (string-val exp)]
      [(void? exp) (null-val)]
      [(list? exp) (list-val exp)])))

(define value-of-mylist
  (lambda (exp env)
    (cases mylist exp
      (empty-list () '())
      (a-list (listvals) (value-of-listValues listvals env)))))

(define value-of-listValues
  (lambda (exp env)
    (cases listValues exp
      (oneelement (exp1)
                  (list (value-of-expression exp1 env)))
      (nelement (exp1 values)
                (cons (value-of-expression exp1 env) (value-of-listValues values env))))))

(define value-of-listmem
  (lambda (exp env the-list)
    (if (not (list? the-list)) (raise "This object is not subscriptable") (let ([len-the-list (length the-list)]) 
    (cases listmem exp
      (oned (exp1)
            (let ([target (value-of-expression exp1 env)])
              (if (number? target) (if (> target (- len-the-list 1)) (raise "Array out of bound") (if (< target 0) (raise "Array out of bound") (list-ref the-list target))) (raise "List Indices must be integers"))))
      (nd (exp1 exp2)
          (let ([first-index (value-of-expression exp1 env)])
             (if (> first-index (- len-the-list 1)) (raise "Array out of bound") (if (< first-index 0) (raise "Array out of bound") (let ([new-list (list-ref the-list first-index)])
               (value-of-listmem exp2 env new-list)))))))))))



;(value-of  (cadr (let ((parser-res (simple-math-parser my-lexer))) parser-res)) (empty-env))
;(let ((parser-res (simple-math-parser my-lexer))) parser-res)
;(display (let((parser-res (simple-math-parser my-lexer))) parser-res))


;test


(define lex-this (lambda (lexer input) (lambda () (lexer input))))
;;;;;;;;;;;;;;;;;;;;
#|
(define inp "f = func(b) { return 8
};
a = f(2/0); b = 2 / 0; return a")
(define my-lexer (lex-this simple-math-lexer (open-input-string inp)))
;(display (let((parser-res (simple-math-parser my-lexer))) parser-res))
(value-of-program (let((parser-res (simple-math-parser my-lexer))) parser-res) (init-env))
|#



(define evaluate
  (lambda (fileinp)
  (let ([inp (apply string-append (file->lines fileinp))])
    (let ([my-lexer (lex-this simple-math-lexer (open-input-string inp))])
      (value-of-program (let((parser-res (simple-math-parser my-lexer))) parser-res) (init-env))))))

(evaluate "test.txt")

; string<?
;(if (string<? "2" "2") 1 2)
















