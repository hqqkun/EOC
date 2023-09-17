#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; * helper functions for implement passes
(define fresh-var-gen
  (lambda (num)
    (lambda (var)
      (let ([cur-num num])
        (set! num (+ 1 num))
        (string->symbol
          (string-append
            (symbol->string var)
            "."
            (number->string cur-num))))))
)

;! uniquify pass
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-var (fresh-var-gen 1))

; uniquify-exp : env * exp -> exp
(define uniquify-exp
  (lambda (env exp)
    (match exp
      [(Var x)  (Var (dict-ref env x))]
      [(Int n) exp]
      [(Prim op es)
        (Prim op (for/list ([e es]) (uniquify-exp env e)))]
      [(Let x exp body)
        (let* 
          ( [new-exp (uniquify-exp env exp)]
            [new-x (fresh-var x)])
          (Let new-x new-exp (uniquify-exp (dict-set env x new-x) body)))]
      ))
)

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info (uniquify-exp '() e))]))

;! uniquify pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;! remove-complex-opera* pass 
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

(define tmp-fresh-var (fresh-var-gen 1))

; rco-atom : exp -> 
(define rco-atom
  (lambda (exp)
    (match exp
      [(Int n) (values exp '())]
      [(Var var) (values exp '())]
      [else
        (let
          ( [atom-exp (rco-exp exp)]
            [new-var (tmp-fresh-var 'tmp)])
          (values (Var new-var) (cons new-var atom-exp)))]))
)

; rco-exp : exp -> anf_exp
(define rco-exp
  (lambda (exp)
    (match exp
      [(Int n) exp]
      [(Var var) exp]
      [(Prim op es)
        (define-values (new-atoms new-binds)
          (for/lists (new-atoms new-binds) ([e es]) (rco-atom e)))
        (let loop ([binds new-binds])
          (cond
            [(null? binds) (Prim op new-atoms)]
            [(null? (car binds)) (loop (cdr binds))]
            [else 
              (let
                ( [alist (car binds)])
                (Let (car alist) (cdr alist) (loop (cdr binds))))]))]
      [(Let x exp body)
        (Let x (rco-exp exp) (rco-exp body))]
      ))
)

;! remove-complex-opera* pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;! explicate-control pass 
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info body)
      (let ( [new-body (explicate-tail body)])
        (CProgram info (list (cons 'start new-body))))])
)

; explicate-tail :  anf_exp -> Cvar_tail
(define explicate-tail
  (lambda (exp)
    (match exp
      [(Var x) (Return exp)]
      [(Int n) (Return exp)]
      [(Prim op es) (Return exp)] 
      [(Let x exp body)
        (let ( [tail-body (explicate-tail body)])
          (explicate-assign x exp tail-body))]
      [else (error "explicate-tail unhandled case" exp)]))
)

; explicate-assign : var * anf_exp * Cvar_tail -> Cvar_tail
(define (explicate-assign x exp cont)
  (match exp
    [(Int n) (Seq (Assign (Var x) exp) cont)]
    [(Var var) (Seq (Assign (Var x) exp) cont)]
    [(Prim op es) (Seq (Assign (Var x) exp) cont)]
    [(Let y rhs body)
      (let ( [new-cont (explicate-assign x body cont)])
        (explicate-assign y rhs new-cont))]
    [else (error "explicate-assign unhandled case" exp)]
    )
)

;! explicate-control pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

(define pro '(program () (let ([y (let ([x 20])
(+ x (let ([x 22]) x)))])
y)))

(define cpro (explicate-control (remove-complex-opera* (uniquify (parse-program pro)))))
(display cpro)