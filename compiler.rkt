#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
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
      (define-values (new-body var-set) (explicate-tail body (set)))
      (CProgram 
        (dict-set info 'locals-vars (set->list var-set)) 
        (list (cons 'start new-body)))])
)

; explicate-tail :  anf_exp -> values(Cvar_tail, var-set)
(define explicate-tail
  (lambda (exp var-set)
    (match exp
      [(Var x) (values (Return exp) var-set)]
      [(Int n) (values (Return exp) var-set)]
      [(Prim op es) (values (Return exp) var-set)] 
      [(Let x exp body)
        (define-values (tail-body new-var-set) (explicate-tail body var-set))
        (explicate-assign x exp tail-body new-var-set)]
      [else (error "explicate-tail unhandled case" exp)]))
)

; explicate-assign : var * anf_exp * Cvar_tail -> values(Cvar_tail, var-set)
(define (explicate-assign x exp cont var-set)
  (define new-var-set (set-add var-set x))
  (define seq (Seq (Assign (Var x) exp) cont))
  (match exp
    [(Int n) (values seq new-var-set)]
    [(Var var) (values seq new-var-set)]
    [(Prim op es) (values seq new-var-set)]
    [(Let y rhs body)
      (define-values (new-cont new-var-set) (explicate-assign x body cont var-set))
      (explicate-assign y rhs new-cont new-var-set)]
    [else (error "explicate-assign unhandled case" exp)])
)

;! explicate-control pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;! select-instructions pass
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info tails) 
      (let
        ( [blocks (for/list ( [tail tails])
            (cons 
              (car tail) 
              (Block '() (select-tail (cdr tail)))))]
          [conclusion
            (cons 
              'conclusion
              (Block '() (list (Retq))))])
        (X86Program info (cons conclusion blocks)))])
)

(define (atom? exp)
  (match exp
    [(Int _) #t]
    [(Var _) #t]
    [(Prim _ _) #f]
    [else (error "atom? unhandled case" exp)])
)

(define (prim? exp)
  (match exp
    [(Int _) #f]
    [(Var _) #f]
    [(Prim _ _) #t]
    [else (error "prim? unhandled case" exp)])
)


; select-tail : tail -> ListOf(Instr)
(define (select-tail tail)
  (match tail
    [(Seq stmt tail)
      (append (select-stmt stmt)
        (select-tail tail))]
    [(Return exp)
      (append
        (select-stmt (Assign (Reg 'rax) exp))
        (list (Jmp 'conclusion)))]
    [else (error "select-tail unhandled case" tail)])
)

; select-stmt : stmt -> ListOf(Instr)
(define (select-stmt stmt)
  (match stmt
    [(Assign x exp)
      (cond
        [(atom? exp) (list (Instr 'movq (list (select-atom exp) (select-atom x))))]
        [(prim? exp) (select-prim x exp)]
        [else (error "cannot handle Assign" exp)]
      )]
    [else (error "select-stmt unhandled case" stmt)])
)


; select-prim : x * prim-exp -> ListOf(Instr)
(define (select-prim x prim-exp)
  (let ( [atom-x (select-atom x)])
    (match prim-exp    
      [(Prim '- (list e1))
        (let ( [neg-instr (Instr 'negq (list atom-x))])
          (if (equal? x e1)
            neg-instr
            (list (Instr 'movq (list (select-atom e1) atom-x))
            neg-instr)))]
      [(Prim '+ (list e1 e2))
        (cond
          [(equal? e1 x) (list (Instr 'addq (list (select-atom e2) atom-x)))]
          [(equal? e2 x) (list (Instr 'addq (list (select-atom e1) atom-x)))]
          [else (list 
                  (Instr 'movq (list (select-atom e1) atom-x))
                  (Instr 'addq (list (select-atom e2) atom-x)))])]
      [(Prim 'read '())
        (list 
          (Callq 'read_int 0)
          (Instr 'movq (list (Reg 'rax) atom-x)))]
      [else (error "select-prim unhandled case" prim-exp)]))
)

; select-atom : atom -> arg
(define (select-atom atom)
  (match atom
    [(Int num) (Imm num)]
    [(Var x) atom]
    [(Reg r) atom]
    [else (error "select-atom unhandled case" exp)])
)

;! select-instructions pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;! assign-homes pass 
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info compound-blocks)
      (define local-vars (dict-ref info 'locals-vars))
      (define stack-offset 0)
      (define var-offset-map (make-hash))
      (let loop ( [local-vars local-vars])
        (if (null? local-vars)
          1
          (begin
            (set! stack-offset (+ stack-offset 8))
            (dict-set! var-offset-map (car local-vars) stack-offset)
            (loop (cdr local-vars)))))
      (if (= (modulo stack-offset 16) 0)
        0
        (set! stack-offset (+ stack-offset 8)))
      (X86Program
        (dict-set info 'stack-space stack-offset)
        (for/list [(compound-block compound-blocks)]
          (cons 
            (car compound-block) 
            (assign-homes-block (cdr compound-block) var-offset-map))))])
)


(define (assign-homes-block block var-offset-map)
  (match block
    [(Block info instrs)
      (Block info
        (for/list ( [instr instrs])
          (assign-homes-instr instr var-offset-map)))])
)

(define (assign-homes-instr instr var-offset-map)
  (match instr
    [(Instr name arg-list)
      (Instr name 
        (for/list ( [arg arg-list])
          (assign-homes-arg arg var-offset-map)))]
    [else instr]
  )
)

(define (assign-homes-arg arg var-offset-map)
  (match arg
    [(Var var) (Deref 'rbp (- (dict-ref var-offset-map var)))]
    [else arg])
)

;! assign-homes pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;! patch-instructions pass
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info compound-blocks)
      (X86Program
        info
        (for/list [(compound-block compound-blocks)]
          (cons 
            (car compound-block) 
            (patch-instructions-block (cdr compound-block)))))])
)

(define (patch-instructions-block block)
  (match block
    [(Block info instrs)
      (define instrs-list
        (for/list ([instr instrs])
          (patch-instructions-instr instr)))
      (Block info (apply append instrs-list))])
)

(define (patch-instructions-instr instr)
  (match instr
    [(Instr name (list arg0 arg1))
      (match* (arg0 arg1)
        [((Deref _ n1) (Deref _ n2))
          (list
            (Instr 'movq (list arg0 (Reg 'rax)))
            (Instr name (list (Reg 'rax) arg1)))]
        [(_ _) (list instr)])]
    [else (list instr)])
)

;! patch-instructions pass done
;!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



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
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
))




(define pro '(program () (let ([x (+ 1 (+ 2 3))])
  (let ([y (+ x x)])
    (+ x y)))
))

; (define pro-ast (parse-program pro))



; (pretty-display  (select-instructions
;   (explicate-control (remove-complex-opera* (uniquify pro-ast)))))

; (newline)

; (pretty-display  (assign-homes (select-instructions
;   (explicate-control (remove-complex-opera* (uniquify pro-ast))))))

; (newline)

; (pretty-display (patch-instructions (assign-homes (select-instructions
;   (explicate-control (remove-complex-opera* (uniquify pro-ast)))))))