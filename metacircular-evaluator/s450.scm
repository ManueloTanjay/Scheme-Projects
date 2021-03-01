(#%require (only racket/base error))
;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with the following
;;; changes:
;;;
;;; 1.  It uses #f and #t, not false and true, to be Scheme-conformant.
;;;
;;; 2.  Some function names were changed to avoid conflict with the
;;; underlying Scheme:
;;;
;;;       eval => xeval
;;;       apply => xapply
;;;       extend-environment => xtend-environment
;;;
;;; 3.  The driver-loop is called s450.
;;;
;;; 4.  The booleans (#t and #f) are classified as self-evaluating.
;;;
;;; 5.  These modifications make it look more like UMB Scheme:
;;;
;;;        The define special form evaluates to (i.e., "returns") the
;;;          variable being defined.
;;;        No prefix is printed before an output value.
;;;
;;; 6.  I changed "compound-procedure" to "user-defined-procedure".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 xeval and xapply -- the kernel of the metacircular evaluator
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Question 2
;;; special form table procedures and definitions
(define (make-table)
  (list '*table*))

(define (lookup key table)
  (let ((record (assoc key (cdr table))))
    (if record
        (cdr record)
        #f)))

(define (insert! key value table)
  (let ((record (assoc key (cdr table))))
    (if record
        (display "ERROR: Special Form already exists")
        (begin (set-cdr! table
                         (cons (cons key value) (cdr table)))
               key))))

(define special-form-table (make-table))

(define (lookup-action action)
  (lookup action special-form-table))

(define (type-of expression)
  (cond ((pair? expression) (car expression))
        (#f)))

(define (install-special-form name action)
  (insert! name action special-form-table))

;;; new xeval procedure
(define (xeval exp env)
  (let ((action (lookup-action (type-of exp))))
    (if action
        (action exp env)
        (cond ((lookup-action exp) (display "Special Form: ") exp) ; check if exp is in special-form-table
              ((self-evaluating? exp) exp)
              ((variable? exp) (lookup-variable-value exp env))
              ((application? exp)
               (xapply (xeval (operator exp) env)
                       (list-of-values (operands exp) env)))
              (else
               (error "Unknown expression type -- XEVAL " exp))))))

(define (xapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((user-defined-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (xtend-environment
             (procedure-parameters procedure)
             arguments
             (procedure-environment procedure))))
        (else
         (error
          "Unknown procedure type -- XAPPLY " procedure))))

;;; Handling procedure arguments

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (xeval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

;;; These functions, called from xeval, do the work of evaluating some 
;;; of the special forms:

(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (xeval (first-exp exps) env))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (let ((name (assignment-variable exp)))
    (if (lookup-action name)
        (display "ERROR: Cannot override special form ")
        (set-variable-value! name
                             (xeval (assignment-value exp) env)
                             env))
    name))    ;; A & S return 'ok

(define (eval-definition exp env)
  (let ((name (definition-variable exp)))  
    (if (lookup-action name)
        (display "ERROR: Cannot override special form ")
        (define-variable! name
          (xeval (definition-value exp) env)
          env))
    name))     ;; A & S return 'ok

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp) 
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp) ; (proc var def)
  (if (symbol? (cadr exp))        ; (define if 5) 
      (cadr exp)                  ; cadr = (car (cdr exp))
      (caadr exp)))               ; caadr = (car (car (cdr)))
                                  ; (define (func arg) (body))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      #f                          ; no else clause -- return #f
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Truth values

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))


;;; Procedures

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing environments
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An environment is a list of frames.

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

;;; Each frame is represented as a pair of lists:
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame)) ; list of variable names in frame
(define (frame-values frame) (cdr frame)) ; list of variables values in frame

(define (add-binding-to-frame! var val frame) ; add a new name-value to frame
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

;;; Extending an environment

(define (xtend-environment vars vals base-env) ; when enviroments are extended, the new frame is added to the start of the environment
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied " vars vals)
          (error "Too few arguments supplied " vars vals))))

;;; Looking up a variable in an environment

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Setting a variable to a new value in a specified environment.
;;; Note that it is an error if the variable is not already present
;;; (i.e., previously defined) in that environment.

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET! " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Defining a (possibly new) variable.  First see if the variable
;;; already exists.  If it does, just change its value to the new
;;; value.  If it does not, define the new variable in the current
;;; frame. 

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The initial environment
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is initialization code that is executed once, when the the
;;; interpreter is invoked.
;;; The setup environment is now defined with the frame containing empty lists for var an val
(define (setup-environment)
  (let ((initial-env
         (xtend-environment '() ; changed both to null since primitive procedures are not predefined now and manually installed instead
                            '()
                            the-empty-environment)))
    initial-env))

;;; Define the primitive procedures

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

;;; Here is where we rely on the underlying Scheme implementation to
;;; know how to apply a primitive procedure.

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The main driver loop
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that (read) returns an internal representation of the next
;;; Scheme expression from the input stream.  It does NOT evaluate
;;; what is typed in -- it just parses it and returns an internal
;;; representation.  It is the job of the scheme evaluator to perform
;;; the evaluation.  In this case, our evaluator is called xeval.

(define input-prompt "s450==> ")

(define (s450)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (xeval input the-global-environment)))
      (user-print output)))
  (s450))

(define (prompt-for-input string)
  (newline) (newline) (display string))

;;; Note that we would not want to try to print a representation of the
;;; <procedure-env> below -- this would in general get us into an
;;; infinite loop.

(define (user-print object)
  (if (user-defined-procedure? object)
      (display (list 'user-defined-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the global environment and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define the-global-environment (setup-environment))

(display "... loaded the metacircular evaluator. (s450) runs it.")
(newline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	Helper functions to find index of element in list
;;;        and delete element in list at certain index
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-index
        (lambda (e lst)
                (if (null? lst)
                        -1
                        (if (eq? (car lst) e)
                                0
                                (if (eq? (find-index e (cdr lst)) -1) 
                                        -1
                                        (+ 1 (find-index e (cdr lst))))))))

(define (find-item-index item list)
  (define (loop list item i)
        (cond ((null? list) i)
              ((equal? (car list) item) i)
              (else
               (loop (cdr list) item (+ i 1)))))
  (if (not (member item list))
      -1
      (loop list item 0)))

(define (delete-at k lst)
  (cond ((null? lst)
         '())
        ((zero? k)
         (cdr lst))
        (else
         (cons (car lst)
               (delete-at (- k 1) (cdr lst))))))

;;; Question 2
;;; install-special-form and installation of special forms
;;; table and procedures that perform operations on table are defined above xeval
(install-special-form 'quote (lambda (exp env) (text-of-quotation exp)))
(install-special-form 'define (lambda (exp env) (eval-definition exp env)))
(install-special-form 'if (lambda (exp env) (eval-if exp env)))
(install-special-form 'set! (lambda (exp env) (eval-assignment exp env)))
(install-special-form 'lambda (lambda (exp env) (make-procedure (lambda-parameters exp)
                                                                (lambda-body exp)
                                                                env)))
(install-special-form 'begin (lambda (exp env) (eval-sequence (begin-actions exp) env)))

(install-special-form 'cond (lambda (exp env) (xeval (cond->if exp) env)))
(install-special-form 'load (lambda (exp env)
                              (define (filename exp) (cadr exp))
                              (define thunk (lambda ()
                                              (readfile)
                                              ))
                              (define readfile (lambda()
                                                 (let ((item (read)))
                                                   (if (not (eof-object? item))
                                                       (begin
                                                         (xeval item env)
                                                         (readfile))))
                                                 ))
                              (with-input-from-file (filename exp) thunk)
                              (filename exp)      ; return the name of the file - why not?
                              ))

;;; Question 6
;;; Install defined?, locally-defined?, make-unbound, locally-make-unbound!
(install-special-form 'defined? (lambda (exp env)
                                  (define (env-loop env) ; loop through frames in global env
                                    (define (scan vars)
                                      (cond ((null? vars)
                                             (env-loop (enclosing-environment env)))
                                            ((eq? (cadr exp) (car vars))
                                             #t)
                                            (else (scan (cdr vars) ))))
                                    (if (eq? env the-empty-environment) ; return #f if end of env is reached
                                        #f
                                        (let ((frame (first-frame env)))
                                          (scan (frame-variables frame) ; try to find the cadr exp in the current frame
                                                ))))
                                  (env-loop env))) ; loop through the  env
(install-special-form 'locally-defined? (lambda (exp env)
                                          (define (scan vars)
                                            (cond ((null? vars)
                                                   #f)
                                                  ((eq? (cadr exp) (car vars)) ; return #t if exp is found in car of frame
                                                   #t)
                                                  (else (scan (cdr vars))))) ; scan remaining elements of vars
                                          (scan (frame-variables (first-frame env)))))
(install-special-form 'locally-make-unbound! (lambda (exp env)
                                               (let ((index (find-index (cadr exp) (frame-variables (first-frame env))))) ; get index of element, -1 if not found
                                                 (if (= index -1)
                                                     #f ; variable not found, cannot unbind
                                                     (begin (set-car! (first-frame env) (delete-at index (frame-variables (first-frame env)))) ; delete element from list 
                                                            (set-cdr! (first-frame env) (delete-at index (frame-values (first-frame env)))) ; delete element from list
                                                            #t))))) ; return #t for debugging purposes
(install-special-form 'make-unbound! (lambda (exp env)
                                       (define (env-loop env) ; loop over frames in env and apply locally-make-unbound to each frame
                                         (define (scan vars)
                                           (cond ((null? vars)
                                                  (env-loop (enclosing-environment env)))
                                                 ((eq? (cadr exp) (car vars))
                                                  (let ((index (find-index (cadr exp) (frame-variables (first-frame the-global-environment)))))
                                                    (if (= index -1)
                                                        #f
                                                        (begin (set-car! (first-frame the-global-environment) (delete-at index (frame-variables (first-frame the-global-environment))))
                                                               (set-cdr! (first-frame the-global-environment) (delete-at index (frame-values (first-frame the-global-environment))))
                                                               (env-loop (enclosing-environment env))))))
                                                 (else (scan (cdr vars) ))))
                                         (if (eq? env the-empty-environment)
                                             #f
                                             (let ((frame (first-frame env)))
                                               (scan (frame-variables frame)
                                                     ))))
                                       (env-loop the-global-environment)))

;;; Question 3
;;; install-primitive-procedure and installation of primitive procedures
(define (install-primitive-procedure name action)
  (define (scan vars vals)
      (cond ((null? vars) ; if there are no variables, add variable
             (add-binding-to-frame! name (list 'primitive action) (car the-global-environment)))
            ((eq? name (car vars)) ; if variable exists, overrite associated value
             (set-car! vals action))
            (else (scan (cdr vars) (cdr vals)))))
  (if (lookup-action name)
      (display "ERROR: Is already a special form")
      (begin (scan (frame-variables (car the-global-environment)) ; scan variables in first frame
                   (frame-values (car the-global-environment))) ; scan values in first frame
             name)))

(install-primitive-procedure 'car car)
(install-primitive-procedure 'cdr cdr)
(install-primitive-procedure 'cons cons)
(install-primitive-procedure 'null? null?)
(install-primitive-procedure 'display display)
(install-primitive-procedure '* *)
(install-primitive-procedure '/ /)
(install-primitive-procedure '+ +)
(install-primitive-procedure '- -)
(install-primitive-procedure '= =)