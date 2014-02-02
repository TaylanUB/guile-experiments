;;; An incomplete/broken pseudo-Scheme with "inter-phase syntactic closures".

;; Copyright (C) 2013  Taylan Ulrich Bayırlı/Kammer

;; Author: Taylan Ulrich Bayırlı/Kammer <taylanbayirli@gmail.com>
;; Keywords: extensions frp functional reactive

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; We support special form (syntax x) to output an object encapsulating the
;;; unevaluated s-expression `x' together with the lexical scope, so that macro
;;; scope spans down into execution.  This is a funny thing to do, but not very
;;; useful in practice, because in case compilation and execution happens
;;; separately, it requires all objects to have an external representation, even
;;; for instance an open file handle!  It could of course be gracefully limited
;;; to objects that can exist statically or possibly be revived at start of
;;; execution, but the utility of this, especially given the complexity and
;;; fragility of implementation, is highly dubious when most of the effect can
;;; be achieved just as well with a `let' style special form whose execution is
;;; simply repeated across compilation and execution phases.

;;; The implementation is incomplete/broken.  Top-level stuff isn't really
;;; implemented.  `set!' isn't implemented.  `quote' and some other special
;;; forms need to handle the output of `syntax'.


;;; Code:

(define-module (taylan scheme)
  #:export (mcrepl mceval mcexpand expansion-env mcexecute execution-env))

(use-modules (ice-9 match)
             (srfi srfi-9)
             (srfi srfi-9 gnu))

;;; Data types

(define-record-type <mcspecial>
  (make-mcspecial name procedure) mcspecial?
  (name      mcspecial-name)
  (procedure mcspecial-procedure))

(define-record-type <mcsyntax>
  (make-mcsyntax form) mcsyntax?
  (form mcsyntax-form))

(define-record-type <mcinjection>
  (make-mcinjection form expansion-env execution-env) mcinjection?
  (form          mcinjection-form)
  (expansion-env mcinjection-expansion-env)
  (execution-env mcinjection-execution-env))

(define-record-type <mcuninjection>
  (make-mcuninjection object) mcuninjection?
  (object mcuninjection-object))

;; (define-record-type <mcpreexpanded>
;;   (make-mcpreexpanded code) mcpreexpanded?
;;   (code mcpreexpanded-code))

(define-record-type <mcvariable>
  (make-mcvariable name) mcvariable?
  (name mcvariable-name))

(define-record-type <mcprocedure>
  (make-mcprocedure env orig-env arglist body) mcprocedure?
  (env      mcprocedure-env)
  (orig-env mcprocedure-orig-env)
  (arglist  mcprocedure-arglist)
  (body     mcprocedure-body))

(define-record-type <env>
  (make-env alist name) env?
  (alist env-alist env-set-alist!)
  (name  env-name))


(set-record-type-printer!
 <mcspecial>
 (lambda (obj port)
   (format port "/~s/" (mcspecial-name obj))))

(set-record-type-printer!
 <mcsyntax>
 (lambda (obj port)
   (format port "{s ~s}" (mcsyntax-form obj))))

(set-record-type-printer!
 <mcinjection>
 (lambda (obj port)
   (format port "{i ~s}" (mcinjection-form obj))))

(set-record-type-printer!
 <mcuninjection>
 (lambda (obj port)
   (format port "{u ~s}" (mcuninjection-object obj))))

;; (set-record-type-printer!
;;  <mcpreexpanded>
;;  (lambda (obj port)
;;    (format port "{p ~s}" (mcpreexpanded-code obj))))

(set-record-type-printer!
 <mcvariable>
 (lambda (obj port)
   (format port "~s_~36r" (mcvariable-name obj) (object-address obj))))

(set-record-type-printer!
 <mcprocedure>
 (lambda (obj port)
   (format port "\\~s.~s\\" (mcprocedure-arglist obj) (mcprocedure-body obj))))

(set-record-type-printer!
 <env>
 (lambda (obj port)
   (format port "<~s>" (env-name obj))))


;;; Environments

(define expansion-env (make-env '() 'expansion-env))

(define execution-env (make-env '() 'execution-env))

(define-syntax-rule (put! env key value)
  (env-set-alist! env (assq-set! (env-alist env) key value)))

(define (get env key)
  (assq-ref (env-alist env) key))

(define (get-handle env key)
  (assq key (env-alist env)))

(define (handle-ref handle)
  (cdr handle))

(define (handle-set! handle value)
  (set-cdr! handle value))

(define (env-append env alist)
  (make-env (append (env-alist env) alist) (env-name env)))


;;; Expansion

(define* (mcexpand form env #:optional original-env)
  (define (map-mcexpand forms)
    (map (lambda (x) (mcexpand x env original-env)) forms))
  (match form
    (((? symbol? operator) operands ...)
     (let ((binding (get env operator)))
       (if (mcspecial? binding)
           (apply-mcspecial binding operands env original-env)
           `(APPLY ,(mcexpand operator env original-env)
                   ,(map-mcexpand operands)))))
    ((operator operands ...)
     (let ((operator (mcexpand operator env original-env)))
       (if (mcspecial? operator)
           (apply-mcspecial operator operands env original-env)
           `(APPLY ,operator ,(map-mcexpand operands)))))
    ((? symbol? symbol)
     (let ((binding (get env symbol)))
       (if binding
           `(REF ,binding)
           `(REF ,symbol))))
    ((? mcsyntax? syn)
     (mcexpand (mcsyntax-form syn) env original-env))
    ((? mcinjection? inj)
     `(INJECT ,(mcexpand (mcinjection-form inj)
                         (mcinjection-expansion-env inj)
                         env)
              ,(mcinjection-execution-env inj)))
    ((? mcuninjection? uninj)
     `(UNINJECT ,(match (mcuninjection-object uninj)
                   ((and obj (or (? mcsyntax?) (? mcinjection?)))
                    (mcexpand obj original-env))
                   ((? symbol? sym)
                    (error "raw symbol in macro output:" sym))
                   (constant
                    `(CONST ,constant)))))
    ;; ((? mcpreexpanded? preexpanded)
    ;;  (mcpreexpanded-code preexpanded))
    (constant
     `(CONST ,constant))))

(define (apply-mcspecial mcspecial operands env orig-env)
  ((mcspecial-procedure mcspecial) operands env orig-env))

(define-syntax-rule
  (define-mcspecial (name . operand-pattern) env orig-env body body* ...)
  (put! expansion-env 'name (make-mcspecial
                             'name
                             (lambda (operands env orig-env)
                               (match operands
                                 (operand-pattern
                                  (let () body body* ...)))))))


(define-mcspecial (lambda arglist body) env orig-env
  ;; We have a bit of a problem here: the user could nest the parameter list in
  ;; arbitrarily deep syntax/unsyntax forms, and the same thing for every
  ;; individual parameter, and it would be very hard for us to get the
  ;; environments right.  Thus we only handle the special-case of one unsyntax
  ;; on the whole parameter list.  This lets us implement `let' style macros.
  (let repeat ((arglist arglist) (use-orig-env? #f))
    (match arglist
      ((? mcuninjection? uninj)
       (repeat (mcuninjection-object uninj) #t))
      (((? mcsyntax? syns) ...)
       (repeat (map (lambda (s) (mcsyntax-form s)) syns) #t))
      ((? list? arglist)
       (let* ((variables (map make-mcvariable arglist))
              (env-appendice (map cons arglist variables))
              (env (if use-orig-env? env (env-append env env-appendice)))
              (orig-env (if use-orig-env? (env-append orig-env env-appendice)
                            orig-env)))
         `(LAMBDA ,variables ,(mcexpand body env orig-env))))
      (form
       (error "invalid lambda arglist" form)))))


(define-mcspecial (quote form) env orig-env
  `(QUOTE ,form))

(let ((unquoter (cons 'unquote #f)))
  (put! expansion-env 'unquote unquoter)
  (define-mcspecial (quasiquote form) env orig-env
    `(QUASIQUOTE
      ,(let traverse ((form form))
         (match form
           (((? (lambda (x) (eq? unquoter (get env x)))) form)
            `(UNQUOTE ,(mcexpand form env orig-env)))
           ((form . forms)
            (cons (traverse form) (traverse forms)))
           (form
            form))))))


(define-mcspecial (let-syntax (((? symbol? names) forms) ...) body) env orig-env
  (define (make-mcmacros forms names)
    (map (lambda (x n) (make-mcmacro x env orig-env n)) forms names))
  (let ((env (env-append env (map cons names (make-mcmacros forms names)))))
    (mcexpand body env orig-env)))

(define (make-mcmacro form env orig-env name)
  (let ((macro-proc (mcexecute (mcexpand form env orig-env) execution-env)))
    (make-mcspecial name
                    (lambda (form env orig-env)
                      (mcexpand #;syntax-unwrap
                       (mcapply macro-proc
                                (list (syntax-wrap form env)))
                       env
                       orig-env)))))

(define (syntax-wrap form env)
  (let traverse ((form form))
    (match form
      ((forms ...)
       (map traverse forms))
      (atom
       (make-mcsyntax atom)))))

;; (define (syntax-unwrap obj env)
;;   (let traverse ((obj obj))
;;     (match obj
;;       ((? mcsyntax? syn)
;;        (mcexpand (mcsyntax-form syn) env))
;;       ((? mcinjection? inj)
;;        (let ((form (mcinjection-form inj))
;;              (expansion-env (mcinjection-expansion-env inj))
;;              (execution-env (mcinjection-execution-env inj)))
;;          `(INJECT
;;            ,(mcexpand (let traverse ((form form))
;;                         (match form
;;                           ((forms ...)
;;                            (map traverse forms))
;;                           ((? mcuninjection? uninj)
;;                            (let ((obj (mcuninjection-object uninj)))
;;                              (make-mcpreexpanded
;;                               `(UNINJECT
;;                                 ,(syntax-unwrap obj env)))))
;;                           (form
;;                            form)))
;;                       expansion-env)
;;            ,execution-env)))
;;       (obj
;;        `(CONST ,obj)                            #;
;;        (error "macro returned non-syntax, non-injection datum" obj)))))

(define-mcspecial (syntax form) env orig-env
  `(SYNTAX ,form ,env))

(let ((unsyntaxer (cons 'unsyntax #f)))
  (put! expansion-env 'unsyntax unsyntaxer)
  (define-mcspecial (quasisyntax form) env orig-env
    `(QUASISYNTAX
      ,(let traverse ((form form))
         (match form
           (((? (lambda (x) (eq? unsyntaxer (get env x)))) form)
            `(UNSYNTAX ,(mcexpand form env orig-env)))
           ((form . forms)
            (cons (traverse form) (traverse forms)))
           (form
            form)))
      ,env)))


;;; Execution

(define* (mcexecute code env #:optional original-env)
  (match code
    (('LAMBDA variables body)
     (make-mcprocedure env original-env variables body))
    (('QUOTE form)
     form)
    (('SYNTAX form expansion-env)
     (make-mcinjection form expansion-env env))
    (('QUASIQUOTE form)
     (let traverse ((form form))
       (match form
         (('UNQUOTE code)
          (mcexecute code env original-env))
         ((form . forms)
          (cons (traverse form) (traverse forms)))
         (form
          form))))
    (('QUASISYNTAX form expansion-env)
     (make-mcinjection
      (let traverse ((form form))
        (match form
          (('UNSYNTAX code)
           (make-mcuninjection (mcexecute code env original-env)))
          ((form . forms)
           (cons (traverse form) (traverse forms)))
          (form
           form)))
      expansion-env
      env))
    (('INJECT code injection-env)
     (mcexecute code injection-env env))
    (('UNINJECT code)
     (mcexecute code original-env))
    (('APPLY operator operands)
     (mcapply (mcexecute operator env original-env)
              (map (lambda (x) (mcexecute x env original-env)) operands)))
    (('REF variable)
     (let ((value (get env variable)))
       ;; Cheat a bit so we can run some real code.
       (or value (module-ref (resolve-module '(taylan scheme)) variable))))
    (('CONST constant)
     constant)
    (form
     (error "invalid code" form))))

(define (mcapply procedure arguments)
  (if (mcprocedure? procedure)
      (mcexecute (mcprocedure-body procedure)
                 (env-append
                  (mcprocedure-env procedure)
                  (map cons (mcprocedure-arglist procedure) arguments))
                 (if (mcprocedure-orig-env procedure)
                     (env-append
                      (mcprocedure-orig-env procedure)
                      (map cons (mcprocedure-arglist procedure) arguments))
                     #f))
      (apply procedure arguments)))


;;; Eval and REPL

(define (mceval-toplevel form)
  (match form
    (('define name form)
     (put! execution-env name (mceval form)))
    (('define-syntax name form)
     (put! expansion-env name (make-mcmacro form expansion-env #f name)))
    (form
     (mceval form))))

(define (mceval form)
  (mcexecute (mcexpand form expansion-env) execution-env))

(define (mcrepl)
  (display ">>> ")
  (let ((form (read)))
    (unless (eq? 'exit form)
      (write (mceval-toplevel form))
      (newline)
      (mcrepl))))

(mceval-toplevel
 `(define apply ,mcapply))

(mceval-toplevel
 '(define-syntax let (lambda (form)
                       #`(apply (lambda #,(map car (car form))
                                  #,(cadr form))
                                #,(map cadr (car form)))
                       )))
