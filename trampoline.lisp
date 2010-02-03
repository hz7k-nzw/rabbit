;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LISP code for RABBIT-compiled code driver
;;; by Darius Bacon (http://wry.me/)
;;;
;;; This file is intended to be loaded after scheme.lisp.
;;; (Overwrites the EVLIS function in scheme.lisp)
;;;
;;; RABBIT is the CPS-based SCHEME compiler
;;; by Guy Lewis Steele, Jr. (see rabbit.scm for detail)
;;;
;;; A few minor changes made by Kenji Nozawa
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DECLARE (SPECIAL **fun** **cont** **nargs** ;also **env** but that's in interpreter too
                  **one** **two** **three** **four** **five** **six** **seven** **eight**))
(DECLARE (SPECIAL **EXP** **UNEVLIS** **ENV** **EVLIS** **PC** **CLINK** **VAL**
                  **TOP**))

(DEFUN rabbit-scheme ()
  "Like (scheme), but can run RABBIT-compiled code too."
  (TERPRI)
  (PRINC '|This is SCHEME modified for RABBIT interoperability|)
  (jump-onto-trampoline **TOP** '(|RABBIT-SCHEME -- Toplevel|)))

;; Convenience function for running code through RABBIT.
(defvar compile-and-load
  '(beta (lambda (fname)
           (block
             (comfile fname)              ;from rabbit.scm
             (terpri)
             (compile-file (java:string-replace-first fname "\\.scm" ".lisp"))
             (format t "~A compiled~%" (java:string-replace-first fname "\\.scm" ".lisp"))
             (load (java:string-replace-first fname "\\.scm" ".fasl"))
             (format t "~A loaded~%" (java:string-replace-first fname "\\.scm" ".fasl"))
             T))
         nil))

(defun bounce-off ()
  (*throw 'bounce-off **one**))

(defun jump-onto-trampoline (fun args)
  "Execute the equivalent of (apply fun args) on the trampoline and return the result."
  (setq **fun** fun
        **cont** (list 'cbeta #'bounce-off))
  (pack-argument-registers args)
  (*catch 'bounce-off (trampoline)))

(defun trampoline ()
  "Top-level loop running Scheme code (compiled or interpreted)."
  (do () (nil)
;    (dump 'in-trampoline)
    (cond
     ((listp **fun**)
      (cond ((eq 'cbeta (car **fun**))
             (setq **env** (cddr **fun**))
             (funcall (cadr **fun**)))
            ((eq 'beta (car **fun**))
             (let ((lambda-exp (cadr **fun**))
                   (environment (caddr **fun**)))
               (let ((parameters (cadr lambda-exp))
                     (body (caddr lambda-exp)))
                 (setq **exp** body
                       **env** (pairlis parameters (unpack-argument-registers) environment)
                       **pc** 'aeval
                       **clink** (compiled->interpreted-cont **cont**)
                       **fun** nil)))
             (my-mloop))
            ((eq (car **fun**) 'delta)
             (setq **clink** (cadr **fun**)
                   **val** **one**
                   **fun** nil)
             (restore)
             (my-mloop))
            (T (ERROR '|BAD FUNCTION - TRAMPOLINE| **FUN** 'FAIL-ACT))))
     ((subrp **fun**) ; Does this detect LSUBRs too? I'm not sure.
      (setq **one**
            (cond
             ;; For speed, we SUBRCALL in common cases, rather than APPLY:
             ;; (except actually we use FUNCALL for now)
             ((= 0 **nargs**) (funcall **fun**))
             ((= 1 **nargs**) (funcall **fun** **one**))
             ((= 2 **nargs**) (funcall **fun** **one** **two**))
             ((= 3 **nargs**) (funcall **fun** **one** **two** **three**))
             (t (apply **fun** (unpack-argument-registers))))
            **fun** **cont**))
     ((exprp **fun**)
      (setq **one** (apply **fun** (unpack-argument-registers))
            **fun** **cont**))
     (t (ERROR '|BAD FUNCTION - TRAMPOLINE| **FUN** 'FAIL-ACT)))))

(defun dump (tag)
  (print '****)
  (princ tag)
  (print (list 'fun **fun**))
  (print (list 'cont **cont**))
  (print (list 'nargs **nargs**))
  (print (list 'one **one**))
  (print (list 'pc **pc**))
  (print '----))

(defun unpack-argument-registers ()
  (cond
   ((= 0 **nargs**) (list))
   ((= 1 **nargs**) (list **one**))
   ((= 2 **nargs**) (list **one** **two**))
   ((= 3 **nargs**) (list **one** **two** **three**))
   ((= 4 **nargs**) (list **one** **two** **three** **four**))
   ((= 5 **nargs**) (list **one** **two** **three** **four** **five**))
   ((= 6 **nargs**) (list **one** **two** **three** **four** **five** **six**))
   ((= 7 **nargs**) (list **one** **two** **three** **four** **five** **six** **seven**))
   ((= 8 **nargs**) (list **one** **two** **three** **four** **five** **six** **seven** **eight**))
   (t **one**)))

(defun pack-argument-registers (args)
  (setq **nargs** (length args))
  (cond ((< 8 **nargs**)
         (setq **one** args))
        (t (when args (setq **one**   (car args) args (cdr args)))
           (when args (setq **two**   (car args) args (cdr args)))
           (when args (setq **three** (car args) args (cdr args)))
           (when args (setq **four**  (car args) args (cdr args)))
           (when args (setq **five**  (car args) args (cdr args)))
           (when args (setq **six**   (car args) args (cdr args)))
           (when args (setq **seven** (car args) args (cdr args)))
           (when args (setq **eight** (car args))))))

(defun compiled->interpreted-cont (cont)
  "Return a continuation representation appropriate for **clink**, 
given one appropriate for **cont**."
  ;(LIST **EXP** **UNEVLIS** **ENV** **EVLIS** RETAG **CLINK**)
  (list nil nil nil nil 'return-to-trampoline cont))

(defun return-to-trampoline ()
  (setq **fun** **clink**
        **one** **val**))

(defun return-to-interpreter ()
  (setq **fun** nil)
  (setq **clink** **env**)
  (restore)
  (setq **val** **one**)
  (my-mloop))

(defun interpreted->compiled-cont (clink)
  "Return a continuation representation appropriate for **cont**, 
given one appropriate for **clink**."
  (list* 'cbeta #'return-to-interpreter clink))

(defun my-mloop ()
  (do () (**fun**)     ;** Changed code: no longer loops forever
    ;XXX I'm not sure of the best way to handle the multiprocessing stuff
    ; between here and (trampoline), so I'm just leaving it out for now.

;    (print '====)
;    (print (list 'pc **pc**))
;    (print (list 'exp **exp**))
;    (print '----)
  
    (funcall **pc**)))

(DEFUN EVLIS ()
  (COND ((NULL **UNEVLIS**)
         (SETQ **EVLIS** (REVERSE **EVLIS**))
         (COND ((ATOM (CAR **EVLIS**))
                (SETQ **VAL** (APPLY (CAR **EVLIS**) (CDR **EVLIS**)))
                (RESTORE))
               ((EQ (CAAR **EVLIS**) 'LAMBDA)
                (SETQ **ENV** (PAIRLIS (CADAR **EVLIS**)
                                       (CDR **EVLIS**)
                                       **ENV**)
                      **EXP** (CADDAR **EVLIS**)
                      **PC** 'AEVAL))
               ((EQ (CAAR **EVLIS**) 'BETA)
                (SETQ **ENV** (PAIRLIS (CADR (CADAR **EVLIS**))
                                       (CDR **EVLIS**)
                                       (CADDAR **EVLIS**))
                      **EXP** (CADDR (CADAR **EVLIS**))
                      **PC** 'AEVAL))
               ((EQ (CAAR **EVLIS**) 'DELTA)
                (SETQ **CLINK** (CADAR **EVLIS**))
                (RESTORE))
               ((eq (caar **evlis**) 'cbeta)                               ;** New code
                (pack-argument-registers (cdr **evlis**))                  ;**
                (setq **fun** (car **evlis**)                              ;**
                      **cont** (interpreted->compiled-cont **clink**)))    ;**
               (T (ERROR '|BAD FUNCTION - EVARGLIST| **EXP** 'FAIL-ACT))))
        (T (SAVEUP 'EVLIS1)
           (SETQ **EXP** (CAR **UNEVLIS**)
                 **PC** 'AEVAL))))
