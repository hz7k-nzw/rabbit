;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LISP code for the SCHEME interpreter
;;; by Gerald Jay Sussman and Guy Lewis Steele, Jr.
;;;
;;; This source code includes the detailed page-by-page notes on the
;;; code in the original paper, and also includes the code for macro
;;; by Darius Bacon (http://wry.me/), which is not included in the
;;; original paper.
;;;
;;; I made a few minor changes on this code. When I modified this
;;; code I preserved the original lines as comments starting with
;;; ";;--" and added new lines written in lowercase letters.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; -- 28 --
;;;
;;; Section 5: The Implementation of the Interpreter
;;; 
;;;  Here we present a real live SCHEME interpreter. This particular version
;;; was written primarily for expository purposes; it works, but not as 
;;; efficiently as possible. The "production version" of SCHEME is coded somewhat
;;; more intricately, and runs about twice as fast as the interpreter presented
;;; below.
;;;  The basic idea behind the implementation is think machine language. In
;;; particular, we must not use recursion in the implementation language to 
;;; implement recursion in the language being interpreted. This is crucial
;;; mistake which has screwed many language implementations (e.g. Micro-PLANNER
;;; [Sussman]). The reason for this is that if the implementation language does
;;; not support certain kinds of control structures, then we will not be able to
;;; effectively interpret them. Thus, for example, if the control frame structure
;;; in the implementation language is constrained to be stack-like, then modelling
;;; more general control structures in the interpreted language will be very
;;; difficult unless we divorce ourselves from the constrained structures at the
;;; outset.
;;;  It will be convenient to think of an implementation machine which has
;;; certain operations, which are "micro-coded" in LISP; these are used to
;;; operate on various "registers", which are represented as free LISP variables.
;;; These registers are:
;;; 
;;; **EXP**
;;;  The expression currently being evaluated.
;;; 
;;; **ENV**
;;;  A pointer to the environment in which to evaluate EXP.
;;; 
;;; **CLINK**
;;;  A pointer to the frame for the computation of which the current one is a
;;; subcomputation.
;;; 
;;; **PC**
;;;  The "program counter". As each "instruction" is executed, it updates
;;; **PC** to point the next instruction to be executed.
;;; 
;;; **VAL**
;;;  The returned value of a subcomputation. This register is not saved and
;;; restored in **CLINK** frames; in fact, its sole purpose is to pass values back
;;; safely across the restoration of a frame.
;;; 
;;; **UNEVLIS**, **EVLIS**
;;;  These are utility registers which are part of the state of the
;;; interpreter (they are saved in **CLINK** frames). They are used primarily for
;;; evaluation of components of combinations, but may be used for other purposes
;;; also.

;;; -- 29 --
;;;
;;; **TEM**
;;;  A super-temporary register, used for random purposes, and not saved in 
;;; **CLINK** frames or across interrupts. It therefore may not be used to pass
;;; information between "instructions" of the "machine", and so is best thought of
;;; as an internal hardware register.
;;; 
;;; **QUEUE**
;;;  A list of all processed other than the one currently being interpreted.
;;; 
;;; **TICK**
;;;  A magic register which a "hardware clock" sets to T every so often, used 
;;; to drive the scheduler.
;;; 
;;; **PROCESS**
;;;  This register always contains the name of the process currently swapped
;;; in and running.

;;; -- 30 --
;;;
;;;  The following declarations and macros are present only to make the
;;; compiler happy, and to make the version number of the SCHEME implementation
;;; available in the global variable VERSION.

(DECLARE (SPECIAL **EXP** **UNEVLIS** **ENV** **EVLIS** **PC** **CLINK** **VAL**
		  **TEM** **TOP** **QUEUE** **TICK** **PROCESS** **QUANTUM**
		  VERSION LISPVERSION))

;;--(DEFUN VERSION MACRO (X)
;;--  (COND (COMPILER-STATE (LIST 'QUOTE (STATUS UREAD)))
;;--	(T (RPLACA X 'QUOTE)
;;--	   (RPLACD X (LIST VERSION))
;;--	   (LIST 'QUOTE VERSION))))
;;--
;;--(DECLARE (READ))
;;--
;;--(SETQ VERSION ((LAMBDA (COMPILER-STATE) (VERSION)) T))

;;; This function initializes the system driver. The two SETQ's
;;; merely set up version numbers. The top level loop itself is written in
;;; SCHEME, and is a LABELS which binds the function **TOP** to be a read-eval-
;;; print loop. The LISP global variable **TOP** is initialized to the closure of
;;; the **TOP** function for convenience and accessibility to user-defined
;;; functions.

(DEFUN SCHEME ()
  ;;--(SETQ VERSION (VERSION) LISPVERSION (STATUS LISPVERSION))
  (setq version "xxx" lispversion "yyy")
  (TERPRI)
  (PRINC '|This is SCHEME |)
  (PRINC VERSION)
  (PRINC '| running in LISP |)
  (PRINC LISPVERSION)
  (SETQ **ENV** NIL **QUEUE** NIL
	**PROCESS** (CREATE!PROCESS '(**TOP** '|SCHEME -- Toplevel|)))
  (SWAPINPROCESS)
  ;;--(ALARMCLOCK 'RUNTIME **QUANTUM**)
  (MLOOP))

(SETQ **TOP**
      '(BETA (LAMBDA (**MESSAGE**)
	       (LABELS ((**TOP1**
			 (LAMBDA (**IGNORE1** **IGNORE2** **IGNORE3**)
			   (**TOP1** (TERPRI) (PRINC '|==> |)
				     ;;--(PRINT (SET '* (EVALUATE (READ))))))))
				     (print (evaluate (read)))))))
		 (**TOP1** (TERPRI)
			   (PRINC **MESSAGE**)
			   NIL)))
	     NIL))

;;;  When the LISP alarmclock tick occurs, the global register **TICK** is
;;; set to T. **QUANTUM**, the amount of runtime between ticks, is measured in

;;; -- 31 --
;;;
;;; micro-seconds.

(DEFUN SETTICK (X) (SETQ **TICK** T))

(SETQ **QUANTUM** 1000000. ALARMCLOCK 'SETTICK)

;;;  MLOOP is the main loop of the interpreter. It may be thought of as the
;;; instruction dispatch in the micro-code of the implementation machine. If an
;;; alarmclock tick has occurred, and interrupts are allowed, then the scheduler
;;; is called to switch processes. Otherwise the "instruction" specified by
;;; **PC** is executed via FASTCALL.

(DEFUN MLOOP ()
  ;;--(DO ((**TICK** NIL)) (NIL) ; DO forever
  (do ((**tick** t)) (nil) ; do forever
    (AND **TICK** (ALLOW) (SCHEDULE))
    (FASTCALL **PC**)))

;;;  FASTCALL is essentially a FUNCALL optimized for compiled "microcode".
;;; Note the way it pulls the SUBR property to the front of the property list if
;;; possible for speed.

(DEFUN FASTCALL (ATSYM)
  ;;--(COND ((EQ (CAR (CDR ATSYM)) 'SUBR)
  (cond ((eq (car (plist atsym)) 'subr)
	 ;;--(SUBRCALL NIL (CADR (CDR ATSYM))))
	 (subrcall nil (cadr (plist atsym))))
	(T ((LAMBDA (SUBR)
	      (COND (SUBR (REMPROP ATSYM 'SUBR)
			  (PUTPROP ATSYM SUBR 'SUBR)
			  (SUBRCALL NIL SUBR))
		    (T (FUNCALL ATSYM))))
	    (GET ATSYM 'SUBR)))))

;;;  Interrupts are allowed unless the variable *ALLOW* is bound to NIL in
;;; the current environment. This is used to implement the 
;;; EVALUATE!UNINTERRUPTIBLY primitive.

(DEFUN ALLOW ()
  ((LAMBDA (VCELL)
     (COND (VCELL (CADR VCELL))
	   (T T)))
   (ASSQ '*ALLOW* **ENV**)))

;;;  Next comes the scheduler. It is apparently interrupt-driven, but in
;;; fact is not. The key here is to think microcode! There is one place in the
;;; microcode instruction interpretation loop which checks to see if there is an
;;; interrupt pending; in our "machine", this occurs in MLOOP, where **TICK** is
;;; checked on every cycle. This is another case where we must beware of using
;;; too much of the power of the host language; just as we must avoid using host
;;; recursion directly to implement recursion, so we must avoid using host
;;; interrupts directly to implement interrupts. We may not modify any register
;;; during a host language interrupt, except one (such as **TICK**) which is

;;; -- 32 --
;;;
;;; specifically intended to signal interrupts. Thus, if we were to add an 
;;; interrupt character facility to SCHEME similar to that in MacLISP [Moon], the
;;; MacLISP interrupt character function would merely set a register like **TICK**
;;; and dismiss; MLOOP would eventually notice that this register had changed and
;;; dispatch to the interrupt handler. All this implies that the "microcode" for
;;; the interrupt handlers does not itself contain critical code that must be
;;; protected from host language interrupts.
;;;  When the scheduler is invoked, if there is another process waiting on 
;;; the process queue, then current process is swapped out and put on the end
;;; of the queue, and a new process swapped in from the front of the queue. The
;;; process stored on the queue consists of an atom which has the current frame
;;; and **VAL** register on its property list. Note that **TEM** register is
;;; not saved, and so cannot be used to pass information between instructions.

(DEFUN SCHEDULE ()
  (COND (**QUEUE**
	 (SWAPOUTPROCESS)
	 (NCONC **QUEUE** (LIST **PROCESS**))
	 (SETQ **PROCESS** (CAR **QUEUE**)
	       **QUEUE** (CDR **QUEUE**))
	 (SWAPINPROCESS)))
  (SETQ **TICK** NIL)
  (ALARMCLOCK 'RUNTIME **QUANTUM**))

(DEFUN SWAPOUTPROCESS ()
  ((LAMBDA (**CLINK**)
     (PUTPROP **PROCESS** (SAVEUP **PC**) 'CLINK)
     (PUTPROP **PROCESS** **VAL** 'VAL))
   **CLINK**))

(DEFUN SWAPINPROCESS ()
  (SETQ **CLINK** (GET **PROCESS** 'CLINK)
	**VAL** (GET **PROCESS** 'VAL))
  (RESTORE))

;;;  Primitive operators are LISP functions, i.e. SUBRs, EXPRs, and LSUBRs.

(DEFUN PRIMOP (X) (GETL X '(SUBR EXPR LSUBR)))

;;;  SAVEUP conses a new frame onto the **CLINK** structure. It saves the 
;;; value of all important registers. It takes one argument, RETAG, which is the
;;; instruction to return to when the computation is restored.

(DEFUN SAVEUP (RETAG)
  (SETQ **CLINK** (LIST **EXP** **UNEVLIS** **ENV**
			**EVLIS** RETAG **CLINK**)))

;;; RESTORE restores a computation from CLINK. The use of TEMP is a 
;;; kludge to optimize the compilation of the "microcode".

;;; -- 33 --

(DEFUN RESTORE ()
  (PROG (TEMP)
	(SETQ TEMP (OR **CLINK**
		       (ERROR '|PROCESS RAN OUT - RESTORE|
			      **EXP**
			      'FAIL-ACT))
	      **EXP** (CAR TEMP)
	      TEMP (CDR TEMP)
	      **UNEVLIS** (CAR TEMP)
	      TEMP (CDR TEMP)
	      **ENV** (CAR TEMP)
	      TEMP (CDR TEMP)
	      **EVLIS** (CAR TEMP)
	      TEMP (CDR TEMP)
	      **PC** (CAR TEMP)
	      TEMP (CDR TEMP)
	      **CLINK** (CAR TEMP))))

;;;  This is the central function of the SCHEME interpreter. This 
;;; "instruction" expects **EXP** to contain an expression to evaluate, and
;;; **ENV** to contain the environment for the evaluation. The fact that we have
;;; arrived here indicates that **PC** contains 'AEVAL, and so we need not change
;;; **PC** if the next instruction is also to be AEVAL. Besides the obvious
;;; objects like numbers, identifiers, LAMBDA expressions, and BETA expressions
;;; (closures), there also several other objects of interest. There are 
;;; primitive operators (LISP functions); AINTs (which are to SCHEME as FSUBRs
;;; like COND are to LISP); and AMACROs, which are used to implement DO, AND, OR,
;;; COND, BLOCK, etc.

;;; -- 34 --

;;--(DEFUN AEVAL ()
;;--  (COND ((ATOM **EXP**)
;;--	 (COND ((NUMBERP **EXP**)
;;--		(SETQ **VAL** **EXP**)
;;--		(RESTORE))
;;--	       ((PRIMOP **EXP**)
;;--		(SETQ **VAL** **EXP**)
;;--		(RESTORE))
;;--	       ((SETQ **TEM** (ASSQ **EXP** **ENV**))
;;--		(SETQ **VAL** (CADR **TEM**))
;;--		(RESTORE))
;;--	       (T (SETQ **VAL** (SYMEVAL **EXP**))
;;--		  (RESTORE))))
;;--	((ATOM (CAR **EXP**))
;;--	 (COND ((SETQ **TEM** (GET (CAR **EXP**) 'AINT))
;;--		(SETQ **PC** **TEM**))
;;--	       ((EQ (CAR **EXP**) 'LAMBDA)
;;--		(SETQ **VAL** (LIST 'BETA **EXP** **ENV**))
;;--		(RESTORE))
;;--	       ((SETQ **TEM** (GET (CAR **EXP**) 'AMACRO))
;;--		(SETQ **EXP** (FUNCALL **TEM** **EXP**)))
;;--	       (T (SETQ **EVLIS** NIL
;;--			**UNEVLIS** **EXP**
;;--			**PC** 'EVLIS))))
;;--	((EQ (CAAR **EXP**) 'LAMBDA)
;;--	 (SETQ **EVLIS** (LIST (CAR **EXP**))
;;--	       **UNEVLIS** (CDR **EXP**)
;;--	       **PC** 'EVLIS))
;;--	(T (SETQ **EVLIS** NIL
;;--		 **UNEVLIS** **EXP**
;;--		 **PC** 'EVLIS))))

(defun aeval ()
  (cond ((atom **exp**)
	 (cond ((numberp **exp**)
		(setq **val** **exp**)
		(restore))
	       ;;-- accepts string as atom
	       ((stringp **exp**)
		(setq **val** **exp**)
		(restore))
	       ;;-- accepts character as atom
	       ((characterp **exp**)
		(setq **val** **exp**)
		(restore))
	       ;;-- look up lex env before checking lisp primop
	       ;;-- (scheme operator may override lisp primop)
	       ((setq **tem** (assq **exp** **env**))
		(setq **val** (cadr **tem**))
		(restore))
	       ;;-- look up global env before checking lisp primop
	       ;;-- (scheme operator may override lisp primop)
	       ((boundp **exp**)
		(setq **val** (symeval **exp**))
		(restore))
	       ;;-- look up lisp primop
	       ((primop **exp**)
		(setq **val** **exp**)
		(restore))
	       (t (error '|BAD ATOM - AEVAL| **exp** 'fail-act))))
	((atom (car **exp**))
	 (cond ((setq **tem** (get (car **exp**) 'aint))
		(setq **pc** **tem**))
	       ((eq (car **exp**) 'lambda)
		(setq **val** (list 'beta **exp** **env**))
		(restore))
	       ;;-- expand macro defined via schmac
	       ((setq **tem** (get (car **exp**) 'amacro))
		(setq **exp** (funcall **tem** **exp**)))
	       ;;-- expand macro defined via defmac or defmacro
	       ((setq **tem** (get (car **exp**) 'macro))
		(setq **exp** (macroexpand **exp**)))
	       ;;-- eval lisp fsubr (defun, defmacro, declare, ...)
	       ((setq **tem** (get (car **exp**) 'fsubr))
		(setq **val** (funcall **tem** (cdr **exp**)))
		(restore))
	       (t (setq **evlis** nil
			**unevlis** **exp**
			**pc** 'evlis))))
	((eq (caar **exp**) 'lambda)
	 (setq **evlis** (list (car **exp**))
	       **unevlis** (cdr **exp**)
	       **pc** 'evlis))
	(t (setq **evlis** nil
		 **unevlis** **exp**
		 **pc** 'evlis))))

;;;  We come to EVLIS when a combination is encountered. The intention is to
;;; evaluate each component of the combination and then apply the resulting
;;; function to the resulting arguments. We use the register **UNEVLIS** to hold
;;; the list of components yet to be evaluated, and the register **EVLIS** to hold
;;; the list of evaluated components. We assume that these have been set up by
;;; AEVAL. Note that in the case of an explicit LAMBDA expression in the CAR of a 
;;; combination **UNEVLIS** is initialized to be the list of unevaluated arguments
;;; and **EVLIS** is initialized to be the list containing the lambda expression.
;;;  EVLIS checks to see if there remain any more components yet to be
;;; evaluated. If not, it applies the function. Note that the primitive
;;; operators are applied using the LISP function APPLY. Note also how a BETA
;;; expression controls the environment in which its body is to be evaluated.
;;; DELTA expressions are CATCH tags (see CATCH). It is interesting that the
;;; evaluated components are collected in the reverse order from that which we
;;; need them in, and so we must reverse the list before applying the function.
;;; Do you see why we must not use side effects (e.g. the NREVERSE function) to
;;; reverse the list? Think about CATCH!
;;;  If there remain components yet to be evaluated, EVLIS saves up a frame,

;;; -- 35 --
;;;
;;; so that execution can be resumed at EVLIS1 when the evaluation of the
;;; component returns with a value. It then sets up **EXP** to point to the
;;; component to be evaluated and dispatches to AEVAL.

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
	       (T (ERROR '|BAD FUNCTION - EVARGLIST| **EXP** 'FAIL-ACT))))
	(T (SAVEUP 'EVLIS1)
	   (SETQ **EXP** (CAR **UNEVLIS**)
		 **PC** 'AEVAL))))

;;;  The purpose of EVLIS1 is to gobble up the value, passed in the **VAL**
;;; register, of the subexpression just evaluated. It saves this value on the
;;; list in the **EVLIS** register, pops off the unevaluated subexpression from
;;; the **UNEVLIS** register, and dispatches back to EVLIS.

(DEFUN EVLIS1 ()
  (SETQ **EVLIS** (CONS **VAL** **EVLIS**)
	**UNEVLIS** (CDR **UNEVLIS**)
	**PC** 'EVLIS))

;;;  Here is the code for the various AINTs. On arrival at the instruction
;;; for an AINT, **EXP** contains the expression whose functional position
;;; contains the name of the AINT. None of the arguments have been evaluated, and
;;; no new control frame has been created. Note that each AINT is defined by the
;;; presence of an AINT property on the property list of the LISP atom which is
;;; its name. The value of this property is the LISP function which is the first
;;; "instruction" of the AINT.
;;; 
;;;  EVALUATE is similar to the LISP function EVAL; it evaluates its
;;; argument, which should result in a s-expression, which is then fed back into
;;; the SCHEME expression evaluator (AEVAL).

;;; -- 36 --

(DEFPROP EVALUATE EVALUATE AINT)

(DEFUN EVALUATE ()
  (SAVEUP 'EVALUATE1)
  (SETQ **EXP** (CADR **EXP**)
	**PC** 'AEVAL))

(DEFUN EVALUATE1 ()
  (SETQ **EXP** **VAL**
	**PC** 'AEVAL))

;;;  IF evaluates its first argument, with a return address of IF1. IF1
;;; examines the resulting **VAL**, and gives either the second or third argument
;;; to AEVAL depending on whether the **VAL** was non-NIL or NIL.

(DEFPROP IF IF AINT)

(DEFUN IF ()
  (SAVEUP 'IF1)
  (SETQ **EXP** (CADR **EXP**)
	**PC** 'AEVAL))

(DEFUN IF1 ()
  (COND (**VAL** (SETQ **EXP** (CADDR **EXP**)))
	(T (SETQ **EXP** (CADDDR **EXP**))))
  (SETQ **PC** 'AEVAL))

;;;  As it was in the beginning, is now, and eval shall be: QUOTE without
;;; end. (Amen, amen.)

(DEFPROP QUOTE AQUOTE AINT)

(DEFUN AQUOTE ()
  (SETQ **VAL** (CADR **EXP**))
  (RESTORE))

;;;  LABELS merely feeds its second argument to AEVAL after constructing a
;;; fiendishly clever environment structure. This is done in two stages: first
;;; the skeleton of the structure is created, with null environment in the
;;; closures of the bound functions; next the created environment is clobbered
;;; into each of the closures.

;;; -- 37 --

(DEFPROP LABELS LABELS AINT)

(DEFUN LABELS ()
  (SETQ **TEM** (MAPCAR '(LAMBDA (DEF)
			   (LIST (CAR DEF)
				 (LIST 'BETA (CADR DEF) NIL)))
			(CADR **EXP**)))
  (MAPC '(LAMBDA (VC)
	   (RPLACA (CDDADR VC) **TEM**))
	**TEM**)
  (SETQ **ENV** (NCONC **TEM** **ENV**)
	**EXP** (CADDR **EXP**)
	**PC** 'AEVAL))

;;;  We now come to the multiprocess primitives.
;;;  CREATE!PROCESS temporarily creates a new set of machine registers (by
;;; the lambda-binding mechanism of the host language), establishes the new
;;; process in those registers, swap it out, and returns the new process id;
;;; returning causes old machine registers to be restored.

(DEFUN CREATE!PROCESS (EXP)
  ((LAMBDA (**PROCESS** **EXP** **ENV** **UNEVLIS** **EVLIS** **PC** **CLINK** **VAL**)
     (SWAPOUTPROCESS)
     **PROCESS**)
   (GENSYM)
   EXP
   **ENV**
   NIL
   NIL
   'AEVAL
   (LIST NIL NIL NIL NIL 'TERMINATE NIL)
   NIL))

(DEFUN START!PROCESS (P)
  (COND ((OR (NOT (ATOM P)) (NOT (GET P 'CLINK)))
	 (ERROR '|BAD PROCESS -- START!PROCESS| **EXP** 'FAIL-ACT)))
  (OR (EQ P **PROCESS**) (MEMQ P **QUEUE**)
      (SETQ **QUEUE** (NCONC **QUEUE** (LIST P))))
  P)

(DEFUN STOP!PROCESS (P)
  (COND ((MEMQ P **QUEUE**)
	 (SETQ **QUEUE** (DELQ P **QUEUE**)))
	((EQ P **PROCESS**) (TERMINATE)))
  P)

;;;  TERMINATE is an internal microcode routine which terminates the current
;;; process. If the current process is the only one, then all processes have been
;;; stopped, and so a new SCHEME top level is created; otherwise TERMINATE pulls
;;; the next process off the scheduler queue and swaps it in. Note that we cannot
;;; use SWAPINPROCESS because a RESTORE will happen in EVLIS as soon as TERMINATE
;;; completes (this is a very deep global property of the interpreter, and a fine

;;; -- 38 --
;;;
;;; source of bugs: much care is required).

(DEFUN TERMINATE ()
  (COND ((NULL **QUEUE**)
	 (SETQ **PROCESS**
	       (CREATE!PROCESS '(**TOP** '|SCHEME -- QUEUEOUT|))))
	(T (SETQ **PROCESS** (CAR **QUEUE**)
		 **QUEUE** (CDR **QUEUE**))))
  (SETQ **CLINK** (GET **PROCESS** 'CLINK))
  (SETQ **VAL** (GET **PROCESS** 'VAL))
  'TERMINATE-VALUE)

;;;  EVALUATE!UNINTERRUPTIBLY merely binds the variable *ALLOW* to NIL, and
;;; then evaluates its argument. This is why this primitive follows the scoping
;;; rules for variables!

(DEFPROP EVALUATE!UNINTERRUPTIBLY EVALUATE!UNINTERRUPTIBLY AINT)

(DEFUN EVALUATE!UNINTERRUPTIBLY ()
  (SETQ **ENV** (CONS (LIST '*ALLOW* NIL) **ENV**)
	**EXP** (CADR **EXP**)
	**PC** 'AEVAL))

;;;  DEFINE closes the function to be defined in the null environment, and
;;; installs the closure in the LISP value cell.

(DEFPROP DEFINE DEFINE AINT)

(DEFUN DEFINE ()
  (SET (CADR **EXP**) (LIST 'BETA (CADDR **EXP**) NIL))
  (SETQ **VAL** (CADR **EXP**))
  (RESTORE))

;;;  ASET looks up the specified variable in the current environment, and
;;; clobbers the value cell in the environment with the new value. If the
;;; variable is not bound in the current environment, the LISP value cell is set.
;;; Note that ASET does not need to be an AINT, since it does not fool with order
;;; of evaluation; all it needs is access to the "machine register" **ENV**.

(DEFUN ASET (VAR VALU)
  (SETQ **TEM** (ASSQ VAR **ENV**))
  (COND (**TEM** (RPLACA (CDR **TEM**) VALU))
	(T (SET VAR VALU)))
  VALU)

;;;  CATCH binds the tag variable to a DELTA expression which contains the
;;; current CLINK. When AEVAL applies such an expression as a function (of one
;;; argument), it makes the **CLINK** in the DELTA expression be the **CLINK**, 
;;; places the value of the argument in **VAL**, and does a RESTORE. The effect
;;; is to return from the CATCH expression with the argument to the DELTA

;;; -- 39 --
;;;
;;; expression as its value (can you see why?).

(DEFPROP CATCH ACATCH AINT)

(DEFUN ACATCH ()
  (SETQ **ENV** (CONS (LIST (CADR **EXP**) (LIST 'DELTA **CLINK**)) **ENV**)
	**EXP** (CADDR **EXP**)
	**PC** 'AEVAL))

;;;  PAIRLIS is as in the LISP 1.5 Programmer's Manual [McCarthy].

(DEFUN PAIRLIS (X Y Z)
  (DO ((I X (CDR I))
       (J Y (CDR J))
       (L Z (CONS (LIST (CAR I) (CAR J)) L)))
      ((AND (NULL I) (NULL J)) L)
    (AND (OR (NULL I) (NULL J))
	 (ERROR '|WRONG NUMBER OF ARGUMENTS - PAIRLIS|
		**EXP**
		'WRNG-NO-ARGS))))

;;;  AMACROs are fairly complicated beasties, and have very little to do with
;;; the basic issues of the implementation of SCHEME per se, so the code for them
;;; will not be given here. AMOCROs behave almost exactly like MacLISP macros
;;; [Moon].
;;; 
;;; This is the end of the SCHEME interpreter!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Macro stuff implemented by Darius Bacon
;;; http://wry.me/
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Macro stuff not implemented in the original Scheme paper:

;;--(eval-when (:execute :compile-toplevel :load-toplevel)
(eval-when (eval compile load)
  ;;--(defmacro defmac (name params &body body)
  (defmacro define-schmac (name params &body body)
    (let ((subject (gensym)))
      `(putprop ',name
		#'(lambda (,subject)
		    (destructuring-bind ,params (cdr ,subject)
		      ,@body))
		'amacro))))

; Think this is buggy but it's currently unused:
;;--(defmac let (pairs exp)
;;--  `((lambda ,(mapcar 'car pairs) ,exp)
;;--    ,@(mapcar 'cadr pairs)))
(define-schmac let (pairs . body)
  `((lambda ,(mapcar 'car pairs) (block ,@body))
    ,@(mapcar 'cadr pairs)))

;;--(defmac and args
(define-schmac and args
  (cond ((null (cdr args)) (car args))
	(t `(if ,(car args)
		(and ,@(cdr args))
	        nil))))

;;--(defmac or args
(define-schmac or args
  (cond ((null (cdr args)) (car args))
	(t `((lambda (x p) (if x x (p)))
	     ,(car args)
	     (lambda () (or ,@(cdr args)))))))

;;--(defmac block (exp . exps)
;;--  (cond ((null exps) exp)
;;--	(t `((lambda (x p) (p))
;;--	     ,exp
;;--	     (lambda () (block ,@exps))))))
(define-schmac block args
  (cond ((null args) nil)
	((null (cdr args)) (car args))
	(t `((lambda (x p) (p))
	     ,(car args)
	     (lambda () (block ,@(cdr args)))))))

;;--(defmac cond clauses
(define-schmac cond clauses
  (cond ((null clauses) nil)
	(t `(if ,(caar clauses)
		(block ,@(cdar clauses))
	        (cond ,@(cdr clauses))))))

;;--(defmac do (iters exit . body)
(define-schmac do (iters exit . body)
  (let ((vars (mapcar 'car iters))
	(inits (mapcar 'cadr iters))
	(steps (mapcar 'caddr iters))
	(done (car exit))
	(result (cdr exit))
	(repeat (gensym)))
    `(labels ((,repeat
	       (lambda (,(gensym) ,@vars)
		 (if ,done 
		     (block ,@result)
		     (,repeat (block ,@body) ,@steps)))))
       (,repeat nil ,@inits))))

;;--(defparameter amapcar
(defvar amapcar
  '(beta (lambda (f xs) 
	   (if (null xs)
	       '()
	       (cons (f (car xs))
		     (amapcar f (cdr xs)))))
	 nil))

;;--(defparameter amaplist
(defvar amaplist
  '(beta (lambda (f xs) 
	   (if (null xs)
	       '()
	       (cons (f xs)
		     (amaplist f (cdr xs)))))
	 nil))

; I added this function for convenience:
;;--(defparameter aload
(defvar aload
  '(beta (lambda (filename)
	   ((lambda (port)
	      (labels ((loop 
			(lambda (input)
			  (if input
			      (block (evaluate input)
			             (loop (read port nil)))))))
		(block (loop (read port nil))
		       (close port))))
	    (open filename)))
	 nil))

; TODO: we'll need an APPLY function eventually

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Code added by Kenji Nozawa
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; note: "macro" used in RABBIT
;;; [operator / property-indicator ; comment]
;;; DEFMAC / MACRO  ; maclisp macro (body: maclisp code)
;;; SCHMAC / AMACRO ; pdp-10 scheme macro (body: maclisp code)
;;; MACRO  / SMACRO ; scheme macro (body: scheme code)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(defprop defmac defmac aint)
;;
;;(defun defmac ()
;;  (eval `(defmacro ,(cadr **exp**) ,(caddr **exp**) ,@(cdddr **exp**)))
;;  (setq **val** (cadr **exp**))
;;  (restore))
(putprop 'defmac (get 'defmacro 'fsubr) 'fsubr)

(putprop 'progn (get 'block 'amacro) 'amacro)

(defprop schmac schmac aint)

(defun schmac ()
  ;; How can I define schmac without using EVAL?
  (eval `(define-schmac ,(cadr **exp**) ,(caddr **exp**) ,@(cdddr **exp**)))
  (setq **val** (cadr **exp**))
  (restore))

(defprop proclaim proclaim aint)

(defun proclaim ()
  (setq **val** 'proclaim)
  (restore))

(defvar amapc
  '(beta (lambda (f xs)
	   (if (null xs)
	       '()
	       (block (f (car xs))
	         (amapc f (cdr xs)))))
	 nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ENCLOSE was originally included in trampoline.lisp by Darius
;;; Bacon, and moved here for better classification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The need for this came up when trying to get RABBIT to compile itself.
;; (When it tried to handle a PROCLAIM form.)
(defvar enclose
  '(beta (lambda (lambda-exp)
           ;; XXX I dunno if this is just what ENCLOSE is supposed to do.
           ;; But something like this...
           (list 'beta lambda-exp nil))
         nil))

