
(COMMENT THIS IS THE RABBIT LISP CODE FOR "rabbit/fact.scm") 

(DECLARE (SPECIAL **CONT** **ONE** **TWO** **THREE** **FOUR** **FIVE**
		  **SIX** **SEVEN** **EIGHT** **ENV** **FUN** **NARGS**)) 
(PROGN (QUOTE COMPILE) (COMMENT MODULE FOR FUNCTION FACT)
       (DEFUN |rabbit/fact-21| NIL
	 (PROG NIL (DECLARE (SPECIAL |rabbit/fact-21|))
	       (GO (PROG2 NIL (CAR **ENV**) (SETQ **ENV** (CDR **ENV**))))
	       F-20 (COMMENT (DEPTH = 0) (FNP = NIL) (VARS = (CONT-18 N)))
	       (COND ((= **ONE** (QUOTE 0))
		      (SETQ **FUN** **CONT**)
		      (SETQ **ONE** (QUOTE 1))
		      (RETURN NIL))
		     (T
		      ((LAMBDA (Q-22 Q-23)
			       (SETQ **ONE** Q-23)
			       (SETQ **CONT** Q-22))
		       (CONS (QUOTE CBETA)
			     (CONS |rabbit/fact-21|
				   (CONS (QUOTE C-19)
					 (CONS **ONE**
					       (CONS **CONT** **ENV**)))))
		       (- **ONE** (QUOTE 1)))
		      (GO F-20)))
	       C-19 (COMMENT (DEPTH = 0) (FNP = NIL) (ENV = (N CONT-18)))
	       (SETQ **FUN** (CADR **ENV**))
	       (SETQ **ONE** (* (CAR **ENV**) **ONE**))
	       (RETURN NIL)))
       (SETQ |rabbit/fact-21| (OR (GET (QUOTE |rabbit/fact-21|) (QUOTE SUBR))
				  (GET (QUOTE |rabbit/fact-21|) (QUOTE EXPR))
				  (ERROR "Either SUBR or EXPR is expected"
					 (QUOTE |rabbit/fact-21|))))
       (SETQ FACT (LIST (QUOTE CBETA) |rabbit/fact-21| (QUOTE F-20)))
       (DEFPROP |rabbit/fact-21| FACT USER-FUNCTION)) 
(PROGN (QUOTE COMPILE) (COMMENT MODULE FOR FUNCTION FACT-ITER)
       (DEFUN |rabbit/fact-54| NIL
	 (PROG NIL (DECLARE (SPECIAL |rabbit/fact-54|))
	       (GO (PROG2 NIL (CAR **ENV**) (SETQ **ENV** (CDR **ENV**))))
	       F-53 (COMMENT (DEPTH = 0) (FNP = NIL) (VARS = (CONT-51 N)))
	       ((LAMBDA (Q-55 Q-56 Q-57)
			(SETQ **FOUR** Q-57)
			(SETQ **THREE** Q-56)
			(SETQ **TWO** Q-55))
		**CONT** **ONE** (QUOTE 1))
	       (COMMENT (DEPTH = 2) (FNP = NOCLOSE) (VARS = (CONT-52 M ANS)))
	       (GO FNVAR-25)
	       FNVAR-25
	       (COMMENT (DEPTH = 2) (FNP = NOCLOSE) (VARS = (CONT-52 M ANS)))
	       (COND ((= **THREE** (QUOTE 0))
		      (SETQ **FUN** **TWO**)
		      (SETQ **ONE** **FOUR**)
		      (RETURN NIL))
		     (T
		      ((LAMBDA (Q-58 Q-59)
			       (SETQ **FOUR** Q-59)
			       (SETQ **THREE** Q-58))
		       (- **THREE** (QUOTE 1))
		       (* **THREE** **FOUR**))
		      (COMMENT (DEPTH = 2) (FNP = NOCLOSE) (VARS = (CONT-52 M ANS)))
		      (GO FNVAR-25)))))
       (SETQ |rabbit/fact-54| (OR (GET (QUOTE |rabbit/fact-54|) (QUOTE SUBR))
				  (GET (QUOTE |rabbit/fact-54|) (QUOTE EXPR))
				  (ERROR "Either SUBR or EXPR is expected"
					 (QUOTE |rabbit/fact-54|))))
       (SETQ FACT-ITER (LIST (QUOTE CBETA) |rabbit/fact-54| (QUOTE F-53)))
       (DEFPROP |rabbit/fact-54| FACT-ITER USER-FUNCTION)) 
(PROGN (QUOTE COMPILE) (COMMENT MODULE FOR FUNCTION |init-rabbit/fact|)
       (DEFUN |rabbit/fact-65| NIL
	 (PROG NIL (DECLARE (SPECIAL |rabbit/fact-65|))
	       (GO (PROG2 NIL (CAR **ENV**) (SETQ **ENV** (CDR **ENV**))))
	       F-64 (COMMENT (DEPTH = 0) (FNP = NIL) (VARS = (CONT-63)))
	       (SETQ **FUN** **CONT**)
	       (SETQ **ONE** (QUOTE NIL))
	       (RETURN NIL)))
       (SETQ |rabbit/fact-65| (OR (GET (QUOTE |rabbit/fact-65|) (QUOTE SUBR))
				  (GET (QUOTE |rabbit/fact-65|) (QUOTE EXPR))
				  (ERROR "Either SUBR or EXPR is expected"
					 (QUOTE |rabbit/fact-65|))))
       (SETQ |init-rabbit/fact| (LIST (QUOTE CBETA) |rabbit/fact-65| (QUOTE F-64)))
       (DEFPROP |rabbit/fact-65| |init-rabbit/fact| USER-FUNCTION)) 
(COMMENT (COMPILE TIME 9 SECONDS)) 
