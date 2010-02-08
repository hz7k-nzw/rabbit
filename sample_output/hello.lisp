
(COMMENT THIS IS THE RABBIT LISP CODE FOR "rabbit/hello.scm") 

(DECLARE (SPECIAL **CONT** **ONE** **TWO** **THREE** **FOUR** **FIVE**
		  **SIX** **SEVEN** **EIGHT** **ENV** **FUN** **NARGS**)) 
(PROGN (QUOTE COMPILE) (COMMENT MODULE FOR FUNCTION |init-rabbit/hello-103|)
       (DEFUN |rabbit/hello-120| NIL
	 (PROG NIL (DECLARE (SPECIAL |rabbit/hello-120|))
	       (GO (PROG2 NIL (CAR **ENV**) (SETQ **ENV** (CDR **ENV**))))
	       F-119 (COMMENT (DEPTH = 0) (FNP = NIL) (VARS = (CONT-118)))
	       (SETQ **FUN** **CONT**)
	       (SETQ **ONE** (PROGN (PRINT (QUOTE "hello")) (QUOTE NIL)))
	       (RETURN NIL)))
       (SETQ |rabbit/hello-120| (OR (GET (QUOTE |rabbit/hello-120|) (QUOTE SUBR))
				    (GET (QUOTE |rabbit/hello-120|) (QUOTE EXPR))
				    (ERROR "Either SUBR or EXPR is expected"
					   (QUOTE |rabbit/hello-120|))))
       (SETQ |init-rabbit/hello-103| (LIST (QUOTE CBETA) |rabbit/hello-120| (QUOTE F-119)))
       (DEFPROP |rabbit/hello-120| |init-rabbit/hello-103| USER-FUNCTION)) 
(DECLARE (SPECIAL |init-rabbit/hello-103|)) 
(PROGN (QUOTE COMPILE) (COMMENT MODULE FOR FUNCTION |init-rabbit/hello|)
       (DEFUN |rabbit/hello-127| NIL
	 (PROG NIL (DECLARE (SPECIAL |rabbit/hello-127|))
	       (GO (PROG2 NIL (CAR **ENV**) (SETQ **ENV** (CDR **ENV**))))
	       F-126 (COMMENT (DEPTH = 0) (FNP = NIL) (VARS = (CONT-125)))
	       (SETQ **FUN** |init-rabbit/hello-103|)
	       (SETQ **NARGS** (QUOTE 0))
	       (RETURN NIL)))
       (SETQ |rabbit/hello-127| (OR (GET (QUOTE |rabbit/hello-127|) (QUOTE SUBR))
				    (GET (QUOTE |rabbit/hello-127|) (QUOTE EXPR))
				    (ERROR "Either SUBR or EXPR is expected"
					   (QUOTE |rabbit/hello-127|))))
       (SETQ |init-rabbit/hello| (LIST (QUOTE CBETA) |rabbit/hello-127| (QUOTE F-126)))
       (DEFPROP |rabbit/hello-127| |init-rabbit/hello| USER-FUNCTION)) 
(COMMENT (COMPILE TIME 3 SECONDS)) 
