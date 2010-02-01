(DEFINE COUNT
  (LAMBDA (L)
    (LABELS ((COUNTCAR
              (LAMBDA (L)
                (IF (ATOM L) 1
                    (+ (COUNTCAR (CAR L))
                       (COUNTCDR (CDR L))))))
             (COUNTCDR
              (LAMBDA (L)
                (IF (ATOM L)
                    (IF (NULL L) 0 1)
                    (+ (COUNTCAR (CAR L))
                       (COUNTCDR (CDR L)))))))
            (COUNTCDR L))))

(DEFINE CONS-CELL
  (LAMBDA (CONTANTS)
    (LABELS ((THE-CELL
              (LAMBDA (MSG)
                (IF (EQ MSG 'CONTENTS?) CONTENTS
                    (IF (EQ MSG 'CELL?) 'YES
                        (IF (EQ (CAR MSG) '<-)
                            (BLOCK (ASET 'CONTENTS (CADR MSG))
                                   THE-CELL)
                            (ERROR '|UNRECOGNIZED MESSAGE - CELL|
                                   MSG
                                   'WRNG-TYPE-ARG)))))))
            THE-CELL)))

(DEFINE SQRT
  (LAMBDA (X EPSILON)
    ((LAMBDA (ANS LOOPTAG)
       (CATCH RETURNTAG
              (PROGN
               (ASET 'LOOPTAG (CATCH M M)) ; CREATE RROG TAG
               (IF (< (ABS (-$ (*$ ANS ANS) X)) EPSILON)
                   (RETURNTAG ANS) ; RETURN
                   NIL) ; JFCL
               (ASET 'ANS (//$ (+$ (//$ X ANS) ANS) 2.0))
               (LOOPTAG LOOPTAG)))) ; GOTO
     1.0
     NIL)))

(DEFINE THROW (LAMBDA (TAG RESULT) (TAG RESULT)))

(DEFINE SEMGEN
  (LAMBDA (SEMVAL)
    (LIST (LAMBDA ()
            (EVALUATE!UNINTERRUPTIBLY
             (ASET' SEMVAL (+ SEMVAL 1))))
          ;;--(LABELS (P (LAMBDA ()
          (labels ((p (lambda ()
                       (EVALUATE!UNINTERRUPTIBLY
                        (IF (PLUSP SEMVAL)
                            (ASET' SEMVAL (- SEMVAL 1))
                            ;;--(P)))))
                            (p))))))
                  P))))

(DEFINE FACT
  (LAMBDA (N)
    (IF (= N 0) 1
        (* N (FACT (- N 1))))))

;;--(DEFINE FACT
(define fact-iter
  (LAMBDA (N)
    (LABELS ((FACT1
              (LAMBDA (M ANS)
                (IF (= M 0) ANS
                    (FACT1 (- M 1) (* M ANS))))))
            (FACT1 N 1))))

(DEFINE REV
  (LAMBDA (L)
    (LABELS ((DOLOOP
              (LAMBDA (L1 ANS)
                (IF (NULL L1) ANS
                    (DOLOOP (CDR L1)
                            (CONS (CAR L1) ANS))))))
            (DOLOOP L NIL))))

;;--(DEFINE FACT
(define fact-cps
  (LAMBDA (N C)
    (IF (= N 0) (C 1)
        ;;--(FACT (- N 1)
        (fact-cps (- n 1)
              (LAMBDA (A) (C (* N A)))))))

(DEFINE FRINGE
  (LAMBDA (TREE)
    (LABELS ((FRINGEN
              (LAMBDA (NODE ALT)
                (LAMBDA (GETTER)
                  (IF (ATOM NODE)
                      (GETTER NODE ALT)
                      ((FRINGEN (CAR NODE)
                                (LAMBDA (GETTER1)
                                  ((FRINGEN (CDR NODE) ALT)
                                   GETTER1)))
                       GETTER))))))
            (FRINGEN TREE
                     (LAMBDA (GETTER)
                       (GETTER '(EXHAUSTED) NIL))))))

(DEFINE SAMEFRINGE
  (LAMBDA (TREE1 TREE2)
    (LABELS ((SAME
              (LAMBDA (S1 S2)
                (S1 (LAMBDA (X1 R1)
                      (S2 (LAMBDA (X2 R2)
                            (IF (EQUAL X1 X2)
                                (IF (EQUAL X1 '(EXHAUSTED))
                                    T
                                    (SAME R1 R2))
                                NIL))))))))
            (SAME (FRINGE TREE1)
                  (FRINGE TREE2)))))

;;--(DEFINE FRINGE
(define fringe~
  (LAMBDA (TREE)
    (LABELS ((FRINGE1
              (LAMBDA (NODE ALT)
                (IF (ATOM NODE)
                    (LAMBDA (MSG)
                      (IF (EQ MSG 'FIRST) NODE
                          (IF (EQ MSG 'NEXT) (ALT)
                              (ERROR))))
                    (FRINGE1 (CAR NODE)
                             (LAMBDA () (FRINGE1 (CDR NODE) ALT)))))))
            (FRINGE1 TREE
                     (LAMBDA ()
                       (LAMBDA (MSG) (IF (EQ MSG 'FIRST) '*EOF* (ERROR))))))))

;;--(DEFINE SAMEFRINGE
(define samefringe~
  (LAMBDA (T1 T2)
    ;;--(DO ((C1 (FRINGE T1) (C1 'NEXT))
    ;;--     (C2 (FRINGE T2) (C2 'NEXT)))
    (do ((c1 (fringe~ t1) (c1 'next))
         (c2 (fringe~ t2) (c2 'next)))
        ((OR (NOT (EQ (C1 'FIRST) (C2 'FIRST)))
             (EQ (C1 'FIRST) '*EOF*)
             (EQ (C2 'FIRST) '*EOF*))
         (EQ (C1 'FIRST) (C2 'FIRST))))))

(DEFINE NFIRST
  (LAMBDA (E N)
    (IF (= N 0) NIL
        (CONS (CAR E) (NFIRST (CDR E) (- N 1))))))

(DEFINE NREST
  (LAMBDA (E N)
    (IF (= N 0) E
        (NREST (CDR E) (- N 1)))))

(DEFINE MATCH
  (LAMBDA (PATTERN EXPRESSION)
    (LABELS ((MATCH1
      (LAMBDA (P E ALIST LOSE)
        (IF (NULL P)
            (IF (NULL E) (LIST ALIST LOSE) (LOSE))
            (IF (ATOM (CAR P))
                (IF (NULL E)
                    (LOSE)
                    (IF (EQ (CAR E) (CAR P))
                        (MATCH1 (CDR P) (CDR E) ALIST LOSE)
                        (LOSE)))
                (IF (EQ (CAAR P) 'THV)
                    (IF (NULL E)
                        (LOSE)
                        ((LAMBDA (V)
                           (IF V
                               (IF (EQ (CAR E) (CADR V))
                                   (MATCH1 (CDR P) (CDR E) ALIST LOSE)
                                   (LOSE))
                               (MATCH1 (CDR P)
                                       (CDR E)
                                       (CONS (LIST (CADAR P) (CAR E)) ALIST)
                                       LOSE)))
                         (ASSQ (CADAR P) ALIST)))
                    (IF (EQ (CAAR P) 'THV*)
                        ((LAMBDA (V)
                           (IF V
                               (IF (< (LENGTH E) (LENGTH (CADR V)))
                                   (LOSE)
                                   (IF (EQUAL (NFIRST E (LENGTH (CADR V))) (CADR V))
                                       (MATCH1 (CDR P)
                                               (NREST E (LENGTH (CADR V)))
                                               ALIST
                                               LOSE)
                                       (LOSE)))
                               (LABELS ((MATCH*
                                 (LAMBDA (N)
                                   (IF (> N (LENGTH E))
                                       (LOSE)
                                       (MATCH1 (CDR P)
                                               (NREST E N)
                                               (CONS (LIST (CADAR P) (NFIRST E N))
                                                     ALIST)
                                               (LAMBDA () (MATCH* (+ N 1))))))))
                                       (MATCH* 0))))
                         (ASSQ (CADAR P) ALIST))
                        (LOSE))))))))
            (MATCH1 PATTERN EXPRESSION NIL (LAMBDA () NIL)))))

(DEFINE TRY!TWO!THINGS!IN!PARALLEL
  (LAMBDA (F1 F2)
    (CATCH C
      ((LAMBDA (P1 P2)
         ((LAMBDA (F1 F2)
            (EVALUATE!UNINTERRUPTIBLY
             (BLOCK (ASET 'P1 (CREATE!PROCESS '(F1)))
                    (ASET 'P2 (CREATE!PROCESS '(F2)))
                    (START!PROCESS P1)
                    (START!PROCESS P2)
                    (STOP!PROCESS **PROCESS**))))
          (LAMBDA ()
            ((LAMBDA (VALUE)
               (EVALUATE!UNINTERRUPTIBLY
                (BLOCK (STOP!PROCESS P2) (C VALUE))))
             (F1)))
          (LAMBDA ()
            ((LAMBDA (VALUE)
               (EVALUATE!UNINTERRUPTIBLY
                (BLOCK (STOP!PROCESS P1) (C VALUE))))
             (F2)))))
       NIL NIL))))

(DEFINE SIGN
  (LAMBDA (N)
    (IF (EQUAL N 0) 'ZERO
        (TRY!TWO!THINGS!IN!PARALLEL
         (LAMBDA ()
            (DO ((I 0 (ADD1 I)))
                ((EQUAL I N) 'POSITIVE)))
         (LAMBDA ()
            (DO ((I 0 (SUB1 I)))
                ((EQUAL I N) 'NEGATIVE)))))))

;;--(DEFINE FACT
;;--  (LAMBDA (N) (IF (= N 0) 1 (* N (FACT (- N 1))))))
;;--
;;--(DEFINE FACT
;;--  (LAMBDA (N)
;;--    (LABELS ((FACT1
;;--              (LAMBDA (M ANS)
;;--                (IF (= M 0) ANS (FACT1 (- M 1) (* M ANS))))))
;;--            (FACT1 N 1))))
;;--
;;--(DEFINE FACT
;;--  (LAMBDA (N C)
;;--    (IF (= N 0) (C 1)
;;--        (FACT (- N 1) (LAMBDA (A) (C (* N A)))))))
;;--
;;--(DEFINE FACT
;;--  (LAMBDA (N C)
;;--    (== N 0
;;--        (LAMBDA () (C 1))
;;--        (LAMBDA ()
;;--          (-- N 1
;;--              (LAMBDA (M)
;;--                (FACT M (LAMBDA (A) (** A N C)))))))))
;;--
;;--(DEFINE CONS
;;--  (LAMBDA (A B)
;;--    (LAMBDA (M)
;;--      (IF (EQ M 'FIRST?) A
;;--          (IF (EQ M 'REST?) B
;;--              (IF (EQ M 'LIST?) 'YES
;;--                  (ERROR '|UNRECOGNIZED MESSAGE - CONS|
;;--                         M
;;--                         'WRNG-TYPE-ARG)))))))
