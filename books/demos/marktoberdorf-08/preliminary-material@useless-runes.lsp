(M1::FACT)
(M1::NTH-NIL)
(M1::ACL2-COUNT-NTH (279 143 (:REWRITE DEFAULT-+-2))
                    (193 143 (:REWRITE DEFAULT-+-1))
                    (128 32 (:REWRITE COMMUTATIVITY-OF-+))
                    (128 32 (:DEFINITION INTEGER-ABS))
                    (128 16 (:DEFINITION LENGTH))
                    (80 16 (:DEFINITION LEN))
                    (59 45 (:REWRITE DEFAULT-<-2))
                    (56 45 (:REWRITE DEFAULT-<-1))
                    (42 42 (:REWRITE DEFAULT-CDR))
                    (37 37 (:REWRITE FOLD-CONSTS-IN-+))
                    (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
                    (30 30 (:REWRITE DEFAULT-CAR))
                    (16 16 (:TYPE-PRESCRIPTION LEN))
                    (16 16 (:REWRITE DEFAULT-REALPART))
                    (16 16 (:REWRITE DEFAULT-NUMERATOR))
                    (16 16 (:REWRITE DEFAULT-IMAGPART))
                    (16 16 (:REWRITE DEFAULT-DENOMINATOR))
                    (16 16 (:REWRITE DEFAULT-COERCE-2))
                    (16 16 (:REWRITE DEFAULT-COERCE-1))
                    (10 10 (:REWRITE ZP-OPEN)))
(M1::PUSH)
(M1::TOP)
(M1::POP)
(M1::OPCODE)
(M1::ARG1)
(M1::ARG2)
(M1::ARG3)
(M1::MAKE-STATE)
(M1::PC)
(M1::LOCALS)
(M1::STACK)
(M1::PROGRAM)
(M1::NEXT-INST)
(M1::EXECUTE-PUSH)
(M1::EXECUTE-LOAD)
(M1::EXECUTE-ADD)
(M1::EXECUTE-STORE (6 3
                      (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
                   (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(M1::EXECUTE-SUB)
(M1::EXECUTE-MUL)
(M1::EXECUTE-GOTO)
(M1::EXECUTE-IFLE)
(M1::EXECUTE-IFLT)
(M1::EXECUTE-IFNE)
(M1::EXECUTE-IFANE)
(M1::EXECUTE-ALOAD)
(M1::DO-INST)
(M1::STEP (1 1 (:TYPE-PRESCRIPTION M1::STEP)))
(M1::HALTEDP (5 5 (:TYPE-PRESCRIPTION M1::STEP)))
(M1::RUN (6 6 (:TYPE-PRESCRIPTION M1::STEP)))
(M1::REPEAT)
(M1::IFACT-LOOP-SCHED)
(M1::IFACT-SCHED)
(M1::FACTORIAL-5-EXAMPLE)
(M1::COLLECT-AT-END)
(M1::COLLECT-VARS-IN-EXPR (163 78 (:REWRITE DEFAULT-+-2))
                          (109 78 (:REWRITE DEFAULT-+-1))
                          (64 16 (:REWRITE COMMUTATIVITY-OF-+))
                          (64 16 (:DEFINITION INTEGER-ABS))
                          (64 8 (:DEFINITION LENGTH))
                          (40 8 (:DEFINITION LEN))
                          (27 21 (:REWRITE DEFAULT-<-2))
                          (26 21 (:REWRITE DEFAULT-<-1))
                          (24 24 (:REWRITE DEFAULT-CDR))
                          (23 23 (:REWRITE FOLD-CONSTS-IN-+))
                          (17 17 (:REWRITE DEFAULT-CAR))
                          (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
                          (8 8 (:TYPE-PRESCRIPTION LEN))
                          (8 8 (:REWRITE DEFAULT-REALPART))
                          (8 8 (:REWRITE DEFAULT-NUMERATOR))
                          (8 8 (:REWRITE DEFAULT-IMAGPART))
                          (8 8 (:REWRITE DEFAULT-DENOMINATOR))
                          (8 8 (:REWRITE DEFAULT-COERCE-2))
                          (8 8 (:REWRITE DEFAULT-COERCE-1)))
(M1::COLLECT-VARS-IN-STMT* (197 98 (:REWRITE DEFAULT-+-2))
                           (131 98 (:REWRITE DEFAULT-+-1))
                           (88 22 (:REWRITE COMMUTATIVITY-OF-+))
                           (88 22 (:DEFINITION INTEGER-ABS))
                           (88 11 (:DEFINITION LENGTH))
                           (55 11 (:DEFINITION LEN))
                           (35 28 (:REWRITE DEFAULT-<-2))
                           (32 28 (:REWRITE DEFAULT-<-1))
                           (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
                           (11 11 (:TYPE-PRESCRIPTION LEN))
                           (11 11 (:REWRITE DEFAULT-REALPART))
                           (11 11 (:REWRITE DEFAULT-NUMERATOR))
                           (11 11 (:REWRITE DEFAULT-IMAGPART))
                           (11 11 (:REWRITE DEFAULT-DENOMINATOR))
                           (11 11 (:REWRITE DEFAULT-COERCE-2))
                           (11 11 (:REWRITE DEFAULT-COERCE-1))
                           (1 1
                              (:TYPE-PRESCRIPTION M1::COLLECT-AT-END)))
(M1::INDEX)
(M1::OP!)
(M1::LOAD!)
(M1::PUSH!)
(M1::EXPR! (163 78 (:REWRITE DEFAULT-+-2))
           (109 78 (:REWRITE DEFAULT-+-1))
           (64 16 (:REWRITE COMMUTATIVITY-OF-+))
           (64 16 (:DEFINITION INTEGER-ABS))
           (64 8 (:DEFINITION LENGTH))
           (40 8 (:DEFINITION LEN))
           (27 21 (:REWRITE DEFAULT-<-2))
           (26 21 (:REWRITE DEFAULT-<-1))
           (24 24 (:REWRITE DEFAULT-CDR))
           (23 23 (:REWRITE FOLD-CONSTS-IN-+))
           (17 17 (:REWRITE DEFAULT-CAR))
           (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
           (8 8 (:TYPE-PRESCRIPTION LEN))
           (8 8 (:REWRITE DEFAULT-REALPART))
           (8 8 (:REWRITE DEFAULT-NUMERATOR))
           (8 8 (:REWRITE DEFAULT-IMAGPART))
           (8 8 (:REWRITE DEFAULT-DENOMINATOR))
           (8 8 (:REWRITE DEFAULT-COERCE-2))
           (8 8 (:REWRITE DEFAULT-COERCE-1)))
(M1::IFLE!)
(M1::GOTO!)
(M1::WHILE!)
(M1::TEST!)
(M1::STORE!)
(M1::STMT*! (197 98 (:REWRITE DEFAULT-+-2))
            (131 98 (:REWRITE DEFAULT-+-1))
            (88 22 (:REWRITE COMMUTATIVITY-OF-+))
            (88 22 (:DEFINITION INTEGER-ABS))
            (88 11 (:DEFINITION LENGTH))
            (55 11 (:DEFINITION LEN))
            (35 28 (:REWRITE DEFAULT-<-2))
            (32 28 (:REWRITE DEFAULT-<-1))
            (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
            (11 11 (:TYPE-PRESCRIPTION LEN))
            (11 11 (:REWRITE DEFAULT-REALPART))
            (11 11 (:REWRITE DEFAULT-NUMERATOR))
            (11 11 (:REWRITE DEFAULT-IMAGPART))
            (11 11 (:REWRITE DEFAULT-DENOMINATOR))
            (11 11 (:REWRITE DEFAULT-COERCE-2))
            (11 11 (:REWRITE DEFAULT-COERCE-1))
            (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(M1::COMPILE)
(M1::EXAMPLE-COMPILATION-1)
(M1::STACKS)
(M1::STATES)
(M1::STEP-OPENER (170 49 (:DEFINITION NTH))
                 (113 63 (:REWRITE DEFAULT-+-2))
                 (92 92
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (89 63 (:REWRITE DEFAULT-+-1))
                 (55 11 (:REWRITE ZP-OPEN))
                 (35 35 (:REWRITE DEFAULT-CAR))
                 (29 29 (:REWRITE DEFAULT-CDR))
                 (28 28 (:META CANCEL_TIMES-EQUAL-CORRECT))
                 (28 28 (:META CANCEL_PLUS-EQUAL-CORRECT))
                 (22 2 (:DEFINITION UPDATE-NTH))
                 (21 17 (:REWRITE DEFAULT-<-1))
                 (19 19 (:TYPE-PRESCRIPTION M1::STEP))
                 (19 19 (:TYPE-PRESCRIPTION M1::DO-INST))
                 (19 17 (:REWRITE DEFAULT-<-2))
                 (17 17 (:META CANCEL_PLUS-LESSP-CORRECT))
                 (16 2 (:REWRITE DEFAULT-CHAR-CODE))
                 (14 2 (:REWRITE CHARACTERP-NTH))
                 (8 4 (:REWRITE DEFAULT-*-2))
                 (8 4 (:REWRITE DEFAULT-*-1))
                 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
                 (2 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
                 (2 2 (:REWRITE DEFAULT-COERCE-2))
                 (2 2 (:REWRITE DEFAULT-COERCE-1))
                 (2 2 (:REWRITE CHARACTER-LISTP-COERCE)))
(M1::RUN-OPENER (60 5 (:REWRITE M1::STEP-OPENER))
                (55 5 (:DEFINITION M1::NEXT-INST))
                (50 5 (:DEFINITION NTH))
                (25 5 (:REWRITE ZP-OPEN))
                (8 8 (:REWRITE DEFAULT-CDR))
                (5 5 (:REWRITE DEFAULT-CAR))
                (5 5 (:REWRITE DEFAULT-<-2))
                (5 5 (:REWRITE DEFAULT-<-1))
                (5 5 (:REWRITE DEFAULT-+-2))
                (5 5 (:REWRITE DEFAULT-+-1))
                (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
                (5 5 (:DEFINITION NOT)))
(M1::RUN-APPEND (168 14 (:REWRITE M1::STEP-OPENER))
                (154 14 (:DEFINITION M1::NEXT-INST))
                (140 14 (:DEFINITION NTH))
                (70 14 (:REWRITE ZP-OPEN))
                (28 28 (:REWRITE DEFAULT-CDR))
                (17 17 (:REWRITE DEFAULT-CAR))
                (16 8
                    (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                (14 14 (:REWRITE DEFAULT-<-2))
                (14 14 (:REWRITE DEFAULT-<-1))
                (14 14 (:REWRITE DEFAULT-+-2))
                (14 14 (:REWRITE DEFAULT-+-1))
                (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
                (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
                (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND))
                (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
                (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(M1::NTH-ADD1! (4 4 (:REWRITE DEFAULT-+-2))
               (4 4 (:REWRITE DEFAULT-+-1))
               (2 2 (:REWRITE ZP-OPEN))
               (2 2 (:REWRITE NATP-RW))
               (2 2 (:REWRITE DEFAULT-CAR))
               (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
               (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(M1::UPDATE-NTH-ADD1! (7 7 (:REWRITE DEFAULT-CDR))
                      (5 5 (:REWRITE DEFAULT-CAR))
                      (4 4 (:REWRITE DEFAULT-+-2))
                      (4 4 (:REWRITE DEFAULT-+-1))
                      (2 2 (:REWRITE ZP-OPEN))
                      (1 1 (:REWRITE NATP-RW)))
(M1::IFACT (4 4
              (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::IFACT-LOOP-LEMMA (76 4 (:DEFINITION M1::RUN))
                      (31 31 (:REWRITE DEFAULT-+-2))
                      (31 31 (:REWRITE DEFAULT-+-1))
                      (12 12 (:REWRITE DEFAULT-*-2))
                      (12 12 (:REWRITE DEFAULT-*-1))
                      (9 9 (:REWRITE DEFAULT-CDR))
                      (8 8
                         (:TYPE-PRESCRIPTION M1::IFACT-LOOP-SCHED))
                      (7 7 (:REWRITE ZP-OPEN))
                      (6 6 (:REWRITE NATP-RW))
                      (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
                      (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
                      (1 1
                         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                      (1 1 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE DEFAULT-<-2))
                      (1 1 (:REWRITE DEFAULT-<-1))
                      (1 1 (:META CANCEL_PLUS-LESSP-CORRECT)))
(M1::IFACT-LEMMA (44 4 (:DEFINITION M1::IFACT))
                 (38 1 (:DEFINITION M1::IFACT-LOOP-SCHED))
                 (34 12 (:DEFINITION BINARY-APPEND))
                 (20 4 (:REWRITE COMMUTATIVITY-OF-*))
                 (16 16 (:REWRITE DEFAULT-+-2))
                 (16 16 (:REWRITE DEFAULT-+-1))
                 (8 8 (:REWRITE DEFAULT-*-2))
                 (8 8 (:REWRITE DEFAULT-*-1))
                 (8 4 (:REWRITE UNICITY-OF-1))
                 (5 5 (:REWRITE ZP-OPEN))
                 (4 4 (:DEFINITION FIX))
                 (2 2 (:REWRITE DEFAULT-CDR))
                 (1 1 (:REWRITE NATP-RW))
                 (1 1 (:REWRITE DEFAULT-CAR)))
(M1::IFACT-IS-FACTORIAL (62 13 (:LINEAR X*Y>1-POSITIVE))
                        (31 20 (:REWRITE DEFAULT-*-2))
                        (21 20 (:REWRITE DEFAULT-*-1))
                        (15 13 (:REWRITE DEFAULT-<-2))
                        (13 13 (:REWRITE DEFAULT-<-1))
                        (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
                        (8 8 (:REWRITE NATP-RW))
                        (7 7 (:REWRITE ZP-OPEN))
                        (6 6 (:REWRITE DEFAULT-+-2))
                        (6 6 (:REWRITE DEFAULT-+-1))
                        (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
                        (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
                        (3 3 (:REWRITE FOLD-CONSTS-IN-*))
                        (1 1
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::IFACT-CORRECT (28 4 (:DEFINITION M1::FACT))
                   (14 8 (:REWRITE DEFAULT-*-2))
                   (10 8 (:REWRITE DEFAULT-*-1))
                   (4 4 (:REWRITE ZP-OPEN))
                   (4 4 (:REWRITE DEFAULT-+-2))
                   (4 4 (:REWRITE DEFAULT-+-1))
                   (1 1 (:REWRITE NATP-RW)))
(M1::IFACT-CORRECT-COROLLARY-1 (14 2 (:DEFINITION M1::FACT))
                               (4 2 (:REWRITE DEFAULT-*-2))
                               (2 2 (:TYPE-PRESCRIPTION M1::FACT))
                               (2 2 (:REWRITE ZP-OPEN))
                               (2 2 (:REWRITE DEFAULT-+-2))
                               (2 2 (:REWRITE DEFAULT-+-1))
                               (2 2 (:REWRITE DEFAULT-*-1))
                               (1 1 (:REWRITE NATP-RW)))
(M1::IFACT-CORRECT-COROLLARY-2 (21 3 (:DEFINITION M1::FACT))
                               (6 3 (:REWRITE DEFAULT-*-2))
                               (3 3 (:REWRITE ZP-OPEN))
                               (3 3 (:REWRITE DEFAULT-+-2))
                               (3 3 (:REWRITE DEFAULT-+-1))
                               (3 3 (:REWRITE DEFAULT-*-1))
                               (1 1 (:REWRITE NATP-RW)))
(M1::IFACT-CORRECT-COROLLARY-3 (21 3 (:DEFINITION M1::FACT))
                               (6 3 (:REWRITE DEFAULT-*-2))
                               (3 3 (:REWRITE ZP-OPEN))
                               (3 3 (:REWRITE DEFAULT-+-2))
                               (3 3 (:REWRITE DEFAULT-+-1))
                               (3 3 (:REWRITE DEFAULT-*-1))
                               (1 1 (:REWRITE NATP-RW)))
(M1::N)
(M1::A)
(M1::IFACT-INV)
(M1::|IFACT-INV-arity-1-defpun-test|)
(M1::|IFACT-INV-arity-1-defpun-base|)
(M1::|IFACT-INV-arity-1-step| (1 1 (:TYPE-PRESCRIPTION M1::STEP)))
(M1::|IFACT-INV-arity-1-defpun-stn|
     (4 4
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::|IFACT-INV-arity-1-defpun-fn|
     (5 5
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(M1::|IFACT-INV-arity-1|
     (1 1
        (:TYPE-PRESCRIPTION M1::|IFACT-INV-arity-1-defpun-stn|)))
(M1::|IFACT-INV-arity-1-DEF|)
(M1::IFACT-INV)
(M1::IFACT-INV-DEF (118 118 (:META CANCEL_TIMES-EQUAL-CORRECT))
                   (118 118 (:META CANCEL_PLUS-EQUAL-CORRECT))
                   (101 101 (:REWRITE NATP-RW))
                   (94 94 (:REWRITE DEFAULT-CAR))
                   (86 10 (:DEFINITION M1::FACT))
                   (40 40 (:REWRITE DEFAULT-CDR))
                   (36 12 (:REWRITE ZP-OPEN))
                   (30 17 (:REWRITE DEFAULT-*-2))
                   (21 17 (:REWRITE DEFAULT-*-1))
                   (18 18 (:REWRITE DEFAULT-<-2))
                   (18 18 (:REWRITE DEFAULT-<-1))
                   (18 18 (:META CANCEL_PLUS-LESSP-CORRECT))
                   (12 12 (:REWRITE DEFAULT-+-2))
                   (12 12 (:REWRITE DEFAULT-+-1))
                   (12 3 (:LINEAR X*Y>1-POSITIVE)))
(M1::IFACT-INV$DEF (1 1 (:TYPE-PRESCRIPTION M1::STEP)))
(M1::IFACT-INV-OPENER (138 17 (:REWRITE M1::STEP-OPENER))
                      (134 23 (:DEFINITION NTH))
                      (121 11 (:DEFINITION M1::NEXT-INST))
                      (69 17 (:REWRITE ZP-OPEN))
                      (50 6 (:DEFINITION M1::FACT))
                      (35 35 (:META CANCEL_TIMES-EQUAL-CORRECT))
                      (35 35 (:META CANCEL_PLUS-EQUAL-CORRECT))
                      (24 8 (:DEFINITION M1::N))
                      (23 23 (:REWRITE DEFAULT-CAR))
                      (20 4 (:DEFINITION M1::A))
                      (17 17 (:REWRITE DEFAULT-+-2))
                      (17 17 (:REWRITE DEFAULT-+-1))
                      (16 4 (:REWRITE M1::NTH-ADD1!))
                      (15 15 (:REWRITE DEFAULT-CDR))
                      (15 15 (:REWRITE DEFAULT-<-2))
                      (15 15 (:REWRITE DEFAULT-<-1))
                      (15 15 (:META CANCEL_PLUS-LESSP-CORRECT))
                      (14 14 (:TYPE-PRESCRIPTION M1::FACT))
                      (14 8 (:REWRITE DEFAULT-*-2))
                      (10 8 (:REWRITE DEFAULT-*-1))
                      (8 8 (:REWRITE NATP-RW)))
(M1::IFACT-INV-STEP (56 31 (:REWRITE DEFAULT-*-2))
                    (48 18 (:REWRITE ZP-OPEN))
                    (42 42 (:REWRITE DEFAULT-CAR))
                    (39 39 (:META CANCEL_TIMES-EQUAL-CORRECT))
                    (39 39 (:META CANCEL_PLUS-EQUAL-CORRECT))
                    (38 31 (:REWRITE DEFAULT-*-1))
                    (30 5 (:LINEAR X*Y>1-POSITIVE))
                    (29 26 (:REWRITE DEFAULT-<-2))
                    (28 28 (:META CANCEL_PLUS-LESSP-CORRECT))
                    (26 26 (:REWRITE DEFAULT-CDR))
                    (26 26 (:REWRITE DEFAULT-<-1))
                    (23 23 (:REWRITE DEFAULT-+-2))
                    (23 23 (:REWRITE DEFAULT-+-1))
                    (17 17
                        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                    (14 14 (:REWRITE NATP-RW))
                    (8 2 (:REWRITE <-0-+-NEGATIVE-1))
                    (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                    (4 4 (:REWRITE FOLD-CONSTS-IN-*)))
(M1::IFACT-INV-RUN (36 3 (:REWRITE M1::STEP-OPENER))
                   (33 3 (:DEFINITION M1::NEXT-INST))
                   (30 3 (:DEFINITION NTH))
                   (15 3 (:REWRITE ZP-OPEN))
                   (9 9 (:REWRITE M1::IFACT-INV-OPENER))
                   (5 5 (:REWRITE DEFAULT-CDR))
                   (3 3 (:REWRITE DEFAULT-CAR))
                   (3 3 (:REWRITE DEFAULT-<-2))
                   (3 3 (:REWRITE DEFAULT-<-1))
                   (3 3 (:REWRITE DEFAULT-+-2))
                   (3 3 (:REWRITE DEFAULT-+-1))
                   (3 3 (:META CANCEL_PLUS-LESSP-CORRECT)))
(M1::PARTIAL-CORRECTNESS-OF-PROGRAM-IFACT
     (22 2 (:DEFINITION M1::FACT))
     (21 3 (:DEFINITION M1::RUN))
     (15 3 (:REWRITE M1::STEP-OPENER))
     (10 2 (:REWRITE ZP-OPEN))
     (7 7 (:REWRITE DEFAULT-CAR))
     (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (6 6 (:DEFINITION M1::NEXT-INST))
     (6 3 (:DEFINITION M1::DO-INST))
     (4 2 (:REWRITE M1::IFACT-INV-OPENER))
     (4 2 (:REWRITE DEFAULT-*-2))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:DEFINITION M1::EXECUTE-PUSH))
     (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2 2 (:REWRITE NATP-RW))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 2 (:META CANCEL_PLUS-LESSP-CORRECT)))
(M1::PARTIAL-CORRECTNESS-OF-PROGRAM-IFACT-CORROLLARY
     (49 7 (:DEFINITION M1::RUN))
     (35 7 (:REWRITE M1::STEP-OPENER))
     (28 4 (:DEFINITION M1::FACT))
     (20 20 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (20 20 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (14 14 (:DEFINITION M1::NEXT-INST))
     (14 7 (:DEFINITION M1::DO-INST))
     (8 4 (:REWRITE DEFAULT-*-2))
     (7 7 (:REWRITE DEFAULT-CDR))
     (7 7 (:DEFINITION M1::EXECUTE-PUSH))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE DEFAULT-*-1))
     (3 3 (:REWRITE NATP-RW))
     (3 3 (:REWRITE DEFAULT-CAR)))
(M1::M1-BOYER-MOORE-LOOP-SCHED (1141 513 (:REWRITE DEFAULT-+-2))
                               (720 120 (:REWRITE COERCE-LEMMA))
                               (701 513 (:REWRITE DEFAULT-+-1))
                               (479 127 (:REWRITE LENS-DIFFER))
                               (260 10 (:REWRITE DEFAULT-CHAR-CODE))
                               (239 155 (:REWRITE DEFAULT-CDR))
                               (208 94 (:REWRITE DEFAULT-<-1))
                               (201 28 (:REWRITE DEFAULT-CAR))
                               (196 14 (:DEFINITION NTHCDR))
                               (157 8 (:REWRITE CONSP-NTHCDR))
                               (137 94 (:REWRITE DEFAULT-<-2))
                               (127 127 (:META CANCEL_TIMES-EQUAL-CORRECT))
                               (127 127 (:META CANCEL_PLUS-EQUAL-CORRECT))
                               (109 67 (:REWRITE DEFAULT-UNARY-MINUS))
                               (98 98 (:REWRITE DEFAULT-COERCE-2))
                               (98 98 (:REWRITE DEFAULT-COERCE-1))
                               (36 4 (:REWRITE O-P-O-INFP-CAR))
                               (24 4 (:REWRITE O-P-DEF-O-FINP-1))
                               (18 18
                                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                               (14 14 (:REWRITE ZP-OPEN))
                               (8 8 (:TYPE-PRESCRIPTION O-FINP))
                               (4 4 (:TYPE-PRESCRIPTION NATP))
                               (4 4 (:REWRITE NATP-RW))
                               (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(M1::M1-BOYER-MOORE-SCHED)
(M1::M1-BOYER-MOORE-LOOP-VARS (1141 513 (:REWRITE DEFAULT-+-2))
                              (720 120 (:REWRITE COERCE-LEMMA))
                              (701 513 (:REWRITE DEFAULT-+-1))
                              (479 127 (:REWRITE LENS-DIFFER))
                              (260 10 (:REWRITE DEFAULT-CHAR-CODE))
                              (239 155 (:REWRITE DEFAULT-CDR))
                              (208 94 (:REWRITE DEFAULT-<-1))
                              (201 28 (:REWRITE DEFAULT-CAR))
                              (196 14 (:DEFINITION NTHCDR))
                              (157 8 (:REWRITE CONSP-NTHCDR))
                              (137 94 (:REWRITE DEFAULT-<-2))
                              (127 127 (:META CANCEL_TIMES-EQUAL-CORRECT))
                              (127 127 (:META CANCEL_PLUS-EQUAL-CORRECT))
                              (109 67 (:REWRITE DEFAULT-UNARY-MINUS))
                              (98 98 (:REWRITE DEFAULT-COERCE-2))
                              (98 98 (:REWRITE DEFAULT-COERCE-1))
                              (36 4 (:REWRITE O-P-O-INFP-CAR))
                              (24 4 (:REWRITE O-P-DEF-O-FINP-1))
                              (18 18
                                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                              (14 14 (:REWRITE ZP-OPEN))
                              (8 8 (:TYPE-PRESCRIPTION O-FINP))
                              (4 4 (:TYPE-PRESCRIPTION NATP))
                              (4 4 (:REWRITE NATP-RW))
                              (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(M1::M1-BOYER-MOORE-LOOP-IS-FAST-LOOP
     (40983 3818 (:DEFINITION LEN))
     (32736 5456 (:REWRITE COERCE-LEMMA))
     (21439 2159 (:REWRITE DEFAULT-CAR))
     (20234 11219 (:REWRITE DEFAULT-+-2))
     (19259 5711 (:REWRITE LENS-DIFFER))
     (17657 5997 (:REWRITE DEFAULT-CDR))
     (15373 534 (:REWRITE CONSP-NTHCDR))
     (11957 11219 (:REWRITE DEFAULT-+-1))
     (10582 595 (:REWRITE DEFAULT-CHAR-CODE))
     (9546 2229 (:REWRITE ZP-OPEN))
     (9536 298 (:DEFINITION SETUP-DELTA))
     (8002 77 (:REWRITE FAST-LOOP-IS-CORRECT-LOOP))
     (5708 5708 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (5708 5708 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (5634 3387 (:REWRITE DEFAULT-<-2))
     (5284 303 (:DEFINITION SETUP-DELTA1-ROW))
     (4573 3387 (:REWRITE DEFAULT-<-1))
     (4461 4461 (:REWRITE DEFAULT-COERCE-2))
     (4461 4461 (:REWRITE DEFAULT-COERCE-1))
     (4408 214 (:REWRITE NATP-RW))
     (3239 19 (:DEFINITION M1::RUN))
     (2611 107 (:REWRITE CONSP-NTHCDR-2))
     (639 57 (:REWRITE O-P-O-INFP-CAR))
     (468 57 (:REWRITE O-P-DEF-O-FINP-1))
     (432 24 (:REWRITE NATP-POSP--1))
     (321 321 (:TYPE-PRESCRIPTION NATP))
     (286 286
          (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-VARS))
     (216 24 (:REWRITE NATP-POSP))
     (179 170 (:REWRITE DEFAULT-UNARY-MINUS))
     (114 114 (:TYPE-PRESCRIPTION O-FINP))
     (96 24 (:REWRITE POSP-RW))
     (96 24 (:DEFINITION POSP))
     (52 13
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (40 40 (:REWRITE CHARACTER-LISTP-COERCE))
     (38 38
         (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-SCHED))
     (24 24 (:REWRITE O-INFP->NEQ-0))
     (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (21 7 (:REWRITE DEFAULT-CODE-CHAR))
     (13 13
         (:REWRITE MINUS-CANCELLATION-ON-RIGHT)))
(M1::M1-BOYER-MOORE-IS-FAST
     (8930 5
           (:DEFINITION M1::M1-BOYER-MOORE-LOOP-SCHED))
     (3099 6
           (:DEFINITION M1::M1-BOYER-MOORE-LOOP-VARS))
     (2654 1555 (:REWRITE DEFAULT-+-2))
     (2379 53 (:DEFINITION CHAR))
     (1772 1555 (:REWRITE DEFAULT-+-1))
     (1520 190 (:REWRITE ZP-OPEN))
     (1499 45
           (:REWRITE CHARACTERP-CAR-NTHCDR-COERCE))
     (1490 315 (:REWRITE COERCE-LEMMA))
     (1425 298 (:REWRITE DEFAULT-CDR))
     (1368 209 (:REWRITE DEFAULT-CAR))
     (1214 34 (:REWRITE DEFAULT-CHAR-CODE))
     (1010 1010 (:TYPE-PRESCRIPTION LEN))
     (1008 261 (:REWRITE LENS-DIFFER))
     (995 127 (:DEFINITION LEN))
     (969 323 (:TYPE-PRESCRIPTION INTEGERP-DELTA))
     (952 43 (:REWRITE CONSP-NTHCDR))
     (808 375 (:REWRITE FOLD-CONSTS-IN-+))
     (807 565
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (760 190 (:REWRITE <-0-+-NEGATIVE-1))
     (720 687 (:META CANCEL_PLUS-LESSP-CORRECT))
     (535 408 (:REWRITE DEFAULT-<-1))
     (521 408 (:REWRITE DEFAULT-<-2))
     (510 11 (:REWRITE EQUAL-CHAR-CODES))
     (315 45 (:DEFINITION NFIX))
     (261 261 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (261 261 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (235 56 (:REWRITE <-+-NEGATIVE-0-1))
     (198 198 (:REWRITE DEFAULT-COERCE-2))
     (198 198 (:REWRITE DEFAULT-COERCE-1))
     (192 9 (:REWRITE EARLY-TERMINATION))
     (190 32 (:LINEAR DELTA-VERY-POSITIVE))
     (132 11 (:REWRITE ASSOCIATIVITY-OF-+))
     (48 8 (:REWRITE O-P-O-INFP-CAR))
     (45 45 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (45 45 (:REWRITE CHARACTER-LISTP-COERCE))
     (24 8 (:REWRITE O-P-DEF-O-FINP-1))
     (22 22
         (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-VARS))
     (22 1 (:DEFINITION M1::RUN))
     (16 16 (:TYPE-PRESCRIPTION O-FINP))
     (4 2 (:REWRITE LEN-0))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 1 (:REWRITE O-INFP->NEQ-0))
     (2 2
        (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-SCHED))
     (2 2 (:DEFINITION ATOM)))
(M1::M1-BOYER-MOORE-HALTS
     (14145 917 (:REWRITE DEFAULT-CAR))
     (13160 420
            (:REWRITE CHARACTERP-CAR-NTHCDR-COERCE))
     (12629 1368 (:DEFINITION LEN))
     (11729 361 (:REWRITE DEFAULT-CHAR-CODE))
     (11061 534 (:REWRITE CONSP-NTHCDR))
     (9242 1513 (:REWRITE LENS-DIFFER))
     (8930 5
           (:DEFINITION M1::M1-BOYER-MOORE-LOOP-SCHED))
     (8896 8896 (:TYPE-PRESCRIPTION LEN))
     (7932 2007 (:REWRITE COERCE-LEMMA))
     (7049 4127 (:REWRITE DEFAULT-+-2))
     (5896 1943 (:REWRITE DEFAULT-CDR))
     (4794 4127 (:REWRITE DEFAULT-+-1))
     (3727 2692 (:REWRITE DEFAULT-<-2))
     (3644 2692 (:REWRITE DEFAULT-<-1))
     (3558 86 (:REWRITE EQUAL-CHAR-CODES))
     (3149 397 (:REWRITE ZP-OPEN))
     (2940 420 (:DEFINITION NFIX))
     (2665 1041 (:REWRITE FOLD-CONSTS-IN-+))
     (1771 168 (:LINEAR DELTA-VERY-POSITIVE))
     (1707 220 (:REWRITE O-P-O-INFP-CAR))
     (1644 548 (:TYPE-PRESCRIPTION INTEGERP-DELTA))
     (1588 397 (:REWRITE <-0-+-NEGATIVE-1))
     (1513 1513 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (1513 1513 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (1107 62 (:REWRITE EARLY-TERMINATION))
     (1047 220 (:REWRITE O-P-DEF-O-FINP-1))
     (1032 86 (:REWRITE ASSOCIATIVITY-OF-+))
     (820 820 (:REWRITE DEFAULT-COERCE-2))
     (820 820 (:REWRITE DEFAULT-COERCE-1))
     (440 440 (:TYPE-PRESCRIPTION O-FINP))
     (330 330
          (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-VARS))
     (225 225 (:REWRITE CHARACTER-LISTP-COERCE))
     (22 1 (:DEFINITION M1::RUN))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-SCHED)))
(M1::M1-BOYER-MOORE-IS-CORRECT
     (8930 5
           (:DEFINITION M1::M1-BOYER-MOORE-LOOP-SCHED))
     (3099 6
           (:DEFINITION M1::M1-BOYER-MOORE-LOOP-VARS))
     (2654 1555 (:REWRITE DEFAULT-+-2))
     (2379 53 (:DEFINITION CHAR))
     (1772 1555 (:REWRITE DEFAULT-+-1))
     (1520 190 (:REWRITE ZP-OPEN))
     (1499 45
           (:REWRITE CHARACTERP-CAR-NTHCDR-COERCE))
     (1490 315 (:REWRITE COERCE-LEMMA))
     (1425 298 (:REWRITE DEFAULT-CDR))
     (1368 209 (:REWRITE DEFAULT-CAR))
     (1214 34 (:REWRITE DEFAULT-CHAR-CODE))
     (1010 1010 (:TYPE-PRESCRIPTION LEN))
     (1008 261 (:REWRITE LENS-DIFFER))
     (995 127 (:DEFINITION LEN))
     (969 323 (:TYPE-PRESCRIPTION INTEGERP-DELTA))
     (952 43 (:REWRITE CONSP-NTHCDR))
     (808 375 (:REWRITE FOLD-CONSTS-IN-+))
     (807 565
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (760 190 (:REWRITE <-0-+-NEGATIVE-1))
     (720 687 (:META CANCEL_PLUS-LESSP-CORRECT))
     (535 408 (:REWRITE DEFAULT-<-1))
     (521 408 (:REWRITE DEFAULT-<-2))
     (510 11 (:REWRITE EQUAL-CHAR-CODES))
     (315 45 (:DEFINITION NFIX))
     (261 261 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (261 261 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (235 56 (:REWRITE <-+-NEGATIVE-0-1))
     (198 198 (:REWRITE DEFAULT-COERCE-2))
     (198 198 (:REWRITE DEFAULT-COERCE-1))
     (192 9 (:REWRITE EARLY-TERMINATION))
     (190 32 (:LINEAR DELTA-VERY-POSITIVE))
     (132 11 (:REWRITE ASSOCIATIVITY-OF-+))
     (48 8 (:REWRITE O-P-O-INFP-CAR))
     (45 45 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (45 45 (:REWRITE CHARACTER-LISTP-COERCE))
     (24 8 (:REWRITE O-P-DEF-O-FINP-1))
     (22 22
         (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-VARS))
     (22 1 (:DEFINITION M1::RUN))
     (16 16 (:TYPE-PRESCRIPTION O-FINP))
     (4 2 (:REWRITE LEN-0))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 1 (:REWRITE O-INFP->NEQ-0))
     (2 2
        (:TYPE-PRESCRIPTION M1::M1-BOYER-MOORE-LOOP-SCHED))
     (2 2 (:DEFINITION ATOM)))
(M1::UNIVERSAL-SCHED-LOOP (1 1
                             (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::UNIVERSAL-SCHED)
(M1::INDUCT-HINT (4 4
                    (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::UNIVERSAL-ALGORITHM (4 4
                            (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::STEP-A-RUN-UNIVERSAL-LOOP
     (84 6 (:REWRITE LENS-DIFFER))
     (42 42 (:TYPE-PRESCRIPTION LEN))
     (36 6 (:DEFINITION LEN))
     (27 21 (:REWRITE DEFAULT-+-2))
     (21 21 (:REWRITE DEFAULT-+-1))
     (13 10 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE NATP-RW))
     (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (5 5 (:REWRITE ZP-OPEN))
     (1 1
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(M1::STEP-A-RUN-UNIVERSAL (14 1
                              (:DEFINITION M1::UNIVERSAL-SCHED-LOOP))
                          (10 4 (:DEFINITION BINARY-APPEND))
                          (8 2 (:DEFINITION M1::UNIVERSAL-ALGORITHM))
                          (6 6 (:REWRITE DEFAULT-+-2))
                          (6 6 (:REWRITE DEFAULT-+-1))
                          (3 3 (:REWRITE ZP-OPEN))
                          (1 1 (:REWRITE NATP-RW)))
(M1::STEP-B (18 3 (:REWRITE LENS-DIFFER))
            (11 11 (:REWRITE DEFAULT-+-2))
            (11 11 (:REWRITE DEFAULT-+-1))
            (9 6 (:DEFINITION LEN))
            (6 6 (:TYPE-PRESCRIPTION LEN))
            (6 6 (:REWRITE NATP-RW))
            (3 3 (:REWRITE ZP-OPEN))
            (3 3 (:REWRITE EQUAL-CONSTANT-+))
            (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
            (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(M1::NEW-FACT-SCHED)
(M1::UNIVERSAL-COMPUTES-FACT (39 1
                                 (:DEFINITION M1::UNIVERSAL-SCHED-LOOP))
                             (35 5 (:DEFINITION M1::FACT))
                             (34 4 (:DEFINITION BINARY-APPEND))
                             (16 11 (:REWRITE DEFAULT-+-2))
                             (12 11 (:REWRITE DEFAULT-+-1))
                             (10 5 (:REWRITE DEFAULT-*-2))
                             (5 5 (:REWRITE ZP-OPEN))
                             (5 5 (:REWRITE DEFAULT-*-1)))
(M1::UNIVERSAL-NEVER-HALTS-LEMMA
     (3533 316 (:REWRITE LENS-DIFFER))
     (1960 1960 (:TYPE-PRESCRIPTION LEN))
     (1917 51 (:REWRITE NTH-IS-CAR-NTHCDR))
     (1542 292 (:DEFINITION LEN))
     (1260 51 (:REWRITE DEFAULT-CAR))
     (813 51 (:REWRITE CONSP-NTHCDR-2))
     (734 418 (:REWRITE DEFAULT-+-2))
     (683 683 (:TYPE-PRESCRIPTION M1::STEP))
     (672 357
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (606 51 (:DEFINITION NTHCDR))
     (594 51 (:REWRITE O-P-O-INFP-CAR))
     (442 418 (:REWRITE DEFAULT-+-1))
     (441 51 (:REWRITE O-P-DEF-O-FINP-1))
     (361 349 (:REWRITE DEFAULT-CDR))
     (316 316 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (316 316 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (315 315 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (255 51 (:REWRITE ZP-OPEN))
     (216 108 (:REWRITE LEN-0))
     (204 51 (:REWRITE CONSP-NTHCDR))
     (204 51 (:DEFINITION NFIX))
     (198 153 (:REWRITE DEFAULT-<-2))
     (186 186 (:TYPE-PRESCRIPTION O-FINP))
     (168 28 (:REWRITE O-INFP->NEQ-0))
     (153 153 (:REWRITE DEFAULT-<-1))
     (153 153 (:META CANCEL_PLUS-LESSP-CORRECT))
     (108 108 (:DEFINITION ATOM))
     (102 102 (:TYPE-PRESCRIPTION NATP))
     (84 28 (:REWRITE O-FIRST-EXPT-O-INFP))
     (56 28 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (51 51 (:REWRITE NATP-RW))
     (48 48
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(M1::UNIVERSAL-NEVER-HALTS (15 1 (:DEFINITION M1::RUN))
                           (13 1 (:REWRITE M1::STEP-OPENER))
                           (6 2 (:DEFINITION M1::NEXT-INST))
                           (6 1 (:DEFINITION M1::DO-INST))
                           (5 1 (:DEFINITION M1::EXECUTE-PUSH))
                           (1 1 (:REWRITE DEFAULT-CDR)))