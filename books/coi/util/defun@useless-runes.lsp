(DEFUN::TRUE-LISTP-APPEND-REWRITE)
(DEFUN::LOCAL-SUFFIX)
(DEFUN::SYMBOLP-SUFFIX)
(DEFUN::CONTAINS-NIL-ALISTP (2 2 (:REWRITE DEFAULT-CAR))
                            (1 1 (:REWRITE DEFAULT-CDR)))
(DEFUN::CONTAINS-NIL)
(DEFUN::DEFUN-FN
     (8800 352
           (:DEFINITION DEFUN::EXTRACT-KEY-FROM-XARG-DECLS-REC))
     (6688 352
           (:DEFINITION DEFUN::EXTRACT-KEY-FROM-XARG-BODIES))
     (5822 5770 (:REWRITE DEFAULT-CDR))
     (3168 352
           (:DEFINITION DEFUN::EXTRACT-XARG-KEY-FROM-BODY-REC))
     (3004 2956 (:REWRITE DEFAULT-CAR))
     (1892 86
           (:DEFINITION DEFUN::GET-XARG-KEYS-FROM-BODY))
     (876 438 (:DEFINITION DEFUN::XARG-P))
     (876 438 (:DEFINITION DEFUN::XARG-BODY))
     (774 86
          (:DEFINITION DEFUN::GET-XARG-KEY-FROM-BODY))
     (600 48
          (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (456 96 (:REWRITE DEFAULT-COERCE-3))
     (408 204 (:REWRITE DEFAULT-COERCE-1))
     (384 12 (:DEFINITION DEFUN::PREFIX-LIST))
     (300 300 (:REWRITE DEFAULT-COERCE-2))
     (300 48
          (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (200 40 (:DEFINITION TRUE-LIST-LISTP))
     (200 40 (:DEFINITION LEN))
     (172 172
          (:TYPE-PRESCRIPTION DEFUN::GET-XARG-KEYS-FROM-BODY))
     (172 172
          (:TYPE-PRESCRIPTION DEFUN::GET-XARG-KEY-FROM-BODY))
     (150 30 (:DEFINITION MEMBER-EQUAL))
     (132 36
          (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (112 7
          (:DEFINITION DEFUN::GET-TYPE-DECLARATIONS-FROM-DECLS))
     (96 96
         (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (81 17 (:DEFINITION DEFUN::CONTAINS-NIL))
     (80 40 (:REWRITE DEFAULT-<-2))
     (80 40 (:REWRITE DEFAULT-+-2))
     (72 36 (:REWRITE DEFAULT-PKG-IMPORTS))
     (42 7
         (:DEFINITION DEFUN::GET-TYPE-DECLARATIONS-FROM-BODY))
     (40 40 (:REWRITE DEFAULT-<-1))
     (40 40 (:REWRITE DEFAULT-+-1))
     (36 36
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (14 14
         (:TYPE-PRESCRIPTION DEFUN::GET-TYPE-DECLARATIONS-FROM-BODY))
     (14 7
         (:DEFINITION DEFUN::TYPE-DECLARATION)))
(DEFUN::DEFUN-FN-WRAPPER)
(DEFUN::SIGNATURE-FN)
(DEFUN::EXTRACT-HINTS)
(DEFUN::ZED)
(DEFUN::INTEGERP-STRINGP-IMPLIES-INTEGERP-STRINGP-ZED
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1)))
(DEFUN::ZED)
(DEFUN::FRED)
(DEFUN::ZED)
(DEFUN::FRED-STRINGP-IMPLIES-FRED-STRINGP-ZED (6 6 (:REWRITE DEFAULT-+-2))
                                              (6 6 (:REWRITE DEFAULT-+-1)))
(DEFUN::ZED)
(DEFUN::EQUIV1)
(DEFUN::EQUIV2)
(DEFUN::EQUIV1-IS-AN-EQUIVALENCE)
(DEFUN::EQUIV2-IS-AN-EQUIVALENCE)
(DEFUN::FOO (10 5 (:REWRITE DEFAULT-+-2))
            (6 6 (:REWRITE DEFAULT-CDR))
            (5 5 (:REWRITE DEFAULT-+-1))
            (2 1 (:REWRITE DEFAULT-<-2))
            (2 1 (:REWRITE DEFAULT-<-1)))
(DEFUN::FOO-INDUCTION (10 5 (:REWRITE DEFAULT-+-2))
                      (6 6 (:REWRITE DEFAULT-CDR))
                      (5 5 (:REWRITE DEFAULT-+-1))
                      (2 1 (:REWRITE DEFAULT-<-2))
                      (2 1 (:REWRITE DEFAULT-<-1)))
(DEFUN::FOO-INDUCTION-TO-FOO)
(DEFUN::EQUIV1-1-IMPLIES-EQUIV2-FOO)
(DEFUN::EQUIV2-2-IMPLIES-EQUIV1-FOO)
(DEFUN::NFIXEQUIV)
(DEFUN::IFIXEQUIV)
(DEFUN::NFIXEQUIV-IS-AN-EQUIVALENCE)
(DEFUN::IFIXEQUIV-IS-AN-EQUIVALENCE)
(DEFUN::GOO)
(DEFUN::IFIXEQUIV-1-IMPLIES-IFIXEQUIV-GOO (8 8 (:REWRITE DEFAULT-<-2))
                                          (8 8 (:REWRITE DEFAULT-<-1)))
(DEFUN::IFIXEQUIV-2-IMPLIES-NFIXEQUIV-GOO (16 16 (:REWRITE DEFAULT-<-2))
                                          (16 16 (:REWRITE DEFAULT-<-1)))
(DEFUN::NFIXEQUIV-3-IMPLIES-IFIXEQUIV-GOO (10 10 (:REWRITE DEFAULT-<-2))
                                          (10 10 (:REWRITE DEFAULT-<-1)))
(DEFUN::NFIXEQUIV-4-IMPLIES-NFIXEQUIV-GOO (12 12 (:REWRITE DEFAULT-<-2))
                                          (12 12 (:REWRITE DEFAULT-<-1)))
(DEFUN::IFIXEQUIV-0-IMPLIES-IFIXEQUIV-GOO (8 8 (:REWRITE DEFAULT-<-2))
                                          (8 8 (:REWRITE DEFAULT-<-1)))
(DEFUN::IFIXEQUIV-1-IMPLIES-NFIXEQUIV-GOO (16 16 (:REWRITE DEFAULT-<-2))
                                          (16 16 (:REWRITE DEFAULT-<-1)))
(DEFUN::NFIXEQUIV-2-IMPLIES-IFIXEQUIV-GOO (10 10 (:REWRITE DEFAULT-<-2))
                                          (10 10 (:REWRITE DEFAULT-<-1)))
(DEFUN::NFIXEQUIV-3-IMPLIES-NFIXEQUIV-GOO (12 12 (:REWRITE DEFAULT-<-2))
                                          (12 12 (:REWRITE DEFAULT-<-1)))
(DEFUN::NFIXEQUIV-0-IMPLIES-IFIXEQUIV-GOO (10 10 (:REWRITE DEFAULT-<-2))
                                          (10 10 (:REWRITE DEFAULT-<-1)))
(DEFUN::INTEGERP-T-IMPLIES-T-NATP-GOO (2 2 (:REWRITE DEFAULT-<-2))
                                      (2 2 (:REWRITE DEFAULT-<-1)))