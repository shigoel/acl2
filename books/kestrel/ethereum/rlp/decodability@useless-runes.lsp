(ETHEREUM::RLP-ENCODE-BYTES-INJECTIVE-LEMMA
     (1577 81 (:REWRITE DEFAULT-<-1))
     (960 48
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (936 48
          (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
     (912 96
          (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
     (792 24 (:DEFINITION ACL2-NUMBER-LISTP))
     (672 48 (:DEFINITION RATIONAL-LISTP))
     (650 650
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 2))
     (650 650
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 1))
     (610 307 (:REWRITE DEFAULT-+-2))
     (606 344 (:REWRITE DEFAULT-CDR))
     (584 24 (:DEFINITION BINARY-APPEND))
     (336 336 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (313 145 (:REWRITE DEFAULT-CAR))
     (311 307 (:REWRITE DEFAULT-+-1))
     (285 11 (:REWRITE SUBSETP-OF-CONS))
     (268 48 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (246 82
          (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST64P-REWRITE))
     (246 82
          (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
     (246 82
          (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST20P-REWRITE))
     (240 96
          (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
     (194 17 (:DEFINITION MEMBER-EQUAL))
     (168 168
          (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (164 164 (:TYPE-PRESCRIPTION BYTE-LIST64P))
     (164 164 (:TYPE-PRESCRIPTION BYTE-LIST32P))
     (164 164 (:TYPE-PRESCRIPTION BYTE-LIST20P))
     (154 154
          (:REWRITE CONSP-OF-NAT=>BEBYTES*-IFF-NOT-ZP))
     (144 48
          (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
     (144 4 (:REWRITE SUBSETP-APPEND1))
     (132 36
          (:REWRITE BYTEP-WHEN-MEMBER-EQUAL-OF-BYTE-LISTP))
     (126 126 (:LINEAR LEN-WHEN-PREFIXP))
     (124 52 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
     (116 68 (:REWRITE SUBSETP-TRANS2))
     (96 48
         (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
     (94 94 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (88 48 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
     (81 81 (:REWRITE DEFAULT-<-2))
     (76 22 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (70 22 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (68 68 (:REWRITE SUBSETP-TRANS))
     (48 24
         (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
     (34 34 (:REWRITE SUBSETP-MEMBER . 2))
     (34 34 (:REWRITE SUBSETP-MEMBER . 1))
     (34 34
         (:REWRITE NAT=>BEBYTES*-OF-NFIX-NAT-NORMALIZE-CONST))
     (26 2 (:DEFINITION TRUE-LISTP))
     (24 16
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (24 4
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (4 4
        (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
     (4 4
        (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
     (4 4
        (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
     (4 4 (:REWRITE SET::IN-SET))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+)))
(ETHEREUM::RLP-ENCODE-BYTES-INJECTIVE)
(ETHEREUM::TREE
 (9 3 (:REWRITE DEFAULT-<-2))
 (9 3 (:REWRITE DEFAULT-<-1))
 (8
  8
  (:REWRITE
       ETHEREUM::RLP-TREE-LIST-COUNT-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST))
 (4 4
    (:REWRITE ETHEREUM::RLP-TREE-COUNT-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (4 4
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 2))
 (4 4
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 1))
 (2 2
    (:REWRITE
         ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (2
  2
  (:REWRITE
   ETHEREUM::RLP-TREE-BRANCH->SUBTREES$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2
  2
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV))
 (2
  2
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV)))
(ETHEREUM::DOUBLE-TREE-INDUCTION-FLAG
 (9 3 (:REWRITE DEFAULT-<-2))
 (9 3 (:REWRITE DEFAULT-<-1))
 (8
  8
  (:REWRITE
       ETHEREUM::RLP-TREE-LIST-COUNT-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST))
 (4 4
    (:REWRITE ETHEREUM::RLP-TREE-COUNT-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (4 4
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 2))
 (4 4
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 1))
 (2 2
    (:REWRITE
         ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (2
  2
  (:REWRITE
   ETHEREUM::RLP-TREE-BRANCH->SUBTREES$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2
  2
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV))
 (2
  2
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV)))
(FLAG::FLAG-EQUIV-LEMMA)
(ETHEREUM::DOUBLE-TREE-INDUCTION-FLAG-EQUIVALENCES)
(ETHEREUM::HELPER-LEMMA-1
 (2356 38
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2223 38
       (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (2090 76
       (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (1995 19 (:DEFINITION ACL2-NUMBER-LISTP))
 (1889 39 (:REWRITE DEFAULT-<-2))
 (1800 9
       (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-BYTES-LOWER-BOUND-WHEN-LEN-LEN))
 (1719 39 (:REWRITE DEFAULT-<-1))
 (1634 38 (:DEFINITION RATIONAL-LISTP))
 (477 42 (:DEFINITION LEN))
 (456 76
      (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (399 157 (:REWRITE DEFAULT-CDR))
 (342 129 (:REWRITE DEFAULT-CAR))
 (266 266 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (228 38
      (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (210 84
      (:REWRITE ETHEREUM::CONSP-OF-RLP-ENCODE-TREE-LIST-WHEN-NO-ERROR))
 (165 10 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (152 38
      (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (143 143 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (134 134
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
 (134 134
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
 (133 133
      (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (120 5 (:DEFINITION BINARY-APPEND))
 (112 56 (:REWRITE DEFAULT-+-2))
 (100 5 (:DEFINITION TRUE-LISTP))
 (84 84
     (:TYPE-PRESCRIPTION ETHEREUM::RLP-TREE-BRANCH->SUBTREES$INLINE))
 (76 19
     (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (60 10
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (60 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (56 56 (:REWRITE DEFAULT-+-1))
 (48
  48
  (:REWRITE
   ETHEREUM::RLP-TREE-BRANCH->SUBTREES$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (48
  48
  (:REWRITE
   ETHEREUM::RLP-ENCODE-TREE-LIST-OF-RLP-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (44 44
     (:REWRITE
          ETHEREUM::RLP-ENCODE-BYTES-OF-BYTE-LIST-FIX-BYTES-NORMALIZE-CONST))
 (40 40
     (:REWRITE ETHEREUM::RLP-TREEP-WHEN-MEMBER-EQUAL-OF-RLP-TREE-LISTP))
 (35
  35
  (:REWRITE
    ETHEREUM::RLP-TREE-LEAF->BYTES$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (30 30
     (:REWRITE CONSP-OF-NAT=>BEBYTES*-IFF-NOT-ZP))
 (23 23
     (:REWRITE
          ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (20 20 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (20 10 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 18 (:LINEAR LEN-WHEN-PREFIXP))
 (10 10 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (10 10 (:REWRITE SET::IN-SET))
 (8 8
    (:REWRITE NAT=>BEBYTES*-OF-NFIX-NAT-NORMALIZE-CONST))
 (4
  4
  (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST)))
(ETHEREUM::EXPAND-TO-CAR-OF-APPEND
 (31 2 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (19 19 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (18 1 (:DEFINITION TRUE-LISTP))
 (14 1 (:DEFINITION BINARY-APPEND))
 (13 6 (:REWRITE DEFAULT-CAR))
 (12 2
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (8 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 2))
 (6 6
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 1))
 (6 3 (:REWRITE DEFAULT-CDR))
 (6 2
    (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2
    (:REWRITE ETHEREUM::CONSP-OF-RLP-ENCODE-TREE-LIST-WHEN-NO-ERROR))
 (3
   3
   (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST))
 (3
  3
  (:REWRITE
   ETHEREUM::RLP-ENCODE-TREE-LIST-OF-RLP-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (3
  3
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2
    (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2
    (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2
    (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (2 2 (:REWRITE SET::IN-SET))
 (1
  1
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV)))
(ETHEREUM::EXPAND-TO-TAKE-OF-APPEND
 (1411 29 (:REWRITE DEFAULT-<-1))
 (1120 19
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1101 12
       (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (1083 6 (:DEFINITION ACL2-NUMBER-LISTP))
 (1074 51
       (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (969 27 (:DEFINITION RATIONAL-LISTP))
 (956 3
      (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-TREE-LOWER-BOUND-WHEN-LEN-LEN-2))
 (956 3
      (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-TREE-LOWER-BOUND-WHEN-LEN-LEN-1))
 (324 42
      (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (227 106 (:REWRITE DEFAULT-CAR))
 (198 60
      (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (186 11 (:REWRITE TAKE-OF-LEN-FREE))
 (161 97 (:REWRITE DEFAULT-CDR))
 (146 146
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
 (146 146
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
 (84 4 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (82 4 (:DEFINITION TRUE-LISTP))
 (66 36 (:REWRITE DEFAULT-+-2))
 (62 62 (:LINEAR LEN-WHEN-PREFIXP))
 (58 8
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (51
   51
   (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST))
 (51 12
     (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (48
  48
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV))
 (42 8 (:REWRITE TAKE-WHEN-ATOM))
 (40 36 (:REWRITE DEFAULT-+-1))
 (38 29 (:REWRITE DEFAULT-<-2))
 (28 15
     (:REWRITE ETHEREUM::CONSP-OF-RLP-ENCODE-TREE-LIST-WHEN-NO-ERROR))
 (27 1 (:REWRITE LEN-OF-APPEND))
 (26 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (24 9
     (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (20 5 (:REWRITE ZP-OPEN))
 (20 2 (:REWRITE CONSP-OF-TAKE))
 (17
  17
  (:REWRITE
   ETHEREUM::RLP-ENCODE-TREE-LIST-OF-RLP-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 16
     (:TYPE-PRESCRIPTION ETHEREUM::RLP-TREE-KIND$INLINE))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (16 4 (:DEFINITION EQ))
 (14
   2
   (:LINEAR ETHEREUM::CAR-OF-RLP-ENCODE-TREE-LEAF-UPPER-BOUND-WHEN-NO-ERROR))
 (14 2
     (:LINEAR
          ETHEREUM::CAR-OF-RLP-ENCODE-TREE-BRANCH-UPPER-BOUND-WHEN-NO-ERROR))
 (12 4
     (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (8 8 (:REWRITE SET::IN-SET))
 (4 4
    (:REWRITE
         ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (4
  4
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(ETHEREUM::CAR-ENCODINGS-SAME-LEN
 (4014 52 (:REWRITE DEFAULT-<-1))
 (2646 14
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2555 14
       (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (2464 28
       (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (2359 7 (:DEFINITION ACL2-NUMBER-LISTP))
 (2276 188 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (2072 14 (:DEFINITION RATIONAL-LISTP))
 (2040 3
       (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-TREE-LOWER-BOUND-WHEN-LEN-LEN-2))
 (2040 3
       (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-TREE-LOWER-BOUND-WHEN-LEN-LEN-1))
 (1296 72 (:DEFINITION TRUE-LISTP))
 (864 144
      (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (744 8 (:DEFINITION TAKE))
 (685 188 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (596 596 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (584 240 (:REWRITE DEFAULT-CAR))
 (535 308 (:REWRITE DEFAULT-CDR))
 (486 486
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
 (486 486
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
 (476 28
      (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (446 91 (:REWRITE CONSP-OF-APPEND))
 (432 16 (:REWRITE TAKE-OF-LEN-FREE))
 (328 32 (:DEFINITION LEN))
 (316 16 (:REWRITE TAKE-OF-TOO-MANY))
 (288 288 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (288 144 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (278 143
      (:REWRITE ETHEREUM::CONSP-OF-RLP-ENCODE-TREE-LIST-WHEN-NO-ERROR))
 (262 142
      (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (238 14
      (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (227
  227
  (:REWRITE
   ETHEREUM::RLP-ENCODE-TREE-LIST-OF-RLP-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (216 8 (:REWRITE LEN-OF-APPEND))
 (192 16 (:REWRITE TAKE-WHEN-ATOM))
 (184 104 (:REWRITE DEFAULT-+-2))
 (148
   148
   (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST))
 (144 144
      (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (144 144
      (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (144 144
      (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (144 144
      (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (144 144 (:REWRITE SET::IN-SET))
 (120 104 (:REWRITE DEFAULT-+-1))
 (100
  100
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV))
 (92
  92
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV))
 (64 52 (:REWRITE DEFAULT-<-2))
 (46 46 (:LINEAR LEN-WHEN-PREFIXP))
 (40 8 (:REWRITE COMMUTATIVITY-OF-+))
 (32 8 (:REWRITE ZP-OPEN))
 (24 8 (:DEFINITION NFIX))
 (16 16 (:TYPE-PRESCRIPTION NFIX))
 (8 8
    (:REWRITE CONS-OF-BYTE-LIST-FIX-Y-NORMALIZE-CONST-UNDER-BYTE-LIST-EQUIV))
 (8 8
    (:REWRITE CONS-OF-BYTE-FIX-X-NORMALIZE-CONST-UNDER-BYTE-LIST-EQUIV))
 (8 8
    (:REWRITE CAR-OF-BYTE-LIST-FIX-X-NORMALIZE-CONST-UNDER-BYTE-EQUIV))
 (8 8
    (:REWRITE BEBYTES=>NAT-OF-BYTE-LIST-FIX-DIGITS-NORMALIZE-CONST))
 (1 1
    (:REWRITE EQUAL-OF-APPENDS-DECOMPOSE)))
(ETHEREUM::HELPER-LEMMA-2
 (1080 9 (:REWRITE DEFAULT-<-1))
 (828 9
      (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-TREE-LOWER-BOUND-WHEN-LEN-LEN-2))
 (828 9
      (:LINEAR ETHEREUM::LEN-OF-RLP-ENCODE-TREE-LOWER-BOUND-WHEN-LEN-LEN-1))
 (720 18
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (684 18
      (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (648 36
      (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (612 9 (:DEFINITION ACL2-NUMBER-LISTP))
 (504 18 (:DEFINITION RATIONAL-LISTP))
 (144 70 (:REWRITE DEFAULT-CAR))
 (144 36
      (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (126 57 (:REWRITE DEFAULT-CDR))
 (104 8 (:DEFINITION BINARY-APPEND))
 (86 86 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (79 16 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (72 18
     (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (66 66
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
 (66 66
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
 (64 16 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (54 18
     (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (48 48
     (:TYPE-PRESCRIPTION ETHEREUM::RLP-TREE-KIND$INLINE))
 (48 12 (:DEFINITION EQ))
 (42
   6
   (:LINEAR ETHEREUM::CAR-OF-RLP-ENCODE-TREE-LEAF-UPPER-BOUND-WHEN-NO-ERROR))
 (42 6
     (:LINEAR
          ETHEREUM::CAR-OF-RLP-ENCODE-TREE-BRANCH-UPPER-BOUND-WHEN-NO-ERROR))
 (29
   29
   (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST))
 (28 4 (:DEFINITION LEN))
 (27 9
     (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (20
  20
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV))
 (19
  19
  (:REWRITE
   ETHEREUM::RLP-ENCODE-TREE-LIST-OF-RLP-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (14 7
     (:REWRITE ETHEREUM::CONSP-OF-RLP-ENCODE-TREE-LIST-WHEN-NO-ERROR))
 (12 12
     (:REWRITE
          ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (12
  12
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV))
 (9 9
    (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (9 9 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 7
    (:REWRITE ETHEREUM::RETURN-TYPE-OF-RLP-ENCODE-TREE-LIST.ENCODING))
 (6 6 (:LINEAR LEN-WHEN-PREFIXP))
 (4 4 (:REWRITE DEFAULT-+-1)))
(ETHEREUM::FLAG-LEMMA-FOR-RLP-ENCODE-TREE-INJECTIVE-LEMMA
 (5401 341 (:DEFINITION BINARY-APPEND))
 (5275 455 (:DEFINITION LEN))
 (3586 682 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (3080 682 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (3024 1071
       (:REWRITE ETHEREUM::CONSP-OF-RLP-ENCODE-TREE-LIST-WHEN-NO-ERROR))
 (2671 1153 (:REWRITE DEFAULT-CDR))
 (1802 1802
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
 (1802 1802
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
 (1395 692 (:REWRITE DEFAULT-CAR))
 (1250 625 (:REWRITE DEFAULT-+-2))
 (625 625 (:REWRITE DEFAULT-+-1))
 (532 532
      (:REWRITE CONSP-OF-NAT=>BEBYTES*-IFF-NOT-ZP))
 (482 482 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (344 344
      (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (341 341
      (:REWRITE ETHEREUM::RETURN-TYPE-OF-RLP-ENCODE-TREE-LIST.ENCODING))
 (302
  302
  (:REWRITE
   ETHEREUM::CDR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-LIST-EQUIV))
 (302
  302
  (:REWRITE
   ETHEREUM::CAR-OF-RLP-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-RLP-TREE-EQUIV))
 (266 178 (:REWRITE DEFAULT-<-1))
 (242
  242
  (:REWRITE
   ETHEREUM::RLP-ENCODE-TREE-LIST-OF-RLP-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (211
  211
  (:REWRITE
   ETHEREUM::RLP-TREE-BRANCH->SUBTREES$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (178 178 (:REWRITE DEFAULT-<-2))
 (103 103
      (:REWRITE NAT=>BEBYTES*-OF-NFIX-NAT-NORMALIZE-CONST))
 (94 94
     (:REWRITE
          ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (79
   79
   (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST))
 (66
  66
  (:REWRITE
    ETHEREUM::RLP-TREE-LEAF->BYTES$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (66 66
     (:REWRITE
          ETHEREUM::RLP-ENCODE-BYTES-OF-BYTE-LIST-FIX-BYTES-NORMALIZE-CONST))
 (44 44 (:LINEAR LEN-WHEN-PREFIXP))
 (39 33 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (35 35 (:REWRITE SUBSETP-TRANS2))
 (35 35 (:REWRITE SUBSETP-TRANS))
 (28 4
     (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (6 1
    (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (3 1
    (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST64P-REWRITE))
 (3 1
    (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
 (3 1
    (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST20P-REWRITE))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION BYTE-LIST64P))
 (2 2 (:TYPE-PRESCRIPTION BYTE-LIST32P))
 (2 2 (:TYPE-PRESCRIPTION BYTE-LIST20P))
 (2 2
    (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1
    (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1
    (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE SET::IN-SET)))
(ETHEREUM::RLP-ENCODE-TREE-INJECTIVE-LEMMA)
(ETHEREUM::RLP-ENCODE-TREE-LIST-INJECTIVE-LEMMA)
(ETHEREUM::RLP-ENCODE-TREE-INJECTIVE)
(ETHEREUM::RLP-ENCODE-TREE-LIST-INJECTIVE)
(ETHEREUM::RLP-ENCODE-SCALAR-INJECTIVE
  (6 2 (:REWRITE DEFAULT-CDR))
  (6 2 (:REWRITE DEFAULT-CAR))
  (6 2
     (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST64P-REWRITE))
  (6 2
     (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
  (6 2
     (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST20P-REWRITE))
  (4 4 (:TYPE-PRESCRIPTION BYTE-LIST64P))
  (4 4 (:TYPE-PRESCRIPTION BYTE-LIST32P))
  (4 4 (:TYPE-PRESCRIPTION BYTE-LIST20P))
  (4 4
     (:REWRITE
          ETHEREUM::RLP-ENCODE-BYTES-OF-BYTE-LIST-FIX-BYTES-NORMALIZE-CONST))
  (4 4
     (:REWRITE NAT=>BEBYTES*-OF-NFIX-NAT-NORMALIZE-CONST))
  (4 4 (:REWRITE DEFAULT-<-2))
  (4 4 (:REWRITE DEFAULT-<-1)))
(ETHEREUM::LEMMA (8 4 (:REWRITE DEFAULT-+-2))
                 (5 5 (:REWRITE DEFAULT-CDR))
                 (4 4 (:REWRITE DEFAULT-+-1))
                 (4 4
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                              . 2))
                 (4 4
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                              . 1))
                 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                 (3 2 (:REWRITE DEFAULT-<-2))
                 (3 2 (:REWRITE DEFAULT-<-1)))
(ETHEREUM::RLP-ENCODE-BYTES-UNAMB-PREFIX
 (25198 340
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24946 340
        (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (24446 160 (:DEFINITION ACL2-NUMBER-LISTP))
 (24342 1292
        (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (22143 1144 (:REWRITE DEFAULT-<-1))
 (22017 251 (:REWRITE TAKE-OF-LEN-FREE))
 (21942 720 (:DEFINITION RATIONAL-LISTP))
 (13326 1840 (:REWRITE DEFAULT-+-2))
 (6910 1120
       (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (5144 1532
       (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (4497 2300 (:REWRITE DEFAULT-CAR))
 (4473 497 (:DEFINITION LEN))
 (4290 88 (:DEFINITION EXPT))
 (3806 2203 (:REWRITE DEFAULT-CDR))
 (2494 2494
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
 (2494 2494
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
 (2152
     2152
     (:REWRITE
          ETHEREUM::RLP-ENCODE-BYTES-OF-BYTE-LIST-FIX-BYTES-NORMALIZE-CONST))
 (1885 1840 (:REWRITE DEFAULT-+-1))
 (1778 1040 (:LINEAR LEN-WHEN-PREFIXP))
 (1417 1144 (:REWRITE DEFAULT-<-2))
 (1415 240 (:REWRITE TAKE-WHEN-ATOM))
 (1394 146
       (:REWRITE BYTE-LIST-FIX-WHEN-BYTE-LISTP))
 (1360 320
       (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (640 240
      (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (336 112 (:REWRITE DEFAULT-*-2))
 (234 234
      (:REWRITE BEBYTES=>NAT-OF-BYTE-LIST-FIX-DIGITS-NORMALIZE-CONST))
 (234 78 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (234 78
      (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST64P-REWRITE))
 (234 78
      (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
 (234 78
      (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST20P-REWRITE))
 (176 22 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (156 156 (:TYPE-PRESCRIPTION BYTE-LIST64P))
 (156 156 (:TYPE-PRESCRIPTION BYTE-LIST32P))
 (156 156 (:TYPE-PRESCRIPTION BYTE-LIST20P))
 (156 156
      (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (154 11 (:DEFINITION BINARY-APPEND))
 (146 11 (:REWRITE REPEAT-WHEN-ZP))
 (112 112 (:REWRITE DEFAULT-*-1))
 (100
    100
    (:REWRITE CONS-OF-BYTE-LIST-FIX-Y-NORMALIZE-CONST-UNDER-BYTE-LIST-EQUIV))
 (100 100
      (:REWRITE CONS-OF-BYTE-FIX-X-NORMALIZE-CONST-UNDER-BYTE-LIST-EQUIV))
 (100 100
      (:REWRITE CAR-OF-BYTE-LIST-FIX-X-NORMALIZE-CONST-UNDER-BYTE-EQUIV))
 (99 22 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (99 11 (:REWRITE CONSP-OF-REPEAT))
 (78 78
     (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (78 39
     (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 (78 39 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 (47 47 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (47 47 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (47 47
     (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (47 47
     (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (43 31 (:REWRITE ZIP-OPEN))
 (33 33 (:TYPE-PRESCRIPTION REPEAT))
 (28 8
     (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (28 8
     (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (22 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 8 (:REWRITE UNICITY-OF-0))
 (11 11 (:TYPE-PRESCRIPTION ZP))
 (8 8 (:REWRITE INVERSE-OF-+))
 (8 8 (:DEFINITION FIX)))
(ETHEREUM::LEMMA (8 4 (:REWRITE DEFAULT-+-2))
                 (5 5 (:REWRITE DEFAULT-CDR))
                 (4 4 (:REWRITE DEFAULT-+-1))
                 (4 4
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                              . 2))
                 (4 4
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                              . 1))
                 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                 (3 2 (:REWRITE DEFAULT-<-2))
                 (3 2 (:REWRITE DEFAULT-<-1)))
(ETHEREUM::RLP-ENCODE-TREE-UMAMB-PREFIX
 (117696 1304 (:REWRITE TAKE-OF-LEN-FREE))
 (84162 7253 (:REWRITE DEFAULT-<-1))
 (81518 1097
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (80750 1097
        (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (79127 526 (:DEFINITION ACL2-NUMBER-LISTP))
 (78906 4187
        (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (71016 2367 (:DEFINITION RATIONAL-LISTP))
 (41011 10060 (:REWRITE DEFAULT-+-2))
 (24291 2699 (:DEFINITION LEN))
 (21961 3682
        (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (21644 10608 (:REWRITE DEFAULT-CAR))
 (16790 4976
        (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (16499 9385 (:REWRITE DEFAULT-CDR))
 (12677 431 (:DEFINITION EXPT))
 (10378
   10378
   (:REWRITE ETHEREUM::RLP-ENCODE-TREE-OF-RLP-TREE-FIX-TREE-NORMALIZE-CONST))
 (10308 10060 (:REWRITE DEFAULT-+-1))
 (10034 10034
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
 (10034 10034
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
 (9708 5280 (:LINEAR LEN-WHEN-PREFIXP))
 (8685 7253 (:REWRITE DEFAULT-<-2))
 (7142 1202 (:REWRITE TAKE-WHEN-ATOM))
 (4471 1052
       (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (4120 4120
       (:TYPE-PRESCRIPTION ETHEREUM::RLP-TREE-KIND$INLINE))
 (4120 1030 (:DEFINITION EQ))
 (3605
   515
   (:LINEAR ETHEREUM::CAR-OF-RLP-ENCODE-TREE-LEAF-UPPER-BOUND-WHEN-NO-ERROR))
 (3605
     515
     (:LINEAR
          ETHEREUM::CAR-OF-RLP-ENCODE-TREE-BRANCH-UPPER-BOUND-WHEN-NO-ERROR))
 (2640 856
       (:REWRITE ETHEREUM::RLP-TREE-FIX-WHEN-RLP-TREEP))
 (2104 789
       (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (1710 204 (:REWRITE APPEND-WHEN-NOT-CONSP-2))
 (1545 515 (:REWRITE DEFAULT-*-2))
 (1491 102 (:DEFINITION BINARY-APPEND))
 (1334 102 (:REWRITE REPEAT-WHEN-ZP))
 (1215 1215
       (:REWRITE BEBYTES=>NAT-OF-BYTE-LIST-FIX-DIGITS-NORMALIZE-CONST))
 (1030
      1030
      (:REWRITE
           ETHEREUM::RLP-TREE-KIND$INLINE-OF-RLP-TREE-FIX-X-NORMALIZE-CONST))
 (986 104 (:REWRITE CONSP-OF-REPEAT))
 (913 204 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (892 892
      (:TYPE-PRESCRIPTION ETHEREUM::RLP-TREEP))
 (892 892
      (:REWRITE ETHEREUM::RLP-TREEP-WHEN-MEMBER-EQUAL-OF-RLP-TREE-LISTP))
 (562
    562
    (:REWRITE CONS-OF-BYTE-LIST-FIX-Y-NORMALIZE-CONST-UNDER-BYTE-LIST-EQUIV))
 (562 562
      (:REWRITE CONS-OF-BYTE-FIX-X-NORMALIZE-CONST-UNDER-BYTE-LIST-EQUIV))
 (562 562
      (:REWRITE CAR-OF-BYTE-LIST-FIX-X-NORMALIZE-CONST-UNDER-BYTE-EQUIV))
 (515 515 (:REWRITE DEFAULT-*-1))
 (440 440
      (:REWRITE TRUE-LISTP-WHEN-DAB-DIGIT-LISTP))
 (440 220
      (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 (440 220
      (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 (247 247 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (247 247 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (247 247
      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (247 247
      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (213 165 (:REWRITE ZIP-OPEN))
 (204 102 (:REWRITE DEFAULT-UNARY-MINUS))
 (174 87 (:REWRITE UNICITY-OF-0))
 (102 27
      (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (102 27
      (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (101 101 (:TYPE-PRESCRIPTION ZP))
 (87 87 (:REWRITE INVERSE-OF-+))
 (87 87 (:DEFINITION FIX)))
(ETHEREUM::RLP-ENCODE-SCALAR-UNAMB-PREFIX
  (12 4 (:REWRITE DEFAULT-CDR))
  (12 4 (:REWRITE DEFAULT-CAR))
  (8 8
     (:REWRITE
          ETHEREUM::RLP-ENCODE-BYTES-OF-BYTE-LIST-FIX-BYTES-NORMALIZE-CONST))
  (8 4
     (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST64P-REWRITE))
  (8 4
     (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
  (8 4
     (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST20P-REWRITE))
  (6 6
     (:REWRITE NAT=>BEBYTES*-OF-NFIX-NAT-NORMALIZE-CONST))
  (4 4 (:TYPE-PRESCRIPTION BYTE-LIST64P))
  (4 4 (:TYPE-PRESCRIPTION BYTE-LIST32P))
  (4 4 (:TYPE-PRESCRIPTION BYTE-LIST20P))
  (4 4 (:REWRITE DEFAULT-<-2))
  (4 4 (:REWRITE DEFAULT-<-1)))