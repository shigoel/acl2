(SUMBITS)
(SUMBITS-BITS (1238 74 (:REWRITE BITS-SPLIT-AROUND-ZERO))
              (774 74 (:REWRITE BITS-REDUCE))
              (386 74 (:REWRITE BITS-TAIL))
              (347 215 (:REWRITE DEFAULT-<-2))
              (309 291 (:REWRITE DEFAULT-+-2))
              (301 291 (:REWRITE DEFAULT-+-1))
              (236 54 (:REWRITE BITN-TOO-SMALL))
              (215 215 (:REWRITE DEFAULT-<-1))
              (106 46 (:REWRITE BITN-BVECP-1))
              (99 33 (:REWRITE BITS-TAIL-SPECIAL))
              (93 31 (:REWRITE DEFAULT-UNARY-MINUS))
              (74 74
                  (:REWRITE BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
              (74 74
                  (:REWRITE BITS-FORCE-WITH-A-CHOSEN-NEG))
              (74 74 (:REWRITE BITS-EXPT-CONSTANT))
              (58 11 (:REWRITE BITN-SPLIT-AROUND-ZERO))
              (54 54 (:REWRITE BITN-BVECP-0-ERIC))
              (48 48 (:REWRITE BITS-WITH-X-NOT-RATIONAL))
              (48 48
                  (:REWRITE BITS-WITH-J-NOT-AN-INTEGER))
              (48 48
                  (:REWRITE BITS-WITH-I-NOT-AN-INTEGER))
              (38 38
                  (:REWRITE BITN-WITH-N-NOT-AN-INTEGER))
              (38 38 (:REWRITE BITN-OF-NON-RATIONAL))
              (38 38 (:REWRITE BITN-MINUS))
              (33 33 (:REWRITE BITS-WITH-BAD-INDEX-2))
              (14 14 (:REWRITE BITN-EQUAL-TO-SILLY-VALUE))
              (11 11 (:REWRITE BITN-OF-EXPT-EQUAL-0))
              (8 4 (:REWRITE DEFAULT-*-2))
              (8 4 (:REWRITE DEFAULT-*-1))
              (5 5
                 (:REWRITE BITS-EQUAL-IMPOSSIBLE-CONSTANT))
              (1 1 (:REWRITE BITN-OF-EXPT-EQUAL-1)))
(SUMBITS-THM (6 4 (:REWRITE DEFAULT-<-2))
             (4 4 (:REWRITE DEFAULT-<-1))
             (2 2 (:REWRITE DEFAULT-+-2))
             (2 2 (:REWRITE DEFAULT-+-1))
             (1 1 (:REWRITE BITS-EXPT-CONSTANT)))
(SUMBITS-BADGUY)
(SUMBITS-BADGUY-IS-CORRECT-LEMMA
     (1187 173 (:REWRITE BITN-TOO-SMALL))
     (324 72 (:REWRITE BITN-SPLIT-AROUND-ZERO))
     (250 76 (:REWRITE DEFAULT-<-2))
     (225 169
          (:REWRITE BITN-WITH-N-NOT-AN-INTEGER))
     (216 216 (:TYPE-PRESCRIPTION SUMBITS-BADGUY))
     (173 173 (:REWRITE BITN-BVECP-0-ERIC))
     (169 169 (:REWRITE BITN-OF-NON-RATIONAL))
     (169 169 (:REWRITE BITN-MINUS))
     (88 64 (:REWRITE DEFAULT-+-2))
     (88 64 (:REWRITE DEFAULT-+-1))
     (84 84 (:REWRITE BITN-EQUAL-TO-SILLY-VALUE))
     (82 76 (:REWRITE DEFAULT-<-1))
     (72 72 (:REWRITE BITN-OF-EXPT-EQUAL-0))
     (18 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 12 (:REWRITE ZP-OPEN))
     (12 6 (:REWRITE BITN-BVECP-1))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(SUMBITS-BADGUY-IS-CORRECT
     (220 2 (:DEFINITION SUMBITS-BADGUY))
     (196 20
          (:REWRITE BITN-KNOWN-NOT-0-REPLACE-WITH-1))
     (144 20 (:REWRITE BITN-TOO-SMALL))
     (76 52
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (56 20 (:REWRITE BITN-BVECP-0-ERIC))
     (52 52 (:TYPE-PRESCRIPTION SUMBITS-BADGUY))
     (52 52
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (36 16 (:REWRITE DEFAULT-<-2))
     (28 20
         (:REWRITE BITN-WITH-N-NOT-AN-INTEGER))
     (28 8 (:REWRITE BITN-SPLIT-AROUND-ZERO))
     (20 20 (:REWRITE BITN-OF-NON-RATIONAL))
     (20 20 (:REWRITE BITN-MINUS))
     (20 16 (:REWRITE DEFAULT-<-1))
     (10 10 (:REWRITE BITN-EQUAL-TO-SILLY-VALUE))
     (8 8 (:REWRITE DEFAULT-+-2))
     (8 8 (:REWRITE DEFAULT-+-1))
     (8 8 (:REWRITE BITN-OF-EXPT-EQUAL-0)))
(SUMBITS-BADGUY-BOUNDS
     (376 72 (:REWRITE BITN-TOO-SMALL))
     (150 150
          (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (150 150
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (84 28 (:REWRITE BITN-SPLIT-AROUND-ZERO))
     (82 42 (:REWRITE DEFAULT-<-2))
     (72 72 (:REWRITE BITN-BVECP-0-ERIC))
     (70 70
         (:REWRITE BITN-WITH-N-NOT-AN-INTEGER))
     (70 70 (:REWRITE BITN-OF-NON-RATIONAL))
     (70 70 (:REWRITE BITN-MINUS))
     (48 42 (:REWRITE DEFAULT-<-1))
     (44 22 (:REWRITE BITN-BVECP-1))
     (34 34 (:REWRITE BITN-EQUAL-TO-SILLY-VALUE))
     (28 28 (:REWRITE BITN-OF-EXPT-EQUAL-0))
     (22 22 (:REWRITE DEFAULT-+-2))
     (22 22 (:REWRITE DEFAULT-+-1)))