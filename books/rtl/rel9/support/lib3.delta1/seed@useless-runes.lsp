(LEMMA-4-1-1
 (453
  453
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (453 453
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (453
     453
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (453 453
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (388 91 (:REWRITE DEFAULT-TIMES-2))
 (388 91 (:REWRITE DEFAULT-TIMES-1))
 (111 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (89 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (57 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (35 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (30 22 (:REWRITE DEFAULT-PLUS-1))
 (30 18
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (23 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22 22 (:REWRITE DEFAULT-PLUS-2))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (21 18 (:REWRITE CONSTANT-<-INTEGERP))
 (21 18
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (18 18 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (11 11 (:REWRITE |(expt c (* d n))|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE DEFAULT-MINUS))
 (8 8 (:REWRITE |(- (* c x))|))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 1 (:REWRITE RATIONALP-X))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(LEMMA-4-1-2 (6 4 (:REWRITE SIMPLIFY-SUMS-<))
             (6 4
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
             (6 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
             (6 4 (:REWRITE DEFAULT-LESS-THAN-1))
             (4 4 (:REWRITE THE-FLOOR-BELOW))
             (4 4 (:REWRITE THE-FLOOR-ABOVE))
             (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
             (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
             (4 4
                (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
             (4 4
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
             (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
             (4 4 (:REWRITE INTEGERP-<-CONSTANT))
             (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
             (4 4 (:REWRITE CONSTANT-<-INTEGERP))
             (4 4
                (:REWRITE |(< c (/ x)) positive c --- present in goal|))
             (4 4
                (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
             (4 4
                (:REWRITE |(< c (/ x)) negative c --- present in goal|))
             (4 4
                (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
             (4 4 (:REWRITE |(< c (- x))|))
             (4 4
                (:REWRITE |(< (/ x) c) positive c --- present in goal|))
             (4 4
                (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
             (4 4
                (:REWRITE |(< (/ x) c) negative c --- present in goal|))
             (4 4
                (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
             (4 4 (:REWRITE |(< (/ x) (/ y))|))
             (4 4 (:REWRITE |(< (- x) c)|))
             (4 4 (:REWRITE |(< (- x) (- y))|))
             (4 4 (:LINEAR FL-MONOTONE-LINEAR))
             (4 2 (:REWRITE DEFAULT-PLUS-2))
             (4 1 (:REWRITE RATIONALP-X))
             (3 3 (:REWRITE REDUCE-INTEGERP-+))
             (3 3 (:REWRITE INTEGERP-MINUS-X))
             (3 3 (:META META-INTEGERP-CORRECT))
             (2 2
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (2 2 (:REWRITE NORMALIZE-ADDENDS))
             (2 2 (:REWRITE DEFAULT-PLUS-1))
             (2 2 (:LINEAR N<=FL-LINEAR))
             (1 1 (:REWRITE REDUCE-RATIONALP-+))
             (1 1 (:REWRITE REDUCE-RATIONALP-*))
             (1 1 (:REWRITE RATIONALP-MINUS-X))
             (1 1 (:META META-RATIONALP-CORRECT)))
(LEMMA-4-1-3
 (440
  440
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (440 440
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (440
     440
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (440 440
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (414 100 (:REWRITE DEFAULT-TIMES-1))
 (406 100 (:REWRITE DEFAULT-TIMES-2))
 (136 28 (:REWRITE DEFAULT-LESS-THAN-2))
 (90 28
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (88 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (66 28 (:REWRITE DEFAULT-LESS-THAN-1))
 (49 11 (:REWRITE SIMPLIFY-SUMS-<))
 (49 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (37 29 (:REWRITE DEFAULT-PLUS-1))
 (35 23
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (35 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (30 28
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (30 28
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (29 29 (:REWRITE DEFAULT-PLUS-2))
 (28 28 (:REWRITE THE-FLOOR-BELOW))
 (28 28 (:REWRITE THE-FLOOR-ABOVE))
 (26 23 (:REWRITE CONSTANT-<-INTEGERP))
 (26 23
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (- x))|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE |(< (- x) c)|))
 (23 23 (:REWRITE |(< (- x) (- y))|))
 (18 18 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE DEFAULT-EXPT-1))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (13 13 (:REWRITE |(expt c (* d n))|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE DEFAULT-MINUS))
 (8 8 (:REWRITE |(- (* c x))|))
 (8 2 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 1 (:REWRITE RATIONALP-X))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(+ 0 x)|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(LEMMA-4-1-5
     (3874 712
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1224 100 (:REWRITE ODD-EXPT-THM))
     (1204 43
           (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (1118 43
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (871 39 (:LINEAR EXPT-<=-1-TWO))
     (854 552 (:REWRITE SIMPLIFY-SUMS-<))
     (798 712
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (798 712
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (712 712 (:REWRITE THE-FLOOR-BELOW))
     (712 712 (:REWRITE THE-FLOOR-ABOVE))
     (703 574 (:REWRITE CONSTANT-<-INTEGERP))
     (700 40 (:REWRITE |(equal (if a b c) x)|))
     (662 574 (:REWRITE INTEGERP-<-CONSTANT))
     (661 577 (:REWRITE |(< (- x) c)|))
     (658 658 (:REWRITE |(expt 1/c n)|))
     (658 658 (:REWRITE |(expt (- x) n)|))
     (605 577
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (595 577
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (577 577
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (577 577
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (577 577
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (577 577 (:REWRITE |(< c (- x))|))
     (577 577
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (577 577
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (577 577
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (577 577 (:REWRITE |(< (/ x) (/ y))|))
     (577 577 (:REWRITE |(< (- x) (- y))|))
     (442 39 (:LINEAR EXPT-<-1-TWO))
     (440 440 (:REWRITE REDUCE-INTEGERP-+))
     (440 440 (:REWRITE INTEGERP-MINUS-X))
     (440 440 (:META META-INTEGERP-CORRECT))
     (336 201 (:REWRITE |(+ c (+ d x))|))
     (307 307 (:REWRITE |(expt c (* d n))|))
     (269 269
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (222 222 (:REWRITE RATIONALP-MINUS-X))
     (219 219 (:REWRITE REDUCE-RATIONALP-+))
     (219 219 (:META META-RATIONALP-CORRECT))
     (207 23
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (207 23
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (207 23
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (207 23
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (172 172 (:TYPE-PRESCRIPTION ABS))
     (170 170 (:REWRITE |(< x (+ c/d y))|))
     (160 40 (:REWRITE |(integerp (- x))|))
     (110 110 (:REWRITE ZP-OPEN))
     (100 20 (:REWRITE |(equal (expt x n) 0)|))
     (89 89 (:REWRITE |(< 0 (* x y))|))
     (80 20
         (:REWRITE |(* (expt x m) (expt x n))|))
     (78 78
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (78 78
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (56 28 (:REWRITE COLLECT-*-PROBLEM-FINDER))
     (54 54 (:REWRITE FOLD-CONSTS-IN-+))
     (52 52
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (52 52
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (52 52 (:REWRITE |(equal c (/ x))|))
     (52 52 (:REWRITE |(equal (/ x) (/ y))|))
     (52 52 (:REWRITE |(equal (- x) (- y))|))
     (49 49
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (49 49 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (49 49
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (49 49
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (49 49
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (49 49 (:REWRITE |(equal c (- x))|))
     (49 49 (:REWRITE |(equal (- x) c)|))
     (49 49 (:REWRITE |(< (+ c/d x) y)|))
     (48 48 (:REWRITE |(< y (+ (- c) x))|))
     (43 43
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (43 43
         (:REWRITE |(< (/ x) y) with (< x 0)|))
     (39 39 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (39 39 (:LINEAR EXPT-LINEAR-UPPER-<))
     (39 39 (:LINEAR EXPT-LINEAR-LOWER-<))
     (39 39 (:LINEAR EXPT->=-1-TWO))
     (39 39 (:LINEAR EXPT->-1-TWO))
     (39 39 (:LINEAR EXPT-<=-1-ONE))
     (39 39 (:LINEAR EXPT-<-1-ONE))
     (36 36 (:REWRITE |(< (+ (- c) x) y)|))
     (36 36 (:REWRITE |(* (- x) y)|))
     (32 8 (:REWRITE |(* (/ x) (expt x n))|))
     (28 28
         (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
     (26 26 (:LINEAR FL-MONOTONE-LINEAR))
     (24 24 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (24 24 (:REWRITE |(* c (* d x))|))
     (20 20 (:REWRITE |(equal (expt 2 n) c)|))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (19 19 (:REWRITE |(< 0 (/ x))|))
     (19 19 (:REWRITE |(< (* x y) 0)|))
     (13 13 (:LINEAR N<=FL-LINEAR))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (5 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE DEFAULT-DIVIDE))
     (3 3 (:REWRITE |(not (equal x (/ y)))|))
     (3 3 (:REWRITE |(equal x (/ y))|))
     (3 3
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (3 3
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (3 3 (:REWRITE |(- (- x))|)))
(LEMMA-4-1-7 (161 161
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
             (161 161
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
             (161 161
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
             (112 4
                  (:REWRITE |(<= x (/ y)) with (< 0 y)|))
             (104 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
             (55 31
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
             (49 28 (:REWRITE SIMPLIFY-SUMS-<))
             (46 4 (:REWRITE ODD-EXPT-THM))
             (42 30 (:REWRITE CONSTANT-<-INTEGERP))
             (39 31
                 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
             (39 31
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
             (31 31 (:REWRITE THE-FLOOR-BELOW))
             (31 31 (:REWRITE THE-FLOOR-ABOVE))
             (30 30
                 (:REWRITE REMOVE-STRICT-INEQUALITIES))
             (30 30 (:REWRITE INTEGERP-<-CONSTANT))
             (30 30
                 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
             (30 30
                 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
             (30 30
                 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
             (30 30
                 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
             (30 30 (:REWRITE |(< c (- x))|))
             (30 30
                 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
             (30 30
                 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
             (30 30
                 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
             (30 30
                 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
             (30 30 (:REWRITE |(< (/ x) (/ y))|))
             (30 30 (:REWRITE |(< (- x) c)|))
             (30 30 (:REWRITE |(< (- x) (- y))|))
             (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
             (26 26 (:REWRITE DEFAULT-EXPT-1))
             (26 26 (:REWRITE |(expt 1/c n)|))
             (26 26 (:REWRITE |(expt (- x) n)|))
             (25 25
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (20 5 (:REWRITE RATIONALP-X))
             (16 16 (:TYPE-PRESCRIPTION ABS))
             (12 12 (:REWRITE REDUCE-INTEGERP-+))
             (12 12 (:REWRITE INTEGERP-MINUS-X))
             (12 12 (:META META-INTEGERP-CORRECT))
             (10 10 (:REWRITE ZP-OPEN))
             (10 9 (:REWRITE |(+ c (+ d x))|))
             (8 8 (:REWRITE |(expt c (* d n))|))
             (6 6 (:REWRITE FOLD-CONSTS-IN-+))
             (6 6 (:REWRITE |(< x (+ c/d y))|))
             (6 6 (:REWRITE |(* (- x) y)|))
             (5 5 (:REWRITE REDUCE-RATIONALP-+))
             (5 5 (:REWRITE REDUCE-RATIONALP-*))
             (5 5 (:REWRITE RATIONALP-MINUS-X))
             (5 5 (:REWRITE |(< y (+ (- c) x))|))
             (5 5 (:META META-RATIONALP-CORRECT))
             (5 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
             (4 4
                (:REWRITE |(<= x (/ y)) with (< y 0)|))
             (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
             (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
             (3 3 (:REWRITE |(< (+ c/d x) y)|))
             (3 3 (:REWRITE |(< (+ (- c) x) y)|))
             (3 3 (:REWRITE |(* c (* d x))|))
             (1 1 (:REWRITE |(< 0 (* x y))|)))
(LEMMA-4-1-8
 (1479
  1479
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1479
      1479
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1479
     1479
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1479 1479
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1479 1479
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (993 50 (:REWRITE DEFAULT-PLUS-2))
 (733 76
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (643 76
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (379 50 (:REWRITE DEFAULT-PLUS-1))
 (325 325
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (325 325
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (325 325
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (323 20
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (305 305
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (254 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (203 18 (:REWRITE SIMPLIFY-SUMS-<))
 (164 20 (:REWRITE ACL2-NUMBERP-X))
 (121 41 (:REWRITE DEFAULT-EXPT-1))
 (116 31 (:REWRITE DEFAULT-MINUS))
 (91 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (83 83
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (80 20 (:REWRITE RATIONALP-X))
 (76 76
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (70 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (69 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (62 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (52 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (44 44 (:REWRITE REDUCE-INTEGERP-+))
 (44 44 (:REWRITE INTEGERP-MINUS-X))
 (44 44 (:META META-INTEGERP-CORRECT))
 (43 2 (:REWRITE ODD-EXPT-THM))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 20 (:REWRITE CONSTANT-<-INTEGERP))
 (25 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20 (:REWRITE REDUCE-RATIONALP-+))
 (20 20 (:REWRITE REDUCE-RATIONALP-*))
 (20 20 (:REWRITE RATIONALP-MINUS-X))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:META META-RATIONALP-CORRECT))
 (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13 (:REWRITE |(* c (* d x))|))
 (12 9 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (1 1 (:REWRITE |(expt (- c) n)|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(LEMMA-4-1-9
 (3600
  3600
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3600
      3600
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3600
     3600
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3600 3600
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3600 3600
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3424 268 (:REWRITE DEFAULT-PLUS-2))
 (1497 268 (:REWRITE DEFAULT-PLUS-1))
 (1468 289
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1407 113 (:REWRITE RATIONALP-X))
 (1270 289
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (927 70 (:REWRITE DEFAULT-LESS-THAN-2))
 (832 110 (:REWRITE REDUCE-RATIONALP-*))
 (812 108 (:REWRITE ACL2-NUMBERP-X))
 (718 718
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (639 52 (:REWRITE SIMPLIFY-SUMS-<))
 (621 213 (:REWRITE DEFAULT-EXPT-1))
 (525 177 (:REWRITE DEFAULT-MINUS))
 (508 508
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (508 508
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (508 508
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (436 234 (:META META-INTEGERP-CORRECT))
 (396 90 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (388 388
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (388 388
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (359 70 (:REWRITE DEFAULT-LESS-THAN-1))
 (289 289
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (268 236 (:REWRITE INTEGERP-MINUS-X))
 (263 1 (:REWRITE |(rationalp (- x))|))
 (234 234 (:REWRITE REDUCE-INTEGERP-+))
 (190 112 (:REWRITE RATIONALP-MINUS-X))
 (163 70
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (161 7 (:REWRITE ODD-EXPT-THM))
 (140 4
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (124 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (108 108
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (107 4 (:DEFINITION RFIX))
 (104 104 (:META META-RATIONALP-CORRECT))
 (103 5 (:REWRITE |(integerp (expt x n))|))
 (99 67 (:REWRITE |(< (- x) c)|))
 (87 87 (:REWRITE |(* c (* d x))|))
 (78 70
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (78 70
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (78 66 (:REWRITE CONSTANT-<-INTEGERP))
 (70 70 (:REWRITE THE-FLOOR-BELOW))
 (70 70 (:REWRITE THE-FLOOR-ABOVE))
 (67 67
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (67 67
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (67 67
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (67 67
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (67 67 (:REWRITE |(< c (- x))|))
 (67 67
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (67 67
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (67 67
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (67 67
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (67 67 (:REWRITE |(< (/ x) (/ y))|))
 (67 67 (:REWRITE |(< (- x) (- y))|))
 (66 66
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (66 66 (:REWRITE INTEGERP-<-CONSTANT))
 (63 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (62 62 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (50 2 (:REWRITE |(equal (if a b c) x)|))
 (42 42
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (42 42
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (42 42
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (31 31 (:REWRITE |(< x (+ c/d y))|))
 (28 28 (:REWRITE |(< y (+ (- c) x))|))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:TYPE-PRESCRIPTION ABS))
 (16 1 (:REWRITE |(+ (+ x y) z)|))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 1 (:REWRITE |(equal (expt x n) 0)|))
 (8 8 (:REWRITE ZP-OPEN))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(expt (- c) n)|))
 (4 4
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (3 3
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(* a (/ a) b)|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LEMMA-4-1-10
 (976
  976
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (976 976
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (976
     976
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (976 976
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (620 42 (:REWRITE DEFAULT-PLUS-2))
 (510 51
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (497 60 (:REWRITE ACL2-NUMBERP-X))
 (438 51
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (340 52
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (303 66 (:REWRITE DEFAULT-LESS-THAN-2))
 (266 51 (:REWRITE SIMPLIFY-SUMS-<))
 (241 61 (:REWRITE RATIONALP-X))
 (219 66 (:REWRITE DEFAULT-LESS-THAN-1))
 (193 42 (:REWRITE DEFAULT-PLUS-1))
 (175 5
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (155 5 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (146 146
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (129 129 (:REWRITE REDUCE-INTEGERP-+))
 (129 129 (:REWRITE INTEGERP-MINUS-X))
 (129 129 (:META META-INTEGERP-CORRECT))
 (119 4 (:REWRITE ODD-EXPT-THM))
 (118 56
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (98 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (92 2
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (70 56
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (70 56
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (69 54 (:REWRITE CONSTANT-<-INTEGERP))
 (66 66 (:REWRITE THE-FLOOR-BELOW))
 (66 66 (:REWRITE THE-FLOOR-ABOVE))
 (61 61 (:REWRITE REDUCE-RATIONALP-+))
 (61 61 (:REWRITE REDUCE-RATIONALP-*))
 (61 61 (:REWRITE RATIONALP-MINUS-X))
 (61 61 (:META META-RATIONALP-CORRECT))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< c (- x))|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) c)|))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (52 52
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (51 51
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (48 48 (:REWRITE DEFAULT-EXPT-1))
 (45 45 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (42 24 (:REWRITE DEFAULT-MINUS))
 (28 28 (:TYPE-PRESCRIPTION ABS))
 (27 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (26 26
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (26 26
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (26 26 (:REWRITE |(expt (- x) n)|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 9 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE |(expt c (* d n))|))
 (8 8 (:LINEAR FL-MONOTONE-LINEAR))
 (8 8 (:LINEAR FL-DEF))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (5 5
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:LINEAR N<=FL-LINEAR))
 (4 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (4 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE |(* (- x) y)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(LEMMA-4-1-11
 (1410
  1410
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1410
      1410
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1410
     1410
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1410 1410
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1410 1410
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (742 44 (:REWRITE DEFAULT-PLUS-2))
 (613 64
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (532 64
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (326 44 (:REWRITE DEFAULT-PLUS-1))
 (325 325
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (325 325
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (325 325
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (305 305
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (273 19
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (213 18 (:REWRITE SIMPLIFY-SUMS-<))
 (164 20 (:REWRITE ACL2-NUMBERP-X))
 (147 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (147 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (111 40 (:REWRITE DEFAULT-EXPT-1))
 (83 83
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (80 20 (:REWRITE RATIONALP-X))
 (70 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (64 64
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (62 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (59 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (44 44 (:REWRITE REDUCE-INTEGERP-+))
 (44 44 (:REWRITE INTEGERP-MINUS-X))
 (44 44 (:META META-INTEGERP-CORRECT))
 (44 26 (:REWRITE DEFAULT-MINUS))
 (43 2 (:REWRITE ODD-EXPT-THM))
 (29 29 (:REWRITE |(expt (- x) n)|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (25 19 (:REWRITE CONSTANT-<-INTEGERP))
 (24 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20 (:REWRITE REDUCE-RATIONALP-+))
 (20 20 (:REWRITE REDUCE-RATIONALP-*))
 (20 20 (:REWRITE RATIONALP-MINUS-X))
 (20 20 (:META META-RATIONALP-CORRECT))
 (19 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< c (- x))|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (19 19 (:REWRITE |(< (- x) c)|))
 (19 19 (:REWRITE |(< (- x) (- y))|))
 (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13 (:REWRITE |(* c (* d x))|))
 (11 8 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(LEMMA-4-1-12
 (2567
  2567
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2567
      2567
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2567
     2567
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2567 2567
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2567 2567
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1895 166 (:REWRITE DEFAULT-PLUS-2))
 (1292 108 (:REWRITE RATIONALP-X))
 (945 166 (:REWRITE DEFAULT-PLUS-1))
 (830 108 (:REWRITE REDUCE-RATIONALP-*))
 (812 108 (:REWRITE ACL2-NUMBERP-X))
 (737 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (656 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (551 551
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (461 461
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (461 461
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (461 461
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (458 175 (:REWRITE DEFAULT-EXPT-1))
 (435 35 (:REWRITE DEFAULT-LESS-THAN-1))
 (408 225 (:META META-INTEGERP-CORRECT))
 (402 30 (:REWRITE SIMPLIFY-SUMS-<))
 (326 65 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (269 269
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (269 269
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (241 35 (:REWRITE DEFAULT-LESS-THAN-2))
 (225 225 (:REWRITE REDUCE-INTEGERP-+))
 (225 225 (:REWRITE INTEGERP-MINUS-X))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (138 120 (:REWRITE DEFAULT-MINUS))
 (108 108 (:REWRITE RATIONALP-MINUS-X))
 (108 108 (:REWRITE |(expt (- x) n)|))
 (107 4 (:DEFINITION RFIX))
 (103 5 (:REWRITE |(integerp (expt x n))|))
 (102 102 (:META META-RATIONALP-CORRECT))
 (81 81
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (77 5 (:REWRITE ODD-EXPT-THM))
 (70 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (66 35
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (66 34 (:REWRITE |(< (- x) c)|))
 (63 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (62 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (60 60 (:REWRITE |(* c (* d x))|))
 (50 2 (:REWRITE |(equal (if a b c) x)|))
 (42 42
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (42 42
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (42 42
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (39 35
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (39 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (39 33 (:REWRITE CONSTANT-<-INTEGERP))
 (35 35 (:REWRITE THE-FLOOR-BELOW))
 (35 35 (:REWRITE THE-FLOOR-ABOVE))
 (34 34
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (34 34
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (34 34
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (34 34
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (34 34 (:REWRITE |(< c (- x))|))
 (34 34
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (34 34
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (34 34
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (34 34
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (34 34 (:REWRITE |(< (/ x) (/ y))|))
 (34 34 (:REWRITE |(< (- x) (- y))|))
 (33 33
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (33 33 (:REWRITE INTEGERP-<-CONSTANT))
 (31 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (19 19 (:REWRITE FOLD-CONSTS-IN-+))
 (16 1 (:REWRITE |(+ (+ x y) z)|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (9 1 (:REWRITE |(equal (expt x n) 0)|))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 2 (:REWRITE |(+ (* c x) (* d x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (2 2 (:REWRITE |(* a (/ a) b)|))
 (2 2 (:REWRITE |(* 0 x)|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|)))
(LEMMA-4-1-13
 (1354
  1354
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1354
      1354
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1354
     1354
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1354 1354
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (780 168
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (780 168
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (603 119 (:REWRITE DEFAULT-TIMES-2))
 (517 45 (:REWRITE DEFAULT-PLUS-2))
 (478 119 (:REWRITE DEFAULT-TIMES-1))
 (380 38
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (344 38
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (197 31 (:REWRITE DEFAULT-LESS-THAN-2))
 (193 17 (:REWRITE SIMPLIFY-SUMS-<))
 (181 45 (:REWRITE DEFAULT-PLUS-1))
 (168 168
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (154 31 (:REWRITE DEFAULT-LESS-THAN-1))
 (153 31
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (58 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (43 2 (:LINEAR EXPT-<=-1-TWO))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (35 35 (:REWRITE DEFAULT-EXPT-2))
 (35 35 (:REWRITE DEFAULT-EXPT-1))
 (35 35 (:REWRITE |(expt 1/c n)|))
 (35 35 (:REWRITE |(expt (- x) n)|))
 (35 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (34 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (33 31
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (31 31 (:REWRITE THE-FLOOR-BELOW))
 (31 31 (:REWRITE THE-FLOOR-ABOVE))
 (30 12 (:REWRITE DEFAULT-MINUS))
 (28 25 (:REWRITE CONSTANT-<-INTEGERP))
 (28 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25 (:REWRITE INTEGERP-<-CONSTANT))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (25 25 (:REWRITE |(< (- x) c)|))
 (25 25 (:REWRITE |(< (- x) (- y))|))
 (23 23 (:REWRITE |(expt c (* d n))|))
 (21 9 (:REWRITE |(+ c (+ d x))|))
 (20 20
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (3 3 (:REWRITE |(* (- x) y)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:META META-RATIONALP-CORRECT))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-14
 (2970
  2970
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2970
      2970
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2970
     2970
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2970 2970
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1554 425 (:REWRITE DEFAULT-TIMES-1))
 (1547 425 (:REWRITE DEFAULT-TIMES-2))
 (783 106
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (719 719
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (719 719
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (719 719
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (669 105 (:REWRITE SIMPLIFY-SUMS-<))
 (583 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (550 113 (:REWRITE DEFAULT-LESS-THAN-2))
 (547 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (537 61 (:REWRITE DEFAULT-PLUS-2))
 (385 11
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (353 113 (:REWRITE DEFAULT-LESS-THAN-1))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (235 113
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (224 224
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (205 61 (:REWRITE DEFAULT-PLUS-1))
 (146 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (144 108
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (141 108 (:REWRITE CONSTANT-<-INTEGERP))
 (141 108
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (140 140
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (140 140
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (135 113
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (135 113
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 128 (:REWRITE DEFAULT-EXPT-2))
 (128 128 (:REWRITE DEFAULT-EXPT-1))
 (128 128 (:REWRITE |(expt 1/c n)|))
 (128 128 (:REWRITE |(expt (- x) n)|))
 (113 113 (:REWRITE THE-FLOOR-BELOW))
 (113 113 (:REWRITE THE-FLOOR-ABOVE))
 (108 108 (:REWRITE INTEGERP-<-CONSTANT))
 (108 108
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (108 108
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (108 108
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (108 108 (:REWRITE |(< c (- x))|))
 (108 108
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (108 108
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (108 108
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (108 108 (:REWRITE |(< (/ x) (/ y))|))
 (108 108 (:REWRITE |(< (- x) c)|))
 (108 108 (:REWRITE |(< (- x) (- y))|))
 (82 82 (:REWRITE |(expt c (* d n))|))
 (73 55 (:REWRITE DEFAULT-MINUS))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (49 8 (:REWRITE ODD-EXPT-THM))
 (46 46 (:REWRITE REDUCE-INTEGERP-+))
 (46 46 (:REWRITE INTEGERP-MINUS-X))
 (46 46 (:META META-INTEGERP-CORRECT))
 (44 44 (:TYPE-PRESCRIPTION ABS))
 (44 11 (:REWRITE RATIONALP-X))
 (43 2 (:LINEAR EXPT-<=-1-TWO))
 (22 22 (:REWRITE ZP-OPEN))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (21 9 (:REWRITE |(+ c (+ d x))|))
 (14 14 (:REWRITE |(* c (* d x))|))
 (12 12
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (11 11 (:META META-RATIONALP-CORRECT))
 (10 10 (:LINEAR FL-MONOTONE-LINEAR))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:LINEAR N<=FL-LINEAR))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(* (- x) y)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(LEMMA-4-1-15
 (3842
  3842
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3842
      3842
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3842
     3842
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3842 3842
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2697 602 (:REWRITE DEFAULT-TIMES-1))
 (2596 602 (:REWRITE DEFAULT-TIMES-2))
 (1170 162 (:REWRITE DEFAULT-PLUS-2))
 (960 107
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (919 919
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (919 919
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (919 919
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (846 106 (:REWRITE SIMPLIFY-SUMS-<))
 (727 114 (:REWRITE DEFAULT-LESS-THAN-2))
 (633 162 (:REWRITE DEFAULT-PLUS-1))
 (583 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (547 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (385 11
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (354 114 (:REWRITE DEFAULT-LESS-THAN-1))
 (278 53 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (236 114
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (224 224
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (145 109
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (142 109 (:REWRITE CONSTANT-<-INTEGERP))
 (142 109
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (140 140
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (140 140
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (136 114
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (136 114
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 128 (:REWRITE DEFAULT-EXPT-2))
 (128 128 (:REWRITE DEFAULT-EXPT-1))
 (128 128 (:REWRITE |(expt 1/c n)|))
 (128 128 (:REWRITE |(expt (- x) n)|))
 (114 114 (:REWRITE THE-FLOOR-BELOW))
 (114 114 (:REWRITE THE-FLOOR-ABOVE))
 (109 109 (:REWRITE INTEGERP-<-CONSTANT))
 (109 109
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (109 109
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (109 109
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (109 109 (:REWRITE |(< c (- x))|))
 (109 109
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (109 109
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (109 109
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (109 109 (:REWRITE |(< (/ x) (/ y))|))
 (109 109 (:REWRITE |(< (- x) c)|))
 (109 109 (:REWRITE |(< (- x) (- y))|))
 (99 99
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (85 67 (:REWRITE DEFAULT-MINUS))
 (82 82 (:REWRITE |(expt c (* d n))|))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (49 8 (:REWRITE ODD-EXPT-THM))
 (46 46 (:REWRITE REDUCE-INTEGERP-+))
 (46 46 (:REWRITE INTEGERP-MINUS-X))
 (46 46 (:META META-INTEGERP-CORRECT))
 (44 44 (:TYPE-PRESCRIPTION ABS))
 (44 11 (:REWRITE RATIONALP-X))
 (43 43 (:REWRITE |(< x (+ c/d y))|))
 (43 2 (:LINEAR EXPT-<=-1-TWO))
 (39 39 (:REWRITE |(< y (+ (- c) x))|))
 (22 22 (:REWRITE ZP-OPEN))
 (21 9 (:REWRITE |(+ c (+ d x))|))
 (14 14 (:REWRITE |(* c (* d x))|))
 (12 12
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (11 11 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(* (- x) y)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(LEMMA-4-1-16)
(LEMMA-4-1-17)
(LEMMA-4-1-A-1)
(K**)
(RHO**)
(K**-RHO**-CONSTRAINT)
(X**)
(X**-CONSTRAINT)
(L**
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(S**)
(S**-CONSTRAINT
 (33 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (33 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE)))
(Q0**
 (50 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (50 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT)))
(LEMMA-4-1-A
     (132 38
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (59 25 (:REWRITE SIMPLIFY-SUMS-<))
     (52 52
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (52 9 (:REWRITE RATIONALP-X))
     (43 33 (:REWRITE INTEGERP-<-CONSTANT))
     (40 38
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (40 38
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (39 33
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (38 38 (:REWRITE THE-FLOOR-BELOW))
     (38 38 (:REWRITE THE-FLOOR-ABOVE))
     (36 33 (:REWRITE CONSTANT-<-INTEGERP))
     (36 33
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (34 2 (:REWRITE ODD-EXPT-THM))
     (34 2 (:LINEAR EXPT-<=-1-TWO))
     (33 33
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (33 33 (:REWRITE |(< c (- x))|))
     (33 33
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (33 33 (:REWRITE |(< (/ x) (/ y))|))
     (33 33 (:REWRITE |(< (- x) c)|))
     (33 33 (:REWRITE |(< (- x) (- y))|))
     (32 32 (:REWRITE |(* c (* d x))|))
     (28 1
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (26 2
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (26 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (26 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (26 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (22 18 (:REWRITE |(+ c (+ d x))|))
     (18 18 (:REWRITE REDUCE-INTEGERP-+))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18 (:META META-INTEGERP-CORRECT))
     (16 16 (:REWRITE |(< x (+ c/d y))|))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9 (:META META-RATIONALP-CORRECT))
     (8 8 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (4 4
        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(expt (- c) n)|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
     (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
     (2 2 (:LINEAR EXPT->=-1-TWO))
     (2 2 (:LINEAR EXPT->-1-TWO))
     (2 2 (:LINEAR EXPT-<=-1-ONE))
     (2 2 (:LINEAR EXPT-<-1-TWO))
     (2 2 (:LINEAR EXPT-<-1-ONE))
     (1 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|)))
(CG-SQRT-1
 (275
   275
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (275
  275
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (275 275
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (275
     275
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (275 275
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (275 275
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (275 275
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (270 53 (:REWRITE DEFAULT-PLUS-2))
 (231 53 (:REWRITE DEFAULT-PLUS-1))
 (224 224
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (196 40
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (193 37 (:REWRITE SIMPLIFY-SUMS-<))
 (159 40 (:REWRITE DEFAULT-LESS-THAN-1))
 (116 40 (:REWRITE DEFAULT-LESS-THAN-2))
 (64 64
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (60 2 (:LINEAR EXPT->=-1-TWO))
 (60 2 (:LINEAR EXPT->-1-TWO))
 (60 2 (:LINEAR EXPT-<-1-ONE))
 (59 40 (:REWRITE |(< (- x) c)|))
 (59 40 (:REWRITE |(< (- x) (- y))|))
 (58 46 (:REWRITE DEFAULT-TIMES-1))
 (54 2 (:LINEAR EXPT-X->=-X))
 (54 2 (:LINEAR EXPT->=-1-ONE))
 (54 2 (:LINEAR EXPT-<=-1-TWO))
 (52 2 (:LINEAR EXPT-X->-X))
 (52 2 (:LINEAR EXPT->-1-ONE))
 (52 2 (:LINEAR EXPT-<-1-TWO))
 (48 10 (:REWRITE DEFAULT-MINUS))
 (46 46 (:REWRITE DEFAULT-TIMES-2))
 (40 40 (:REWRITE THE-FLOOR-BELOW))
 (40 40 (:REWRITE THE-FLOOR-ABOVE))
 (40 40
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (40 40
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (40 40
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (40 40
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (40 40 (:REWRITE INTEGERP-<-CONSTANT))
 (40 40 (:REWRITE CONSTANT-<-INTEGERP))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< c (- x))|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< (/ x) (/ y))|))
 (36 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (24 6 (:REWRITE RATIONALP-X))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE DEFAULT-EXPT-1))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 6 (:META META-INTEGERP-CORRECT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(LEMMA-4-1-18
     (790 117 (:REWRITE RATIONALP-X))
     (701 181
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (461 22
          (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (443 22
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (361 245 (:META META-INTEGERP-CORRECT))
     (332 108 (:META META-RATIONALP-CORRECT))
     (278 157 (:REWRITE CONSTANT-<-INTEGERP))
     (265 249 (:REWRITE INTEGERP-MINUS-X))
     (258 152 (:REWRITE SIMPLIFY-SUMS-<))
     (245 245 (:REWRITE REDUCE-INTEGERP-+))
     (228 36 (:REWRITE ACL2-NUMBERP-X))
     (218 22
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (218 22
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (215 159 (:REWRITE |(< (- x) c)|))
     (199 181
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (199 181
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (196 196 (:REWRITE |(expt (- x) n)|))
     (188 132 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (182 182 (:REWRITE THE-FLOOR-BELOW))
     (182 182 (:REWRITE THE-FLOOR-ABOVE))
     (176 157
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (174 159
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (174 159
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (173 41
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (161 23 (:REWRITE |(integerp (expt x n))|))
     (159 159
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (159 159
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (159 159
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (159 159 (:REWRITE |(< c (- x))|))
     (159 159
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (159 159
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (159 159
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (159 159 (:REWRITE |(< (/ x) (/ y))|))
     (159 159 (:REWRITE |(< (- x) (- y))|))
     (157 157 (:REWRITE INTEGERP-<-CONSTANT))
     (128 128
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (127 27
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (122 71 (:TYPE-PRESCRIPTION NATP-MOD))
     (117 117 (:REWRITE RATIONALP-MINUS-X))
     (112 28 (:REWRITE |(integerp (- x))|))
     (112 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (112 4 (:REWRITE MOD-X-Y-=-X . 4))
     (112 4 (:REWRITE MOD-X-Y-=-X . 3))
     (108 108 (:REWRITE REDUCE-RATIONALP-+))
     (108 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (97 59 (:REWRITE |(+ c (+ d x))|))
     (96 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (95 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (92 92 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (92 92 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (92 92 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (92 92 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (92 92
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (92 92
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (92 92 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (92 92
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (92 92
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (92 92 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (92 4 (:REWRITE MOD-DOES-NOTHING))
     (80 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (74 14 (:REWRITE |(< (/ x) 0)|))
     (71 71 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (71 71 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (56 4 (:REWRITE MOD-ZERO . 4))
     (52 4 (:REWRITE CANCEL-MOD-+))
     (51 51 (:TYPE-PRESCRIPTION NATP))
     (44 44 (:REWRITE |(< x (+ c/d y))|))
     (42 6
         (:REWRITE |(* (expt c m) (expt d n))|))
     (41 41
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (36 36 (:TYPE-PRESCRIPTION ABS))
     (31 31 (:REWRITE DEFAULT-MOD-2))
     (31 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (30 30
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
     (30 30
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
     (30 30
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
     (30 30
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
     (30 30
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
     (30 30
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
     (30 6
         (:REWRITE |(* (expt x n) (expt y n))|))
     (30 6
         (:REWRITE |(* (expt x m) (expt x n))|))
     (29 29 (:REWRITE |(equal c (/ x))|))
     (29 29 (:REWRITE |(equal (/ x) (/ y))|))
     (29 29 (:REWRITE |(equal (- x) (- y))|))
     (28 28 (:REWRITE |(equal c (- x))|))
     (28 28 (:REWRITE |(equal (- x) c)|))
     (27 27
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (25 25 (:REWRITE |(* c (* d x))|))
     (24 4 (:REWRITE MOD-ZERO . 3))
     (24 4 (:LINEAR MOD-BOUNDS-3))
     (23 23 (:REWRITE |(mod x 2)| . 2))
     (22 22 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (22 22 (:REWRITE |(< y (+ (- c) x))|))
     (22 22 (:REWRITE |(< 0 (* x y))|))
     (21 21 (:REWRITE FOLD-CONSTS-IN-+))
     (20 20
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (20 20
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (18 18 (:REWRITE ZP-OPEN))
     (18 18 (:REWRITE |(< (+ c/d x) y)|))
     (18 18 (:REWRITE |(< (+ (- c) x) y)|))
     (17 2
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (11 11 (:LINEAR EXPT-LINEAR-UPPER-<))
     (11 11 (:LINEAR EXPT-LINEAR-LOWER-<))
     (11 11 (:LINEAR EXPT->=-1-TWO))
     (11 11 (:LINEAR EXPT->-1-TWO))
     (11 11 (:LINEAR EXPT-<=-1-ONE))
     (11 11 (:LINEAR EXPT-<-1-ONE))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:LINEAR MOD-BOUNDS-2))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (4 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (4 4 (:REWRITE MOD-X-Y-=-X . 2))
     (4 4
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE MOD-CANCEL-*-CONST))
     (4 4 (:REWRITE |(mod x (- y))| . 3))
     (4 4 (:REWRITE |(mod x (- y))| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 1))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(mod (- x) y)| . 3))
     (4 4 (:REWRITE |(mod (- x) y)| . 2))
     (4 4 (:REWRITE |(mod (- x) y)| . 1))
     (4 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (4 4
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:LINEAR MOD-BND-3))
     (2 2 (:REWRITE |(equal (expt 2 n) c)|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2 (:REWRITE |(- (- x))|))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|)))
(LEMMA-4-1-19
     (1401 835
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
     (1385 835
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
     (940 940
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
     (903 903
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (903 903
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (903 903
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (835 835
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
     (804 244 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (804 244 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (804 244
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (804 244
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (791 155 (:REWRITE RATIONALP-X))
     (711 93 (:REWRITE ACL2-NUMBERP-X))
     (598 493 (:REWRITE DEFAULT-PLUS-1))
     (383 268 (:REWRITE INTEGERP-MINUS-X))
     (344 175 (:REWRITE SIMPLIFY-SUMS-<))
     (343 343
          (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (313 17
          (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (312 11 (:REWRITE ODD-EXPT-THM))
     (293 17
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (288 43
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (265 5 (:REWRITE CANCEL-MOD-+))
     (263 263 (:REWRITE REDUCE-INTEGERP-+))
     (263 263 (:META META-INTEGERP-CORRECT))
     (258 12 (:LINEAR EXPT-<=-1-TWO))
     (248 184 (:REWRITE |(< c (- x))|))
     (248 182 (:REWRITE CONSTANT-<-INTEGERP))
     (245 245 (:REWRITE THE-FLOOR-BELOW))
     (245 245 (:REWRITE THE-FLOOR-ABOVE))
     (244 244 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (244 244
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (244 244
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (244 244
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (244 244 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (243 160 (:TYPE-PRESCRIPTION NATP-MOD))
     (240 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (233 233 (:REWRITE |(expt 1/c n)|))
     (233 233 (:REWRITE |(expt (- x) n)|))
     (228 218
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (228 218
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (225 225
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (225 225
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (225 225
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (225 225
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (200 200
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (188 28
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (188 28
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (184 184
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (184 184
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (184 184
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (184 184
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (184 184
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (184 184
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (184 184
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (184 184
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (184 184 (:REWRITE |(< (/ x) (/ y))|))
     (184 184 (:REWRITE |(< (- x) (- y))|))
     (182 182
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (182 182 (:REWRITE INTEGERP-<-CONSTANT))
     (182 182 (:REWRITE |(< (- x) c)|))
     (175 5 (:REWRITE MOD-X-Y-=-X . 4))
     (175 5 (:REWRITE MOD-X-Y-=-X . 3))
     (170 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (168 150 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (160 160 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (160 160 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (160 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (155 155 (:REWRITE RATIONALP-MINUS-X))
     (155 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (145 145 (:REWRITE REDUCE-RATIONALP-+))
     (145 145 (:META META-RATIONALP-CORRECT))
     (143 17
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (143 17
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (130 5 (:REWRITE MOD-DOES-NOTHING))
     (120 24 (:LINEAR MOD-BOUNDS-2))
     (117 69 (:REWRITE DEFAULT-MINUS))
     (110 5 (:REWRITE MOD-ZERO . 3))
     (100 25 (:REWRITE |(* (- x) y)|))
     (90 5 (:REWRITE MOD-ZERO . 4))
     (83 83 (:TYPE-PRESCRIPTION NATP))
     (75 75 (:REWRITE DEFAULT-MOD-2))
     (65 65 (:REWRITE |(mod x 2)| . 2))
     (62 62 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (61 61 (:REWRITE |(< (* x y) 0)|))
     (59 59 (:REWRITE |(expt c (* d n))|))
     (55 55 (:REWRITE |(< (/ x) 0)|))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (50 50 (:REWRITE |(< (+ c/d x) y)|))
     (44 44 (:REWRITE |(< (+ (- c) x) y)|))
     (43 43
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (34 34 (:REWRITE |(< x (+ c/d y))|))
     (28 28
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (28 28 (:REWRITE |(equal c (/ x))|))
     (28 28 (:REWRITE |(equal c (- x))|))
     (28 28 (:REWRITE |(equal (/ x) c)|))
     (28 28 (:REWRITE |(equal (/ x) (/ y))|))
     (28 28 (:REWRITE |(equal (- x) c)|))
     (28 28 (:REWRITE |(equal (- x) (- y))|))
     (27 27 (:REWRITE |(< 0 (* x y))|))
     (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (25 5 (:REWRITE MOD-X-Y-=-X . 2))
     (25 5
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (25 5 (:REWRITE MOD-CANCEL-*-CONST))
     (25 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (25 5
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (25 5
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (24 24
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (24 24
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (21 21 (:REWRITE |(* c (* d x))|))
     (20 20 (:TYPE-PRESCRIPTION ABS))
     (17 17 (:REWRITE |(< 0 (/ x))|))
     (16 16 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:LINEAR MOD-BND-3))
     (12 12 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
     (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
     (12 12 (:LINEAR EXPT->=-1-TWO))
     (12 12 (:LINEAR EXPT->-1-TWO))
     (12 12 (:LINEAR EXPT-<=-1-ONE))
     (12 12 (:LINEAR EXPT-<-1-TWO))
     (12 12 (:LINEAR EXPT-<-1-ONE))
     (10 10 (:REWRITE ZP-OPEN))
     (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
     (6 6
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (5 5 (:REWRITE |(mod x (- y))| . 3))
     (5 5 (:REWRITE |(mod x (- y))| . 2))
     (5 5 (:REWRITE |(mod x (- y))| . 1))
     (5 5
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (5 5
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (5 5 (:REWRITE |(mod (- x) y)| . 3))
     (5 5 (:REWRITE |(mod (- x) y)| . 2))
     (5 5 (:REWRITE |(mod (- x) y)| . 1))
     (5 5
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (5 5
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (3 3 (:REWRITE |(equal (expt 2 n) c)|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:REWRITE |(- (- x))|)))
(LEMMA-4-1-20
 (2908
  2908
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2908
      2908
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2908
     2908
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2908 2908
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1384 282
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1128 278 (:REWRITE SIMPLIFY-SUMS-<))
 (753 27 (:REWRITE MOD-X-Y-=-X . 3))
 (675 27 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (648 27 (:REWRITE MOD-DOES-NOTHING))
 (646 296
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (615 27 (:REWRITE MOD-X-Y-=-X . 4))
 (594 27 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (485 23 (:REWRITE ODD-EXPT-THM))
 (464 16
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (460 115 (:REWRITE RATIONALP-X))
 (460 20
      (:REWRITE |(* (expt c m) (expt d n))|))
 (438 330 (:REWRITE INTEGERP-MINUS-X))
 (432 16
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (425 425
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (425 425
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (425 425
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (373 69 (:REWRITE ACL2-NUMBERP-X))
 (351 27 (:REWRITE CANCEL-MOD-+))
 (336 156 (:REWRITE DEFAULT-EXPT-1))
 (330 282 (:REWRITE CONSTANT-<-INTEGERP))
 (328 296
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (328 296
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (322 210 (:TYPE-PRESCRIPTION NATP-MOD))
 (320 80 (:REWRITE |(integerp (- x))|))
 (303 303 (:REWRITE REDUCE-INTEGERP-+))
 (303 303 (:META META-INTEGERP-CORRECT))
 (300 27 (:REWRITE MOD-ZERO . 4))
 (297 297 (:REWRITE THE-FLOOR-BELOW))
 (297 297 (:REWRITE THE-FLOOR-ABOVE))
 (282 282
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (282 282 (:REWRITE INTEGERP-<-CONSTANT))
 (282 282
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (282 282
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (282 282
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (282 282
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (282 282 (:REWRITE |(< c (- x))|))
 (282 282
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (282 282
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (282 282
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (282 282
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (282 282 (:REWRITE |(< (/ x) (/ y))|))
 (282 282 (:REWRITE |(< (- x) c)|))
 (282 282 (:REWRITE |(< (- x) (- y))|))
 (213 213 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (213 213 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (213 213 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (213 213 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (213 213
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (213 213
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (213 213
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (213 213
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (213 213
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (213 213 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (212 212 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (210 210 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (210 210 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (190 58
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (174 66 (:REWRITE |(* (- x) y)|))
 (162 27 (:REWRITE MOD-ZERO . 3))
 (156 156 (:REWRITE |(expt 1/c n)|))
 (156 156 (:REWRITE |(expt (- x) n)|))
 (154 154
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (119 46
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (118 118 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (115 115 (:REWRITE RATIONALP-MINUS-X))
 (112 112 (:TYPE-PRESCRIPTION NATP))
 (112 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (111 46
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (108 27 (:REWRITE |(mod x 2)| . 1))
 (100 20 (:REWRITE |(expt (expt x m) n)|))
 (100 20
      (:REWRITE |(* (expt x n) (expt y n))|))
 (100 20
      (:REWRITE |(* (expt x m) (expt x n))|))
 (83 83 (:REWRITE REDUCE-RATIONALP-+))
 (83 83 (:META META-RATIONALP-CORRECT))
 (80 50 (:REWRITE |(+ c (+ d x))|))
 (80 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (64 64 (:TYPE-PRESCRIPTION ABS))
 (58 58
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (51 51 (:REWRITE DEFAULT-MOD-2))
 (46 46
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 46 (:REWRITE |(equal c (/ x))|))
 (46 46 (:REWRITE |(equal c (- x))|))
 (46 46 (:REWRITE |(equal (/ x) c)|))
 (46 46 (:REWRITE |(equal (/ x) (/ y))|))
 (46 46 (:REWRITE |(equal (- x) c)|))
 (46 46 (:REWRITE |(equal (- x) (- y))|))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (42 42 (:REWRITE |(< (/ x) 0)|))
 (42 42 (:REWRITE |(< (* x y) 0)|))
 (38 38 (:REWRITE ZP-OPEN))
 (36 36 (:REWRITE |(expt c (* d n))|))
 (35 35 (:REWRITE |(< 0 (* x y))|))
 (30 30 (:REWRITE |(* c (* d x))|))
 (28 28 (:REWRITE |(< x (+ c/d y))|))
 (27 27 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (27 27 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (27 27 (:REWRITE MOD-X-Y-=-X . 2))
 (27 27
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (27 27
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (27 27 (:REWRITE MOD-CANCEL-*-CONST))
 (27 27 (:REWRITE |(mod x 2)| . 2))
 (27 27 (:REWRITE |(mod x (- y))| . 3))
 (27 27 (:REWRITE |(mod x (- y))| . 2))
 (27 27 (:REWRITE |(mod x (- y))| . 1))
 (27 27
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (27 27
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (27 27 (:REWRITE |(mod (- x) y)| . 3))
 (27 27 (:REWRITE |(mod (- x) y)| . 2))
 (27 27 (:REWRITE |(mod (- x) y)| . 1))
 (27 27 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (27 27
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (27 27
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (27 27
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (21 21 (:REWRITE |(< 0 (/ x))|))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (16 16
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (13 13 (:REWRITE |(equal (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:REWRITE |(equal (mod (+ x y) z) x)|)))
(LEMMA-4-1-21
     (3443 3443
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
     (3443 3443
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
     (3443 3443
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
     (3052 109 (:REWRITE MOD-X-Y-=-X . 4))
     (3052 109 (:REWRITE MOD-X-Y-=-X . 3))
     (2943 109 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (2616 109 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2507 109 (:REWRITE MOD-DOES-NOTHING))
     (2441 1995 (:REWRITE INTEGERP-MINUS-X))
     (2270 342 (:REWRITE ACL2-NUMBERP-X))
     (2220 1590 (:REWRITE SIMPLIFY-SUMS-<))
     (2183 1688 (:REWRITE |(< c (- x))|))
     (2128 532 (:REWRITE |(integerp (- x))|))
     (2103 1668 (:REWRITE |(< (- x) c)|))
     (1947 1821
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1947 1821
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1886 1886 (:REWRITE REDUCE-INTEGERP-+))
     (1886 1886 (:META META-INTEGERP-CORRECT))
     (1841 1652 (:REWRITE CONSTANT-<-INTEGERP))
     (1825 1825 (:REWRITE THE-FLOOR-BELOW))
     (1825 1825 (:REWRITE THE-FLOOR-ABOVE))
     (1764 63
           (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (1721 1688 (:REWRITE |(< (- x) (- y))|))
     (1715 1688
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1703 1652 (:REWRITE INTEGERP-<-CONSTANT))
     (1700 1688
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1688 1688
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1688 1688
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1688 1688
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1688 1688
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1688 1688
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1688 1688
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1688 1688 (:REWRITE |(< (/ x) (/ y))|))
     (1659 371
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1638 63
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (1526 109 (:REWRITE MOD-ZERO . 4))
     (1417 109 (:REWRITE CANCEL-MOD-+))
     (1335 786 (:TYPE-PRESCRIPTION NATP-MOD))
     (1238 1171 (:REWRITE DEFAULT-EXPT-1))
     (1167 1167 (:REWRITE |(expt (- x) n)|))
     (1128 36 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1062 1062
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1015 1015 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1015 1015 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1015 1015 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1015 1015 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1015 1015
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1015 1015
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1015 1015
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1015 1015
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1015 1015
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1015 1015
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (828 243
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (820 243
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (786 786 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (786 786 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (752 744 (:REWRITE RATIONALP-MINUS-X))
     (720 36 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (700 140
          (:REWRITE |(* (expt x m) (expt x n))|))
     (654 109 (:REWRITE MOD-ZERO . 3))
     (577 577 (:META META-RATIONALP-CORRECT))
     (549 549 (:TYPE-PRESCRIPTION NATP))
     (470 94
          (:REWRITE |(* (expt x n) (expt y n))|))
     (404 404 (:REWRITE DEFAULT-MOD-2))
     (371 371
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (357 357 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (354 98
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (345 345 (:REWRITE |(< (* x y) 0)|))
     (322 322 (:REWRITE |(< (/ x) 0)|))
     (308 308
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (308 308
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (286 208 (:REWRITE |(< 0 (/ x))|))
     (280 280 (:REWRITE |(mod x 2)| . 2))
     (280 280 (:REWRITE |(< 0 (* x y))|))
     (252 252 (:TYPE-PRESCRIPTION ABS))
     (243 243
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (243 243 (:REWRITE |(equal c (/ x))|))
     (243 243 (:REWRITE |(equal c (- x))|))
     (243 243 (:REWRITE |(equal (/ x) c)|))
     (243 243 (:REWRITE |(equal (/ x) (/ y))|))
     (243 243 (:REWRITE |(equal (- x) c)|))
     (243 243 (:REWRITE |(equal (- x) (- y))|))
     (197 197
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (197 197
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (152 152 (:REWRITE |(* c (* d x))|))
     (136 136 (:REWRITE ZP-OPEN))
     (127 127 (:REWRITE |(< (+ c/d x) y)|))
     (126 126 (:REWRITE |(< y (+ (- c) x))|))
     (122 8
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (122 8
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (122 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (122 8 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (110 110
          (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (110 110
          (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (109 109
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (109 109 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (109 109 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (109 109 (:REWRITE MOD-X-Y-=-X . 2))
     (109 109
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (109 109
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (109 109 (:REWRITE MOD-CANCEL-*-CONST))
     (109 109 (:REWRITE |(mod x (- y))| . 3))
     (109 109 (:REWRITE |(mod x (- y))| . 2))
     (109 109 (:REWRITE |(mod x (- y))| . 1))
     (109 109
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (109 109
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (109 109 (:REWRITE |(mod (- x) y)| . 3))
     (109 109 (:REWRITE |(mod (- x) y)| . 2))
     (109 109 (:REWRITE |(mod (- x) y)| . 1))
     (109 109
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (109 109
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (109 109
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (109 109
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (92 46 (:REWRITE COLLECT-*-PROBLEM-FINDER))
     (86 86 (:LINEAR MOD-BOUNDS-2))
     (75 75 (:REWRITE FOLD-CONSTS-IN-+))
     (64 64
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (63 63
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (63 63
         (:REWRITE |(< (/ x) y) with (< x 0)|))
     (60 60
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (55 55 (:LINEAR EXPT-LINEAR-UPPER-<))
     (55 55 (:LINEAR EXPT-LINEAR-LOWER-<))
     (55 55 (:LINEAR EXPT->=-1-TWO))
     (55 55 (:LINEAR EXPT->-1-TWO))
     (55 55 (:LINEAR EXPT-<=-1-ONE))
     (55 55 (:LINEAR EXPT-<-1-ONE))
     (46 46
         (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
     (38 38 (:LINEAR MOD-BND-3))
     (36 36
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (36 36 (:REWRITE |(- (- x))|))
     (26 26 (:REWRITE |(equal (+ (- c) x) y)|)))
(LEMMA-4-1-22
 (6700 112 (:REWRITE ACL2-NUMBERP-X))
 (3900
  3900
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3900
      3900
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3900
     3900
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3900 3900
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3652 142 (:REWRITE RATIONALP-X))
 (2044 179 (:REWRITE DEFAULT-LESS-THAN-2))
 (1067 320
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (936 936
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (936 936
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (653 306 (:REWRITE DEFAULT-PLUS-1))
 (487 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (487 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (487 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (487 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (483 16 (:REWRITE ODD-EXPT-THM))
 (443 282 (:REWRITE INTEGERP-MINUS-X))
 (427 155 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (427 155 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (371 7 (:REWRITE CANCEL-MOD-+))
 (363 155
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (363 155
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (320 320
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (292 137
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (275 275 (:REWRITE REDUCE-INTEGERP-+))
 (275 275 (:META META-INTEGERP-CORRECT))
 (252 124 (:REWRITE DEFAULT-MINUS))
 (245 7 (:REWRITE MOD-X-Y-=-X . 4))
 (245 7 (:REWRITE MOD-X-Y-=-X . 3))
 (238 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (236 83 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (228 132 (:REWRITE |(< c (- x))|))
 (223 155 (:TYPE-PRESCRIPTION NATP-MOD))
 (217 7 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (182 7 (:REWRITE MOD-DOES-NOTHING))
 (179 179 (:REWRITE THE-FLOOR-BELOW))
 (179 179 (:REWRITE THE-FLOOR-ABOVE))
 (177 30
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (168 132 (:REWRITE |(< (- x) (- y))|))
 (155 155 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (155 155 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (155 155 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (155 155
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (155 155
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (155 155
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (155 155 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (155 155 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (155 155 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (154 7 (:REWRITE MOD-ZERO . 3))
 (149 129 (:REWRITE INTEGERP-<-CONSTANT))
 (144 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (143 137
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (143 137
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (142 142 (:REWRITE RATIONALP-MINUS-X))
 (138 129 (:REWRITE CONSTANT-<-INTEGERP))
 (132 132
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (132 132
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (132 132
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (132 132
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (132 132
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (132 132
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (132 132
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (132 132
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (132 132 (:REWRITE |(< (/ x) (/ y))|))
 (129 129
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (129 129 (:REWRITE |(< (- x) c)|))
 (129 24 (:REWRITE |(* (- x) y)|))
 (128 128 (:META META-RATIONALP-CORRECT))
 (126 7 (:REWRITE MOD-ZERO . 4))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (117 21
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (117 21
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (112 112 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (105 105 (:REWRITE DEFAULT-EXPT-1))
 (105 3
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (96 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (94 94 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (93 3 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (82 82
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (68 68 (:TYPE-PRESCRIPTION NATP))
 (57 57 (:REWRITE |(expt 1/c n)|))
 (57 57 (:REWRITE |(expt (- x) n)|))
 (44 4
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (44 4
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (44 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (44 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (35 7 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (35 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (35 7 (:REWRITE MOD-X-Y-=-X . 2))
 (35 7
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (35 7 (:REWRITE MOD-CANCEL-*-CONST))
 (35 7 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (35 7
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (35 7
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (33 33 (:REWRITE |(< 0 (* x y))|))
 (30 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (28 28 (:REWRITE |(< 0 (/ x))|))
 (28 7 (:REWRITE |(mod x 2)| . 1))
 (27 27 (:REWRITE |(< (+ c/d x) y)|))
 (27 27 (:REWRITE |(< (+ (- c) x) y)|))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (21 21
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (21 21 (:REWRITE |(equal c (/ x))|))
 (21 21 (:REWRITE |(equal c (- x))|))
 (21 21 (:REWRITE |(equal (/ x) c)|))
 (21 21 (:REWRITE |(equal (/ x) (/ y))|))
 (21 21 (:REWRITE |(equal (- x) c)|))
 (21 21 (:REWRITE |(equal (- x) (- y))|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (13 13 (:REWRITE DEFAULT-MOD-2))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 7
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (7 7 (:REWRITE |(mod x 2)| . 2))
 (7 7 (:REWRITE |(mod x (- y))| . 3))
 (7 7 (:REWRITE |(mod x (- y))| . 2))
 (7 7 (:REWRITE |(mod x (- y))| . 1))
 (7 7
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (7 7
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (7 7 (:REWRITE |(mod (- x) y)| . 3))
 (7 7 (:REWRITE |(mod (- x) y)| . 2))
 (7 7 (:REWRITE |(mod (- x) y)| . 1))
 (7 7
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (7 7 (:REWRITE |(* c (* d x))|))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE |(expt c (* d n))|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (3 3
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (3 3 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE |(- (- x))|)))
(LEMMA-4-1-23
 (11391
  11391
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11391
      11391
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11391
     11391
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11391 11391
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2825 2825
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2825 2825
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2825 2825
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2459 938
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (2281 324 (:REWRITE DEFAULT-LESS-THAN-2))
 (2193 187 (:REWRITE RATIONALP-X))
 (1420 340 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1420 340 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1287 423 (:REWRITE DEFAULT-PLUS-1))
 (1252 1252
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1252 1252
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1252 1252
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1252 1252
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1230 1230
       (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1007 19 (:REWRITE CANCEL-MOD-+))
 (956 28 (:LINEAR MOD-BOUNDS-2))
 (938 938
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (857 357 (:REWRITE INTEGERP-MINUS-X))
 (732 340
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (732 340
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (690 82 (:REWRITE ACL2-NUMBERP-X))
 (665 19 (:REWRITE MOD-X-Y-=-X . 4))
 (665 19 (:REWRITE MOD-X-Y-=-X . 3))
 (646 19 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (637 12
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (596 333 (:TYPE-PRESCRIPTION NATP-MOD))
 (592 12
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (590 311
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (589 19 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (547 547
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (547 547
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (547 547
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (547 547
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (527 86
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (516 17 (:REWRITE ODD-EXPT-THM))
 (494 19 (:REWRITE MOD-DOES-NOTHING))
 (491 168 (:REWRITE DEFAULT-MINUS))
 (458 302
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (434 14 (:LINEAR MOD-BND-2))
 (432 9 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (418 19 (:REWRITE MOD-ZERO . 3))
 (407 302 (:REWRITE CONSTANT-<-INTEGERP))
 (381 302 (:REWRITE INTEGERP-<-CONSTANT))
 (368 340 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (355 70 (:REWRITE |(* (- x) y)|))
 (347 59
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (347 59
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (342 19 (:REWRITE MOD-ZERO . 4))
 (340 340 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (340 340
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (340 340
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (340 340
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (340 340 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (338 338 (:REWRITE REDUCE-INTEGERP-+))
 (338 338 (:META META-INTEGERP-CORRECT))
 (333 333 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (333 333 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (333 311
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (333 311
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (329 302 (:REWRITE |(< (- x) (- y))|))
 (324 324 (:REWRITE THE-FLOOR-BELOW))
 (324 324 (:REWRITE THE-FLOOR-ABOVE))
 (316 93 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (311 302 (:REWRITE |(< (- x) c)|))
 (308 14 (:LINEAR MOD-BOUNDS-3))
 (302 302
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (302 302
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (302 302
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (302 302
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (302 302 (:REWRITE |(< c (- x))|))
 (302 302
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (302 302
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (302 302
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (302 302
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (302 302 (:REWRITE |(< (/ x) (/ y))|))
 (288 9 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (263 263 (:TYPE-PRESCRIPTION NATP))
 (237 237 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (223 187 (:REWRITE RATIONALP-MINUS-X))
 (196 10 (:LINEAR EXPT-<=-1-TWO))
 (195 195 (:REWRITE DEFAULT-EXPT-1))
 (177 177 (:REWRITE |(expt 1/c n)|))
 (177 177 (:REWRITE |(expt (- x) n)|))
 (177 60 (:REWRITE |(+ c (+ d x))|))
 (175 175
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (168 168 (:REWRITE REDUCE-RATIONALP-+))
 (168 168 (:META META-RATIONALP-CORRECT))
 (160 1
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (160 1
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (160 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (160 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (130 10 (:LINEAR EXPT-<=-1-ONE))
 (126 10 (:LINEAR EXPT->=-1-TWO))
 (126 10 (:LINEAR EXPT->-1-TWO))
 (126 10 (:LINEAR EXPT-<-1-ONE))
 (110 10 (:LINEAR EXPT-<-1-TWO))
 (95 19 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (95 19 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (95 19 (:REWRITE MOD-X-Y-=-X . 2))
 (95 19
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (95 19 (:REWRITE MOD-CANCEL-*-CONST))
 (95 19 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (95 19
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (95 19
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (86 86
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (76 19 (:REWRITE |(mod x 2)| . 1))
 (60 2
     (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (59 59
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (59 59 (:REWRITE |(equal c (/ x))|))
 (59 59 (:REWRITE |(equal c (- x))|))
 (59 59 (:REWRITE |(equal (/ x) c)|))
 (59 59 (:REWRITE |(equal (/ x) (/ y))|))
 (59 59 (:REWRITE |(equal (- x) c)|))
 (59 59 (:REWRITE |(equal (- x) (- y))|))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (57 57 (:REWRITE |(< (/ x) 0)|))
 (57 57 (:REWRITE |(< (* x y) 0)|))
 (54 2
     (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (51 51 (:REWRITE |(< 0 (* x y))|))
 (44 44 (:TYPE-PRESCRIPTION ABS))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (42 42 (:REWRITE |(< 0 (/ x))|))
 (39 39 (:REWRITE |(expt c (* d n))|))
 (29 29 (:REWRITE DEFAULT-MOD-2))
 (28 7 (:REWRITE |(integerp (expt x n))|))
 (27 27 (:REWRITE |(* c (* d x))|))
 (26 26 (:REWRITE ZP-OPEN))
 (25 25 (:REWRITE |(< x (+ c/d y))|))
 (25 12
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (25 12
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (24 2 (:REWRITE |(* x (expt x n))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (19 19
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (19 19 (:REWRITE |(mod x 2)| . 2))
 (19 19 (:REWRITE |(mod x (- y))| . 3))
 (19 19 (:REWRITE |(mod x (- y))| . 2))
 (19 19 (:REWRITE |(mod x (- y))| . 1))
 (19 19
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (19 19
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (19 19 (:REWRITE |(mod (- x) y)| . 3))
 (19 19 (:REWRITE |(mod (- x) y)| . 2))
 (19 19 (:REWRITE |(mod (- x) y)| . 1))
 (19 19
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (18 2
     (:REWRITE |(< (expt x n) (expt x m))|))
 (16 16 (:REWRITE |(< y (+ (- c) x))|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (14 14 (:LINEAR MOD-BND-3))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (9 1 (:REWRITE |(equal (expt x n) 0)|))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2
    (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(LEMMA-4-1-24
     (1489 739
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1486 308 (:REWRITE RATIONALP-X))
     (1234 1234
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1102 38 (:REWRITE MOD-X-Y-=-X . 4))
     (1102 38 (:REWRITE MOD-X-Y-=-X . 3))
     (1064 38 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1062 198 (:REWRITE ACL2-NUMBERP-X))
     (950 38 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (914 752 (:REWRITE INTEGERP-MINUS-X))
     (912 38 (:REWRITE MOD-DOES-NOTHING))
     (906 60 (:REWRITE ODD-EXPT-THM))
     (900 216 (:REWRITE |(integerp (- x))|))
     (797 709 (:REWRITE |(< (- x) (- y))|))
     (787 739
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (787 739
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (781 709 (:REWRITE CONSTANT-<-INTEGERP))
     (759 759 (:REWRITE |(* c (* d x))|))
     (739 739 (:REWRITE THE-FLOOR-BELOW))
     (739 739 (:REWRITE THE-FLOOR-ABOVE))
     (719 709 (:REWRITE |(< (- x) c)|))
     (714 714 (:REWRITE REDUCE-INTEGERP-+))
     (714 714 (:META META-INTEGERP-CORRECT))
     (709 709
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (709 709 (:REWRITE INTEGERP-<-CONSTANT))
     (709 709
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (709 709
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (709 709
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (709 709
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (709 709 (:REWRITE |(< c (- x))|))
     (709 709
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (709 709
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (709 709
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (709 709
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (709 709 (:REWRITE |(< (/ x) (/ y))|))
     (696 24
          (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (648 24
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (609 609 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (532 38 (:REWRITE MOD-ZERO . 4))
     (494 38 (:REWRITE CANCEL-MOD-+))
     (443 273 (:TYPE-PRESCRIPTION NATP-MOD))
     (389 125
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (309 309 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (309 309 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (309 309 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (309 309 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (309 309
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (309 309
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (309 309
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (309 309
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (309 309
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (309 309 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (306 296 (:REWRITE RATIONALP-MINUS-X))
     (273 273 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (273 273 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (270 270 (:REWRITE FOLD-CONSTS-IN-+))
     (257 59
          (:REWRITE |(* (expt x m) (expt x n))|))
     (241 101
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (241 101
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (234 234 (:REWRITE |(< x (+ c/d y))|))
     (228 228 (:META META-RATIONALP-CORRECT))
     (228 38 (:REWRITE MOD-ZERO . 3))
     (224 8 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (210 210 (:REWRITE |(< (+ c/d x) y)|))
     (210 210 (:REWRITE |(< (+ (- c) x) y)|))
     (210 12 (:LINEAR EXPT-<=-1-TWO))
     (204 204 (:REWRITE |(< y (+ (- c) x))|))
     (170 170 (:TYPE-PRESCRIPTION NATP))
     (160 8 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (152 38 (:REWRITE |(mod x 2)| . 1))
     (150 54 (:REWRITE |(* x (expt x n))|))
     (148 74 (:REWRITE COLLECT-*-PROBLEM-FINDER))
     (142 142 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (125 125
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (101 101
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (101 101 (:REWRITE |(equal c (/ x))|))
     (101 101 (:REWRITE |(equal c (- x))|))
     (101 101 (:REWRITE |(equal (/ x) c)|))
     (101 101 (:REWRITE |(equal (/ x) (/ y))|))
     (101 101 (:REWRITE |(equal (- x) c)|))
     (101 101 (:REWRITE |(equal (- x) (- y))|))
     (98 98 (:REWRITE |(< 0 (* x y))|))
     (96 96 (:TYPE-PRESCRIPTION ABS))
     (92 92 (:REWRITE DEFAULT-MOD-2))
     (88 88 (:REWRITE |(< (/ x) 0)|))
     (88 88 (:REWRITE |(< (* x y) 0)|))
     (76 76
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (76 76
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (74 74
         (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
     (72 72 (:REWRITE |(expt (- c) n)|))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (68 68 (:REWRITE |(< 0 (/ x))|))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (48 48 (:REWRITE ZP-OPEN))
     (38 38 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (38 38 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (38 38 (:REWRITE MOD-X-Y-=-X . 2))
     (38 38
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (38 38
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (38 38 (:REWRITE MOD-CANCEL-*-CONST))
     (38 38 (:REWRITE |(mod x 2)| . 2))
     (38 38 (:REWRITE |(mod x (- y))| . 3))
     (38 38 (:REWRITE |(mod x (- y))| . 2))
     (38 38 (:REWRITE |(mod x (- y))| . 1))
     (38 38
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (38 38
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (38 38 (:REWRITE |(mod (- x) y)| . 3))
     (38 38 (:REWRITE |(mod (- x) y)| . 2))
     (38 38 (:REWRITE |(mod (- x) y)| . 1))
     (38 38 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (38 38
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (38 38
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (38 38
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (24 24
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (24 24
         (:REWRITE |(< (/ x) y) with (< x 0)|))
     (23 23 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 12 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
     (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
     (12 12
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (12 12
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (12 12 (:LINEAR EXPT->=-1-TWO))
     (12 12 (:LINEAR EXPT->-1-TWO))
     (12 12 (:LINEAR EXPT-<=-1-ONE))
     (12 12 (:LINEAR EXPT-<-1-TWO))
     (12 12 (:LINEAR EXPT-<-1-ONE))
     (10 10
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (8 8
        (:REWRITE |(equal (mod (+ x y) z) x)|)))
(LEMMA-4-1-25
 (3630
  3630
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3630
      3630
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3630
     3630
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3630 3630
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3630 3630
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1480 131 (:REWRITE DEFAULT-LESS-THAN-2))
 (924 924
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (924 924
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (924 924
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (697 220
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (650 6 (:LINEAR MOD-BND-1))
 (635 635
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (635 635
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (635 635
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (635 635
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (604 132 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (604 132 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (583 11 (:REWRITE CANCEL-MOD-+))
 (571 116
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (568 76 (:REWRITE RATIONALP-X))
 (487 487
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (420 115 (:REWRITE SIMPLIFY-SUMS-<))
 (401 148 (:REWRITE INTEGERP-MINUS-X))
 (398 46 (:REWRITE ACL2-NUMBERP-X))
 (385 11 (:REWRITE MOD-X-Y-=-X . 4))
 (385 11 (:REWRITE MOD-X-Y-=-X . 3))
 (380 132 (:REWRITE DEFAULT-PLUS-1))
 (374 11 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (356 132
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (356 132
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (341 11 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (332 12 (:LINEAR MOD-BOUNDS-2))
 (290 45
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (286 11 (:REWRITE MOD-DOES-NOTHING))
 (250 132 (:TYPE-PRESCRIPTION NATP-MOD))
 (242 11 (:REWRITE MOD-ZERO . 3))
 (240 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (227 227
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (227 227
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (227 227
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (227 227
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (220 220
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (198 11 (:REWRITE MOD-ZERO . 4))
 (190 30
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (190 30
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (186 6 (:LINEAR MOD-BND-2))
 (162 47 (:REWRITE DEFAULT-MINUS))
 (160 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (158 80 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (149 118
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (137 137 (:REWRITE REDUCE-INTEGERP-+))
 (137 137 (:META META-INTEGERP-CORRECT))
 (132 132 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (132 132 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (132 132 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (132 132
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (132 132
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (132 132
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (132 132 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (132 132 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (132 132 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (132 6 (:LINEAR MOD-BOUNDS-3))
 (131 131 (:REWRITE THE-FLOOR-BELOW))
 (131 131 (:REWRITE THE-FLOOR-ABOVE))
 (123 117 (:REWRITE CONSTANT-<-INTEGERP))
 (122 118
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (122 118
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (118 118 (:TYPE-PRESCRIPTION NATP))
 (117 117 (:REWRITE INTEGERP-<-CONSTANT))
 (117 117
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (117 117
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (117 117
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (117 117
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (117 117 (:REWRITE |(< c (- x))|))
 (117 117
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (117 117
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (117 117
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (117 117
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (117 117 (:REWRITE |(< (/ x) (/ y))|))
 (117 117 (:REWRITE |(< (- x) c)|))
 (117 117 (:REWRITE |(< (- x) (- y))|))
 (76 76 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (76 76 (:REWRITE RATIONALP-MINUS-X))
 (75 22 (:REWRITE |(+ c (+ d x))|))
 (73 42 (:REWRITE DEFAULT-EXPT-1))
 (70 70 (:REWRITE REDUCE-RATIONALP-+))
 (70 70 (:META META-RATIONALP-CORRECT))
 (70 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (62 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (62 2 (:LINEAR EXPT-<=-1-ONE))
 (60 2 (:LINEAR EXPT->=-1-TWO))
 (60 2 (:LINEAR EXPT->-1-TWO))
 (60 2 (:LINEAR EXPT-<-1-ONE))
 (55 11 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (55 11 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (55 11 (:REWRITE MOD-X-Y-=-X . 2))
 (55 11
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (55 11 (:REWRITE MOD-CANCEL-*-CONST))
 (55 11 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (55 11
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (55 11
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (54 2 (:LINEAR EXPT-X->=-X))
 (54 2 (:LINEAR EXPT->=-1-ONE))
 (54 2 (:LINEAR EXPT-<=-1-TWO))
 (52 2 (:LINEAR EXPT-X->-X))
 (52 2 (:LINEAR EXPT->-1-ONE))
 (52 2 (:LINEAR EXPT-<-1-TWO))
 (49 49
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (48 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (45 45
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (44 11 (:REWRITE |(mod x 2)| . 1))
 (43 2 (:REWRITE ODD-EXPT-THM))
 (36 36 (:REWRITE |(expt (- x) n)|))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (31 31 (:REWRITE |(< (/ x) 0)|))
 (31 31 (:REWRITE |(< (* x y) 0)|))
 (30 30
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (30 30 (:REWRITE |(equal c (/ x))|))
 (30 30 (:REWRITE |(equal c (- x))|))
 (30 30 (:REWRITE |(equal (/ x) c)|))
 (30 30 (:REWRITE |(equal (/ x) (/ y))|))
 (30 30 (:REWRITE |(equal (- x) c)|))
 (30 30 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:REWRITE |(< 0 (* x y))|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< 0 (/ x))|))
 (15 15 (:REWRITE DEFAULT-MOD-2))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (11 11 (:REWRITE |(mod x 2)| . 2))
 (11 11 (:REWRITE |(mod x (- y))| . 3))
 (11 11 (:REWRITE |(mod x (- y))| . 2))
 (11 11 (:REWRITE |(mod x (- y))| . 1))
 (11 11
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (11 11
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (11 11 (:REWRITE |(mod (- x) y)| . 3))
 (11 11 (:REWRITE |(mod (- x) y)| . 2))
 (11 11 (:REWRITE |(mod (- x) y)| . 1))
 (11 11
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (6 6 (:LINEAR MOD-BND-3))
 (5 5
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (2 2
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(LEMMA-4-1-26)
(LEMMA-4-1-27
     (18848 1920 (:REWRITE RATIONALP-X))
     (15157 1602 (:REWRITE REDUCE-RATIONALP-+))
     (15157 1602 (:META META-RATIONALP-CORRECT))
     (8114 1864 (:REWRITE RATIONALP-MINUS-X))
     (7306 4421 (:META META-INTEGERP-CORRECT))
     (6636 4614 (:REWRITE INTEGERP-MINUS-X))
     (6540 392 (:DEFINITION RFIX))
     (5148 292 (:REWRITE |(equal (expt x n) 0)|))
     (4931 1046 (:REWRITE |(integerp (expt x n))|))
     (4800 52 (:REWRITE |(rationalp (- x))|))
     (4421 4421 (:REWRITE REDUCE-INTEGERP-+))
     (4253 1911
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4194 990 (:REWRITE |(integerp (- x))|))
     (3388 121 (:REWRITE MOD-X-Y-=-X . 4))
     (3388 121 (:REWRITE MOD-X-Y-=-X . 3))
     (3267 121 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (3224 559 (:REWRITE ACL2-NUMBERP-X))
     (2904 121 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2783 121 (:REWRITE MOD-DOES-NOTHING))
     (2726 2726
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2304 951
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2154 1914
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2100 75
           (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (2061 1911
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2022 1797 (:REWRITE CONSTANT-<-INTEGERP))
     (1914 1914 (:REWRITE THE-FLOOR-BELOW))
     (1914 1914 (:REWRITE THE-FLOOR-ABOVE))
     (1884 1800 (:REWRITE |(< (- x) c)|))
     (1864 1800
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1839 1797 (:REWRITE INTEGERP-<-CONSTANT))
     (1814 1800 (:REWRITE |(< (- x) (- y))|))
     (1806 1800
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1800 1800
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1800 1800
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1800 1800
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1800 1800 (:REWRITE |(< c (- x))|))
     (1800 1800
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1800 1800
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1800 1800
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1800 1800 (:REWRITE |(< (/ x) (/ y))|))
     (1788 100 (:REWRITE ODD-EXPT-THM))
     (1694 121 (:REWRITE MOD-ZERO . 4))
     (1573 121 (:REWRITE CANCEL-MOD-+))
     (1484 788
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1484 788
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1397 819 (:TYPE-PRESCRIPTION NATP-MOD))
     (1184 1184 (:REWRITE |(* c (* d x))|))
     (1148 41 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (951 951
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (906 906 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (906 906 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (906 906 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (906 906 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (906 906
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (906 906
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (906 906
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (906 906
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (906 906
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (906 906 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (836 828 (:REWRITE |(equal (/ x) c)|))
     (828 828 (:REWRITE |(equal c (/ x))|))
     (828 828 (:REWRITE |(equal (/ x) (/ y))|))
     (828 828 (:REWRITE |(equal (- x) (- y))|))
     (824 824 (:REWRITE |(equal c (- x))|))
     (824 824 (:REWRITE |(equal (- x) c)|))
     (820 41 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (819 819 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (819 819 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (795 159
          (:REWRITE |(* (expt x m) (expt x n))|))
     (788 788
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (726 121 (:REWRITE MOD-ZERO . 3))
     (585 585
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (578 578 (:TYPE-PRESCRIPTION NATP))
     (541 541 (:REWRITE FOLD-CONSTS-IN-+))
     (531 531 (:REWRITE |(< x (+ c/d y))|))
     (476 28 (:LINEAR EXPT-<=-1-TWO))
     (437 437 (:REWRITE |(< y (+ (- c) x))|))
     (409 409 (:REWRITE DEFAULT-MOD-2))
     (351 147 (:REWRITE |(* x (expt x n))|))
     (310 310 (:REWRITE |(< (+ c/d x) y)|))
     (307 307 (:REWRITE |(< (+ (- c) x) y)|))
     (304 304 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (303 303 (:TYPE-PRESCRIPTION ABS))
     (300 150 (:REWRITE COLLECT-*-PROBLEM-FINDER))
     (248 248 (:REWRITE |(< (* x y) 0)|))
     (247 247 (:REWRITE |(mod x 2)| . 2))
     (245 245 (:REWRITE |(< (/ x) 0)|))
     (242 242
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (242 242
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (205 205 (:REWRITE |(expt (- c) n)|))
     (190 190 (:REWRITE |(< 0 (* x y))|))
     (170 170 (:REWRITE ZP-OPEN))
     (168 28 (:LINEAR MOD-BOUNDS-3))
     (150 150
          (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
     (124 124
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (124 124
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (124 124 (:REWRITE |(< 0 (/ x))|))
     (121 121 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (121 121 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (121 121 (:REWRITE MOD-X-Y-=-X . 2))
     (121 121
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (121 121
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (121 121 (:REWRITE MOD-CANCEL-*-CONST))
     (121 121 (:REWRITE |(mod x (- y))| . 3))
     (121 121 (:REWRITE |(mod x (- y))| . 2))
     (121 121 (:REWRITE |(mod x (- y))| . 1))
     (121 121
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (121 121
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (121 121 (:REWRITE |(mod (- x) y)| . 3))
     (121 121 (:REWRITE |(mod (- x) y)| . 2))
     (121 121 (:REWRITE |(mod (- x) y)| . 1))
     (121 121
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (121 121
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (121 121
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (121 121
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (105 7
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (105 7
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (105 7 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (105 7 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (89 89
         (:REWRITE |(< (/ x) y) with (< x 0)|))
     (80 80 (:REWRITE |(equal (+ (- c) x) y)|))
     (75 75
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (65 53
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (56 56 (:LINEAR MOD-BOUNDS-2))
     (56 56
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (56 56
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (41 41
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (28 28 (:LINEAR MOD-BND-3))
     (28 28 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (28 28 (:LINEAR EXPT-LINEAR-UPPER-<))
     (28 28 (:LINEAR EXPT-LINEAR-LOWER-<))
     (28 28 (:LINEAR EXPT->=-1-TWO))
     (28 28 (:LINEAR EXPT->-1-TWO))
     (28 28 (:LINEAR EXPT-<=-1-ONE))
     (28 28 (:LINEAR EXPT-<-1-TWO))
     (28 28 (:LINEAR EXPT-<-1-ONE))
     (15 3 (:REWRITE |(* (- c) (expt c n))|))
     (4 4 (:REWRITE DEFAULT-DIVIDE))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(/ (/ x))|))
     (3 3
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(LEMMA-4-1-B-1
     (731 333
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (698 698 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (698 698 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (698 698 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (698 698 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (698 698
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (698 698
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (698 698
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (698 698
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (698 698
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (698 698 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (500 500
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (456 27 (:REWRITE ODD-EXPT-THM))
     (383 302
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (377 13
          (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (359 333
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (359 333
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (341 302 (:REWRITE CONSTANT-<-INTEGERP))
     (341 302
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (333 333 (:REWRITE THE-FLOOR-BELOW))
     (333 333 (:REWRITE THE-FLOOR-ABOVE))
     (325 302 (:REWRITE INTEGERP-<-CONSTANT))
     (308 302 (:REWRITE |(< (- x) (- y))|))
     (307 302 (:REWRITE |(< (- x) c)|))
     (302 302
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (302 302
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (302 302
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (302 302 (:REWRITE |(< c (- x))|))
     (302 302
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (302 302
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (302 302
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (302 302 (:REWRITE |(< (/ x) (/ y))|))
     (254 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (150 50 (:REWRITE DEFAULT-MOD-RATIO))
     (136 136 (:REWRITE |(* c (* d x))|))
     (107 107 (:REWRITE |(< x (+ c/d y))|))
     (106 106 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (106 106 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (106 106 (:TYPE-PRESCRIPTION NATP-MOD))
     (106 106 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (97 96 (:REWRITE INTEGERP-MINUS-X))
     (96 96 (:REWRITE REDUCE-INTEGERP-+))
     (96 96 (:REWRITE FOLD-CONSTS-IN-+))
     (96 96 (:META META-INTEGERP-CORRECT))
     (91 91 (:REWRITE |(< y (+ (- c) x))|))
     (57 57 (:REWRITE |(< (+ c/d x) y)|))
     (57 57 (:REWRITE |(< (+ (- c) x) y)|))
     (52 52 (:TYPE-PRESCRIPTION ABS))
     (52 13 (:REWRITE RATIONALP-X))
     (50 50 (:REWRITE DEFAULT-MOD-2))
     (50 50 (:REWRITE DEFAULT-MOD-1))
     (50 50 (:REWRITE |(mod x 2)| . 2))
     (27 27
         (:REWRITE |(< (/ x) y) with (< x 0)|))
     (26 26 (:REWRITE ZP-OPEN))
     (18 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (18 18
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 18
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (18 18 (:REWRITE |(equal c (/ x))|))
     (18 18 (:REWRITE |(equal c (- x))|))
     (18 18 (:REWRITE |(equal (/ x) c)|))
     (18 18 (:REWRITE |(equal (/ x) (/ y))|))
     (18 18 (:REWRITE |(equal (- x) c)|))
     (18 18 (:REWRITE |(equal (- x) (- y))|))
     (18 18 (:REWRITE |(equal (+ (- c) x) y)|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (13 13 (:REWRITE REDUCE-RATIONALP-+))
     (13 13 (:REWRITE REDUCE-RATIONALP-*))
     (13 13 (:REWRITE RATIONALP-MINUS-X))
     (13 13
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (13 13 (:META META-RATIONALP-CORRECT))
     (12 12
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (12 12
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (8 5
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
     (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
     (6 6 (:LINEAR EXPT->=-1-TWO))
     (6 6 (:LINEAR EXPT->-1-TWO))
     (6 6 (:LINEAR EXPT-<=-1-ONE))
     (6 6 (:LINEAR EXPT-<-1-TWO))
     (6 6 (:LINEAR EXPT-<-1-ONE))
     (6 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (6 3
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
     (6 3
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
     (5 5 (:REWRITE |(expt (- c) n)|))
     (3 3
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
     (3 3
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(S1** (60 12 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
      (60 12 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
      (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
      (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
      (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
      (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
      (24 12 (:TYPE-PRESCRIPTION NATP-MOD))
      (12 12 (:TYPE-PRESCRIPTION RATIONALP-MOD))
      (12 12 (:TYPE-PRESCRIPTION NATP-MOD-2))
      (12 12 (:TYPE-PRESCRIPTION NATP))
      (12 12 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
      (12 12 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
      (12 12
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
      (12 12
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
      (12 12 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
      (12 12 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
      (12 12
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
      (12 12
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
      (12 12 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
      (12 12 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
      (12 12 (:TYPE-PRESCRIPTION INTEGERP-MOD)))
(Q1**
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(LEMMA-4-1-B
     (168 21 (:REWRITE RATIONALP-X))
     (162 68
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (112 48 (:REWRITE SIMPLIFY-SUMS-<))
     (102 102
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (99 63 (:REWRITE INTEGERP-<-CONSTANT))
     (85 5
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (85 5
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (85 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (85 5 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (81 81
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
     (81 81
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
     (81 81
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
     (81 81
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
     (81 81
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
     (81 81
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
     (75 75 (:REWRITE |(* c (* d x))|))
     (72 72 (:REWRITE THE-FLOOR-BELOW))
     (72 72 (:REWRITE THE-FLOOR-ABOVE))
     (70 68
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (70 68
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (69 63
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (67 63 (:REWRITE |(< (- x) c)|))
     (67 63 (:REWRITE |(< (- x) (- y))|))
     (66 63 (:REWRITE CONSTANT-<-INTEGERP))
     (66 63
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (65 65 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (65 65 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (65 65 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (65 65 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (65 65
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (65 65
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (65 65 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (65 65
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (65 65
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (65 65 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (63 63
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (63 63
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (63 63
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (63 63 (:REWRITE |(< c (- x))|))
     (63 63
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (63 63
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (63 63
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (63 63 (:REWRITE |(< (/ x) (/ y))|))
     (50 40 (:REWRITE INTEGERP-MINUS-X))
     (48 16 (:REWRITE DEFAULT-MOD-RATIO))
     (40 40 (:REWRITE REDUCE-INTEGERP-+))
     (40 40 (:META META-INTEGERP-CORRECT))
     (34 2 (:REWRITE ODD-EXPT-THM))
     (34 2 (:LINEAR EXPT-<=-1-TWO))
     (29 21 (:REWRITE RATIONALP-MINUS-X))
     (28 1
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (27 27 (:REWRITE |(< x (+ c/d y))|))
     (23 23 (:REWRITE |(< y (+ (- c) x))|))
     (21 21 (:REWRITE REDUCE-RATIONALP-+))
     (21 21 (:REWRITE REDUCE-RATIONALP-*))
     (21 21 (:META META-RATIONALP-CORRECT))
     (16 16 (:REWRITE FOLD-CONSTS-IN-+))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (16 16 (:REWRITE DEFAULT-MOD-1))
     (16 16 (:REWRITE |(mod x 2)| . 2))
     (13 13 (:REWRITE |(< (+ c/d x) y)|))
     (13 13 (:REWRITE |(< (+ (- c) x) y)|))
     (10 10
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (10 5 (:TYPE-PRESCRIPTION NATP-MOD))
     (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (5 5 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (5 5 (:TYPE-PRESCRIPTION NATP))
     (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (5 5 (:REWRITE |(expt (- c) n)|))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (4 4
        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
     (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
     (2 2 (:LINEAR EXPT->=-1-TWO))
     (2 2 (:LINEAR EXPT->-1-TWO))
     (2 2 (:LINEAR EXPT-<=-1-ONE))
     (2 2 (:LINEAR EXPT-<-1-TWO))
     (2 2 (:LINEAR EXPT-<-1-ONE))
     (1 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|)))
(H**)
(H**-CONSTRAINT
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(Q**
 (20 16 (:REWRITE DEFAULT-PLUS-1))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (16 16 (:REWRITE DEFAULT-PLUS-2))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (8 2 (:REWRITE RATIONALP-X))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(Q**-CONSTRAINT
 (5744 641
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (4808 641
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3847 772 (:REWRITE DEFAULT-TIMES-1))
 (3674
  3674
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3674
      3674
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3674
     3674
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3674 3674
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2309 103 (:REWRITE DEFAULT-LESS-THAN-2))
 (1283 131 (:REWRITE DEFAULT-PLUS-2))
 (926 70 (:REWRITE SIMPLIFY-SUMS-<))
 (641 641
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (526 131 (:REWRITE DEFAULT-PLUS-1))
 (444 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (444 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (374 122 (:REWRITE DEFAULT-MINUS))
 (280 55 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (264 24 (:REWRITE DEFAULT-MOD-RATIO))
 (255 255
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (209 87
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (196 196
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (180 20 (:REWRITE ACL2-NUMBERP-X))
 (164 164 (:REWRITE DEFAULT-EXPT-2))
 (164 164 (:REWRITE DEFAULT-EXPT-1))
 (164 164 (:REWRITE |(expt 1/c n)|))
 (164 164 (:REWRITE |(expt (- x) n)|))
 (142 22 (:REWRITE RATIONALP-X))
 (126 2 (:LINEAR FL-DEF))
 (103 103 (:REWRITE THE-FLOOR-BELOW))
 (103 103 (:REWRITE THE-FLOOR-ABOVE))
 (95 77
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (93 75 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (87 87
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (87 87
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (87 87
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (77 77 (:REWRITE INTEGERP-<-CONSTANT))
 (77 77 (:REWRITE CONSTANT-<-INTEGERP))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< c (- x))|))
 (77 77
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (77 77
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< (/ x) (/ y))|))
 (77 77 (:REWRITE |(< (- x) c)|))
 (77 77 (:REWRITE |(< (- x) (- y))|))
 (53 53 (:REWRITE REDUCE-INTEGERP-+))
 (53 53 (:REWRITE INTEGERP-MINUS-X))
 (53 53 (:META META-INTEGERP-CORRECT))
 (53 17 (:REWRITE |(+ c (+ d x))|))
 (43 2 (:REWRITE ODD-EXPT-THM))
 (43 2 (:LINEAR EXPT-<=-1-TWO))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (28 28 (:REWRITE |(< 0 (/ x))|))
 (27 27 (:REWRITE |(* c (* d x))|))
 (27 27 (:REWRITE |(* (- x) y)|))
 (24 24 (:REWRITE DEFAULT-MOD-2))
 (24 24 (:REWRITE DEFAULT-MOD-1))
 (24 24 (:REWRITE |(mod x 2)| . 2))
 (22 22 (:REWRITE REDUCE-RATIONALP-+))
 (22 22 (:REWRITE REDUCE-RATIONALP-*))
 (22 22 (:REWRITE RATIONALP-MINUS-X))
 (22 22 (:META META-RATIONALP-CORRECT))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (18 18
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (15 15 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(expt c (* d n))|))
 (8 8
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (6 6
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (6 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(INTP-S1
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6 2 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (6 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (6 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2 1 (:TYPE-PRESCRIPTION NATP-MOD))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (1 1 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD)))
(RATP-Q1
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(LEMMA-4-1-28
     (1479 51 (:REWRITE MOD-X-Y-=-X . 4))
     (1479 51 (:REWRITE MOD-X-Y-=-X . 3))
     (1473 1473
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
     (1473 1473
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
     (1473 1473
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
     (1428 51 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1275 51 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (1224 51 (:REWRITE MOD-DOES-NOTHING))
     (1152 288 (:REWRITE RATIONALP-X))
     (1070 30 (:LINEAR MOD-BND-2))
     (854 427 (:TYPE-PRESCRIPTION NATP-MOD))
     (851 647 (:REWRITE INTEGERP-MINUS-X))
     (795 576
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (714 51 (:REWRITE MOD-ZERO . 4))
     (663 51 (:REWRITE CANCEL-MOD-+))
     (627 576
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (613 101 (:REWRITE ACL2-NUMBERP-X))
     (607 576 (:REWRITE SIMPLIFY-SUMS-<))
     (596 596 (:REWRITE REDUCE-INTEGERP-+))
     (596 596 (:META META-INTEGERP-CORRECT))
     (591 591 (:REWRITE THE-FLOOR-BELOW))
     (591 591 (:REWRITE THE-FLOOR-ABOVE))
     (576 576
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (576 576
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (576 576
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (576 576
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (576 576 (:REWRITE INTEGERP-<-CONSTANT))
     (576 576 (:REWRITE CONSTANT-<-INTEGERP))
     (576 576
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (576 576
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (576 576
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (576 576
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (576 576 (:REWRITE |(< c (- x))|))
     (576 576
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (576 576
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (576 576
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (576 576
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (576 576 (:REWRITE |(< (/ x) (/ y))|))
     (576 576 (:REWRITE |(< (- x) c)|))
     (576 576 (:REWRITE |(< (- x) (- y))|))
     (500 40 (:LINEAR EXPT-X->=-X))
     (500 40 (:LINEAR EXPT-X->-X))
     (460 60 (:LINEAR MOD-BOUNDS-2))
     (434 434 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (427 427 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (427 427 (:TYPE-PRESCRIPTION NATP))
     (427 427 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (427 427 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (427 427 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (427 427 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (427 427
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (427 427
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (427 427
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (427 427
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (427 427
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (427 427 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (427 427 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (427 427 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (323 170 (:REWRITE |(- (* c x))|))
     (307 103 (:REWRITE |(* (- x) y)|))
     (306 51 (:REWRITE MOD-ZERO . 3))
     (288 288 (:REWRITE RATIONALP-MINUS-X))
     (246 246 (:REWRITE REDUCE-RATIONALP-+))
     (246 246 (:META META-RATIONALP-CORRECT))
     (244 113
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (224 224 (:REWRITE |(expt 1/c n)|))
     (224 224 (:REWRITE |(expt (- x) n)|))
     (224 112 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (204 204 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (204 51 (:REWRITE |(mod x 2)| . 1))
     (180 30 (:LINEAR MOD-BOUNDS-3))
     (149 116
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (147 147
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (147 147
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (147 147 (:REWRITE |(< (/ x) 0)|))
     (147 147 (:REWRITE |(< (* x y) 0)|))
     (131 131
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (131 131
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (131 131 (:REWRITE |(< 0 (/ x))|))
     (131 131 (:REWRITE |(< 0 (* x y))|))
     (116 116
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (114 113 (:REWRITE |(equal (- x) (- y))|))
     (113 113
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (113 113 (:REWRITE |(equal c (/ x))|))
     (113 113 (:REWRITE |(equal c (- x))|))
     (113 113 (:REWRITE |(equal (/ x) c)|))
     (113 113 (:REWRITE |(equal (/ x) (/ y))|))
     (113 113 (:REWRITE |(equal (- x) c)|))
     (93 93 (:REWRITE DEFAULT-MOD-2))
     (80 80
         (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (80 80
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (80 80
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (51 51
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (51 51 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (51 51 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (51 51 (:REWRITE MOD-X-Y-=-X . 2))
     (51 51
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (51 51
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (51 51 (:REWRITE MOD-CANCEL-*-CONST))
     (51 51 (:REWRITE |(mod x 2)| . 2))
     (51 51 (:REWRITE |(mod x (- y))| . 3))
     (51 51 (:REWRITE |(mod x (- y))| . 2))
     (51 51 (:REWRITE |(mod x (- y))| . 1))
     (51 51
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (51 51
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (51 51 (:REWRITE |(mod (- x) y)| . 3))
     (51 51 (:REWRITE |(mod (- x) y)| . 2))
     (51 51 (:REWRITE |(mod (- x) y)| . 1))
     (51 51 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (51 51
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (51 51
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (51 51
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (47 47
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (40 40 (:LINEAR EXPT-LINEAR-UPPER-<))
     (40 40 (:LINEAR EXPT-LINEAR-LOWER-<))
     (40 40 (:LINEAR EXPT->=-1-TWO))
     (40 40 (:LINEAR EXPT->-1-TWO))
     (40 40 (:LINEAR EXPT-<=-1-ONE))
     (40 40 (:LINEAR EXPT-<-1-ONE))
     (30 30 (:REWRITE ODD-EXPT-THM))
     (30 30 (:LINEAR MOD-BND-3))
     (28 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (20 20 (:REWRITE |(< y (+ (- c) x))|))
     (20 20 (:REWRITE |(< x (+ c/d y))|))
     (20 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (8 4 (:REWRITE |(+ c (+ d x))|))
     (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
     (5 1 (:REWRITE |(+ y (+ x z))|))
     (1 1 (:TYPE-PRESCRIPTION LEMMA-4-1-28))
     (1 1
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1 (:REWRITE |(* c (* d x))|)))
(LEMMA-4-1-28-2
 (48 48
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (48 48
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (48 48
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (48
  48
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (48 48
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (48 48
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (48 48
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (48 48
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (48 48
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 1 (:TYPE-PRESCRIPTION LEMMA-4-1-28-2))
 (1 1 (:TYPE-PRESCRIPTION ZP)))
(LEMMA-4-1-29)
(LEMMA-4-1-30
     (700 202 (:REWRITE RATIONALP-X))
     (630 315 (:TYPE-PRESCRIPTION NATP-MOD))
     (582 130 (:REWRITE ACL2-NUMBERP-X))
     (519 519
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
     (519 519
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
     (519 519
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
     (414 74 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (384 16 (:REWRITE MOD-DOES-NOTHING))
     (333 9 (:LINEAR MOD-BND-2))
     (315 315 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (315 315 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (315 315 (:TYPE-PRESCRIPTION NATP))
     (315 315 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (315 315 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (315 315 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (315 315 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (315 315
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (315 315
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (315 315
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (315 315
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (315 315
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (315 315
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (315 315 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (315 315 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (315 315 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (256 256 (:REWRITE REDUCE-INTEGERP-+))
     (256 256 (:REWRITE INTEGERP-MINUS-X))
     (256 256 (:META META-INTEGERP-CORRECT))
     (244 29
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (202 202 (:REWRITE REDUCE-RATIONALP-+))
     (202 202 (:REWRITE REDUCE-RATIONALP-*))
     (202 202 (:REWRITE RATIONALP-MINUS-X))
     (202 202 (:META META-RATIONALP-CORRECT))
     (198 18 (:LINEAR MOD-BOUNDS-2))
     (198 18 (:LINEAR MOD-BOUNDS-1))
     (176 16 (:REWRITE MOD-ZERO . 4))
     (176 16 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (176 16 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (176 16 (:REWRITE MOD-CANCEL-*-CONST))
     (160 16
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (131 74
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (128 16
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (128 16
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (121 74 (:REWRITE SIMPLIFY-SUMS-<))
     (113 28 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (96 96
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (96 16 (:REWRITE MOD-ZERO . 3))
     (95 95 (:REWRITE |(expt 1/c n)|))
     (95 95 (:REWRITE |(expt (- x) n)|))
     (88 58 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (74 74 (:REWRITE THE-FLOOR-BELOW))
     (74 74 (:REWRITE THE-FLOOR-ABOVE))
     (74 74
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (74 74
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (74 74
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (74 74 (:REWRITE INTEGERP-<-CONSTANT))
     (74 74 (:REWRITE CONSTANT-<-INTEGERP))
     (74 74
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (74 74
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (74 74
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (74 74
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (74 74 (:REWRITE |(< c (- x))|))
     (74 74
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (74 74
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (74 74
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (74 74
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (74 74 (:REWRITE |(< (/ x) (/ y))|))
     (74 74 (:REWRITE |(< (- x) c)|))
     (74 74 (:REWRITE |(< (- x) (- y))|))
     (70 10 (:REWRITE ODD-EXPT-THM))
     (64 16 (:REWRITE |(mod x 2)| . 1))
     (63 7
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (56 7 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (56 7 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (54 9 (:LINEAR MOD-BOUNDS-3))
     (36 36 (:REWRITE |(- (* c x))|))
     (32 16 (:REWRITE MOD-X-Y-=-X . 4))
     (32 16 (:REWRITE CANCEL-MOD-+))
     (32 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (30 29 (:REWRITE |(equal (- x) (- y))|))
     (29 29
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (29 29 (:REWRITE |(equal c (/ x))|))
     (29 29 (:REWRITE |(equal c (- x))|))
     (29 29 (:REWRITE |(equal (/ x) c)|))
     (29 29 (:REWRITE |(equal (/ x) (/ y))|))
     (29 29 (:REWRITE |(equal (- x) c)|))
     (24 24 (:REWRITE |(expt c (* d n))|))
     (16 16 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (16 16 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (16 16 (:REWRITE MOD-X-Y-=-X . 3))
     (16 16 (:REWRITE MOD-X-Y-=-X . 2))
     (16 16
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (16 16 (:REWRITE |(mod x 2)| . 2))
     (16 16 (:REWRITE |(mod x (- y))| . 3))
     (16 16 (:REWRITE |(mod x (- y))| . 2))
     (16 16 (:REWRITE |(mod x (- y))| . 1))
     (16 16
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (16 16
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (16 16 (:REWRITE |(mod (- x) y)| . 3))
     (16 16 (:REWRITE |(mod (- x) y)| . 2))
     (16 16 (:REWRITE |(mod (- x) y)| . 1))
     (16 16
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
     (13 13 (:REWRITE |(* (- x) y)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:REWRITE |(* c (* d x))|))
     (9 9 (:LINEAR MOD-BND-3))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3)))
(LEMMA-4-1-30-1
 (3570 357
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (2724 357
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (2704
  2704
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2704
      2704
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2704
     2704
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2704 2704
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2604 515 (:REWRITE DEFAULT-TIMES-1))
 (860 116 (:REWRITE DEFAULT-PLUS-2))
 (699 39 (:REWRITE DEFAULT-LESS-THAN-2))
 (638 29
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (545 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (545 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (412 79 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (365 116 (:REWRITE DEFAULT-PLUS-1))
 (360 28 (:REWRITE SIMPLIFY-SUMS-<))
 (357 357
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (162 72 (:REWRITE DEFAULT-MINUS))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (155 33
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (126 2 (:LINEAR FL-DEF))
 (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (88 88 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (88 8 (:REWRITE DEFAULT-MOD-RATIO))
 (76 76 (:REWRITE DEFAULT-EXPT-2))
 (76 76 (:REWRITE DEFAULT-EXPT-1))
 (76 76 (:REWRITE |(expt 1/c n)|))
 (76 76 (:REWRITE |(expt (- x) n)|))
 (70 4 (:REWRITE RATIONALP-X))
 (47 29
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (47 6 (:REWRITE ODD-EXPT-THM))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 27 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (43 2 (:LINEAR EXPT-<=-1-TWO))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (39 39 (:REWRITE THE-FLOOR-BELOW))
 (39 39 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< c (- x))|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< (/ x) (/ y))|))
 (29 29 (:REWRITE |(< (- x) c)|))
 (29 29 (:REWRITE |(< (- x) (- y))|))
 (23 11 (:REWRITE |(+ c (+ d x))|))
 (19 19 (:REWRITE |(expt c (* d n))|))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:REWRITE INTEGERP-MINUS-X))
 (17 17 (:META META-INTEGERP-CORRECT))
 (11 11 (:REWRITE |(* c (* d x))|))
 (11 11 (:REWRITE |(* (- x) y)|))
 (8 8
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (8 8 (:REWRITE DEFAULT-MOD-2))
 (8 8 (:REWRITE DEFAULT-MOD-1))
 (8 8 (:REWRITE |(mod x 2)| . 2))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-30-2)
(LEMMA-4-1-31
     (137 123
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (136 136 (:REWRITE THE-FLOOR-BELOW))
     (136 136 (:REWRITE THE-FLOOR-ABOVE))
     (131 131
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (131 131
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (131 131
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (127 127 (:REWRITE INTEGERP-<-CONSTANT))
     (127 127 (:REWRITE CONSTANT-<-INTEGERP))
     (127 127
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (127 127
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (127 127
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (127 127
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (127 127 (:REWRITE |(< c (- x))|))
     (127 127
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (127 127
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (127 127
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (127 127
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (127 127 (:REWRITE |(< (/ x) (/ y))|))
     (127 127 (:REWRITE |(< (- x) c)|))
     (127 127 (:REWRITE |(< (- x) (- y))|))
     (111 111 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (104 104
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (91 91 (:REWRITE |(expt 1/c n)|))
     (91 91 (:REWRITE |(expt (- x) n)|))
     (88 11 (:REWRITE ACL2-NUMBERP-X))
     (76 76 (:REWRITE REDUCE-INTEGERP-+))
     (76 76 (:REWRITE INTEGERP-MINUS-X))
     (76 76 (:META META-INTEGERP-CORRECT))
     (40 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (37 7 (:REWRITE RATIONALP-X))
     (36 36 (:REWRITE |(< 0 (/ x))|))
     (36 36 (:REWRITE |(< 0 (* x y))|))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (30 30 (:REWRITE |(expt c (* d n))|))
     (16 16
         (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (16 16
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (16 16
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (14 14 (:REWRITE ODD-EXPT-THM))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (10 10 (:REWRITE |(< x (+ c/d y))|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
     (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
     (8 8 (:LINEAR EXPT->=-1-TWO))
     (8 8 (:LINEAR EXPT->-1-TWO))
     (8 8 (:LINEAR EXPT-<=-1-TWO))
     (8 8 (:LINEAR EXPT-<=-1-ONE))
     (8 8 (:LINEAR EXPT-<-1-TWO))
     (8 8 (:LINEAR EXPT-<-1-ONE))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7 (:REWRITE REDUCE-RATIONALP-+))
     (7 7 (:REWRITE REDUCE-RATIONALP-*))
     (7 7 (:REWRITE RATIONALP-MINUS-X))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(* x (- y))|))
     (4 4 (:REWRITE |(* (- x) y)|))
     (3 3 (:REWRITE LEMMA-4-1-28-2))
     (2 1 (:TYPE-PRESCRIPTION LEMMA-4-1-31)))
(Q**-REWRITE
 (353 33 (:TYPE-PRESCRIPTION LEMMA-4-1-28))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (24 24
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(LEMMA-4-1-32
 (1048
  1048
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1048
      1048
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1048
     1048
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1048 1048
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (324 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (261 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (261 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (130 58 (:REWRITE |(< (- x) (- y))|))
 (110 60
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (109 37 (:REWRITE SIMPLIFY-SUMS-<))
 (62 62 (:REWRITE THE-FLOOR-BELOW))
 (62 62 (:REWRITE THE-FLOOR-ABOVE))
 (60 60
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (58 58 (:REWRITE DEFAULT-EXPT-1))
 (58 58 (:REWRITE |(expt 1/c n)|))
 (58 58 (:REWRITE |(expt (- x) n)|))
 (58 58
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (58 58
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (58 58
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (58 58
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (58 58 (:REWRITE |(< c (- x))|))
 (58 58
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (58 58
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (58 58
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (58 58
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (58 58 (:REWRITE |(< (/ x) (/ y))|))
 (56 56
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (56 56
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (56 56 (:REWRITE INTEGERP-<-CONSTANT))
 (56 56 (:REWRITE CONSTANT-<-INTEGERP))
 (54 54 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (51 51 (:REWRITE |(- (* c x))|))
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (19 19 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:REWRITE |(< 0 (/ x))|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (7 5 (:REWRITE |(+ c (+ d x))|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(LEMMA-4-1-33
 (3050 66 (:REWRITE ACL2-NUMBERP-X))
 (2050 68 (:REWRITE LEMMA-4-1-28-2))
 (891 141 (:REWRITE |(< (- x) (- y))|))
 (523 141
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (506 68 (:REWRITE RATIONALP-X))
 (401 151
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (227 141 (:REWRITE |(< (- x) c)|))
 (166 166 (:REWRITE THE-FLOOR-BELOW))
 (166 166 (:REWRITE THE-FLOOR-ABOVE))
 (153
   153
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (153
  153
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (153
     153
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (153 151
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (153 151
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (141 141
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (141 141 (:REWRITE INTEGERP-<-CONSTANT))
 (141 141 (:REWRITE CONSTANT-<-INTEGERP))
 (141 141
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (141 141
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (141 141
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (141 141
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (141 141 (:REWRITE |(< c (- x))|))
 (141 141
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (141 141
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (141 141
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (141 141
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (141 141 (:REWRITE |(< (/ x) (/ y))|))
 (131 131 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (74 64 (:REWRITE |(+ c (+ d x))|))
 (71 71 (:REWRITE REDUCE-INTEGERP-+))
 (71 71 (:REWRITE INTEGERP-MINUS-X))
 (71 71 (:META META-INTEGERP-CORRECT))
 (68 68 (:REWRITE REDUCE-RATIONALP-+))
 (68 68 (:REWRITE REDUCE-RATIONALP-*))
 (68 68 (:REWRITE RATIONALP-MINUS-X))
 (68 68 (:META META-RATIONALP-CORRECT))
 (44 44 (:REWRITE |(< x (+ c/d y))|))
 (44 44 (:REWRITE |(< (+ c/d x) y)|))
 (44 44 (:REWRITE |(< (+ (- c) x) y)|))
 (34 34 (:REWRITE |(< y (+ (- c) x))|))
 (21 21
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(* (- x) y)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(LEMMA-4-1-34
 (350 20 (:REWRITE RATIONALP-X))
 (270 66
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (253 62 (:REWRITE SIMPLIFY-SUMS-<))
 (111 66 (:REWRITE |(< (- x) c)|))
 (111 66 (:REWRITE |(< (- x) (- y))|))
 (109 27 (:REWRITE INTEGERP-MINUS-X))
 (106 18 (:REWRITE RATIONALP-MINUS-X))
 (93 93 (:REWRITE THE-FLOOR-BELOW))
 (93 93 (:REWRITE THE-FLOOR-ABOVE))
 (93 93
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (93 93
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (71 66
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (67 65 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (66 66 (:REWRITE INTEGERP-<-CONSTANT))
 (66 66 (:REWRITE CONSTANT-<-INTEGERP))
 (66 66
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (66 66
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (66 66
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (66 66
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (66 66 (:REWRITE |(< c (- x))|))
 (66 66
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (66 66
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (66 66
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (66 66
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (66 66 (:REWRITE |(< (/ x) (/ y))|))
 (39 39 (:REWRITE |(< 0 (* x y))|))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27
  27
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (27 27 (:REWRITE REDUCE-INTEGERP-+))
 (27 27 (:REWRITE |(< x (+ c/d y))|))
 (27 27 (:META META-INTEGERP-CORRECT))
 (20 2 (:REWRITE |(integerp (- x))|))
 (18 18 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:META META-RATIONALP-CORRECT))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(- (* c x))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(* (- x) y)|)))
(LEMMA-4-1-35)
(LEMMA-4-1-36
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(LEMMA-4-1-37)
(LEMMA-4-1-38
 (189
  189
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (189 189
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (189
     189
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (189 189
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (65 8 (:REWRITE |(< (- x) c)|))
 (51 2 (:LINEAR EXPT->=-1-ONE))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6 (:REWRITE |(- (* c x))|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(LEMMA-4-1-39)
(LEMMA-4-1-40
 (5561
  5561
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5561
      5561
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5561
     5561
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5561 5561
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5561 5561
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2019 41 (:REWRITE ACL2-NUMBERP-X))
 (1936 76 (:LINEAR EXPT->-1-ONE))
 (1516 76 (:LINEAR EXPT-X->=-X))
 (1516 76 (:LINEAR EXPT-X->-X))
 (1411 836
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1386 29 (:REWRITE LEMMA-4-1-28-2))
 (1096 749 (:REWRITE |(< (- x) (- y))|))
 (897 897 (:REWRITE THE-FLOOR-BELOW))
 (897 897 (:REWRITE THE-FLOOR-ABOVE))
 (836 836
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (836 836
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (772 749 (:REWRITE |(< (- x) c)|))
 (749 749 (:REWRITE INTEGERP-<-CONSTANT))
 (749 749 (:REWRITE CONSTANT-<-INTEGERP))
 (749 749
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (749 749
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (749 749
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (749 749
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (749 749 (:REWRITE |(< c (- x))|))
 (749 749
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (749 749
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (749 749
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (749 749
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (749 749 (:REWRITE |(< (/ x) (/ y))|))
 (521 472 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (373 373
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (369 66
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (369 66
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (369 66
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (296 35 (:REWRITE RATIONALP-X))
 (258 258 (:REWRITE |(< x (+ c/d y))|))
 (235 235 (:REWRITE |(< y (+ (- c) x))|))
 (232 232 (:REWRITE DEFAULT-EXPT-1))
 (232 232 (:REWRITE |(expt 1/c n)|))
 (232 232 (:REWRITE |(expt (- x) n)|))
 (226 226 (:REWRITE |(< (+ c/d x) y)|))
 (221 221 (:REWRITE |(< 0 (* x y))|))
 (162 162
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (155 132 (:REWRITE |(+ c (+ d x))|))
 (152 152
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (152 152
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (152 152
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (152 152
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (148 140 (:REWRITE |(< 0 (/ x))|))
 (129 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (93 93 (:REWRITE REDUCE-INTEGERP-+))
 (93 93 (:REWRITE INTEGERP-MINUS-X))
 (93 93 (:REWRITE |(< (/ x) 0)|))
 (93 93 (:REWRITE |(< (* x y) 0)|))
 (93 93 (:META META-INTEGERP-CORRECT))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (82 82 (:REWRITE |(- (* c x))|))
 (81 54
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (76 76 (:LINEAR EXPT-LINEAR-UPPER-<))
 (76 76 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (76 76 (:LINEAR EXPT-LINEAR-LOWER-<))
 (76 76 (:LINEAR EXPT->=-1-TWO))
 (76 76 (:LINEAR EXPT->-1-TWO))
 (76 76 (:LINEAR EXPT-<=-1-ONE))
 (76 76 (:LINEAR EXPT-<-1-ONE))
 (70 62 (:REWRITE |(equal (/ x) (/ y))|))
 (62 62
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (62 62
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (62 62 (:REWRITE |(equal c (/ x))|))
 (62 62 (:REWRITE |(equal (- x) (- y))|))
 (54 54 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (54 54
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (54 54 (:REWRITE |(equal c (- x))|))
 (54 54 (:REWRITE |(equal (- x) c)|))
 (48 48
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (39 39 (:REWRITE FOLD-CONSTS-IN-+))
 (35 35 (:REWRITE REDUCE-RATIONALP-+))
 (35 35 (:REWRITE REDUCE-RATIONALP-*))
 (35 35 (:REWRITE RATIONALP-MINUS-X))
 (35 35 (:META META-RATIONALP-CORRECT))
 (34 8 (:REWRITE |(equal x (/ y))|))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (21 8 (:REWRITE |(not (equal x (/ y)))|))
 (16 16
     (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 8 (:REWRITE DEFAULT-DIVIDE))
 (6 6 (:REWRITE |(* x (- y))|))
 (6 6 (:REWRITE |(* (- x) y)|)))
(LEMMA-4-1-41
 (302
  302
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (302 302
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (302
     302
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (302 302
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (302 302
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (216 24
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (90 15 (:REWRITE SIMPLIFY-SUMS-<))
 (48 25 (:REWRITE |(< (- x) (- y))|))
 (28 25 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 2 (:REWRITE ODD-EXPT-THM))
 (25 25
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (25 25 (:REWRITE INTEGERP-<-CONSTANT))
 (25 25 (:REWRITE CONSTANT-<-INTEGERP))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (8 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:META META-INTEGERP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(Q**-REWRITE-2
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(LEMMA-4-1-42
 (855
  855
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (855 855
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (855
     855
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (855 855
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (225 21
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (153 18 (:REWRITE SIMPLIFY-SUMS-<))
 (130 130
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (130 130
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (130 130
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (89 4 (:REWRITE ODD-EXPT-THM))
 (43 22 (:REWRITE |(< (- x) (- y))|))
 (32 22 (:REWRITE |(< (- x) c)|))
 (27 27 (:REWRITE DEFAULT-EXPT-1))
 (27 27 (:REWRITE |(expt 1/c n)|))
 (27 27 (:REWRITE |(expt (- x) n)|))
 (23 23 (:REWRITE THE-FLOOR-BELOW))
 (23 23 (:REWRITE THE-FLOOR-ABOVE))
 (23 23 (:REWRITE |(- (* c x))|))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (22 22 (:REWRITE INTEGERP-<-CONSTANT))
 (22 22 (:REWRITE CONSTANT-<-INTEGERP))
 (22 22
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (22 22
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (22 22
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (22 22
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (22 22 (:REWRITE |(< c (- x))|))
 (22 22
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (22 22
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (22 22
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (22 22
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (22 22 (:REWRITE |(< (/ x) (/ y))|))
 (17 6 (:REWRITE INTEGERP-MINUS-X))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE |(expt c (* d n))|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LEMMA-4-1-43
 (247
  247
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (247 247
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (247
     247
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (247 247
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (54 54
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (43 8 (:REWRITE SIMPLIFY-SUMS-<))
 (43 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (43 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE CONSTANT-<-INTEGERP))
 (9 9 (:REWRITE |(expt c (* d n))|))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< c (- x))|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:TYPE-PRESCRIPTION LEMMA-4-1-31))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-44
 (268 231 (:TYPE-PRESCRIPTION LEMMA-4-1-31))
 (236
  236
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (236
     236
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (76 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (76 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (62 10 (:REWRITE SIMPLIFY-SUMS-<))
 (50 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (23 23 (:REWRITE DEFAULT-EXPT-1))
 (23 23 (:REWRITE |(expt 1/c n)|))
 (23 23 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE |(expt c (* d n))|))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13 (:REWRITE CONSTANT-<-INTEGERP))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< c (- x))|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (7 7 (:REWRITE |(* c (* d x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-45
 (228
  228
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (228 228
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (228
     228
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (228 228
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (42 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (25 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (17 17 (:REWRITE THE-FLOOR-BELOW))
 (17 17 (:REWRITE THE-FLOOR-ABOVE))
 (17 17
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (16 9 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (2 1 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(+ 0 x)|))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-46
 (559 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (487 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (487 487
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (383
  383
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (383 383
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (383
     383
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (383 383
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (230 126
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (230 126
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (230 126
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (126 126
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (126 126
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (126 126
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (122 26 (:REWRITE ACL2-NUMBERP-X))
 (97 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (83 83
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (83 83
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (83 83
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (83 83
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (64 16 (:REWRITE RATIONALP-X))
 (60 30 (:TYPE-PRESCRIPTION NATP-MOD))
 (57 24 (:REWRITE SIMPLIFY-SUMS-<))
 (57 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (44 24
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (43 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (35 35 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (35 35
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (35 35
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (35 35 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (35 35
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (35 35
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (35 35 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (34 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (30 30 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (30 30 (:TYPE-PRESCRIPTION NATP))
 (30 30 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (29 1 (:REWRITE MOD-X-Y-=-X . 4))
 (29 1 (:REWRITE MOD-X-Y-=-X . 3))
 (28 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (28 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (26 22 (:REWRITE INTEGERP-MINUS-X))
 (26 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (24 24 (:REWRITE INTEGERP-<-CONSTANT))
 (24 24 (:REWRITE DEFAULT-EXPT-1))
 (24 24 (:REWRITE CONSTANT-<-INTEGERP))
 (24 24 (:REWRITE |(expt 1/c n)|))
 (24 24 (:REWRITE |(expt (- x) n)|))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< c (- x))|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< (/ x) (/ y))|))
 (24 24 (:REWRITE |(< (- x) c)|))
 (24 24 (:REWRITE |(< (- x) (- y))|))
 (24 1 (:REWRITE MOD-DOES-NOTHING))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:META META-INTEGERP-CORRECT))
 (21 18 (:REWRITE |(- (* c x))|))
 (20 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (17 17 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (16 16 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:META META-RATIONALP-CORRECT))
 (14 1 (:REWRITE MOD-ZERO . 4))
 (13 1 (:REWRITE CANCEL-MOD-+))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10 (:REWRITE |(* c (* d x))|))
 (10 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (7 3 (:REWRITE |(+ c (+ d x))|))
 (6 2 (:REWRITE |(+ y x)|))
 (6 2 (:REWRITE |(* (- x) y)|))
 (6 1 (:REWRITE MOD-ZERO . 3))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE NORMALIZE-ADDENDS))
 (5 1 (:REWRITE |(+ y (+ x z))|))
 (4 1 (:REWRITE |(mod x 2)| . 1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE DEFAULT-MOD-2))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ 0 x)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X . 2))
 (1 1
    (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE MOD-CANCEL-*-CONST))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1 1
    (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(LEMMA-4-1-47
 (86
  86
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (86 86
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (86 86
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (86 86
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (86 86
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(expt c (* d n))|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LEMMA-4-1-48
 (189
  189
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (189 189
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (189
     189
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (189 189
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (189 189
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:REWRITE THE-FLOOR-BELOW))
 (3 3 (:REWRITE THE-FLOOR-ABOVE))
 (3 3 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3 3
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3 3 (:REWRITE INTEGERP-<-CONSTANT))
 (3 3 (:REWRITE CONSTANT-<-INTEGERP))
 (3 3
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3 3
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3 3
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3 3
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< c (- x))|))
 (3 3
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3 3
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3 3
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3 3
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< (/ x) (/ y))|))
 (3 3 (:REWRITE |(< (- x) c)|))
 (3 3 (:REWRITE |(< (- x) (- y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(LEMMA-4-1-49)
(LEMMA-4-1-50
 (20
  20
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20 20
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2 (:TYPE-PRESCRIPTION ZP)))
(LEMMA-4-1-51
 (463
  463
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (463 463
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (463
     463
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (463 463
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (104 11
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (78 9 (:REWRITE SIMPLIFY-SUMS-<))
 (32 14 (:REWRITE |(< (- x) (- y))|))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (14 14 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE CONSTANT-<-INTEGERP))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< c (- x))|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE |(expt c (* d n))|))
 (7 7 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(* (- x) y)|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(LEMMA-4-1-52
 (216 2
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (214 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (132 30
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (92
  92
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (92 92
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (92 92
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (92 92
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (92 92
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (70 19 (:REWRITE SIMPLIFY-SUMS-<))
 (55 31 (:REWRITE INTEGERP-<-CONSTANT))
 (38 31 (:REWRITE |(< (- x) (- y))|))
 (36 31 (:REWRITE |(< (- x) c)|))
 (36 4 (:REWRITE |(* x (+ y z))|))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (31 31
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (31 31
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (31 31 (:REWRITE CONSTANT-<-INTEGERP))
 (31 31
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (31 31
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (31 31
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (31 31
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (31 31 (:REWRITE |(< c (- x))|))
 (31 31
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (31 31
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (31 31
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (31 31
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (31 31 (:REWRITE |(< (/ x) (/ y))|))
 (26 2 (:REWRITE ODD-EXPT-THM))
 (22 2 (:REWRITE |(* y x)|))
 (20 4 (:REWRITE |(* x (- y))|))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (17 17
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 5 (:REWRITE |(- (* c x))|))
 (12 8 (:REWRITE INTEGERP-MINUS-X))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 4 (:REWRITE |(+ (* c x) (* d x))|))
 (8 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (8 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (7 7 (:REWRITE |(+ c (+ d x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(* 0 x)|))
 (4 4 (:REWRITE |(* (- x) y)|))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<)))
(LEMMA-4-1-53
 (2400 286 (:REWRITE |(< c (- x))|))
 (1698 22 (:LINEAR EXPT->=-1-ONE))
 (1680 22 (:LINEAR EXPT-<=-1-TWO))
 (1669 22 (:LINEAR EXPT-<-1-TWO))
 (1651 22 (:LINEAR EXPT->-1-ONE))
 (1536 22 (:LINEAR EXPT-X->=-X))
 (1525 22 (:LINEAR EXPT-X->-X))
 (1396 206 (:REWRITE |(< (- x) c)|))
 (909
  909
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (909 909
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (909
     909
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (909 909
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (909 909
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (829 22 (:LINEAR EXPT-<=-1-ONE))
 (819 22 (:LINEAR EXPT->=-1-TWO))
 (818 22 (:LINEAR EXPT->-1-TWO))
 (818 22 (:LINEAR EXPT-<-1-ONE))
 (457 165
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (446 4
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (430 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (336 286 (:REWRITE |(< (- x) (- y))|))
 (287 287 (:REWRITE THE-FLOOR-BELOW))
 (287 287 (:REWRITE THE-FLOOR-ABOVE))
 (286 286
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (286 286
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (286 286
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (286 286
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (286 286
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (286 286
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (286 286
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (286 286
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (286 286
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (286 286
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (286 286
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (286 286 (:REWRITE |(< (/ x) (/ y))|))
 (282 166 (:REWRITE INTEGERP-<-CONSTANT))
 (189 158 (:REWRITE SIMPLIFY-SUMS-<))
 (166 166
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (166 166 (:REWRITE CONSTANT-<-INTEGERP))
 (144 4 (:REWRITE |(* x (+ y z))|))
 (104 21 (:REWRITE DEFAULT-EXPT-1))
 (92 6 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (91 91
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (91 91
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (91 91
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (84 84 (:REWRITE |(< 0 (/ x))|))
 (84 84 (:REWRITE |(< 0 (* x y))|))
 (82 82 (:REWRITE |(< (/ x) 0)|))
 (82 82 (:REWRITE |(< (* x y) 0)|))
 (82 10 (:REWRITE |(* c (expt d n))|))
 (66 66 (:TYPE-PRESCRIPTION COLLECT-*))
 (56 2 (:REWRITE |(* (* x y) z)|))
 (46 2
     (:REWRITE |(* (expt c m) (expt d n))|))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (44 44
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (41 41
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (41 41
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (40 40
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (40 40
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (34 4
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (34 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (33 9 (:REWRITE ACL2-NUMBERP-X))
 (32 8 (:REWRITE |(integerp (- x))|))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (16 16 (:REWRITE |(< (+ (- c) x) y)|))
 (16 8 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (14 6 (:REWRITE |(expt (expt x m) n)|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 2
     (:REWRITE |(* (expt x n) (expt y n))|))
 (10 2
     (:REWRITE |(* (expt x m) (expt x n))|))
 (9 9 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (6 6 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:REWRITE |(* x (expt x n))|))
 (4 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (4 2 (:REWRITE |(+ (* c x) (* d x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(* 0 x)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(expt (- c) n)|)))
(LEMMA-4-1-54
 (522
  522
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (522 522
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (522
     522
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (522 522
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (393 13 (:LINEAR EXPT-<=-1-TWO))
 (392 13 (:LINEAR EXPT-<-1-TWO))
 (273 26
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (177 26
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (174 26
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (166 13 (:LINEAR EXPT-<=-1-ONE))
 (165 13 (:LINEAR EXPT->=-1-TWO))
 (165 13 (:LINEAR EXPT->-1-TWO))
 (165 13 (:LINEAR EXPT-<-1-ONE))
 (162 13 (:LINEAR EXPT-X->=-X))
 (162 13 (:LINEAR EXPT->=-1-ONE))
 (161 13 (:LINEAR EXPT-X->-X))
 (161 13 (:LINEAR EXPT->-1-ONE))
 (130 25 (:REWRITE SIMPLIFY-SUMS-<))
 (85 47 (:REWRITE DEFAULT-EXPT-1))
 (45 45 (:REWRITE |(expt (- x) n)|))
 (38 29 (:REWRITE |(< (- x) (- y))|))
 (29 29 (:REWRITE THE-FLOOR-BELOW))
 (29 29 (:REWRITE THE-FLOOR-ABOVE))
 (29 29
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (29 29
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (29 29
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< c (- x))|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< (/ x) (/ y))|))
 (29 29 (:REWRITE |(< (- x) c)|))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(* c (* d x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-1-55
 (3747
  3390
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3747
      3390
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3747
     3390
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3390 3390
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (844 61
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (838 838
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (838 838
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (838 838
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (796 61 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (644 61 (:REWRITE SIMPLIFY-SUMS-<))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (394 286
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (394 286
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (394 286
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (393 13 (:LINEAR EXPT-<=-1-TWO))
 (392 13 (:LINEAR EXPT-<-1-TWO))
 (289 289
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (289 289
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (289 289
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (289 289
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (286 286
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (286 286
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (286 286
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (220 36 (:REWRITE ACL2-NUMBERP-X))
 (177 26
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (174 26
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (166 13 (:LINEAR EXPT-<=-1-ONE))
 (165 13 (:LINEAR EXPT->=-1-TWO))
 (165 13 (:LINEAR EXPT->-1-TWO))
 (165 13 (:LINEAR EXPT-<-1-ONE))
 (162 13 (:LINEAR EXPT-X->=-X))
 (162 13 (:LINEAR EXPT->=-1-ONE))
 (161 13 (:LINEAR EXPT-X->-X))
 (161 13 (:LINEAR EXPT->-1-ONE))
 (111 111 (:REWRITE |(expt (- x) n)|))
 (92 23 (:REWRITE RATIONALP-X))
 (89 65
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (66 66 (:REWRITE THE-FLOOR-BELOW))
 (66 66 (:REWRITE THE-FLOOR-ABOVE))
 (65 65
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (65 65
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (65 65
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (65 65 (:REWRITE INTEGERP-<-CONSTANT))
 (65 65 (:REWRITE CONSTANT-<-INTEGERP))
 (65 65
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (65 65
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (65 65
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (65 65
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (65 65 (:REWRITE |(< c (- x))|))
 (65 65
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (65 65
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (65 65
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (65 65
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (65 65 (:REWRITE |(< (/ x) (/ y))|))
 (65 65 (:REWRITE |(< (- x) c)|))
 (65 65 (:REWRITE |(< (- x) (- y))|))
 (31 31 (:REWRITE REDUCE-INTEGERP-+))
 (31 31 (:REWRITE INTEGERP-MINUS-X))
 (31 31 (:META META-INTEGERP-CORRECT))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (25 25 (:REWRITE |(* c (* d x))|))
 (23 23 (:REWRITE REDUCE-RATIONALP-+))
 (23 23 (:REWRITE REDUCE-RATIONALP-*))
 (23 23 (:REWRITE RATIONALP-MINUS-X))
 (23 23 (:META META-RATIONALP-CORRECT))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (13 13 (:REWRITE |(< 0 (/ x))|))
 (13 13 (:REWRITE |(< 0 (* x y))|))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LEMMA-4-1-56
 (673
  634
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (673 634
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (673
     634
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (634 634
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (393 13 (:LINEAR EXPT-<=-1-TWO))
 (392 13 (:LINEAR EXPT-<-1-TWO))
 (230 24
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (224 224
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (224 224
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (224 224
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (198 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (182 143
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (177 26
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (174 26
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (166 13 (:LINEAR EXPT-<=-1-ONE))
 (165 13 (:LINEAR EXPT->=-1-TWO))
 (165 13 (:LINEAR EXPT->-1-TWO))
 (165 13 (:LINEAR EXPT-<-1-ONE))
 (162 13 (:LINEAR EXPT-X->=-X))
 (162 13 (:LINEAR EXPT->=-1-ONE))
 (161 13 (:LINEAR EXPT-X->-X))
 (161 13 (:LINEAR EXPT->-1-ONE))
 (116 20 (:REWRITE ACL2-NUMBERP-X))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (111 111
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (111 111
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (111 111
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (111 111
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (111 111
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (111 111
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (92 52 (:REWRITE DEFAULT-EXPT-1))
 (78 24 (:REWRITE SIMPLIFY-SUMS-<))
 (61 61
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (61 61
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (61 61
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (61 61
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (50 50 (:REWRITE |(expt (- x) n)|))
 (48 12 (:REWRITE RATIONALP-X))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (26 26
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (26 26 (:REWRITE INTEGERP-<-CONSTANT))
 (26 26 (:REWRITE CONSTANT-<-INTEGERP))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< c (- x))|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< (/ x) (/ y))|))
 (26 26 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE |(< (- x) (- y))|))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 14 (:REWRITE REDUCE-INTEGERP-+))
 (14 14 (:REWRITE INTEGERP-MINUS-X))
 (14 14 (:REWRITE |(* c (* d x))|))
 (14 14 (:META META-INTEGERP-CORRECT))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LEMMA-4-1-57
 (5428 649
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3326 77
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (3326 77
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (2298
  2298
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2298
      2298
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2298
     2298
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2298 2298
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1435 77
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (1175 77
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (1175 77
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (649 649
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (636 78
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (636 78
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (170 18
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (126 126
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (126 126
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (126 126
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (126 126
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (126 126
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (126 126 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (126 2 (:LINEAR FL-DEF))
 (120 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (114 17 (:REWRITE SIMPLIFY-SUMS-<))
 (78 78
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (78 78
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (77 77
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (70 4 (:REWRITE RATIONALP-X))
 (70 2 (:LINEAR MOD-BND-2))
 (63 14 (:REWRITE DEFAULT-MOD-RATIO))
 (40 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (35 2 (:REWRITE ODD-EXPT-THM))
 (35 2 (:LINEAR EXPT-<=-1-TWO))
 (34 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (29 29 (:REWRITE DEFAULT-EXPT-1))
 (29 29 (:REWRITE |(expt 1/c n)|))
 (29 29 (:REWRITE |(expt (- x) n)|))
 (23 23
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22 6 (:REWRITE ACL2-NUMBERP-X))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (20 14 (:REWRITE DEFAULT-MOD-1))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18 (:REWRITE CONSTANT-<-INTEGERP))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (18 18 (:REWRITE |(< (- x) (- y))|))
 (18 2 (:LINEAR MOD-BOUNDS-3))
 (14 14 (:REWRITE DEFAULT-MOD-2))
 (13 13 (:REWRITE |(mod x 2)| . 2))
 (13 9 (:REWRITE |(+ c (+ d x))|))
 (10 10 (:REWRITE |(expt c (* d n))|))
 (9 1 (:REWRITE |(* (if a b c) x)|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (8 4 (:TYPE-PRESCRIPTION NATP-MOD))
 (8 4 (:LINEAR MOD-BOUNDS-2))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (4 4 (:TYPE-PRESCRIPTION NATP-MOD-2))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(* (- x) y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR MOD-BND-3))
 (2 2 (:LINEAR FL-MONOTONE-LINEAR))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-58
     (29 1 (:LINEAR MOD-BND-2))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (22 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (22 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (22 22 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (22 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (22 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (14 14
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 4 (:REWRITE DEFAULT-MOD-RATIO))
     (8 4 (:TYPE-PRESCRIPTION NATP-MOD))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:LINEAR FL-MONOTONE-LINEAR))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 1 (:LINEAR MOD-BOUNDS-3))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4 (:TYPE-PRESCRIPTION NATP-MOD-2))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE |(mod x 2)| . 2))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:LINEAR N<=FL-LINEAR))
     (2 2 (:LINEAR MOD-BOUNDS-2))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(* (- x) y)|))
     (1 1 (:LINEAR MOD-BND-3)))
(LEMMA-4-1-59
 (732
  732
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (732 732
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (732
     732
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (732 732
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (565 565
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (565 565
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (565 565
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (294 264
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (294 264
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (294 264
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (120 18
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (116 20 (:REWRITE ACL2-NUMBERP-X))
 (100 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (100 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (100 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (88 18 (:REWRITE SIMPLIFY-SUMS-<))
 (88 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (55 55 (:REWRITE DEFAULT-EXPT-1))
 (55 55 (:REWRITE |(expt 1/c n)|))
 (55 55 (:REWRITE |(expt (- x) n)|))
 (48 12 (:REWRITE RATIONALP-X))
 (44 44 (:REWRITE |(- (* c x))|))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (23 23 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (23 23 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (23 23 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (23 23
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (23 23
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (23 23 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (23 23
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (23 23
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (23 23 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:META META-INTEGERP-CORRECT))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 4 (:REWRITE DEFAULT-MOD-RATIO))
 (14 14 (:REWRITE |(* c (* d x))|))
 (13 13 (:REWRITE |(expt c (* d n))|))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4G-EXPT-A))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3Q-EXPT-A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3L))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3G-EXPT-A))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2Q-EXPT-A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2L))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2G-EXPT-A))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1Q-EXPT-A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1L))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1G-EXPT-A))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (8 4 (:REWRITE DEFAULT-MOD-1))
 (8 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (4 4 (:REWRITE DEFAULT-MOD-2))
 (4 4 (:REWRITE |(mod x 2)| . 2))
 (4 4 (:LINEAR FL-MONOTONE-LINEAR))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-60
 (1225
  1225
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1225
      1225
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1225
     1225
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1225 1225
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (429 429
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (429 429
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (429 429
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (338 30
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (216 25 (:REWRITE SIMPLIFY-SUMS-<))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (155 4 (:REWRITE ODD-EXPT-THM))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (85 85
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (83 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (70 31 (:REWRITE |(< (- x) (- y))|))
 (41 31 (:REWRITE |(< (- x) c)|))
 (35 35 (:REWRITE DEFAULT-EXPT-1))
 (35 35 (:REWRITE |(expt 1/c n)|))
 (35 35 (:REWRITE |(expt (- x) n)|))
 (34 34 (:REWRITE THE-FLOOR-BELOW))
 (34 34 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (31 31 (:REWRITE INTEGERP-<-CONSTANT))
 (31 31 (:REWRITE CONSTANT-<-INTEGERP))
 (31 31
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (31 31
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (31 31
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (31 31
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (31 31 (:REWRITE |(< c (- x))|))
 (31 31
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (31 31
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (31 31
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (31 31
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (31 31 (:REWRITE |(< (/ x) (/ y))|))
 (30 30 (:REWRITE |(- (* c x))|))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 5 (:REWRITE ACL2-NUMBERP-X))
 (18 7 (:REWRITE INTEGERP-MINUS-X))
 (12 3 (:REWRITE RATIONALP-X))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (8 6 (:REWRITE |(+ c (+ d x))|))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(LEMMA-4-1-61
 (461
  461
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (461 461
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (461
     461
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (461 461
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (301 301
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (301 301
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (301 301
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (174 30 (:REWRITE ACL2-NUMBERP-X))
 (169 169
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (169 169
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (169 169
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (132 132
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (102 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (72 18 (:REWRITE RATIONALP-X))
 (54 17 (:REWRITE SIMPLIFY-SUMS-<))
 (54 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (46 46
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (46 46
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (46 46
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (46 46
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (28 28 (:REWRITE DEFAULT-EXPT-1))
 (28 28 (:REWRITE |(expt 1/c n)|))
 (28 28 (:REWRITE |(expt (- x) n)|))
 (23 23 (:REWRITE THE-FLOOR-BELOW))
 (23 23 (:REWRITE THE-FLOOR-ABOVE))
 (23 23
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (- x))|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE |(< (- x) c)|))
 (23 23 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:REWRITE |(- (* c x))|))
 (20 20 (:META META-INTEGERP-CORRECT))
 (18 18 (:REWRITE REDUCE-RATIONALP-+))
 (18 18 (:REWRITE REDUCE-RATIONALP-*))
 (18 18 (:REWRITE RATIONALP-MINUS-X))
 (18 18 (:META META-RATIONALP-CORRECT))
 (12 12 (:REWRITE |(* c (* d x))|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(LEMMA-4-1-62
 (191
  191
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (191 191
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (191
     191
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (191 191
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (176 176
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (176 176
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (176 176
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (89 89
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (89 89
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (89 89
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (89 89
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (87 87
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (87 87
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (87 87
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (87 87
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (87 87
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (87 87
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (87 15 (:REWRITE ACL2-NUMBERP-X))
 (58 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 9 (:REWRITE RATIONALP-X))
 (34 12 (:REWRITE SIMPLIFY-SUMS-<))
 (34 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (14 14 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE CONSTANT-<-INTEGERP))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< c (- x))|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (14 14 (:REWRITE |(< (- x) (- y))|))
 (11 11 (:REWRITE REDUCE-INTEGERP-+))
 (11 11 (:REWRITE INTEGERP-MINUS-X))
 (11 11 (:META META-INTEGERP-CORRECT))
 (10 10 (:REWRITE |(- (* c x))|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE |(* c (* d x))|))
 (4 4 (:LINEAR FL-MONOTONE-LINEAR))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR N<=FL-LINEAR)))
(LEMMA-4-1-C
 (1245
  1170
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1245
      1170
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1245
     1170
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1170 1170
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (393 13 (:LINEAR EXPT-<=-1-TWO))
 (392 13 (:LINEAR EXPT-<-1-TWO))
 (389 50
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (316 241
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (301 141 (:REWRITE DEFAULT-EXPT-1))
 (282 50 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (270 270
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (270 270
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (270 270
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (240 48 (:REWRITE ACL2-NUMBERP-X))
 (177 26
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (174 26
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (173 50 (:REWRITE SIMPLIFY-SUMS-<))
 (166 13 (:LINEAR EXPT-<=-1-ONE))
 (165 13 (:LINEAR EXPT->=-1-TWO))
 (165 13 (:LINEAR EXPT->-1-TWO))
 (165 13 (:LINEAR EXPT-<-1-ONE))
 (162 13 (:LINEAR EXPT-X->=-X))
 (162 13 (:LINEAR EXPT->=-1-ONE))
 (161 13 (:LINEAR EXPT-X->-X))
 (161 13 (:LINEAR EXPT->-1-ONE))
 (133 133 (:REWRITE |(expt (- x) n)|))
 (96 24 (:REWRITE RATIONALP-X))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3N-EXPT-C))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3K-EXPT))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2N-EXPT-C))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2K-EXPT))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1N-EXPT-C))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1K-EXPT))
 (81 81
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (72 72
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (72 72
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (72 72
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (72 72
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (59 59 (:REWRITE THE-FLOOR-BELOW))
 (59 59 (:REWRITE THE-FLOOR-ABOVE))
 (59 59
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (59 59
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (59 59
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (59 59
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (59 59 (:REWRITE INTEGERP-<-CONSTANT))
 (59 59 (:REWRITE CONSTANT-<-INTEGERP))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< c (- x))|))
 (59 59
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (59 59
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< (/ x) (/ y))|))
 (59 59 (:REWRITE |(< (- x) c)|))
 (59 59 (:REWRITE |(< (- x) (- y))|))
 (55 55
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 36 (:REWRITE |(* c (* d x))|))
 (26 26 (:REWRITE REDUCE-INTEGERP-+))
 (26 26 (:REWRITE INTEGERP-MINUS-X))
 (26 26 (:META META-INTEGERP-CORRECT))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (15 15 (:REWRITE |(< y (+ (- c) x))|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (10 10 (:LINEAR FL-MONOTONE-LINEAR))
 (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:LINEAR N<=FL-LINEAR))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(CG-SQRT
 (65 9 (:REWRITE ACL2-NUMBERP-X))
 (33 12 (:REWRITE REDUCE-INTEGERP-+))
 (30 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28 12 (:REWRITE INTEGERP-MINUS-X))
 (28 7 (:REWRITE RATIONALP-X))
 (22 13 (:REWRITE |(< (- x) c)|))
 (22 13 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13 (:REWRITE CONSTANT-<-INTEGERP))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< c (- x))|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (12
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12 (:META META-INTEGERP-CORRECT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (10 1 (:REWRITE |(integerp (- x))|))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7 (:META META-RATIONALP-CORRECT))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(SEED
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(CG-SQRT-2
 (1092
  1092
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1092
      1092
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1092
     1092
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1092 1092
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1092 1092
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (771 188
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (610 178 (:REWRITE SIMPLIFY-SUMS-<))
 (504 18 (:LINEAR EXPT->=-1-TWO))
 (492 18 (:LINEAR EXPT-<=-1-ONE))
 (468 18 (:LINEAR EXPT-X->-X))
 (468 18 (:LINEAR EXPT->-1-ONE))
 (468 18 (:LINEAR EXPT-<-1-TWO))
 (270 198
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (216 18 (:LINEAR EXPT->-1-TWO))
 (216 18 (:LINEAR EXPT-<-1-ONE))
 (198 198 (:REWRITE THE-FLOOR-BELOW))
 (198 198 (:REWRITE THE-FLOOR-ABOVE))
 (198 198
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (198 198
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (198 198
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (198 198 (:REWRITE INTEGERP-<-CONSTANT))
 (198 198 (:REWRITE CONSTANT-<-INTEGERP))
 (198 198
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (198 198
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (198 198
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (198 198
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (198 198 (:REWRITE |(< c (- x))|))
 (198 198
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (198 198
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (198 198
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (198 198
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (198 198 (:REWRITE |(< (/ x) (/ y))|))
 (198 198 (:REWRITE |(< (- x) c)|))
 (198 198 (:REWRITE |(< (- x) (- y))|))
 (198 18 (:LINEAR EXPT-<=-1-TWO))
 (139 139
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (96 80 (:REWRITE DEFAULT-EXPT-1))
 (85 85
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (80 80 (:REWRITE |(expt 1/c n)|))
 (80 80 (:REWRITE |(expt (- x) n)|))
 (36 36
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (36 36
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (36 36
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (36 36
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 9 (:REWRITE RATIONALP-X))
 (26 26 (:REWRITE |(< (+ c/d x) y)|))
 (26 26 (:REWRITE |(< (+ (- c) x) y)|))
 (20 20 (:REWRITE |(* (- x) y)|))
 (18 18 (:REWRITE ZP-OPEN))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< 0 (/ x))|))
 (18 18 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (18 18 (:LINEAR EXPT-LINEAR-UPPER-<))
 (18 18 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (18 18 (:LINEAR EXPT-LINEAR-LOWER-<))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (9 9 (:META META-INTEGERP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|)))
(CG-SQRT-LEMMA
 (1050
  1050
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1050
      1050
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1050
     1050
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1050 1050
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1050 1050
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (550 550
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (500 62
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (473 58 (:REWRITE SIMPLIFY-SUMS-<))
 (373 373
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (62 62 (:REWRITE THE-FLOOR-BELOW))
 (62 62 (:REWRITE THE-FLOOR-ABOVE))
 (62 62 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (62 62
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (62 62
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (62 62
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (62 62
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (62 62 (:REWRITE INTEGERP-<-CONSTANT))
 (62 62 (:REWRITE CONSTANT-<-INTEGERP))
 (62 62
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (62 62
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (62 62
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (62 62
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (62 62 (:REWRITE |(< c (- x))|))
 (62 62
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (62 62
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (62 62
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (62 62
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (62 62 (:REWRITE |(< (/ x) (/ y))|))
 (62 62 (:REWRITE |(< (- x) c)|))
 (62 62 (:REWRITE |(< (- x) (- y))|))
 (52 43 (:REWRITE DEFAULT-EXPT-1))
 (43 43 (:REWRITE |(expt 1/c n)|))
 (43 43 (:REWRITE |(expt (- x) n)|))
 (28 7 (:REWRITE RATIONALP-X))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE ZP-OPEN))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE |(* (- x) y)|))
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-RATIONALP-CORRECT))
 (7 7 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|)))
(NATP-CG)
(LEMMA-4-2-1
 (252 17
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (73
  73
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (54 1
     (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (53 1
     (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (34 1 (:LINEAR EXPT->=-1-ONE))
 (34 1 (:LINEAR EXPT-<=-1-TWO))
 (33 1 (:LINEAR EXPT->-1-ONE))
 (33 1 (:LINEAR EXPT-<-1-TWO))
 (32 8 (:REWRITE SIMPLIFY-SUMS-<))
 (32 1 (:LINEAR EXPT-X->=-X))
 (32 1 (:LINEAR EXPT-X->-X))
 (24 4 (:REWRITE |(+ y (+ x z))|))
 (22 10 (:REWRITE NORMALIZE-ADDENDS))
 (22 10 (:REWRITE |(+ c (+ d x))|))
 (20 4 (:REWRITE |(+ y x)|))
 (17 17 (:REWRITE THE-FLOOR-BELOW))
 (17 17 (:REWRITE THE-FLOOR-ABOVE))
 (17 17
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE CONSTANT-<-INTEGERP))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< c (- x))|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE |(+ 0 x)|))
 (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:DEFINITION FIX))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE |(+ x (- x))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(LEMMA-4-2-2
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(LEMMA-4-2-3
 (373 31
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (151
  151
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (151 151
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (151
     151
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (151 151
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (151 151
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (151 151
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (69 3 (:REWRITE ODD-EXPT-THM))
 (68 2 (:LINEAR EXPT->=-1-ONE))
 (68 2 (:LINEAR EXPT-<=-1-TWO))
 (66 2 (:LINEAR EXPT->-1-ONE))
 (66 2 (:LINEAR EXPT-<-1-TWO))
 (64 2 (:LINEAR EXPT-X->=-X))
 (64 2 (:LINEAR EXPT-X->-X))
 (44 17 (:REWRITE SIMPLIFY-SUMS-<))
 (44 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (35 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (35 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (31 31 (:REWRITE THE-FLOOR-BELOW))
 (31 31 (:REWRITE THE-FLOOR-ABOVE))
 (31 31
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (28 14 (:REWRITE |(+ c (+ d x))|))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< c (- x))|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE |(< (- x) c)|))
 (17 17 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE |(+ 0 x)|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-4
 (1675
  1675
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1675
      1675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1675
     1675
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1675 1675
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (934 104
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (366 8 (:LINEAR EXPT-<=-1-TWO))
 (360 8 (:LINEAR EXPT-<-1-TWO))
 (332 65 (:REWRITE SIMPLIFY-SUMS-<))
 (231 8 (:LINEAR EXPT-<=-1-ONE))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (212 16
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (204 8 (:LINEAR EXPT->=-1-TWO))
 (204 8 (:LINEAR EXPT->-1-TWO))
 (204 8 (:LINEAR EXPT-<-1-ONE))
 (150 55 (:REWRITE DEFAULT-EXPT-1))
 (124 70
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (104 104 (:REWRITE THE-FLOOR-BELOW))
 (104 104 (:REWRITE THE-FLOOR-ABOVE))
 (104 104
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (104 104
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (77 41 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (70 70 (:REWRITE INTEGERP-<-CONSTANT))
 (70 70 (:REWRITE CONSTANT-<-INTEGERP))
 (70 70
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (70 70
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (70 70
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (70 70
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (70 70 (:REWRITE |(< c (- x))|))
 (70 70
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (70 70
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (70 70
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (70 70
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (70 70 (:REWRITE |(< (/ x) (/ y))|))
 (70 70 (:REWRITE |(< (- x) c)|))
 (70 70 (:REWRITE |(< (- x) (- y))|))
 (55 55 (:REWRITE |(expt 1/c n)|))
 (55 55 (:REWRITE |(expt (- x) n)|))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (33 33 (:REWRITE |(expt c (* d n))|))
 (33 33 (:REWRITE |(< x (+ c/d y))|))
 (22 22 (:REWRITE |(< 0 (* x y))|))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3)))
(LEMMA-4-2-5
 (1782
  1782
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1782
      1782
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1782
     1782
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1782 1782
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (948 118
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (397 9 (:LINEAR EXPT-<=-1-TWO))
 (390 9 (:LINEAR EXPT-<-1-TWO))
 (347 77 (:REWRITE SIMPLIFY-SUMS-<))
 (266 9 (:LINEAR EXPT-<=-1-ONE))
 (247 18
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (238 9 (:LINEAR EXPT->=-1-TWO))
 (238 9 (:LINEAR EXPT->-1-TWO))
 (238 9 (:LINEAR EXPT-<-1-ONE))
 (232 232
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (190 57 (:REWRITE DEFAULT-EXPT-1))
 (138 84
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (118 118 (:REWRITE THE-FLOOR-BELOW))
 (118 118 (:REWRITE THE-FLOOR-ABOVE))
 (118 118
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (118 118
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (84 84 (:REWRITE INTEGERP-<-CONSTANT))
 (84 84 (:REWRITE CONSTANT-<-INTEGERP))
 (84 84
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (84 84
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (84 84
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (84 84
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (84 84 (:REWRITE |(< c (- x))|))
 (84 84
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (84 84
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (84 84
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (84 84
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (84 84 (:REWRITE |(< (/ x) (/ y))|))
 (84 84 (:REWRITE |(< (- x) c)|))
 (84 84 (:REWRITE |(< (- x) (- y))|))
 (84 48 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (77 43 (:REWRITE |(+ c (+ d x))|))
 (57 57 (:REWRITE |(expt 1/c n)|))
 (57 57 (:REWRITE |(expt (- x) n)|))
 (55 55
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 35 (:REWRITE |(< x (+ c/d y))|))
 (33 33 (:REWRITE |(expt c (* d n))|))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(* (- x) y)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(* c (* d x))|)))
(LEMMA-4-2-6
 (865
  865
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (865 865
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (865
     865
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (865 865
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (682 2 (:REWRITE LEMMA-4-2-2))
 (618 65
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (174 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (165 35 (:REWRITE SIMPLIFY-SUMS-<))
 (145 5 (:LINEAR EXPT-<=-1-TWO))
 (141 5 (:LINEAR EXPT-<-1-TWO))
 (122 67
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (70 43
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (67 67 (:REWRITE THE-FLOOR-BELOW))
 (67 67 (:REWRITE THE-FLOOR-ABOVE))
 (66 66
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (65 65
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (59 40 (:REWRITE DEFAULT-EXPT-1))
 (43 43 (:REWRITE INTEGERP-<-CONSTANT))
 (43 43 (:REWRITE CONSTANT-<-INTEGERP))
 (43 43
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (43 43
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (43 43
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (43 43
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (43 43 (:REWRITE |(< c (- x))|))
 (43 43
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (43 43
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (43 43
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (43 43
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (43 43 (:REWRITE |(< (/ x) (/ y))|))
 (43 43 (:REWRITE |(< (- x) c)|))
 (43 43 (:REWRITE |(< (- x) (- y))|))
 (40 40 (:REWRITE |(expt 1/c n)|))
 (40 40 (:REWRITE |(expt (- x) n)|))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 24 (:REWRITE |(< x (+ c/d y))|))
 (19 19 (:REWRITE |(expt c (* d n))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9 (:REWRITE |(- (* c x))|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(+ (* c x) (* d x))|))
 (2 2 (:REWRITE |(* a (/ a) b)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-7)
(LEMMA-4-2-8
 (562 38
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (214 26 (:REWRITE CONSTANT-<-INTEGERP))
 (178 3 (:LINEAR EXPT-X->=-X))
 (178 3 (:LINEAR EXPT-X->-X))
 (105 3 (:LINEAR EXPT->=-1-ONE))
 (105 3 (:LINEAR EXPT-<=-1-TWO))
 (102 3 (:LINEAR EXPT->-1-ONE))
 (102 3 (:LINEAR EXPT-<-1-TWO))
 (47
  47
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (36 12 (:REWRITE |(* y (* x z))|))
 (26 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 26
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< c (- x))|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< (/ x) (/ y))|))
 (26 26 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE |(< (- x) (- y))|))
 (22 22 (:REWRITE SIMPLIFY-SUMS-<))
 (22 22
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 22 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE |(* a (/ a) b)|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-9
 (688 79
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (682 2 (:REWRITE LEMMA-4-2-2))
 (597
  597
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (597 597
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (597
     597
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (597 597
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (597 597
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (247 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (238 52
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (195 52 (:REWRITE SIMPLIFY-SUMS-<))
 (169 7 (:LINEAR EXPT-<=-1-TWO))
 (164 7 (:LINEAR EXPT-<-1-TWO))
 (104 5 (:REWRITE ODD-EXPT-THM))
 (88 46 (:REWRITE DEFAULT-EXPT-1))
 (81 54
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (79 79 (:REWRITE THE-FLOOR-BELOW))
 (79 79 (:REWRITE THE-FLOOR-ABOVE))
 (79 79
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (79 79
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (76 76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (54 54 (:REWRITE INTEGERP-<-CONSTANT))
 (54 54 (:REWRITE CONSTANT-<-INTEGERP))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< c (- x))|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) c)|))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (47 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (46 46 (:REWRITE |(expt 1/c n)|))
 (46 46 (:REWRITE |(expt (- x) n)|))
 (42 42
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (41 7 (:LINEAR EXPT-<=-1-ONE))
 (40 7 (:LINEAR EXPT->=-1-TWO))
 (40 7 (:LINEAR EXPT->-1-TWO))
 (40 7 (:LINEAR EXPT-<-1-ONE))
 (23 23 (:REWRITE |(< x (+ c/d y))|))
 (22 22 (:REWRITE |(expt c (* d n))|))
 (15 15 (:REWRITE |(< 0 (* x y))|))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-10
 (377
  377
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (377 377
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (377
     377
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (377 377
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (63 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (54 9 (:REWRITE SIMPLIFY-SUMS-<))
 (33 15
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (24 1 (:LINEAR EXPT-X->=-X))
 (24 1 (:LINEAR EXPT-X->-X))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE |(expt 1/c n)|))
 (21 21 (:REWRITE |(expt (- x) n)|))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< c (- x))|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (15 15 (:REWRITE |(< (- x) c)|))
 (15 15 (:REWRITE |(< (- x) (- y))|))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE |(- (* c x))|))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(LEMMA-4-2-11)
(LEMMA-4-2-12
 (341 1 (:REWRITE LEMMA-4-2-2))
 (325 33
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (319
  319
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (319 319
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (319
     319
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (319 319
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (319 319
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (91 19
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (91 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (82 19 (:REWRITE SIMPLIFY-SUMS-<))
 (69 3 (:LINEAR EXPT-<=-1-TWO))
 (67 3 (:LINEAR EXPT-<-1-TWO))
 (36 3 (:REWRITE ODD-EXPT-THM))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (24 12 (:REWRITE |(+ c (+ d x))|))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 21 (:REWRITE |(expt 1/c n)|))
 (21 21 (:REWRITE |(expt (- x) n)|))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (- x))|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (21 21 (:REWRITE |(< (- x) c)|))
 (21 21 (:REWRITE |(< (- x) (- y))|))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (12 12 (:REWRITE |(+ 0 x)|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(* c (* d x))|)))
(LEMMA-4-2-13
 (351
  351
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (351
     351
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (293 49
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (102 39
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (92 38 (:REWRITE SIMPLIFY-SUMS-<))
 (83 3 (:LINEAR EXPT->=-1-TWO))
 (83 3 (:LINEAR EXPT-<=-1-ONE))
 (80 3 (:LINEAR EXPT-X->-X))
 (80 3 (:LINEAR EXPT->-1-ONE))
 (80 3 (:LINEAR EXPT-<-1-TWO))
 (63 27 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (49 49 (:REWRITE THE-FLOOR-BELOW))
 (49 49 (:REWRITE THE-FLOOR-ABOVE))
 (49 49
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (49 49
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (43 43
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (39 39
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (39 39 (:REWRITE INTEGERP-<-CONSTANT))
 (39 39 (:REWRITE CONSTANT-<-INTEGERP))
 (39 39
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (39 39
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (39 39
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (39 39
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (39 39 (:REWRITE |(< c (- x))|))
 (39 39
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (39 39
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (39 39
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (39 39
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (39 39 (:REWRITE |(< (/ x) (/ y))|))
 (39 39 (:REWRITE |(< (- x) c)|))
 (39 39 (:REWRITE |(< (- x) (- y))|))
 (36 9 (:REWRITE RATIONALP-X))
 (35 3 (:LINEAR EXPT->-1-TWO))
 (35 3 (:LINEAR EXPT-<=-1-TWO))
 (35 3 (:LINEAR EXPT-<-1-ONE))
 (25 25 (:REWRITE |arith (* c (* d x))|))
 (22 12 (:REWRITE |(+ c (+ d x))|))
 (14 14
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE |arith (* (- x) y)|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (9 9 (:META META-INTEGERP-CORRECT))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:REWRITE |arith (expt 1/c n)|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3)))
(LEMMA-4-2-14
 (682 2 (:REWRITE LEMMA-4-2-2))
 (535 47
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (143
  143
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (143 143
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (143
     143
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (143 143
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (143 143
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (103 4 (:REWRITE ODD-EXPT-THM))
 (103 4 (:LINEAR EXPT-<=-1-TWO))
 (100 4 (:LINEAR EXPT-<-1-TWO))
 (52 25 (:REWRITE SIMPLIFY-SUMS-<))
 (52 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (47 47 (:REWRITE THE-FLOOR-BELOW))
 (47 47 (:REWRITE THE-FLOOR-ABOVE))
 (47 47
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (47 47
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (40 20 (:REWRITE |(+ c (+ d x))|))
 (27 27
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (27 27 (:REWRITE INTEGERP-<-CONSTANT))
 (27 27 (:REWRITE CONSTANT-<-INTEGERP))
 (27 27
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (27 27
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (27 27
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (27 27
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (27 27 (:REWRITE |(< c (- x))|))
 (27 27
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (27 27
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (27 27
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (27 27
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (27 27 (:REWRITE |(< (/ x) (/ y))|))
 (27 27 (:REWRITE |(< (- x) c)|))
 (27 27 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE |(+ 0 x)|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(expt c (* d n))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-15
 (2047 7 (:REWRITE LEMMA-4-2-2))
 (1734 160
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1509
      1509
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1509 1509
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1509 1509
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (339 339
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (323 86 (:REWRITE SIMPLIFY-SUMS-<))
 (282 9 (:LINEAR EXPT-<=-1-TWO))
 (279 15 (:REWRITE ODD-EXPT-THM))
 (274 9 (:LINEAR EXPT-<-1-TWO))
 (160 160 (:REWRITE THE-FLOOR-BELOW))
 (160 160 (:REWRITE THE-FLOOR-ABOVE))
 (160 160
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (160 160
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (153 99
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (140 67 (:REWRITE |(+ c (+ d x))|))
 (99 99 (:REWRITE INTEGERP-<-CONSTANT))
 (99 99 (:REWRITE CONSTANT-<-INTEGERP))
 (99 99
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (99 99
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (99 99
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (99 99
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (99 99 (:REWRITE |(< c (- x))|))
 (99 99
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (99 99
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (99 99
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (99 99
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (99 99 (:REWRITE |(< (/ x) (/ y))|))
 (99 99 (:REWRITE |(< (- x) c)|))
 (99 99 (:REWRITE |(< (- x) (- y))|))
 (60 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (52 9 (:LINEAR EXPT-<=-1-ONE))
 (51 9 (:LINEAR EXPT->=-1-TWO))
 (51 9 (:LINEAR EXPT->-1-TWO))
 (51 9 (:LINEAR EXPT-<-1-ONE))
 (50 50 (:REWRITE |(< x (+ c/d y))|))
 (50 43 (:REWRITE DEFAULT-EXPT-1))
 (43 43 (:REWRITE |(expt 1/c n)|))
 (43 43 (:REWRITE |(expt (- x) n)|))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE |(< 0 (* x y))|))
 (23 23 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(expt c (* d n))|))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 16 (:REWRITE |(< (* x y) 0)|))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(* (- x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-16)
(LEMMA-4-2-18
 (940
  940
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (940 940
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (940
     940
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (940 940
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (682 2 (:REWRITE LEMMA-4-2-2))
 (543 55
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (263 33
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (263 33 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (254 33 (:REWRITE SIMPLIFY-SUMS-<))
 (238 238
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (105 6 (:REWRITE ODD-EXPT-THM))
 (103 4 (:LINEAR EXPT-<=-1-TWO))
 (100 4 (:LINEAR EXPT-<-1-TWO))
 (62 35
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (55 55 (:REWRITE THE-FLOOR-BELOW))
 (55 55 (:REWRITE THE-FLOOR-ABOVE))
 (55 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (55 43 (:REWRITE DEFAULT-EXPT-1))
 (53 33 (:REWRITE |(+ c (+ d x))|))
 (50 50
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (43 43 (:REWRITE |(expt 1/c n)|))
 (43 43 (:REWRITE |(expt (- x) n)|))
 (35 35 (:REWRITE INTEGERP-<-CONSTANT))
 (35 35 (:REWRITE CONSTANT-<-INTEGERP))
 (35 35
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (35 35
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (35 35
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (35 35
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (35 35 (:REWRITE |(< c (- x))|))
 (35 35
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (35 35
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (35 35
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (35 35
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (35 35 (:REWRITE |(< (/ x) (/ y))|))
 (35 35 (:REWRITE |(< (- x) c)|))
 (35 35 (:REWRITE |(< (- x) (- y))|))
 (33 33
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (33 33
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (33 33
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (20 20 (:REWRITE |(+ 0 x)|))
 (16 16 (:REWRITE |(expt c (* d n))|))
 (14 14 (:REWRITE |(- (* c x))|))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(* c (* d x))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-19
 (908
  908
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (908 908
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (908
     908
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (908 908
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (682 2 (:REWRITE LEMMA-4-2-2))
 (548 60
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (390 38
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (246 246
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (227 33 (:REWRITE SIMPLIFY-SUMS-<))
 (162 162
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (162 162
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (162 162
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (105 6 (:REWRITE ODD-EXPT-THM))
 (103 4 (:LINEAR EXPT-<=-1-TWO))
 (100 4 (:LINEAR EXPT-<-1-TWO))
 (67 40
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 60
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (58 38 (:REWRITE |(+ c (+ d x))|))
 (55 43 (:REWRITE DEFAULT-EXPT-1))
 (51 51
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (43 43 (:REWRITE |(expt 1/c n)|))
 (43 43 (:REWRITE |(expt (- x) n)|))
 (40 40 (:REWRITE INTEGERP-<-CONSTANT))
 (40 40 (:REWRITE CONSTANT-<-INTEGERP))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< c (- x))|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< (/ x) (/ y))|))
 (40 40 (:REWRITE |(< (- x) c)|))
 (40 40 (:REWRITE |(< (- x) (- y))|))
 (33 33
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (33 33
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (33 33
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (25 25 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE |(expt c (* d n))|))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(* c (* d x))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-2-20
     (14 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(LEMMA-4-2
 (3772
  3772
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3772
      3772
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3772
     3772
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3772 3772
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2289 241
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2037 6 (:REWRITE LEMMA-4-2-2))
 (1428 609
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (1428 609
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (827 147
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (609 609
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (591 144 (:REWRITE SIMPLIFY-SUMS-<))
 (524 524
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (515 20 (:LINEAR EXPT-<=-1-TWO))
 (378 152
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (372 20 (:LINEAR EXPT-<-1-TWO))
 (356 21 (:REWRITE ODD-EXPT-THM))
 (248 152
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (241 241 (:REWRITE THE-FLOOR-BELOW))
 (241 241 (:REWRITE THE-FLOOR-ABOVE))
 (241 241
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (241 241
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (185 101 (:REWRITE |(+ c (+ d x))|))
 (161 152 (:REWRITE |(< c (- x))|))
 (152 152 (:REWRITE INTEGERP-<-CONSTANT))
 (152 152 (:REWRITE CONSTANT-<-INTEGERP))
 (152 152
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (152 152
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (152 152
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (152 152
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (152 152
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (152 152
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (152 152
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (152 152 (:REWRITE |(< (/ x) (/ y))|))
 (152 152 (:REWRITE |(< (- x) c)|))
 (152 152 (:REWRITE |(< (- x) (- y))|))
 (110 104 (:REWRITE DEFAULT-EXPT-1))
 (104 104 (:REWRITE |(expt 1/c n)|))
 (104 104 (:REWRITE |(expt (- x) n)|))
 (78 78 (:REWRITE |(< x (+ c/d y))|))
 (77 6 (:REWRITE REDUCE-INTEGERP-+))
 (77 6 (:META META-INTEGERP-CORRECT))
 (75 75
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (37 37 (:REWRITE |(expt c (* d n))|))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (29 29
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (29 29
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (29 29 (:REWRITE |(equal c (/ x))|))
 (29 29 (:REWRITE |(equal c (- x))|))
 (29 29 (:REWRITE |(equal (/ x) c)|))
 (29 29 (:REWRITE |(equal (/ x) (/ y))|))
 (29 29 (:REWRITE |(equal (- x) c)|))
 (29 29 (:REWRITE |(equal (- x) (- y))|))
 (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (27 27
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (27 27
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (27 27
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (27 27 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<))
 (20 20 (:LINEAR EXPT-LINEAR-LOWER-<))
 (20 20 (:LINEAR EXPT->=-1-TWO))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT-<=-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (19 19 (:REWRITE |(< (* x y) 0)|))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE |(* c (* d x))|))
 (5 5
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(< (/ x) 0)|)))
(DIGIT)
(ROOT
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT)))
(LEMMA-4-3-1
 (388 46
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (345 3
      (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (341 1 (:REWRITE LEMMA-4-2-2))
 (318 6 (:REWRITE |(< (+ (- c) x) y)|))
 (280 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (164
  164
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (164 164
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (164
     164
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (164 164
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (163 25 (:REWRITE SIMPLIFY-SUMS-<))
 (88 3 (:LINEAR EXPT-X->=-X))
 (88 3 (:LINEAR EXPT-X->-X))
 (69 9 (:REWRITE |(+ y (+ x z))|))
 (69 3 (:REWRITE ODD-EXPT-THM))
 (69 3 (:LINEAR EXPT-<=-1-TWO))
 (67 3 (:LINEAR EXPT-<-1-TWO))
 (55 28
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (47 29
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (46 46 (:REWRITE THE-FLOOR-BELOW))
 (46 46 (:REWRITE THE-FLOOR-ABOVE))
 (46 46
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< c (- x))|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< (/ x) (/ y))|))
 (29 29 (:REWRITE |(< (- x) c)|))
 (29 29 (:REWRITE |(< (- x) (- y))|))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 3 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE BITS-NEG))
 (3 3 (:REWRITE |(expt c (* d n))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(* c (* d x))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(LEMMA-4-3-2
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(LEMMA-4-3-3)
(LEMMA-4-3-4)
(LEMMA-4-3-5
 (2420 18
       (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (2284 76 (:REWRITE |(< (+ (- c) x) y)|))
 (1516 192
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (748 18 (:REWRITE BITS-NEG))
 (682 2 (:REWRITE LEMMA-4-2-2))
 (534
  534
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (534 534
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (534
     534
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (534 534
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (295 295
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (236 178 (:REWRITE |(+ c (+ d x))|))
 (192 192 (:REWRITE THE-FLOOR-BELOW))
 (192 192 (:REWRITE THE-FLOOR-ABOVE))
 (192 192
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (192 192
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (176 6 (:LINEAR EXPT-X->=-X))
 (176 6 (:LINEAR EXPT-X->-X))
 (171 135
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (138 6 (:REWRITE ODD-EXPT-THM))
 (138 6 (:LINEAR EXPT-<=-1-TWO))
 (135 135 (:REWRITE INTEGERP-<-CONSTANT))
 (135 135 (:REWRITE CONSTANT-<-INTEGERP))
 (135 135
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (135 135
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (135 135
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (135 135
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (135 135 (:REWRITE |(< c (- x))|))
 (135 135
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (135 135
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (135 135
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (135 135
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (135 135 (:REWRITE |(< (/ x) (/ y))|))
 (135 135 (:REWRITE |(< (- x) c)|))
 (135 135 (:REWRITE |(< (- x) (- y))|))
 (134 10 (:REWRITE ZP-OPEN))
 (134 6 (:LINEAR EXPT-<-1-TWO))
 (102 102 (:REWRITE |(< x (+ c/d y))|))
 (94 94 (:REWRITE |(< (+ c/d x) y)|))
 (82 82 (:REWRITE FOLD-CONSTS-IN-+))
 (82 82 (:REWRITE |(< y (+ (- c) x))|))
 (63 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (63 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (63 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (46 46 (:REWRITE |(- (* c x))|))
 (25 25 (:REWRITE DEFAULT-EXPT-1))
 (25 25 (:REWRITE |(expt 1/c n)|))
 (25 25 (:REWRITE |(expt (- x) n)|))
 (20 20 (:REWRITE |(< (* x y) 0)|))
 (17 17 (:REWRITE |(< 0 (* x y))|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9 (:REWRITE |(expt c (* d n))|))
 (8 4 (:REWRITE |(+ (- x) (* c x))|))
 (6 6 (:REWRITE |(* (- x) y)|))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(LEMMA-4-3-6
 (5115 15 (:REWRITE LEMMA-4-2-2))
 (4254 467
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2092 277
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2062 38 (:REWRITE |(< (+ (- c) x) y)|))
 (1606
  1606
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1606
      1606
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1606
     1606
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1606 1606
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1606 1606
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1331 258 (:REWRITE SIMPLIFY-SUMS-<))
 (872 29 (:LINEAR EXPT-X->=-X))
 (872 29 (:LINEAR EXPT-X->-X))
 (797 38 (:REWRITE ODD-EXPT-THM))
 (755 29 (:LINEAR EXPT-<=-1-TWO))
 (733 29 (:LINEAR EXPT-<-1-TWO))
 (619 277
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (500 293
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (467 467 (:REWRITE THE-FLOOR-BELOW))
 (467 467 (:REWRITE THE-FLOOR-ABOVE))
 (467 467
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (467 467
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (362 207 (:REWRITE |(+ c (+ d x))|))
 (293 293 (:REWRITE INTEGERP-<-CONSTANT))
 (293 293 (:REWRITE CONSTANT-<-INTEGERP))
 (293 293
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (293 293
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (293 293
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (293 293
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (293 293 (:REWRITE |(< c (- x))|))
 (293 293
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (293 293
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (293 293
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (293 293
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (293 293 (:REWRITE |(< (/ x) (/ y))|))
 (293 293 (:REWRITE |(< (- x) c)|))
 (293 293 (:REWRITE |(< (- x) (- y))|))
 (181 181 (:REWRITE |(< x (+ c/d y))|))
 (180 180
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (160 15
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (160 15
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (158 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (147 147
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (82 82 (:REWRITE |(< (+ c/d x) y)|))
 (78 78 (:REWRITE DEFAULT-EXPT-1))
 (78 78 (:REWRITE |(expt 1/c n)|))
 (78 78 (:REWRITE |(expt (- x) n)|))
 (73 73 (:REWRITE |(< 0 (* x y))|))
 (70 70 (:REWRITE |(< y (+ (- c) x))|))
 (58 58
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (58 58
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (58 58
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (58 58
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (49 49 (:REWRITE |(< (* x y) 0)|))
 (35 35 (:REWRITE |(expt c (* d n))|))
 (31 31 (:REWRITE FOLD-CONSTS-IN-+))
 (29 29 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (29 29 (:LINEAR EXPT-LINEAR-UPPER-<))
 (29 29 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (29 29 (:LINEAR EXPT-LINEAR-LOWER-<))
 (29 29 (:LINEAR EXPT->=-1-TWO))
 (29 29 (:LINEAR EXPT->-1-TWO))
 (29 29 (:LINEAR EXPT-<=-1-ONE))
 (29 29 (:LINEAR EXPT-<-1-ONE))
 (19 19 (:REWRITE BITS-NEG))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (15 15 (:REWRITE |(equal c (/ x))|))
 (15 15 (:REWRITE |(equal c (- x))|))
 (15 15 (:REWRITE |(equal (/ x) c)|))
 (15 15 (:REWRITE |(equal (/ x) (/ y))|))
 (15 15 (:REWRITE |(equal (- x) c)|))
 (15 15 (:REWRITE |(equal (- x) (- y))|))
 (10 10 (:REWRITE |(- (* c x))|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (7 7 (:REWRITE |(* (- x) y)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(LEMMA-4-3-7
 (483 44
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (341 1 (:REWRITE LEMMA-4-2-2))
 (285 1 (:REWRITE BITS-TAIL-2))
 (158
  158
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (158 158
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (158
     158
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (158 158
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (158 158
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (120 4 (:LINEAR EXPT-X->=-X))
 (120 4 (:LINEAR EXPT-X->-X))
 (103 4 (:LINEAR EXPT-<=-1-TWO))
 (69 3 (:REWRITE ODD-EXPT-THM))
 (68 4 (:LINEAR EXPT-<-1-TWO))
 (50 23 (:REWRITE SIMPLIFY-SUMS-<))
 (50 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (44 44 (:REWRITE THE-FLOOR-BELOW))
 (44 44 (:REWRITE THE-FLOOR-ABOVE))
 (44 44
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (44 44
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (34 25
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (25 25 (:REWRITE INTEGERP-<-CONSTANT))
 (25 25 (:REWRITE CONSTANT-<-INTEGERP))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (25 25 (:REWRITE |(< (- x) c)|))
 (25 25 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(expt c (* d n))|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(LEMMA-4-3
 (1744 5 (:REWRITE LEMMA-4-2-2))
 (1549 156
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (834
  834
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (834 834
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (834
     834
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (834 834
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (352 12 (:LINEAR EXPT-X->=-X))
 (352 12 (:LINEAR EXPT-X->-X))
 (286 34
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (276 12 (:LINEAR EXPT-<=-1-TWO))
 (268 12 (:LINEAR EXPT-<-1-TWO))
 (210 91 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (190 91 (:REWRITE SIMPLIFY-SUMS-<))
 (170 98
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (163 156
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (163 156
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (156 156 (:REWRITE THE-FLOOR-BELOW))
 (156 156 (:REWRITE THE-FLOOR-ABOVE))
 (140 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (116 98 (:REWRITE INTEGERP-<-CONSTANT))
 (114 57 (:REWRITE |(+ c (+ d x))|))
 (107 99
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (105 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (99 99
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (99 99
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (99 99
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (99 99
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (99 99
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (99 99
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (99 99
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (99 99 (:REWRITE |(< (/ x) (/ y))|))
 (99 99 (:REWRITE |(< (- x) (- y))|))
 (98 98 (:REWRITE CONSTANT-<-INTEGERP))
 (98 98 (:REWRITE |(< c (- x))|))
 (98 98 (:REWRITE |(< (- x) c)|))
 (80 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (75 4 (:REWRITE |(< 0 (/ x))|))
 (72 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (72 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (57 57 (:REWRITE |(+ 0 x)|))
 (41 41 (:REWRITE DEFAULT-EXPT-1))
 (41 41 (:REWRITE |(expt 1/c n)|))
 (41 41 (:REWRITE |(expt (- x) n)|))
 (41 41 (:REWRITE |(< x (+ c/d y))|))
 (34 34
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (29 29 (:REWRITE |(< 0 (* x y))|))
 (27 27 (:REWRITE |(expt c (* d n))|))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE ZP-OPEN))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (11 11 (:REWRITE |(- (* c x))|))
 (11 3 (:REWRITE ACL2-NUMBERP-X))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 1 (:REWRITE DEFAULT-DIVIDE))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (8 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (6 3
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (6 1 (:REWRITE |(/ (expt x n))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (4 1 (:REWRITE RATIONALP-X))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:META META-RATIONALP-CORRECT)))