(RTL::DIVIDES (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::LEMMA0
     (13 2
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (12 3 (:REWRITE RATIONALP-X))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE DEFAULT-TIMES-2))
     (4 4 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::LEMMA1
     (39 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-1))
     (17 17
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (16 4 (:REWRITE RATIONALP-X))
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (15 15 (:REWRITE DEFAULT-TIMES-2))
     (15 15 (:REWRITE DEFAULT-TIMES-1))
     (15 14 (:REWRITE DEFAULT-PLUS-1))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE DEFAULT-PLUS-2))
     (14 3
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-MINUS))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::DIVIDES-LEQ
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (14 10 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE DEFAULT-DIVIDE))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::DIVIDES-MINUS (18 2 (:REWRITE ACL2-NUMBERP-X))
                    (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                    (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (17 17 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (8 2 (:REWRITE RATIONALP-X))
                    (5 5 (:REWRITE DEFAULT-TIMES-2))
                    (5 5 (:REWRITE DEFAULT-TIMES-1))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                    (3 3 (:REWRITE REDUCE-INTEGERP-+))
                    (3 3 (:REWRITE INTEGERP-MINUS-X))
                    (3 3 (:META META-INTEGERP-CORRECT))
                    (2 2 (:REWRITE REDUCE-RATIONALP-+))
                    (2 2 (:REWRITE REDUCE-RATIONALP-*))
                    (2 2 (:REWRITE RATIONALP-MINUS-X))
                    (2 2
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                    (2 2
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (2 2 (:REWRITE DEFAULT-MINUS))
                    (2 2 (:REWRITE DEFAULT-DIVIDE))
                    (2 2 (:META META-RATIONALP-CORRECT))
                    (1 1
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (1 1
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (1 1
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (1 1
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (1 1
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (1 1
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (1 1 (:REWRITE |(equal c (/ x))|))
                    (1 1 (:REWRITE |(equal c (- x))|))
                    (1 1 (:REWRITE |(equal (/ x) c)|))
                    (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                    (1 1 (:REWRITE |(equal (- x) c)|))
                    (1 1 (:REWRITE |(equal (- x) (- y))|))
                    (1 1 (:REWRITE |(- (* c x))|)))
(RTL::DIVIDES-SUM (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                  (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (27 3 (:REWRITE ACL2-NUMBERP-X))
                  (12 3 (:REWRITE RATIONALP-X))
                  (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                  (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (8 8 (:REWRITE DEFAULT-TIMES-2))
                  (8 8 (:REWRITE DEFAULT-TIMES-1))
                  (5 5 (:REWRITE REDUCE-INTEGERP-+))
                  (5 5
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (5 5 (:REWRITE INTEGERP-MINUS-X))
                  (5 5 (:META META-INTEGERP-CORRECT))
                  (3 3 (:REWRITE REDUCE-RATIONALP-+))
                  (3 3 (:REWRITE REDUCE-RATIONALP-*))
                  (3 3 (:REWRITE RATIONALP-MINUS-X))
                  (3 3
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                  (3 3 (:REWRITE DEFAULT-DIVIDE))
                  (3 3 (:META META-RATIONALP-CORRECT))
                  (2 2
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (2 2 (:REWRITE NORMALIZE-ADDENDS))
                  (2 2 (:REWRITE DEFAULT-PLUS-2))
                  (2 2 (:REWRITE DEFAULT-PLUS-1))
                  (1 1
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (1 1
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (1 1
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (1 1
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (1 1
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (1 1
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (1 1 (:REWRITE |(equal c (/ x))|))
                  (1 1 (:REWRITE |(equal c (- x))|))
                  (1 1 (:REWRITE |(equal (/ x) c)|))
                  (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                  (1 1 (:REWRITE |(equal (- x) c)|))
                  (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::DIVIDES-PRODUCT (36 4 (:REWRITE ACL2-NUMBERP-X))
                      (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                      (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                      (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                      (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                      (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                      (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                      (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                      (16 4 (:REWRITE RATIONALP-X))
                      (15 15 (:REWRITE REDUCE-INTEGERP-+))
                      (15 15 (:REWRITE INTEGERP-MINUS-X))
                      (15 11 (:REWRITE DEFAULT-TIMES-2))
                      (11 11 (:REWRITE DEFAULT-TIMES-1))
                      (7 7
                         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (4 4 (:REWRITE REDUCE-RATIONALP-+))
                      (4 4 (:REWRITE REDUCE-RATIONALP-*))
                      (4 4 (:REWRITE RATIONALP-MINUS-X))
                      (4 4
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                      (4 4 (:REWRITE DEFAULT-DIVIDE))
                      (4 4 (:META META-RATIONALP-CORRECT))
                      (4 1 (:REWRITE INTEGERP-/))
                      (3 3 (:TYPE-PRESCRIPTION FIX))
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
                      (1 1 (:REWRITE |(* c (* d x))|)))
(RTL::DIVIDES-TRANSITIVE
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (32 8 (:REWRITE RATIONALP-X))
     (25 21 (:REWRITE DEFAULT-TIMES-2))
     (21 21 (:REWRITE DEFAULT-TIMES-1))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (10 10
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 10 (:REWRITE DEFAULT-DIVIDE))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|)))
(RTL::DIVIDES-SELF (9 1 (:REWRITE ACL2-NUMBERP-X))
                   (4 1 (:REWRITE RATIONALP-X))
                   (1 1
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (1 1
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (1 1 (:REWRITE REDUCE-RATIONALP-+))
                   (1 1 (:REWRITE REDUCE-RATIONALP-*))
                   (1 1
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                   (1 1 (:REWRITE REDUCE-INTEGERP-+))
                   (1 1
                      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                   (1 1 (:REWRITE RATIONALP-MINUS-X))
                   (1 1
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (1 1
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                   (1 1 (:REWRITE INTEGERP-MINUS-X))
                   (1 1
                      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                   (1 1 (:REWRITE DEFAULT-TIMES-2))
                   (1 1 (:REWRITE DEFAULT-TIMES-1))
                   (1 1 (:REWRITE DEFAULT-DIVIDE))
                   (1 1 (:REWRITE |(equal c (/ x))|))
                   (1 1 (:REWRITE |(equal c (- x))|))
                   (1 1 (:REWRITE |(equal (/ x) c)|))
                   (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                   (1 1 (:REWRITE |(equal (- x) c)|))
                   (1 1 (:REWRITE |(equal (- x) (- y))|))
                   (1 1 (:META META-RATIONALP-CORRECT))
                   (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::DIVIDES-0 (9 1 (:REWRITE ACL2-NUMBERP-X))
                (4 1 (:REWRITE RATIONALP-X))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (1 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (1 1 (:REWRITE REDUCE-RATIONALP-+))
                (1 1 (:REWRITE REDUCE-RATIONALP-*))
                (1 1
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (1 1 (:REWRITE REDUCE-INTEGERP-+))
                (1 1
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (1 1 (:REWRITE RATIONALP-MINUS-X))
                (1 1
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (1 1
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (1 1 (:REWRITE INTEGERP-MINUS-X))
                (1 1
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (1 1 (:REWRITE DEFAULT-TIMES-2))
                (1 1 (:REWRITE DEFAULT-TIMES-1))
                (1 1 (:REWRITE DEFAULT-DIVIDE))
                (1 1 (:REWRITE |(equal c (/ x))|))
                (1 1 (:REWRITE |(equal c (- x))|))
                (1 1 (:REWRITE |(equal (/ x) c)|))
                (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                (1 1 (:REWRITE |(equal (- x) c)|))
                (1 1 (:REWRITE |(equal (- x) (- y))|))
                (1 1 (:META META-RATIONALP-CORRECT))
                (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::DIVIDES-MOD-EQUAL
     (1467 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (1385 1385
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1385 1385
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1385 1385
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (936 24 (:REWRITE CANCEL-MOD-+))
     (935 187 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (934 32
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (840 24 (:REWRITE MOD-X-Y-=-X . 4))
     (840 24 (:REWRITE MOD-X-Y-=-X . 3))
     (767 187 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (762 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (735 187
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (735 187
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (651 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (624 24 (:REWRITE RTL::MOD-DOES-NOTHING))
     (609 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (504 24 (:REWRITE MOD-ZERO . 3))
     (448 20 (:LINEAR MOD-BOUNDS-1))
     (432 27 (:REWRITE |(integerp (- x))|))
     (432 24 (:REWRITE MOD-ZERO . 4))
     (374 187 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (310 10 (:LINEAR RTL::MOD-BND-2))
     (263 32
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (245 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (245 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (240 24 (:REWRITE DEFAULT-MOD-RATIO))
     (240 24 (:REWRITE |(* (- x) y)|))
     (229 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (210 10 (:LINEAR MOD-BOUNDS-3))
     (187 187
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (187 187 (:TYPE-PRESCRIPTION NATP))
     (187 187 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (187 187 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (187 187
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (187 187
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (187 187 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (187 187 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (187 187
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (184 10 (:LINEAR RTL::MOD-BND-1))
     (164 77 (:REWRITE REDUCE-INTEGERP-+))
     (162 162 (:REWRITE THE-FLOOR-BELOW))
     (162 162 (:REWRITE THE-FLOOR-ABOVE))
     (162 162 (:REWRITE SIMPLIFY-SUMS-<))
     (162 162
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (162 162
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (162 162
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (162 162
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (162 162
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (162 162
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (162 162 (:REWRITE INTEGERP-<-CONSTANT))
     (162 162 (:REWRITE DEFAULT-LESS-THAN-2))
     (162 162 (:REWRITE DEFAULT-LESS-THAN-1))
     (162 162 (:REWRITE CONSTANT-<-INTEGERP))
     (162 162
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (162 162
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (162 162
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (162 162
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (162 162 (:REWRITE |(< c (- x))|))
     (162 162
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (162 162
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (162 162
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (162 162
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (162 162 (:REWRITE |(< (/ x) (/ y))|))
     (162 162 (:REWRITE |(< (- x) c)|))
     (162 162 (:REWRITE |(< (- x) (- y))|))
     (162 38 (:REWRITE DEFAULT-MINUS))
     (150 150 (:REWRITE DEFAULT-TIMES-2))
     (150 150 (:REWRITE DEFAULT-TIMES-1))
     (120 24 (:REWRITE MOD-X-Y-=-X . 2))
     (120 24
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (120 24 (:REWRITE MOD-CANCEL-*-CONST))
     (120 24
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (120 24 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (120 24
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (120 24
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (102 102
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (93 77 (:REWRITE INTEGERP-MINUS-X))
     (90 90
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (90 90 (:REWRITE DEFAULT-DIVIDE))
     (82 21 (:REWRITE DEFAULT-PLUS-2))
     (77 77 (:META META-INTEGERP-CORRECT))
     (74 74 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (68 68 (:REWRITE |(< 0 (/ x))|))
     (68 68 (:REWRITE |(< 0 (* x y))|))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (56 56 (:REWRITE |(< (/ x) 0)|))
     (56 56 (:REWRITE |(< (* x y) 0)|))
     (50 21 (:REWRITE DEFAULT-PLUS-1))
     (42 42
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (36 9 (:REWRITE RATIONALP-X))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (32 32 (:REWRITE |(equal c (/ x))|))
     (32 32 (:REWRITE |(equal c (- x))|))
     (32 32 (:REWRITE |(equal (/ x) c)|))
     (32 32 (:REWRITE |(equal (/ x) (/ y))|))
     (32 32 (:REWRITE |(equal (- x) c)|))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (31 31 (:REWRITE |(- (* c x))|))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (24 24
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (24 24 (:REWRITE DEFAULT-MOD-2))
     (24 24 (:REWRITE DEFAULT-MOD-1))
     (24 24 (:REWRITE |(mod x (- y))| . 3))
     (24 24 (:REWRITE |(mod x (- y))| . 2))
     (24 24 (:REWRITE |(mod x (- y))| . 1))
     (24 24
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (24 24 (:REWRITE |(mod (- x) y)| . 3))
     (24 24 (:REWRITE |(mod (- x) y)| . 2))
     (24 24 (:REWRITE |(mod (- x) y)| . 1))
     (24 24
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (23 17 (:REWRITE NORMALIZE-ADDENDS))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 1 (:REWRITE |(+ y (+ x z))|))
     (10 10 (:LINEAR RTL::MOD-BND-3))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (4 1 (:REWRITE |(+ y x)|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:DEFINITION FIX))
     (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE |(+ x (- x))|))
     (1 1 (:REWRITE |(+ 0 x)|)))
(RTL::DIVIDES-MOD-0
     (305 37 (:REWRITE REDUCE-RATIONALP-*))
     (270 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (270 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (270 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (270 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (236 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (220 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (174 30
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (151 43 (:REWRITE RATIONALP-X))
     (148 16 (:DEFINITION RFIX))
     (136 136
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (136 136
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (136 136
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (136 136
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (124 4 (:REWRITE MOD-X-Y-=-X . 4))
     (124 4 (:REWRITE MOD-X-Y-=-X . 3))
     (104 4 (:REWRITE RTL::MOD-DOES-NOTHING))
     (102 56 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (100 60
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (100 60
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (76 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (74 9 (:REWRITE MOD-ZERO . 4))
     (64 4 (:REWRITE |(+ y (+ x z))|))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (60 60
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (60 60
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (56 56 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (56 56 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (56 56 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (56 56 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (56 56 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (56 56
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (56 8 (:REWRITE ACL2-NUMBERP-X))
     (54 6 (:REWRITE RATIONALP-/))
     (48 48 (:REWRITE THE-FLOOR-BELOW))
     (48 48 (:REWRITE THE-FLOOR-ABOVE))
     (48 48 (:REWRITE SIMPLIFY-SUMS-<))
     (48 48
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (48 48
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (48 48
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (48 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (48 48 (:REWRITE INTEGERP-<-CONSTANT))
     (48 48 (:REWRITE DEFAULT-LESS-THAN-2))
     (48 48 (:REWRITE DEFAULT-LESS-THAN-1))
     (48 48 (:REWRITE CONSTANT-<-INTEGERP))
     (48 48
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (48 48
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (48 48
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (48 48
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (48 48 (:REWRITE |(< c (- x))|))
     (48 48
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (48 48 (:REWRITE |(< (/ x) (/ y))|))
     (48 48 (:REWRITE |(< (- x) c)|))
     (48 48 (:REWRITE |(< (- x) (- y))|))
     (46 46
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (46 46 (:TYPE-PRESCRIPTION NATP))
     (44 4 (:REWRITE CANCEL-MOD-+))
     (42 38 (:REWRITE DEFAULT-PLUS-1))
     (38 38 (:REWRITE REDUCE-INTEGERP-+))
     (38 38 (:REWRITE INTEGERP-MINUS-X))
     (38 38 (:REWRITE DEFAULT-PLUS-2))
     (38 38 (:META META-INTEGERP-CORRECT))
     (37 37 (:REWRITE REDUCE-RATIONALP-+))
     (37 37 (:REWRITE RATIONALP-MINUS-X))
     (37 37 (:META META-RATIONALP-CORRECT))
     (36 12 (:REWRITE NORMALIZE-ADDENDS))
     (30 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (30 30
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (30 30
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (30 30
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (30 30 (:REWRITE DEFAULT-TIMES-2))
     (30 30 (:REWRITE DEFAULT-TIMES-1))
     (30 30 (:REWRITE |(equal c (/ x))|))
     (30 30 (:REWRITE |(equal c (- x))|))
     (30 30 (:REWRITE |(equal (/ x) c)|))
     (30 30 (:REWRITE |(equal (/ x) (/ y))|))
     (30 30 (:REWRITE |(equal (- x) c)|))
     (30 30 (:REWRITE |(equal (- x) (- y))|))
     (26 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (26 26
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (26 26 (:REWRITE DEFAULT-DIVIDE))
     (24 4 (:REWRITE |(* (- x) y)|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (22 22 (:REWRITE |(< 0 (* x y))|))
     (22 22 (:REWRITE |(< (/ x) 0)|))
     (22 22 (:REWRITE |(< (* x y) 0)|))
     (13 13 (:REWRITE DEFAULT-MOD-2))
     (13 13 (:REWRITE DEFAULT-MOD-1))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
     (8 8 (:DEFINITION FIX))
     (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (6 6 (:REWRITE INTEGERP-/))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4 (:REWRITE MOD-ZERO . 2))
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
     (4 4 (:REWRITE |(- (* c x))|))
     (4 4 (:REWRITE |(+ x (- x))|)))
(RTL::LEAST-DIVISOR
     (54 54 (:REWRITE DEFAULT-PLUS-2))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
     (17 17
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (17 17 (:REWRITE |(< (- x) (- y))|))
     (16 4 (:REWRITE RATIONALP-X))
     (15 15
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (15 15 (:REWRITE INTEGERP-<-CONSTANT))
     (15 15 (:REWRITE CONSTANT-<-INTEGERP))
     (14 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(RTL::LEAST-DIVISOR-DIVIDES
     (92 92 (:REWRITE THE-FLOOR-BELOW))
     (92 92 (:REWRITE THE-FLOOR-ABOVE))
     (92 92 (:REWRITE DEFAULT-LESS-THAN-2))
     (91 91
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (91 91
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (91 91
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (86 86
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (86 86 (:REWRITE INTEGERP-<-CONSTANT))
     (86 86 (:REWRITE CONSTANT-<-INTEGERP))
     (86 86
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (86 86
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (86 86
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (86 86
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (86 86 (:REWRITE |(< c (- x))|))
     (86 86
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (86 86
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (86 86
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (86 86
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (86 86 (:REWRITE |(< (/ x) (/ y))|))
     (86 86 (:REWRITE |(< (- x) c)|))
     (86 86 (:REWRITE |(< (- x) (- y))|))
     (60 4 (:REWRITE ACL2-NUMBERP-X))
     (57 57 (:REWRITE SIMPLIFY-SUMS-<))
     (57 57 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:META META-INTEGERP-CORRECT))
     (28 4 (:REWRITE RATIONALP-X))
     (20 20 (:REWRITE DEFAULT-TIMES-2))
     (20 20 (:REWRITE DEFAULT-TIMES-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE NORMALIZE-ADDENDS))
     (15 15 (:REWRITE DEFAULT-PLUS-2))
     (15 15 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (5 5
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (5 5
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (5 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(RTL::LEAST-DIVISOR-IS-LEAST
     (75 5 (:REWRITE ACL2-NUMBERP-X))
     (54 54 (:REWRITE THE-FLOOR-BELOW))
     (54 54 (:REWRITE THE-FLOOR-ABOVE))
     (52 52
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (52 52
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (52 52
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (52 52 (:REWRITE DEFAULT-LESS-THAN-1))
     (51 51
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (51 51 (:REWRITE INTEGERP-<-CONSTANT))
     (51 51 (:REWRITE CONSTANT-<-INTEGERP))
     (51 51
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (51 51
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (51 51
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (51 51
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (51 51 (:REWRITE |(< c (- x))|))
     (51 51
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (51 51
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (51 51
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (51 51
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (51 51 (:REWRITE |(< (/ x) (/ y))|))
     (51 51 (:REWRITE |(< (- x) c)|))
     (51 51 (:REWRITE |(< (- x) (- y))|))
     (38 38 (:REWRITE SIMPLIFY-SUMS-<))
     (38 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (35 5 (:REWRITE RATIONALP-X))
     (25 25 (:REWRITE REDUCE-INTEGERP-+))
     (25 25 (:REWRITE INTEGERP-MINUS-X))
     (25 25 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-2))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE DEFAULT-TIMES-2))
     (4 4 (:REWRITE DEFAULT-TIMES-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::PRIMEP)
(RTL::PRIMEP-GT-1)
(RTL::PRIMEP-NO-DIVISOR
     (20 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (17 3 (:REWRITE ACL2-NUMBERP-X))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 1 (:REWRITE RATIONALP-X))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::PRIMEP-LEAST-DIVISOR
     (858 33 (:DEFINITION RTL::LEAST-DIVISOR))
     (44 44 (:REWRITE THE-FLOOR-BELOW))
     (44 44 (:REWRITE THE-FLOOR-ABOVE))
     (44 44
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (44 44
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (44 44 (:REWRITE INTEGERP-<-CONSTANT))
     (44 44 (:REWRITE DEFAULT-LESS-THAN-2))
     (44 44 (:REWRITE DEFAULT-LESS-THAN-1))
     (44 44 (:REWRITE CONSTANT-<-INTEGERP))
     (44 44
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (44 44
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< c (- x))|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< (/ x) (/ y))|))
     (44 44 (:REWRITE |(< (- x) c)|))
     (44 44 (:REWRITE |(< (- x) (- y))|))
     (20 20 (:REWRITE SIMPLIFY-SUMS-<))
     (20 20
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (20 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::FACT)
(RTL::GREATER-PRIME)
(RTL::GREATER-PRIME-DIVIDES)
(RTL::DIVIDES-FACT
     (102 3 (:REWRITE ZP-OPEN))
     (54 3 (:REWRITE |(* (+ x y) z)|))
     (37 21 (:REWRITE DEFAULT-TIMES-2))
     (30 25 (:REWRITE DEFAULT-PLUS-1))
     (28 25 (:REWRITE DEFAULT-PLUS-2))
     (22 21 (:REWRITE DEFAULT-TIMES-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 3 (:REWRITE |(+ c (+ d x))|))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (12 12 (:REWRITE INTEGERP-<-CONSTANT))
     (12 12 (:REWRITE CONSTANT-<-INTEGERP))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (12 12 (:REWRITE |(< c (- x))|))
     (12 12
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (12 12 (:REWRITE |(< (/ x) (/ y))|))
     (12 12 (:REWRITE |(< (- x) c)|))
     (12 12 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 3 (:REWRITE |(* -1 x)|))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 3 (:REWRITE DEFAULT-MINUS))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(* (- x) y)|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(RTL::NOT-DIVIDES-FACT-PLUS1
     (63 7 (:DEFINITION RTL::FACT))
     (19 13 (:REWRITE DEFAULT-PLUS-2))
     (18 13 (:REWRITE DEFAULT-PLUS-1))
     (17 9 (:REWRITE DEFAULT-TIMES-2))
     (10 9 (:REWRITE DEFAULT-TIMES-1))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 3 (:REWRITE DEFAULT-MINUS))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::INFINITUDE-OF-PRIMES
     (110 11 (:DEFINITION RTL::FACT))
     (33 22 (:REWRITE DEFAULT-PLUS-2))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE NORMALIZE-ADDENDS))
     (22 22 (:REWRITE DEFAULT-PLUS-1))
     (22 11 (:REWRITE DEFAULT-TIMES-2))
     (18 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (17 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 11 (:REWRITE ZP-OPEN))
     (11 11
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 11 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT)))
(RTL::G-C-D-NAT
     (103 3 (:REWRITE |(< (if a b c) x)|))
     (45 5 (:REWRITE ACL2-NUMBERP-X))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (23 23
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (22 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (20 5 (:REWRITE RATIONALP-X))
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE ZP-OPEN))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE DEFAULT-MINUS))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(RTL::G-C-D
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::G-C-D-NAT-POS
     (55 46 (:REWRITE DEFAULT-LESS-THAN-2))
     (50 41
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (46 46 (:REWRITE THE-FLOOR-BELOW))
     (46 46 (:REWRITE THE-FLOOR-ABOVE))
     (46 46
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (46 46
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (46 46
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (46 46
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (46 46 (:REWRITE INTEGERP-<-CONSTANT))
     (46 46 (:REWRITE DEFAULT-LESS-THAN-1))
     (46 46 (:REWRITE CONSTANT-<-INTEGERP))
     (46 46
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (46 46
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (46 46
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (46 46
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (46 46 (:REWRITE |(< c (- x))|))
     (46 46
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (46 46
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (46 46
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (46 46
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (46 46 (:REWRITE |(< (/ x) (/ y))|))
     (46 46 (:REWRITE |(< (- x) c)|))
     (46 46 (:REWRITE |(< (- x) (- y))|))
     (44 41 (:REWRITE DEFAULT-PLUS-1))
     (41 41 (:REWRITE DEFAULT-PLUS-2))
     (39 39 (:REWRITE SIMPLIFY-SUMS-<))
     (20 20 (:REWRITE |(< (/ x) 0)|))
     (20 20 (:REWRITE |(< (* x y) 0)|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (15 15 (:REWRITE REDUCE-INTEGERP-+))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE INTEGERP-MINUS-X))
     (15 15 (:REWRITE DEFAULT-MINUS))
     (15 15 (:META META-INTEGERP-CORRECT))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (13 13 (:REWRITE |(< 0 (/ x))|))
     (13 13 (:REWRITE |(< 0 (* x y))|))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE ZP-OPEN))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(RTL::G-C-D-POS
     (1099 17 (:DEFINITION RTL::G-C-D-NAT))
     (285 4 (:REWRITE |(< x (if a b c))|))
     (223 78 (:REWRITE |(< (- x) (- y))|))
     (186 10 (:REWRITE ZP-OPEN))
     (135 73 (:REWRITE |(< c (- x))|))
     (128 1 (:REWRITE |(< (if a b c) x)|))
     (100 20 (:REWRITE |(+ y x)|))
     (84 83 (:REWRITE DEFAULT-LESS-THAN-2))
     (83 83 (:REWRITE THE-FLOOR-BELOW))
     (83 83 (:REWRITE THE-FLOOR-ABOVE))
     (83 83 (:REWRITE DEFAULT-LESS-THAN-1))
     (78 78
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (78 78
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (78 78
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (78 78 (:REWRITE |(< (/ x) (/ y))|))
     (73 73
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (73 73
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (73 73
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (73 73
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (73 73
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (73 73
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (73 73
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (73 73
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (72 72 (:REWRITE DEFAULT-MINUS))
     (72 71
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (72 71 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (71 71 (:REWRITE SIMPLIFY-SUMS-<))
     (71 71 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (71 71
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (71 71 (:REWRITE INTEGERP-<-CONSTANT))
     (71 71 (:REWRITE CONSTANT-<-INTEGERP))
     (71 71 (:REWRITE |(< (- x) c)|))
     (66 66 (:REWRITE DEFAULT-PLUS-2))
     (66 66 (:REWRITE DEFAULT-PLUS-1))
     (58 2 (:REWRITE |(+ x (if a b c))|))
     (48 4 (:REWRITE |(+ (if a b c) x)|))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (40 40
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (40 40 (:REWRITE NORMALIZE-ADDENDS))
     (40 40 (:REWRITE |(< (/ x) 0)|))
     (40 40 (:REWRITE |(< (* x y) 0)|))
     (30 30 (:REWRITE |(- (- x))|))
     (13 13 (:REWRITE |(< 0 (/ x))|))
     (13 13 (:REWRITE |(< 0 (* x y))|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 2 (:REWRITE |(- (if a b c))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|)))
(RTL::DIVIDES-G-C-D-NAT
     (141 120 (:REWRITE DEFAULT-PLUS-1))
     (120 120 (:REWRITE DEFAULT-PLUS-2))
     (64 64 (:REWRITE THE-FLOOR-BELOW))
     (64 64 (:REWRITE THE-FLOOR-ABOVE))
     (64 64
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (64 64
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (64 64
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (64 64 (:REWRITE DEFAULT-LESS-THAN-2))
     (64 64 (:REWRITE DEFAULT-LESS-THAN-1))
     (56 56
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (56 56 (:REWRITE INTEGERP-<-CONSTANT))
     (56 56 (:REWRITE CONSTANT-<-INTEGERP))
     (56 56
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (56 56
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (56 56
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (56 56
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (56 56 (:REWRITE |(< c (- x))|))
     (56 56
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (56 56
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (56 56
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (56 56
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (56 56 (:REWRITE |(< (/ x) (/ y))|))
     (56 56 (:REWRITE |(< (- x) c)|))
     (56 56 (:REWRITE |(< (- x) (- y))|))
     (32 32 (:REWRITE DEFAULT-TIMES-2))
     (32 32 (:REWRITE DEFAULT-TIMES-1))
     (28 28 (:REWRITE DEFAULT-MINUS))
     (26 26 (:REWRITE SIMPLIFY-SUMS-<))
     (26 26 (:REWRITE |(< (/ x) 0)|))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (21 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (8 8
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (8 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:TYPE-PRESCRIPTION RTL::G-C-D-NAT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::G-C-D-DIVIDES
     (570 8 (:REWRITE |(< x (if a b c))|))
     (386 154 (:REWRITE |(< (- x) (- y))|))
     (376 24 (:REWRITE ZP-OPEN))
     (270 146 (:REWRITE |(< c (- x))|))
     (256 2 (:REWRITE |(< (if a b c) x)|))
     (164 164 (:REWRITE THE-FLOOR-BELOW))
     (164 164 (:REWRITE THE-FLOOR-ABOVE))
     (164 164 (:REWRITE DEFAULT-LESS-THAN-2))
     (164 164 (:REWRITE DEFAULT-LESS-THAN-1))
     (160 32 (:REWRITE |(+ y x)|))
     (154 154
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (154 154
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (154 154
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (154 154 (:REWRITE DEFAULT-MINUS))
     (154 154 (:REWRITE |(< (/ x) (/ y))|))
     (146 146
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (146 146
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (146 146
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (146 146
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (146 146
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (146 146
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (146 146
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (146 146
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (142 142 (:REWRITE SIMPLIFY-SUMS-<))
     (142 142
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (142 142 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (142 142
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (142 142
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (142 142 (:REWRITE INTEGERP-<-CONSTANT))
     (142 142 (:REWRITE CONSTANT-<-INTEGERP))
     (142 142 (:REWRITE |(< (- x) c)|))
     (116 4 (:REWRITE |(+ x (if a b c))|))
     (108 108 (:REWRITE DEFAULT-PLUS-2))
     (108 108 (:REWRITE DEFAULT-PLUS-1))
     (106 106
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (106 106
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (106 106 (:REWRITE |(< (/ x) 0)|))
     (106 106 (:REWRITE |(< (* x y) 0)|))
     (96 8 (:REWRITE |(+ (if a b c) x)|))
     (64 64
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (64 64 (:REWRITE NORMALIZE-ADDENDS))
     (30 30 (:REWRITE DEFAULT-TIMES-2))
     (30 30 (:REWRITE DEFAULT-TIMES-1))
     (16 4 (:REWRITE |(- (if a b c))|))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:REWRITE |(* x (- y))|))
     (12 12 (:META META-INTEGERP-CORRECT))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(RTL::R-NAT
     (103 3 (:REWRITE |(< (if a b c) x)|))
     (45 5 (:REWRITE ACL2-NUMBERP-X))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (23 23
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (22 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (20 5 (:REWRITE RATIONALP-X))
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE ZP-OPEN))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE DEFAULT-MINUS))
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-S-NAT
     (1575 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1197 37 (:REWRITE ZP-OPEN))
     (732 561 (:REWRITE DEFAULT-PLUS-1))
     (662 561 (:REWRITE DEFAULT-PLUS-2))
     (412 58 (:REWRITE |(+ x x)|))
     (233 40 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (215 187 (:REWRITE DEFAULT-MINUS))
     (184 23 (:REWRITE |(- (+ x y))|))
     (177 177
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (168 135 (:REWRITE DEFAULT-TIMES-2))
     (137 135 (:REWRITE DEFAULT-TIMES-1))
     (105 105
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (104 24 (:REWRITE |(- (* c x))|))
     (96 92 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (93 93 (:REWRITE THE-FLOOR-BELOW))
     (93 93 (:REWRITE THE-FLOOR-ABOVE))
     (93 93
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (93 93
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (93 93
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (93 93
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (93 93 (:REWRITE INTEGERP-<-CONSTANT))
     (93 93 (:REWRITE DEFAULT-LESS-THAN-2))
     (93 93 (:REWRITE DEFAULT-LESS-THAN-1))
     (93 93 (:REWRITE CONSTANT-<-INTEGERP))
     (93 93
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (93 93
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (93 93
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (93 93
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (93 93 (:REWRITE |(< c (- x))|))
     (93 93
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (93 93
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (93 93
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (93 93
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (93 93 (:REWRITE |(< (/ x) (/ y))|))
     (93 93 (:REWRITE |(< (- x) c)|))
     (93 93 (:REWRITE |(< (- x) (- y))|))
     (85 85
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (56 56 (:REWRITE |(+ c (+ d x))|))
     (55 55 (:REWRITE SIMPLIFY-SUMS-<))
     (51 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (31 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (23 23 (:REWRITE |(- (- x))|))
     (20 20 (:REWRITE |(< y (+ (- c) x))|))
     (20 20 (:REWRITE |(< x (+ c/d y))|))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (15 11 (:REWRITE |(equal (- x) (- y))|))
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (11 11
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (11 11 (:REWRITE |(equal c (/ x))|))
     (11 11 (:REWRITE |(equal c (- x))|))
     (11 11 (:REWRITE |(equal (/ x) c)|))
     (11 11 (:REWRITE |(equal (/ x) (/ y))|))
     (11 11 (:REWRITE |(equal (- x) c)|))
     (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (10 10 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::R-INT
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::S-INT
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::G-C-D-LINEAR-COMBINATION
     (855 12 (:REWRITE |(< x (if a b c))|))
     (681 5 (:DEFINITION RTL::S-NAT))
     (680 5 (:DEFINITION RTL::R-NAT))
     (564 5 (:DEFINITION RTL::G-C-D-NAT))
     (546 18 (:REWRITE ZP-OPEN))
     (384 3 (:REWRITE |(< (if a b c) x)|))
     (277 192 (:REWRITE DEFAULT-PLUS-2))
     (270 84 (:REWRITE |(< c (- x))|))
     (269 192 (:REWRITE DEFAULT-PLUS-1))
     (264 90 (:REWRITE |(< (- x) (- y))|))
     (136 116 (:REWRITE DEFAULT-MINUS))
     (105 105 (:REWRITE THE-FLOOR-BELOW))
     (105 105 (:REWRITE THE-FLOOR-ABOVE))
     (105 105 (:REWRITE DEFAULT-LESS-THAN-2))
     (105 105 (:REWRITE DEFAULT-LESS-THAN-1))
     (92 92
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (90 90
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (90 90
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (90 90
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (90 90 (:REWRITE |(< (/ x) (/ y))|))
     (84 84
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (84 84
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (84 84
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (84 84
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (84 84
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (84 84
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (84 84
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (84 84
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (78 78 (:REWRITE SIMPLIFY-SUMS-<))
     (78 78
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (78 78 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (78 78
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (78 78 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (78 78 (:REWRITE INTEGERP-<-CONSTANT))
     (78 78 (:REWRITE CONSTANT-<-INTEGERP))
     (78 78 (:REWRITE |(< (- x) c)|))
     (52 32 (:REWRITE DEFAULT-TIMES-1))
     (48 48
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (48 48
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (48 48 (:REWRITE |(< (/ x) 0)|))
     (48 48 (:REWRITE |(< (* x y) 0)|))
     (48 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (44 32 (:REWRITE DEFAULT-TIMES-2))
     (42 42 (:REWRITE |(- (- x))|))
     (32 8 (:REWRITE |(- (if a b c))|))
     (22 12 (:REWRITE |(equal (- x) (- y))|))
     (16 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (13 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(- (* c x))|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::DIVIDES-G-C-D (21 1
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (18 12 (:REWRITE DEFAULT-TIMES-2))
                    (18 12 (:REWRITE DEFAULT-TIMES-1))
                    (17 3 (:REWRITE ACL2-NUMBERP-X))
                    (7 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (7 1 (:REWRITE RATIONALP-X))
                    (7 1
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (6 6
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (4 2 (:REWRITE DEFAULT-PLUS-2))
                    (4 2 (:REWRITE DEFAULT-PLUS-1))
                    (2 2
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (2 2 (:REWRITE NORMALIZE-ADDENDS))
                    (1 1 (:REWRITE REDUCE-RATIONALP-+))
                    (1 1 (:REWRITE REDUCE-RATIONALP-*))
                    (1 1
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (1 1 (:REWRITE REDUCE-INTEGERP-+))
                    (1 1
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (1 1 (:REWRITE RATIONALP-MINUS-X))
                    (1 1 (:REWRITE INTEGERP-MINUS-X))
                    (1 1
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (1 1 (:REWRITE |(equal c (/ x))|))
                    (1 1 (:REWRITE |(equal c (- x))|))
                    (1 1 (:REWRITE |(equal (/ x) c)|))
                    (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                    (1 1 (:REWRITE |(equal (- x) c)|))
                    (1 1 (:REWRITE |(equal (- x) (- y))|))
                    (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
                    (1 1 (:META META-RATIONALP-CORRECT))
                    (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::G-C-D-PRIME
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
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
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::HACK (45 20 (:REWRITE DEFAULT-TIMES-2))
           (20 20 (:REWRITE DEFAULT-TIMES-1))
           (11 6 (:REWRITE DEFAULT-PLUS-2))
           (11 6 (:REWRITE DEFAULT-PLUS-1))
           (10 10
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (7 7
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
           (7 7
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
           (7 7 (:REWRITE |(equal c (/ x))|))
           (7 7 (:REWRITE |(equal (/ x) (/ y))|))
           (7 7 (:REWRITE |(equal (- x) (- y))|))
           (7 5
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
           (6 6
              (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
           (6 6 (:REWRITE |(equal c (- x))|))
           (6 6 (:REWRITE |(equal (- x) c)|))
           (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
           (4 4
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
           (4 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
           (3 3
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (3 3 (:REWRITE NORMALIZE-ADDENDS))
           (3 3 (:REWRITE |(* c (* d x))|))
           (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
           (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
           (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
           (2 2 (:REWRITE REDUCE-INTEGERP-+))
           (2 2 (:REWRITE INTEGERP-MINUS-X))
           (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
           (2 2 (:META META-INTEGERP-CORRECT))
           (1 1 (:REWRITE DEFAULT-DIVIDE))
           (1 1 (:REWRITE |(not (equal x (/ y)))|))
           (1 1 (:REWRITE |(equal x (/ y))|)))
(RTL::EUCLID (51 34 (:REWRITE DEFAULT-TIMES-2))
             (44 34 (:REWRITE DEFAULT-TIMES-1))
             (22 2
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (21 21
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (16 2 (:REWRITE ACL2-NUMBERP-X))
             (8 2
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (7 1 (:REWRITE RATIONALP-X))
             (6 6 (:REWRITE |(* c (* d x))|))
             (6 3 (:REWRITE DEFAULT-PLUS-2))
             (6 3 (:REWRITE DEFAULT-PLUS-1))
             (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (2 2
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (2 2
                (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (2 2
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (2 2 (:REWRITE |(equal c (/ x))|))
             (2 2 (:REWRITE |(equal c (- x))|))
             (2 2 (:REWRITE |(equal (/ x) c)|))
             (2 2 (:REWRITE |(equal (/ x) (/ y))|))
             (2 2 (:REWRITE |(equal (- x) c)|))
             (2 2 (:REWRITE |(equal (- x) (- y))|))
             (1 1 (:REWRITE REDUCE-RATIONALP-+))
             (1 1 (:REWRITE REDUCE-RATIONALP-*))
             (1 1 (:REWRITE REDUCE-INTEGERP-+))
             (1 1 (:REWRITE RATIONALP-MINUS-X))
             (1 1
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (1 1 (:REWRITE NORMALIZE-ADDENDS))
             (1 1 (:REWRITE INTEGERP-MINUS-X))
             (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
             (1 1 (:META META-RATIONALP-CORRECT))
             (1 1 (:META META-INTEGERP-CORRECT)))