(SET-MEMBER-EQUAL)
(SET-SUBSET-EQUAL)
(SET-EQUIV-EQUAL)
(SET-INSERT-EQUAL)
(SET-DELETE-EQUAL)
(SET-UNION-EQUAL (6 6
                    (:TYPE-PRESCRIPTION SET-INSERT-EQUAL)))
(SET-MEMBER-CAR-EQUAL (6 6 (:REWRITE DEFAULT-CAR))
                      (5 5 (:REWRITE DEFAULT-CDR)))
(SET-MEMBER-CONS-EQUAL)
(CONS-SET-SUBSET-EQUAL (15 5 (:DEFINITION SET-MEMBER-EQUAL))
                       (10 10 (:REWRITE DEFAULT-CDR))
                       (10 10 (:REWRITE DEFAULT-CAR)))
(SET-SUBSET-REFLEXIVE-EQUAL)
(SET-SUBSET-MEMBER-EQUAL)
(SET-SUBSET-TRANSITIVE-EQUAL)
(EQUIVALENCE-SET-EQUIV-EQUAL (40 4 (:DEFINITION SET-SUBSET-EQUAL))
                             (16 4 (:DEFINITION SET-MEMBER-EQUAL))
                             (8 8
                                (:REWRITE SET-SUBSET-TRANSITIVE-EQUAL))
                             (8 8 (:REWRITE SET-SUBSET-MEMBER-EQUAL))
                             (8 8 (:REWRITE DEFAULT-CDR))
                             (8 8 (:REWRITE DEFAULT-CAR))
                             (4 4
                                (:TYPE-PRESCRIPTION SET-MEMBER-EQUAL)))
(SET-MEMBER-CONGRUENCE-2-EQUAL)
(CONSP-SET-CONGRUENCE-1-EQUAL)
(SET-SUBSET-CONGRUENCE-1-EQUAL)
(SET-SUBSET-CONGRUENCE-2-EQUAL)
(SET-INSERT-CONGRUENCE-2-EQUAL (17 17
                                   (:TYPE-PRESCRIPTION SET-INSERT-EQUAL))
                               (8 2 (:DEFINITION SET-MEMBER-EQUAL))
                               (4 4 (:REWRITE SET-SUBSET-MEMBER-EQUAL))
                               (2 2 (:REWRITE DEFAULT-CDR))
                               (2 2 (:REWRITE DEFAULT-CAR)))
(SET-INSERT-CONS-EQUAL (11 11
                           (:TYPE-PRESCRIPTION SET-INSERT-EQUAL))
                       (4 1 (:DEFINITION SET-MEMBER-EQUAL))
                       (2 2 (:REWRITE SET-SUBSET-MEMBER-EQUAL))
                       (1 1 (:REWRITE DEFAULT-CDR))
                       (1 1 (:REWRITE DEFAULT-CAR)))
(SET-MEMBER-DELETE-1-EQUAL (14 14 (:REWRITE DEFAULT-CDR))
                           (14 14 (:REWRITE DEFAULT-CAR)))
(SET-SUBSET-DELETE-SUBSET-EQUAL)
(SET-DELETE-CONGRUENCE-2-EQUAL)
(SET-UNION-MEMBER1-EQUAL (31 31 (:REWRITE DEFAULT-CAR))
                         (29 29 (:REWRITE DEFAULT-CDR))
                         (2 2 (:REWRITE CDR-CONS))
                         (2 2 (:REWRITE CAR-CONS))
                         (1 1
                            (:REWRITE SET-SUBSET-TRANSITIVE-EQUAL)))
(SET-UNION-MEMBER2-EQUAL)
(SET-UNION-SUBSET1-1-EQUAL)
(SET-UNION-SUBSET1-2-EQUAL)
(SET-UNION-SUBSET2-EQUAL)
(SET-UNION-CONGRUENCE-1-EQUAL)
(SET-UNION-CONGRUENCE-2-EQUAL)
(SET-UNION-COMMUTATIVE-EQUAL)
(SET-UNION-MEMBER3-EQUAL)
(SET-DELETE-LEN-EQUAL)