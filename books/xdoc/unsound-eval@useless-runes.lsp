(UNSOUND-EVAL-FN)
(STATE-P1-OF-UNSOUND-EVAL.STATE
     (12 4
         (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
     (8 2 (:DEFINITION STATE-P))
     (4 4 (:TYPE-PRESCRIPTION STATE-P)))
(UNSOUND-EVAL-ELIDE (25 13 (:REWRITE DEFAULT-+-2))
                    (14 14 (:REWRITE DEFAULT-CDR))
                    (13 13 (:REWRITE DEFAULT-+-1)))