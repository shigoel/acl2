;; Original Authors: Shilpi Goel      <shigoel@gmail.com>
;;                   Mayank Manjrekar <mankmonjre@gmail.com>

(in-package "IRV")

(include-book "irv")
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ----------------------------------------------------------------------

;; Condorcet Loser Criterion:
;; An easy-to-understand definition from Wikipedia:
;; (https://en.m.wikipedia.org/wiki/Instant-runoff_voting#Satisfied_Criteria)

;;    The Condorcet loser criterion states that "if a candidate would
;;    lose a head-to-head competition against every other candidate,
;;    then that candidate must not win the overall election".

;; Note that a head-to-head competition is a pairwise showdown ---
;; i.e., making a candidate compete with every other candidate,
;; pretending as though all other candidates don't exist.

;; ----------------------------------------------------------------------

;; Let xs be the original ballot, where c1 is a candidate.  Let
;; xs-pairwise be the modified xs that has been obtained by eliminating
;; all candidates but two --- c1 and say, some other candidate c2. If
;; IRV(xs-pairwise) != c1 for every such xs-pairwise, then IRV(xs) != c1.

(define eliminate-other-candidates-aux ((cids nat-listp)
                                        (all-cids nat-listp)
                                        (xs   irv-ballot-p))

  :returns (new-xs irv-ballot-p :hyp (irv-ballot-p xs))

  (if (endp all-cids)
      xs
    (if (member-equal (car all-cids) cids)
        (eliminate-other-candidates-aux cids (cdr all-cids) xs)
      (b* ((new-xs (eliminate-candidate (car all-cids) xs)))
        (eliminate-other-candidates-aux cids (cdr all-cids) new-xs))))

  ///

  ;; (eliminate-other-candidates-aux '(1) '(4) '((1 2 3) (3 1 2 4)))
  ;; = ((1 2 3) (3 1 2))
  (defthm cids-is-a-subset-of-candidate-ids-of-eliminate-other-candidates-aux
    (implies (subsetp-equal cids (candidate-ids xs))
             (subsetp-equal
              cids
              (candidate-ids (eliminate-other-candidates-aux cids all-cids xs))))
    :hints (("Goal" :in-theory (e/d (subsetp-equal)
                                    ())))))

(define eliminate-other-candidates ((cids nat-listp "Candidates to preserve in @('xs')")
                                    (xs irv-ballot-p))

  :short "Remove all candidates from @('xs') except for those in
  @('cids')"

  :returns (new-xs irv-ballot-p :hyp (irv-ballot-p xs))

  (eliminate-other-candidates-aux cids (candidate-ids xs) xs)

  ///

  (defthm cids-is-a-subset-of-candidate-ids-of-eliminate-other-candidates-1
    (implies (subsetp-equal cids (candidate-ids xs))
             (subsetp-equal
              cids
              (candidate-ids (eliminate-other-candidates cids xs))))
    :hints (("Goal" :in-theory (e/d (subsetp-equal)
                                    ()))))


  ;; (local
  ;;  (defthm cids-is-a-subset-of-candidate-ids-of-eliminate-other-candidates-2
  ;;    (implies (subsetp-equal cids (candidate-ids xs))
  ;;             (subsetp-equal
  ;;              (candidate-ids (eliminate-other-candidates cids xs))
  ;;              cids))
  ;;    :hints (("Goal" :in-theory (e/d (subsetp-equal)
  ;;                                    ())))))
  )

;; ----------------------------------------------------------------------

;; (defun-sk forall-c2-condorcet-loser-p (c1 xs)
;;   (forall c2
;;           (and (member-equal c2 (candidate-ids xs))
;;                (not (equal c2 c1))
;;                (not (equal
;;                      c1
;;                      (irv (eliminate-other-candidates (list c1 c2) xs)))))))

;; (local (in-theory (e/d () (forall-c2-condorcet-loser-p forall-c2-condorcet-loser-p-necc))))

;; (defthm irv-satisfies-condorcet-loser-criterion
;;   (implies
;;    (and (irv-ballot-p xs)
;;         (member-equal c1 (candidate-ids xs))
;;         (forall-c2-condorcet-loser-p c1 xs))
;;    (not (equal (irv xs) c1))))

;; ----------------------------------------------------------------------

(defun-sk exists-loser-against-winner-in-head-to-head-p (xs)
  (exists loser
          (b* ((winner (irv xs)))
            (and (member-equal loser (candidate-ids xs))
                 (not (equal loser winner))
                 (equal (irv (eliminate-other-candidates (list loser winner) xs))
                        winner)))))

(local (in-theory (e/d () (exists-loser-against-winner-in-head-to-head-p
                           exists-loser-against-winner-in-head-to-head-p-suff))))

(local
 (defthm irv-satisfies-condorcet-loser-criterion-aux-trivial-subgoal-1
   (implies
    (and (irv-ballot-p xs)
         (consp xs)
         (< 2 (number-of-candidates xs))
         (< (number-of-candidates
             (eliminate-candidate
              (candidate-with-least-nth-place-votes
               0 (candidate-ids xs) xs)
              xs))
            2)
         (<= 2 (number-of-candidates xs)))
    (exists-loser-against-winner-in-head-to-head-p xs))
   :hints (("Goal"
            :in-theory
            (e/d
             ()
             (eliminate-candidate-reduces-the-number-of-candidates-by-one))
            :use
            ((:instance
              eliminate-candidate-reduces-the-number-of-candidates-by-one
              (id (candidate-with-least-nth-place-votes
                   0 (candidate-ids xs) xs))
              (xs xs)))))))

#||

;; (defthm eliminate-other-candidates-does-not-modify-xs
;;   (implies
;;    (acl2::set-equiv cids (candidate-ids xs))
;;    (equal (eliminate-other-candidates cids xs)
;;           xs)))

(skip-proofs
 ;; TODO -- needs eliminate-other-candidates-does-not-modify-xs, etc.
 (defthm irv-satisfies-condorcet-loser-criterion-aux-2
   (implies (and (equal (number-of-candidates xs) 2)
                 (irv-ballot-p xs)
                 (consp xs))
            (exists-loser-against-winner-in-head-to-head-p xs))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance exists-loser-against-winner-in-head-to-head-p-suff
                             (loser (car (remove-equal (irv xs) (candidate-ids xs))))
                             (xs xs)))))
   :otf-flg t))

;; (local
;;  (defthm first-choice-of-majority-satisfies-existence-of-loser
;;    (implies
;;     (and (irv-ballot-p xs)
;;          (consp xs)
;;          (< 2 (number-of-candidates xs)))
;;     (exists-loser-against-winner-in-head-to-head-p
;;      (first-choice-of-majority-p (candidate-ids xs) xs)
;;      xs))
;;    :hints
;;    (("Goal"
;;      :do-not-induct t
;;      :use
;;      ((:instance exists-loser-against-winner-in-head-to-head-p-suff
;;                  (loser (car (remove-equal
;;                               (first-choice-of-majority-p (candidate-ids xs) xs)
;;                               (candidate-ids xs))))
;;                  (c (first-choice-of-majority-p (candidate-ids xs) xs))
;;                  (xs xs)))))
;;    :otf-flg t))


(local
 (defthm irv-satisfies-condorcet-loser-criterion-aux-inductive-step
   (implies
    (and (irv-ballot-p xs)
         (consp xs)
         (< 2 (number-of-candidates xs))
         (exists-loser-against-winner-in-head-to-head-p
          (eliminate-candidate
           (candidate-with-least-nth-place-votes
            0 (candidate-ids xs) xs)
           xs)))
    (exists-loser-against-winner-in-head-to-head-p xs))
   :hints (("Goal"
            :do-not-induct t
            :use
            ((:instance exists-loser-against-winner-in-head-to-head-p-suff
                        (loser
                         (candidate-with-least-nth-place-votes
                          0 (candidate-ids xs) xs))
                        (xs xs)))
            :in-theory (e/d ()
                            ())))
   :otf-flg t))

(define condorcet-loser-ind-hint (xs)
  :enabled t
  :measure (number-of-candidates xs)
  :prepwork
  ((local (in-theory (e/d (number-of-candidates) ())))

   (local
    (defthm remove-equal-reduces-length-of-list
      (implies
       (and (true-listp lst) (member-equal x lst))
       (< (len (remove-equal x lst)) (len lst)))))

   (local
    (defthm condorcet-loser-ind-hint-termination-lemma
      (implies
       (and (consp xs)
            (irv-ballot-p xs)
            (< 2 (len (candidate-ids xs))))
       (<
        (len
         (remove-equal (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                             xs)
                       (candidate-ids xs)))
        (len (candidate-ids xs))))
      :hints (("Goal" :in-theory (e/d ()
                                      (candidate-with-least-nth-place-votes-is-in-cids
                                       candidate-with-least-nth-place-votes-returns-a-natp))
               :use ((:instance candidate-with-least-nth-place-votes-returns-a-natp
                                (n 0)
                                (cids (candidate-ids xs))
                                (xs xs))
                     (:instance candidate-with-least-nth-place-votes-is-in-cids
                                (n 0)
                                (cids (candidate-ids xs))
                                (xs xs))))))))

  (if (irv-ballot-p xs)

      (if (endp xs)
          xs
        (if (<= (number-of-candidates xs) 2)
            xs
          (b* ((step-n-candidate-to-remove
                (candidate-with-least-nth-place-votes
                 0 (candidate-ids xs) xs))
               (reduced-xs (eliminate-candidate step-n-candidate-to-remove xs)))
            (condorcet-loser-ind-hint reduced-xs))))
    xs))

(defthm irv-satisfies-condorcet-loser-criterion-aux
  (implies
   (and (irv-ballot-p xs)
        (<= 2 (number-of-candidates xs)))
   (exists-loser-against-winner-in-head-to-head-p xs))
  :hints
  (("Goal"
    :induct (condorcet-loser-ind-hint xs)
    :in-theory (e/d () ()))))

||#
