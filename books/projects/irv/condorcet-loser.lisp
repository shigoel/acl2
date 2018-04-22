;; Original Authors: Shilpi Goel      <shigoel@gmail.com>
;;                   Mayank Manjrekar <mankmonjre@gmail.com>

(in-package "IRV")

(include-book "irv")
(local (include-book "std/lists/set-difference"  :dir :system))
(local (include-book "std/lists/flatten"  :dir :system))
(local (include-book "std/lists/duplicity"  :dir :system))
(local (include-book "std/lists/remove-duplicates"  :dir :system))
(local (include-book "std/lists/remove"  :dir :system))
(local (include-book "std/lists/nth"  :dir :system))
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

(defxdoc condorcet-loser-criterion
  :parents (irv)
  :short "Proof that Instant-Runoff Voting Algorithm satisfies the
  Condorcet Loser Criterion" )

(local (xdoc::set-default-parents condorcet-loser-criterion))

;; ----------------------------------------------------------------------

;; Let xs be the original ballot, where c1 is a candidate.  Let
;; xs-pairwise be the modified xs that has been obtained by eliminating
;; all candidates but two --- c1 and say, some other candidate c2. If
;; IRV(xs-pairwise) != c1 for every such xs-pairwise, then IRV(xs) != c1.

(define remove-all ((x true-listp)
                    (y true-listp))
  :short "Remove all elements in @('x') from @('y')"
  :enabled t
  (if (endp x)
      y
    (remove-all (cdr x) (remove-equal (car x) y)))

  ///

  (defthm remove-all-cons-to-remove-all-remove-equal
    (equal (remove-all (cons e x) y)
           (remove-all x (remove-equal e y))))

  (defthm remove-all-x-and-cdr-x
    (equal (remove-all x (cdr x)) nil))

  (defthm remove-all-x-x-is-nil
    (implies (true-listp x)
             (equal (remove-all x x) nil))
    :hints (("Goal"
             :in-theory (e/d () (remove-all-cons-to-remove-all-remove-equal))
             :use ((:instance remove-all-cons-to-remove-all-remove-equal
                              (e (car x))
                              (x (cdr x))
                              (y (cdr x)))))))

  (defthm remove-all-and-remove-equal-commute
    (equal (remove-all as (remove-equal e bs))
           (remove-equal e (remove-all as bs))))

  (defthm remove-all-commutes
    (equal (remove-all as (remove-all bs cs))
           (remove-all bs (remove-all as cs))))

  (defthm subsetp-equal-and-remove-all-1
    (implies (subsetp-equal x y)
             (subsetp-equal (remove-all x y) y))
    :hints (("Goal" :in-theory (e/d (subsetp-equal) ())))))

(define eliminate-candidates ((cids nat-listp "Candidates to remove")
                              (xs   irv-ballot-p))
  :short "Remove @('cids') from @('xs')"
  :returns (new-xs irv-ballot-p :hyp (irv-ballot-p xs))

  (if (endp cids)
      xs
    (b* ((new-xs (eliminate-candidate (car cids) xs)))
      (eliminate-candidates (cdr cids) new-xs)))

  ///

  (defthm eliminate-candidates-returns-a-subset-of-candidates
    (subsetp-equal (candidate-ids (eliminate-candidates cids xs))
                   (candidate-ids xs)))

  (defthm intersectp-equal-and-remove-equal
    (implies (intersectp-equal x (remove-equal e y))
             (intersectp-equal x y))
    :hints (("Goal" :in-theory (e/d (intersectp-equal remove-equal) ()))))

  (defthm eliminate-candidates-removes-no-candidate-when-cids-not-in-candidates
    (implies (and (irv-ballot-p xs)
                  (not (intersectp-equal cids (candidate-ids xs))))
             (equal (eliminate-candidates cids xs) xs))
    :hints (("Goal" :in-theory (e/d (intersectp-equal) ()))))

  (defthm remove-equal-commutes
    (equal (remove-equal c1 (remove-equal c2 x))
           (remove-equal c2 (remove-equal c1 x)))
    :hints (("Goal" :in-theory (e/d (remove-equal) ()))))

  (local
   (defthm remove-equal-and-consp-lemma
     (implies (and (not (consp (remove-equal c1 x)))
                   (consp (remove-equal c2 x)))
              (not (consp (remove-equal c1 (remove-equal c2 x)))))
     :hints (("Goal" :in-theory (e/d (remove-equal) ())))))

  (defthm eliminate-candidate-commutes
    (equal (eliminate-candidate c1 (eliminate-candidate c2 xs))
           (eliminate-candidate c2 (eliminate-candidate c1 xs)))
    :hints (("Goal" :in-theory (e/d (eliminate-candidate) ()))))

  (defthm eliminate-candidates-and-eliminate-candidate-commute
    (equal (eliminate-candidates cids (eliminate-candidate cid xs))
           (eliminate-candidate cid (eliminate-candidates cids xs))))

  (defthm eliminate-candidates-does-remove-candidates
    (implies (member-equal cid cids)
             (equal (member-equal cid (candidate-ids (eliminate-candidates cids xs)))
                    nil))
    :hints (("Goal" :in-theory
             (e/d (eliminate-candidates-and-eliminate-candidate-commute)
                  ()))))

  (defthm eliminate-candidates-removes-only-the-requested-candidates
    (implies (not (member-equal c cids))
             (iff (member-equal c (candidate-ids (eliminate-candidates cids xs)))
                  (member-equal c (candidate-ids xs)))))

  (defthm candidate-ids-of-eliminate-candidates
    (equal (candidate-ids (eliminate-candidates cids xs))
           (remove-all cids (candidate-ids xs)))))

(define eliminate-other-candidates ((cids nat-listp "Candidates to preserve")
                                    (xs irv-ballot-p))

  :short "Remove all candidates from @('xs') except for those in
  @('cids')"

  :prepwork
  ((defthm nat-listp-of-set-difference-equal
     (implies (nat-listp x)
              (nat-listp (set-difference-equal x y)))
     :hints (("Goal" :in-theory (e/d (set-difference-equal) ())))))

  :returns (new-xs irv-ballot-p :hyp (irv-ballot-p xs))

  (b* ((candidates-to-remove
        (remove-all cids (candidate-ids xs))))
    (eliminate-candidates candidates-to-remove xs))

  ///

  (defthm eliminate-other-candidates-returns-a-subset-of-cids
    (subsetp-equal (candidate-ids (eliminate-other-candidates cids xs))
                   cids))  

  (defthm remove-all-and-member-equal-1
    (implies (member-equal e a)
             (equal (member-equal e (remove-all a b))
                    nil)))

  (defthm remove-all-and-member-equal-2
    (implies (not (member-equal e a))
             (iff (member-equal e (remove-all a b))
                  (member-equal e b))))

  ;; (defthm subsetp-equal-and-remove-all-2
  ;;   (implies (and (subsetp-equal a b)
  ;;                 (no-duplicatesp-equal a)
  ;;                 (no-duplicatesp-equal b))
  ;;            (subsetp-equal a (remove-all (remove-all a b) b)))
  ;;   :hints (("Goal" :in-theory (e/d (subsetp-equal
  ;;                                    no-duplicatesp-equal)
  ;;                                   ()))))

  ;; (defthm cids-is-a-subset-of-eliminate-other-candidates
  ;;   (implies (subsetp-equal cids (candidate-ids xs))
  ;;            (subsetp-equal
  ;;             cids
  ;;             (candidate-ids (eliminate-other-candidates cids xs)))))

  ;; (defthm eliminate-other-candidates-equal-to-cids-under-set-equiv
  ;;   (implies (subsetp-equal cids (candidate-ids xs))
  ;;            (acl2::set-equiv
  ;;             (candidate-ids (eliminate-other-candidates cids xs))
  ;;             cids))
  ;;   :hints (("Goal" :in-theory (e/d (acl2::set-equiv)
  ;;                                   (eliminate-other-candidates
  ;;                                    candidate-ids)))))
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
