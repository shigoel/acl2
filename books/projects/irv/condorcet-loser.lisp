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

  (defthm remove-all-returns-a-subset-of-the-list
    (subsetp-equal (remove-all x y) y)
    :hints (("Goal" :in-theory (e/d (subsetp-equal) ()))))

  (defthm remove-all-and-member-equal-1
    (implies (member-equal e a)
             (equal (member-equal e (remove-all a b)) nil)))

  (defthm remove-all-and-member-equal-2
    (implies (not (member-equal e a))
             (iff (member-equal e (remove-all a b))
                  (member-equal e b))))

  (defthm remove-all-of-nil-is-nil
    (equal (remove-all x nil) nil))

  (defthm remove-all-x-from-cons-e-y
    (equal (remove-all x (cons e y))
           (if (member-equal e x)
               (remove-all x y)
             (cons e (remove-all x y)))))

  (defthm remove-all-superset-from-subset-is-nil
    (implies (and (subsetp-equal y x)
                  (true-listp y))
             (equal (remove-all x y) nil))
    :hints (("Goal" :in-theory (e/d (subsetp-equal) ()))))

  (defthm remove-all-and-set-equiv
    ;; More general version of remove-all-x-x-is-nil.
    (implies (and (acl2::set-equiv x y)
                  (true-listp y))
             (equal (remove-all x y) nil))
    :hints (("Goal"
             :induct (remove-all x y)
             :in-theory (e/d (acl2::set-equiv)
                             ((:induction member-equal)
                              remove-all-cons-to-remove-all-remove-equal
                              remove-all-and-remove-equal-commute)))))

  (defthm nested-remove-alls-and-subsetp-equal
    (implies (subsetp-equal a c)
             (subsetp-equal a (remove-all (remove-all a b) c)))
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
           (remove-all cids (candidate-ids xs))))

  (defthm eliminate-candidates-where-cids=nil-does-not-modify-xs
    (equal (eliminate-candidates nil xs) xs)
    :hints (("Goal" :in-theory (e/d (eliminate-candidates) ())))))

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

  (defthm cids-is-a-subset-of-eliminate-other-candidates
    (implies (subsetp-equal cids (candidate-ids xs))
             (subsetp-equal
              cids
              (candidate-ids (eliminate-other-candidates cids xs)))))

  (defthm eliminate-other-candidates-equal-to-cids-under-set-equiv
    (implies (subsetp-equal cids (candidate-ids xs))
             (acl2::set-equiv
              (candidate-ids (eliminate-other-candidates cids xs))
              cids))
    :hints (("Goal" :in-theory (e/d (acl2::set-equiv)
                                    (eliminate-other-candidates
                                     candidate-ids)))))

  (defthm eliminate-other-candidates-does-not-modify-xs-when-cids=candidate-ids
    ;; Directly follows from remove-all-and-set-equiv.
    (implies
     (acl2::set-equiv cids (candidate-ids xs))
     (equal (eliminate-other-candidates cids xs) xs))
    :hints (("Goal" :do-not-induct t))))

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

;; ----------------------------------------------------------------------

;; TODO:
(skip-proofs
 (defthm head-to-head-irv-is-the-same-as-full-irv
   (implies
    (and (member-equal id (candidate-ids xs))
         (not (equal id (irv xs)))
         (irv-ballot-p xs)
         (<= 2 (number-of-candidates xs)))
    (equal (irv (eliminate-other-candidates (list id (irv xs)) xs))
           (irv xs)))
   :hints (("Goal" :in-theory (e/d (eliminate-other-candidates)
                                   ())))))

(local
 (defthm car-of-remove-element-is-not-equal-to-that-element
   (implies (and (<= 2 (len x))
                 (no-duplicatesp-equal x))
            (not (equal (car (remove-equal e x)) e)))
   :hints (("Goal" :in-theory (e/d (len) ())))))

(local
 (defthm car-of-remove-element-is-still-a-member-of-list
   (implies (and (<= 2 (len x))
                 (no-duplicatesp-equal x))
            (member-equal (car (remove-equal e x)) x))
   :hints (("Goal" :in-theory (e/d () ())))))

(local
 (defthm list-with-two-elements-and-set-equiv-lemma
   (implies (and (equal (len x) 2)
                 (no-duplicatesp-equal x)
                 (member-equal e x))
            (acl2::set-equiv
             (list (car (remove-equal e x)) e)
             x))
   :hints (("Goal" :in-theory (e/d (len acl2::set-equiv)
                                   ())))))

(local
 (defthmd consp-of-xs-based-on-number-of-candidates
   (implies (and (not (equal (number-of-candidates xs) 0))
                 (irv-ballot-p xs))
            (consp xs))
   :hints (("Goal" :in-theory (e/d (number-of-candidates) ())))))

(defthm irv-satisfies-condorcet-loser-criterion-aux-helper-1
  (implies (and (equal (number-of-candidates xs) 2)
                (irv-ballot-p xs))
           (exists-loser-against-winner-in-head-to-head-p xs))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (e/d (number-of-candidates
          consp-of-xs-based-on-number-of-candidates)
         (eliminate-other-candidates-does-not-modify-xs-when-cids=candidate-ids))
    :use
    ((:instance exists-loser-against-winner-in-head-to-head-p-suff
                (loser
                 (car (remove-equal (irv xs) (candidate-ids xs))))
                (xs xs))
     (:instance eliminate-other-candidates-does-not-modify-xs-when-cids=candidate-ids
                (cids (list (car (remove-equal
                                  (irv xs)
                                  (candidate-ids xs)))
                            (irv xs)))
                (xs xs))))))

(defthm loser-exists-against-majority-winner
  (implies
   (and (irv-ballot-p xs)
        (consp xs)
        (natp (first-choice-of-majority-p (candidate-ids xs) xs))
        (<= 2 (number-of-candidates xs)))
   (exists-loser-against-winner-in-head-to-head-p xs))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (e/d (number-of-candidates)
         (eliminate-other-candidates-does-not-modify-xs-when-cids=candidate-ids))
    :use
    ((:instance exists-loser-against-winner-in-head-to-head-p-suff
                (loser (car (remove-equal (irv xs) (candidate-ids xs))))
                (xs xs))
     (:instance eliminate-other-candidates-does-not-modify-xs-when-cids=candidate-ids
                (cids (list (car (remove-equal
                                  (irv xs)
                                  (candidate-ids xs)))
                            (irv xs)))
                (xs xs))))))

(defthmd unwind-irv-when-not-majority
  (implies (and (irv-ballot-p xs)
                (not (natp (first-choice-of-majority-p
                            (candidate-ids xs) xs))))
           (equal (irv xs)
                  (irv (eliminate-candidate
                        (candidate-with-least-nth-place-votes
                         0 (candidate-ids xs) xs)
                        xs))))
  :hints (("Goal" :in-theory (e/d (irv) ()))))

(local
 (defthm irv-satisfies-condorcet-loser-criterion-aux-inductive-step
   (implies
    (and (irv-ballot-p xs)
         (consp xs)
         (< 2 (number-of-candidates xs))
         (not (natp (first-choice-of-majority-p (candidate-ids xs) xs)))
         (exists-loser-against-winner-in-head-to-head-p
          (eliminate-candidate
           (candidate-with-least-nth-place-votes
            0 (candidate-ids xs) xs)
           xs)))
    (exists-loser-against-winner-in-head-to-head-p xs))
   :hints
   (("Goal"
     :do-not-induct t
     :use
     ((:instance (:definition
                  exists-loser-against-winner-in-head-to-head-p)
                 ;; For the quantifier in the hypotheses:
                 (xs
                  (eliminate-candidate
                   (candidate-with-least-nth-place-votes
                    0 (candidate-ids xs) xs)
                   xs)))
      (:instance exists-loser-against-winner-in-head-to-head-p-suff
                 ;; For the quantifier in the conclusion: using the witness of
                 ;; the quantifier in the hypotheses to proceed...
                 (loser
                  (exists-loser-against-winner-in-head-to-head-p-witness
                   (eliminate-candidate
                    (candidate-with-least-nth-place-votes
                     0 (candidate-ids xs) xs)
                    xs)))
                 (xs xs))))
    (and stable-under-simplificationp
         '(:in-theory (e/d (unwind-irv-when-not-majority) ()))))))

(local
 (defthmd irv-satisfies-condorcet-loser-criterion-aux-helper-2
   (implies
    (and (irv-ballot-p xs)
         (< 2 (number-of-candidates xs)))
    (exists-loser-against-winner-in-head-to-head-p xs))
   :hints
   (("Goal" :induct (irv xs)
     :in-theory (e/d (irv) ())))))

(defthm irv-satisfies-condorcet-loser-criterion-in-terms-of-exists-quantifier
  (implies
   (and (irv-ballot-p xs)
        (<= 2 (number-of-candidates xs)))
   (exists-loser-against-winner-in-head-to-head-p xs))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance irv-satisfies-condorcet-loser-criterion-aux-helper-2))
    :in-theory (e/d (irv-satisfies-condorcet-loser-criterion-aux-helper-1)
                    (irv-satisfies-condorcet-loser-criterion-aux-helper-2)))))

;; ----------------------------------------------------------------------

(i-am-here)

(defthm head-to-head-irv-is-the-same-as-full-irv
  (implies
   (and (member-equal id (candidate-ids xs))
        (not (equal id (irv xs)))
        (irv-ballot-p xs)
        (< 2 (number-of-candidates xs)))
   (equal (irv (eliminate-other-candidates (list id (irv xs)) xs))
          (irv xs)))
  :hints (("Goal"
           :in-theory (e/d () ()))))
