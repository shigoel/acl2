;; Original Authors: Shilpi Goel      <shigoel@gmail.com>
;;                   Mayank Manjrekar <mankmonjre@gmail.com>

(in-package "IRV")

(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs"  :dir :system)
(include-book "std/lists/sets"  :dir :system)
(include-book "defsort/defsort" :dir :system)
(local (include-book "std/lists/flatten"  :dir :system))
(local (include-book "std/lists/duplicity"  :dir :system))
(local (include-book "std/lists/remove-duplicates"  :dir :system))
(local (include-book "std/lists/nth"  :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; The winner will be chosen as follows.

;;   (1) If a candidate is the first choice of more than half of the voters,
;;       then he/she wins.  Otherwise:

;;   (2) Adjust each ballot by eliminating the candidate with the
;;       fewest first-place votes.  If there is a tie for the fewest
;;       first-place votes, then delete the candidate with the least
;;       second-place votes, etc.  If the tie persists, then delete
;;       the candidate with the smallest ID.

;;   (3) Go to (1).

;; ----------------------------------------------------------------------

(defxdoc irv
  :parents (acl2::projects)
  :short "Reasoning about an Instant-Runoff Voting Algorithm"
  )

(local (xdoc::set-default-parents irv))

;; ----------------------------------------------------------------------
;; Recognizer for a well-formed IRV ballot
;; ----------------------------------------------------------------------

(define non-empty-true-list-listp (x)
  :enabled t
  :short "Similar to @(see true-list-listp), except that if @('x') is
  non-empty, each element of @('x') must be a @(see consp)."
  (cond ((atom x) (eq x nil))
        (t (and (true-listp (car x))
                (consp (car x))
                (non-empty-true-list-listp (cdr x)))))

  ///

  (defthm non-empty-true-list-listp-implies-true-listp
    (implies (non-empty-true-list-listp xs)
             (true-listp xs))
    :rule-classes :forward-chaining)

  (defthm non-empty-true-list-listp-implies-true-list-listp
    (implies (non-empty-true-list-listp x)
             (true-list-listp x))
    :rule-classes :forward-chaining)

  (defthm non-empty-true-list-listp-bigger-implies-smaller
    (implies (non-empty-true-list-listp xs)
             (non-empty-true-list-listp (cdr xs)))))

(define irv-ballot-p (xs)
  :short "Recognizer for a well-formed IRV ballot"
  :enabled t
  (if (consp xs)
      (b* ((one (car xs))
           (rest (cdr xs)))
        (and
         ;; There must be at least one candidate in the election at
         ;; this point.  Each voter may or may not rank all the
         ;; candidates. The preferences of a voter must satisfy the
         ;; following constraints: a voter should not list a candidate
         ;; more than once and should list at least one candidate.
         (nat-listp one)
         (consp one)
         (no-duplicatesp-equal one)
         (irv-ballot-p rest)))
    (equal xs nil))

  ///

  (defthm irv-ballot-p-implies-non-empty-true-list-listp
    (implies (irv-ballot-p xs)
             (non-empty-true-list-listp xs))
    :rule-classes :forward-chaining)

  (defthm irv-ballot-p-cdr
    (implies (irv-ballot-p xs)
             (irv-ballot-p (cdr xs)))))

(defsection sorting

  :parents (irv)

  (acl2::defsort
   :comparablep natp
   :compare< <
   :prefix <
   :comparable-listp nat-listp
   :true-listp t
   :weak nil)

  ;; (defthm set-equiv-implies-equal-nat-listp
  ;;   (implies (acl2::set-equiv x y)
  ;;            (iff (nat-listp x)
  ;;                 (nat-listp y)))
  ;;   :hints (("Goal" :in-theory (e/d (acl2::set-equiv
  ;;                                     nat-listp
  ;;                                     subsetp-equal)
  ;;                                    ())))
  ;;   :rule-classes :congruence)

  (local
   (defthm member-equal-and-insert-sort
     (implies (consp a)
              (member-equal (car a) (acl2::<-insertsort a)))
     :hints (("Goal" :in-theory (e/d (acl2::<-insertsort
                                       acl2::<-insert)
                                      ())))))

  (defthm subsetp-cdr-and-<-insertsort
    (subsetp-equal (acl2::<-insertsort (cdr a))
                   (acl2::<-insertsort a))
    :hints (("Goal" :in-theory (e/d (acl2::<-insertsort
                                      acl2::<-insert
                                      subsetp-equal)
                                     ()))))

  (defthmd a-is-a-subset-of-<-insertsort-a
    (subsetp-equal a (acl2::<-insertsort a))
    :hints (("Goal" :in-theory (e/d (subsetp-equal
                                      member-equal)
                                     ()))))

  (defthmd <-insertsort-a-is-a-subset-of-a
    (subsetp-equal (acl2::<-insertsort a) a)
    :hints (("Goal" :in-theory (e/d (subsetp-equal
                                      member-equal
                                      acl2::<-insertsort
                                      acl2::<-insert)
                                     ()))))

  (defthm <-insertsort-equal-under-set-equiv
    (acl2::set-equiv (acl2::<-insertsort a) a)
    :hints (("Goal" :in-theory (e/d (<-insertsort-a-is-a-subset-of-a
                                      a-is-a-subset-of-<-insertsort-a
                                      acl2::set-equiv)
                                     ())))))

(define candidate-ids ((xs irv-ballot-p))
  :short "Get a sorted list of candidate IDs currently in the election"
  :returns (cids true-listp :rule-classes :type-prescription)

  (acl2::<-sort (remove-duplicates-equal (acl2::flatten xs)))

  ///

  (local
   (defthm nat-listp-of-candidate-ids-helper
     (implies (irv-ballot-p xs)
              (nat-listp (remove-duplicates-equal (acl2::flatten xs))))
     :hints (("Goal" :in-theory (e/d (nat-listp acl2::flatten) ())))))

  (defthm nat-listp-of-candidate-ids
    (implies (irv-ballot-p xs)
             (nat-listp (candidate-ids xs)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d ()
                              (remove-duplicates-equal
                               acl2::flatten)))))

  (local
   (defthm consp-of-candidate-ids-helper
     (implies
      (and (non-empty-true-list-listp xs)
           (consp xs))
      (consp (acl2::flatten xs)))
     :hints (("Goal" :in-theory (e/d (acl2::flatten) ())))
     :rule-classes :type-prescription))

  (defthm consp-of-candidate-ids
    (implies
     (and (non-empty-true-list-listp xs)
          (consp xs))
     (consp (candidate-ids xs)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () (acl2::flatten))))
    :rule-classes :type-prescription)

  (defthm subset-of-candidate-ids-cdr
    (subsetp-equal (candidate-ids (cdr xs))
                   (candidate-ids xs)))

  (defthmd nat-listp-and-subsetp-equal
    (implies (and (subsetp-equal x y)
                  (true-listp x)
                  (nat-listp y))
             (nat-listp x))
    :hints (("Goal" :in-theory (e/d (nat-listp subsetp-equal)
                                     ()))))

  (defthm candidate-ids-nat-listp-smaller
    (implies (nat-listp (candidate-ids xs))
             (nat-listp (candidate-ids (cdr xs))))
    :hints (("Goal"
             :use ((:instance subset-of-candidate-ids-cdr)
                   (:instance nat-listp-and-subsetp-equal
                              (x (candidate-ids (cdr xs)))
                              (y (candidate-ids xs))))
             :in-theory (e/d ()
                              (subset-of-candidate-ids-cdr)))))

  (local
   (defthm subset-of-flatten-helper
     (implies (member-equal y xs)
              (subsetp-equal y (acl2::flatten xs)))
     :hints (("Goal"
              :in-theory (e/d (subsetp-equal acl2::flatten) ())))))

  (defthm subset-of-flatten
    (implies (subsetp-equal ys xs)
             (subsetp-equal (acl2::flatten ys) (acl2::flatten xs)))
    :hints (("Goal"
             :in-theory (e/d (subsetp-equal acl2::flatten) ()))))

  (defthm subsetp-of-irv-ballots-implies-subsetp-of-candidate-ids
    (implies (subsetp-equal ys xs)
             (subsetp-equal (candidate-ids ys)
                            (candidate-ids xs)))
    :hints (("Goal" :in-theory (e/d (acl2::flatten) ()))))

  (defthm no-duplicates-in-candidate-ids
    (no-duplicatesp-equal (candidate-ids xs))
    :hints (("Goal" :in-theory (e/d (no-duplicatesp-equal)
                                     ())))))

(define number-of-candidates ((xs irv-ballot-p))
  :returns (num natp :rule-classes :type-prescription)
  (len (candidate-ids xs))

  ///

  (defthmd number-of-candidates-is-exactly-one-lemma
    (implies
     (and (irv-ballot-p xs)
          (consp xs)
          (<= (number-of-candidates xs) 1))
     (equal (number-of-candidates xs) 1))
    :hints (("Goal"
             :in-theory (e/d (candidate-ids)
                              ())))))

(define number-of-voters ((xs irv-ballot-p))
  :returns (num natp :rule-classes :type-prescription)
  (len xs))

;; ----------------------------------------------------------------------
;; Implementation of the IRV algorithm
;; ----------------------------------------------------------------------

(define make-nth-choice-list ((n natp)
                              (xs irv-ballot-p))
  :short "Returns a list of the @('n')th preference candidates of all
  the voters"

  :prepwork
  ((defthm natp-nth-of-nat-listp
     (implies (and (nat-listp lst)
                   (< n (len lst))
                   (natp n))
              (natp (nth n lst)))
     :rule-classes (:rewrite :type-prescription))

   (local (in-theory (e/d (number-of-candidates) ()))))

  :returns (choice-lst nat-listp :hyp :guard)

  (if (endp xs)
      nil
    (if (< n (len (car xs)))
        ;; If the first voter ranked less than n candidates, then skip
        ;; that voter and collect nth choices for the rest of the
        ;; voters.
        (cons (nth n (car xs)) ;; nth choice of the first voter
              (make-nth-choice-list n (cdr xs)))
      (make-nth-choice-list n (cdr xs))))

  ///

  (defthm consp-of-0th-choice-occurrence-list
    (implies (and (consp xs)
                  (irv-ballot-p xs))
             (consp (make-nth-choice-list 0 xs)))
    :rule-classes :type-prescription)

  (defthm make-nth-choice-list-returns-subset-of-all-cids
    (implies (and (irv-ballot-p xs) (natp n))
             (subsetp-equal (make-nth-choice-list n xs)
                            (candidate-ids xs)))
    :hints (("Goal" :in-theory (e/d (number-of-candidates
                                     candidate-ids
                                     acl2::flatten
                                     remove-duplicates-equal
                                     len)
                                    ())))))

(define count-alistp (l)
  :enabled t
  :short "Recognizer for a count alist (see @(see create-count-alist))"
  (cond ((atom l) (eq l nil))
        (t (and (consp (car l))
                (natp (caar l))
                (natp (cdar l))
                (count-alistp (cdr l)))))
  ///
  (defthm count-alistp-implies-alistp
    (implies (count-alistp l)
             (alistp l)))

  (defthm nat-listp-of-strip-cars-of-count-alistp
    (implies (count-alistp alst)
             (nat-listp (strip-cars alst))))

  (defthm nat-listp-of-strip-cdrs-of-count-alistp
    (implies (count-alistp alst)
             (nat-listp (strip-cdrs alst))))

  (defthm natp-of-key-of-first-pair-of-count-alistp
    (implies (and (count-alistp alst) (consp alst))
             (natp (caar alst)))))

(define create-count-alist ((cids nat-listp "All the candidates in the election, sorted")
                            (choice-lst nat-listp))
  :short "Given a choice list, maps each candidate ID to the number
  of votes they obtained"
  :returns (count-alst alistp)

  (if (endp cids)
      nil
    (b* ((cid (car cids))
         (count (acl2::duplicity cid choice-lst)))
      (cons (cons cid count)
            (create-count-alist (cdr cids) choice-lst))))
  ///

  (defret count-alistp-of-create-count-alist
    (implies (nat-listp cids)
             (count-alistp count-alst)))

  (defthm consp-of-create-count-alist
    (equal (consp (create-count-alist cids choice-lst))
           (consp cids)))

  (defthm strip-cars-of-create-count-alist-is-sorted-if-cids-is-sorted
    (implies (acl2::<-ordered-p cids)
             (acl2::<-ordered-p (strip-cars (create-count-alist cids choice-lst))))
    :hints (("Goal" :in-theory (e/d (acl2::<-ordered-p) ()))))

  (defthm strip-cars-of-create-count-alist-equal-under-set-equiv
    (acl2::set-equiv (strip-cars (create-count-alist cids choice-lst)) cids)
    :hints (("Goal" :in-theory (e/d (acl2::set-equiv) ())))))

(define create-nth-choice-count-alist
  ((n natp)
   (cids nat-listp "All the candidates in the election, sorted")
   (xs irv-ballot-p))

  :returns (count-alst alistp)

  (b* ((choice-lst (make-nth-choice-list n xs))
       (count-alst (create-count-alist cids choice-lst)))
    count-alst)

  ///

  (defret count-alistp-of-create-nth-choice-count-alist
    (implies (nat-listp cids)
             (count-alistp count-alst)))

  (defret strip-cars-of-create-nth-choice-count-alist-is-sorted-if-cids-is-sorted
    (implies (acl2::<-ordered-p cids)
             (acl2::<-ordered-p (strip-cars count-alst))))

  (defthm consp-of-create-nth-choice-count-alist
    (equal (consp (create-nth-choice-count-alist 0 cids xs))
           (consp cids)))

  (defret strip-cars-of-create-nth-choice-count-alist-equal-under-set-equiv
    (acl2::set-equiv (strip-cars count-alst) cids)))

(define majority ((n natp "Number of voters"))
  :returns (maj natp
                :hyp :guard
                :rule-classes :type-prescription)
  :prepwork
  ((local (include-book "arithmetic-5/top" :dir :system)))
  (if (evenp n) (/ n 2) (/ (- n 1) 2))

  ///

  (local (in-theory (e/d () (acl2::functional-commutativity-of-minus-*-left))))

  (defthm majority-is-less-than-total
    (implies (posp n)
             (< (majority n) n))
    :rule-classes :linear))

(define max-nats ((x nat-listp))
  :short "Pick the maximum number in a list of natural numbers"
  :returns (max natp :hyp :guard
                :rule-classes (:rewrite :type-prescription))
  (cond ((atom x) 0)
        ((atom (cdr x)) (lnfix (car x)))
        (t (max (lnfix (car x)) (max-nats (cdr x)))))
  ///

  (defthm max-nats-returns-a-member-of-input
    (implies (and (nat-listp x) (consp x))
             (member-equal (max-nats x) x)))

  (defthm max-nats-of-list-of-one-element
    (implies (natp e)
             (equal (max-nats (list e)) e))))

(define first-choice-of-majority-p ((cids nat-listp "Sorted candidate IDs")
                                    (xs irv-ballot-p))
  :short "Returns the candidate, if any, who is the first choice of
  more than half of the voters"
  :long "<p>This function encodes step (1) of the IRV algorithm: if a
  candidate among @('cids') is the first choice of more than half of
  the voters, then it wins --- this function returns the ID of that
  candidate.  If no such candidate exists, this function returns
  @('nil').</p>"

  :guard-hints (("Goal" :do-not-induct t))

  :returns (first-choice-of-majority
            acl2::maybe-natp
            :hyp :guard
            :hints (("Goal" :in-theory (e/d (acl2::maybe-natp) ()))))

  :prepwork
  ((defthm consp-of-rassoc-equal-of-max-nats-of-strip-cdrs
     (implies (and (consp alst)
                   (nat-listp (strip-cdrs alst)))
              (consp (rassoc-equal (max-nats (strip-cdrs alst)) alst)))
     :hints (("Goal" :in-theory (e/d (max-nats) ()))))

   (defthm natp-of-car-of-rassoc-equal-of-max-nats-of-strip-cdrs
     (implies (and (consp alst)
                   (nat-listp (strip-cars alst))
                   (nat-listp (strip-cdrs alst)))
              (natp (car (rassoc-equal (max-nats (strip-cdrs alst)) alst))))
     :hints (("Goal" :in-theory (e/d (max-nats) ())))
     :rule-classes (:rewrite :type-prescription)))

  (if (or (endp xs) (endp cids))
      nil
    (b* ((n (number-of-voters xs))
         (majority (majority n))
         (count-alst (create-nth-choice-count-alist 0 cids xs))
         (max-votes  (max-nats (strip-cdrs count-alst))))
      (if (< majority max-votes)
          (car (rassoc-equal max-votes count-alst))
        nil))))

(define list-elements-equal (e (x true-listp))
  :short "Returns @('t') if all elements of @('x') are equal to @('e')"
  :returns (elem-equal? booleanp :rule-classes :type-prescription)

  (if (endp x)
      t
    (and (equal (car x) e)
         (list-elements-equal e (cdr x)))))

;; (define pick-candidate-among-those-with-same-number-of-first-place-votes
;;   ((cids nat-listp "Sorted Candidate IDs")
;;    (xs irv-ballot-p))
;;   :short "If every remaining candidate has the same number of
;;     first-place votes, pick the candidate with the smallest ID"
;;   :long "<p>This function encodes step (2) of the IRV algorithm. This
;;   function returns @('nil') if <b>all</b> the remaining candidates do
;;   not have the same number of first-place votes.</p>"

;;   :guard-hints (("Goal" :do-not-induct t))

;;   :returns (candidate
;;             acl2::maybe-natp
;;             :hyp :guard
;;             :hints (("Goal" :in-theory (e/d (acl2::maybe-natp) ()))))

;;   :prepwork
;;   ((local
;;     (defthm consp-of-car-of-count-alist
;;       (implies (and (consp alst)
;;                     (count-alistp alst))
;;                (consp (car alst))))))

;;   (if (or (endp xs) (endp cids))
;;       nil
;;     (b* ((count-alst (create-nth-choice-count-alist 0 cids xs))
;;          (all-votes  (strip-cdrs count-alst))
;;          (all-votes-same? (list-elements-equal (car all-votes) all-votes)))
;;       (if all-votes-same?
;;           (car (car count-alst)) ;; Smallest candidate ID
;;         nil))))

(define min-nats ((x nat-listp))
  :short "Pick the minimum number in a list of natural numbers"
  :returns (min natp :hyp :guard
                :rule-classes (:rewrite :type-prescription))
  (cond ((atom x) 0)
        ((atom (cdr x)) (lnfix (car x)))
        (t (min (lnfix (car x)) (min-nats (cdr x)))))
  ///
  (defthm min-nats-returns-a-member-of-input
    (implies (and (nat-listp x) (consp x))
             (member-equal (min-nats x) x))))

(define all-keys ((val natp)
                  (alst count-alistp))
  :short "Returns a list of all the keys in @('alst') with the value @('val')"
  :prepwork
  ((defthm consp-of-rassoc-equal
     (implies (and (alistp alst)
                   (rassoc-equal val alst))
              (consp (rassoc-equal val alst))))

   (local
    (defthm natp-of-car-of-rassoc-equal-of-count-alist
      (implies (and (natp val)
                    (count-alistp alst)
                    (rassoc-equal val alst))
               (natp (car (rassoc-equal val alst))))))

   (defthm count-alistp-of-delete-assoc-equal
     (implies (count-alistp alst)
              (count-alistp (delete-assoc-equal key alst)))))
  :returns
  (cids nat-listp :hyp :guard)

  (if (endp alst)
      nil
    (b* ((pair (rassoc-equal val alst)))
      (if (equal pair nil)
          nil
        (cons (car pair)
              (all-keys val (delete-assoc-equal
                             (car pair)
                             alst))))))

  ///

  (defthm rassoc-equal-returns-a-member-of-keys
    (implies (member-equal val (strip-cdrs alst))
             (member-equal (car (rassoc-equal val alst))
                           (strip-cars alst))))

  (defthm delete-assoc-equal-and-subset-equal
    (subsetp-equal (delete-assoc-equal val alst) alst))

  (defthm strip-cars-of-delete-assoc-equal-and-subset-equal
    (subsetp-equal (strip-cars (delete-assoc-equal val alst))
                   (strip-cars alst)))

  (defthm rassoc-equal-returns-nil-when-value-not-found-in-alist
    (implies (not (member-equal val (strip-cdrs alst)))
             (equal (rassoc-equal val alst) nil)))

  (defthmd all-keys-returns-nil-when-value-not-found-in-alist
    (implies (not (member-equal val (strip-cdrs alst)))
             (equal (all-keys val alst) nil)))

  (defthm rassoc-equal-is-non-empty-when-non-nil-value-found-in-alist
    (implies (and (member-equal val (strip-cdrs alst)) val)
             (rassoc-equal val alst)))

  (defthm all-keys-is-non-empty-when-non-nil-value-found-in-alist
    (implies (and (member-equal val (strip-cdrs alst)) val)
             (all-keys val alst)))

  (defthm nil-is-not-a-member-of-any-nat-listp
    (implies (nat-listp lst)
             (equal (member-equal nil lst) nil)))

  (defthmd all-keys-returns-a-subset-of-keys-helper
    (implies (member-equal val (strip-cdrs alst))
             (subsetp-equal (all-keys val alst)
                            (strip-cars alst))))

  (defthm all-keys-returns-a-subset-of-keys
    (subsetp-equal (all-keys val alst)
                   (strip-cars alst))
    :hints (("Goal"
             :cases ((not (member-equal val (strip-cdrs alst))))
             :in-theory (e/d (all-keys-returns-nil-when-value-not-found-in-alist
                              all-keys-returns-a-subset-of-keys-helper)
                             ()))))

  ;; (i-am-here)

  ;; (defthm <-ordered-p-after-remove-equal
  ;;   (implies (acl2::<-ordered-p lst)
  ;;            (acl2::<-ordered-p (remove-equal val lst)))
  ;;   :hints (("Goal"
  ;;            :cases ((member-equal val lst))
  ;;            :in-theory (e/d (acl2::<-ordered-p nat-listp) ()))))

  ;; (local
  ;;  (defthm remove-equal-and-strip-cars-of-delete-assoc-equal
  ;;    (implies (no-duplicatesp-equal (strip-cars alst))
  ;;             (equal (strip-cars (delete-assoc-equal key alst))
  ;;                    (remove-equal key (strip-cars alst))))))

  ;; (defthm <-ordered-p-after-delete-assoc-equal
  ;;   (implies (and (acl2::<-ordered-p (strip-cars alst))
  ;;                 (no-duplicatesp-equal (strip-cars alst)))
  ;;            (acl2::<-ordered-p (strip-cars (delete-assoc-equal key alst))))
  ;;   :hints (("Goal"
  ;;            :do-not-induct t
  ;;            :use ((:instance <-ordered-p-after-remove-equal
  ;;                             (val key)
  ;;                             (lst (strip-cars alst))))
  ;;            :in-theory (e/d () (<-ordered-p-after-remove-equal)))))

  ;; (defthm nat-listp-of-strip-cars-after-delete-assoc-equal
  ;;   (implies (nat-listp (strip-cars alst))
  ;;            (nat-listp (strip-cars (delete-assoc-equal key alst))))
  ;;   :hints (("Goal"
  ;;            :in-theory (e/d (nat-listp) ()))))


  ;; (local
  ;;  (defthm strip-cars-of-delete-assoc-equal-if-key-not-in-alist
  ;;    (implies (not (member-equal key (strip-cars alst)))
  ;;             (equal (strip-cars (delete-assoc-equal key alst))
  ;;                    (strip-cars alst)))))

  ;; (local
  ;;  (defthm <-ordered-p-after-delete-assoc-equal-2
  ;;    (implies (and (member-equal key (strip-cars alst))
  ;;                  (acl2::<-ordered-p (strip-cars alst)))
  ;;             (acl2::<-ordered-p (strip-cars (delete-assoc-equal key alst))))
  ;;    :hints (("Goal" :in-theory (e/d (acl2::<-ordered-p) ())))))

  ;; (defthm <-ordered-p-after-delete-assoc-equal
  ;;   (implies (and (acl2::<-ordered-p (strip-cars alst))
  ;;                 (nat-listp (strip-cars alst)))
  ;;            (acl2::<-ordered-p (strip-cars (delete-assoc-equal key alst))))
  ;;   :hints (("Goal"
  ;;            :do-not-induct t
  ;;            :cases ((member-equal key (strip-cars alst)))
  ;;            :in-theory (e/d (acl2::<-ordered-p) ())))
  ;;   :otf-flg t)

  ;; (local
  ;;  (defthmd first-element-of-ordered-list-is-smaller-than-any-other
  ;;    (implies (and (acl2::<-ordered-p lst)
  ;;                  (member-equal e (cdr lst)))
  ;;             (<= (car lst) e))
  ;;    :hints (("Goal" :in-theory (e/d (acl2::<-ordered-p nat-listp) ())))
  ;;    :rule-classes :linear))

  ;; (defthmd car-of-all-keys-is-car-of-rassoc-equal
  ;;   (equal (car (all-keys val alst))
  ;;          (car (rassoc-equal val alst))))

  ;; (defthm all-keys-returns-an-alistp-sorted-by-keys
  ;;   (implies (acl2::<-ordered-p (strip-cars alst))
  ;;            (acl2::<-ordered-p (all-keys val alst)))
  ;;   :hints (("Goal" :in-theory (e/d (acl2::<-ordered-p
  ;;                                     car-of-all-keys-is-car-of-rassoc-equal)
  ;;                                    ()))))
  )

(define candidates-with-min-votes ((count-alst count-alistp))
  :short "Returns a list of candidates, if any, which received the
  minimum number of votes"
  :returns (cids nat-listp :hyp :guard)
  (b* ((min-num-of-votes (min-nats (strip-cdrs count-alst))))
    (all-keys min-num-of-votes count-alst))

  ///

  (defret natp-car-of-candidates-with-min-votes
    (implies (and (count-alistp count-alst)
                  cids)
             (natp (car cids)))
    :rule-classes (:rewrite :type-prescription))

  (local
   (defthm all-keys-and-min-nats-lemma
     (implies (all-keys (min-nats (strip-cdrs (cdr count-alst)))
                        (cdr count-alst))
              (all-keys (min-nats (strip-cdrs (cdr count-alst)))
                        count-alst))
     :hints (("goal" :in-theory (e/d (all-keys min-nats) nil)))))

  (defthm candidates-with-min-votes-is-non-empty
    (implies (and (count-alistp count-alst)
                  (consp count-alst))
             (and (candidates-with-min-votes count-alst)
                  (consp (candidates-with-min-votes count-alst))))
    :hints (("Goal" :in-theory (e/d (min-nats) ()))))

  (defthm candidates-with-min-votes-returns-a-subset-of-candidates
    (subsetp-equal (candidates-with-min-votes count-alst)
                   (strip-cars count-alst)))

  ;; (defthm candidates-with-min-votes-returns-a-sorted-cids-list
  ;;   ;; First prove all-keys-returns-an-alistp-sorted-by-keys.
  ;;   (implies (acl2::<-ordered-p (strip-cars count-alst))
  ;;            (acl2::<-ordered-p (candidates-with-min-votes count-alst))))
  )

(define candidate-with-least-nth-place-votes
  ((n    natp      "@('nth') preference under consideration")
   (cids nat-listp "Candidates relevant in this round of
                    tie-breaking (in ascending order)")
   (xs   irv-ballot-p))

  :short "Returns a candidate to be eliminated in step (2) of the IRV
  algorithm"
  :long "<p>This function encodes step (2) of the IRV algorithm. If it
  can find exactly one candidate among @('cids') with the fewest
  @('n')th-place votes, then it returns that candidate.  Otherwise, if
  it finds more than one candidate (i.e., if there is a tie), it goes
  on with its search among these candidates to pick one with the
  fewest @('n+1')th-place votes, and so on.  If the tie persists till
  we run out of candidates, then it returns the candidate with the
  smallest candidate ID.</p>

  <p>For example:</p>

  <code>
  (candidate-with-least-nth-place-votes 0 '(1 2 3 4)
                                        '((1 2 3 4) (2 3 1 4) (3 2 1 4)))
  </code>
  <p>Result: candidate 4 <br/>
     Reason: 4 has zero 0th-place votes.</p>

  <code>
  (candidate-with-least-nth-place-votes 0 '(1 2 3) 
                                        '((1 2 3) (1 3 2) (3 2 1) (3 2 1) (2 3 1)))
  </code>
  <p>Result: candidate 2 <br/>
     Reason: 2 has the fewest number of 0th-place votes.</p>

  <code>
  (candidate-with-least-nth-place-votes 0 '(1 2 3) '((1 2 3) (1 3 2) (3 2 1) (2 3 1)))
  </code>
  <p>Result: candidate 2 <br/>
     Reason: 2 and 3 are tied for fewest number of 0th, 1st, and 2nd
     place votes. So we pick 2, because it is lesser than 3.</p>

  <p>Note that this function will not be called by @(see irv) on
  ballots where step (1) of the IRV algorithm applies, i.e., when
  there is a majority in the first-place votes.</p>"

  :prepwork
  ((local (in-theory (e/d (number-of-candidates acl2::maybe-natp) ())))

   (local
    (defthm len-=-1-of-nat-listp
      (implies (and (nat-listp l)
                    (equal (len l) 1))
               (natp (car l))))))

  :measure (nfix (- (number-of-candidates xs) (nfix n)))

  :returns (cid acl2::maybe-natp :hyp (and (natp n)
                                           (nat-listp cids)
                                           (irv-ballot-p xs)))

  (b* (((when (endp cids))
        ;; CIDs must not be empty in this function.
        nil)
       (n (lnfix n))
       ((unless (< n (number-of-candidates xs)))
        ;; When all candidates have been considered, then it means there was a
        ;; tie throughout the voter preferences.  In this case, the first
        ;; candidate in CIDs should be picked --- because CIDs is expected to
        ;; be in ascending order, this will be the candidate with the smallest
        ;; ID.
        (car cids))
       (count-alst (create-nth-choice-count-alist n cids xs))
       ((when (endp count-alst))
        ;; TODO: When will this happen?
        ;; If all the candidates in this round are irrelevant, then return the
        ;; candidate with the smallest ID from the previous round.
        (car cids))
       (candidates-with-min-votes (candidates-with-min-votes count-alst)))
    (if (equal (len candidates-with-min-votes) 1)
        (car candidates-with-min-votes)
      (candidate-with-least-nth-place-votes
       (1+ n) candidates-with-min-votes xs)))

  ///

  (defthm candidates-with-min-votes-is-a-subset-of-cids
    (subsetp-equal
     (candidates-with-min-votes
      (create-nth-choice-count-alist n cids xs))
     cids)
    :hints
    (("Goal"
      :use
      ((:instance candidates-with-min-votes-returns-a-subset-of-candidates
                  (count-alst (create-nth-choice-count-alist n cids xs))))
      :in-theory
      (e/d ()
           (candidates-with-min-votes-returns-a-subset-of-candidates)))))

  (local
   (defthm subsetp-and-memberp-when-len-of-list==1
     (implies
      (and (equal (len candidate-lst) 1)
           (subsetp-equal candidate-lst cids))
      (member-equal (car candidate-lst) cids))))

  (defthm candidate-with-least-nth-place-votes-is-in-cids
    (b* ((cid (candidate-with-least-nth-place-votes n cids xs)))
      (implies cid (member-equal cid cids))))

  (defthm candidate-with-least-nth-place-votes-returns-a-natp
    (implies
     (and (nat-listp cids)
          (consp cids)
          (irv-ballot-p xs))
     (natp (candidate-with-least-nth-place-votes n cids xs)))
    :hints (("Goal" :in-theory (e/d (number-of-candidates) ())))
    :rule-classes (:rewrite :type-prescription)))

(define eliminate-candidate ((id natp "Candidate ID")
                             (xs irv-ballot-p))
  :short "Eliminate candidate @('id') from every voter's preference
  list in @('xs')"

  (if (endp xs)
      nil
    (b* ((one (car xs))
         (rest (cdr xs))
         (new-one (remove-equal id one))
         (new-rest (eliminate-candidate id rest)))
      (if (endp new-one)
          ;; This voter's preferences exhausted!
          new-rest
        (cons new-one new-rest))))

  ///

  (defthm no-duplicatesp-equal-of-remove-equal
    (implies (no-duplicatesp-equal x)
             (no-duplicatesp-equal (remove-equal id x))))

  (defthm nat-listp-after-remove-equal
    (implies (nat-listp x)
             (nat-listp (remove-equal val x)))
    :hints (("Goal" :in-theory (e/d (nat-listp) ()))))

  (defthm irv-ballot-p-of-eliminate-candidate
    (implies (irv-ballot-p xs)
             (b* ((new-xs (eliminate-candidate id xs)))
               (irv-ballot-p new-xs))))

  (defthm eliminate-candidate-returns-a-subset-of-candidates
    (subsetp-equal (candidate-ids (eliminate-candidate id xs))
                   (candidate-ids xs))
    :hints (("Goal" :in-theory (e/d (candidate-ids) ()))))

  (local
   (defthm remove-equal-when-not-a-member
     (implies (and (true-listp xs)
                   (not (member-equal id xs)))
              (equal (remove-equal id xs) xs))))

  (defthm eliminate-candidate-removes-no-candidate-when-cid-not-in-candidates
    (implies (and (irv-ballot-p xs)
                  (not (member-equal id (candidate-ids xs))))
             (equal (eliminate-candidate id xs) xs))
    :hints (("Goal" :in-theory (e/d (candidate-ids) ()))))

  (defthm eliminate-candidate-does-remove-a-candidate
    (implies (and (irv-ballot-p xs) (natp id))
             (equal (member-equal id (candidate-ids (eliminate-candidate id xs)))
                    nil))
    :hints (("Goal" :in-theory (e/d (candidate-ids) ()))))

  (defthm eliminate-candidate-removes-only-the-requested-candidate
    (implies (not (equal c1 c2))
             (iff (member-equal c2 (candidate-ids (eliminate-candidate c1 xs)))
                  (member-equal c2 (candidate-ids xs))))
    :hints (("Goal" :in-theory (e/d (candidate-ids) ()))))

  (local
   (defthm member-equal-and-len-helper-1
     (implies (and (equal (len flattened-original-xs) 0)
                   (not (consp flattened-new-xs))
                   (member-equal id flattened-original-xs)
                   (true-listp flattened-original-xs))
              (not (natp id)))))

  (local
   (defthm member-of-nat-listp-is-a-natp
     (implies (and (member-equal id lst)
                   (nat-listp lst))
              (natp id))
     :hints (("Goal" :in-theory (e/d (nat-listp) ())))))

  (local
   (defthm remove-equal-no-duplicatesp-equal-and-len-lemma
     (implies (and (no-duplicatesp-equal old)
                   (member-equal e old))
              (equal (len (remove-equal e old))
                     (+ -1 (len old))))
     :hints (("Goal" :in-theory (e/d (remove-equal
                                       no-duplicatesp-equal
                                       len)
                                      ())))))

  (local
   (defthm remove-duplicates-equal-remove-equal-and-len-lemma
     (implies (and (not (member-equal id y)) (member-equal id x))
              (equal (len (remove-duplicates-equal (append (remove-equal id x) y)))
                     (+ -1 (len (remove-duplicates-equal (append x y))))))
     :hints (("Goal" :in-theory (e/d (remove-equal
                                       remove-duplicates-equal
                                       len)
                                      ())))))


  (local
   (defun proper-subset-ind-hint (sub super)
     (if (endp sub)
         super
       (proper-subset-ind-hint
        (cdr sub)
        (remove-equal (car sub) super)))))

  (local
   (defthmd len-of-proper-subset-is-less-than-its-superset-when-no-duplicates
     (implies (and (member-equal id flattened-old-xs)
                   (not (member-equal id flattened-new-xs))
                   (subsetp-equal flattened-new-xs flattened-old-xs)
                   (true-listp flattened-old-xs)
                   (no-duplicatesp-equal flattened-old-xs)
                   (no-duplicatesp-equal flattened-new-xs)
                   (natp id))
              (< (len flattened-new-xs) (len flattened-old-xs)))
     :hints (("Goal"
              :induct (proper-subset-ind-hint
                       flattened-new-xs
                       flattened-old-xs)
              :in-theory (e/d (len subsetp-equal)
                               ((:induction member-equal)
                                (:induction no-duplicatesp-equal)
                                (:induction true-listp)
                                (:induction subsetp-equal)))))))

  (local
   (defthm eliminate-candidate-reduces-the-number-of-candidates-helper-1
     (and
      (implies
       (and
        (<
         (len
          (remove-duplicates-equal (acl2::flatten (eliminate-candidate id xs))))
         (len (remove-duplicates-equal (acl2::flatten xs))))
        (nat-listp (car xs))
        (consp (car xs))
        (no-duplicatesp-equal (car xs))
        (not (member-equal id
                           (candidate-ids (eliminate-candidate id xs))))
        (irv-ballot-p xs)
        (member-equal id (candidate-ids xs)))
       (< (number-of-candidates (eliminate-candidate id xs))
          (number-of-candidates xs)))
      (implies
       (and (member-equal id
                          (acl2::flatten (eliminate-candidate id xs)))
            (nat-listp (car xs))
            (consp (car xs))
            (no-duplicatesp-equal (car xs))
            (not (member-equal id
                               (candidate-ids (eliminate-candidate id xs))))
            (irv-ballot-p xs)
            (member-equal id (candidate-ids xs)))
       (< (number-of-candidates (eliminate-candidate id xs))
          (number-of-candidates xs)))
      (implies
       (and (not (member-equal id (acl2::flatten xs)))
            (nat-listp (car xs))
            (consp (car xs))
            (no-duplicatesp-equal (car xs))
            (not (member-equal id
                               (candidate-ids (eliminate-candidate id xs))))
            (irv-ballot-p xs)
            (member-equal id (candidate-ids xs)))
       (< (number-of-candidates (eliminate-candidate id xs))
          (number-of-candidates xs))))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d (number-of-candidates candidate-ids) ())))))

  (local
   (defthm eliminate-candidate-reduces-the-number-of-candidates-helper-2
     (implies
      (and (not (subsetp-equal (acl2::flatten (eliminate-candidate id xs))
                               (acl2::flatten xs)))
           (nat-listp (car xs))
           (consp (car xs))
           (no-duplicatesp-equal (car xs))
           (not (member-equal id
                              (candidate-ids (eliminate-candidate id xs))))
           (irv-ballot-p xs)
           (member-equal id (candidate-ids xs)))
      (< (number-of-candidates (eliminate-candidate id xs))
         (number-of-candidates xs)))
     :hints (("Goal" :do-not-induct t
              :use ((:instance eliminate-candidate-returns-a-subset-of-candidates))
              :in-theory (e/d (number-of-candidates candidate-ids)
                               (eliminate-candidate-returns-a-subset-of-candidates))))))

  (defthm eliminate-candidate-reduces-the-number-of-candidates
    (implies (and (irv-ballot-p xs)
                  (member-equal id (candidate-ids xs)))
             (< (number-of-candidates (eliminate-candidate id xs))
                (number-of-candidates xs)))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance len-of-proper-subset-is-less-than-its-superset-when-no-duplicates
                       (flattened-old-xs
                        (remove-duplicates-equal (acl2::flatten xs)))
                       (flattened-new-xs
                        (remove-duplicates-equal
                         (acl2::flatten (eliminate-candidate id xs)))))
            (:instance eliminate-candidate-does-remove-a-candidate))
      :in-theory (e/d ()
                      (eliminate-candidate-does-remove-a-candidate))))
    :rule-classes :linear)

  (defthm if-eliminate-candidate-reduced-the-number-of-candidates-then-id-was-a-candidate
    (implies (and (irv-ballot-p xs)
                  (< (number-of-candidates (eliminate-candidate id xs))
                     (number-of-candidates xs)))
             (member-equal id (candidate-ids xs)))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance len-of-proper-subset-is-less-than-its-superset-when-no-duplicates
                       (flattened-old-xs
                        (remove-duplicates-equal (acl2::flatten xs)))
                       (flattened-new-xs
                        (remove-duplicates-equal
                         (acl2::flatten (eliminate-candidate id xs)))))
            (:instance eliminate-candidate-does-remove-a-candidate))
      :in-theory (e/d ()
                      (eliminate-candidate-does-remove-a-candidate)))))

  (defthm remove-equal-and-append
    (equal (remove-equal id (append x y))
           (append (remove-equal id x)
                   (remove-equal id y))))

  (local
   (defthm candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids-helper
     (equal (acl2::flatten (eliminate-candidate id xs))
            (remove-equal id (acl2::flatten xs)))
     :hints (("Goal" :in-theory (e/d (acl2::flatten)
                                      ())))))

  (defthm remove-equal-of-<-insert-same-element
    (equal (remove-equal e (acl2::<-insert e lst))
           (remove-equal e lst))
    :hints (("Goal" :in-theory (e/d (acl2::<-insert)
                                     ()))))

  (defthm remove-equal-of-<-insert-different-element
    (implies (and (not (equal e1 e2))
                  (acl2::<-ordered-p lst))
             (equal (remove-equal e1 (acl2::<-insert e2 lst))
                    (acl2::<-insert e2 (remove-equal e1 lst))))
    :hints (("Goal" :in-theory (e/d (acl2::<-insert
                                      acl2::<-ordered-p)
                                     ()))))

  (defthm remove-equal-and-<-insertsort-commute
    (equal
     (acl2::<-insertsort (remove-equal id x))
     (remove-equal id (acl2::<-insertsort x)))
    :hints (("Goal" :in-theory (e/d (acl2::<-insertsort
                                      acl2::<-insert
                                      acl2::<-ordered-p)
                                     ()))))

  (defthm candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids
    (equal (candidate-ids (eliminate-candidate id xs))
           (remove-equal id (candidate-ids xs)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (candidate-ids)
                              ()))))

  (defthm eliminate-candidate-reduces-the-number-of-candidates-by-one
    (implies (and (irv-ballot-p xs)
                  (member-equal id (candidate-ids xs)))
             (equal (number-of-candidates (eliminate-candidate id xs))
                    (+ -1 (number-of-candidates xs))))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (e/d (number-of-candidates)
                       ()))))

  (defthm consp-of-eliminate-candidate
    (implies (and (irv-ballot-p xs)
                  (< 1 (number-of-candidates xs)))
             (consp (eliminate-candidate id xs)))
    :hints
    (("Goal"
      :use ((:instance eliminate-candidate-reduces-the-number-of-candidates-by-one))
      :in-theory
      (e/d ()
           (eliminate-candidate-reduces-the-number-of-candidates-by-one))))
    :rule-classes (:rewrite :type-prescription)))

(define irv ((xs irv-ballot-p))

  ;; (trace$ first-choice-of-majority-p)
  ;; (trace$ candidate-with-least-nth-place-votes)

  ;; (irv '((1 2 3) (3 1 2) (3 2 1) (3 2 1))) ;; 3 wins (majority)
  ;; (irv '((1 2 3) (3 1 2) (3 2 1) (2 3 1))) ;; 2 wins
  ;; (irv '((1 2 3) (1 3 2) (3 2 1) (2 3 1))) ;; 1 wins (tie-breaks in all rounds)
  ;; (irv '((1 2 3 4) (1 3 2 4) (3 2 1 4) (2 3 1 4)))

  :measure (number-of-candidates xs)

  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (e/d () (irv-ballot-p))))

  :prepwork

  ((defthm nat-listp-of-flatten-of-irv-ballot
     (implies (irv-ballot-p xs)
              (nat-listp (acl2::flatten xs)))
     :hints (("Goal" :in-theory (e/d (nat-listp) ()))))

   (defthm irv-termination-helper-lemma
     (implies
      (and
       (irv-ballot-p xs)
       (consp xs)
       (not (natp (first-choice-of-majority-p (candidate-ids xs)
                                              xs)))
       ;; (not (natp (pick-candidate-among-those-with-same-number-of-first-place-votes
       ;;             (candidate-ids xs)
       ;;             xs)))
       )
      (< (number-of-candidates
          (eliminate-candidate
           (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                 xs)
           xs))
         (number-of-candidates xs)))
     :hints (("Goal"
              :use
              ((:instance candidate-with-least-nth-place-votes-is-in-cids
                          (n 0)
                          (cids (candidate-ids xs))
                          (xs xs)))
              :in-theory
              (e/d ()
                   (candidate-with-least-nth-place-votes-is-in-cids))))
     :rule-classes :linear)

   ;; Lemmas for the guard proof:

   (local
    (defthm candidate-with-least-nth-place-votes-when-not-natp
      (implies (and (not (natp (candidate-with-least-nth-place-votes n cids xs)))
                    (irv-ballot-p xs)
                    (nat-listp cids)
                    (natp n))
               (equal (candidate-with-least-nth-place-votes n cids xs) nil))
      :hints (("Goal"
               :use ((:instance maybe-natp-of-candidate-with-least-nth-place-votes))
               :in-theory (e/d (acl2::maybe-natp)
                               (maybe-natp-of-candidate-with-least-nth-place-votes))))))

   (encapsulate
     ()

     (defthm len-of-consp-not-zero
       (implies (consp x)
                (not (equal (len x) 0))))

     (local
      (defthm len-of-0th-choice-list-is-equal-to-the-number-of-voters
        (implies (irv-ballot-p xs)
                 (equal (len (make-nth-choice-list 0 xs))
                        (number-of-voters xs)))
        :hints (("Goal" :in-theory
                 (e/d (make-nth-choice-list
                        number-of-candidates
                        number-of-voters)
                       ())))))

     (local
      (defthm duplicity-upper-bound
        (<= (acl2::duplicity e lst) (len lst))
        :rule-classes :linear))

     (local
      (defthm duplicity-for-list-elements-equal
        (iff (list-elements-equal e lst)
             (equal (acl2::duplicity e lst)
                    (len lst)))
        :hints (("Goal" :in-theory (e/d (list-elements-equal
                                          acl2::duplicity
                                          len)
                                         ())))))

     (local
      (defthm create-count-alist-of-list-elements-equal
        (implies (and (list-elements-equal e lst)
                      (member-equal e cids))
                 (equal
                  (cdr (assoc-equal e (create-count-alist cids lst)))
                  ;; (acl2::duplicity e lst) --- true, irrespective of
                  ;; list-elements-equal.
                  (len lst)))
        :hints (("Goal" :in-theory
                 (e/d (list-elements-equal
                        create-count-alist)
                       ())))))

     (local
      (defthmd max-number-of-votes-in-a-count-alist-means-same-choice-list
        (implies
         (and
          (equal (cdr (assoc-equal e (create-count-alist cids lst)))
                 (len lst))
          (member-equal e cids))
         (list-elements-equal e lst))
        :hints (("Goal"
                 :in-theory (e/d (create-count-alist
                                   list-elements-equal
                                   len)
                                  ((:induction max-nats)
                                   (:induction member-equal)
                                   (:induction true-listp)))))))

     (local
      (defthm uniqueness-of-duplicity-element-lemma
        (implies (and
                  (equal (acl2::duplicity e1 lst)
                         (len lst))
                  (consp lst))
                 (iff (equal (acl2::duplicity e2 lst)
                             (len lst))
                      (equal e1 e2)))
        :hints (("Goal" :in-theory (e/d (acl2::duplicity
                                          len)
                                         ())))))

     (local
      (defthm zero-len-cids-and-create-count-alist
        (implies (equal (len cids) 0)
                 (equal (create-count-alist cids lst) nil))
        :hints (("Goal" :in-theory (e/d (create-count-alist
                                          len)
                                         ())))))


     (local
      (defthmd same-choice-list-means-max-nats-is-len-of-list
        (implies
         (and (list-elements-equal e lst)
              (member-equal e cids)
              (equal (len cids) 1))
         (equal (max-nats (strip-cdrs (create-count-alist cids lst)))
                (len lst)))
        :hints (("Goal"
                 :in-theory (e/d (create-count-alist
                                   list-elements-equal
                                   len
                                   max-nats)
                                  ())))))

     (local
      (defthm exactly-one-candidate-gets-all-the-votes-helper
        (implies
         (and
          (equal (cdr (assoc-equal e (create-count-alist cids lst)))
                 (len lst))
          (member-equal e cids)
          (equal (len cids) 1))
         (equal (max-nats (strip-cdrs (create-count-alist cids lst)))
                (len lst)))
        :hints (("Goal"
                 :use
                 ((:instance max-number-of-votes-in-a-count-alist-means-same-choice-list)
                  (:instance same-choice-list-means-max-nats-is-len-of-list))))))

     (local
      (defthm exactly-one-candidate-gets-all-the-votes-helper-1
        (implies
         (and
          (equal
           (cdr
            (assoc-equal
             (car (car xs))
             (create-count-alist
              (acl2::<-insertsort (remove-duplicates-equal (acl2::flatten xs)))
              (make-nth-choice-list 0 xs))))
           (number-of-voters xs))
          (irv-ballot-p xs)
          (equal (number-of-candidates xs) 1))
         (equal
          (max-nats
           (strip-cdrs
            (create-count-alist
             (acl2::<-insertsort (remove-duplicates-equal (acl2::flatten xs)))
             (make-nth-choice-list 0 xs))))
          (number-of-voters xs)))
        :hints (("Goal"
                 :in-theory
                 (e/d
                  (create-nth-choice-count-alist
                   candidate-ids
                   number-of-voters
                   number-of-candidates)
                  (create-count-alist-of-list-elements-equal))
                 :use
                 ((:instance max-number-of-votes-in-a-count-alist-means-same-choice-list
                             (e (car (car xs)))
                             (cids (candidate-ids xs))
                             (lst (make-nth-choice-list 0 xs)))
                  (:instance same-choice-list-means-max-nats-is-len-of-list
                             (e (car (car xs)))
                             (cids (candidate-ids xs))
                             (lst (make-nth-choice-list 0 xs))))))))

     (local
      (defthm zero-len-of-remove-duplicates-equal-lemma
        (implies (equal (len (remove-duplicates-equal x)) 0)
                 (not (consp x)))
        :hints (("Goal" :in-theory (e/d (len remove-duplicates-equal)
                                         ())))))

     (defthmd list-elements-equal-under-remove-duplicates-equal
       (iff (list-elements-equal e x)
            (list-elements-equal e (remove-duplicates-equal x)))
       :hints (("Goal" :in-theory (e/d (list-elements-equal) ()))))

     (local
      (defthmd list-elements-equal-of-list-of-length=1
        (implies
         (and
          (equal (len x) 1)
          (member-equal e x))
         (list-elements-equal e x))
        :hints (("Goal" :in-theory (e/d (list-elements-equal
                                          len)
                                         (duplicity-for-list-elements-equal))))))

     (local
      (defthmd list-elements-equal-of-list-of-unique-elements-length=1
        (implies
         (and
          (equal (len (remove-duplicates-equal x)) 1)
          (member-equal e x))
         (list-elements-equal e x))
        :hints (("Goal"
                 :do-not-induct t
                 :use ((:instance list-elements-equal-of-list-of-length=1
                                  (x (remove-duplicates-equal x)))
                       (:instance list-elements-equal-under-remove-duplicates-equal))
                 :in-theory (e/d ()
                                  (list-elements-equal
                                   len
                                   duplicity-for-list-elements-equal))))))

     (local
      (defthmd each-voter-has-exactly-one-preference
        (implies (and (irv-ballot-p xs)
                      (equal (len (remove-duplicates-equal (acl2::flatten xs))) 1))
                 (equal (car xs)
                        (list (car (car xs)))))
        :hints (("Goal" :in-theory (e/d (acl2::flatten
                                          make-nth-choice-list)
                                         ())))))

     (defthmd make-nth-choice-list-and-flatten-for-1-candidate-helper-1
       (implies (and (nat-listp (car xs))
                     (no-duplicatesp-equal (car xs))
                     (equal (make-nth-choice-list 0 (cdr xs))
                            (acl2::flatten (cdr xs)))
                     (irv-ballot-p (cdr xs))
                     (equal (len (remove-duplicates-equal (acl2::flatten xs)))
                            1))
                (equal (make-nth-choice-list 0 xs)
                       (acl2::flatten xs)))
       :hints (("Goal"
                :use ((:instance each-voter-has-exactly-one-preference))
                :do-not-induct t
                :expand ((make-nth-choice-list 0 xs)
                         (acl2::flatten xs)))))

     (local
      (defthmd one-voter-has-exactly-one-preference
        (implies
         (and (equal (len (remove-duplicates-equal (append x y))) 1)
              (not (equal (len (remove-duplicates-equal y)) 1)))
         (not (consp y)))
        :hints (("Goal" :in-theory (e/d (len) ())))))

     (local
      (defthmd make-nth-choice-list-and-flatten-for-1-candidate-helper-2
        (implies
         (and (irv-ballot-p xs)
              (equal (len (remove-duplicates-equal (acl2::flatten xs)))
                     1)
              (not (equal
                    (len (remove-duplicates-equal (acl2::flatten (cdr xs))))
                    1)))
         (equal (cdr xs) nil))
        :hints (("Goal"
                 :in-theory (e/d (acl2::flatten) ()))
                (if (and (consp (car id))
                         (< 1 (len (car id))))
                    '(:use ((:instance one-voter-has-exactly-one-preference
                                       (x (car xs))
                                       (y (acl2::flatten (cdr xs))))))
                  nil))))

     (local
      (defthmd make-nth-choice-list-and-flatten-for-1-candidate
        (implies (and (irv-ballot-p xs)
                      (equal (len (remove-duplicates-equal (acl2::flatten xs))) 1))
                 (equal (make-nth-choice-list 0 xs)
                        (acl2::flatten xs)))
        :hints (("Goal"
                 :in-theory (e/d (make-nth-choice-list-and-flatten-for-1-candidate-helper-1
                                   make-nth-choice-list-and-flatten-for-1-candidate-helper-2)
                                  ())))))

     (local
      (defthmd list-elements-equal-of-0th-choice-list-for-exactly-1-candidate-helper
        (implies
         (and (irv-ballot-p xs)
              (member-equal e (acl2::flatten xs))
              (equal (len (remove-duplicates-equal (acl2::flatten xs))) 1))
         (list-elements-equal e (make-nth-choice-list 0 xs)))
        :hints (("Goal"
                 :use ((:instance list-elements-equal-of-list-of-unique-elements-length=1
                                  (x (acl2::flatten xs))))
                 :in-theory (e/d (make-nth-choice-list-and-flatten-for-1-candidate)
                                  (list-elements-equal
                                   len
                                   acl2::flatten
                                   duplicity-for-list-elements-equal))))))

     (local
      (defthmd list-elements-equal-of-0th-choice-list-for-exactly-1-candidate
        (implies
         (and (irv-ballot-p xs)
              (equal (number-of-candidates xs) 1))
         (list-elements-equal (car (car xs)) (make-nth-choice-list 0 xs)))
        :hints
        (("Goal"
          :in-theory (e/d (number-of-candidates
                            candidate-ids)
                           ())
          :use
          ((:instance list-elements-equal-of-0th-choice-list-for-exactly-1-candidate-helper
                      (e (car (car xs)))))))))

     (defthm exactly-one-candidate-gets-all-the-votes
       (implies
        (and (irv-ballot-p xs)
             (equal (number-of-candidates xs) 1))
        (equal (max-nats (strip-cdrs
                          (create-nth-choice-count-alist 0 (candidate-ids xs) xs)))
               (number-of-voters xs)))
       :hints
       (("Goal"
         :do-not '(preprocess)
         :do-not-induct t
         :use
         ((:instance
           create-count-alist-of-list-elements-equal
           (e (caar xs))
           (cids (candidate-ids xs))
           (lst (make-nth-choice-list 0 xs))))
         :in-theory
         (e/d
          (create-nth-choice-count-alist
           candidate-ids
           list-elements-equal-of-0th-choice-list-for-exactly-1-candidate)
          (create-count-alist-of-list-elements-equal
           duplicity-for-list-elements-equal)))))

     (defthm exactly-one-candidate-gets-the-majority-votes
       (implies
        (and (irv-ballot-p xs)
             (consp xs)
             (<= (number-of-candidates xs) 1))
        (< (majority (number-of-voters xs))
           (max-nats (strip-cdrs
                      (create-nth-choice-count-alist
                       0 (candidate-ids xs) xs)))))
       :hints
       (("Goal"
         :use ((:instance exactly-one-candidate-gets-all-the-votes)
               (:instance majority-is-less-than-total
                          (n (number-of-voters xs))))
         :in-theory
         (e/d (posp
                number-of-voters
                number-of-candidates)
               (exactly-one-candidate-gets-all-the-votes
                majority-is-less-than-total))))))

   (local
    (defthm natp-of-rassoc-equal-max-nats-of-strip-cdrs-count-alistp
      (implies (and (count-alistp alst) (consp alst))
               (natp (car (rassoc-equal (max-nats (strip-cdrs alst)) alst))))
      :hints (("Goal" :in-theory (e/d (max-nats
                                        nat-listp)
                                       ())))))

   (defthm first-choice-of-majority-p-empty-implies-more-than-one-candidate
     (b* ((cids (candidate-ids xs))
          (winner-by-majority (first-choice-of-majority-p cids xs)))
       (implies (and
                 ;; The following two hypotheses about xs just imply
                 ;; that the election has 1 or more contesting
                 ;; candidates.  We want to prove that the election has
                 ;; strictly more than 1 candidate contesting when no
                 ;; one wins by a majority.
                 (irv-ballot-p xs)
                 (consp xs)
                 (not (natp winner-by-majority)))
                (< 1 (number-of-candidates xs))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (first-choice-of-majority-p)
                              ())))
     :rule-classes :linear))

  (if (mbt (irv-ballot-p xs))

      (if (endp xs)
          nil
        (b* ((cids (candidate-ids xs)) ;; sorted CIDs.
             (step-1-candidate (first-choice-of-majority-p cids xs))
             ((when (natp step-1-candidate))
              step-1-candidate)
             ;; (step-2-candidate
             ;;  (pick-candidate-among-those-with-same-number-of-first-place-votes
             ;;   cids xs))
             ;; ((when (natp step-2-candidate))
             ;;  step-2-candidate)
             (step-2-candidate-to-remove
              (candidate-with-least-nth-place-votes
               0    ;; First preference
               cids ;; List of relevant candidates
               xs))
             ;; ((unless (or (natp step-n-candidate-to-remove)
             ;;              (member-equal step-n-candidate-to-remove
             ;;                            (acl2::flatten xs))))
             ;;  ;; We have proved that nil can't be returned here.
             ;;  nil)
             (new-xs (eliminate-candidate step-2-candidate-to-remove xs)))
          (irv new-xs)))

    nil)

  ///
  (local
   (defthm irv-ballot-p-consp-of-flatten
     (implies (and (irv-ballot-p xs) (consp xs))
              (consp (acl2::flatten xs)))
     :hints (("Goal" :in-theory (e/d (acl2::flatten) ())))))


  (defthm non-empty-ballot-returns-one-winner
    (implies (and (irv-ballot-p xs) (consp xs))
             (natp (irv xs)))
    :hints (("Goal" :in-theory (e/d () ())))
    :rule-classes (:rewrite :type-prescription)))

;; ----------------------------------------------------------------------
