;; Original Authors: Shilpi Goel      <shigoel@gmail.com>
;;                   Mayank Manjrekar <mankmonjre@gmail.com>

(in-package "IRV")

(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs"  :dir :system)
(include-book "std/lists/sets"  :dir :system)
(include-book "std/lists/flatten"  :dir :system)
(include-book "std/lists/duplicity"  :dir :system)
(include-book "std/lists/nth"  :dir :system)
(include-book "defsort/defsort" :dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))

;; The winner will be chosen as follows.

;;   (1) If a candidate is the first choice of more than half of the voters,
;;       then it wins.  Otherwise:

;;   (2) If every remaining candidate has the same number of first-place
;;       votes, pick the one with the smallest ID.  Otherwise:

;;   (3) Adjust each ballot by eliminating the candidate with the
;;       fewest first-place votes.  If there is a tie for the fewest
;;       first-place votes, then delete the candidate with the least
;;       second-place votes, etc.  If the tie persists, then delete
;;       the candidate with the smallest ID.

;;   (4) Go to (1).

;; ----------------------------------------------------------------------
;; Recognizer for a well-formed IRV ballot
;; ----------------------------------------------------------------------

(define irv-ballot-p-core ((cids nat-listp "List of candidate IDs currently in the election")
                           xs)
  :guard (consp cids)
  :short "Core function for recognizing a well-formed IRV ballot"
  :enabled t
  (if (consp xs)
      (b* ((one (car xs))
           (rest (cdr xs)))
        (and
         ;; cids is the list of candidate IDs currently in the
         ;; election at --- there must be at least one candidate in
         ;; the election at this point.  Each voter must rank *all*
         ;; the candidates. The preferences of a voter must satisfy
         ;; the following constraints: a voter should not list a
         ;; candidate more than once, and the preferences should be
         ;; some permutation of the cids.
         (nat-listp one)
         (subsetp-equal one cids)
         (subsetp-equal cids one)
         (no-duplicatesp-equal one)
         (irv-ballot-p-core cids rest)))
    (equal xs nil))

  ///

  (defthm irv-ballot-p-core-cdr
    (implies (irv-ballot-p-core cids xs)
             (irv-ballot-p-core cids (cdr xs))))

  (defthm irv-ballot-p-core-equiv
    (implies (and (nat-listp cids1)
                  (consp cids1)
                  (no-duplicatesp-equal cids1)
                  (nat-listp cids2)
                  (no-duplicatesp-equal cids2)
                  (subsetp-equal cids2 cids1)
                  (subsetp-equal cids1 cids2)
                  (irv-ballot-p-core cids1 xs))
             (irv-ballot-p-core cids2 xs))))

(define irv-ballot-p (xs)
  :enabled t
  :short "The recognizer for a well-formed IRV ballot structure"
  :long "<p>A candidate is identified by his ID, which is a natural
  number.  Each element of @('xs') must be a list of natural numbers,
  which represents the preferences of one voter. The position of the
  candidate ID in this list denotes his rank.  For example, if a
  voter's preferences are @('(100 0 5)'), then candidates 100, 0, and
  5 are his first, second, and third preferences, respectively.</p>"
  (if (consp xs)
      (b* ((one (car xs)))
        (and (nat-listp one)
             (consp one)
             (no-duplicatesp-equal one)
             (irv-ballot-p-core one (cdr xs))))
    (equal xs nil))

  ///

  (defthm irv-ballot-p-implies-true-list-listp
    (implies (irv-ballot-p xs)
             (true-list-listp xs)))

  (defthm irv-ballot-p-cdr
    (implies (irv-ballot-p xs)
             (irv-ballot-p (cdr xs)))))

;; ----------------------------------------------------------------------
;; Implementation of the IRV algorithm
;; ----------------------------------------------------------------------

(define number-of-candidates ((xs irv-ballot-p))
  :returns (num natp :rule-classes :type-prescription)
  (len (car xs)))

(define number-of-voters ((xs irv-ballot-p))
  :returns (num natp :rule-classes :type-prescription)
  (len xs))

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

  (if (or (endp xs)
          (not (< n (number-of-candidates xs))))
      nil
    (cons (nth n (car xs)) ;; nth choice of the first voter
          (make-nth-choice-list n (cdr xs))))
  ///

  (defthm consp-of-make-nth-choice-list
    (implies (and (consp xs)
                  (natp n)
                  (< n (number-of-candidates xs))
                  (irv-ballot-p xs))
             (consp (make-nth-choice-list n xs))))

  (defthm consp-of-make-first-choice-occurrence-list
    (implies (and (consp xs)
                  (irv-ballot-p xs))
             (consp (make-nth-choice-list 0 xs)))))

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
             (alistp l))))

(define create-count-alist ((choice-lst nat-listp))
  :short "Given a choice list, maps each candidate ID to the number of
  votes they obtained"
  :returns (count-alst alistp)
  (if (endp choice-lst)
      nil
    (b* ((one (car choice-lst))
         (count (acl2::duplicity one choice-lst))
         (rest (remove-equal one choice-lst)))
      (cons (cons one count)
            (create-count-alist rest))))
  ///

  (defthm nat-listp-of-remove-equal
    (implies (nat-listp choice-lst)
             (nat-listp (remove-equal e choice-lst))))

  (defret count-alistp-of-create-count-alist
    (implies (nat-listp choice-lst)
             (count-alistp count-alst)))

  (defthm consp-of-create-count-alist
    (equal (consp (create-count-alist lst))
           (consp lst)))

  (defthm consp-of-car-of-create-count-alist
    (equal (consp (car (create-count-alist lst)))
           (consp lst)))

  (defthm consp-of-strip-cars-of-create-count-alist
    (equal (consp (strip-cars (create-count-alist lst)))
           (consp lst)))

  (defthm consp-of-strip-cdrs-of-create-count-alist
    (equal (consp (strip-cdrs (create-count-alist lst)))
           (consp lst)))

  (defthm nat-listp-of-strip-cars-of-create-count-alist
    (implies (nat-listp choice-lst)
             (nat-listp (strip-cars (create-count-alist choice-lst)))))

  (defthm nat-listp-of-strip-cdrs-of-create-count-alist
    (implies (nat-listp choice-lst)
             (nat-listp (strip-cdrs (create-count-alist choice-lst))))))

(define majority ((n natp "Number of voters"))
  :returns (maj natp
                :hyp :guard
                :rule-classes :type-prescription)
  :prepwork
  ((local (include-book "arithmetic-5/top" :dir :system)))
  (if (evenp n) (/ n 2) (/ (- n 1) 2)))

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
             (member-equal (max-nats x) x))))

(acl2::defsort :comparablep natp
               :compare< <
               :prefix <
               :comparable-listp nat-listp
               :true-listp t
               :weak nil)

(define first-choice-of-majority-p ((xs irv-ballot-p))
  :short "Returns the candidate, if any, who is the first choice of
  more than half of the voters"
  :long "<p>This function encodes step (1) of the IRV algorithm: if a
  candidate is the first choice of more than half of the voters, then
  it wins --- this function returns the ID of that candidate.  If no
  such candidate exists, this function returns @('nil').</p>"

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

  (if (endp xs)
      nil
    (b* ((n (number-of-voters xs))
         (majority (majority n))
         (choice-lst (acl2::<-sort (make-nth-choice-list 0 xs)))
         (count-alst (create-count-alist choice-lst))
         (max-votes  (max-nats (strip-cdrs count-alst))))
      (if (< majority max-votes)
          (car (rassoc-equal max-votes count-alst))
        nil))))

(define list-elements-equal (e
                             (x true-listp))
  :short "Returns @('t') if all elements of @('x') are equal to @('e')"
  :returns (elem-equal? booleanp :rule-classes :type-prescription)
  (if (endp x)
      t
    (and (equal (car x) e)
         (list-elements-equal e (cdr x)))))

(define pick-candidate-among-those-with-same-number-of-first-place-votes ((xs irv-ballot-p))
  :short "If every remaining candidate has the same number of
    first-place votes, pick the candidate with the smallest ID"
  :long "<p>This function encodes step (2) of the IRV algorithm. This
  function returns @('nil') if <b>all</b> the remaining candidates do
  not have the same number of first-place votes.</p>"

  :returns (candidate
            acl2::maybe-natp
            :hyp :guard
            :hints (("Goal" :in-theory (e/d (acl2::maybe-natp) ()))))

  :prepwork
  ((local
    (defthm natp-of-car-of-car-of-create-count-alist
      (implies (and (nat-listp lst)
                    (consp lst))
               (natp (car (car (create-count-alist lst)))))
      :hints (("Goal" :in-theory (e/d (create-count-alist) ()))))))

  (if (endp xs)
      nil
    (b* ((choice-lst (acl2::<-sort (make-nth-choice-list 0 xs)))
         (count-alst (create-count-alist choice-lst))
         (all-votes  (strip-cdrs count-alst))
         (all-votes-same? (list-elements-equal (car all-votes) all-votes)))
      (if all-votes-same?
          (car (car count-alst)) ;; Smallest candidate ID
        nil))))

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

(define rassocs ((n natp)
                 (count-alst count-alistp))
  :short "Returns a list of all the keys in @('count-alst') with the
  value @('n')"
  :prepwork
  ((defthm consp-of-rassoc-equal
     (implies (and (alistp alst)
                   (rassoc-equal n alst))
              (consp (rassoc-equal n alst))))

   (local
    (defthm natp-of-car-of-rassoc-equal-of-count-alist
      (implies (and (natp n)
                    (count-alistp count-alst)
                    (rassoc-equal n count-alst))
               (natp (car (rassoc-equal n count-alst))))))

   (defthm count-alistp-of-delete-assoc-equal
     (implies (count-alistp count-alst)
              (count-alistp (delete-assoc-equal i count-alst)))))
  :returns
  (cids nat-listp :hyp :guard)

  (b* ((candidate-one-info  (rassoc-equal n count-alst)))
    (if (or (endp count-alst)
            (equal candidate-one-info nil))
        nil
      (cons (car candidate-one-info)
            (rassocs n (delete-assoc-equal
                        (car candidate-one-info)
                        count-alst)))))

  ///

  (defthm rassoc-equal-returns-a-member-of-keys
    (implies (member-equal n (strip-cdrs alst))
             (member-equal (car (rassoc-equal n alst))
                           (strip-cars alst))))

  (defthm delete-assoc-equal-and-subset-equal
    (subsetp-equal (delete-assoc-equal n alst) alst))

  (defthm strip-cars-of-delete-assoc-equal-and-subset-equal
    (subsetp-equal (strip-cars (delete-assoc-equal n alst))
                   (strip-cars alst)))

  (defthm rassoc-equal-returns-nil-when-value-not-found-in-alist
    (implies (not (member-equal n (strip-cdrs alst)))
             (equal (rassoc-equal n alst) nil)))

  (defthmd rassocs-returns-nil-when-value-not-found-in-alist
    (implies (not (member-equal n (strip-cdrs alst)))
             (equal (rassocs n alst) nil)))

  (defthm rassoc-equal-is-non-empty-when-non-nil-value-found-in-alist
    (implies (and (member-equal n (strip-cdrs alst)) n)
             (rassoc-equal n alst)))

  (defthm rassocs-is-non-empty-when-non-nil-value-found-in-alist
    (implies (and (member-equal n (strip-cdrs alst)) n)
             (rassocs n alst)))

  (defthm nil-is-not-a-member-of-any-nat-listp
    (implies (nat-listp lst)
             (equal (member-equal nil lst) nil)))

  (defthmd rassocs-returns-a-subset-of-keys-helper
    (implies (member-equal n (strip-cdrs alst))
             (subsetp-equal (rassocs n alst)
                            (strip-cars alst))))

  (defthm rassocs-returns-a-subset-of-keys
    (subsetp-equal (rassocs n alst)
                   (strip-cars alst))
    :hints (("Goal"
             :cases ((not (member-equal n (strip-cdrs alst))))
             :in-theory (e/d (rassocs-returns-nil-when-value-not-found-in-alist
                              rassocs-returns-a-subset-of-keys-helper)
                             ())))))

(define candidates-with-min-votes ((count-alst count-alistp))
  :short "Returns a list of candidates, if any, which received the
  minimum number of votes"
  :returns (cids nat-listp :hyp :guard)
  (b* ((min-num-of-votes (min-nats (strip-cdrs count-alst))))
    (rassocs min-num-of-votes count-alst))

  ///

  (defret natp-car-of-candidates-with-min-votes
    (implies (and (count-alistp count-alst)
                  cids)
             (natp (car cids)))
    :rule-classes (:rewrite :type-prescription))

  (local
   (defthm rassocs-and-min-nats-lemma
     ;; TODO: Move strip-cdrs and cdr outside min-nats to get a nicer lemma.
     (implies (rassocs (min-nats (strip-cdrs (cdr count-alst)))
                       (cdr count-alst))
              (rassocs (min-nats (strip-cdrs (cdr count-alst)))
                       count-alst))
     :hints (("goal" :in-theory (e/d* (rassocs min-nats) nil)))))

  (defthm candidates-with-min-votes-is-non-empty
    (implies (and (count-alistp count-alst)
                  (consp count-alst))
             (candidates-with-min-votes count-alst))
    :hints (("Goal" :in-theory (e/d (min-nats) ()))))

  (defthm candidates-with-min-votes-returns-a-subset-of-candidates
    (subsetp-equal (candidates-with-min-votes count-alst)
                   (strip-cars count-alst))))

(define delete-all-pairs-but ((cids nat-listp)
                              (count-alst count-alistp))
  :short "Remove all pairs from @('count-alst') except those with keys
  in @('cids')"

  :returns (new-count-alst count-alistp :hyp (count-alistp count-alst))

  (if (endp count-alst)
      nil
    (if (member-equal (caar count-alst) cids)
        (cons (car count-alst) (delete-all-pairs-but cids (cdr count-alst)))
      (delete-all-pairs-but cids (cdr count-alst))))

  ///  

  (defthm delete-all-pairs-but-returns-a-subset-of-the-alist
    (subsetp-equal (delete-all-pairs-but cids count-alst)
                   count-alst))

  (defthm delete-all-pairs-but-returns-a-subset-of-the-cids
    (subsetp-equal (strip-cars (delete-all-pairs-but cids count-alst))
                   cids))

  ;; (defthm delete-all-pairs-but-returns-non-empty-alist
  ;;   (implies (and (consp cids)
  ;;                 (subsetp-equal cids (strip-cars count-alst))
  ;;                 (consp count-alst))
  ;;            (delete-all-pairs-but cids count-alst)))
  )

(define candidate-with-least-nth-place-votes
  ((n    natp      "@('nth') preference under consideration")
   (cids nat-listp "Candidates relevant in this round of
                    tie-breaking (in ascending order)")
   (xs   irv-ballot-p))

  :short "Returns a candidate to be eliminated in step (3) of the IRV
  algorithm"
  :long "<p>This function encodes step (3) of the IRV algorithm. If it
  can find exactly one candidate among @('cids') with the fewest
  @('n')th-place votes, then it returns that candidate.  Otherwise, if
  it finds more than one candidate (i.e., if there is a tie), it goes
  on with its search among these candidates to pick one with the
  fewest @('n+1')th-place votes, and so on.  If the tie persists till
  we run out of candidates, then it returns the candidate with the
  smallest candidate ID.</p>

  <p>For example:</p>

  <code>
  (candidate-with-least-nth-place-votes 0 '(1 2 3) '((1 2 3) (1 3 2) (3 2 1) (3 2 1) (2 3 1)))
  </code>
  <p>Result: candidate 2 <br/>
     Reason: 2 has the fewest number of 0th-place votes.</p>

  <code>
  (candidate-with-least-nth-place-votes 0 '(1 2 3) '((1 2 3) (1 3 2) (3 2 1) (2 3 1)))
  </code>
  <p>Result: candidate 3 <br/>
     Reason: 2 and 3 are tied for fewest number of 0th, 1st, and 2nd
     place votes. So we pick 2, because it is lesser than 3.</p>

  <p>Note that this function will not be called by @(see irv) on
  ballots where step (1) and (2) of the IRV algorithm apply, i.e.,
  when there is a majority or tie among candidates for the first-place
  votes.</p>"

  :prepwork
  ((local (in-theory (e/d (number-of-voters acl2::maybe-natp) ())))

   (local
    (defthm len-=-1-of-nat-listp
      (implies (and (nat-listp l)
                    (equal (len l) 1))
               (natp (car l))))))

  :measure (nfix (- (number-of-voters xs) (nfix n)))

  ;; TODO --- make this function return a natp instead?
  ;; Prove that this function returns a member of the initial cids.
  :returns (cid acl2::maybe-natp :hyp (and (natp n)
                                           (nat-listp cids)
                                           (irv-ballot-p xs)))

  (b* (((when (endp cids))
        ;; CIDs must not be empty in this function.
        nil)
       (n (lnfix n))
       ((when (<= (number-of-voters xs) n))
        ;; When no voter records are left, then it means there was a
        ;; tie throughout the voter preferences.  In this case, the
        ;; first candidate in CIDs should be picked --- because CIDs
        ;; is expected to be in ascending order, this will be the
        ;; candidate with the smallest ID.
        (car cids))
       (choice-lst (acl2::<-sort (make-nth-choice-list n xs)))
       (count-alst (create-count-alist choice-lst))
       (count-alst (delete-all-pairs-but cids count-alst))
       (candidates-with-min-votes (candidates-with-min-votes count-alst)))
    (if (equal (len candidates-with-min-votes) 1)
        (car candidates-with-min-votes)
      (candidate-with-least-nth-place-votes (1+ n) candidates-with-min-votes xs)))

  ///

  ;; TODO: Should follow from
  ;; candidates-with-min-votes-returns-a-subset-of-candidates and
  ;; delete-all-pairs-but-returns-a-subset-of-the-cids.

  ;; (defthm candidate-with-least-nth-place-votes-is-in-cids
  ;;   (b* ((cid (candidate-with-least-nth-place-votes n cids xs)))
  ;;     (implies (and (natp cid) (natp n))
  ;;              (member-equal cid cids))))
  )

(define eliminate-candidate ((id natp "Candidate ID")
                             (xs irv-ballot-p))
  :short "Eliminate candidate @('id') from every voter's preference
  list in @('xs')"

  (if (endp xs)
      nil
    (b* ((one (car xs))
         (new-one (remove-equal id one))
         ((when (endp new-one))
          ;; All candidates eliminated!
          nil)
         (rest (cdr xs))
         (new-rest (eliminate-candidate id rest)))
      (cons new-one new-rest)))

  ///

  (defthm no-duplicatesp-equal-of-remove-equal
    (implies (no-duplicatesp-equal x)
             (no-duplicatesp-equal (remove-equal id x))))

  (defthm irv-ballot-p-core-of-eliminate-candidate
    (implies (irv-ballot-p-core cids xs)
             (b* ((new-cids (remove-equal id cids))
                  (new-xs (eliminate-candidate id xs)))
               (irv-ballot-p-core new-cids new-xs))))

  (defthm irv-ballot-p-of-eliminate-candidate
    (implies (irv-ballot-p xs)
             (b* ((new-xs (eliminate-candidate id xs)))
               (irv-ballot-p new-xs))))

  ;; We need both remove-equal-does-not-increase-len-of-list and
  ;; remove-equal-decreases-len-of-list here.
  (defthm remove-equal-does-not-increase-len-of-list
    (<= (len (remove-equal id lst))
        (len lst))
    :rule-classes :linear)

  (defthm remove-equal-decreases-len-of-list
    (implies (member-equal id lst)
             (< (len (remove-equal id lst))
                (len lst)))
    :rule-classes :linear)

  (defthm len-of-flatten-list-is-more-than-len-of-a-sublist
    (<= (len (car xs))
        (len (acl2::flatten xs)))
    :hints (("Goal" :in-theory (e/d (acl2::flatten) ()))))

  (local
   (defthm a-candidate-is-present-in-every-voter-record-in-irv-ballot-p-core
     (implies (and (not (member-equal id (acl2::flatten (cdr xs))))
                   (member-equal id (acl2::flatten xs))
                   (irv-ballot-p-core (car xs) (cdr xs)))
              (equal (cdr xs) nil))
     :hints (("Goal" :in-theory (e/d (acl2::flatten) ())))))

  (local
   (defthm ill-formed-irv-ballot-p-core
     (implies (and (not (member-equal id (acl2::flatten xs)))
                   (consp xs)
                   (member-equal id cids))
              (not (irv-ballot-p-core cids xs)))))

  (local
   (defthm flatten-list-with-one-element
     (implies (equal (cdr xs) nil)
              (equal (len (acl2::flatten xs))
                     (len (car xs))))))

  (defthm eliminate-candidate-reduces-the-len-of-flatten-of-xs
    (implies (and (member-equal id (acl2::flatten xs))
                  (irv-ballot-p xs))
             (< (len (acl2::flatten (eliminate-candidate id xs)))
                (len (acl2::flatten xs))))
    :rule-classes :linear))

(i-am-here)

;; TODO: Prove termination of IRV before, and then after removing the error conditions below.
;; Prove that unless empty, step-n-candidate-to-remove is in the ballot xs.
(define irv ((xs irv-ballot-p))
  ;; :measure (len (acl2::flatten
  ;;                (eliminate-candidate
  ;;                 (candidate-with-least-nth-place-votes
  ;;                  0 (acl2::<-insertsort (car xs))
  ;;                  xs)
  ;;                 xs)))
  (if (endp xs)
      nil
    (b* ((step-1-candidate (first-choice-of-majority-p xs))
         ((when (natp step-1-candidate))
          step-1-candidate)
         (step-2-candidate (pick-candidate-among-those-with-same-number-of-first-place-votes xs))
         ((when (natp step-2-candidate))
          step-2-candidate)
         (step-n-candidate-to-remove
          (candidate-with-least-nth-place-votes
           0                       ;; First preference
           (acl2::<-sort (car xs)) ;; List of relevant candidates
           xs))
         ((unless (or (natp step-n-candidate-to-remove)
                      (member-equal step-n-candidate-to-remove (car xs))))
          ;; Error! This shouldn't happen.
          nil)
         (new-xs (eliminate-candidate step-n-candidate-to-remove xs)))
      (irv new-xs))))

(trace$ first-choice-of-majority-p)
(trace$ pick-candidate-among-those-with-same-number-of-first-place-votes)
(trace$ candidate-with-least-nth-place-votes)

(irv '((1 2 3) (1 3 2) (3 2 1) (2 3 1)))

;; ----------------------------------------------------------------------
