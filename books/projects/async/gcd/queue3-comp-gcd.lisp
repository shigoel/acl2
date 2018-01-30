;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2018

(in-package "ADE")

(include-book "comp-gcd")
(include-book "queue3")

(local (include-book "arithmetic-3/top" :dir :system))

(local (in-theory (disable nth)))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. DE Module Generator of QUEUE3-COMP-GCD
;;; 2. Specifying the Final State of QUEUE3-COMP-GCD After An N-Step Execution
;;; 3. Single-Step-Update Property
;;; 4. Relationship Between the Input and Output Sequences

;; ======================================================================

;; 1. DE Module Generator of QUEUE3-COMP-GCD
;;
;; Constructing a DE module generator that concatenates Q3 with COMP-GCD via a
;; link. Proving the value and state lemmas for this module generator.

(defconst *queue3-comp-gcd$go-num* (+ *queue3$go-num*
                                 *comp-gcd$go-num*))
(defconst *queue3-comp-gcd$st-len* 4)

(defun queue3-comp-gcd$data-ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ 2 (* 2 (mbe :logic (nfix data-width)
                 :exec  data-width))))

(defun queue3-comp-gcd$ins-len (data-width)
  (declare (xargs :guard (natp data-width)))
  (+ (queue3-comp-gcd$data-ins-len data-width)
     *queue3-comp-gcd$go-num*))

;; DE module generator of QUEUE3-COMP-GCD. It reports the "in-act" signal at
;; its input port, and the "out-act" signal and output data at its output port.

(module-generator
 queue3-comp-gcd* (data-width)
 (si 'queue3-comp-gcd data-width)
 (list* 'full-in 'empty-out- (append (sis 'data-in 0 (* 2 data-width))
                                     (sis 'go 0 *queue3-comp-gcd$go-num*)))
 (list* 'in-act 'out-act
        (sis 'data-out 0 data-width))
 '(l d q3 comp-gcd)
 (list
  ;; LINK
  ;; L
  '(l (l-status) link-cntl (q3-out-act comp-gcd-in-act))
  (list 'd
        (sis 'd-out 0 (* 2 data-width))
        (si 'latch-n (* 2 data-width))
        (cons 'q3-out-act (sis 'q3-data-out 0 (* 2 data-width))))

  ;; JOINTS
  ;; Q3
  (list 'q3
        (list* 'in-act 'q3-out-act
               (sis 'q3-data-out 0 (* 2 data-width)))
        (si 'queue3 (* 2 data-width))
        (list* 'full-in 'l-status
               (append (sis 'data-in 0 (* 2 data-width))
                       (sis 'go 0 *queue3$go-num*))))

  ;; COMP-GCD
  (list 'comp-gcd
        (list* 'comp-gcd-in-act 'out-act
               (sis 'data-out 0 data-width))
        (si 'comp-gcd data-width)
        (list* 'l-status 'empty-out-
               (append (sis 'd-out 0 (* 2 data-width))
                       (sis 'go
                            *queue3$go-num*
                            *comp-gcd$go-num*)))))

 :guard (natp data-width))

;; DE netlist generator. A generated netlist will contain an instance of
;; QUEUE3-COMP-GCD.

(defun queue3-comp-gcd$netlist (data-width)
  (declare (xargs :guard (and (natp data-width)
                              (<= 2 data-width))))
  (cons (queue3-comp-gcd* data-width)
        (union$ (queue3$netlist (* 2 data-width))
                (comp-gcd$netlist data-width)
                :test 'equal)))

;; Sanity syntactic check

(defthmd queue3-comp-gcd$netlist-64-okp
  (and (net-syntax-okp (queue3-comp-gcd$netlist 64))
       (net-arity-okp (queue3-comp-gcd$netlist 64))))

;; Recognizer for QUEUE3-COMP-GCD

(defund queue3-comp-gcd& (netlist data-width)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-width)
                              (<= 2 data-width))))
  (and (equal (assoc (si 'queue3-comp-gcd data-width) netlist)
              (queue3-comp-gcd* data-width))
       (b* ((netlist (delete-to-eq (si 'queue3-comp-gcd data-width)
                                   netlist)))
         (and (queue3& netlist (* 2 data-width))
              (comp-gcd& netlist data-width)
              (latch-n& netlist (* 2 data-width))))))

;; Sanity check

(defthm check-queue3-comp-gcd$netlist-64
  (queue3-comp-gcd& (queue3-comp-gcd$netlist 64) 64))

(defconst *queue3-comp-gcd$l*   0)
(defconst *queue3-comp-gcd$d*   1)
(defconst *queue3-comp-gcd$q3*  2)
(defconst *queue3-comp-gcd$comp-gcd* 3)

;; Constraints on the state of QUEUE3-COMP-GCD

(defund queue3-comp-gcd$valid-st (st data-width)
  (b* ((l   (get-field *queue3-comp-gcd$l* st))
       (d   (get-field *queue3-comp-gcd$d* st))
       (q3  (get-field *queue3-comp-gcd$q3* st))
       (comp-gcd (get-field *queue3-comp-gcd$comp-gcd* st)))
    (and (validp l)
         (len-1-true-listp d)
         (equal (len d) (* 2 data-width))
         (or (emptyp l)
             (bvp (strip-cars d)))

         (queue3$valid-st q3 (* 2 data-width))
         (comp-gcd$valid-st comp-gcd data-width))))

(defthmd queue3-comp-gcd$valid-st=>data-width-constraint
  (implies (queue3-comp-gcd$valid-st st data-width)
           (and (natp data-width)
                (<= 3 data-width)))
  :hints (("Goal"
           :use (:instance
                 comp-gcd$valid-st=>data-width-constraint
                 (st (get-field *queue3-comp-gcd$comp-gcd* st)))
           :in-theory (enable queue3-comp-gcd$valid-st)))
  :rule-classes :forward-chaining)

;; QUEUE3-COMP-GCD simulator

(progn
  (defun queue3-comp-gcd$map-to-links (st)
    (b* ((l   (get-field *queue3-comp-gcd$l* st))
         (d   (get-field *queue3-comp-gcd$d* st))
         (q3  (get-field *queue3-comp-gcd$q3* st))
         (comp-gcd (get-field *queue3-comp-gcd$comp-gcd* st)))
      (append (list (cons 'q3 (queue3$map-to-links q3)))
              (map-to-links (list (list 'l l d)))
              (list (cons 'comp-gcd (comp-gcd$map-to-links comp-gcd))))))

  (defun queue3-comp-gcd$map-to-links-list (x)
    (if (atom x)
        nil
      (cons (queue3-comp-gcd$map-to-links (car x))
            (queue3-comp-gcd$map-to-links-list (cdr x)))))

  (defund queue3-comp-gcd$sim (data-width n state)
    (declare (xargs :guard (and (natp data-width)
                                (natp n))
                    :verify-guards nil
                    :stobjs state))
    (b* ((num-signals (queue3-comp-gcd$ins-len data-width))
         ((mv inputs-lst state)
          (signal-vals-gen num-signals n state nil))
         ;;(- (cw "~x0~%" inputs-lst))
         (full '(t))
         (empty '(nil))
         (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
         (q3 (list empty invalid-data
                   empty invalid-data
                   empty invalid-data))
         (comp-gcd (list full '(nil)
                         empty invalid-data
                         empty invalid-data
                         empty invalid-data))
         (st (list empty invalid-data q3 comp-gcd)))
      (mv (pretty-list
           (remove-dup-neighbors
            (queue3-comp-gcd$map-to-links-list
             (de-sim-list (si 'queue3-comp-gcd data-width)
                          inputs-lst
                          st
                          (queue3-comp-gcd$netlist data-width))))
           0)
          state)))
  )

;; Extracting the input data

(defun queue3-comp-gcd$data-in (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (take (* 2 (mbe :logic (nfix data-width)
                  :exec  data-width))
        (nthcdr 2 inputs)))

(defthm len-queue3-comp-gcd$data-in
  (equal (len (queue3-comp-gcd$data-in inputs data-width))
         (* 2 (nfix data-width))))

(in-theory (disable queue3-comp-gcd$data-in))

;; Extracting the inputs for the Q3 joint

(defund queue3-comp-gcd$q3-inputs (inputs st data-width)
  (b* ((full-in (nth 0 inputs))
       (data-in (queue3-comp-gcd$data-in inputs data-width))
       (go-signals (nthcdr (queue3-comp-gcd$data-ins-len data-width)
                           inputs))

       (q3-go-signals (take *queue3$go-num* go-signals))

       (l (get-field *queue3-comp-gcd$l* st)))

    (list* full-in (car l)
           (append data-in q3-go-signals))))

;; Extracting the inputs for the COMP-GCD joint

(defund queue3-comp-gcd$comp-gcd-inputs (inputs st data-width)
  (b* ((empty-out- (nth 1 inputs))
       (go-signals (nthcdr (queue3-comp-gcd$data-ins-len data-width)
                           inputs))

       (comp-gcd-go-signals (take *comp-gcd$go-num*
                                  (nthcdr *queue3$go-num* go-signals)))

       (l (get-field *queue3-comp-gcd$l* st))
       (d (get-field *queue3-comp-gcd$d* st)))

    (list* (car l) empty-out-
           (append (v-threefix (strip-cars d))
                   comp-gcd-go-signals))))

;; Extracting the "in-act" signal

(defund queue3-comp-gcd$in-act (inputs st data-width)
  (queue3$in-act (queue3-comp-gcd$q3-inputs inputs st data-width)
                 (get-field *queue3-comp-gcd$q3* st)
                 (* 2 data-width)))

;; Extracting the "out-act" signal

(defund queue3-comp-gcd$out-act (inputs st data-width)
  (comp-gcd$out-act (queue3-comp-gcd$comp-gcd-inputs inputs st data-width)
                    (get-field *queue3-comp-gcd$comp-gcd* st)
                    data-width))

;; Extracting the output data

(defund queue3-comp-gcd$data-out (inputs st data-width)
  (comp-gcd$data-out (queue3-comp-gcd$comp-gcd-inputs inputs st data-width)
                     (get-field *queue3-comp-gcd$comp-gcd* st)
                     data-width))

(defthm len-queue3-comp-gcd$data-out
  (implies (queue3-comp-gcd$valid-st st data-width)
           (equal (len (queue3-comp-gcd$data-out inputs st data-width))
                  data-width))
  :hints (("Goal" :in-theory (enable queue3-comp-gcd$valid-st
                                     queue3-comp-gcd$data-out))))

(defthm bvp-queue3-comp-gcd$data-out
  (implies (and (queue3-comp-gcd$valid-st st data-width)
                (queue3-comp-gcd$out-act inputs st data-width))
           (bvp (queue3-comp-gcd$data-out inputs st data-width)))
  :hints (("Goal" :in-theory (enable queue3-comp-gcd$valid-st
                                     queue3-comp-gcd$out-act
                                     queue3-comp-gcd$data-out))))

(not-primp-lemma queue3-comp-gcd)

(encapsulate
  ()

  (local
   (defthm validp=>f-buf-canceled
     (implies (validp x)
              (equal (f-buf (car x))
                     (car x)))))

  ;; The value lemma for QUEUE3-COMP-GCD

  (defthmd queue3-comp-gcd$value
    (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
      (implies
       (and (queue3-comp-gcd& netlist data-width)
            (true-listp data-in)
            (equal (len data-in) (* 2 data-width))
            (true-listp go-signals)
            (equal (len go-signals) *queue3-comp-gcd$go-num*)
            (queue3-comp-gcd$valid-st st data-width))
       (equal (se (si 'queue3-comp-gcd data-width) inputs st netlist)
              (list* (queue3-comp-gcd$in-act inputs st data-width)
                     (queue3-comp-gcd$out-act inputs st data-width)
                     (queue3-comp-gcd$data-out inputs st data-width)))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (se (si 'queue3-comp-gcd data-width)
                         (list* full-in empty-out-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              get-field
                              comp-gcd$valid-st=>data-width-constraint
                              len-1-true-listp=>true-listp
                              not-primp-queue3-comp-gcd
                              queue3-comp-gcd&
                              queue3-comp-gcd*$destructure
                              latch-n$value
                              queue3$value
                              comp-gcd$value
                              queue3-comp-gcd$data-in
                              queue3-comp-gcd$valid-st
                              queue3-comp-gcd$in-act
                              queue3-comp-gcd$out-act
                              queue3-comp-gcd$data-out
                              queue3-comp-gcd$q3-inputs
                              queue3-comp-gcd$comp-gcd-inputs)
                             ((queue3-comp-gcd*)
                              nfix
                              acl2::take-of-append
                              if*
                              b-not
                              cons-equal
                              validp
                              fullp
                              emptyp
                              de-module-disabled-rules)))))

  ;; This function specifies the next state of QUEUE3-COMP-GCD.

  (defun queue3-comp-gcd$state-fn (inputs st data-width)
    (b* ((l   (get-field *queue3-comp-gcd$l* st))
         (d   (get-field *queue3-comp-gcd$d* st))
         (q3  (get-field *queue3-comp-gcd$q3* st))
         (comp-gcd (get-field *queue3-comp-gcd$comp-gcd* st))

         (q3-inputs (queue3-comp-gcd$q3-inputs inputs st data-width))
         (comp-gcd-inputs (queue3-comp-gcd$comp-gcd-inputs
                           inputs st data-width))

         (d-in (queue3$data-out q3))

         (q3-out-act (queue3$out-act q3-inputs q3 (* 2 data-width)))
         (comp-gcd-in-act (comp-gcd$in-act comp-gcd-inputs
                                           comp-gcd data-width)))
      (list
       ;; L
       (list (f-sr q3-out-act comp-gcd-in-act (car l)))
       (pairlis$ (fv-if q3-out-act d-in (strip-cars d))
                 nil)

       ;; Joint Q3
       (queue3$state-fn q3-inputs q3 (* 2 data-width))
       ;; Joint COMP-GCD
       (comp-gcd$state-fn comp-gcd-inputs comp-gcd data-width))))

  (defthm len-of-queue3-comp-gcd$state-fn
    (equal (len (queue3-comp-gcd$state-fn inputs st data-width))
           *queue3-comp-gcd$st-len*))

  ;; The state lemma for QUEUE3-COMP-GCD

  (defthmd queue3-comp-gcd$state
    (b* ((inputs (list* full-in empty-out- (append data-in go-signals))))
      (implies
       (and (queue3-comp-gcd& netlist data-width)
            (true-listp data-in)
            (equal (len data-in) (* 2 data-width))
            (true-listp go-signals)
            (equal (len go-signals) *queue3-comp-gcd$go-num*)
            (queue3-comp-gcd$valid-st st data-width))
       (equal (de (si 'queue3-comp-gcd data-width) inputs st netlist)
              (queue3-comp-gcd$state-fn inputs st data-width))))
    :hints (("Goal"
             :do-not-induct t
             :do-not '(preprocess)
             :expand (de (si 'queue3-comp-gcd data-width)
                         (list* full-in empty-out-
                                (append data-in go-signals))
                         st
                         netlist)
             :in-theory (e/d (de-rules
                              get-field
                              comp-gcd$valid-st=>data-width-constraint
                              len-1-true-listp=>true-listp
                              not-primp-queue3-comp-gcd
                              queue3-comp-gcd&
                              queue3-comp-gcd*$destructure
                              queue3-comp-gcd$valid-st
                              queue3-comp-gcd$data-in
                              queue3-comp-gcd$data-out
                              queue3-comp-gcd$q3-inputs
                              queue3-comp-gcd$comp-gcd-inputs
                              queue3$value queue3$state
                              comp-gcd$value comp-gcd$state
                              latch-n$value latch-n$state)
                             ((queue3-comp-gcd*)
                              nfix
                              if*
                              b-not
                              append-take-nthcdr
                              acl2::take-of-append
                              acl2::prefer-positive-addends-equal
                              acl2::simplify-sums-equal
                              acl2::simplify-products-gather-exponents-equal
                              acl2::|(equal (- x) (- y))|
                              append
                              cons-equal
                              true-listp
                              validp
                              fullp
                              emptyp
                              de-module-disabled-rules)))))

  (in-theory (disable queue3-comp-gcd$state-fn))
  )

;; ======================================================================

;; 2. Specifying the Final State of QUEUE3-COMP-GCD After An N-Step Execution

;; Conditions on the inputs

(defund queue3-comp-gcd$input-format (inputs data-width)
  (declare (xargs :guard (and (true-listp inputs)
                              (natp data-width))))
  (b* ((full-in    (nth 0 inputs))
       (empty-out- (nth 1 inputs))
       (data-in    (queue3-comp-gcd$data-in inputs data-width))
       (go-signals (nthcdr (queue3-comp-gcd$data-ins-len data-width)
                           inputs)))
    (and
     (booleanp full-in)
     (booleanp empty-out-)
     (or (not full-in) (bvp data-in))
     (true-listp go-signals)
     (= (len go-signals) *queue3-comp-gcd$go-num*)
     (equal inputs
            (list* full-in empty-out- (append data-in go-signals))))))

;; Proving that queue3-comp-gcd$valid-st is an invariant.

(progn
  (local
   (defthm queue3-comp-gcd$input-format=>q3$input-format
     (implies (and (queue3-comp-gcd$input-format inputs data-width)
                   (queue3-comp-gcd$valid-st st data-width))
              (queue3$input-format
               (queue3-comp-gcd$q3-inputs inputs st data-width)
               (* 2 data-width)))
     :hints (("Goal"
              :in-theory (e/d (queue3-comp-gcd$input-format
                               comp-gcd$valid-st=>data-width-constraint
                               queue3$input-format
                               queue3$data-in
                               queue3-comp-gcd$valid-st
                               queue3-comp-gcd$q3-inputs)
                              (nthcdr
                               nfix
                               len
                               take-of-too-many))))))

  (local
   (defthm queue3-comp-gcd$input-format=>comp-gcd$input-format
     (implies (and (queue3-comp-gcd$input-format inputs data-width)
                   (queue3-comp-gcd$valid-st st data-width))
              (comp-gcd$input-format
               (queue3-comp-gcd$comp-gcd-inputs inputs st data-width)
               data-width))
     :hints (("Goal"
              :in-theory (e/d (queue3-comp-gcd$input-format
                               comp-gcd$valid-st=>data-width-constraint
                               comp-gcd$input-format
                               comp-gcd$data-in
                               queue3-comp-gcd$valid-st
                               queue3-comp-gcd$comp-gcd-inputs)
                              (nthcdr
                               nfix
                               len
                               take-of-too-many))))))

  (local
   (defthm booleanp-queue3-comp-gcd$q3-out-act
     (implies (and (or (equal (nth *queue3-comp-gcd$l* st) '(t))
                       (equal (nth *queue3-comp-gcd$l* st) '(nil)))
                   (queue3$valid-st (nth *queue3-comp-gcd$q3* st)
                                    (* 2 data-width)))
              (booleanp
               (queue3$out-act (queue3-comp-gcd$q3-inputs
                                inputs st data-width)
                               (nth *queue3-comp-gcd$q3* st)
                               (* 2 data-width))))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               queue3-comp-gcd$q3-inputs
                               queue3$valid-st
                               queue3$out-act)
                              (nfix))))
     :rule-classes :type-prescription))

  (local
   (defthm queue3-comp-gcd$q3-out-act-nil
     (implies (equal (nth *queue3-comp-gcd$l* st) '(t))
              (not (queue3$out-act (queue3-comp-gcd$q3-inputs inputs st data-width)
                                   (nth *queue3-comp-gcd$q3* st)
                                   (* 2 data-width))))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               queue3-comp-gcd$q3-inputs
                               queue3$out-act)
                              (nfix))))))

  (local
   (defthm booleanp-queue3-comp-gcd$comp-gcd-in-act
     (implies (and (or (equal (nth *queue3-comp-gcd$l* st) '(t))
                       (equal (nth *queue3-comp-gcd$l* st) '(nil)))
                   (comp-gcd$valid-st (nth *queue3-comp-gcd$comp-gcd* st)
                                      data-width))
              (booleanp
               (comp-gcd$in-act (queue3-comp-gcd$comp-gcd-inputs inputs st data-width)
                                (nth *queue3-comp-gcd$comp-gcd* st)
                                data-width)))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               queue3-comp-gcd$comp-gcd-inputs
                               merge$act0
                               comp-gcd$valid-st
                               comp-gcd$me-inputs
                               comp-gcd$in-act)
                              (nfix))))
     :rule-classes :type-prescription))

  (local
   (defthm queue3-comp-gcd$comp-gcd-in-act-nil
     (implies (equal (nth *queue3-comp-gcd$l* st) '(nil))
              (not (comp-gcd$in-act (queue3-comp-gcd$comp-gcd-inputs inputs st data-width)
                                    (nth *queue3-comp-gcd$comp-gcd* st)
                                    data-width)))
     :hints (("Goal"
              :in-theory (e/d (get-field
                               queue3-comp-gcd$comp-gcd-inputs
                               merge$act0
                               comp-gcd$me-inputs
                               comp-gcd$in-act)
                              (nfix))))))

  (defthm queue3-comp-gcd$valid-st-preserved
    (implies (and (queue3-comp-gcd$input-format inputs data-width)
                  (queue3-comp-gcd$valid-st st data-width))
             (queue3-comp-gcd$valid-st
              (queue3-comp-gcd$state-fn inputs st data-width)
              data-width))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue3-comp-gcd$input-format
                              queue3-comp-gcd$valid-st
                              queue3-comp-gcd$state-fn
                              f-sr)
                             (if*
                              nfix
                              nthcdr
                              b-if
                              acl2::true-listp-append)))))
  )

(defthmd queue3-comp-gcd$state-alt
  (implies (and (queue3-comp-gcd& netlist data-width)
                (queue3-comp-gcd$input-format inputs data-width)
                (queue3-comp-gcd$valid-st st data-width))
           (equal (de (si 'queue3-comp-gcd data-width) inputs st netlist)
                  (queue3-comp-gcd$state-fn inputs st data-width)))
  :hints (("Goal"
           :in-theory (enable queue3-comp-gcd$valid-st=>data-width-constraint
                              queue3-comp-gcd$input-format)
           :use (:instance
                 queue3-comp-gcd$state
                 (full-in    (nth 0 inputs))
                 (empty-out- (nth 1 inputs))
                 (data-in    (queue3-comp-gcd$data-in inputs data-width))
                 (go-signals (nthcdr (queue3-comp-gcd$data-ins-len data-width)
                                     inputs))))))

(state-fn-n-gen queue3-comp-gcd data-width)
(input-format-n-gen queue3-comp-gcd data-width)

(defthmd de-sim-n$queue3-comp-gcd
  (implies (and (queue3-comp-gcd& netlist data-width)
                (queue3-comp-gcd$input-format-n inputs-lst data-width n)
                (queue3-comp-gcd$valid-st st data-width))
           (equal (de-sim-n (si 'queue3-comp-gcd data-width)
                            inputs-lst st netlist
                            n)
                  (queue3-comp-gcd$state-fn-n inputs-lst st data-width n)))
  :hints (("Goal" :in-theory (enable queue3-comp-gcd$state-alt))))

;; ======================================================================

;; 3. Single-Step-Update Property

;; The operation of QUEUE3-COMP-GCD over an accepted input sequence

(defun queue3-comp-gcd$op-seq (in-seq)
  (if (atom in-seq)
      nil
    (cons (comp-gcd$op (car in-seq))
          (queue3-comp-gcd$op-seq (cdr in-seq)))))

(defthm len-of-queue3-comp-gcd$op-seq
  (equal (len (queue3-comp-gcd$op-seq x))
         (len x)))

(defthm queue3-comp-gcd$op-seq-of-append
  (equal (queue3-comp-gcd$op-seq (append x y))
         (append (queue3-comp-gcd$op-seq x) (queue3-comp-gcd$op-seq y))))

;; The extraction function for QUEUE3-COMP-GCD that computes the future output
;; sequence from the current state.

(defund queue3-comp-gcd$extract-state (st)
  (b* ((l   (get-field *queue3-comp-gcd$l* st))
       (d   (get-field *queue3-comp-gcd$d* st))
       (q3  (get-field *queue3-comp-gcd$q3* st))
       (comp-gcd (get-field *queue3-comp-gcd$comp-gcd* st)))
    (append
     (queue3-comp-gcd$op-seq
      (append (queue3$extract-state q3)
              (extract-state (list l d))))
     (comp-gcd$extract-state comp-gcd))))

;; Specifying and proving a state invariant

(progn
  (defund queue3-comp-gcd$inv (st)
    (b* ((comp-gcd (get-field *queue3-comp-gcd$comp-gcd* st)))
      (comp-gcd$inv comp-gcd)))

  (defthm queue3-comp-gcd$inv-preserved
    (implies (and (queue3-comp-gcd$input-format inputs data-width)
                  (queue3-comp-gcd$valid-st st data-width)
                  (queue3-comp-gcd$inv st))
             (queue3-comp-gcd$inv
              (queue3-comp-gcd$state-fn inputs st data-width)))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              queue3-comp-gcd$valid-st
                              queue3-comp-gcd$inv
                              queue3-comp-gcd$state-fn)
                             ()))))
  )

;; Extracting the accepted input sequence

(defun queue3-comp-gcd$in-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue3-comp-gcd$in-act inputs st data-width) t)
          (append (queue3-comp-gcd$in-seq
                   (cdr inputs-lst)
                   (queue3-comp-gcd$state-fn inputs st data-width)
                   data-width
                   (1- n))
                  (list (queue3-comp-gcd$data-in inputs data-width)))
        (queue3-comp-gcd$in-seq
         (cdr inputs-lst)
         (queue3-comp-gcd$state-fn inputs st data-width)
         data-width
         (1- n))))))

;; Extracting the valid output sequence

(defun queue3-comp-gcd$out-seq (inputs-lst st data-width n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      nil
    (b* ((inputs (car inputs-lst)))
      (if (equal (queue3-comp-gcd$out-act inputs st data-width) t)
          (append (queue3-comp-gcd$out-seq
                   (cdr inputs-lst)
                   (queue3-comp-gcd$state-fn inputs st data-width)
                   data-width
                   (1- n))
                  (list (queue3-comp-gcd$data-out inputs st data-width)))
        (queue3-comp-gcd$out-seq
         (cdr inputs-lst)
         (queue3-comp-gcd$state-fn inputs st data-width)
         data-width
         (1- n))))))

;; Input-output sequence simulator

(defund queue3-comp-gcd$in-out-seq-sim (data-width n state)
  (declare (xargs :guard (and (natp data-width)
                              (natp n))
                  :verify-guards nil
                  :stobjs state))
  (b* ((num-signals (queue3-comp-gcd$ins-len data-width))
       ((mv inputs-lst state)
        (signal-vals-gen num-signals n state nil))
       (full '(t))
       (empty '(nil))
       (invalid-data (make-list (* 2 data-width) :initial-element '(x)))
       (q3 (list empty invalid-data
                 empty invalid-data
                 empty invalid-data))
       (comp-gcd (list full '(nil)
                       empty invalid-data
                       empty invalid-data
                       empty invalid-data))
       (st (list empty invalid-data q3 comp-gcd)))
    (mv
     (append
      (list
       (cons 'in-seq
             (v-to-nat-split-lst
              (queue3-comp-gcd$in-seq inputs-lst st data-width n)
              data-width)))
      (list
       (cons 'out-seq
             (v-to-nat-lst
              (queue3-comp-gcd$out-seq inputs-lst st data-width n)))))
     state)))

;; The extracted next-state function for QUEUE3-COMP-GCD

(defund queue3-comp-gcd$step-spec (inputs st data-width)
  (b* ((data (comp-gcd$op (queue3-comp-gcd$data-in inputs data-width)))
       (extracted-st (queue3-comp-gcd$extract-state st))
       (n (1- (len extracted-st))))
    (cond
     ((equal (queue3-comp-gcd$out-act inputs st data-width) t)
      (cond
       ((equal (queue3-comp-gcd$in-act inputs st data-width) t)
        (cons data (take n extracted-st)))
       (t (take n extracted-st))))
     (t (cond
         ((equal (queue3-comp-gcd$in-act inputs st data-width) t)
          (cons data extracted-st))
         (t extracted-st))))))

(local
 (defthm comp-gcd-cond$extract-state-not-empty
   (implies (and (comp-gcd-cond$out-act0 inputs st data-width)
                 (comp-gcd-cond$valid-st st data-width))
            (< 0 (len (comp-gcd-cond$extract-state st))))
   :hints (("Goal"
            :in-theory (e/d (branch$act0
                             gcd-cond$br-inputs
                             gcd-cond$act0
                             comp-gcd-cond$br-inputs
                             comp-gcd-cond$out-act0
                             comp-gcd-cond$valid-st
                             comp-gcd-cond$extract-state)
                            (nfix))))
   :rule-classes :linear))

(local
 (defthm comp-gcd$extract-state-not-empty
   (implies (and (comp-gcd$out-act inputs st data-width)
                 (comp-gcd$valid-st st data-width))
            (< 0 (len (comp-gcd$extract-state st))))
   :hints (("Goal"
            :in-theory (e/d (comp-gcd$valid-st
                             comp-gcd$extract-state
                             comp-gcd$out-act)
                            (nfix))))
   :rule-classes :linear))

;; The single-step-update property

(encapsulate
  ()

  (local
   (defthm queue3-comp-gcd$step-spec-correct-aux-1
     (b* ((q3-inputs (queue3-comp-gcd$q3-inputs inputs st data-width)))
       (implies (natp data-width)
                (equal (queue3$data-in q3-inputs (* 2 data-width))
                       (take (* 2 data-width)
                             (nthcdr 2 inputs)))))
     :hints (("Goal" :in-theory (enable queue3-comp-gcd$q3-inputs
                                        queue3-comp-gcd$data-in
                                        queue3$data-in)))))

  (local
   (defthm queue3-comp-gcd$step-spec-correct-aux-2
     (b* ((comp-gcd-inputs (queue3-comp-gcd$comp-gcd-inputs
                            inputs st data-width))
          (d (nth *queue3-comp-gcd$d* st)))
       (implies (and (natp data-width)
                     (equal (len d) (* 2 data-width))
                     (bvp (strip-cars d)))
                (equal (comp-gcd$data-in comp-gcd-inputs data-width)
                       (strip-cars d))))
     :hints (("Goal" :in-theory (enable get-field
                                        queue3-comp-gcd$comp-gcd-inputs
                                        comp-gcd$data-in)))))

  (local
   (defthm queue3-comp-gcd$op-seq-of-append-instance
     (equal (queue3-comp-gcd$op-seq (append x (list (strip-cars d))))
            (append (queue3-comp-gcd$op-seq x)
                    (queue3-comp-gcd$op-seq (list (strip-cars d)))))))

  (defthm queue3-comp-gcd$step-spec-correct
    (b* ((next-st (queue3-comp-gcd$state-fn inputs st data-width)))
      (implies (and (queue3-comp-gcd$input-format inputs data-width)
                    (queue3-comp-gcd$valid-st st data-width)
                    (queue3-comp-gcd$inv st))
               (equal (queue3-comp-gcd$extract-state next-st)
                      (queue3-comp-gcd$step-spec inputs st data-width))))
    :hints (("Goal"
             :in-theory (e/d (get-field
                              comp-gcd$valid-st=>data-width-constraint
                              queue3$step-spec
                              comp-gcd$step-spec
                              queue3-comp-gcd$step-spec
                              queue3-comp-gcd$input-format
                              queue3-comp-gcd$valid-st
                              queue3-comp-gcd$inv
                              queue3-comp-gcd$state-fn
                              queue3-comp-gcd$data-in
                              queue3-comp-gcd$in-act
                              queue3-comp-gcd$out-act
                              queue3-comp-gcd$data-out
                              queue3-comp-gcd$extract-state
                              f-sr)
                             (if*
                              not
                              queue3-comp-gcd$op-seq-of-append
                              take-of-too-many)))))
  )

;; ======================================================================

;; 4. Relationship Between the Input and Output Sequences

(defthm queue3-comp-gcd$extract-state-lemma
  (implies (and (queue3-comp-gcd$valid-st st data-width)
                (queue3-comp-gcd$inv st)
                (equal n (1- (len (queue3-comp-gcd$extract-state st))))
                (queue3-comp-gcd$out-act inputs st data-width))
           (equal (append
                   (take n (queue3-comp-gcd$extract-state st))
                   (list (queue3-comp-gcd$data-out inputs st data-width)))
                  (queue3-comp-gcd$extract-state st)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (queue3-comp-gcd$valid-st
                            queue3-comp-gcd$inv
                            queue3-comp-gcd$extract-state
                            queue3-comp-gcd$out-act
                            queue3-comp-gcd$data-out)
                           ()))))

(encapsulate
  ()

  (local
   (defthm queue3-comp-gcd$dataflow-correct-aux
     (implies (equal (append x1 y1)
                     (append (queue3-comp-gcd$op-seq in-seq) y2))
              (equal (append x1 y1 z)
                     (append (queue3-comp-gcd$op-seq in-seq) y2 z)))
     :hints (("Goal" :in-theory (e/d (left-associativity-of-append)
                                     (acl2::associativity-of-append))))))

  (defthmd queue3-comp-gcd$dataflow-correct
    (b* ((extracted-st (queue3-comp-gcd$extract-state st))
         (final-st (queue3-comp-gcd$state-fn-n inputs-lst st data-width n))
         (final-extracted-st (queue3-comp-gcd$extract-state final-st)))
      (implies
       (and (queue3-comp-gcd$input-format-n inputs-lst data-width n)
            (queue3-comp-gcd$valid-st st data-width)
            (queue3-comp-gcd$inv st))
       (equal (append final-extracted-st
                      (queue3-comp-gcd$out-seq inputs-lst st data-width n))
              (append (queue3-comp-gcd$op-seq
                       (queue3-comp-gcd$in-seq inputs-lst st data-width n))
                      extracted-st))))
    :hints (("Goal"
             :in-theory (e/d (queue3-comp-gcd$step-spec)
                             ()))))
  )

