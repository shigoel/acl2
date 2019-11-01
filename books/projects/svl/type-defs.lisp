; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")


(include-book "centaur/sv/svex/vars" :dir :system)
(include-book "centaur/sv/mods/svmods" :dir :system)

(include-book "centaur/fty/top" :dir :system)

;;(include-book "projects/apply/top" :dir :system)

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "tools")
(include-book "macros")

(include-book "projects/rp-rewriter/top" :dir :system)

(encapsulate
  nil

  (define stringlist*-p (list*)
    :enabled t
    (if (atom list*)
        (stringp list*)
      (and (stringp (car list*))
           (stringlist*-p (cdr list*)))))

  (define occ-name-p (x)
    (declare (ignorable x))
    t; (not (booleanp x))
    #|(or (and (symbolp x)
    (not (booleanp x)))
    (stringlist*-p x))||#
    :returns (res booleanp))

  (define occ-name-fix (x)
    (if (occ-name-p x)
        x
      ""))

;(defprod

  (defthm occ-name-p-occ-name-fix-x
    (occ-name-p (occ-name-fix acl2::x))
    :hints (("goal"
             :in-theory (e/d (occ-name-p
                              occ-name-fix) ()))))

  (defthm occ-name-p-occ-name-fix-x-2
    (implies (occ-name-p acl2::x)
             (equal (occ-name-fix acl2::x)
                    acl2::x))
    :hints (("goal"
             :in-theory (e/d (occ-name-p
                              occ-name-fix) ()))))

  (fty::deffixtype occ-name
                   :pred  occ-name-p
                   :fix   occ-name-fix
                   :equiv occ-name-equiv
                   :define t
                   :forward t)

  (fty::deflist occ-name-list
                :elt-type occ-name)

  (fty::defalist occ-name-alist
                 :val-type occ-name-list
                 :key-type occ-name))




(encapsulate
  nil
  (defun wire-p (wire)
    (declare (xargs :guard t))
    (case-match wire
      ((wire-name size . start)
       (and #|(or (stringp wire-name)
        (symbolp wire-name))||#
        (sv::svar-p wire-name)
;      (not (booleanp wire-name))
        (natp size)
        (natp start)))
      ((wire-name)
       (sv::svar-p wire-name)
       #|(and (or (stringp wire-name)
       (symbolp wire-name))
       (not (booleanp wire-name)))||#)
      (& nil)))

  (defun wire-fix (wire)
    (declare (xargs :guard t))
    (if (wire-p wire)
        wire
      `("" 1 . 0)))

  (defthm wire-p-wire-fix-x
    (wire-p (wire-fix x)))

  (defun wire-list-p (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        (eq wires nil)
      (and (wire-p (car wires))
           (wire-list-p (cdr wires)))))

  (defun wire-list-fix (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        nil
      (cons (wire-fix (car wires))
            (wire-list-fix (cdr wires)))))

  (defthm WIRE-LIST-P-WIRE-LIST-FIX-x
    (WIRE-LIST-P (WIRE-LIST-FIX ACL2::X))
    :hints (("Goal"
             :in-theory (e/d (WIRE-LIST-P
                              WIRE-LIST-FIX)
                             (wire-p
                              wire-fix)))))

  (fty::deffixtype wire-list
                   :pred  wire-list-p
                   :fix   wire-list-fix
                   :equiv equal)

  (define module-occ-wire-p (wire)
    :enabled t
    (and (consp wire)
         (stringp (car wire))
;(sv::lhs-p (cdr wire))
         ))

  (define module-occ-wire-fix (wire)
    :enabled t
    (if (module-occ-wire-p wire)
        wire
      `("" . ("" 1 . 0))))

  (fty::deffixtype module-occ-wire
                   :pred  module-occ-wire-p
                   :fix   module-occ-wire-fix
                   :equiv equal)

  (defun module-occ-wire-list-p (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        (eq wires nil)
      (and (module-occ-wire-p (car wires))
           (module-occ-wire-list-p (cdr wires)))))

  (defun module-occ-wire-list-fix (wires)
    (declare (xargs :guard t))
    (if (atom wires)
        nil
      (cons (module-occ-wire-fix (car wires))
            (module-occ-wire-list-fix (cdr wires)))))

  (fty::deffixtype module-occ-wire-list
                   :pred  module-occ-wire-list-p
                   :fix   module-occ-wire-list-fix
                   :equiv equal)

  (defmacro wire-name (wire)
    `(car ,wire))

  (defmacro wire-size (wire)
    `(cadr ,wire))

  (defmacro wire-start (wire)
    `(cddr ,wire)))


(encapsulate
  nil
  (local
   (in-theory (enable measure-lemmas)))

  (local
   (defthm svl-env-measure-lemma
     (implies (and (< a x)
                   (natp z)
                   (natp y))
              (< a
                 (+ x y z)))))

  (local
   (defthm lemma1
     (implies
      (and (consp x) (consp (car x)))
      (< (cons-countw (cdr (car x)) 2)
         (cons-countw x 2)))
     :hints (("goal"
	      :in-theory (e/d (cons-countw) ())))))

  (local
   (defthm lemma2-lemma
     (implies (and (natp a)
                   (natp b)
                   (natp x))
              (< x
                 (+ 1 a x b)))))

  (local
   (defthm lemma2-lemma2
     (implies (and (natp a))
              (< 2
                 (+ 3 a)))))

  (local
   (defthm lemma2
     (< (cons-countw (cadr x) 2)
        (+ 1 (cons-countw x 2)))
     :otf-flg t
     :hints (("goal"
              :expand ((cons-countw x 2)
                       (cons-countw (cdr x) 2))
              :in-theory (e/d () ())))))

  (local
   (defthm lemma3-lemma1
     (implies (natp w)
              (<= w (cons-countw x w)))
     :hints (("Goal"
              :induct (cons-countw x w)
              :in-theory (e/d (cons-countw) ())))))

  (local
   (defthm lemma3-lemma2
     (implies
      (and (<= 2 a)
           (<= 2 b))
      (< (1+ x)
         (+ a b x)))))

  (local
   (defthm lemma3
     (implies (and (consp x) (consp (car x)))
              (< (+ 1 (cons-countw (cdr (car x)) 2))
                 (cons-countw x 2)))
     :hints (("Goal"
              :expand ((cons-countw x 2)
                       (CONS-COUNTW (CAR X) 2))
              :in-theory (e/d () ())))))

  (fty::deftypes
   svl-env
   (fty::defprod svl-env
                 ((wires sv::svex-env-p)
                  (modules svl-env-alist-p))
                 :tag nil
                 :count nil
                 :measure (+ 1 (cons-countw x 2))
                 :layout :list)

   (fty::defalist svl-env-alist
                  :count nil
                  :measure (cons-countw x 2)
                  :val-type svl-env)))
