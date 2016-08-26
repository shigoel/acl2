; Theorems about world-related functions
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm arity-iff
  (iff (arity fn wrld)
       (or (consp fn)
           (function-symbolp fn wrld)))
  :hints (("Goal" :in-theory (enable arity))))

(defthm plist-worldp-when-plist-worldp-with-formals-cheap
  (implies (not (plist-worldp wrld))
           (not (plist-worldp-with-formals wrld)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))