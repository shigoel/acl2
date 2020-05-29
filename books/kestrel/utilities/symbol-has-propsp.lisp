; A utility to check whether a symbol has any properties
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;would call this has-propsp, but that is already defined
(defun symbol-has-propsp (name state)
    (declare (xargs :stobjs state
                    :guard (symbolp name)))
  (getprops name 'current-acl2-world (w state)))
