(in-package "ACL2")

(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

(defpkg "IRV"
  (union-eq
   '(
     binary-logand
     binary-logior
     binary-logxor

     a b c d e f g h i j k l m n o p q r s t u v w x y z lst

     definline
     def-gl-thm
     b*
     include-raw
     
     ;; XDOC
     defsection
     defxdoc
     top

     ;; TOOLS
     defprod
     def-ruleset
     def-ruleset!
     add-to-ruleset
     ruleset-theory
     enable*
     disable*
     e/d*

     IRV ; so that top-level :doc topic is also in "ACL2" package

     )
   (union-eq *acl2-exports*
             acl2::*bitops-exports*
             std::*std-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

;; ======================================================================
