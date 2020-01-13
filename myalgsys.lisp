;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/
(in-package :maxima)
(eval-when (:compile-toplevel :load-toplevel :execute)
   ($load "grobner"))

(defun $myalgsys (ee x)
   ;;merror when ee or x isn't a Maxima list.
   (when (or (not ($listp ee)) (not ($listp x)))
      (merror (intl:gettext "myalgsys: both arguments must be a Maxima lists")))
   ;;merror when not every unknown is a mapatom.
   (when (not (every #'$mapatom (cdr x)))
      (merror (intl:gettext "myalgsys: each unknown must be a maptom")))

   (let ((sol) (cnds) (e))
       (setq e (mapcar #'meqhk (cdr ee))) ; remove '(mlist) and convert a=b to a-b.
       (setq cnds (mapcar #'(lambda (q) (take '(mnotequal) ($ratdenom q) 0)) e)); collect denominators.
       (setq e (mapcar #'$ratnumer e)) ;collect numerators
       ;; merror for non-rational expression inputs
       (when (not (every #'(lambda (q) ($polynomialp q x
   			              	#'(lambda (s) ($lfreeof x s))
   	   	           		  #'(lambda (s) (and (integerp s) (>= s 0))))) (append e cnds)))
            (merror (intl:gettext "myalgsys: equations must be a list of rational expressions.")))
       (setq e (cons '(mlist) e))  ; return e to a Maxima list
       (setq e ($poly_reduced_grobner e x)) ;triangularize equations
       (setq e ($expand e 0 0)) ;I think poly_reduced_grobner returns unsimplified expressions
       (setq e ($setify e)) ;convert both e and x to sets.
       (setq x ($setify x))
       (setq e (triangularize-eqs e x)) ; group equations in to a list of sets with the same unknowns
       (setq sol (solve-triangular-system (cdr e) (cdr x))) ;dispatch solve-triangular-system
       (setq sol (mapcar #'(lambda (q) (cons '(mlist) q)) sol))
       (if sol (simplifya (cons '(mlist) sol) t) ee)))
