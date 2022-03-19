;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

;;; convert a^b --> exp(b * log(a)), where a is freeof x and b isn't freeof x.
(defun to-exp-base (e x)
   (cond (($mapatom e) e)
	        ((and (mexptp e) (not (eql (second e) '$%e)) ($freeof x (second e)) (not ($freeof x (third e))))
				 	    (take '(mexpt) '$%e
							     (mul
								     (take '(%log) (to-exp-base (second e) x))
							       (to-exp-base (third e) x))))
				    (t (simplifya (cons (list (caar e)) (mapcar #'(lambda (q) (to-exp-base q x)) (cdr e))) t))))

(defun equation-extra-simplify (e x)
   (cond (($mapatom e) e)
	       ((mtimesp e)
			 	   (setq e (mapcar #'(lambda (q) (if ($freeof x q) 1 q)) (cdr e)))
					 (simplifya (cons '(mtimes) e) t))
				((and (mexptp e) (mnump (third e)) (mgrp (third e) 0)) ; do z^n --> z when n is a positive mnump
		 	 	   (equation-extra-simplify (second e) x))

				(t e)))

;;; This function solves x*exp(x) = constant. The match to x*exp(x) must be explicit; for example,
;;; lambert-w-solve is unable to solve x*exp(x)/2 = 10. When no solution is found, return nil. Of course,
;;; this function could be extended to solve more equations in terms of the Lambert W function.

(defun lambert-w-solve (e x m)
  (let ((q) (ee) (expargs) (ker) (g (gensym)) (sol) (zz) (ss) (mu) (gg (gensym)))
	  (when (or t $solveverbose)
		    (mtell "Top of lambert-w-solve: e = ~M x = ~M ~%" e x))
    (setq e (to-exp-base ($ratdisrep e) x)) ;convert a^b --> exp(b * log(a))
		;; find the subexpressions of e of the form exp(X), where X depends on x.

	  (setq q (kernelize-fn e
			   #'(lambda (s) (and (mexptp s) (eql '$%e (second s)) (not ($freeof x (third s)))))))

		(setq ee (first q))
		(setq expargs (second q))
		(setq expargs (mapcar #'car expargs))
    ;; Is there a subexpression exp(X) of e such that substituting g for
		;; exp(X)/X yields an expression that is free of x?
	  (while expargs
				 (setq ex (pop expargs))
				 ;(setq ker (third ex))
				 (setq ker ex)
				 (setq ee ($ratsubst g (third ex) e))
				 (setq ker ($ratsubst g (third ex) ker))
				 (setq ee ($ratsubst gg ker ee))
				 (mtell "ee = ~M ker = ~M ~%" ee ker)
				 (merror "TAF")
				 (when ($freeof x ee)
						(mtell "Success ee = ~M ~%" ee)
				    (setq expargs nil))) ;found it, so quit!

			(cond (($freeof x ee) ;we win!
			        (mtell "ker = ~M ~%" ker)
	    		    (setq sol ($solve ee g))
							(setq sol (mapcar #'$rhs (cdr sol)))
							(cond ((eql $solve_inverse_package $single_valued_inverse)
						      	  (setq sol (mapcar #'(lambda (q) (if (zerop1 q) 0 (take '($lambert_w) q))) sol)))
										(t
	    			          (setq sol (mapcar #'(lambda (q) (if (zerop1 q) 0
					              (take '(%generalized_lambert_w) (my-new-variable '$integer) q)))
						     			sol))))

              (setq sol (mapcan #'(lambda (s) (cdr (solve-single-equation (mm= ker s) x))) sol))
					    (setq sol (simplifya (cons '(mlist) sol) t))
						  (multiplicities-fix-up sol m)
							sol)

						(t nil))))
