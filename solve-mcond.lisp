
;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

(defun mcond-p (e) "True iff e the operator of e is mcond."
  (and (consp e) (consp (car e)) (eql 'mcond (caar e))))

(defun solve-mcond (e x m use-trigsolve)
  (let ((subs nil) (ker) (kker) (g) (sol) (solx) (ssol) (cnd) (ifcnd) (xcnd t) (xcnd-save) (mx))
	      (setq e (kernelize-fn e #'(lambda (q) (and (mcond-p q) (among x q))) nil))
        (setq subs (second e))
		    (setq e (first e))
	    	(cond ((and (not (cdr subs)) (not (among x e))) ;subs has length 1 & e is kernelized
	    	        (setq ker (car (first subs)))
		    	    	(setq g (cdr (first subs)))
		    	    	(setq sol (let (($solveexplicit t)) (solve-single-equation e g m use-trigsolve)))
								(setq sol (cdr sol)) ;remove '(mlist)
		        		(pop ker) ;remove (mcond)
		      		  (dolist (sx sol)
		        	    	(setq kker (copy-list ker))
			              (while kker
							 				 (setq ifcnd (pop kker))

                       (setq ifcnd (take '(mand) (in-domain ifcnd (list x))  ifcnd))
                       (setq xcnd-save (take '(mand) xcnd (take '(mnot) ifcnd)))
				               (setq ifcnd (simplifya (list '(mand) xcnd ifcnd) t))
                       (setq xcnd xcnd-save)
					        		 (setq eq (pop kker)) ; the "then" part of "if."
						        	 (setq solx (solve-single-equation (sub eq ($rhs sx)) x m use-trigsolve))
							         (setq solx (filter-solution-x solx ifcnd))
							         (setq ssol (append (cdr solx) ssol))
							         (setq mx (append (cdr $multiplicities) mx))))
                (simplifya (cons '(mlist) ssol) t))
				     (t nil))))
