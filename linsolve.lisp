
;;; Standard $linsolve bypasses $solve and calls solvex. That requires $linsolve/solvex to duplicate
;;; some of the features of $solve (argument checking and non-atom solve, for example). Instead, let's
;;; route linsolve through $solve. Not sure why, but standard $linsolve sets $ratfac to nil.

;;; Eventually standard linsolve calls tfgeli. But there is a 2006 bug (#963: linsolve incorrect result)
;;; that has gone unfixed for over 14 years. There was, I think, a great deal of effort that went into
;;; tfgeli--somebody ought to fix bug #963. For now.we workaround this bug by calour own linsolve.

;;; linsolve needs to be OK with non-mapatom unknowns...

;;; This code needs to support globalsolve & programmode.

(defun $linsolve (e x)
     (let (($ratmx t) (mat) (sol nil) (s) (ssol nil) (k 0) (g) (vars nil) (nonatom-subs nil) ($scalarmatrixp nil))
		 	    (setq x (copy-list (cdr x)))  ;cdr removes (mlist). Is copy-list needed? Not sure.
				  (dolist (z x)
             (setq ($ratdisrep z))
					   (cond ((not ($mapatom z))
						          (setq g (gensym))
											(push g vars)
						          (setq g (take '(mequal) z g))
							     	  (setq e ($substitute g e))
							      	(push g nonatom-subs))
									 (t (push z vars))))

					(setq x (cons '(mlist) (reverse vars)))
				  (setq mat ($augcoefmatrix e x))
		    	(setq mat ($rat ($triangularize mat)))
		      (setq sol (take '(mnctimes) mat ($rat ($transpose ($append x (take '(mlist) 1))))))
					(setq sol (reverse (mapcan #'cdr (cdr sol))))
          (setq k (length x))
					(while (zerop1 ($ratdisrep (car sol))) ; remove equation(s) 0 = 0.
					   (incf p)
					   (pop sol))
			    (setq x (reverse (cdr x)))
					(while (and sol (> k -1))
					  (setq v ($ratdisrep (pop x)))
						(cond (($freeof v ($ratdisrep (first sol)))
						   	   (decf k)
									 (setq s (take '(mequal) v ($new_variable '$real)))
									 (push s ssol))
								 (t
									 (setq q ($ratdisrep (pop sol)))
					         (setq s (polynomial-solve q v)) ;call polynomial-solve -- it returns a mequal expression
				      		 (push (cadr s) ssol)))
					   (when $backsubst
						     (setq sol (mapcar #'(lambda (w) ($substitute s w)) sol))))

					(setq ssol (simplifya (cons '(mlist) ssol) t))
					(dolist (g nonatom-subs)
						(setq ssol ($substitute ($lhs g) ($rhs g) ssol)))
					ssol))
