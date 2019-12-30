;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations and systems of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/


;;; Allow %rnum to only be set to a nonnegative integer.
(defun nonnegative-integer-assign (a b) "merror when b isn't a nonnegative integer"
	(when (or (not (integerp b)) (< b 0))
        (merror "The value of ~M must be a nonnegative integer, not ~M ~%" a b)))

(setf (get '$%rnum 'assign) #'nonnegative-integer-assign)

;;; Standard $linsolve bypasses $solve and calls solvex. That requires $linsolve/solvex to duplicate
;;; some of the features of $solve (argument checking and non-atom solve, for example). Instead, let's
;;; route linsolve through $solve. Not sure why, but standard $linsolve sets $ratfac to nil.

;;; Eventually standard linsolve calls tfgeli. But there is a 2006 bug (#963: linsolve incorrect result)
;;; that has gone unfixed for over 14 years. There was, I think, a great deal of effort that went into
;;; tfgeli--somebody ought to fix bug #963. For now, we workaround this bug by calling our linsolve.

;;; linsolve needs to be OK with non-mapatom unknowns...

;;; This code needs to support globalsolve & programmode.

(defun $linsolve (e x) "Solve list of linear equations e for the list of unknowns x."
     ;(mtell "Top of my linsolve ~%")
     (mfuncall '$reset $%rnum_list) ; reset %rnum_list to default.
     (let ((mat) (sol nil) (g) (xx nil) (nonatom-subs nil) ($scalarmatrixp nil))
		 	    ;; Remove '(mlist), ratdisrep, and remove duplicates in list of unknowns.
          ;; We don't want x & rat(x) to be distinct variables, so we ratdisrep.
          (setq x (remove-duplicates (mapcar #'$ratdisrep (cdr x)) :test #'alike1 :from-end t))
				  (dolist (z x) ; substitute gensyms for nonmaptoms--collect these subs in a llist nonatom-subs
					   (cond (($mapatom z)
                      (push z xx))
                   (t
						          (setq g (gensym))
											(push g xx)
						          (setq g (take '(mequal) z g))
							     	  (setq e ($substitute g e))
							      	(push g nonatom-subs))))
					(setq x (cons '(mlist) (reverse xx)))

          ;; check that equations are all linear (affine) in the variables x.
          (when (some #'(lambda (q) (not ($affine_p (meqhk q) x))) (cdr e))
             (merror (intl:gettext "Linsolve: equations must be linear")))

          ;; construct a triangularized list of equations:
				  (setq mat ($triangularize ($augcoefmatrix e x)))
		      (setq sol (take '(mnctimes) mat ($transpose ($append x (take '(mlist) 1)))))
					(setq sol (reverse (mapcan #'cdr (cdr sol))))
          (setq x (reverse (cdr x)))

          ;; solve the triangular system and revert the notatom subsitutions
          (setq sol (solve-triangular-linear-system sol x nil $linsolve_params $backsubst))
          (setq sol (simplifya (cons '(mlist) sol) t))
          (dolist (sx nonatom-subs)
             (setq sol ($substitute ($reverse sx) sol)))
          sol))

(defun next-rnum-variable () "Increment %rnum, create new %rnum variable, push into %rnum_list, and
  return next %rnum variable"
    (let ((g ($concat '$%r $%rnum)))
      (incf $%rnum)
      (setq $%rnum_list ($cons g $%rnum_list))
      g))

(defun solve-triangular-linear-system (eqs vars &optional (subs nil) (parametrize-free-vars t) (backsubst t))
     (setq eqs (mapcar #'sratsimp eqs))
     ;(displa `((mequal) eqs ,(cons '(mlist) eqs)))
     ;(displa `((mequal) vars ,(cons '(mlist) vars)))
     (let ((e) ($listconstvars nil) (solx) (x) (svars))
       (cond ((null eqs) ; no more equations
              (cond ((and vars $linsolve_params) ; parametrize free variables
                      (append subs (reverse (mapcar #'(lambda (s) (take '(mequal) s (next-rnum-variable))) vars))))
                     (t
                       subs))) ;no more equations, no more unknowns!

              ((zerop1 (first eqs)) ; first equation vanishes--move on to next equation
                (when $linsolvewarn
                  (mtell (intl:gettext "Linsolve: dependent equations eliminated ~%")))
                (solve-triangular-linear-system (rest eqs) vars subs parametrize-free-vars backsubst))

              ((null vars) ; no unknowns but remaining equations
                  (setq eqs (mapcar #'(lambda (s) (take '($notequal) 0 s)) eqs))
                  (setq eqs (mapcar #'(lambda (s) (if ($lfreeof $%rnum_list s) s t)) eqs))
                  (setq eqs (simplifya (cons '(mand) eqs) t))
                  (setq eqs (let (($opsubst t)) ($substitute 'mnotequal '$notequal eqs)))
                  (mtell (intl:gettext "Linsolve is assuming ~M ~%") eqs)
                  nil)

              (t
                (setq e (pop eqs))
                (setq x (pop vars))
                (cond (($freeof x e) ; equation doesn't depend on x, so x is a free variable.
                       (push e eqs) ;haven't yet solved e for x, so push e back into eqs.
                       (when parametrize-free-vars
                              (setq solx (take '(mequal) x (next-rnum-variable)))
                              (setq subs (cons solx subs))
                              (when backsubst
                                (setq eqs (mapcar #'(lambda (s) ($substitute solx s)) eqs)))))
                      (t
                          (when parametrize-free-vars
                            (setq svars nil)
                            (dolist (xk vars)
                                (when (not ($freeof xk e))
                                   (push xk svars)
                                   (setq solx (take '(mequal) xk (next-rnum-variable)))
                                   (setq e ($substitute solx e))
                                   (setq subs (cons solx subs))
                                   (when backsubst
                                      (setq eqs (mapcar #'(lambda (s) ($substitute solx s)) eqs)))))
                             (dolist (sk svars)
                                 (setq vars (delete sk vars))))


                          (setq solx (polynomial-solve e x)) ;solx is a Maxima list!
                          (setq solx ($first solx))
                          (setq subs (cons solx subs))
                          (when backsubst
                              (setq eqs (mapcar #'(lambda (s) ($substitute solx s)) eqs)))))
                  (solve-triangular-linear-system eqs vars subs parametrize-free-vars backsubst)))))
