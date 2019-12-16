;; Author: Barton Willis
;; Common Lisp/Maxima code for symbolic solutions of equations.

;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.

(in-package :maxima)

;;; Unrelated to solving equations...
(dolist (e (list '$max '%acosh '%cos '%cosh '%lambert_w '%log '%sin '%sinh 'mabs 'rat))
	(setf (get e 'msimpind) (list e 'simp)))

;;; When $use_to_poly is true, dispatch the to_poly_solver after attempting other methods;
;;; when $use_to_poly is false, never dispatch the to_poly_solver.
(defmvar $use_to_poly t)

;;; When $solve_ignores_conditions is true, ....?
(defmvar $solve_ignores_conditions nil)

(eval-when
	(:compile-toplevel :load-toplevel :execute)
	($load "to_poly_solve")
	($load "function-inverses.lisp")
	(setq $solve_inverse_package $multivalued_inverse)
	($load "trig_identities.lisp")
	($load "polynomial-solve.lisp")
	($load "in-domain.lisp")
	($load "grobner"))

;;; This code fixes polynomialp. When polynomialp is fixed, this code should be expunged.
(defun polynomialp (p vars coeffp exponp)
  (or
   (mfuncall coeffp p)
   (if (member p vars :test #'alike1) t nil)
   (and (op-equalp p 'mtimes 'mplus)
	(every #'(lambda (s) (polynomialp s vars coeffp exponp)) (margs p)))
   (and (op-equalp p 'mexpt) (polynomialp (car (margs p)) vars coeffp exponp)
	(mfuncall exponp (cadr (margs p))))))

(declare-top (special
			  *var
		      *roots ;alternating list of solutions and multiplicities
		      *failures
			  xm* xn* mul*))

;; In expression e, convert all floats (binary64) and bigfloats to their exact rational value
;; and put that value inside a labeled box. Doing this allows solve to preserve the exact
;; value of floats.

(defmvar *float-box-label* (gensym))
(defmvar *big-float-box-label* (gensym))

(defun keep-float (e) "Convert floats and big floats to rational form and put them inside labeled boxes."
    (cond
        (($mapatom e)
         (cond ((floatp e)
                (take '(mlabox) ($rationalize e) *float-box-label*))
               (($bfloatp e)
                (take '(mlabox) ($rationalize e) *big-float-box-label*))
               (t e)))
        (t (simplifya (cons (list (caar e)) (mapcar #'keep-float (cdr e))) t))))

;; In expression e, convert all labeled boxes that contain floats but to float form.
(defun unkeep-float (e) "Convert numbers in labeled float boxes back to float numbers."
    (cond
        (($mapatom e) e)
        ((and (consp e) (consp (car e)) (eql 'mlabox (caar e)) (third e)) ;it's a labeled box
         (cond ((eql *float-box-label* (third e)) ($float (second e))) ;unbox and convert to ieee float
               ((eql *big-float-box-label* (third e)) ($bfloat (second e))) ;unbox and convert to bigfloat
              (t e)))
        (t (simplifya (cons (list (caar e)) (mapcar #'unkeep-float (cdr e))) t))))

;; Flags that I've ignored: $solveexplicit (not entirely), $dispflag, $programmode, and $breakup.

;; The top level function solve function:
;;   (a) reset multiplicative to default
;;   (b) creates new super context--all assumptions made during solve are removed after exiting
;;   (c) expunge constant variables and duplicates from list of variables
;;   (d) checks for non equal inequations, and signals an error when found
;;   (e) expunge duplicate equations
;;   (f) does gensym substitutions for solving for nonatoms
;;   (g) dispatches appropriate lower level solve function
;;   (h) reverts gensym substitutions for nonatom solve

(defun $solve (eqlist &optional (varl nil))
  (mfuncall '$reset $multiplicities)

  (let ((cntx ($supcontext)) ;make asksign and friends data vanishes after exiting $solve.
		(nonatom-subst nil)	(sol) (g) ($domain '$complex) ($negdistrib t))
	   ;; Allow sets for eqlist and varl.
	   (when (and (consp eqlist) (consp (car eqlist)) (eql '$set (caar eqlist)))
		   (setq eqlist ($listify eqlist)))

	   (when (and (consp varl) (consp (car varl)) (eql '$set (caar varl)))
		   (setq varl ($listify varl)))

	   ;; When varl is empty, solve for the nonconstant variables. Set varl to a CL list and remove
	   ;; duplicates. For variable ordering, we take the same order as listofvars.

	   (setq varl
			 (remove-duplicates
			 	(cond
					((null varl) (let (($listconstvars nil)) (cdr ($listofvars eqlist))))
					(($listp varl) (cdr varl))
					(t (list varl)))
			  :from-end t))

	 ;; Create the equation list (this is a CL list, not Maxima list). For a inequation that isn't equality,
	 ;; throw an error.
	 (setq eqlist (if ($listp eqlist) (cdr eqlist) (list eqlist)))

	 (setq eqlist (mapcar #'$ratdisrep eqlist)) ;new--fixes bugs in rtest_matrixexp.

	 (when (some #'(lambda (q) (and (consp q) (consp (car q))
									(member (caar q) (list 'mnotequal 'mgreaterp 'mlessp 'mgeqp 'mleqp) :test #'eq))) eqlist)
		 (merror (intl:gettext "Solve: cannot solve inequalities.~%")))

	 ;; Some sanity checks and warning messages.
	 (when (and (null eqlist) $solvenullwarn)
	   (mtell (intl:gettext "Solve: equation list is empty, continuing anyway.~%")))

	 (when (some #'mnump varl)
	   (merror (intl:gettext "Solve: all variables must not be numbers.~%")))

	 ;; (setq eqlist (remove-if #'zerop1 eqlist))
	 ;;Eliminate duplicate equations.
	 ;;;(setq eqlist (cdr (simplifya (cons '($set) eqlist) t)))

	 ;; stuff for solving for nonatoms. Should check for problems such as solve([xxx,yyy],[f(x),x])
	 (dolist (xxx varl)
		 (cond (($mapatom xxx)
				(push (take '(mequal) xxx xxx) nonatom-subst))
		       (t
			    (setq g (gensym))
			    (push (take '(mequal) xxx g) nonatom-subst)
			    (setq eqlist (mapcar #'(lambda (q) ($ratsubst g xxx q)) eqlist))
			    ;; is freeof xxx sufficiently strong?
			    (when (some #'(lambda (q) (not ($freeof xxx q))) eqlist)
			 	 (merror (intl:gettext "Solve: Cannot solve for non-atom.~%"))))))

	 (setq nonatom-subst (reverse nonatom-subst))
	 (setq varl (mapcar #'third nonatom-subst))  ;was $rhs
	 ;;(setq nonatom-subst (mapcar #'(lambda(q) (take '(mequal) ($rhs q) ($lhs q))) nonatom-subst))
	 (setq nonatom-subst (mapcar #'$reverse nonatom-subst))
	 (push '(mlist) nonatom-subst)

	 (unwind-protect
	  (progn
		  (cond

			  ((null varl)
			   (when $solvenullwarn
				   (mtell (intl:gettext "Solve: variable list is empty, continuing anyway.~%")))
			   (if (every #'zerop1 eqlist) '$all (take '(mlist))))

			  ((and (null (cdr varl)) (null (cdr eqlist))) ; one equation, one unknown
			   (setq eqlist (keep-float (car eqlist)))
			   (setq sol ($substitute nonatom-subst (solve-single-equation eqlist (car varl))))
			   (setq eqlist (unkeep-float eqlist))
		 	   (setq sol (unkeep-float sol)))

			  ((null (cdr varl)) ;one unknown, more than one equation
			   (redundant-equation-solve (cons '(mlist) eqlist) (car varl)))

			  ;; Multiple equations: SOLVEX.
			  (t
			   (setq sol (solvex eqlist varl nil nil))
			   (when (not (every #'$listp (cdr sol))) ;;this is unfortunate?
				   (setq sol `((mlist) ,sol)))
				(setq sol ($substitute nonatom-subst sol))
			    sol)))

	  ($killcontext cntx))))

;;; Do basic simplifications of an equation. In particular:
;;;    (i) convert a=b to a-b
;;;    (ii) convert to general form
;;;    (iii) when solveradcan is true, apply radcan
;;;    (iv) when n is a positive integer, convert e^n --> e and modify the multiplicity
;;;    (v) ratsimp and extract the numerator
;;;    (vi) apply the Pythagorean identities (things like sin(x)^2 + cos(x)^2 --> 1).

;;; We return a CL list of both the simplified expression and the modified multiplicity.

;;; Extracting the numerator can, of course, introduce spurious solutions.

;;; Factoring an equation isn't an automatic win--for example, factoring x^107-1 is a loser.
;;; The option variable solvefactors controls factoring, but it's uncertain when the factoring
;;; happens. This function does not factor. It's unclear to me exactly when in the solve
;;; process that radcan should be applied.

;;; Additionally, we could remove factors from e that don't depend on the solve variable(s). But
;;; to do that, the solve variables would need to be an argument.

(defun equation-simplify (e &optional (m 1))
	(setq e ($ratdisrep (meqhk e))) ;do a=b -->a-b & convert to general form

	(when $solveradcan ;unsure when is the best time to do this...let's get it done.
		(setq e ($radcan e)))

	(cond
		((and (mexptp e) (integerp (third e)) (> (third e) 0)) ; do z^n --> z when n is a positive integer
		 (equation-simplify (second e) (mul m (third e))))

		(t
		 (setq e ($num (sratsimp e)))
		 (setq e (apply-identities e *pythagorean-identities*))
		 (setq e (convert-from-max-min-to-abs e)) ; by itself, this doesn't do all that much.
		 (list e m))))


(defun to-poly-fixup (cnd)
	(let ((q))
		(setq q ($substitute #'(lambda (s) (take '(mgreaterp) s 0)) '$isnonnegative_p cnd))
		(setq q ($substitute #'(lambda (a b) (mnqp a b)) '$notequal q))
		($substitute #'(lambda (a b) (mnqp a b)) 'mnotequal q)))

(defun my-ask-boolean (cnd)
	(let ((answer (if $solve_ignores_conditions t (mfuncall '$maybe (to-poly-fixup cnd)))))
		  (cond
			 ((or (eql answer t) (eql answer nil)) answer)
			 (t
			  (setq answer (retrieve `((mtext) ,(intl:gettext "Is ") ,cnd ,(intl:gettext "?")) nil))
			  (cond
				  ((member answer '($yes |$y| |$Y|) :test #'eql)

				   ;(mapcar #'(lambda (q) (mfuncall '$assume q)) cnd)
				   t)

				  ((member answer '($no |$n| |$N|) :test #'eql) nil)

				  (t
				   (mtell (intl:gettext "Acceptable answers are yes, y, Y, no, n, N. ~%"))
				   (my-ask-boolean cnd)))))))

;; Remove the members of sol that do not satisfy cnd. The members of the CL list sol have
;; the form solution.multiplicity.
;; The Maxima expression cnd is generally a conjunction of Maxima predicates. For each solution, we
;; substitute sx in to cnd and call my-ask-boolean.

(defun filter-solution (sol cnd) "Remove the members of sol that do not satisfy cnd"
	(let ((checked-sol nil))
		 (dolist (sx sol)
			 (when (my-ask-boolean ($substitute (car sx) cnd))
				 (push sx checked-sol)))
		 (reverse checked-sol)))

;; Solve the equation e=0 for x, where e is a mtimes expression. Actually, effectively the equation is e^m = 0, so
;; m is the multiplicity so far in the solving process. The list cnd has conditions on the solution.

;; When e = e1*e2* ... * en, solve e1=0, e2=0, ... en = 0.  Remove the duplicates from the union of the solutions, and
;; remove those solutions that do not satisfy cnd. One problem is when one of the solutions is all, but there is a condition
;; on the solution--something like solve ((sin(x)^2 + cos(x)^2-1)*(1/x),x). I'm not sure how to fix this.

(defun product-solver (e x m use-trigsolve cnd) "Solve e=e1*e2*...*en for x"
	;(mtell "using product solve ~%")
	;(displa `((mequal) cnd ,cnd))

	(let ((solx) (sol nil) (wmul))
		 (setq e (cdr e))
		 (catch 'found-all
				(dolist (ex e)
					(setq solx (solve-single-equation ex x m use-trigsolve))
					(when (eql solx '$all)
						(setq sol '$all)
						(throw 'found-all nil))

					;; the conditional is a workaround for some other bug, I think.
					(setq solx (cdr solx))
					(setq wmul (if ($listp $multiplicities) (cdr $multiplicities)
								   (mapcar #'(lambda (q) (declare (ignore q)) '$not_yet_set) solx)))


					(dolist (sx solx) ;build an association list of the form solution.multiplicity
						(push (cons sx (pop wmul)) sol))))
		 (cond
			 ((eql sol '$all)
				sol)
			 (t
			  (setq sol (remove-duplicates sol :test #'alike1 :key #'car :from-end t))
			  (setq sol (filter-solution sol cnd))
			  (setq $multiplicities (simplifya (cons '(mlist) (mapcar #'cdr sol)) t))
			  (simplifya (cons '(mlist) (mapcar #'car sol)) t)))))

(defvar $the_unsolved nil) ;;this is purely for debugging

(defun solve-single-equation (e x &optional (m 1) (use-trigsolve t))
	(let ((cnd)) ;did have ($assume_pos nil), but why?
		 (setq e (equation-simplify e m))
		 (setq m (second e))
		 (setq e (first e))

		 ;; maybe this should be before equation-simplify, but that causes slowness.
		 (setq cnd (if $solve_ignores_conditions t (in-domain e)))
		 ;;(displa `((mequal) eeee ,e))
		 (cond

			 ((or (zerop1 e) (and (consp e) (consp (car e)) (eql 'mlabox (caar e)) (zerop1 (unkeep-float e))))
			  (setq $multiplicities (simplifya (list '(mlist) '$inf) t))
			  (take '(mlist) (take '(mequal) x ($new_variable (if ($featurep x '$complex) '$complex '$real)))))

			((and ($mapatom x) ($polynomialp e (list '(mlist) x) #'(lambda (q) ($freeof x q)))) ;solve polynomial equations
			   (polynomial-solve e x m))

			((solve-mexpt-equation e x m use-trigsolve))

			((mtimesp ($factor e))
			  (product-solver ($factor e) x m use-trigsolve cnd))

			((solve-by-kernelize e x m))

		    ;;;;((and use-trigsolve (trigsolve e x)))

			((lambert-w-solve e x m))

			((and $use_to_poly (new-to-poly-solve e x cnd)))

			($solveexplicit ;give up & return the empty set
			  (mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning the empty list.~%") e x)
			  (push (list '(mlist) e x) $the_unsolved)
			  (setq $multiplicities (take '(mlist) m))
			  (take '(mlist)))

			(t
			  ;; Integration is sensitive to what happens for unsolved equations. Try
			  ;; laplace(exp(-8*exp(u)),u,v) after changing the return value to 0 = e.
			  ;; Standard Maxima chooses to solve for some equation kernel, but I don't know
			  ;; how it chooses the kernel--so use a silly heuristic for choosing a kernel.
			  (mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning an implicit solution.~%") e x)
			  (push (list '(mlist) e x) $the_unsolved)
			  (let ((ker))
				   (setq ker (if (and (mplusp e) (not ($freeof x (first (last e))))) (first (last e)) x))
				   (setq $multiplicities (take '(mlist) m))
				   (take '(mlist) (take '(mequal) ker (sub ker e))))))))

;; This function attempts to identify a term F(x) such e is a function of only F(x). And when it is,
;; first solve for F(x), and second solve for x. The function F has a known inverse. Unifying the
;; cases, for example,  of F(x) = x^a and F(x) = cos(x) is problematic. Maybe these cases can be unified,
;; but we'll handle the case when F is a
;; power function separately.

(defun solve-by-kernelize (e x m)
	(let ((kernel-p #'(lambda (q) (and (consp q)
									   (consp (car q))
									   (gethash (caar q) $solve_inverse_package)
									   (not ($freeof x q)))))
		  ($solveexplicit t) (z) (sol) (fun-inverse) (ker) (fun) (acc nil) (q)
		  (mult-acc nil) (xxx) (mult-save))

		 (setq e (kernelize e kernel-p))
		 (cond ((and (null (cdr (second e))) ($freeof x (first e)))
				(setq ker (second e))
				(setq e (first e))
				(setq z (cdar ker))
				(setq ker (caar ker))
				(setq fun (caar ker))
				(setq sol ($solve e z))
				(setq mult-save (mapcar #'(lambda (q) (mult m q)) (cdr $multiplicities)))
				(setq sol (mapcar #'third (cdr sol)))  ;third = $rhs
				(setq fun-inverse (gethash fun $solve_inverse_package))
				;; after this, sol is a list of lists
				(setq sol (mapcar #'(lambda (q) (apply fun-inverse (list q))) sol))
				(setq mult-save (mapcar #'(lambda (a b)
											(mapcar #'(lambda (c) (declare (ignore c)) b) a)) sol mult-save))

				(setq sol (reduce #'append sol))
				(setq ker (second ker))
				(setq mult-save (reduce #'append mult-save))
				(setq sol (mapcar #'(lambda (q) (take '(mequal) ker q)) sol))

				(dolist (sx sol)
					(setq q ($solve sx x))
					(push (cdr q) acc)
					(setq xxx (pop mult-save))
					(push (mapcar #'(lambda (q) (mult xxx q)) (cdr $multiplicities)) mult-acc))

				(setq acc (reverse acc))
				(setq acc (reduce #'append acc))
				(setq mult-acc (reduce #'append mult-acc))
				(setq mult-acc (reverse mult-acc))

				(setq $multiplicities (simplifya (cons '(mlist) mult-acc) t))
				(simplifya (cons '(mlist) acc) t))
			 (t nil))))

(defun kernelize (e kernel-p &optional (subs nil))
	(let ((g (gensym)) (x nil) (op))
		 (cond
			 (($mapatom e) (list e subs))

			  ((funcall kernel-p e) ;it's a kernel
			   (setq x (assoc e subs :test #'alike1)) ;is it a known kernel?
			   (cond (x
					  (list (cdr x) subs)) ;it's a known kernel--use the value from the association list subs
				   	 (t
				   	  (list g (acons e g subs))))) ;it's unknown--append a new key/value to subs

			 (t ; map kernelize onto the argument list and build up the association list subs
			  (setq op (list (caar e)))
			  (setq e (cdr e))
			  (dolist (xk e)
				  (setq xk (kernelize xk kernel-p subs))
				  (push (first xk) x)
				  (setq subs (second xk)))
			  (list (simplifya (cons op (reverse x)) t) subs)))))

(defun homogeneous-linear-poly-p (e vars)
	(setq e ($rat e))
	(dolist (x vars)
		(setq e (sub e (mul x ($ratcoef e x)))))
	(zerop1 ($ratdisrep e)))

;; Try to find a kernel blob1^blob2 in ee such that ee is a function of constants (thing free of x)
;; and blob1^blob2. Solve for blob1^blob2 and attempt to invert blob1^blob2.

(defun solve-mexpt-equation (ee x m use-trigsolve)
	(declare (ignore m use-trigsolve)) ;likely bug
	;(mtell "top of solve-mexpt-equation ~M  ~%" ee)
	(setq ee ($expand ee))
	;(displa `((mequal) ee ,ee))
	(let ((nvars) (kernels) (ker) (sol nil) (e ee)  (zzz)
				  (inverse-function nil) ($use_to_poly nil))

		 (setq e (kernelize ee #'(lambda (q) (and (mexptp q) (not ($freeof x q))))))
		 (mapcar #'(lambda (q) (push (car q) kernels) (push (cdr q) nvars)) (second e))

		 (cond ((and (second e) (not (cdr (second e))) ($freeof x (first e)))
				;(setq nvars (car (mapcar #'cdr (second e))))
				(setq nvars (car nvars))
				(setq ker (first kernels))
				(setq inverse-function
					  (cond (($freeof x (second ker)) ;looking at a^X = b
							 (setq zzz (second ker))
							 (setq ker (third ker))
							 (gethash 'exponential-inverse $solve_inverse_package))

					  	    (($freeof x (third ker)) ;looking at X^a = b
							 (setq zzz (third ker))
							 (setq ker (second ker))
							 (gethash 'power-inverse $solve_inverse_package))

						    ((alike1 (second ker) (third ker))
							 (setq zzz 0)
							 (setq ker (second ker))
							 (gethash 'lambert-like-inverse $solve_inverse_package))))

				(when inverse-function
					(setq sol ($solve (first e) nvars))
					(cond
						((eql sol '$all) '$all)
						(t
						 (setq sol (mapcan #'(lambda (q) (funcall inverse-function ($rhs q) zzz)) (cdr sol)))
						 ;; not sure what to do when solve returns $all? It's a mess--don't want an error.
						 (setq sol (mapcan #'(lambda (q) (let ((sq ($solve (sub ker q) x)))
																(if ($listp sq) (cdr sq) (list sq)))) sol))
						 (setq sol (simplifya (cons '(mlist) sol) t))))))

			 	((and (eql 2 (length nvars)) ($freeof x (first e)) (homogeneous-linear-poly-p (first e) nvars))
				 (let ((k1) (a) (k2) (b) (xx) (yy))
					  ;(mtell "doing new mexpt solver ~%")
					  (setq e (first e))
					  (setq k1 ($ratcoef e (first nvars)))
					  (setq a (second (first kernels)))
					  (setq xx (third (first kernels)))
					  (setq k2 ($ratcoef e (second nvars)))
					  (setq b (second (second kernels)))
					  (setq yy (third (second kernels)))

					  ;; We're looking at k1 * a^XX + k2 * b^YY = 0, where XX & YY depend on x.  Transform this to
					  ;; exp(log(k1) + log(a)*XX) + exp(log(k2) + log(b)*YY) = 0. And transform this to
					  ;; exp(log(k1) + log(a)*XX - log(k2) - log(b)*YY) = -1.

					  ;;(displa `((mlist) k1 ,k1 k2 ,k2 X ,xx  y ,yy a ,a b ,b))

					  (cond ((and ($freeof x a) ($freeof x b))

							 (setq inverse-function (gethash 'exponential-inverse $solve_inverse_package))
							 (setq sol ($solve (add
												(take '(%log) k1)
												(mul (take '(%log) a) xx)
												(mul -1 (take '(%log) k2))
												(mul -1 (take '(%log) b) yy)
												(mul -1 (car (funcall inverse-function -1 '$%e)))) x)))))))

		 sol))

(defun new-to-poly-solve (e x cnd)
	(let ((q) (eq) (nonalg-sub) (nvars) (sol) (ek) (cx) ($algexact t) (checked-sol nil))
		 (setq q (let ((errcatch t) ($errormsg nil)) (ignore-errors ($to_poly e (list '(mlist) x)))))

		 ;(mtell "doing to poly solve")

		 (when (and q (< ($length ($third q)) 2))
			 (setq checked-sol (list '(mlist)))
			 (setq eq ($first q))
			 (setq cnd (take '(%and) cnd (simplifya (cons '(%and) (cdr ($second q))) t)))
			 (setq nonalg-sub ($third q))

			 (setq nvars ($subset (set-of-vars eq) #'(lambda (q) (and (symbolp q) (get q 'general-gentemp)))))
			 (setq nvars ($adjoin x nvars))
			 (setq nvars ($listify nvars))


			 (setq sol (let (($algexact t)) (cdr ($algsys eq ($listify nvars)))))
			 (cond ((and sol ($emptyp nonalg-sub))
					;(mtell "branch 1 ~%")
					(dolist (sk sol)
						(setq cx ($substitute sk cnd))
						(setq cx (my-ask-boolean cx))
						;(setq cx (simplifya (cons '(%and) (mapcar #'(lambda (q) (mfuncall '$maybe q)) (cdr cx))) t))
						(when (or (eql cx t) (eql cx '$unknown))
							(setq sk (take '(mequal) x ($substitute sk x)))
							(setq checked-sol ($cons sk checked-sol)))))
				 ((and sol (or (null nonalg-sub) ($freeof x eq)))
				  ;(mtell "branch 2 ~%")
				  ;(mtell "branch 2 ~%")
				  (setq nvars ($first nvars))
				  (dolist (sk sol)
					  (setq sk (let (($use_to_poly nil)) ($solve ($first sk) nvars)))
					  (setq ek ($substitute sk nonalg-sub))
					  (setq cx ($substitute sk cnd))
					  (setq cx (my-ask-boolean cx))
					  ;;;;(setq cx (simplifya (cons '(%and) (mapcar #'(lambda (q) (mfuncall '$maybe q)) (cdr cx))) t))
					  (when (or (eql cx t) (eql cx '$maybe))
						  (setq sk ($solve ek x))
						  (setq sk ($rectform sk))
						(setq checked-sol ($append checked-sol sk))))))

			 ;(setq checked-sol (filter-solution (cdr checked-sol) (cdr cnd)))
			 ;(setq checked-sol (simplifya (cons '(mlist) checked-sol) t))

			 (when checked-sol
				 (mtell "used the to poly solver")))

		 checked-sol))

;; Standard $linsolve bypasses $solve and calls solvex. That requires $linsolve/solvex to duplicate
;; some of the features of $solve (argument checking and non-atom solve, for example). instead, let's
;; route linsolve through $solve. Not sure why, but standard $linsolve sets $ratfac to nil.

;; Eventually standard linsolve calls tfgeli. But there is a 2006 bug (#963: linsolve incorrect result)
;; that has gone unfixed for over ten years. Using $solve (and eventually $algys) fixes this bug. Possibly
;; tfgeli gives better performance--eventually it should be fixed. But until it is fixed, let's use
;; $solve/$algys.

(defun $linsolve (e x)
	(let ((sol ($solve e x)))
		 (if (and ($listp sol) (not ($emptyp sol)) ($listp ($first sol))) ($first sol) sol)))

(defun equation-complexity-guess (a b) (< (my-size a) (my-size b))) ;my-size defined in trig_identities

;;; Solve the Maxima list of expressions eqs for the symbol x. This function doesn't attempt to set the
;;; multiplicities to anything reasonable--it resets  multiplicities to the default.
(defun redundant-equation-solve (eqs x)
	;(mtell "using redundant solve ~%")
	(let ((eqset) (sol) (checked-sol nil))
		 (setq eqs (mapcar #'meqhk (cdr eqs))) ;eqs is now a CL list
		 (setq eqset (simplifya (cons '($set) eqs) t))

		 (dolist (ek eqs) ;for each equation ek, ratsubst 0 for ek and adjoin ek back into the equations
			 (when (not ($freeof x ek)) ;disallow subsitution when ek is freeof x
				 (setq eqset ($ratsubst 0 ek eqset))
				 (setq eqset ($disjoin 0 eqset))
				 (setq eqset ($adjoin ek eqset))))

		 (setq eqset (sort (cdr eqset) #'equation-complexity-guess)) ;effort to find simplest equation
		 (setq sol (let (($solveexplicit t)) ($solve (first eqset) x)))
		 ;;include only solutions that can be verified--likely this will sometimes miss legitimate solutions.
		 (push '(mlist) eqs) ;restore eqs to a Maxima list
		 (when ($listp sol) ;sol could be $all, maybe?
			 (setq sol (cdr sol))
			 (dolist (sx sol)
				 (cond ((every #'(lambda (q) (zerop1 (try-to-crunch-to-zero q))) (cdr ($substitute sx eqs)))
						(push sx checked-sol))
					   (t
						(intl:gettext (mtell "Solve: unable to verify putative solution ~M ~%" sx))))))
		 (mfuncall '$reset '$multiplicities)
		 (simplifya (cons '(mlist) checked-sol) t)))

(defun set-of-vars (e)
	(let (($listconstvars nil)) ($setify ($listofvars e))))

(defun triangularize-eqs (e x)
	;(setq e ($setify e))
	;(setq x ($setify x))
	(setq e ($equiv_classes e #'(lambda (a b) ($setequalp
											   ($intersection (set-of-vars a) x)
											   ($intersection (set-of-vars b) x)))))
	(setq e ($listify e))
	($sort e #'(lambda (a b) (< ($cardinality ($intersection (set-of-vars a) x))
										($cardinality ($intersection (set-of-vars b) x))))))

(defun list-of-list-p (e)
	(and
	 ($listp e)
	 (every #'$listp (cdr e))))

;;; eqs is a CL list of Maxima sets; vars is a CL list of symbols
(defun solve-triangular-system (eqs vars &optional (subs nil))
	(let ((e) (eeqs) (x) ($listconstvars nil) (sol) (ssol) (acc (list (list 'mlist))))
		 (cond ((null eqs)
				(when (not ($listp subs))
					(push '(mlist) subs))
				subs)
			 (t
			  (setq e (pop eqs))
			  (setq x (intersection (cdr ($listofvars e)) vars :test #'alike1))
			  (cond ((null (cdr x)) ;only one variable
					 (setq sol (cdr ($solve e (first x))))
					 (dolist (sx sol)
						 (setq eeqs (mapcar #'(lambda (q) ($substitute sx q)) eqs))
						 (setq ssol (solve-triangular-system eeqs vars (append subs (list sx))))
						 (cond ((list-of-list-p ssol)
								(setq acc ($append ssol acc)))
							 (t (setq acc ($cons ssol acc)))))
					 acc)
				  (t

					 (mtell (intl:gettext "Solve: unable to solve.~%"))
				   (if $solveexplicit (list (list 'mlist)) nil)))))))


(defun solvex (e v &optional (foo nil) (baz nil)) ;ahh, what's the meaning of the optional args? One is programmode?
	;(print `(foo = ,foo))
	;(print `(baz = ,baz))
	(declare (ignore foo baz))
	(let ((ee) (sol))
		 ;(mtell "calling solvex ~%")
		 (setq e (mapcar #'(lambda (q) (first (equation-simplify q 1))) e))
		 (push '(mlist) e)
		 (push '(mlist) v)

		 (cond
			 ;; when every member of e is a polynomial, dispatch algsys.

			 (($emptyp e)
			  `((mlist)))

			 ((every #'(lambda (q) ($polynomialp q v #'(lambda (s) ($lfreeof v s)))) (cdr e))
			  (let (($algexact nil))
				   ;(displa (mfuncall '$reset))
				   ($algsys e v))) ;previously set $solveradcan to nil, but not sure why

			 (t
			  (setq ee e)
			  (setq e ($setify e))
			  (setq v ($setify v))
			  (setq e (triangularize-eqs e v))
			  (setq sol (solve-triangular-system (cdr e) (cdr v)))
			  (if sol sol ee)))))

;;; This is the entry-level function for system level calls to solve. Solutions are pushed into the
;;; special variable *roots. Maybe this should call solve-single-equation instead of the top-level $solve?
;;; Skipping $solve and going directly to solve-single-equation would sidestep the call to supercontext--that
;;; would all assumptions made in the solve process to remain.

;;; The solve function is sometimes called from the integrate code. But the integration code doesn't tolerate
;;; things like solve(sin(x)=1/2,x) --> [x=(12*%pi*%z1+%pi)/6,x=(12*%pi*%z2+5*%pi)/6]. Thus we'll locally
;;; set $solve_inverse_package to *function-inverses-alt*.

;;; When realonly is true, the testsuite has problems. Not sure--$realonly only affects algsys, not solve. So
;;; I'm not sure...

;;; The non-user level option variable *solve-factors-biquadratic* is a silly workaround.  The testsuite has a handful
;;; of definite integration problems of the form integrate(1/(a + b*sin(x)^2,x, c,d). These lead to solving
;;; biquadratics. Standard Maxima doesn't factor the biquadratic--that results in pairs of solutions of the
;;; form +/-sqrt(XXX). For such definite integrals, factoring the biquadratic and solving yields solutions that are
;;; arguably more complex than not factoring.

;;; I think solve isn't supposed to alter $multiplicities--it's a mess.

;;; Quote from solve.lisp

;; Solve takes three arguments, the expression to solve for zero, the variable
;; to solve for, and what multiplicity this solution is assumed to have (from
;; higher-level Solve's).  Solve returns NIL.  Isn't that useful?  The lists
;; *roots and *failures are special variables to which Solve prepends solutions
;; and their multiplicities in that order: *roots contains explicit solutions
;; of the form <var>=<function of independent variables>, and *failures
;; contains equations which if solved would yield additional solutions.

(defun solve (e x ms)
	(let ((sol) (mss)
				($solve_inverse_package *function-inverses-alt*)
				($solve_ignores_conditions t)
				($use_to_poly t)
				($realonly nil)
				($negdistrib t) ;not sure about this?
				(*solve-factors-biquadratic* nil)
				(m))
		 	(setq x (if x x *var))
		 	(let (($multiplicities nil))
				 (setq sol ($solve e x)) ;what if solve returns all? It's a bug!
				 (setq sol (reverse (cdr sol)))
				 (setq m (cond (($listp $multiplicities)
								(cdr $multiplicities))
							 (t
							  (mtell "Yikes--multiplicities didn't get set ~%")
							  (mapcar #'(lambda (q) (declare (ignore q)) 1) sol)))))

		    (setq m (reverse m))
		 	(setq *roots nil)
		 	(setq *failures nil)
		 	(dolist (q sol)
				(setq mss (mul ms (pop m)))
				(cond ((and (mequalp q) (eql 0 (second q))) ;second = $lhs
					   (push q *failures)
					   (push mss *failures))
					  (t
			   	    	(push mss *roots)
				    	(push q *roots))))
		   (rootsort *roots)
		   (rootsort *failures)
		 nil))

;; This function solves x*exp(x) = constant. The match to x*exp(x) must be explicit; for example,
;; lambert-w-solve is unable to solve x*exp(x)/2 = 10. When no solution is found, return nil. Of course,
;; this function could be extended to solve more equations in terms of the Lambert W function.
(defun lambert-w-solve (e x m) "solve x exp(x) = constant where m is the multiplicity so far"
  (let ((cnst (sratsimp (sub (mult x (take '(mexpt) '$%e x)) e))))
		(cond (($freeof x cnst) ;match with x*exp(x) = cnst
			       (setq $multiplicities (take '(mlist) m))
			       (cond ((eql $solve_inverse_package $multivalued_inverse)
		   	         		(take '(%generalized_lambert_w) ($new_variable '$integer) cnst))
							    	(t (take '(%lambert_w) cnst))))
		    	(t nil))))

;; Let's make sure that the old functions solvecubic and solvequartic are not called. So, replace the
;; function definitions with a call to merror.
(defun solvecubic (x) (declare (ignore x)) (merror "solvecubic"))
(defun solvequartic (x) (declare (ignore x)) (merror "solvequartic"))

;;;;;;;;;;;;;broken code!
;;; Attempt to solve equations that are rational functions of trig functions with identical arguments. When the equation
;;; e doesn't have the required form, return nil. Steps: (#1) convert all trig functions to sine or cosine (#2) gather
;;; the arguments of sine and cosine (#3) check that the arguments of sine and cosine are identical, and when they are
;;; replace cos(X) --> gc and sin(X) --> gs (#4) append gc^2 + gs^2-1 to the equation and solve.

(defun trigsolve (e x) "Attempt to solve equations that are rational functions of trig functions with the same argument."
	(let ((sine-args) (cosine-args) (kc) (ks) (gc) (gs) (sol) (buzz nil) (fun) (ker))
		 ;(mtell "new trigsolve ~%")
		;(displa `((mequal) e ,e))
		 (setq e (apply-identities e *pythagorean-identities*))
		 (setq e (apply-identities-xxx e *to-cos/sin-identities*))
		  ;;(displa `((mequal) e2 ,e))
		 (setq sine-args (mapcar #'second (cdr ($gatherargs e '%sin))))
		 (setq cosine-args (mapcar #'second (cdr ($gatherargs e '%cos))))
		 (setq sine-args (simplifya (cons '($set) sine-args) t))
		 (setq sine-args ($subset sine-args #'(lambda (q) (not ($freeof x q)))))

		 (setq cosine-args (simplifya (cons '($set) cosine-args) t))
		 (setq cosine-args ($subset cosine-args #'(lambda (q) (not ($freeof x q)))))
		 (cond ((and (eql 1 ($cardinality sine-args))
					 (eql 1 ($cardinality cosine-args))
					 (alike1 (second cosine-args) (second sine-args)))

				(setq ker (second sine-args))
				(setq kc (take '(%cos) (second cosine-args)))
				(setq gc (gensym))
				(setq ks (take '(%sin) (second sine-args)))
				(setq gs (gensym))
				(setq e ($ratsubst gc kc e))
				(setq e ($ratsubst gs ks e))
				(when ($freeof x e) ;bailout when e isn't freeof x
					(setq sol (cdr ($algsys (list '(mlist) e (add (mul gc gc) (mul gs gs) -1))
											(list '(mlist) gc gs))))
					(setq fun (gethash '%sin $solve_inverse_package))
					(dolist (sx sol)
						;(displa `((mequal) sx ,sx))
						;(displa `((mequal) ker ,ker))
						(setq sx ($substitute sx gs))
						(setq sx (funcall fun sx))
						(setq sx (mapcan #'(lambda(q) (cdr ($solve (take '(mequal) ker q) x))) sx))
						(setq buzz (append sx buzz)))
					(setq buzz (simplifya (cons '(mlist) buzz) t)))))

		 buzz))
