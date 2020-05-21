;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

;;; The option variable solveverbose is useful for debugging, but it's not intended
;;; for general use.
(defmvar $solveverbose nil)

(defmvar $solve_domain '$complex)

(defun solve-domain-assign (a b)
  (when (not (or (eql b '$real) (eql b '$complex)))
	    (merror "The value of ~M must be either 'complex' or 'real' ~%" a)))

(setf (get '$solve_domain 'assign) #'solve-domain-assign)

;;; The need for setting *evaluator-mode* is a mystery to me. And I'm not entirely sure
;;; about the need for loading solve.lisp.
(eval-when (:compile-toplevel :load-toplevel :execute)
  #+(or sbcl) (setq sb-ext:*evaluator-mode* :INTERPRET)
	($load "solve.lisp"))

;;; Unrelated to solving equations...
(dolist (e (list '$max '%acosh '%cos '%cosh '%lambert_w '%log '%sin '%sinh 'mabs 'rat))
	(setf (get e 'msimpind) (list e 'simp)))

;;; When $use_to_poly is true, dispatch the to_poly_solver after attempting other methods;
;;; when $use_to_poly is false, never dispatch the to_poly_solver.
(defmvar $use_to_poly t)

;;; When ask_mode is true, the function my-ask-boolean will prompt the user
;;; for information whose truth value cannot be determined from assumed facts
;;; and put that data into the fact database in the current context; when false,
;;; my-ask-boolean assumes the fact is true.
(defmvar $ask_mode t)

(defun ask-mode-assign (a b)
	(when (not (or (eql b t) (eql b nil)))
        (merror "The value of ~M must either true or false ~%" a)))

(setf (get '$ask_mode 'assign) #'ask-mode-assign)

;;; Wrap $new_variable into a function that switches to the context 'initial' before declaring
;;; the type. After the declaration, return to the original context. Maybe this functionality
;;; should be blended into $new_variable. Finally, I'm not sure the unwind_protect is really
;;; need--but it's OK.
(defun my-new-variable (knd) "wrapper for  $new_variable that autodeclares the type in the context initial."
	 (let ((cntx $context))
				(unwind-protect
					(progn
						(msetq $context '$initial)
						($new_variable knd))
				(msetq $context cntx))))

;;;Because I can't remember mlessp, mleqp, and ...
(defun mm< (a b) (take '(mlessp) a b))
(defun mm<= (a b) (take '(mleqp) a b))
(defun mm= (a b) (take '(mequal) a b))
;;; Load all need files--maybe SBCL still needs to be in interpret mode.

#+(or sbcl) (setq sb-ext:*evaluator-mode* :INTERPRET)

(eval-when (:compile-toplevel :load-toplevel :execute)
	($load "to_poly")
	($load "to_poly_solve_extra")
	($load "function-inverses.lisp")
	($load "trig_identities.lisp")
	($load "polynomial-solve.lisp")
	($load "in-domain.lisp")
	($load "linsolve.lisp")
	($load "solve_alt_top_level.lisp")
	($load "grobner.lisp")
	($load "one-to-one-solve.lisp")
	($load "fourier_elim.lisp")
	($load "solve-mcond.lisp")
	($load "myalgsys.lisp"))

;;; This code fixes polynomialp. When polynomialp is fixed, this code should be expunged.
;;; To avoid some test failures with rtest_solve_rec, put this definition in
;;; linearalgebra/polynomialp.lisp
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
    		*defint-assumptions*
			  xm* xn* mul*))

;; In expression e, convert all floats (binary64) and bigfloats to their exact rational value
;; and put that value inside a labeled box. Doing this allows solve to preserve the exact
;; value of floats.

(defmvar *float-box-label* (gensym))
(defmvar *big-float-box-label* (gensym))

(defun keep-float (e) "Convert floats and big floats to rational form and put them inside labeled boxes."
    (let ((xx) (ee) (sgn 1))
      (cond
         (($mapatom e)
          (cond ((floatp e)
					        (when (< e 0)
									   (setq e (* -1 e))
										 (setq sgn -1))

					        (setq xx ($rationalize e))
					  			(setq ee (take '(mlabox) xx *float-box-label*))
						  		(mfuncall '$assume (take '($equal) ee xx))
                  (mul sgn ee))
               (($bfloatp e)
						   	 (when (mfuncall '$is (mm< e 0)) ;ahh this is crazy
							  		(setq e (mul -1 e))
								  	(setq sgn -1))
						  	  (setq xx ($rationalize e))
                  (setq ee (take '(mlabox) ($rationalize e) *big-float-box-label*))
					  			(mfuncall '$assume (take '($equal) ee xx))
						  		(mul sgn ee))
               (t e)))
        (t (simplifya (cons (list (caar e)) (mapcar #'keep-float (cdr e))) t)))))

;;; In expression e, convert all labeled boxes that contain floats but to float form.
(defun unkeep-float (e) "Convert numbers in labeled float boxes back to float numbers."
    (cond
        (($mapatom e) e)
        ((and (consp e) (consp (car e)) (eql 'mlabox (caar e)) (third e)) ;it's a labeled box
         (cond ((eql *float-box-label* (third e)) ($float (second e))) ;unbox and convert to ieee float
               ((eql *big-float-box-label* (third e)) ($bfloat (second e))) ;unbox and convert to bigfloat
              (t e)))
        (t (simplifya (cons (list (caar e)) (mapcar #'unkeep-float (cdr e))) t))))

;;; Solve, apply nicedummies, simplify in current context, and sort solutions (keeping
;;; correct order of solutions and multiplicities). Using ssort instead of sort is
;;; especially useful for rtest files. The function sort-solutions (defined
;;; in solve_alt_top.lisp) sorts solutions and the multiplicities. The function
;;; nicedummies re-indexes %rXXX, %cXXX, and %zXXX variables to start with zero.
;;; The call to $expand(XXX,0,0) does the simplifcation in the current context.
(defun $ssolve (e x)
		(let (($%rnum 0)) (sort-solutions ($expand ($nicedummies ($solve e x)) 0 0) nil)))

;;; Flags that I've ignored: $solveexplicit (not entirely), $dispflag, $programmode, and $breakup.

;;; The top level function solve function:
;;;   (a) resets multiplicities to its default value
;;;   (b) expunges constant variables and duplicates from the list of variables
;;;  (c) checks for inequalities and signals an error when found
;;;   (d) creates a new super context--all assumptions made during solve are removed after exiting
;;;   (e) does gensym substitutions when solving for nonatoms
;;;   (f) dispatches the appropriate lower level solve function
;;;   (g) reverts gensym substitutions for nonatom solve
;;;   (h) kills the super context

(defmfun $solve (eqlist &optional (varl nil))
  (mfuncall '$reset '$multiplicities)
  (mfuncall '$reset '$%rnum_list) ;not sure about this?

  (let ((cntx) (nonatom-subst nil)	(sol) (g) ($domain '$complex) ($negdistrib t)
      	($algebraic t)	($gcd '$subres))
	   ;; Allow eqlist and varl to be sets.
	   (when ($setp eqlist)
		   (setq eqlist ($listify eqlist)))

	   (when ($setp varl)
		   (setq varl ($listify varl)))

	   ;; When varl is empty, solve for the nonconstant variables. Set varl to a CL list and remove
	   ;; duplicates. For variable ordering, we take the same order as listofvars.

	   (setq varl
			 (remove-duplicates
			 	(cond
					((null varl) (let (($listconstvars nil)) (cdr ($listofvars eqlist))))
					(($listp varl) (cdr varl))
					(t (list varl)))
			   :test #'alike1 :from-end t))

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

	 ;(setq eqlist (remove-if #'zerop1 eqlist))
	 ;;Eliminate duplicate equations.
	 ;(setq eqlist (delete-duplicates eqlist :test #'alike1 :from-end t))
	 (setq eqlist (cdr (simplifya (cons '($set) eqlist) t)))

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
	 (setq nonatom-subst (mapcar #'$reverse nonatom-subst))
	 (push '(mlist) nonatom-subst)

	 (unwind-protect
	  (progn
			(setq cntx ($supcontext)) ;make asksign and friends data vanish after exiting $solve.
		  (cond
			  ((null varl)
		  	   (when $solvenullwarn
			   	    (mtell (intl:gettext "Solve: variable list is empty, continuing anyway.~%")))
           (cond ((every #'zerop1 eqlist)
				           (simplifya (take '(mlist) (take '(mequal) 0 0)) t)) ;was '$all
						  	 (t (take '(mlist)))))

			  ((and (null (cdr varl)) (null (cdr eqlist))) ; one equation and one unknown
			   (setq eqlist (keep-float (car eqlist)))
			   (setq sol ($substitute nonatom-subst (solve-single-equation eqlist (car varl))))
		  	 (unkeep-float sol))

			  ((null (cdr varl)) ;one unknown, more than one equation
			    (redundant-equation-solve (cons '(mlist) eqlist) (car varl)))

			  ;; several equations, several unknowns.
			  (t
			  	(setq sol (solve-multiple-equations eqlist varl))
			 	  ($substitute nonatom-subst sol))))
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
	(cond
		((and (mexptp e) (mnump (third e)) (mgrp (third e) 0)) ; do z^n --> z when n is a positive mnump
		 (equation-simplify (second e) (mul m (third e))))
		(t
	   ;;unsure when is the best time to do radcan, but it's better to do it after
		 ;; the z^n --> z simplification.
		 (when $solveradcan
				(setq e ($radcan e)))
		 (setq e ($num (sratsimp e)))
		 ;(setq e (apply-identities-conditionally e *trig-power-reduce*))
		 (setq e (apply-identities-conditionally e *pythagorean-identities*))
		 ;(setq e (convert-from-max-min-to-abs e)) ; by itself, this doesn't do all that much.
		 (list e m))))

;;; Convert to-poly style predicates to Maxima predicates. In particular, do
;;; $isnonnegative_p -> >, =/= -> $notequal, %and --> mand.
(defun to-poly-fixup (cnd)
	(let ((q) ($opsubst t))
		(setq q ($substitute #'(lambda (s) (take '(mgreaterp) s 0)) '$isnonnegative_p cnd))
		(setq q ($substitute #'(lambda (a b) (take '(mor) a b)) '%or q))
		($substitute #'(lambda (a b) (take '(mand) a b)) '%and q)))

;;; True iff the operator of e is mor.
(defun or-p (e) (and (consp e) (eql (caar e) 'mor)))

;;; True iff the operator of e is mand.
(defun and-p (e) (and (consp e)  (eql (caar e) 'mand)))

;;; When "maybe" is unable to determine if the predicate "cnd" is either true or false
;;; and the option variable ask_mode is true, ask the user. In the current context,
;;  assume cnd or its negation, depending on the input from the user. Keep prompting
;;; the user until the user gives a proper response (no, n, N, yes, y, Y).

;;; When ask_mode is false, append cnd to the current context.

(defun my-ask-boolean (cnd)
  (setq cnd (to-poly-fixup cnd)) ;convert to-poly style to Maxima predicates
	(let ((context $context) ;workaround for a bug somewhere?
         (answer (mfuncall '$maybe cnd))) ; not ready for this?

    ;; The definite integration code sometimes introduces a new variable, often named
		;; yx, and puts 'internal on its symbol list. We don't want to be asked questions
		;; about these internal symbols, so we hold our breath and assume the condition is
		;; true. Sadly it doesn't seem to be the case that assumptions about internal variables
		;; get recorded in any context. See the function intcv defined in defint.
  ;  (when (some #'identity (mapcar #'(lambda (q) (get q 'internal)) (cdr ($listofvars cnd))))
	;	    (mtell "Found internal variable--assuming ~M is true. ~%" cnd)
	;			(mfuncall '$assume cnd)
	;			(setq answer t))

    ;; When a solution involves a %zXXX variable (say solve(sin(x)=0,x)), we simply append any
		;; needed fact about %zXXX to the initial fact database. By appending to the initial context,
		;; this fact is preserved after the solve process. Not sure about this....
		(when (and
			       (not $ask_mode)
			       (some #'identity (mapcar #'(lambda (q) (get q 'integer-gentemp))
							   (cdr ($listofvars cnd))))
					 (not (or-p cnd)))
				 (mtell "Appending ~M to fact database. ~%" cnd)
				 (let (($context '$initial) (context '$initial)) (mfuncall '$assume cnd))
				 (setq answer t))

		  (cond ((or (eql answer t) (eql answer nil)) answer)
	  	   	  ($ask_mode
		   	      (setq answer (retrieve `((mtext) ,(intl:gettext "Is ") ,cnd ,(intl:gettext "?")) nil))
							;; The function 'assume' gives an error for attempting to assume an
							;; 'or' expression. So we attempt to check if cnd is a valid input to
							;; 'assume.' Maybe a better approach would be to wrap an error catch around
							;; 'assume.'
			        (cond ((member answer '($yes |$y| |$Y|) :test #'eql)
							         (when (not (or-p cnd))
						              (mfuncall '$assume cnd))
				              t)
				            ((member answer '($no |$n| |$N|) :test #'eql)
										   (when (not (and-p cnd))
                          (mfuncall '$assume (take '(mnot) cnd)))
					             nil)
			      	     (t
				              (mtell (intl:gettext "Acceptable answers are yes, y, Y, no, n, N. ~%"))
				              (my-ask-boolean cnd))))
							 (t
								 (mtell (intl:gettext	"assuming ~M ~%") cnd)
								 (mfuncall '$assume cnd)
								 t))))

(defun error-substitute (sub e)
  (setq e (let (($errormsg nil) (errcatch (cons bindlist loclist)))
		   (errset ($substitute sub e))))
	(if e (car e) e))

;;; Remove the members of sol that do not satisfy cnd. The members of the CL list sol have
;;; the form solution.multiplicity. The Maxima expression cnd is generally a conjunction
;;; of Maxima predicates. For each solution, we substitute sx in to cnd and call my-ask-boolean.

(defun filter-solution (sol cnd) "Remove the members of sol that do not satisfy cnd"
	(let ((checked-sol nil))
		 (dolist (sx sol)
			 (when (my-ask-boolean (error-substitute (car sx) cnd))
				 (push sx checked-sol)))
		 (reverse checked-sol)))

;;; Solve the equation e=0 for x, where e is a mtimes expression. Actually, effectively the
;;; equation is e^m = 0, so m is the multiplicity so far in the solving process. The list cnd
;;; has conditions on the solution.

;;; When e = e1*e2* ... * en, solve e1=0, e2=0, ... en = 0.  Remove the duplicates from the
;;; union of the solutions, and remove those solutions that do not satisfy cnd. One problem is
;;; when one of the solutions is all, but there is a condition on the solution--something like
;;; solve ((sin(x)^2 + cos(x)^2-1)*(1/x),x). I'm not sure how to fix this.

(defun product-solver (e x m use-trigsolve cnd) "Solve e=e1*e2*...*en for x"
	;;(mtell "using product solve ~%")
	;;(displa `((mequal) cnd ,cnd))

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


					(dolist (sx solx) ; build an association list of the form solution.multiplicity
						(push (cons sx (pop wmul)) sol))))
		 (cond
			 ((eql sol '$all)
				sol)
			 (t
			  (setq sol (remove-duplicates sol :test #'alike1 :key #'car :from-end t))
			  (setq sol (filter-solution sol cnd))
			  (setq $multiplicities (simplifya (cons '(mlist) (mapcar #'cdr sol)) t))
			  (simplifya (cons '(mlist) (mapcar #'car sol)) t)))))

(defun filter-solution-x (sol cnd)
  (let ((alist nil))
	  (cond
			((not ($listp sol)) sol) ;pass through for non listp solution (for example nil or $all)
			(t
				 ;; When either $multiplicities hasn't been set or its length doesn't match the solution,
				 ;; silently change the multiplicities to a list of $not_yet_set.
			   (when (not (and ($listp $multiplicities) (eql (length sol) (length $multiplicities))))
				        (mtell "warning: setting multiplicities to 1! ~%")
					      (setq $multiplicities (mapcar #'(lambda (q) (declare (ignore q)) 1) (cdr sol)))
						  	(push '(mlist) $multiplicities))
       		;; First build an association list of solution.multiplicity. Second call filter-solution.
		  		;; And third re-constitute Maxima lists for the solution and the multiplicities. The
					;; filtering process requires using sign, but the keepfloat mechanism interferes with
					;; sign.  So we'll unkeep-float each solution. Maybe the entire keep-float/unkeep-float
					;; scheme needs to be re-considered.
		  		(setq alist (mapcar #'(lambda (a b) (cons (unkeep-float a) b)) (cdr sol) (cdr $multiplicities)))
		  		(setq alist (filter-solution alist (unkeep-float cnd)))
		  		(setq $multiplicities (simplifya (cons '(mlist) (mapcar #'cdr alist)) t))
		  		(simplifya (cons '(mlist) (mapcar #'car alist)) t)))))

(defmvar $the_unsolved '(($set)));this is purely for debugging

(defun real-or-complex-mapatom (e)
     (cond (($subvarp e) (real-or-complex-mapatom (caar e)))
					 ((kindp e '$complex) '$complex)
					 (t '$real)))

(defun solve-single-equation (e x &optional (m 1) (use-trigsolve nil))
(when (or $solveverbose)
	  (mtell "top of solve-single-equation e = ~M x = ~M m = ~M use = ~M ~%" e x m use-trigsolve))

	(let ((cnd) ($solve_domain (real-or-complex-mapatom x)))
	   (setq cnd (or (not $ask_mode) (in-domain e (list x))))
		 (setq e (equation-simplify e m))
		 (setq m (second e))
		 (setq e (first e))

		 (when (not ($mapatom x))
		    (mtell "Looks like a non maptom e = ~M x = ~M ~%" e x))

		 (cond

			((and ($mapatom x) ($polynomialp e (list '(mlist) x) #'(lambda (q) ($freeof x q)))) ;solve polynomial equations
			   (filter-solution-x (polynomial-solve e x m) cnd))

			((mtimesp e) ;for equations that are explicitly products, use product-solver
			  (product-solver e x m use-trigsolve cnd))

      ((filter-solution-x (one-to-one-solve e x m nil) cnd))

			((filter-solution-x (solve-by-kernelize e x m) cnd))

      ((filter-solution-x (solve-mcond e x m use-trigsolve) cnd))

		  ((filter-solution-x (solve-mexpt-equation-extra e x m nil) cnd))

			((filter-solution-x (solve-mexpt-equation-extra e x m t) cnd))

			((and ($mapatom x) (algebraic-p e (list x)) ;why the mapatom filter?
				 (filter-solution-x (solve-algebraic-equation e x) cnd)))

			((mtimesp ($factor e))
			  (product-solver ($factor e) x m use-trigsolve cnd))

		  ((filter-solution-x (lambert-w-solve e x m) cnd))

			((and $use_to_poly (new-to-poly-solve e x cnd)))

			($solveexplicit ; give up & return the empty set
			  (mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning the empty list.~%") e x)
			  (setq $the_unsolved ($adjoin (list '(mlist) e x) $the_unsolved))
			  (setq $multiplicities (take '(mlist) m))
			  (take '(mlist)))

			(t
			  ;; Integration is sensitive to what happens for unsolved equations. Try
			  ;; laplace(exp(-8*exp(u)),u,v) after changing the return value to 0 = e.
			  ;; Standard Maxima chooses to solve for some equation kernel, but I don't know
			  ;; how it chooses the kernel--so use a silly heuristic for choosing a kernel.
			  (mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning an implicit solution.~%") e x)
			  ;(push (list '(mlist) e x) $the_unsolved)
			  (let ((ker))
				   (setq ker (if (and (mplusp e) (not ($freeof x (first (last e))))) (first (last e)) x))
				   (setq $multiplicities (take '(mlist) m))
				   (take '(mlist) (take '(mequal) ker (sub ker e))))))))



;;; For a given function fun, kernel ker, and variable x, return the inverse
;;; of fun and the adjusted kernel. Examples:

;;; When fun is a function of one variable, the adjusted kernel is the argument of ker:
;;;  fun = %sin, ker = sin(x-1), x = x  --> (asin  x-1)

;;; When fun is a function of two or more variables, for example mexpt, we have
;;;  fun = mexpt, ker = 5^x, x = x --> (q -> (log q)/(log 5), x)  (adjusted kernel is x)
;;;  fun = mexpt, ker = (3x)^5, x = x --> (q -> q^(1/5), 3x)  (adjusted kernel is 3x)
;;;  fun = mexpt, ker = (6x)^(6x), x = x --> (q -> lambert_w (....), 6x)

;;; Yes, fun and ker have redundant data (because fun is the caar of ker). But OK.

(defun solve-get-inverse (fun ker x)
    (let ((fn))
       (cond
				 ((eql fun 'mexpt)
		        (cond ((alike1 (second ker) (third ker)) ;looking at x^x = b
					          (list
											(gethash 'lambert-like-inverse $solve_inverse_package)
											(second ker)))

							 	 ((among x (second ker)) ;looking at x^a = b
									  (setq fn (gethash 'power-inverse $solve_inverse_package))
										(list
											#'(lambda (q) (funcall fn q (third ker)))
											(second ker)))

								 ((among x (third ker)) ;looking at a^x = b
										 (setq fn (gethash 'exponential-inverse $solve_inverse_package))
										 (list
											 #'(lambda (q) (funcall fn q (second ker)))
											 (third ker)))))

				 (t	(list
					      (gethash fun $solve_inverse_package)
								(second ker))))))

;;; This function attempts to identify a term F(x) such e is a function of only F(x). And when it is,
;;; first solve for F(x), and second solve for x. The function F has a known inverse. Unifying the
;;; cases, for example,  of F(x) = x^a and F(x) = cos(x) is problematic. Maybe these cases can be unified,
;;; but we'll handle the case when F is a
;;; power function separately.

(defun solve-by-kernelize (e x m)
  (when (or $solveverbose)
		(mtell "Top of solve-by-kernelize e = ~M x = ~M ~%" e x)
		($read ))

	(let (($solveexplicit t) (z) (sol) (fun-inverse) (ker) (fun) (acc nil) (q)
		  (mult-acc nil) (xxx) (mult-save))
		 (setq e (kernelize e x))

		 (cond ((and (null (cdr (second e))) ($freeof x (first e)))
				(setq ker (second e))
				(setq e (first e))
				(setq z (cdar ker))
				(setq ker (caar ker))
				(setq fun (caar ker))
				(setq sol ($solve e z))
				(when (not ($listp $multiplicities))
				   (mtell "using fake multiplicities ~%")
					 (setq $multiplicities (mapcar #'(lambda (s) (declare (ignore s)) 1) sol)))
				(setq mult-save (mapcar #'(lambda (q) (mult m q)) (cdr $multiplicities)))
				(setq sol (mapcar #'third (cdr sol)))  ;third = $rhs

				;; Return the inverse of the function fun and the adjusted kernel. For
				;; and explanation and examples, see the documentation for solve-get-inverse.
        (setq fun-inverse (solve-get-inverse fun ker x))
        (setq ker (second fun-inverse))
				(setq fun-inverse (first fun-inverse))
				;; after this, sol is a list of lists
		    (setq sol (mapcar #'(lambda (q) (apply fun-inverse (list q))) sol))

				(setq mult-save (mapcar #'(lambda (a b)
											(mapcar #'(lambda (c) (declare (ignore c)) b) a)) sol mult-save))

				(setq sol (reduce #'append sol))
				(setq mult-save (reduce #'append mult-save))
				(setq sol (mapcar #'(lambda (q) (take '(mequal) ker q)) sol))

				(dolist (sx sol)
					(setq q ($solve sx x))
					(when (not ($listp $multiplicities))
						 (mtell "using fake multiplicities ~%")
						 (setq $multiplicities (mapcar #'(lambda (s) (declare (ignore s)) 1) sol)))

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

;; True iff e is a kernel. Either e has the form F(X), where F has a known
;; inverse and X depends on x, or e has the form a^X, X^b, or X^X, where
;; X depends on x and a & b do not.
(defun kernel-p (e x)
   (or
		 (and ;; e = F(X), where F has a known inverse and X depends on x.
			 (consp e)
	  	 (consp (car e))
			 (gethash (caar e) $solve_inverse_package)
			 (not ($freeof x e)))
			(and
				 (mexptp e) ;; e = a^X, e=X^b, or e=X^X, where X depends on x.
	 	      	(or
							  (and ($freeof x (second e)) (not ($freeof x (third e)))) ;; a^X
								(and (not ($freeof x (second e)))
									(and ($freeof x (third e)) (not (integerp (third e))))) ;; X^a
	 							(and (not ($freeof x (second e))) (alike1 (second e) (third e))))))) ;X^X

(defun kernelize (e x &optional (subs nil))
;;  (mtell "top of kernelize ~M ~M ~%" e x)
	(let ((g (gensym)) (kn nil) (xop) (eargs))
		 (cond
			 (($mapatom e) (list e subs))

			  ((kernel-p e x)
			   (setq kn (assoc e subs :test #'alike1)) ;is it a known kernel?
			   (cond (kn
					       (list (cdr kn) subs)) ; it's a known kernel--use the value from the association list subs
				   	   (t
				   	    (list g (acons e g subs))))) ; it's unknown--append a new key/value to subs

			 (t ; map kernelize onto the argument list and build up the association list subs
			  (setq xop (list (caar e)))
			  (setq e (cdr e))
				(setq eargs nil)
			  (dolist (xk e)
				  (setq xk (kernelize xk x subs))
				  (push (first xk) eargs)
				  (setq subs (second xk)))
			  (list (simplifya (cons xop (reverse eargs)) t) subs)))))


(defun homogeneous-linear-poly-p (e vars)
	(setq e ($rat e))
	(dolist (x vars)
		(setq e (sub e (mul x ($ratcoef e x)))))
	(zerop1 ($ratdisrep e)))

;;; experimental code for solving equations of the form Polynomial(a^x) = 0.

;;; Return a CL list of all the terms in the expression e that have the form a^x, where a is freeof x,
;;; or a constant times a product of one or  more terms of this form. The local predicate expt-match,
;;; is true for any constant or any term of the form a^x.
(defun gather-expt-terms (e x) "Gather terms in e that have the form a^x or products of such terms"
	   (labels ((expt-match (q z) (and (mexptp q) ($freeof z (second q)) (not ($freeof z (third q))))))
	     (cond (($mapatom e) nil)
	    	    	((or (expt-match e x)
	 					     (and (mtimesp e)
						 		    (not ($freeof x e)) ; require dependence on x
							      (every #'(lambda (s) (or ($freeof x s) (expt-match s x))) (cdr e))))
	 		 			     (list e))
	          ((and (consp e) (consp (car e)))
	 			 		  (mapcan #'(lambda (s) (gather-expt-terms s x)) (cdr e)))
	 			  	(t nil)))) ; likely the final clause should never happen?

(defun get-algebraic-relations (e x kernel)
   (let ((f) (p-list) (d) (subs) (consts))
      (labels ((get-power (f g x)
               (let ((p ($radcan (div (mul ($diff f x) g) (mul f ($diff g x))))))
                  (list p ($radcan (div f (take '(mexpt) g p)))))))
      (setq f (first e))
      ;;(setq base (second f)) ; f = a^x
      (setq p-list (mapcar #'(lambda (g) (get-power g f x)) e)) ; list of (powers,constants)
      (setq consts (mapcar #'second p-list)) ;list of constants
      (setq p-list (mapcar #'first p-list))  ;list of powers

      ;; when every power is rational, multiply it by its lcm; otherwise set p-list to nil.
      (cond ((every #'$ratnump p-list)
                 (setq d (apply #'lcm (mapcar #'$denom p-list)))
                 (setq p-list (mapcar #'(lambda (s) (mul d s)) p-list)))
              (t (setq p-list nil)))

    (setq subs (mapcar #'(lambda (a b c) (take '(mequal) a (mul c (power kernel b)))) e p-list consts))
    (simplifya (cons '(mlist) subs) t))))

(defun cl-list-of-vars (e)
	(cdr (let (($listconstvars nil)) ($listofvars e))))

(defun checked-subst (eq e)
   (let ((cnd (in-domain e (cl-list-of-vars e))))
			(setq cnd (mfuncall '$is ($substitute eq cnd)))
	;;;;		(if (not cnd) (displa "Caught one!!!!!!!!!!"))
			(if cnd ($substitute eq e) eq)))

(defun solve-mexpt-equation-extra (e x m use-trigsolve)
  (when $solveverbose
     (mtell "Top of solve-mexpt-equation-extra; e = ~M x = ~M ~%" e x))

 	(let ((pterms) (g (gensym)) (subs) (sol nil) (submin nil) (sol-all nil) (do-rectform nil))
        (when use-trigsolve
					(setq do-rectform t)
	      	(setq e ($exponentialize e)))
	      ;	(setq e (apply-identities-conditionally e *pythagorean-identities*))
      	;	(setq e (apply-identities-unconditionally e *to-cos/sin-identities*)))

     (setq pterms (gather-expt-terms e x))

	   (setq pterms (remove-duplicates pterms :test #'alike1 :from-end t))
     (setq subs (get-algebraic-relations pterms x g))

		 (when $solveverbose
			  (print `(subs = ,subs))
				($read))


		 ;; look for a substitution that is linear in g--call it submin.
		 (when (cdr subs)
      	(setq submin (first (remove-if #'(lambda (s) (> ($hipow s g) 1)) (cdr subs)))))
		 ;; When there is a substitution that is linear in g, we:
		 ;; (1)	substitute subs into the equation
		 ;; (2) when the result is free of x (only unknown is g) we
		 ;; (3) solve for g
		 ;; (4) for each of these solutions, substitute it into submin; and
     ;; (5) solve for the unknown collecting the solutions

	   (when submin
	      	(setq e (checked-subst subs e))
	      	(when (and e ($freeof x e))
		         (setq sol (solve-single-equation e g m use-trigsolve))
						 (setq sol (cdr sol))
						 (setq sol-all nil)
						 (dolist (sx sol)
						    ;;;(mtell "solution sx = ~M submin = ~M ~%" sx submin)
						    (setq sx (checked-subst sx submin));;; was ($substitute sx submin))
								(setq sol-all (append (cdr (solve-single-equation sx x m use-trigsolve)) sol-all)))
			       (setq sol (simplifya (cons '(mlist) sol-all) t)))
					(when do-rectform
						(setq sol (sratsimp ($rectform sol)))))
		sol))


(defun algebraic-p (e x) "True iff expression e is an algebraic expression in x."
   (or
     ($numberp e)
		 ($mapatom e)
		 (and (mexptp e) (algebraic-p (second e) x) ($ratnump (third e)))
		 (or
			  ($lfreeof (cons '(mlist) x) e)
		    (and
					 (or (mplusp e) (mtimesp e))
           (every #'(lambda (s) (algebraic-p s x)) (cdr e))))))

(defun solve-algebraic-equation-system (e x)
		(let ((q) (eq) (nonalg-sub) (cnds) (nvars) (sol) (ssol nil) ($errormsg nil) ($algexact t))
				(setq eqs ($to_poly e x)) ;convert to polynomial system
				(setq nonalg-sub (fourth eqs)) ;should be a Maxima empty list
		 	  (cond (($emptyp nonalg-sub)
								(setq cnds (third eqs)) ;Maxima list of constraints on variables
							  (setq cnds (simplifya (cons '(mand) (cdr cnds)) t)) ;cnds is a Maxima boolean
								(setq eq (second eqs))  ;the polynomial system
							  ;; gather the gensym variables generated in the process of converting to
							  ;; a polynomial system.
							  (setq nvars ($subset (set-of-vars eq) #'(lambda (q) (and (symbolp q) (get q 'general-gentemp)))))
								(setq nvars ($union ($setify x) nvars))
								(setq nvars ($listify nvars))
								;(setq eq (unkeep-float eq))
							  (setq sol (cdr ($myalgsys eq nvars))) ;sol is a CL list of Maxima lists of solutions
								;; Check that the putative solution satisfies the constraints; and
						  	;; remove solutions for the gensym variables & gather solutions into ssol.
							  (dolist (sx sol)
									(when (my-ask-boolean (error-substitute sx cnds))
										 (setq sx (remove-if #'(lambda (s) (not (memq ($lhs s) (cdr x)))) (cdr sx)))
										 (setq sx (simplifya (cons '(mlist) sx) t))
										 (push sx ssol)))
								(setq ssol (remove-duplicates ssol :test #'alike1 :from-end t))
								(simplifya (cons '(mlist) ssol) t))
						(t nil))))

;; Return a Maxima list of solutions to the algebraic equation e.
(defun solve-algebraic-equation (e x)
    (let ((q) (eq) (nonalg-sub) (cnds) (nvars) (sol) (ssol nil) ($errormsg nil) ($algexact t))
        (setq eqs ($to_poly e (list '(mlist) x))) ;convert to polynomial system
        (setq nonalg-sub (fourth eqs)) ;should be a Maxima empty list
				(cond (($emptyp nonalg-sub)
                (setq cnds (third eqs)) ;Maxima list of constraints on variables
			        	(setq cnds (simplifya (cons '(mand) (cdr cnds)) t)) ;cnds is a Maxima boolean
                (setq eq (second eqs))  ;the polynomial system
		        		;; gather the gensym variables generated in the process of converting to
		    	    	;; a polynomial system.
		    	    	(setq nvars ($subset (set-of-vars eq) #'(lambda (q) (and (symbolp q) (get q 'general-gentemp)))))
 			          (setq nvars ($adjoin x nvars))
 		    	      (setq nvars ($listify nvars))
				        (setq sol (cdr ($myalgsys eq nvars))) ;sol is a CL list of Maxima lists of solutions
                ;; Check that the putative solution satisfies the constraints; and
			         	;; remove solutions for the gensym variables & gather solutions into ssol.
			        	(dolist (sx sol)
								   (when (my-ask-boolean (error-substitute sx cnds))
				              (setq sx (remove-if #'(lambda (s) (not (eql ($lhs s) x))) (cdr sx)))
					            (setq ssol (append ssol sx))))

								 (mtell "solve-algebraic-equation!!! ~%")
								 (setq ssol (remove-duplicates ssol :test #'alike1 :from-end t))
				         (simplifya (cons '(mlist) ssol) t))
						 (t nil))))

#|
(defun ok-p (e)
			(and (consp e) (consp (car e)) (gethash (caar e) $solve_inverse_package)))

(defun $experimental_solve (e x &optional (m 1) (cnd t))
  (let ((q (kernelize-fn e #'(lambda (s) (and (not ($freeof x s)) (ok-p s)))))
	      ($solveexplicit t) (eqs) (sol nil) (ssol nil))
    	(cond ((and (null (cdr (second q))) ($freeof q (first q)))
    		 (setq ker (second q))
    		 (setq e (first q))
    		 (setq z (cdar ker))
    		 (setq ker (caar ker))
				 (mtell "e = ~M z = ~M ker = ~M ~%" e z ker)
         (when (algebraic-p e z)
				    (setq sol (cdr (solve-algebraic-equation e z))) ;; CL list of solutions
						(dolist (sx sol)
						    (mtell "ker = ~M sx = ~M ~%" ker sx)
						    (setq ssol (append ssol (cdr (solve-single-equation (sub ker ($rhs sx)) x)))))
						(cons '(mlist) ssol))))))

|#

(defun new-to-poly-solve (e x cnd)

  (when (or t $solveverbose)
		(mtell "doing to poly solve e = ~M x = ~M cnd = ~M  ~%" e x cnd))

	(let ((q) (eq) (nonalg-sub) (nvars) (sol) (ek) (cx) ($algexact t) (checked-sol nil))
		 (setq q (let ((errcatch t) ($errormsg nil)) (ignore-errors ($to_poly e (list '(mlist) x)))))
		 (when (and q (< ($length ($third q)) 2))
			 (setq checked-sol (list '(mlist)))
			 (setq eq ($first q))
			   (setq cnd (take '(mand) cnd (simplifya (cons '(mand) (cdr ($second q))) t)))
			 (setq nonalg-sub ($third q))

			 (setq nvars ($subset (set-of-vars eq) #'(lambda (q) (and (symbolp q) (get q 'general-gentemp)))))
			 (setq nvars ($adjoin x nvars))
			 (setq nvars ($listify nvars))
			 (setq sol (let (($algexact t)) (cdr ($algsys eq ($listify nvars)))))
			 (cond ((and sol ($emptyp nonalg-sub))
					;;(mtell "branch 1 ~%")
					(dolist (sk sol)
						(setq cx ($substitute sk cnd))
						(setq cx (my-ask-boolean cx))
						;(setq cx (simplifya (cons '(%and) (mapcar #'(lambda (q) (mfuncall '$maybe q)) (cdr cx))) t))
						(when (or (eql cx t) (eql cx '$unknown))
							(setq sk (take '(mequal) x ($substitute sk x)))
							(setq checked-sol ($cons sk checked-sol)))))
				 ((and sol (or (null nonalg-sub) ($freeof x eq)))
				  ;;(mtell "branch 2 ~%")
				  ;;(mtell "branch 2 ~%")
				  (setq nvars ($first nvars))
				  (dolist (sk sol)
					  (setq sk (let (($use_to_poly nil)) ($solve ($first sk) nvars)))
					  (setq ek ($substitute sk nonalg-sub))
					  (setq cx ($substitute sk cnd))
					  (setq cx (my-ask-boolean cx))
					  ;;(setq cx (simplifya (cons '(%and) (mapcar #'(lambda (q) (mfuncall '$maybe q)) (cdr cx))) t))
					  (when (or (eql cx t) (eql cx '$maybe))
						  (setq sk ($solve ek x))
						  (setq sk ($rectform sk))
						(setq checked-sol ($append checked-sol sk))))))

			 ;;(setq checked-sol (filter-solution (cdr checked-sol) (cdr cnd)))
			 ;;(setq checked-sol (simplifya (cons '(mlist) checked-sol) t))

			 (when checked-sol
				 (mtell "used the to poly solver ~%")))

     (mtell "checked = ~M ~%" checked-sol)
		 checked-sol))

(defun equation-complexity-guess (a b) (< (trig-fun-count a) (trig-fun-count b))) ; trig-fun-count defined in trig_identities

;;; Solve the Maxima list of expressions eqs for the symbol x. This function doesn't attempt
;;; to set the multiplicities to anything reasonable--it resets  multiplicities to the default.
(defun redundant-equation-solve (eqs x)
	(mtell "top of redundant solve eqs = ~M x = ~M ~%" eqs x)
	(setq eqs (if (or ($listp eqs) ($setp eqs)) (cdr eqs) eqs))
	(setq eqs (mapcar #'meqhk eqs)) ;convert a=b to a-b. This is important!
	(setq eqs (mapcar #'try-to-crunch-to-zero eqs)) ;simplify eqs
	(setq eqs (remove-if #'zerop1 eqs)) ;remove all vanishing equations

  ;; Maybe the polynomial case should be caught higher up? We'll do it here for now.
	;; The $flatten call is ugly.
  (cond ((every #'(lambda (q) ($polynomialp q (list '(mlist) x) #'(lambda (s) ($freeof x s))
				       	#'(lambda (s) (and (integerp s) (>= s 0))))) eqs)
			    ($flatten (solve-multiple-equations eqs (list x))))
    	;; Solve the eqations one at a time and collect the intersection of the
     	;; solutions. Some problems remain--if x = %c0, for example, we need a
   	  ;; specialized intersection. And there are additional problems with %zXXX
	    ;; kinds of solutions too.
			(t
         (let ((sol ($setify ($solve (pop eqs) x)))) ;solve first equation & setify solution
            (while eqs
				       (when ($emptyp sol) ;early bailout when intersection is empty
					   	   (setq eqs nil))
				       (setq sol ($intersection sol ($nicedummies ($setify ($solve (pop eqs) x))))))
				   ($listify sol))))) ;convert set of solutions to a list

(defun set-of-vars (e)
	(let (($listconstvars nil)) ($setify ($listofvars e))))

(defun triangularize-eqs (e x)
   (let ((xx x))
	    (setq e (apply-identities-conditionally e *pythagorean-identities*))
	    (setq e (if ($listp e) ($setify e) e))
	    (setq x (if ($listp x) ($setify x) x))
      (setq e ($equiv_classes e #'(lambda (a b) ($setequalp
											   ($intersection (set-of-vars a) xx)
											   ($intersection (set-of-vars b) xx)))))
    	(setq e ($listify e))
	    ($sort e #'(lambda (a b) (< ($cardinality ($intersection (set-of-vars a) x))
									          	($cardinality ($intersection (set-of-vars b) x)))))))

(defun list-of-list-p (e)
	(and
	 ($listp e)
	 (every #'$listp (cdr e))))

;; not sure about when e is CRE?
(defun mequalp (e) "True iff e is an mequal expression"
  (and (consp e) (consp (car e)) (eql (caar e) 'mequal)))

;;; Solve a triangular system of equations eqs for the variables vars. Specifically, eqs is a CL
;;; list of Maxima sets and vars is a CL list of mapatoms. We return a CL list of CL lists of the form
;;; ((x=5,y=42), (x=107,y=12)), for example. The CL list of Maxima sets eqs has a special structure.
;;; The set of variables in the n-th set is a proper subset of the set of variables in all
;;; subsequent sets.
(defun solve-triangular-system (eqs vars)
    (when $solveverbose
	   	(mtell "Top of solve-triangular-system eqs = ~M vars = ~M ~%"
				  (cons '(mlist) eqs) (cons '(mlist) vars)))

	  (let ((e) ($listconstvars nil) ($solveexplicit t) (sol) (ssol nil) (eqvars))
            (setq eqs (mapcar #'(lambda (q) (try-to-crunch-to-zero q
							       #'apply-identities-unconditionally  #'sqrtdenest #'fullratsimp)) eqs))

				    (cond
							((null eqs)
				        ;; No equations to solve, so all variables are free.
								;; Return ((var1 = %r1 var2 = %r2...varn = %rn))
				         ;(mtell "null equations vars = ~M ~%" (cons '(mlist) vars))
								(list (mapcar #'(lambda (s) (take '(mequal) s (next-rnum-variable))) vars)))

	           ((every #'zerop1 (cdr (first eqs)))
						     ;; The first equation is a set of zeros--move on to next equation
	               (solve-triangular-system (rest eqs) vars)) ; remove first equation & solve the rest

						 (t
							 ;; find intersection of variables in 1st equation and the unknowns.
							 (setq eqvars ($intersection
								            ($setify ($listofvars (first eqs)))
											  		(simplifya (cons '($set) vars) t)))

							 (cond (($emptyp eqvars)
						        	 ;; No unknowns but remaining nontrival equation(s), so return nil
					        		 (mtell (intl:gettext "Unable to show that ~M vanishes; returning the empty list ~%")
												  (cons '(mlist) eqs))
					       	 	   nil)
										 (t
											 (setq vars (simplifya (cons '($set) vars) t))  ; vars is now a set.
									     (setq vars ($setdifference vars eqvars)) ; remove eqvars from unknowns
											 (setq vars (cdr vars)) ;return vars to a CL list.
											 (setq eqvars (cdr eqvars)) ;return eqvars to a CL list
	               			 (setq e (pop eqs))
                       (cond ((and (eql 1 (length eqvars)) (eql 1 ($cardinality e))) ;one equation & unknown
												        ;(mtell "one equation one unknown ~%")
											          (setq sol (solve-single-equation (cadr e) (car eqvars))))

														((eql 1 ($cardinality e)) ;one equation and two or more unknowns
															   ; (print "at 1")
																	(setq sol (solve-single-equation (cadr e) (car eqvars)))
																;	(mtell "sol = ~M ~%" sol)
																	(setq sol (cdr sol)) ; remove (mlist)
																	(when sol
																		(setq sol
																			(append
																	  		sol
																	  		(mapcar #'(lambda (q) (take '(mequal) q (next-rnum-variable))) (cdr eqvars)))))
																	(push '(mlist) sol)
																	(setq sol `((mlist) ,sol)))

                             ((eql 1 (length eqvars)) ;several equations, one unknown.
														     (setq sol (redundant-equation-solve (cdr e) (car eqvars))))

														 (t  (setq sol nil)))  ;several equations, several unknown--give up.

			 		        	  (setq sol (cdr sol)) ; remove (mlist)
  					    		   (setq ssol nil)
	                     (dolist (sx sol)
								          ;; Don't panic! We have popped one equation and at least one variable.
								           (setq ssol
								   	    		 (append ssol
								        	   (mapcar #'(lambda (q) (cons sx q))
							    	        	  (solve-triangular-system
												         	(mapcar #'(lambda (s) ($substitute sx s)) eqs) vars)))))
	                       ssol))))))

;;; We replace solvex with a call to $solve -- I need to look up the meanings of ind and flag.
(defun solvex (eql varl ind flag)
	(mtell "Top of solvex ind = ~M flag = ~M ~%" ind flag)
	(setq eql (simplifya (cons '(mlist) eql) t))
	(setq varl (simplifya (cons '(mlist) varl) t))
   ($solve eql varl))

(defun dispatch-grobner (e x)
     (let ((cnds))
        (setq e (mapcar #'meqhk (cdr e))) ; remove '(mlist) and convert a=b to a-b.
        (setq e (mapcar #'try-to-crunch-to-zero e)) ;ratsimp
        (setq e (remove-if #'zerop1 e)) ; remove vanishing
        ;; We should, of course, expunge putative solutions that make a denominator vanish.
        ;; But for now, we only collect the denominators.
        (setq cnds (mapcar #'(lambda (q) ($ratdenom q)) e)); collect denominators.
        (setq e (mapcar #'$ratnumer e)) ;collect numerators
        (setq e (cons '(mlist) e))  ; return e to a Maxima list
        (setq e ($poly_reduced_grobner e x)) ;triangularize equations
        (setq e ($expand e 0 0)) ;I think poly_reduced_grobner returns unsimplified expressions
        (setq e (apply-identities-unconditionally e))))

;;; missing need to filter using cnd?
;;; Solve the CL list of equations e for the CL list of variables in x.
(defun solve-multiple-equations (e x) "Solve the CL list of equations e for the CL list of unknowns x"
 (let ((cnd) (sol) (ee nil))
  ;; We don't attempt to determine the multiplicity for multiple equations. Thus we reset
	;; $multiplicities to its default.
	 (mfuncall '$reset '$multiplicities)
	 (setq e (mapcar #'keep-float e)) ; protect floats in boxes.
	 ;; collect the domain conditions in cnd.
	 (setq cnd (reduce #'(lambda (a b) (take '(mand) a b)) (mapcar #'(lambda (q) (in-domain q x)) e)))
	 ;; The second member of equation-simplify holds multiplicity data--thus extract just the first
	 ;; member returned by equation-simplify.
 	 (setq e (mapcar #'(lambda (q) (first (equation-simplify q 1))) e))

	 (push '(mlist) e) ;convert e and x to Maxima lists.
	 (push '(mlist) x)

  	(cond  ((every #'(lambda (q) ($polynomialp q x
			    	#'(lambda (s) ($lfreeof x s))
	   			  #'(lambda (s) (and (integerp s) (>= s 0))))) (cdr e))
						(setq e (cons '(mlist) (mapcar #'unkeep-float (cdr e))))
						(setq e ($setify e)) ;convert both e and x to sets & expunge redundant eqs
			      (setq x ($setify x))
						(setq e ($listify e)) ;convert both e and x to sets & expunge redundant eqs
			      (setq x ($listify x))
						(setq e (dispatch-grobner e x))
						(setq sol ($algsys e x))
						(unkeep-float sol))
          ;; The check (< (length x) 4) is silly. But the rtest_lsquares test generates
					;; some huge equations that have no chance at a symbolic solution. For these
					;; cases, algsys runs for a long time and consumes huge amounts of memory. I'm
					;; not sure if these tests even finsh.
					((and (every #'(lambda (q) (algebraic-p q (cdr x))) (cdr e)) (< (length x) 4))
					  (mtell "Solving algebraic system e = ~M x = ~M ~%" e x)
					  (solve-algebraic-equation-system e x))
		 		(t
					 (setq ee e)
	  			 (setq e ($setify e))
	  			 (setq x ($setify x))
	  			 (setq e (triangularize-eqs e x))
	  			 (setq sol (solve-triangular-system (cdr e) (cdr x)))

					 (cond ((and $solveexplicit (null sol))
					          (mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning the empty list.~%") e x)
					 			    (simplifya (list '(mlist)) t))

                 ((and (not $solveexplicit) (null sol))
								    (mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning an implicit solutoin.~%") e x)
								    (simplifya (cons '(mlist) (mapcar #'(lambda (q) (take '(mequal) 0 q)) (cdr ee))) t))

							   (t
				       	    (setq sol (mapcar #'(lambda (q) (cons '(mlist) q)) sol))
					          (simplifya (cons '(mlist) sol) t)))))))

;;; This is the entry-level function for system level calls to solve. Solutions are pushed into the
;;; special variable *roots.

;;; The solve function is sometimes called from the integrate code. But the integration code doesn't tolerate
;;; things like solve(sin(x)=1/2,x) --> [x=(12*%pi*%z1+%pi)/6,x=(12*%pi*%z2+5*%pi)/6]. Thus we'll locally
;;; set $solve_inverse_package to *function-inverses-alt*.

;;; I think solve isn't supposed to alter $multiplicities--it's a mess.

;;; Quote from solve.lisp

;; Solve takes three arguments, the expression to solve for zero, the variable
;; to solve for, and what multiplicity this solution is assumed to have (from
;; higher-level Solve's).  Solve returns NIL.  Isn't that useful?  The lists
;; *roots and *failures are special variables to which Solve prepends solutions
;; and their multiplicities in that order: *roots contains explicit solutions
;; of the form <var>=<function of independent variables>, and *failures
;; contains equations which if solved would yield additional solutions.

(defvar $list_of_equations '(($set)))

(defun solve (e x ms)
  (when $solveverbose
      (mtell "top of ?solve ~M ~M ~M ~%" e x ms))
	;(setq $list_of_equations ($adjoin (list '(mlist) e x) $list_of_equations)) ; debugging-like thing
	(let ((sol) (mss)
				($solve_inverse_package *function-inverses-alt*) ;compatibilty mode
				($ask_mode nil)
				($use_to_poly t)
				($algebraic t)
				($gcd '$subres)
				($negdistrib t) ;not sure about this--likely needed!
				($multiplicities nil)
				(m))
		 	(setq x (if x x *var))
			   ;; clunkly workaround for bug with integrate(sqrt(1+cos(x)),x,-%pi,%pi).
				 ;; For this case, we need to solve (cos(x)+1)*sqrt(sin(x)^2/(cos(x)+1)^2+1).
				 ;; Arguably it has no solutions, but the definite integrate code needs to
				 ;; find the solution x = %pi. Some trigsimp, radcan, and factoring cancels the
				 ;; troublesome factor and allows solve to return %pi as a solution.

				 ;; To allow the cancelation of (cos(x)+1)*sqrt(2/(cos(x)+1)) with ratsimp,
				 ;; we need to set $domain to $real. All this is a bit scary. Finally extracting
				 ;; the numerator allows for some spurious solutions to sneak through.
			   (let (($domain '$real))
			 		  (setq e (apply-identities-unconditionally e))
				    (setq e (let (($logsimp t) ($logconcoeffp '$ratnump)) ($logcontract e)))
						(setq e ($num e)))

				 (setq sol ($solve e x)) ; was solve-single-equation, but x can be a non-mapatom.
				 (setq sol (reverse (cdr sol))) ; reverse makes this more consistent with standard solve.
				 (setq m
					     (cond (($listp $multiplicities)
								    	(reverse (cdr $multiplicities)))
							 (t
						  	  (mtell "Warning: multiplicities didn't get set solving ~M for ~M ~%" e x)
							    (mapcar #'(lambda (q) (declare (ignore q)) 1) sol))))

		  	(setq *roots nil)
		  	(setq *failures nil)
		  	(dolist (q sol)
			   	(setq mss (mul ms (pop m)))
			  	(cond ((and (mequalp q) (eql 0 (second q))) ; second = $lhs
			    		   (push q *failures)
				    	   (push mss *failures))
				  	  (t
			   	    	(push mss *roots)
				      	(push q *roots))))
		   ;(rootsort *roots)  not needed, I think
		   ; (rootsort *failures)
		 nil))

;;; This function solves x*exp(x) = constant. The match to x*exp(x) must be explicit; for example,
;;; lambert-w-solve is unable to solve x*exp(x)/2 = 10. When no solution is found, return nil. Of course,
;;; this function could be extended to solve more equations in terms of the Lambert W function.
(defun lambert-w-solve (e x m) "solve x exp(x) = constant where m is the multiplicity so far"
  (let ((sol) (cnst (sratsimp (sub (mult x (take '(mexpt) '$%e x)) e))))
		(cond (($freeof x cnst) ; match with x*exp(x) = cnst
			       (setq $multiplicities (take '(mlist) m))
			       (setq sol (cond ((eql $solve_inverse_package $multivalued_inverse)
		   	         		(take '(%generalized_lambert_w) (my-new-variable'$integer) cnst))
							    	(t (take '(%lambert_w) cnst))))
						(opcons 'mlist (take '(mequal) x sol)))
		    	(t nil))))

;;; Let's make sure that the old functions solvecubic and solvequartic are not called. So, replace the
;;; function definitions with a call to merror.
(defun solvecubic (x) (declare (ignore x)) (merror "solvecubic"))
(defun solvequartic (x) (declare (ignore x)) (merror "solvequartic"))
