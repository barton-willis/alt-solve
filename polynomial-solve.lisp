
;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of polynomial equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.

(in-package :maxima)

(defmvar *solve-factors-biquadratic* t)
;;; Make an extra effort to simplify the expression e to zero, but respect principal branch
;;; cuts (don't use radcan, for example).
(defun try-to-crunch-to-zero (e) "Ratsimp with algebraic = true and domain = complex."
	(let (($algebraic t) ($domain '$complex)) (sratsimp e))) ; was (fullratsimp e)))

;;; Solve a*x + b = 0 for x. Return both a CL list of the solution (-b/a) and a CL list of the multiplicity.
(defun my-solve-linear (x a b) "Return solution and multiplicity of ax+b=0."
	(values (list (take '(mequal) x (try-to-crunch-to-zero (div (mul -1 b) a)))) (list 1)))

;;; Return a CL list of the solutions to the quadratic equation ax^2+bx+c = 0 and a CL list of the
;;; multiplicities. The function simpnrt makes some effort to find even power factors.

;;; We don't special case b = 0; arguably x = +/- sqrt(-c a)/a is simpler than is
;;; x = +/- sqrt(c/a); additionally when I tried special casing b = 0, the testsuite had lots of problems.
(defun my-solve-quadratic (x a b c) "Return solutions and multiplicities of ax^2+bx+c=0."
	(let ((d (sub (mul b b) (mul 4 a c))))
		 (setq d (try-to-crunch-to-zero d))
		  (cond ((zerop1 d)
			   	 ;(mtell "Found multiple root of quadratic ~%")
				    (values (list (take '(mequal) x (div b (mul -2 a)))) (list 2)))
		  	   (t
		   		  (setq d (simpnrt d 2)) ;any branch is OK
			     	 (values
			  	    (list
			   		  (take '(mequal) x (try-to-crunch-to-zero (mul -1 (div (add d b) (mul 2 a)))))
			   		  (take '(mequal) x (try-to-crunch-to-zero (div (sub d b) (mul 2 a)))))
				      (list 1 1))))))

;;; Return a CL list of the solutions to the cubic equation a x^3 + b x^2 + c x + d= 0 and a CL list of the
;;; multiplicities.
(defun my-solve-cubic (x a b c d) "Return solutions and multiplicities of ax^3+bx^2+cx+d=0."
	(let ((d0) (discr) (d1) (K) (xi) (xii) (sol nil) (n))
		 ;(print "solving cubic" t)
		 (setq discr (add (mul 18 a b c d) (mul -4 b b b d) (mul b b c c) (mul -4 a c c c) (mul -27 a a d d)))
		 (setq discr (try-to-crunch-to-zero discr))

		 (setq d0 (try-to-crunch-to-zero (sub (mul b b) (mul 3 a c))))
		 (setq d1 (try-to-crunch-to-zero  (add (mul 2 b b b) (mul -9 a b c) (mul 27 a a d))))
		 (setq K (add d1 (simpnrt (mul -27 a a discr) 2)))
		 (setq K (div K 2))
		 (setq K (try-to-crunch-to-zero K))
		 (when (zerop1 K)
			  (setq K (div (sub d1 (simpnrt (mul -27 a a discr) 2)) 2))
  		      (setq K (try-to-crunch-to-zero K)))

		 (setq K (simpnrt k 3))
		 (cond ((and (zerop1 discr) (zerop1 d0))
				(values (list (div b (mul -3 a))) (list 3)))

			   ((zerop1 discr)
				(setq $multiplicities (list 2 1))
				(values
				 	(list (div (sub (mul 9 a d) (mul b c)) (mul 2 d0))
						  (div (add (mul 4 a b c) (mul -9 a a d) (mul b b b)) (mul a d0)))
				    (list 2 1)))
			   (t
				(setq xi (list 1 (div (sub (mul '$%i (simpnrt 3 2)) 1) 2) (div (sub (mul -1'$%i (simpnrt 3 2)) 1) 2)))
				(setq n 0)
				(while (< n 3)
					   (incf n 1)
					   (setq xii (pop xi))
					   (push (take '(mequal) x (div (add b (mul xii K) (div d0 (mul xii K))) (mul -3 a))) sol))
				(values sol (list 1 1 1))))))

;;; Solve the biquadratic p4 x^4 + p2 x^2 + p0 = 0. Return both a CL list of the solutions and
;;; the list of the multiplicities.
(defun my-solve-biquadratic (x p4 p2 p0) "Solve the biquadratic p4 x^4 + p2 x^2 + p0 = 0."
	(multiple-value-bind (sol m) (my-solve-quadratic x p4 p2 p0)
		(setq sol (mapcar #'third sol)) ; remove x = part of solutions
		(setq sol (mapcan #'(lambda (q) (setq q (simpnrt q 2)) (list (mul -1 q) q)) sol))
		(setq sol (mapcar #'(lambda (q) (take '(mequal) x q)) sol))
		(setq m (mapcan #'(lambda (q) (list q q)) m))
		(values sol m)))

;;; Lodovico Ferrari's method for quartic equations. First, eliminate the cubic term using the
;;; translation x --> x - p3/4p4. Second, solve the cubic resolvent. The loop over the solutions
;;; to the cubic selects the least complicated solution to the cubic resolvent. Third solve two
;;; quadratic equations. And fourth and finally undo the translation x --> x - p3/4p4.

;;; This code does not detect the quasi-palindromic case.

;;; Solve the quartic p4 x^4 + p3 x^3 + p2 x^2 + p1 x + p0=0. Return both a CL list of the solutions and the
;;; list of the multiplicities.
(defun my-solve-quartic (v p4 p3 p2 p1 p0) "Return solutions and multiplicities of p4 v^4+p3 v^3+p2 v^2+ p1 v + p0=0."
	(mtell "solving quartic ~%")
	;(displa `((mlist) ,p4 ,p3 ,p2 ,p1 ,p0))
	(let ((pp4) (pp3) (pp2) (pp1) (pp0) (m) (g (gensym)) (x) (mm) (shift))

		 (cond ((and (zerop1 p3) (zerop1 p1))
				(my-solve-biquadratic v p4 p2 p0))
			 (t
			  (setq shift (div p3 (mul 4 p4)))
			  ;; eliminate the cubic term with a shift and make monic
			  (setq pp4 1)
			  (setq pp3 0)
			  ;; (8*p2*p4-3*p3^2)/(8*p4^2)
			  (setq pp2 (div (add (mul 8 p2 p4) (mul -3 p3 p3)) (mul 8 p4 p4)))
			  ;; (8*p1*p4^2-4*p2*p3*p4+p3^3)/(8*p4^3)
			  (setq pp1 (div (add (mul 8 p1 p4 p4) (mul -4 p2 p3 p4) (mul p3 p3 p3)) (mul 8 p4 p4 p4)))
			  ;; (256*p0*p4^3-64*p1*p3*p4^2+16*p2*p3^2*p4-3*p3^4)/(256*p4^4)
			  (setq pp0 (div (add (mul 256 p0 (power p4 3)) (mul -64 p1 p3 p4 p4) (mul 16 p2 p3 p3 p4)
								  (mul -3 (power p3 4))) (mul 256 (power p4 4))))
			  ;;cubic resolvent
			  (setq m (add (mul 8 (power g 3)) (mul 8 pp2 (power g 2)) (mul (sub (mul 2 pp2 pp2) (mul 8 pp0)) g)
						   (mul -1 pp1 pp1)))

			  ;; We would like the simpliest nonzero zero of m. Accordingly it behooves us to factor m.
			  (setq m (polynomial-solve ($gfactor m) g)) ;was ($solve m g)
			  (setq $multiplicities nil)
			  (setq m (mapcar #'third (cdr m))) ;remove '(mlist) and extract $rhs
			  ;; remove members that are explicitly zero and sort according to my-size.
			  (setq m (sort (remove-if #'zerop1 m) #'(lambda(a b) (< (my-size a) (my-size b)))))
			  (setq m (car m)) ;set m to the "simplest" member of m
			  (setq x m)
			  (setq mm (simpnrt (mul 2 m) 2))
			  (multiple-value-bind (sol1 ms1)
				  (my-solve-quadratic x 1 mm  (add (div pp2 2) m (div pp1 (mul -2 mm))))
				  (multiple-value-bind (sol2 ms2)
					  (my-solve-quadratic x 1 (mul -1 mm) (add (div pp2 2) m (div pp1 (mul 2 mm))))
					  (setq sol1 (mapcar #'third sol1)) ;third was $rhs
					  (setq sol2 (mapcar #'third sol2))
					  (values (mapcar #'(lambda (q) (take '(mequal) v (sub q shift))) (append sol1 sol2)) (append ms1 ms2))))))))

;;; Solve p=0 using polynomial decomposition. I'm not sure this always gets the multiplicities correct.
(defun poly-solve-by-decomp (pp x) "Solve p=0 using polynomial decomposition."
	(let ((sol) (p) (pk) ($solvedecomposes nil) ($solveexplicit t))
		  (setq p (cdr ($polydecomp pp x)))
		  (catch 'bailout (setq sol nil)
				 (setq sol (cdr (polynomial-solve (pop p) x)))

				 (when ($emptyp sol)
					 (set sol nil)
					 (throw 'bailout nil))

				 (setq sol (mapcar #'third sol))
				 (while p
						(setq pk (pop p))
						(setq sol (mapcan #'(lambda (q) (mapcar #'third (cdr (polynomial-solve (sub pk q) x)))) sol)))
				 (mapcar #'(lambda (q) (take '(mequal) x q)) sol))

		   (setq $multiplicities (mapcar #'(lambda (q) (declare (ignore q)) 1) sol))
		   (setq $multiplicities (cons '(mlist) $multiplicities))

		   (cond (sol
				  (mapcar #'(lambda (q) (take '(mequal) x q)) sol))
			     (t (list (take '(mequal) 0 pp))))))

;;; True iff e is a biquadraic in the variable x.
(defun biquadratic-p (e x) "True iff e is a biquadraic in the variable x."
	(and (eql 4 ($hipow e x))
		 (zerop1 ($ratcoef e x 3))
		 (zerop1 ($ratcoef e x 1))))

;;; Solve the degree six cyclotomic polynomials. When the input isn't cyclotomic, return nil. Special casing all
;;; this is somewhat error prone--a general cyclotomic polynomial detector and solver might be more robust.
(defun solve-cyclotomic-polynomial-degree-6 (cfs) "Solve the degree six cyclotomic polynomials."
	(let ((x) (lc) (sol nil))
		 (setq x (pop cfs))
		 (setq lc (first cfs))
		 (setq cfs (mapcar #'(lambda (q) (div q lc)) cfs))

		 (cond ((every #'alike1 cfs (list 1 1 1 1 1 1 1))
				 ;(mtell "solved 6th cyclotomic~%")
			 	 (setq sol (mapcar #'(lambda (s) (div s 7)) (list 2 4 6 8 10 12))))

				((every #'alike1 cfs (list 1 -1 1 -1 1 -1 1))
				 ;(mtell "solved 6th cyclotomic~%")
				 (setq sol (mapcar #'(lambda (s) (div s 7)) (list 1 3 5 9 11 13))))

			 	((every #'alike1 cfs (list 1 0 0 -1 0 0 1))
				  ;(mtell "solved 6th cyclotomic~%")
				 (setq sol (mapcar #'(lambda (s) (div s 9)) (list 1 11 13 5 7 17))))

	            ((every #'alike1 cfs (list 1 0 0 1 0 0 1))
				  ;(mtell "solved 6th cyclotomic~%")
				  (setq sol (mapcar #'(lambda (s) (div s 9)) (list 2 4 5 7 10)))))

			(values  (mapcar #'(lambda (q) (take '(mequal) x (power '$%e (mul '$%i '$%pi q)))) sol)
					 (mapcar #'(lambda (q) (declare (ignore q)) 1) sol))))

;;; Solve a x^n + b = 0 for x. Set the $multiplicities and return a CL list of the solutions. The optional
;;; variable mx is the multiplicity so far. For degrees four or less, this function returns nil--lower degree
;;; polynomials need to be solved by my-solve-linear & friends. That might allow equations to be represented
;;; in a less surprising way.

(defun solve-poly-x^n+b (p x &optional (mx 1)) "Solve a x^n + b = 0 for x."
	(let ((a) (b) (sol nil) (n) (k 0) ($algebraic t) ($domain '$complex) ($m1pbranch t))
		 (setq p ($expand p))
		 (setq n ($hipow p x))
		 (when (> n 2)
			 (setq a ($coeff p x n))
			 (setq b (try-to-crunch-to-zero (mul -1 (sub p (mul a (power x n))))))
			 (when ($freeof x b)
			   (mtell "doing solve-poly-x^n+b; p = ~M  ~%" p)
				 (setq $multiplicities nil)
				 (cond ((zerop1 b) ;solve x^n=0
				    	  	 (push (take '(mequal) x 0) sol)
					    	   (push (mul mx n) $multiplicities))

								((> n 12) ; magic numbers 12 for no particular reason
		 		 					 (setq $multiplicities (list 1))
		 		 					 (setq sol (mul (take '(mexpt) '$%e (div (mul 2 '$%pi '$%i (my-new-variable '$integer)) n))
		 		 								(simpnrt (div b a) n)))
		 		 						(setq sol (list (take '(mequal) x sol))))

				       (t
				     	  	(setq b (simpnrt (try-to-crunch-to-zero (div b a)) n))
					       	(while (< k n)
						  	     (push (take '(mequal) x (mul b (power '$%e (div (mul 2 '$%pi '$%i k) n)))) sol)
							       (push mx $multiplicities)
							       (incf k))))
				      (push '(mlist) $multiplicities)
			        (setq $multiplicities (simplifya $multiplicities t))))
	      sol))

;;; Solve e=0 for x, where e is a polynomial in x. The optional variable mx gives the multiplicity so far.
;;; To solve, for example, (x^2+x+1)^3, the variable mx would be 3 and the polynomial x^2+x+1.

;;; This function doesn't check that the input e is a polynomial.

;;; The silly option variable *solve-factors-biquadratic* is explained in solve_alt.lisp. This mechanism could be
;;; expunged, resulting in a handful of correct, but failed testsuite tests.

;;; Incidentally: gfactor(2+(-sqrt(a^2+4)+a)*x) --> ((a-sqrt(a^2+4))*(2*x-sqrt(a^2+4)-a))/2.

;;; I'm not sure why domain is set to complex. It's my understanding that algsys eliminates spurious solutions by
;;; explicitly checking the putative solutions. It seems that some so-called simplifications such as sqrt(x^2) --> |x|
;;; can cause this mechanism in algsys to fail. To avoid some such cases, let's set domain to complex.

;;; I've experimented with gfactor or factor---gfactor does things like

;;;(%i1)	gfactor((-sqrt(a^2+4))*x+1);
;;;(%o1)	-(a^2*x+4*x-sqrt(a^2+4))/sqrt(a^2+4)

;;; This result is bogus when a = 2*%i. But the test suite has

;;; g2917785^5+sqrt(2)*g2917785^4-4*g2917785^3-2^(5/2)*g2917785^2+4*g2917785+2^(5/2)

;;; using gfactor allows Maxima to solve this equation.

(defun polynomial-solve (e x &optional (mx 1)) "Solve e=0 for x, where e is a polynomial in x and mx is a multiplicity."
	(let ((ee e) (n) (m) (sol) (k 0) (cfs) (xsol) ($domain '$complex) ($algebraic t) (p-multiplicities nil))
	   ;; Build up the multiplicities in the CL list p-multiplicities.
		 ;; Factoring isn't a universal win; for example x^105-1=0. So before we factor, look for equations of the
		 ;; form ax^n+b with n > 4. We could allow n to be any positive integer, but this causes more testsuite
		 ;; failures.
		 (setq sol (solve-poly-x^n+b e x mx))
		 (cond (sol
				(simplifya (cons '(mlist) sol) t))
			 (t
			  (setq sol nil)
			  (when (and $solvefactors (or *solve-factors-biquadratic* (not (biquadratic-p e x))))
				  (setq e ($gfactor e)))
			  (setq e (if (mtimesp e) (cdr e) (list e)))
			  (dolist (q e)
				  (setq m mx)
				  (when (mexptp q)
					  (setq m (mul mx (third q)))
					  (setq q (second q)))

				  (setq n ($hipow q x))
				  (setq k 0)
				  (setq cfs nil)
				  (while (<= k n)
						 (push (try-to-crunch-to-zero ($ratcoef q x k)) cfs)
						 (incf k 1))

				  (push x cfs)
				(multiple-value-bind (zzz mss)
					(cond
						((eql n 0)
						 (values nil nil))
						((eql n 1)
						 (apply 'my-solve-linear cfs))
						((eql n 2)
						 	(apply 'my-solve-quadratic cfs))
						((eql n 3)
							(apply 'my-solve-cubic cfs))
						((eql n 4)
							(apply 'my-solve-quartic cfs))

						((and (eql n 6) (solve-cyclotomic-polynomial-degree-6 cfs)))

						((and (> n 4) $solvedecomposes)
						 (setq q ($expand q))
						 (setq xsol (poly-solve-by-decomp q x))
						 (when $solveexplicit
							 (setq xsol (remove-if #'(lambda (q) (eql 0 ($lhs q))) xsol)))
						 (values xsol (mapcar #'(lambda (w) (declare (ignore w)) 1) xsol)))

						((> n 4)
						  (cond
								($solveexplicit
									(mtell (intl:gettext "Solve: No method for solving ~M for ~M; returning the empty list.~%") ee x)
									(values nil nil))
								(t
									(values (list (take '(mequal) 0 q)) (list 1))))))
					(setq sol (append sol zzz))
					(setq p-multiplicities (append p-multiplicities (mapcar #'(lambda (s) (mul s m)) mss)))))
				  (setq $multiplicities (simplifya (cons '(mlist) p-multiplicities) t))
			  	(simplifya (cons '(mlist) sol) t)))))
