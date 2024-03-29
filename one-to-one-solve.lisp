;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

;;; Merge two or more solution sets. The input looks like CL list of solutions,
;;; CL list of multiplicities, Maxima expression for condition (repeat). This
;;; function removes redundant solutions and it removes solutions that do not
;;; satisfy the conjunction of the conditions. It, of course, does this and
;;; maintains the correct ordering for the multiplicities.
(defun merge-solutions (&rest xxx)
   (let ((sx) (mx) (cx) (sol nil) (cnd t))
      (while xxx
    		 (setq sx (pop xxx)) ;solution
	    	 (setq mx (pop xxx)) ;multiplicities -- Maxima list
         (setq cx (pop xxx)) ;conditions --cx is a Maxima predicate
		     (setq cnd (take '(mand) cnd cx)) ;collect all conditions
			   ;; build an association list of the form solution.multiplicity
	       (setq sol (append sol (mapcar #'(lambda (a b) (cons a b)) (cdr sx) (cdr mx)))))

    ;;(displa (cons '(mlist) (mapcar #'car sol)))
    ;; remove redundant solutions
	  (setq sol (remove-duplicates sol :test #'alike1 :key #'car :from-end t))
    (setq sol (filter-solution sol cnd)) ;remove supurious solutions
		(setq mx (mapcar #'cdr sol)) ;reformulate multiplicity
		(setq sol (mapcar #'car sol)) ;reformulate solutions
		(setq $multiplicities (simplifya (cons '(mlist) mx) t))
		(simplifya (cons '(mlist) sol) t)))

(defvar *one-to-one-reduce* (make-hash-table :test #'equal))

;; attempt to solve equation c0*sin(kn0) + c1*sin(kn1) + b = 0 for x
(defun sin-sin-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   (let ((sol0) (sol1) (sol2) (mx0) (mx1) (mx2))
      (cond ((and (zerop1 b) (alike1 c0 c1)) ;c0*sin(kn0) + c0*sin(kn1) = 0
				      (setq sol0 (solve-single-equation c0 x ml use-trigsolve))
							(setq mx0 $multiplicities)
	            (setq sol1 (solve-single-equation
								   (add kn0 kn1 (mul -2 '$%pi (my-new-variable '$integer))) x ml use-trigsolve))
							(setq mx1 $multiplicities)
			   		  (setq sol2 (solve-single-equation (add kn0 (mul -1 kn1)
								   (mul -2 '$%pi (sub (my-new-variable '$integer) (div 1 2)))) x ml use-trigsolve))
              (setq mx2 $multiplicities)
							(merge-solutions sol0 mx0 t sol1 mx1 t sol2 mx2 t))

				  	((and (zerop1 b) (alike1 c0 (mul -1 c1)))	 ;c0*sin(kn0) - c0*sin(kn1) = 0
							(setq sol0 ($solve c0 x))
							(setq mx0 $multiplicities)
							(setq sol1 (solve-single-equation
								  (add kn0 kn1 (mul -2 '$%pi (sub (my-new-variable '$integer) (div 1 2)))) x ml use-trigsolve))
              (setq mx1 $multiplicities)
						  (setq sol2 (solve-single-equation
								  (add kn0 (mul -1 kn1) (mul -2 '$%pi (my-new-variable '$integer))) x ml use-trigsolve))
              (setq mx2 $multiplicities)
						  (merge-solutions sol0 mx0 t sol1 mx1 t sol2 mx2 t))
				(t
					nil))))

(setf (gethash (list '%sin '%sin) *one-to-one-reduce*) #'sin-sin-solve)

;; attempt to solve equation c0*cos(kn0) + c1*cos(kn1) + b = 0 for x
(defun cos-cos-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   (let ((sol0) (sol1) (sol2) (mx0) (mx1) (mx2))
      (cond ((and (zerop1 b) (alike1 c0 c1)) ;c0*cos(kn0) + c0*cos(kn1) = 0
				      (setq sol0 (solve-single-equation c0 x ml use-trigsolve))
							(setq mx0 $multiplicities)

	            (setq sol1 (solve-single-equation
								   (add kn0 kn1 (mul -2 '$%pi (sub (my-new-variable '$integer) (div 1 2)))) x ml use-trigsolve))
							(setq mx1 $multiplicities)

			   		  (setq sol2 (solve-single-equation  (add kn0 (mul -1 kn1)
								   (mul -2 '$%pi (sub (my-new-variable '$integer) (div 1 2)))) x ml use-trigsolve))
							(setq mx2 $multiplicities)

							(merge-solutions sol0 mx0 t sol1 mx1 t sol2 mx2 t))

				  	((and (zerop1 b) (alike1 c0 (mul -1 c1)))	 ;c0*cos(kn0) - c0*cos(kn1) = 0
							(setq sol0 (solve-single-equation c0 x ml use-trigsolve))
							(setq mx0 $multiplicities)

							(setq sol1 (solve-single-equation
								 (add kn0 kn1 (mul -2 '$%pi (my-new-variable '$integer))) x ml use-trigsolve))
							(setq mx1 $multiplicities)

						  (setq sol2 (solve-single-equation
								 (add kn0 (mul -1 kn1) (mul -2 '$%pi (my-new-variable '$integer))) x ml use-trigsolve))
							(setq mx2 $multiplicities)

							(merge-solutions sol0 mx0 t sol1 mx1 t sol2 mx2 t))
				(t
					nil))))

(setf (gethash (list '%cos '%cos) *one-to-one-reduce*) #'cos-cos-solve)

;;; Attempt to solve equation c0*sin(kn0) + c1*cos(kn1) + b = 0 for x. When c0 and
;;; are both real and kn0 = kn1, solve sqrt(c0^2+c1^2)*cos(kn0 - atan2(c0 c1)) + b.

;;; When either c0 or c1 isn't real, give up. We'll do an ask-boolean to determine
;;; if c0 & c1 are real. I suppose we could handle the case where c0 = c*p & c1 = c*q,
;;; where c is complex and both p & q are real.
(defun sin-cos-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   (let ((r) (ph) (eq))
			(cond ((and
				 		   (alike1 kn0 kn1)
				       (my-ask-boolean (mm= c0 (take '($conjugate) c0))) ;is c0 real?
               (my-ask-boolean (mm= c1 (take '($conjugate) c1)))) ;is c1 real?
	         (setq r (simpnrt (add (mul c0 c0) (mul c1 c1)) 2))
           (setq ph (take '($atan2) c0 c1))
			  	 (setq eq (add (mul r (take '(%cos) (sub kn0 ph))) b))
			  	 (solve-single-equation eq x ml use-trigsolve))
			(t nil))))

(setf (gethash (list '%sin '%cos) *one-to-one-reduce*) #'sin-cos-solve)

(defun cos-sin-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
    (sin-cos-solve x c1 kn1 c0 kn0 b ml use-trigsolve))

(setf (gethash (list '%cos '%sin) *one-to-one-reduce*) #'cos-sin-solve)

;; attempt to solve c0*tan(kn0) + c1*tan(kn1) + b = 0 for x
(defun tan-tan-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
    (let ((sol0) (mx0) (sol1) (mx1))
        (cond ((and (alike1 c0 c1) (zerop1 b)) ;; c0*tan(kn0) + c1*tan(kn1) = 0
                 (setq sol0 (solve-single-equation
									    (add kn0 kn1 (mul '$%pi (my-new-variable '$integer))) x ml use-trigsolve))
				    		 (setq mx0 $multiplicities)
                 (setq sol1 (solve-single-equation c0 x ml use-trigsolve))
				    		 (setq mx1 $multiplicities)
				    		 (merge-solutions sol0 mx0 t sol1 mx1 t))

          ((and (alike1 c0 (mul -1 c1)) (zerop1 b)) ;; c0*tan(kn0) - c1*tan(kn1) = 0
			    				(setq sol0 (solve-single-equation
										(add kn0 (mul -1 kn1) (mul '$%pi (my-new-variable '$integer))) x  ml use-trigsolve))
						    	(setq mx0 $multiplicities)
                  (setq sol1 (solve-single-equation c0 x ml use-trigsolve))
						     	(setq mx1 $multiplicities)
						      (merge-solutions sol0 mx0 t sol1 mx1 t))
              (t
                nil))))

(setf (gethash (list '%tan '%tan) *one-to-one-reduce*) #'tan-tan-solve)

;; attempt to solve c0*e1^(kn0) + c1*e2^(kn1) + b = 0 for x
(defun exp-exp-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   (let ((e))
      (cond ((and
		           (zerop1 b)
		           (alike1 (second kn0) (second kn1))
		      		 ($freeof x (second kn0)) ($freeof x (second kn1)))
			     		(setq e (let (($logexpand '$super))
					    	  (add
							    	(take '(%log) (mul c0 kn0))
					          (mul -1 (take '(%log) (mul -1 c1 kn1)))
							    	(mul 2 '$%pi '$%i  (my-new-variable '$integer)))))
			  	(solve-single-equation e x ml use-trigsolve))
					(t
						nil))))

(setf (gethash (list 'mexpt 'mexpt) *one-to-one-reduce*) #'exp-exp-solve)

;; attempt to solve c0*asin(kn0) + c1*atan(kn1) + b = 0 for x
(defun asin-atan-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   (cond ((and (alike1 kn0 kn1) (alike c0 (mul -1 c1)) (zerop1 b))
	          (solve-single-equation kn0 x ml use-trigsolve))
				  (t nil)))

(setf (gethash (list '%asin '%atan) *one-to-one-reduce*) #'asin-atan-solve)
(setf (gethash (list '%atan '%asin) *one-to-one-reduce*) #'asin-atan-solve)

;; attempt to solve c0*acos(kn0) + c1*atan(kn1) + b = 0 for x
(defun acos-atan-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   (cond ((and (alike1 kn0 kn1) (alike c0 (mul -1 c1)) (zerop1 b))

	          (solve-single-equation
							(sub kn0 (power (div (sub (power 5 (div 1 2)) 1) 2) (div 1 2)))
							 x ml use-trigsolve))
				  (t nil)))
(setf (gethash (list '%acos '%atan) *one-to-one-reduce*) #'acos-atan-solve)
(setf (gethash (list '%atan '%acos) *one-to-one-reduce*) #'acos-atan-solve)

;; attempt to solve c0*abs(kn0) + c1*abs(kn1) + b = 0 for x
(defun abs-abs-solve  (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
   	(let ((sol0) (sol1) (sol2) (sol3) (mx0) (mx1) (mx2) (mx3) (eq))
		      (cond ((and (among x kn0) (among x kn1))
				  	(setq eq (add (mul c0 kn0) (mul c1 kn1) b))
				  	(setq sol0 (solve-single-equation eq x ml use-trigsolve))
				  	(setq mx0 $multiplicities)
				  	(setq sol0 (filter-solution-x sol0 (take '(mand) (mm<= 0 kn0) (mm<= 0 kn1))))

				  	(setq eq (add (mul c0 kn0) (mul -1 c1 kn1) b))
				  	(setq sol1 (solve-single-equation eq x ml use-trigsolve))
				  	(setq mx1 $multiplicities)
				  	(setq sol1 (filter-solution-x sol1 (take '(mand) (mm<= 0 kn0) (mm<= kn1 0))))

				  	(setq eq (add (mul -1 c0 kn0) (mul c1 kn1) b))
				  	(setq sol2 (solve-single-equation eq x ml use-trigsolve))
				  	(setq mx2 $multiplicities)
				  	(setq sol2 (filter-solution-x sol2 (take '(mand) (mm<= kn0 0) (mm<= 0 kn1))))

				  	(setq eq (add (mul -1 c0 kn0) (mul -1 c1 kn1) b))
				  	(setq sol3 (solve-single-equation eq x ml use-trigsolve))
				  	(setq mx3 $multiplicities)
				  	(setq sol3 (filter-solution-x sol3 (take '(mand) (mm<= kn0 0) (mm<= kn1 0))))

			  		(merge-solutions sol0 mx0 t sol1 mx1 t sol2 mx2 t sol3 mx3 t))
				(t nil))))

(setf (gethash (list 'mabs 'mabs) *one-to-one-reduce*) #'abs-abs-solve)

;; attempt to solve c0*exp(kn0) + c1*exp(kn1) + b = 0 for x
(defun mexpt-mexpt-solve  (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
  (let ((sol) (mx))
  	(cond ((and (zerop1 b) ($freeof x (second kn0)) ($freeof x (second kn1)))
		        (cond ((zerop1 (add c0 c1)) ;looking at a^X = b^Y
						        (setq eq (add
											   (mul (third kn0) (take '(%log) (second kn0)))
												 (mul -1 (third kn1) (take '(%log) (second kn1)))
												 (mul 2 '$%pi '$%i (my-new-variable '$integer)))))
								  (t	;looking at c0 a^X + c1 b^Y	= 0
	                   (setq eq (add
					              (take '(%log) (div (mul -1 c0) c1))
					              (mul  (third kn0) (take '(%log) (second kn0)))
			 		              (mul  -1 (third kn1) (take '(%log) (second kn1)))
									    	(mul 2 '$%pi '$%i (my-new-variable '$integer))))))
		      	  	(setq sol (solve-single-equation eq x ml use-trigsolve)))
           ((and (zerop1 b) ($freeof x (third kn0)) ($freeof x (third kn1))
				        (alike1 (third kn0) (third kn1)) (zerop1 (add c0 c1)))
					  	(setq eq (sub
							         (second kn1)
											 (mul (second kn0)
												 ($polarform (take '(mexpt) '$%e
												    (div (mul 2 '$%pi '$%i (my-new-variable '$integer)) (third kn0)))))))
						(setq sol (solve-single-equation eq x ml use-trigsolve)))

				(t nil))))

(setf (gethash (list 'mexpt 'mexpt) *one-to-one-reduce*) #'mexpt-mexpt-solve)

;;; Attempt to solve c0*log(kn0) + c1*log(kn1) + b = 0 for x. We convert this equation
;;; into  kn0^c0 * kn1^c1 - exp(-b) = 0.
(defun log-log-solve (x c0 kn0 c1 kn1 b &optional (ml 1) (use-trigsolve nil))
  ;(mtell "c0 =  ~M kn0 = ~M,  c1 = ~M, kn1 = ~M, b = ~M  ~%" c0 kn0 c1 kn1 b)
	(let ((eq))
	   (setq eq (sub (mul (power kn0 c0) (power kn1 c1))  (power '$%e (mul -1 b))))
     (solve-single-equation eq x ml use-trigsolve)))

(setf (gethash (list '%log '%log) *one-to-one-reduce*) #'log-log-solve)

(defun kernelize-fn (e fn &optional (subs nil))
		(let ((g (gensym)) (kn nil) (xop) (xk) (eargs nil))
					(cond (($mapatom e) (list e subs))
				    	   ((funcall fn e)
								   (setq kn (assoc e subs :test #'alike1)) ;is it a known kernel?
								   (cond (kn
										       (list (cdr kn) subs)) ; it's a known kernel--use the value from the association list subs
									   	   (t
									   	    (list g (acons e g subs))))) ; it's unknown--append a new key/value to subs

								 (t ; map kernelize onto the argument list and build up the association list subs
								  (setq xop (list (caar e)))
								  (setq e (cdr e))
								  (dolist (xk e)
									  (setq xk (kernelize-fn xk fn subs))
									  (push (first xk) eargs)
									  (setq subs (second xk)))
								  (list (simplifya (cons xop (reverse eargs)) t) subs)))))


;; affine_p(p,vars) returns true iff p is an affine polynomial in vars, that is,
;; that it is a polynomial in vars (a list) whose total degree in vars is no greater than 1.
;; Stavros Macrakis wrote $affine_p and the tests (see rtest_fourier_elim.mac) for this function.

;; I'm not sure I want to load fourier_elim, so here is a re-named version of this function.

(defun $myaffine_p (p vl)
  (setq vl (require-list vl "affine_p"))
  (let* (($ratfac nil)
	 ($ratprint nil)
	 (rat ($rat p)))
    (and (eq (caar rat) 'mrat) ; don't handle bags etc.
	 (not (memq 'trunc (car rat))) ; don't handle taylor series (even in other vars)
	 (let* (;; in affine poly, only numer can include vars
		(num ($ratnumer rat))
		;; (what vars are actually used; cf. $ratfreeof/$showratvars)
		(numvars (caddar (minimize-varlist num)))
		;; ... and denominator cannot depend on vars at all
		(den ($ratdenom rat))
		(denvars (caddar (minimize-varlist den)))
		(truncnum))
	   (and
	    ;; everything in denvars must be freeof vl
	    (every #'(lambda (term)
		       (every #'(lambda (var) (freeof var term)) vl))
		   denvars)
	    ;; everything in numvars must be either in vl or freeof vl
	    (every #'(lambda (term)
		       (or (memalike term vl)
			   (every #'(lambda (var) (freeof var term)) vl)))
		   numvars)
	    ;; there must be no terms of degree > 1
	    (progn
	      ;; calculate p without terms of degree > 1
	      (let (($ratwtlvl 1)
		    ;; ignore prevailing *ratweights (don't append to new ones)
		    (*ratweights (mapcar #'(lambda (x) (cons x 1)) vl)))
		;; adding ($rat 0) performs the truncation; just ($rat num) does not
		(setq truncnum (add ($rat 0) num)))
	      ;; subtract out: any terms of degree > 1?
	      (equal 0 (ratdisrep (sub num truncnum)))))))))

;;; Attempt to solve an equation of the form c0 F(kn0) + c1 G(kn1) + b, where c0, c1,
;;; and b are free of the unknown x, and at least one of the kernels kn0 & kn1 depends on
;;; x. The pair of functions (F,G) must be listed in the hashtable *one-to-one-reduce*.
;;; Once we find c0,c1,b, kn0, and kn1, all that is left is to dispatch the appropriate
;;; function from the hashtable.
(defun one-to-one-solve (e x m zzz)
 (when $solveverbose
	 (mtell "top of one-one-solve e = ~M  x = ~M ~%" e x))

  (let ((ee) (subs nil) (gvars nil) (fn nil) (c0 nil) (c1 nil) (b nil))
     (flet ((is-a-kernel (e)
	           (and
						  	(consp e)
						  	(consp (car e))
						  	(member (caar e) (list '%sin '%cos '%tan '%log 'mexpt '%atan '%asin '%acos 'mabs) :test #'eql))))
		     	  (setq ee (kernelize-fn e #'is-a-kernel))
		    		(setq subs (second ee))
						(setq gvars (mapcar #'cdr subs)) ;CL
            (setq ee (first ee))
						(setq subs (mapcar #'car subs)) ;CL list of kernels
						(cond ((and
							        (eql 2 (length gvars))
											($myaffine_p ee (cons '(mlist) gvars)))

									(setq fn (gethash (mapcar #'caar subs) *one-to-one-reduce*))
									(mtell "fn = ~M ~%" fn)
									(when fn
				    					(setq c0 ($ratcoef ee (first gvars)))
					    				(setq c1 ($ratcoef ee (second gvars)))
							    		(setq b ($substitute 0 (first gvars) ($substitute 0 (second gvars) ee)))
									   	(setq kn0 (if (mexptp (first subs)) (first subs)  (second (first subs))))
										  (setq kn1 (if (mexptp (second subs)) (second subs)  (second (second subs))))
							   	  	(funcall fn x c0 kn0 c1 kn1 b m zzz)))
							   (t (one-to-one-solve-alt e x m zzz))))))

 ;;; Attempt to solve an equation of the form c0 F(kn0) + c1 G(kn1) + b, where c0, c1,
 ;;; and b are free of the unknown x, and and both kernels kn0 & kn1 depend on
 ;;; x. The pair of functions (F,G) must be listed in the hashtable *one-to-one-reduce*.
 ;;; Once we find c0,c1,b, kn0, and kn1, all that is left is to dispatch the appropriate
 ;;; function from the hashtable.

 ;;; likely one-to-one-solve and one-to-one-solve-alt should be merged. For the equation
 ;;; the log(x) + log(1-x) = log(42), one-to-one-solve finds three log kernels, then it fails.
 ;;; But this function is able to solve the equation.
(defun one-to-one-solve-alt (e x m zzz)
 (when $solveverbose
	 (mtell "top of one-one-solve-alt e = ~M  x = ~M ~%" e x))

  (let ((ee) (subs nil) (gvars nil) (fn nil) (c0 nil) (c1 nil) (b nil))
     (flet ((is-a-kernel (e)
	           (and
						  	(consp e)
						  	(consp (car e))
						  	(member (caar e) (list '%sin '%cos '%tan '%log 'mexpt '%atan '%asin '%acos 'mabs) :test #'eql)
								(among x e))))
		     	  (setq ee (kernelize-fn e #'is-a-kernel))
		    		(setq subs (second ee))
						(setq gvars (mapcar #'cdr subs)) ;CL
            (setq ee (first ee))
						(setq subs (mapcar #'car subs)) ;CL list of kernels
						(cond ((and
							        (eql 2 (length gvars))
											($myaffine_p ee (cons '(mlist) gvars)))

									(setq fn (gethash (mapcar #'caar subs) *one-to-one-reduce*))
									(mtell "fn = ~M ~%" fn)
									(when fn
				    					(setq c0 ($ratcoef ee (first gvars)))
					    				(setq c1 ($ratcoef ee (second gvars)))
							    		(setq b ($substitute 0 (first gvars) ($substitute 0 (second gvars) ee)))
									   	(setq kn0 (if (mexptp (first subs)) (first subs)  (second (first subs))))
										  (setq kn1 (if (mexptp (second subs)) (second subs)  (second (second subs))))
							   	  	(funcall fn x c0 kn0 c1 kn1 b m zzz)))))))
