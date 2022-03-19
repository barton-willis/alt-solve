;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations and systems of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

(defun my-real (e)
   ;(try-to-crunch-to-zero (div (add e (take '($conjugate) e)) 2)))
	 ($realpart e))

(defun my-imag (e)
	 ;(try-to-crunch-to-zero (div (sub e (take '($conjugate) e)) (mul 2 '$%i))))
	 ($imagpart e))

(defvar *function-inverses* (make-hash-table))

(defun power-inverse-standard-xxx (q a)
  ;;(mtell "top of power-inverse-standard q = ~M  a = ~M ~%" q a)
	(let ((mag-q (take '(mexpt) (mul q (take '($conjugate) q)) (div 1 2)))
	      (ph (take '($parg) q)))

      ;;(mtell "mag-q = ~M  phase = ~M ~%" mag-q ph)
			(list (mul (take '(mexpt) mag-q (div 1 a))
				(take '(mexpt) '$%e (mul '$%i (div (add ph
					(mul 2 '$%pi (my-new-variable '$integer))) a)))))))

(defun power-inverse-standard (q a)
  ;;(mtell "top of power-inverse-standard q = ~M  a = ~M ~%" q a)
	(let ((kmax) (kmin) (sol nil) (xxx) (ph) (cnd) (ok) ($m1pbranch t) ($domain '$complex))

		 (cond
			 ((and (integerp a) (> a 0))
			  (setq kmin 0)
			  (setq kmax a))

			 ((and (integerp (div 1 a)) (> (div 1 a) 0))
			  (setq ph (take '($parg) q))
			  (setq cnd (take '($%and)
							  (take '(mlessp) (mul -1 '$%pi a) ph)
							  (take '(mleqp) ph (mul '$%pi a))))

			 ; (setq ok (let (($solve_ignores_conditions nil)) (my-ask-boolean cnd)))
			 (setq ok (my-ask-boolean cnd))
			  (cond (ok
					 (setq kmax (div 1 a))
			  	     (setq kmin (- kmax 1)))
				    (t
					  (setq kmax 0)
			  	      (setq kmin 0))))

			 (t
			  (setq kmax (take '($floor) (sub (div (take '(mabs) a) 2) (div (take '($parg) q) (mul 2 '$%pi)))))
			  (setq kmin (sub (div (take '(mabs) a) -2) (div (take '($parg) q) (mul 2 '$%pi))))))

		 (cond
			 ((and (zerop1 q) (mgrp a 0)) (list 0)) ;x^a = 0, where a >0
			 ((and (zerop1 q) (mgrp 0 a)) nil) ;x^a = 0, where a < 0
			 ((and ($ratnump kmin) ($ratnump kmax))
			  (setq xxx (take '(mexpt) q (div 1 a)))
			  (while (mgrp kmax kmin)
					 (push (mul xxx (take '(mexpt) '$%e (div (mul 2 '$%pi '$%i kmax) a))) sol)
					 (decf kmax))
			  sol)

			 (t
				 ;;(mtell "doing plain power")
			  ;;; problem: solve(abs(x^2-1) = ha ,x)
			  (list (take '(mexpt) q (div 1 a)))))))

(mapcar #'(lambda (x) (setf (gethash (first x) *function-inverses*) (second x)))
		(list

		 ; a^X=q --> if q=0 then empty else
		 (list 'exponential-inverse #'(lambda (q a)
											  (cond ((zerop1 q) nil)
												  	(t (list (div (add (take '(%log) q) (mul 2 '$%pi '$%i
																						(my-new-variable '$integer)))
																  (take '(%log) a)))))))

		  ; x^a=q --> x=q^(1/a)
		  (list 'power-inverse #'power-inverse-standard)

		 ; x^x = q -->
		 (list 'lambert-like-inverse #'(lambda (q)
											   (cond
												   ((zerop1 q) nil)
												   (t
													(list (take '(mexpt) '$%e (take '(%lambert_w)
															(add (take '(%log) q)
																		(mul 2 '$%pi '$%i (my-new-variable '$integer))))))))))

		  (list '%sin #'(lambda (q)
								(cond ((zerop1 q)
										(list (mul '$%pi (my-new-variable '$integer))))
									   ((onep1 q)
										(list (add (div '$%pi 2) (mul 2 '$%pi (my-new-variable '$integer)))))
									   (t
										(list
										 (add (mul 2 '$%pi (my-new-variable '$integer)) (take '(%asin) q))
										 (add (mul 2 '$%pi (my-new-variable '$integer)) (sub '$%pi (take '(%asin) q))))))))

		 (list '%csc #'(lambda (q)
		           (cond ((zerop1 q) nil)
								     ((onep1 q)
										  (list (div (add (mul 4 '$%pi (my-new-variable '$integer)) '$%pi) 2)))
										(t
								     (list
							   	 	   (add (mul 2 '$%pi (my-new-variable '$integer)) (take '(%acsc) q))
							       	 (add (mul 2 '$%pi (my-new-variable '$integer)) (sub '$%pi (take '(%acsc) q))))))))

		  (list '%cos #'(lambda (q)
								(if (eql q 1) (list (mul 2 '$%pi (my-new-variable '$integer)))
								(list
								 (add (mul 2 '$%pi (my-new-variable '$integer)) (take '(%acos) q))
								 (sub (mul 2 '$%pi (my-new-variable '$integer)) (take '(%acos) q))))))

		 (list '%sec #'(lambda (q)
							   (if (eql q 0) (list)
								(list
								 (add (mul 2 '$%pi (my-new-variable '$integer)) (take '(%asec) q))
								 (sub (mul 2 '$%pi (my-new-variable '$integer)) (take '(%asec) q))))))

		 (list '%tan #'(lambda (q)
								 (cond  ((zerop1 (add 1 (mul q q))) (list))
								         (t (list (add (mul '$%pi (my-new-variable '$integer)) (take '(%atan) q)))))))

		 (list '%cot #'(lambda (q)
							   (cond
								   ((zerop1 (add 1 (mul q q))) (list))
								   (t
									(list (add (mul '$%pi (my-new-variable '$integer)) (take '(%acot) q)))))))

		 (list '%asin #'(lambda (q)
   	 	  (let ((cnd))
					;; could require -pi/2 <= Re(q) <= pi/2 or Re(q)=-pi/2 & Im(q) >=  0
					;; or Re(q) = pi/2 & Im(q) <= 0, but we can't assume or expressions. Plus
					;; this is much easier. The option variable triginverses controls the
					;; sin(asin(x)) simplification.
					(setq cnd (my-ask-boolean (take '($equal) q (take '(%sin) (take '(%asin) q)))))
					(if cnd (list (take '(%sin) q)) nil))))

		 (list '%acos #'(lambda (q) (let ((cnd))
				 ;;could require 0 < Re(q) < pi or Re(q)=0 & Im(q) >= 0 or Re(q)=pi & Im(q) <= 0
				 (setq cnd (my-ask-boolean (take '($equal) q (take '(%cos) (take '(%acos) q)))))
 				 (if cnd (list (take '(%cos) q)) nil))))

		 (list '%acot #'(lambda (q)
								(cond ((zerop1 q) (list))
									(t (list (take '(%cot) q))))))

		(list '%atan #'(lambda (q)
        (let ((qr (my-real q)) (qi (my-imag q)) (cnd))
				     ;;require -pi/2 < Re(q) <= pi/2 or Re(q)=-pi/2 & Im(q) <  0 or Re(q)=pi/2 & Im(q) > 0
					   (setq cnd
							  (my-ask-boolean
									(take '(mor)
							   	 	  (take '(mand)
						     	       (mm< (div '$%pi -2) qr)
						   	         (mm<= qr (div '$%pi 2)))
											(take '(mand)
													(mm= qr (div '$%pi -2))
													(mm< qi 0))
											(take '(mand)
													(mm= qr (div '$%pi 2))
													(mm< qi 0)))))

						(cond ((eql cnd t)
						       	(list (take '(%tan) q)))
								  (t
										nil)))))

		 (list '%sinh #'(lambda (q) (list
									 (add (mul 2 '$%pi '$%i (my-new-variable '$integer)) (take '(%asinh) q))
									 (add (mul 2 '$%pi '$%i (my-new-variable '$integer)) (mul '$%pi '$%i)
										  (mul -1 (take '(%asinh) q))))))

		 (list '%cosh #'(lambda (q) (list
									 (add (mul 2 '$%pi '$%i (my-new-variable '$integer)) (take '(%acosh) q))
		 							 (sub (mul 2 '$%pi '$%i (my-new-variable '$integer)) (take '(%acosh) q)))))

		 (list '%sech #'(lambda (q)
								(if (zerop1 q)
									(list)
									(list
									 (add (mul 2 '$%pi '$%i (my-new-variable '$integer)) (take '(%acosh) (div 1 q)))
									 (sub (mul 2 '$%pi '$%i (my-new-variable '$integer)) (take '(%acosh) (div 1 q)))))))

		 (list '%csch #'(lambda (q) (list
									 (add (mul 2 '$%pi '$%i (my-new-variable '$integer)) (take '(%acsch) (div 1 q)))
									 (sub (mul '$%pi '$%i (add 1 (mul 2 (my-new-variable '$integer)))) (take '(%acsch) (div 1 q))))))

		 (list '%tanh #'(lambda (q)
								(if (or (onep q) (onep (mul -1 q))) (list)
									(list (add (mul '$%pi '$%i (my-new-variable '$integer)) (take '(%atanh) q))))))


		 (list '%coth #'(lambda (q)
								(if (or (onep q) (onep (mul -1 q))) (list)
								(list (add (mul '$%pi '$%i (my-new-variable '$integer)) (take '(%acoth) q))))))

		 (list '$conjugate #'(lambda (q) (list (take '($conjugate) q))))

		 (list '%signum #'(lambda (q)
		      (let ((qmag (sratsimp (mul q (take '($conjugate) q)))))
					(cond ((my-ask-boolean (mm= qmag 1))
					       (list (mul (take '(mexpt) '$%e (my-new-variable '$real)) q)))
							((my-ask-boolean (mm= qmag 0))
							   (list 0))
						  (t
								 nil)))))

     (list '$unit_step #'(lambda (q)
					   (cond ((my-ask-boolean (mm= q 0)) ;; unit_step(X) = 0 --> X = 0 or X < 0
								        (list 0 (mul -1 (take '(mexpt) '$%e (my-new-variable '$real)))))
										((my-ask-boolean (mm= q 1)) ;; unit_step(X) = 1 --> X > 1
						 	 	        (list (take '(mexpt) '$%e (my-new-variable '$real))))
							      (t nil)))) ;;otherwise no solution

		 ;; not sure about all these....
		 (list '%asinh #'(lambda (q) (list (take '(%sinh) q))))
		 (list '%acosh #'(lambda (q) (list (take '(%cosh) q))))
		 (list '%atanh #'(lambda (q) (list (take '(%tanh) q))))

		 (list '%acsch #'(lambda (q) (list (take '(%csch) q))))
		 (list '%asech #'(lambda (q) (list (take '(%sech) q))))
		 (list '%acoth #'(lambda (q) (list (take '(%coth) q))))

		 ;; Require -pi < Im(q) <= pi.
		 (list '%log  #'(lambda (q)
           (let ((qi (my-imag q)) (cnd))
						  (setq cnd
								(my-ask-boolean
					   	  		(take '(mand) ;;require -pi < Im(q) <= pi.
								       (mm< (mul -1 '$%pi) qi)
								       (mm<= qi '$%pi))))
			(if cnd (list (take '(mexpt) '$%e q)) nil))))

		 (list '%plog  #'(lambda (q)
			 (let ((qi (my-imag q)) (cnd))
				 (setq cnd
					 (my-ask-boolean
							 (take '(mand) ;;require -pi < Im(q) <= pi.
									(mm< (mul -1 '$%pi) qi)
									(mm<= qi '$%pi))))
				(if cnd (list (take '(mexpt) '$%e q)) nil))))))

(defvar *function-inverses-alt* (make-hash-table))

(mapcar #'(lambda (x) (setf (gethash (first x) *function-inverses-alt*) (second x)))
		(list

		 	 ; exp(X)=q --> if q=0 then empty else
		  (list 'exponential-inverse #'(lambda (q a)
											  (cond ((zerop1 q) nil)
												  	(t (list (div (take '(%log) q) (take '(%log) a)))))))

		  ; x^a=q --> x=q^(1/a)
		  (list 'power-inverse #'power-inverse-standard)
		;  (list 'power-inverse #'(lambda (q a)
		;								 (cond ((and (zerop1 q) (mgrp a 0)) ;x^a = 0, where a >0
		;										(list 0))
		;									   ((and (zerop1 q) (mgrp 0 a)) ;x^a = 0, where a < 0
		;										nil)
		;									   (t
		;									    (list (take '(mexpt) q (div 1 a)))))))


		 (list 'lambert-like-inverse #'(lambda (q a)
											   (declare (ignore a))
											   (cond
												   ((zerop1 q) nil)
												   (t
													(list (take '(mexpt) '$%e (take '(%lambert_w)
															(add (take '(%log) q)
																		(mul 2 '$%pi '$%i (my-new-variable '$integer))))))))))


		  (list '%sin #'(lambda (q) (list (take '(%asin) q))))
		  (list '%cos #'(lambda (q) (list (take '(%acos) q))))

			(list '%tan #'(lambda (q)
									(cond
										((zerop1 (add 1 (mul q q))) (list)) ; +/- %i not in range of tan
										(t (list (take '(%atan) q))))))

	    (list '%csc #'(lambda (q) (if (zerop1 q) (list) (list (take '(%acsc) q)))))
		  (list '%sec #'(lambda (q) (if (zerop1 q) (list) (list (take '(%asec) q)))))
		  (list '%cot #'(lambda (q) (if (zerop1 q) (list ) (list (take '(%acot) q)))))

		  (list '%asin #'(lambda (q) (list (take '(%sin) q))))
		  (list '%acos #'(lambda (q) (list (take '(%cos) q))))
			;; Maybe this should check if the -pi/2 < Re(q) <= pi/2
		  (list '%atan #'(lambda (q) (list (take '(%tan) q))))
		  (list '%acot #'(lambda (q)
								(cond ((zerop1 q) (list))
									(t (list (take '(%cot) q))))))

	    (list '%acsc #'(lambda (q) (list (take '(%csc) q))))
		  (list '%asec #'(lambda (q) (list (take '(%sec) q))))
		  ;(list '%acot #'(lambda (q) (list (take '(%cot) q))))

    	  (list '%sinh #'(lambda (q) (list (take '(%asinh) q))))
    	  (list '%cosh #'(lambda (q) (list (take '(%acosh) q))))
 		    (list '%tanh #'(lambda (q) (list (take '(%atanh) q))))

	 	    (list '%csch #'(lambda (q) (list (take '(%acsch) q))))
    	  (list '%sech #'(lambda (q) (list (take '(%asech) q))))
 		    (list '%coth #'(lambda (q) (list (take '(%acoth) q))))

		  ;; not sure about all these....
 	      (list '%asinh #'(lambda (q) (list (take '(%sinh) q))))
    	  (list '%acosh #'(lambda (q) (list (take '(%cosh) q))))
 		    (list '%atanh #'(lambda (q) (list (take '(%tanh) q))))

	 	  (list '%acsch #'(lambda (q) (list (take '(%csch) q))))
    	(list '%asech #'(lambda (q) (list (take '(%sech) q))))
 		  (list '%acoth #'(lambda (q) (list (take '(%coth) q))))

		  (list '%log  #'(lambda (q) (list (take '(mexpt) '$%e q))))
		  (list '%plog  #'(lambda (q) (list (take '(mexpt) '$%e q))))))

(defun mabs-inverse (x)
		(let ((sgn (my-ask-boolean (take '(mgreaterp) x 0))))
					(cond (sgn (list x (mul -1 x)))
								(t
									(setq sgn (my-ask-boolean (take '($equal) 0 x)))
									 (if sgn (list 0) nil)))))

(setf (gethash 'mabs *function-inverses*) #'mabs-inverse)
(setf (gethash 'mabs *function-inverses-alt*) #'mabs-inverse)

(setf (get '$solve_standard 'assign) 'neverset)
(setf (get '$solve_alt 'assign) 'neverset)

(defun solve-inverse-assign (a b)
	;;(print (list a b))
	(when (not (hash-table-p b))
        (merror "The value of ~M must be a hash table' ~%" a)))

(defmvar $multivalued_inverse *function-inverses*)
(defmvar $single_valued_inverse *function-inverses-alt*)

(defmvar $solve_inverse_package *function-inverses*)
(setf (get '$solve_inverse_package 'assign) #'solve-inverse-assign)
