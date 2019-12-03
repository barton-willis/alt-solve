;; Author: Barton Willis
;; 2020
;; Common Lisp/Maxima code for symbolic solutions of equations and systems of equations.

;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.

(in-package :maxima)

(defvar *function-inverses* (make-hash-table))

(defun power-inverse-standard (q a)
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
			  ;;; problem: solve(abs(x^2-1) = ha ,x)
			  (list (take '(mexpt) q (div 1 a)))))))

(mapcar #'(lambda (x) (setf (gethash (first x) *function-inverses*) (second x)))
		(list
		 ; a^X=q --> if q=0 then empty else
		 (list 'exponential-inverse #'(lambda (q a)
											  (cond ((zerop1 q) nil)
												  	(t (list (div (add (take '(%log) q) (mul 2 '$%pi '$%i
																						($new_variable '$integer)))
																  (take '(%log) a)))))))

		  ; x^a=q --> x=q^(1/a)
		  (list 'power-inverse #'power-inverse-standard)

		 ; x^x = q -->
		 (list 'lambert-like-inverse #'(lambda (q a)
											   (declare (ignore a))
											   (cond
												   ((zerop1 q) nil)
												   (t
													(list (take '(mexpt) '$%e (take '(%lambert_w)
															(add (take '(%log) q)
																		(mul 2 '$%pi '$%i ($new_variable '$integer))))))))))




		  (list '%sin #'(lambda (q)
								(cond ((zerop1 q)
										(list (mul '$%pi ($new_variable '$integer))))
									   ((onep1 q)
										(list (add (div '$%pi 2) (mul 2 '$%pi ($new_variable '$integer)))))
									   (t
										(list
										 (add (mul 2 '$%pi ($new_variable '$integer)) (take '(%asin) q))
										 (add (mul 2 '$%pi ($new_variable '$integer)) (sub '$%pi (take '(%asin) q))))))))

		 (list '%csc #'(lambda (q)
							   (if (zerop1 q)
								   (list)
								   (list
									(add (mul 2 '$%pi ($new_variable '$integer)) (take '(%acsc) q))
									(add (mul 2 '$%pi ($new_variable '$integer)) (sub '$%pi (take '(%acsc) q)))))))

		  (list '%cos #'(lambda (q)
								(if (eql q 1) (list (mul 2 '$%pi ($new_variable '$integer)))
								(list
								 (add (mul 2 '$%pi ($new_variable '$integer)) (take '(%acos) q))
								 (sub (mul 2 '$%pi ($new_variable '$integer)) (take '(%acos) q))))))

		 (list '%sec #'(lambda (q)
							   (if (eql q 0) (list)
								(list
								 (add (mul 2 '$%pi ($new_variable '$integer)) (take '(%asec) q))
								 (sub (mul 2 '$%pi ($new_variable '$integer)) (take '(%asec) q))))))

		 (list '%tan #'(lambda (q)
							   (cond
								   ((zerop1 (add 1 (mul q q))) (list))
								   (t (list (add (mul '$%pi ($new_variable '$integer)) (take '(%atan) q)))))))

		 (list '%cot #'(lambda (q)
							   (cond
								   ((zerop1 (add 1 (mul q q))) (list))
								   (t
									(list (add (mul '$%pi ($new_variable '$integer)) (take '(%acot) q)))))))

		 ;; This is OK if asin is multivalued, I guess. Otherwise, it needs to be conditionalized in
		 ;; a fairly crabbed way--would need -pi/2 < Re(q) < pi/2 or Re(q)=-pi/2 and Im(q) >= 0 or
		 ;; Re(q) = pi/2 and Im(q) < 0. Much the same applies for the other inverse functions.

		 (list '%asin #'(lambda (q) (list (take '(%sin) q))))

		 (list '%acos #'(lambda (q) (list (take '(%cos) q))))

		 (list '%acot #'(lambda (q)
								(cond ((zerop1 q) (list))
									(t (list (take '(%cot) q))))))


		 (list '%sinh #'(lambda (q) (list
									 (add (mul 2 '$%pi '$%i ($new_variable '$integer)) (take '(%asinh) q))
									 (add (mul 2 '$%pi '$%i ($new_variable '$integer)) (mul '$%pi '$%i)
										  (mul -1 (take '(%asinh) q))))))

		 (list '%cosh #'(lambda (q) (list
									 (add (mul 2 '$%pi '$%i ($new_variable '$integer)) (take '(%acosh) q))
		 							 (sub (mul 2 '$%pi '$%i ($new_variable '$integer)) (take '(%acosh) q)))))

		 (list '%sech #'(lambda (q)
								(if (zerop1 q)
									(list)
									(list
									 (add (mul 2 '$%pi '$%i ($new_variable '$integer)) (take '(%acosh) (div 1 q)))
									 (sub (mul 2 '$%pi '$%i ($new_variable '$integer)) (take '(%acosh) (div 1 q)))))))


		 (list '%csch #'(lambda (q) (list
									 (add (mul 2 '$%pi '$%i ($new_variable '$integer)) (take '(%acsch) (div 1 q)))
									 (sub (mul '$%pi '$%i (add 1 (mul 2 ($new_variable '$integer)))) (take '(%acsch) (div 1 q))))))

		 (list '%tanh #'(lambda (q)
								(if (or (onep q) (onep (mul -1 q))) (list)
									(list (add (mul '$%pi '$%i ($new_variable '$integer)) (take '(%atanh) q))))))


		 (list '%coth #'(lambda (q)
								(if (or (onep q) (onep (mul -1 q))) (list)
								(list (add (mul '$%pi '$%i ($new_variable '$integer)) (take '(%acoth) q))))))

		 (list '$conjugate #'(lambda (q) (list (take '($conjugate) q))))

		 ;; not sure about all these....
		 (list '%asinh #'(lambda (q) (list (take '(%sinh) q))))
		 (list '%acosh #'(lambda (q) (list (take '(%cosh) q))))
		 (list '%atanh #'(lambda (q) (list (take '(%tanh) q))))

		 (list '%acsch #'(lambda (q) (list (take '(%csch) q))))
		 (list '%asech #'(lambda (q) (list (take '(%sech) q))))
		 (list '%acoth #'(lambda (q) (list (take '(%coth) q))))

		 ;; could be super strict and require -pi < q <= pi.
		 (list '%log  #'(lambda (q) (list (take '(mexpt) '$%e q))))
		 (list '%plog  #'(lambda (q) (list (take '(mexpt) '$%e q))))))

(defvar *function-inverses-alt* (make-hash-table))

(mapcar #'(lambda (x) (setf (gethash (first x) *function-inverses-alt*) (second x)))
		(list

		 	 ; exp(X)=q --> if q=0 then empty else
		  (list 'exponential-inverse #'(lambda (q a)
											   ;;;(print `(q = ,q a = ,a))
											  (cond ((zerop1 q) nil)
												  	(t (list (div (take '(%log) q) (take '(%log) a)))))))

		  ; x^a=q --> x=q^(1/a)
		  (list 'power-inverse #'power-inverse-standard)
		;  (list 'power-inverse #'(lambda (q a)
		;								 (print "TJB")
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
																		(mul 2 '$%pi '$%i ($new_variable '$integer))))))))))


		  (list '%sin #'(lambda (q) (list (take '(%asin) q))))
		  (list '%cos #'(lambda (q) (list (take '(%acos) q))))
		  (list '%tan #'(lambda (q) (list (take '(%atan) q))))

	      (list '%csc #'(lambda (q) (if (zerop1 q) (list) (list (take '(%acsc) q)))))
		  (list '%sec #'(lambda (q) (if (zerop1 q) (list) (list (take '(%asec) q)))))
		  (list '%cot #'(lambda (q) (if (zerop1 q) (list ) (list (take '(%acot) q)))))

		  (list '%asin #'(lambda (q) (list (take '(%sin) q))))
		  (list '%acos #'(lambda (q) (list (take '(%cos) q))))
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
	(let ((sgn ($asksign x)))
		 (cond ((or (eq sgn '$pos) (eq sgn '$pz))
				(list x (mul -1 x)))
			   ((eq sgn '$zero)
				(list 0))
			   (t nil))))

(setf (gethash 'mabs *function-inverses*) #'mabs-inverse)
(setf (gethash 'mabs *function-inverses-alt*) #'mabs-inverse)

(setf (get '$solve_standard 'assign) 'neverset)
(setf (get '$solve_alt 'assign) 'neverset)

(defun solve-inverse-assign (a b)
	(print (list a b))
	(when (not (hash-table-p b))
        (merror "The value of ~M must be a hash table' ~%" a)))

(defmvar $multivalued_inverse *function-inverses*)
(defmvar $single_valued_inverse *function-inverses-alt*)

(defmvar $solve_inverse_package *function-inverses-alt*)
(setf (get '$solve_inverse_package 'assign) #'solve-inverse-assign)
