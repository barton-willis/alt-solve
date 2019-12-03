;; Author: Barton Willis
;; Common Lisp/Maxima code for symbolic solutions of equations.

;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.

(in-package :maxima)


(eval-when (:compile-toplevel :load-toplevel :execute)
	($load "opsubst")
	(defvar *pythagorean-identities* (make-hash-table))
	(defvar *pythagorean-identities-extra* (make-hash-table))
    (defvar *double-angle-identities* (make-hash-table))
	(defvar *to-cos/sin-identities* (make-hash-table))
	(defvar *trig-power-reduce* (make-hash-table))

	(maphash #'(lambda (key val) (declare (ignore val)) (remhash key *pythagorean-identities*)) *pythagorean-identities*)
	
	(mapcar #'(lambda (x) (setf (gethash (first x) *pythagorean-identities*) (second x)))
		(list
		  (list '%cos #'(lambda (q) (take '(mequal) (add (power (take '(%cos) q) 2) (power (take '(%sin) q) 2)) 1)))
		  (list '%tan #'(lambda (q) (take '(mequal) (sub (power (take '(%tan) q) 2) (power (take '(%sec) q) 2)) 1)))
		  (list '%cot #'(lambda (q) (take '(mequal) (sub (power (take '(%cot) q) 2) (power (take '(%csc) q) 2)) 1)))
		 
		  (list '%cosh #'(lambda (q) (take '(mequal) (sub (power (take '(%cosh) q) 2) (power (take '(%sinh) q) 2)) 1)))
		  (list '%tanh #'(lambda (q) (take '(mequal) (add (power (take '(%tanh) q) 2) (power (take '(%sech) q) 2)) 1)))
		  (list '%coth #'(lambda (q) (take '(mequal) (add (power (take '(%coth) q) 2) (power (take '(%csch) q) 2)) 1)))))
	
	(maphash #'(lambda (key val) (declare (ignore val)) 
					   (remhash key *pythagorean-identities-extra*)) *pythagorean-identities-extra*)
	(mapcar #'(lambda (x) (setf (gethash (first x) *pythagorean-identities-extra*) (second x)))
		(list 
		 (list '%sin #'(lambda (q) (take '(mequal) (power (take '(%sin) q) 2) (sub 1 (power (take '(%cos) q) 2)))))
		 (list '%sinh #'(lambda (q) (take '(mequal) (power (take '(%sinh) q) 2) (sub (power (take '(%cosh) q) 2) 1))))))
	
	(maphash #'(lambda (key val) (declare (ignore val)) (remhash key *double-angle-identities*)) *double-angle-identities*)
	(mapcar #'(lambda (x) (setf (gethash (first x) *double-angle-identities*) (second x)))
		(list
		  (list '%cos #'(lambda (q) (take '(mequal) 
										  (mul (take '(%cos) q) (take '(%sin) q)) (div (take '(%sin) (mul 2 q)) 2))))))
	
	(maphash #'(lambda (key val) (declare (ignore val)) (remhash key *to-cos/sin-identities*)) *to-cos/sin-identities*)
	(mapcar #'(lambda (x) (setf (gethash (first x) *to-cos/sin-identities*) (second x)))
			(list 
			 (list '%tan #'(lambda (q) (take '(mequal) (take '(%tan) q) (div (take '(%sin) q) (take '(%cos) q)))))
			 (list '%sec #'(lambda (q) (take '(mequal) (take '(%sec) q) (div 1 (take '(%cos) q)))))
			 (list '%csc #'(lambda (q) (take '(mequal) (take '(%csc) q) (div 1 (take '(%sin) q)))))
			 (list '%cot #'(lambda (q) (take '(mequal) (take '(%cot) q) (div (take '(%cos) q) (take '(%sin) q)))))
			
			 (list '%tanh #'(lambda (q) (take '(mequal) (take '(%tanh) q) (div (take '(%sinh) q) (take '(%cosh) q)))))
			 (list '%sech #'(lambda (q) (take '(mequal) (take '(%sech) q) (div 1 (take '(%cosh) q)))))
			 (list '%csch #'(lambda (q) (take '(mequal) (take '(%csch) q) (div 1 (take '(%sinh) q)))))
			 (list '%coth #'(lambda (q) (take '(mequal) (take '(%csch) q) (div (take '(%cosh) q) (take '(%sinh) q))))))))


(defun apply-identities-xxx (e &optional (id-table *pythagorean-identities*))
	(setq e ($ratdisrep e))
	(maphash #'(lambda (key val) 
					   (let ((q (cdr ($setify ($gatherargs e key)))) (id))
							(dolist (z q)
								(setq id (apply val (cdr z)))
								(setq e ($ratsubst ($rhs id) ($lhs id) e))))) id-table) ;was ratsubst....
	e)
				

(defun my-size (e)
	(cond ((or (mtimesp e) (mplusp e))
		   (reduce #'+ (mapcar #'my-size (cdr e))))
		  ((mexptp e)
		   (my-size (cadr e)))
		  (t 1)))

(defun conditional-ratsubst (new old e)
	(let ((ee ($ratsubst old new e)))
	    	(if (< (my-size ee) (my-size e)) ee e)))

(defun apply-identities (e id-table)
	(maphash #'(lambda (key val) 
					   (let ((q (cdr ($setify ($gatherargs e key)))) (id))
							(dolist (z q)
								(setq id (apply val (cdr z)))
								(setq e (conditional-ratsubst ($lhs id) ($rhs id) e))))) id-table)
	e)	

