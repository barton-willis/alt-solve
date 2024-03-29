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
		  (list '%sec #'(lambda (q) (take '(mequal) (sub (power (take '(%sec) q) 2) (power (take '(%tan) q) 2)) 1)))
		  (list '%csc #'(lambda (q) (take '(mequal) (sub (power (take '(%csc) q) 2) (power (take '(%cot) q) 2)) 1)))

		  (list '%cosh #'(lambda (q) (take '(mequal) (sub (power (take '(%cosh) q) 2) (power (take '(%sinh) q) 2)) 1)))
		  (list '%sech #'(lambda (q) (take '(mequal) (add (power (take '(%tanh) q) 2) (power (take '(%sech) q) 2)) 1)))
		  (list '%csch #'(lambda (q) (take '(mequal) (sub (power (take '(%coth) q) 2) (power (take '(%csch) q) 2)) 1)))))

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


(maphash #'(lambda (key val) (declare (ignore val)) (remhash key *trig-power-reduce*)) *trig-power-reduce*)
(mapcar #'(lambda (x) (setf (gethash (first x) *trig-power-reduce*) (second x)))
  (list
   ;; sin(x)^2=(1-cos(2*x))/2
   (list '%sin #'(lambda (q)
		 (take '(mequal) (power (take '(%sin) q) 2) (div (sub 1 (take '(%cos) (mul 2 q))) 2))))
	 ;; cos(x)^2=(cos(2*x)+1)/2
	 (list '%cos #'(lambda (q)
		 (take '(mequal) (power (take '(%cos) q) 2) (div (add 1 (take '(%cos) (mul 2 q))) 2))))
	 ;; sinh(x)^2=(cosh(2*x)-1)/2
	 (list '%sinh #'(lambda (q)
		 (take '(mequal) (power (take '(%sinh) q) 2) (div (sub (take '(%cosh) (mul 2 q)) 1) 2))))
	 ;; cosh(x)^2=(cosh(2*x)+1)/2
	 (list '%cosh #'(lambda (q)
		 (take '(mequal) (power (take '(%cosh) q) 2) (div (add (take '(%cosh) (mul 2 q)) 1) 2))))))

;; Apply the identities described by the hashtable id-table to the expression e. Make the
;; substitution even when the result has a larger expression size.
(defun apply-identities-unconditionally (e &optional (id-table *pythagorean-identities*))
	(setq e ($ratdisrep e))
	(maphash #'(lambda (key val)
					   (let ((q (cdr ($setify ($gatherargs e key)))) (id))
							(dolist (z q)
								(setq id (apply val (cdr z)))
								(setq e ($ratsubst ($rhs id) ($lhs id) e))))) id-table)
	e)

;; A metric for the expression size. When equation-simplify uses
;; apply-identities-conditionally, changing this metric, for example, using max instead
;; of plus, can result in changes to the testsuite--some good, some less good. But when
;; we use apply-identities-unconditionally, the testsuite results don't matter so
;; much with variations in this function.
(defun trigfun-p (e)
   (and (consp e) (consp (car e))
	   (memq (caar e) (list '%cos '%sin '%tan '%sec '%csc '%cot
                          '%cosh '%sinh '%tanh '%sech '%csch '%coth))))

	(defun trig-fun-count (e)
	  (cond (($mapatom e) 0)
		      ((trigfun-p e) (+ 1 (trig-fun-count (cadr e))))
					(t (reduce #'+ (mapcar #'trig-fun-count (cdr e))))))



;; When ratsubst(new, old, e) has a smaller expression size than does e, do the
;; substitution; otherwise don't do the substitution.
(defun conditional-ratsubst (new old e)
	(let ((ee ($ratsubst new old e)))
	    	(if (< (trig-fun-count ee) (trig-fun-count e)) ee e)))

;; Apply the identities described by the hashtable id-table to the expression e. Make the
;; substitution only when the result has a smaller expression size as determined by
;; trig-fun-count.
(defun apply-identities-conditionally (e &optional (id-table *pythagorean-identities*))
	(setq e ($ratdisrep e))
	(maphash #'(lambda (key val)
					   (let ((q (cdr ($setify ($gatherargs e key)))) (id))
							(dolist (z q)
								(setq id (apply val (cdr z)))
								(setq e (conditional-ratsubst ($rhs id) ($lhs id) e))))) id-table)
	e)
