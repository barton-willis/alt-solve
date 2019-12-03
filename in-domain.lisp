;; Author: Barton Willis
;; Common Lisp/Maxima code for determining the function domain.

;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.

(in-package :maxima)

(defvar *in-domain* (make-hash-table))
	 
(defun unlike (a b) 
	(not (alike1 a b)))

(defun not-zerop (a) 
	(take '(mnotequal) a 0))
	;(not (zerop1 a)))

(mapcar #'(lambda (x) (setf (gethash (first x) *in-domain*) (second x)))
		(list
		 
		  ;; atan2(0,0) is undefined.
		  (list '$atan2 #'(lambda (p q) (take '(%and) (not-zerop p)
											  		  (not-zerop q)
											          (in-domain p)
											          (in-domain q))))
		 
		 (list '%tan #'(lambda (q) (take '(%and) (not-zerop (take '(%cos) q)) (in-domain q))))
		 
		 (list '%cot #'(lambda (q) (take '(%and) (not-zerop (take '(%sin) q)) (in-domain q))))
		 
		 (list '%csc #'(lambda (q) (take '(%and) (not-zerop (take '(%sin) q)) (in-domain q))))
		 
		 (list '%sec #'(lambda (q) (take '(%and) (not-zerop (take '(%cos) q)) (in-domain q))))
		 
		 
		 (list '%atan #'(lambda (q) (take '(%and) 
										   (unlike q '$%i) 
										   (unlike q (mul -1 '$%i))
										   (in-domain q))))
		 
		 
		 (list '%acot #'(lambda (q) (take '(%and) 
										   (unlike q '$%i) 
										   (unlike q (mul -1 '$%i))
										   (in-domain q))))
		
		  (list '%log #'(lambda (q) (take '(%and) (not-zerop q) (in-domain q))))
		 
		  (list '%plog #'(lambda (q) (take '(%and)  (not-zerop q)  (in-domain q))))
		 
		  (list 'mexpt #'(lambda (a b) (take '(%and)
											 (in-domain a) 
											 (in-domain b) 
											 (take '(%or) (not-zerop a) (take '(mgreaterp) b 0)))))))
		

(defun $indomain(e)
	(in-domain e))

(defun in-domain (e)
	(let ((fn (and (consp e) (consp (car e)) (gethash (caar e) *in-domain*))))
		 
		 (cond 
			 (($mapatom e) t)
			 (fn (apply fn (cdr e)))
			 (t ;;assume operator is defined everywhere--return the conjunction of map in-domain onto argument list.
			  (simplifya (cons '(%and) (mapcar #'in-domain (cdr e))) t)))))
		   