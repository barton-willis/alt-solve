;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for determining the function domain.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

(defvar *in-domain* (make-hash-table))

(defun unlike (a b)
	(not (alike1 a b)))

(defun not-zerop (a)
   (take '(mnotequal) a 0))

(mapcar #'(lambda (x) (setf (gethash (first x) *in-domain*) (second x)))
		(list

		  ;; atan2(0,0) is undefined.
		  (list '$atan2 #'(lambda (p q) (take '(mand) (not-zerop p)
											  		  (not-zerop q)
											          (in-domain p)
											          (in-domain q))))

		 (list '%tan #'(lambda (q) (take '(mand) (not-zerop (take '(%cos) q)) (in-domain q))))

		 (list '%cot #'(lambda (q) (take '(mand) (not-zerop (take '(%sin) q)) (in-domain q))))

		 (list '%csc #'(lambda (q) (take '(mand) (not-zerop (take '(%sin) q)) (in-domain q))))

		 (list '%sec #'(lambda (q) (take '(mand) (not-zerop (take '(%cos) q)) (in-domain q))))


		 (list '%atan #'(lambda (q) (take '(mand)
										   (unlike q '$%i)
										   (unlike q (mul -1 '$%i))
										   (in-domain q))))


		 (list '%acot #'(lambda (q) (take '(mand)
										   (unlike q '$%i)
										   (unlike q (mul -1 '$%i))
										   (in-domain q))))

		  (list '%log #'(lambda (q) (take '(mand) (not-zerop q) (in-domain q))))

		  (list '%plog #'(lambda (q) (take '(mand)  (not-zerop q)  (in-domain q))))

		  (list 'mexpt #'(lambda (a b)
				             (cond ((and (integerp b) (> b 0))
										         (in-domain a))
													 (t
														 (take '(mand)
										        	 (in-domain a)
										        	 (in-domain b)
									        		 (take '(mor) (not-zerop a) (take '(mgreaterp) b 0)))))))))


(defun $indomain(e x)
	(in-domain e (cdr x)))

(defun in-domain (e &optional (x nil))
    (let ((fn (and (consp e) (consp (car e)) (gethash (caar e) *in-domain*))))
    	(standardize-inequality
      	 (cond
	      	 (($mapatom e) t)
			  	 ((every #'(lambda (q) (not (among q e))) x) t)
					 (fn (apply fn (cdr e)))
	   	     (t ;;assume operator is defined everywhere--return the conjunction of map in-domain onto argument list.
			       (simplifya (cons '(mand) (mapcar #'(lambda (q) (in-domain q x)) (cdr e))) t))))))
