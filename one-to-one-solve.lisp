;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

#|
(one_to_one_reduce[a,b] := false,
  one_to_one_reduce['sin,'sin] : lambda([a,b],
      (a - b - 2 * %pi * new_variable('integer)) * (a + b - 2 * %pi * new_variable('integer) + %pi)),

  one_to_one_reduce['cos,'cos] : lambda([a,b],
      (a - b - 2 * %pi * new_variable('integer)) * (a + b - 2 * %pi * new_variable('integer))),

  one_to_one_reduce['sin,'cos] : lambda([a,b],
    (a/2 - b/2 - %pi/4 - %pi * new_variable('integer))*(a/2 + b/2 - %pi/4 - %pi * new_variable('integer))),

  one_to_one_reduce['cos,'sin] :  lambda([a,b],
    (b/2 - a/2 - %pi * new_variable('integer) - %pi/4)*(b/2 + a/2 - %pi * new_variable('integer) - %pi/4)),

  one_to_one_reduce['tan,'tan] : lambda([a,b], (a-b - %pi*new_variable('integer))/(cos(a)*cos(b))),

  one_to_one_reduce['%exp,'%exp] : lambda([a,b],
      a - b - 2 * %pi * %i * new_variable('integer)));

|#
(in-package :maxima)

(defvar *one-to-one-reduce* (make-hash-table :test #'equal))

;; attempt to solve equation c0*sin(kn0) + c1*sin(kn1) + b = 0 for x
(defun sin-sin-solve (x c0 kn0 c1 kn1 b)
   (let ((sol0) (sol1) (sol2))
      (cond ((and (zerop1 b) (alike1 c0 c1)) ;c0*sin(kn0) + c0*sin(kn1) = 0
				      (setq sol0 ($solve c0 x))
	            (setq sol1 ($solve (add kn0 kn1 (mul -2  '$%pi ($new_variable '$integer))) x))
			   		  (setq sol2 ($solve (add kn0 (mul -1 kn1) (mul -2  '$%pi (sub ($new_variable '$integer) (div 1 2)))) x))
			  	    ($append sol0 sol1 sol2)) ;;need to blend solutions + multiplicities!

				  	((and (zerop1 b) (alike1 c0 (mul -1 c1)))	 ;c0*sin(kn0) - c0*sin(kn1) = 0
							(setq sol0 ($solve c0 x))
							(setq sol1 ($solve (add kn0 kn1 (mul -2 '$%pi (sub ($new_variable '$integer) (div 1 2)))) x))
						  (setq sol2 ($solve (add kn0 (mul -1 kn1) (mul -2 '$%pi ($new_variable '$integer))) x))
						  ($append sol0 sol1 sol2)) ;;need to blend solutions + multiplicities!
				(t
					nil))))

(setf (gethash (list '%sin '%sin) *one-to-one-reduce*) #'sin-sin-solve)

;; attempt to solve equation c0*sin(kn0) + c1*sin(kn1) + b = 0 for x
(defun cos-cos-solve (x c0 kn0 c1 kn1 b)
   (let ((sol0) (sol1) (sol2))
      (cond ((and (zerop1 b) (alike1 c0 c1)) ;c0*cos(kn0) + c0*cos(kn1) = 0
				      (setq sol0 ($solve c0 x))
	            (setq sol1 ($solve (add kn0 kn1 (mul -2 '$%pi (sub ($new_variable '$integer) (div 1 2)))) x))
			   		  (setq sol2 ($solve (add kn0 (mul -1 kn1) (mul -2  '$%pi (sub ($new_variable '$integer) (div 1 2)))) x))
			  	    ($append sol0 sol1 sol2)) ;;need to blend solutions + multiplicities!

				  	((and (zerop1 b) (alike1 c0 (mul -1 c1)))	 ;c0*cos(kn0) - c0*cos(kn1) = 0
							(setq sol0 ($solve c0 x))
							(setq sol1 ($solve (add kn0 kn1 (mul -2 '$%pi ($new_variable '$integer))) x))
						  (setq sol2 ($solve (add kn0 (mul -1 kn1) (mul -2 '$%pi ($new_variable '$integer))) x))
						  ($append sol0 sol1 sol2)) ;;need to blend solutions + multiplicities!
				(t
					nil))))

(setf (gethash (list '%cos '%cos) *one-to-one-reduce*) #'cos-cos-solve)

;; attempt to solve equation c0*sin(kn0) + c1*sin(kn1) + b = 0 for x
(defun sin-cos-solve (x c0 kn0 c1 kn1 b)
   (let ((r) (ph))
      (cond ((and ($freeof x c0) ($freeof x c1) (alike1 kn0 kn1)) ;c0*cos(kn0) + c0*cos(kn1) = 0
              (setq r (take '(mexpt) (add (mul c0 c0) (mul c1 c1)) (div 1 2)))
              (setq ph (take '($atan2) c0 c1))
				      ($solve (add kn0 ph (mul -1 (take '(%asin) (div b r))) (mul '$%pi ($new_variable '$integer))) x))
				(t
					nil))))

(setf (gethash (list '%sin '%cos) *one-to-one-reduce*) #'sin-cos-solve)

(defun cos-sin-solve (x c0 kn0 c1 kn1 b)
    (sin-cos-solve x c1 kn1 c0 kn0 b))
(setf (gethash (list '%cos '%sin) *one-to-one-reduce*) #'cos-sin-solve)

;; attempt to solve c0*tan(kn0) + c1*tan(kn1) + b = 0 for x
(defun tan-tan-solve (x c0 kn0 c1 kn1 b)
    (cond ((and (alike1 c0 c1) (zerop1 b)) ;; c0*tan(kn0) + c1*tan(kn1) = 0
            ($append
               ($solve (add kn0 kn1 (mul '$%pi ($new_variable '$integer))) x)
               ($solve c0 x)))
          ((and (alike1 c0 (mul -1 c1)) (zerop1 b)) ;; c0*tan(kn0) - c1*tan(kn1) = 0
              ($append
                ($solve (add kn0 (mul -1 kn1) (mul '$%pi ($new_variable '$integer))) x)
                ($solve c0 x)))
              (t
                nil)))
(setf (gethash (list '%tan '%tan) *one-to-one-reduce*) #'tan-tan-solve)

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

(defun $one_to_one_solve (e x)
  (let ((ee) (subs nil) (gvars nil) (fn nil) (c0 nil) (c1 nil) (b nil))
     (flet ((is-a-kernel (e)
	           (and
						  	(consp e)
						  	(consp (car e))
						  	(member (caar e) (list '%sin '%cos '%tan '%log 'mexpt) :test #'eql))))
		     	  (setq ee (kernelize-fn e #'is-a-kernel))
		    		(setq subs (second ee))
						(setq gvars (mapcar #'cdr subs)) ;CL
						(setq subs (mapcar #'car subs)) ;CL list of kernels
	          (setq ee (first ee))
						(cond ((and
							        (eql 2 (length gvars))
							        ($polynomialp ee (cons '(mlist) gvars)
							                         #'(lambda (q) ($freeof x q))
																	  	 #'(lambda (q) (or (eql 0 q) (eql 1 q)))))

									(setq fn (gethash (mapcar #'caar subs) *one-to-one-reduce*))
									(when fn
				    					(setq c0 ($ratcoef ee (first gvars)))
					    				(setq c1 ($ratcoef ee (second gvars)))
							    		(setq b ($substitute 0 (first gvars) ($substitute 0 (second gvars) ee)))
							    		(setq kn0 (second (first subs)))
							    		(setq kn1 (second (second subs)))
							   	  	(funcall fn x c0 kn0 c1 kn1 b)))))))
