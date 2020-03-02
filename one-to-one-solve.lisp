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

(defvar *one-to-one-reduce* (make-hash-table))

(setf (gethash (list '%sin '%sin) *one-to-one-reduce*)
	  #'(lambda (a b) 42))


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
  (let ((ee) (b) (subs nil) (gvars nil))
     (flet ((is-a-kernel (e)
	           (and
						  	(consp e)
						  	(consp (car e))
						  	(member (caar e) (list '%sin '%cos '%tan '%log '%sqrt 'mexpt) :test #'eql))))
		     	  (setq ee (kernelize-fn e #'is-a-kernel))
		    		(setq subs (second ee))
						(setq gvars (mapcar #'cdr subs))
						(setq subs (mapcar #'car subs))
						(displa (cons '(mlist) gvars))
						(displa (cons '(mlist) subs))

			      (first ee))))
