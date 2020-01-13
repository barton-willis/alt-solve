(in-package :maxima)

(eval-when (:compile-toplevel :load-toplevel :execute)
   ($load "grobner"))

(defun $myalgsys (ee x)
   (mtell "Top of myalgsys ee = ~M  x = ~M ~%" ee x)

   ;;error when ee or x isn't a Maxima list.
   (when (or (not ($listp ee)) (not ($listp x)))
      (merror (intl:gettext "myalgsys: both arguments must be a Maxima lists")))

   ;;error when not every unknown is a mapatom
   (when (not (every #'$mapatom (cdr x)))
      (merror  (intl:gettext "myalgsys: each unknown must be a maptom")))

   (let ((sol) (cnds) (e))
       (setq e (mapcar #'meqhk (cdr ee))) ; remove '(mlist) and convert a=b to a-b
       (setq cnds (mapcar #'(lambda (q) (take '(mnotequal) ($ratdenom q) 0)) e))
       (setq e (mapcar #'$ratnumer e)) ;remove denominators

       ;; error for non-rational expression inputs
       (when (not (every #'(lambda (q) ($polynomialp q x
   			              	#'(lambda (s) ($lfreeof x s))
   	   	           		  #'(lambda (s) (and (integerp s) (>= s 0))))) (append e cnds)))
            (merror (intl:gettext "myalgsys: equations must be a list of rational expressions.")))


       (setq e (cons '(mlist) e))  ; return e to a Maxima list
       (setq e ($poly_reduced_grobner e x))
       (setq e ($expand e 0 0)) ;I think poly_reduced_grobner returns unsimplified
       (setq e ($setify e))
       (setq x ($setify x))
       (setq e (triangularize-eqs e x))
       (setq sol (solve-triangular-system (cdr e) (cdr x)))
       (setq sol (mapcar #'(lambda (q) (cons '(mlist) q)) sol))
       (if sol (simplifya (cons '(mlist) sol) t) ee)))
