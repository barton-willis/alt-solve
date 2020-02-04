(defvar *loaded-files* (make-hash-table :test #'equal))
(defvar *thyme* 0)

(setf (symbol-function '$load_original) (symbol-function '$load))

(defun $load (fn)
	(let ((n (or (gethash fn *loaded-files*) 0)) (z))
			(setf (gethash fn *loaded-files*) (+ n 1))
		 	(setq z (get-internal-real-time))
		 	($load_original fn)
		 	(incf *thyme* (- (get-internal-real-time) z))))

(defun $loadreport ()
	(let ((z nil))
		 (print `(time = ,(/ (float *thyme*) internal-time-units-per-second) seconds))
		 (maphash #'(lambda (key val) (push (list val key) z))  *loaded-files*)
		 (setq z (sort z #'(lambda (a b) (> (first a) (first b)))))
		 (dolist (zk z)
			 (print zk))))
