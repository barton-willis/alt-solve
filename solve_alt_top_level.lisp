;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

;;; Attempt to verify that sol is a solution to the equations eqs. When sol is a solution, return
;;; 'ok; when the solution is definitely spurious, return 'spurious; otherwise, return 'maybe.
;;; eqs can be either a list of equations or a single equation.

;;; To verify a solution, we use try-to-crunch-to-zero followed by trigsimp. We could, of course,
;;; try other methods.

(defun check-solution (eqs sol) "Attempt to verify that sol is a solution to the equations eqs "
   (setq eqs ($substitute sol eqs))
   (setq eqs (if ($listp eqs) (cdr eqs) (list eqs)))
   (setq eqs (mapcar #'(lambda (s) (mfuncall '$trigsimp (try-to-crunch-to-zero (meqhk s)))) eqs))
   (setq eqs (mapcar #'(lambda (s) (mfuncall '$is (mfuncall '$maybe (take '($equal) s 0)))) eqs))

   (cond ((some #'(lambda (s) (not s)) eqs) 'spurious)
         ((some #'(lambda (s) (eql s '$unknown)) eqs) 'maybe)
         (t 'ok)))

;;; Alternative top-level solve. This function solves, checks each putative solution, and sorts
;;; the non-spurious solutions. It prints a message for each solution that it is unable to verify
;;; and for each purely spurious solution. The spurious solutions are excluded from the returned
;;; solution.

(defun $solve_checked (e x)
  (let ((sol ($solve e x)) (ok-sol nil) (maybe-sol nil) (bogus-sol nil) (chk))
     (cond (($listp sol)
              (setq sol (cdr sol)) ; remove '(mlist)
              (dolist (sx sol)
                 (setq chk (check-solution e sx))
                 (cond ((eql chk 'maybe)
                     (intl:gettext
                        (mtell "Solve: unable to verify putative solution ~M to equation ~M for unknown ~M ~%" sx e x))
                     (push sx maybe-sol))
                 ((eql chk 'spurious)
                    (intl:gettext
                        (mtell "Spurious solution ~M to equation ~M for ~M ~%" sx e x))
                     (push sx bogus-sol))
                 (t
                    (push sx ok-sol))))
                ($sort (simplifya (cons '(mlist) (append maybe-sol ok-sol)) t)))
              (t
                (intl:gettext
                   (mtell "Solve: returning nonlist solution to equation ~M for unknown ~M ~%" e x))
                sol))))
