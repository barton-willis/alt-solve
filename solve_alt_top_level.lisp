;;;; Author: Barton Willis
;;;; Common Lisp/Maxima code for symbolic solutions of equations.

;;;; This work is licensed under a Creative Commons Attribution-ShareAlike 4.0 International License.
;;;; https://creativecommons.org/licenses/by-sa/4.0/

(in-package :maxima)

;;; sort solutions using orderlessp & maintain correct ordering of multiplicities.
(defun sort-solutions (sol &optional (ignore-multiplicities nil))
  ;; Is the length check needed? Of course, if it fails, it's a bug. For the equation
  ;; solve([y*sin(x)=0,cos(x)=0],[x,y]), multiplicities is incorrectly set to [1]. Untill
  ;; this bug is fixed, we need the length check.
  (cond ((and ($listp sol) (not ignore-multiplicities) ($listp $multiplicities) (eql (length sol) (length $multiplicities)))
         (setq sol (mapcar #'(lambda (a b) (cons a b)) (cdr sol) (cdr $multiplicities)))
         (setq sol (sort sol #'$orderlessp :key #'car))
         (setq $multiplicities (mapcar #'cdr sol))
         (setq sol (mapcar #'car sol))
         (setq $multiplicities (simplifya (cons '(mlist) $multiplicities) t))
         (simplifya (cons '(mlist) sol) t))

      (($listp sol)
         ;; might be a list of lists, so apply sort-solutions to each list member
         (setq sol (mapcar #'(lambda (q) (sort-solutions q t)) (cdr sol)))
         ;; now sort the list of solutions
         (setq sol (sort sol #'$orderlessp))
         (simplifya (cons '(mlist) sol) t))

     (t
        ;; solution isn't a list, so just return
        sol)))

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

;;; Issue is that solutions & multiplicities get jumbled!
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

;;; Experimental function that solves an equation and attemps to determine if each solution
;;; is consistent with the fact database. We use featurep to decide check declared facts--especially
;;; for real values, featurep isn't all that smart.

;;; One issue: when sol = $all. Another issue is that solutions & multiplicities get jumbled!

(defun $solve_filter (e x)
  (let ((sol (cdr ($solve e x))) (fcts) (ssol nil) (chk) ($opsubst t))
     (setq x (if (or ($listp x) ($setp x)) (cdr x) (list x)))
     (setq fcts (simplifya (cons '(mand) (mapcan #'(lambda (q) (cdr ($facts q))) x)) t))
     (dolist (sx sol)
        (setq chk ($substitute sx fcts))
        (setq chk ($substitute '$featurep '$kind chk))
        (setq chk (mfuncall '$maybe chk))
        (cond ((eql chk t)
               (push sx ssol))
              ((eql chk '$unknown)
                (intl:gettext
                  (mtell "Solve: unable to verify solution ~M is consistent with fact database ~%" sx))
                (push sx ssol))))
      (simplifya (cons '(mlist) ssol) t)))
