;; https://sourceforge.net/p/maxima/mailman/message/35054017/

;; Code by Richard Fateman

;; stopme command, only for sbcl

(in-package :maxima)

(defmspec $stopme(args)    ;; usage:  stopme (do x:x+1, 2) ; stops infinite loop after 2 sec
   (let* ((evalme(cadr args))          ;  not evaluated !
          (timelimit (meval (caddr args))) ; evaluate the time limit

      (v (sb-ext::make-timer ;; the timer program
          (lambda()
            (format t "~%your time limit of ~s seconds ran out" timelimit)
            (throw 'stopme `((mtext) "timed out on " ,evalme))))))
     (catch 'stopme
       (progn
         (sb-ext::schedule-timer v timelimit)
         (prog1 (meval evalme)
           (sb-ext::unschedule-timer v))))))
