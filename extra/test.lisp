;(proclaim '(optimize (speed 3)))
(declaim (optimize (speed 3)))

(Defstruct boolean-state-space
  vars)

(defstruct state 
  hash)

(defun enumerate-states (space)
  (mapcar (lambda (x) (make-state :hash 
				  (let ((h (make-hash-table :Test #'eq)))
				    (dolist (item x)
				      (setf (gethash (car item) h) (cdr item)))
				    h)))
	  (enumerate-boolean-hashes (boolean-state-space-vars space))))

(Defun enumerate-boolean-hashes (vars)
  (if (null vars)
      (list nil)
      (let ((recs (enumerate-boolean-hashes (cdr vars))))
	(mapcan (lambda (x) 
		  (mapcar (lambda (y) (cons (cons (car vars) x) y))
			  recs))
		'(t nil)))))

;(load "/Users/w01fe/Projects/angel/test.lisp")

; (time (length (enumerate-states (make-boolean-state-space :vars '(:a :b :c :d :e :f :g :h :i :j :k :l :m :n :o :p :q :r )))))


(defun smartpow (x n)
  (Declare (fixnum n)
	   (double-float x))
  (let ((ret 1.0d0))
    (declare (Double-float ret))
    (loop repeat n do (Setf ret (* ret x)))
    ret))

(defun stupidpow (x n)
  (let ((ret 1.0d0))
    (loop repeat n do (Setf ret (* ret x)))
    ret))

(defun stupidpow2 (x n)
  (reduce #'* (loop repeat n collect x)))

;  (if (= n 0) 1 (* x (stupidpow x (- n 1)))))

; (dotimes (i 5) (time (stupidpow2 1.00001d0 100000000)))

; (dotimes (i 5) (time (print (smartpow 1.00000001d0 100000000))))