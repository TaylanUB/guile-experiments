(define (n x max sub)                   ;start with sub=max
  (cond ((= 0 x) (values 0 sub))
        ((= 1 x) (values max sub))
        ((= 2 x) (values (/ max 2.0) sub))
        (else (let-values (((prev sub) (n (- x 1) max sub)))
                (let ((y (- prev sub)))
                  (if (< y 0)
                      (values (- max (/ sub 4.0)) (/ sub 2.0))
                      (values y sub)))))))

(define (n x max sub)                   ;start with sub=2max
  (cond ((= 0 x) (values 0 sub))
        ((= 1 x) (values max sub))
        (else (let-values (((y sub) (n (- x 1) max sub)))
                (let ((y (- y sub)))
                  (if (< y 0)
                      (values (- max (/ sub 4.0)) (/ sub 2.0))
                      (values y sub)))))))

;;; The two above work, but are recursive and use MV returns, not nice.  The
;;; following fails to start the sequence with 0, n, n/2, it starts either with
;;; 0, n, n/4, or 0, n/2, n/4, depending on what you initially assign to `add'.

(define (n x max)
  (let lp ((x x) (max max) (add max) (acc 0))
    (if (= 0 x) (inexact->exact (round acc))
        (let ((acc (+ add acc)))
          (if (> acc max)
              (lp (- x 1) max (- acc max) (/ (- acc max) 2.0))
              (lp (- x 1) max add acc))))))
