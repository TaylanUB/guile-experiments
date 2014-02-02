(define-syntax-rule (peek expr ...)
  (begin
    (newline)
    (let ((vals (call-with-values
                    (lambda () expr)
                  list)))
      (display ";;; ")
      (if (= 1 (length vals))
          (write (car vals))
          (begin (write "values: ")
                 (write vals)))
      (newline)
      (apply values vals))
    ...))
