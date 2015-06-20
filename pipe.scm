(define make-pipe (@ (guile) pipe))

(define (pipe . thunks)
  (let lp ((thunks thunks)
           (input #f)
           (threads '()))
    (if (null? thunks)
        (for-each join-thread threads)
        (let* ((pipe (and (not (null? (cdr thunks))) (make-pipe)))
               (output (and pipe (cdr pipe)))
               (next-input (and pipe (car pipe)))
               (thread (begin-thread
                        (when input (current-input-port input))
                        (when output (current-output-port output))
                        ((car thunks))
                        (when output (close-port output)))))
          (lp (cdr thunks)
              next-input
              (cons thread threads))))))

(define-syntax pipe*
  (syntax-rules ()
    ((_ command ...)
     (pipe (lambda () command) ...))))

;;; Example:
;; (pipe* (display "foo\n")
;;        (display (string-append (read-line) "bar\n"))
;;        (display (string-append (read-line) "baz\n")))
;;; Displays "foobarbaz\n".
