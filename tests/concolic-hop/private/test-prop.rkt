#lang racket/base

(module config racket/base
  (require racket/port)
  (provide current-printing-port)
  (define current-printing-port
    (make-parameter (open-output-nowhere)))

  (module* printing-to-current-output-port #f
    (current-printing-port (current-output-port)))
  )

(require rackunit
         'config
         "../../../concolic-hop/lib.rkt")

(concolic-test-timeout 3)
(concolic-test-memory (* 256 1024 1024))
(concolic-test-path-limit 2000)

(define-logger concolic:test)

(provide test-proposition
         concolic:test-logger
         log-concolic:test-debug
         log-concolic:test-info
         log-concolic:test-warning
         log-concolic:test-error)

(define (test-proposition-with-config kws kw-vals prop)
  (parameterize ([current-output-port (current-printing-port)])
    (define test-name (object-name (test-info-action prop)))
    (printf "\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n")
    (printf "Testing ~a\n" test-name)
    (log-concolic:test-info "Testing ~a" test-name)
    (define-values (results cpu real gc)
      (time-apply
       (λ () (keyword-apply concolic-test kws kw-vals prop '()))
       '()))
    (log-concolic:test-info "finish  ~a; real time: ~a" test-name real)
    (printf "cpu time: ~a real time: ~a gc time: ~a\n" cpu real gc)
    (check-not-false (car results))))

(define test-proposition (make-keyword-procedure test-proposition-with-config))
