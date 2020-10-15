#lang racket/base

(provide (all-defined-out))

(require racket/port
         rackunit
         concolic-hop/lib)

(define-logger concolic:test)

(concolic-test-timeout 10)
(concolic-test-memory (* 256 1024 1024))
(concolic-test-path-limit 2000)

(define regex-failed-with-exn
  #rx" failed with exception")

(define (test-property message
                       property
                       #:all? [all?/fuel #f]
                       #:timeout [timeout #f]
                       #:path-limit [path-limit (concolic-test-path-limit)]
                       #:strategy [strategy #f]
                       #:check [check-check
                                (λ (result)
                                  (check-regexp-match regex-failed-with-exn
                                                      result))])
  (log-concolic:test-info "~a: ~a" (object-name (test-info-action property)) message)
  (define-values (read-end write-end) (make-pipe))
  (define verbose-output (current-output-port))
  (define-values (results cpu real gc)
    (time-apply
     (λ ()
       (with-output-to-string
         (λ ()
           (define string-output (current-output-port))
           (define tid
             (thread
              (λ ()
                (cond
                  [(log-level? concolic:test-logger 'debug)
                   (copy-port read-end string-output verbose-output)]
                  [else
                   (copy-port read-end string-output)]))))
           (parameterize ([current-output-port write-end])
             (define-values (kw-lst kw-val-lst)
               (cond
                 [strategy
                  (values (list '#:strategy)
                          (list strategy))]
                 [else
                  (values '()
                          '())]))
             (keyword-apply concolic-test kw-lst kw-val-lst
                            property
                            '()
                            #:all? all?/fuel
                            #:timeout timeout
                            #:path-limit path-limit))
           (flush-output write-end)
           (close-output-port write-end)
           (sync/timeout/enable-break 0.5 tid))))
     '()))
  (define result (car results))
  (log-concolic:test-info "~a: cpu time: ~a real time: ~a gc time: ~a"
                          (object-name (test-info-action property))
                          cpu real gc)

  (check-check result))
