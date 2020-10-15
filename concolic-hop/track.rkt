#lang racket/base

(require racket/logging)

(provide (all-defined-out))

(define-logger concolic-trace)
(define concolic-path-log-level 'debug)
(define concolic-path-topic 'concolic:path)

(define (log-trace message data)
  (log-message concolic-trace-logger
               concolic-path-log-level
               concolic-path-topic
               message
               data
               #f))

(define (call-with-tracing action #:path-limit [path-limit #f])
  (define path-conditions '())
  (define path-length 0)
  (define (add-path-condition! log-event)
    (when (or (not path-limit) (< path-length path-limit))
      (set! path-length (add1 path-length))
      (set! path-conditions
            (cons (vector-ref log-event 2) path-conditions))))
  (define results
    (call-with-values
     (λ ()
       (with-intercepted-logging add-path-condition!
         action
         #:logger concolic-trace-logger concolic-path-log-level concolic-path-topic))
     list))
  (apply values
    path-conditions
    results))
