#lang racket/base

(require racket/contract)

(provide
 (except-out
  (all-defined-out)
  concolic-test-heartbeat-path-step
  concolic-test-heartbeat-pending-step
  concolic-test-heartbeat-new-clause-step)
 (contract-out
  [concolic-test-heartbeat-path-step
   (parameter/c (and/c exact-nonnegative-integer? positive?))]
  [concolic-test-heartbeat-pending-step
   (parameter/c (and/c exact-nonnegative-integer? positive?))]
  [concolic-test-heartbeat-new-clause-step
   (parameter/c (and/c exact-nonnegative-integer? positive?))]))

(define-logger concolic:status)
(define-logger concolic:inputs)
(define-logger concolic:constraint)
(define-logger concolic:adjacent)
(define-logger concolic:heartbeat)

(define concolic-test-heartbeat-path-step (make-parameter 1000))
(define concolic-test-heartbeat-pending-step (make-parameter 150))
(define concolic-test-heartbeat-new-clause-step (make-parameter 5000))
