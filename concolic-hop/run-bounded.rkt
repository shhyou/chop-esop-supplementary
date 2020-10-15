#lang racket/base

(require racket/async-channel
         racket/match)

(provide (all-defined-out))

(struct exn:fail:would-diverge exn:fail (function args) #:transparent)
(define (raise-input-would-cause-divergent-error function . args)
  (raise (exn:fail:would-diverge
          (format "~a: input would cause divergent" function)
          (current-continuation-marks)
          function
          args)))

(struct run () #:transparent)

(struct run:terminated run (marks cpu real gc) #:transparent)
(struct run:terminated:killed run:terminated () #:transparent)
(struct run:terminated:out-of-memory run:terminated () #:transparent)

(struct run:timed run (cpu real gc) #:transparent)
(struct run:timed:normal run:timed (results) #:transparent)
(struct run:timed:exn run:timed (exception) #:transparent)
(struct run:timed:would-diverge run:timed (exception) #:transparent)

(define ((timed-run result-channel thunk))
  (define-values (status cpu-time real-time gc-time)
    (time-apply
     (λ ()
       (with-handlers ([exn:fail:would-diverge? (λ (e) (cons 'diverge e))]
                       [exn:fail? (λ (e) (cons 'exn e))])
         (call-with-values thunk (λ results (cons 'normal results)))))
     '()))
  (define result
    (match status
      [(list (cons 'diverge e))
       (run:timed:would-diverge cpu-time real-time gc-time e)]
      [(list (cons 'exn e))
       (run:timed:exn cpu-time real-time gc-time e)]
      [(list (cons 'normal results))
       (run:timed:normal cpu-time real-time gc-time results)]))
  (async-channel-put result-channel result))

(define (run-with-limit thunk
                        #:timeout [timeout #f]
                        #:memory [memory-limit #f])
  (define test-custodian (make-custodian))
  (define shutdown-box
    (make-custodian-box test-custodian 'available))
  (when memory-limit
    (custodian-limit-memory test-custodian memory-limit))
  (define result-channel (make-async-channel 1))
  (define thread-id
    (parameterize ([current-custodian test-custodian])
      (thread/suspend-to-kill (timed-run result-channel thunk))))
  (define suspend-evt (thread-suspend-evt thread-id))
  (match-define-values ((list ended-event)
                        cpu-time
                        real-time
                        gc-time)
    (time-apply
     sync/timeout/enable-break
     (list timeout
           thread-id
           shutdown-box
           suspend-evt)))
  (unless ended-event (kill-thread thread-id))
  (sync/enable-break thread-id shutdown-box suspend-evt)
  (cond
    [(not (custodian-box-value shutdown-box))
     (run:terminated:out-of-memory (continuation-marks thread-id)
                                   cpu-time
                                   real-time
                                   gc-time)]
    [(not ended-event)
     (run:terminated:killed (continuation-marks thread-id)
                            cpu-time
                            real-time
                            gc-time)]
    [else
     (async-channel-get result-channel)]))
