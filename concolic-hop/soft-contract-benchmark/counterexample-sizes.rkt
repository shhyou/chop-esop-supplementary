#lang racket
(require "private/paths.rkt")

(define (size-delta file.sch)
  (- (size-of (file.sch->counterexample-file.rkt file.sch))
     (size-of file.sch)))

(define ht (make-hash))
(define (size-of file)
  (hash-ref!
   ht
   file
   (λ ()
     (call-with-input-file file
       (λ (port)
         (let loop ([n 0])
           (define b (read-byte port))
           (cond
             [(eof-object? b) n]
             [else (loop (+ n 1))])))))))
(define (get-sizes)
  (sort
   (for/list ([file.sch (in-list sch-files)]
              #:when (known-to-work? file.sch))
     (list (file.sch->string file.sch)
           (size-delta file.sch)))
   >
   #:key cadr))

(module+ main
  (define sizes (get-sizes))
  (printf "total size of the counterexamples, in bytes: ~a\n" (apply + (map cadr sizes)))
  (printf "sizes of the source text of the counterexamples, in bytes:\n")
  (pretty-write sizes))
