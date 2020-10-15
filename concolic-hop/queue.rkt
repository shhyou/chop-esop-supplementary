#lang racket/base

(provide make-empty-queue
         queue-empty?
         queue-count
         queue-first
         queue-insert!
         queue-insert-last!
         queue-remove-first!
         queue-ref
         queue-remove!)

(require data/order
         data/splay-tree)

(struct splay-queue (data [next-key #:mutable]))

(define dict-order
  (order '< exact? = <))

(define (make-empty-queue)
  (splay-queue (make-splay-tree dict-order)
               1))

(define (queue-empty? queue)
  (zero? (queue-count queue)))

(define (queue-count queue)
  (splay-tree-count (splay-queue-data queue)))

(define (queue-first queue)
  (define priority-queue
    (splay-queue-data queue))
  (define idx (splay-tree-iterate-least priority-queue))
  (unless idx
    (error 'queue-first "empty priority queue"))
  (values (splay-tree-iterate-key priority-queue idx)
          (splay-tree-iterate-value priority-queue idx)))

(struct no-key ())
(define no-key-value (no-key))

(define (queue-insert! queue new-value [base-priority 0])
  (define priority-queue
    (splay-queue-data queue))
  (define new-key
    (let loop ()
      (define new-key
        (+ (splay-queue-next-key queue) base-priority))
      (set-splay-queue-next-key! queue
                                 (+ 1 (splay-queue-next-key queue)))
      (cond [(no-key? (splay-tree-ref priority-queue new-key (λ () no-key-value)))
             new-key]
            [else
             (loop)])))
  (splay-tree-set! priority-queue new-key new-value)
  new-key)

(define (queue-insert-last! queue new-value)
  (define priority-queue
    (splay-queue-data queue))
  (define key-max
    (cond [(splay-tree-iterate-greatest priority-queue)
           => (λ (idx) (splay-tree-iterate-key priority-queue idx))]
          [else 0]))
  (define new-key (+ key-max 1))
  (splay-tree-set! priority-queue new-key new-value)
  new-key)

(define (queue-remove-first! queue)
  (define priority-queue
    (splay-queue-data queue))
  (when (zero? (splay-tree-count priority-queue))
    (error 'remove-first! "empty priority queue"))
  (define idx-min
    (splay-tree-iterate-least priority-queue))
  (define key-min (splay-tree-iterate-key priority-queue idx-min))
  (define value-min (splay-tree-iterate-value priority-queue idx-min))
  (splay-tree-remove! priority-queue key-min)
  (values key-min value-min))

(define (queue-ref queue key)
  (splay-tree-ref (splay-queue-data queue) key))

(define (queue-remove! queue key)
  (define old-value (queue-ref queue key))
  (splay-tree-remove! (splay-queue-data queue) key)
  old-value)
