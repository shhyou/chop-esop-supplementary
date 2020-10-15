#lang racket/base

(require racket/list
         racket/generic
         racket/match
         racket/contract/base
         "queue.rkt"

         "data.rkt"
         "path.rkt")

(provide
 gen:concolic-queue concolic-queue? concolic-queue/c
 concolic-queue-empty? concolic-queue-insert! concolic-queue-extract!
 (contract-out
  [ignore-locals-adapter ((-> concolic-queue?)
                         . -> .
                         (-> concolic-queue?))]
  [simple-destructor-adapter ((-> concolic-queue?)
                              . -> .
                              (-> concolic-queue?))]
  [breadth-first-search-strategy (-> concolic-queue?)]
  [simple-prioritize-branch-strategy (exact-nonnegative-integer?
                                      . -> .
                                      (-> concolic-queue?))])
 )

(define-generics concolic-queue
  (concolic-queue-empty? concolic-queue)
  (concolic-queue-insert! concolic-queue new-pending-element)
  (concolic-queue-extract! concolic-queue))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (a$list≡-has-locals? a$xs≡)
  (match a$xs≡
    [(a$empty≡ _) #f]
    [(a$cons≡ _ a$car≡ a$cdr≡)
     (or (a$≡-has-locals? a$car≡)
         (a$list≡-has-locals? a$cdr≡))]))

(define (a$≡-has-locals? a$≡)
  (match a$≡
    [(struct a$x≡ _) #t]
    [(struct a$X≡ _) #f]
    [(struct a$λ≡ _) #f]
    [(struct a$empty≡ _) #f]
    [(struct* a$cons≡ ([car car≡] [cdr cdr≡]))
     (or (a$≡-has-locals? car≡) (a$≡-has-locals? cdr≡))]
    [(struct a$let≡ (elim≡))
     (match elim≡
       [(struct* a$%app≡ ([arg arg≡])) (a$≡-has-locals? arg≡)]
       [(struct a$car≡ _) #f]
       [(struct a$cdr≡ _) #f])]))

#|
Forbids canonical functions from using local variables. Technically,
this strategy ignores any pending input whose predicted path contains
a dispatch of canonical function that uses local variables.
|#
(struct ignore-locals-wrapper (queue)
  #:methods gen:concolic-queue
  [(define/generic super::concolic-queue-empty? concolic-queue-empty?)
   (define/generic super::concolic-queue-insert! concolic-queue-insert!)
   (define/generic super::concolic-queue-extract! concolic-queue-extract!)

   (define (concolic-queue-empty? queue)
     (super::concolic-queue-empty? (ignore-locals-wrapper-queue queue)))
   (define (concolic-queue-insert! queue new-pending)
     (define path-keys
       (path-constraint->key (pending-partial-inputs new-pending)
                             (pending-prediction new-pending)))
     (define has-locals?
       (for/or ([a-path-key (in-vector path-keys)])
         (match a-path-key
           [(or #t #f) #f]
           [(struct list-access≡ _) #f]
           [(struct dispatch-else≡ _) #f]
           [(struct* dispatch≡ ([kind a$≡]))
            (a$≡-has-locals? a$≡)])))
     (when (not has-locals?)
       (super::concolic-queue-insert! (ignore-locals-wrapper-queue queue) new-pending)))
   (define (concolic-queue-extract! queue)
     (super::concolic-queue-extract! (ignore-locals-wrapper-queue queue)))])

(define ((ignore-locals-adapter strategy))
  (ignore-locals-wrapper (strategy)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
For list values, either immediately extract the head element and
dispatch on the result or discard the head element.
|#
(struct simple-destructor-wrapper (queue)
  #:methods gen:concolic-queue
  [(define/generic super::concolic-queue-empty? concolic-queue-empty?)
   (define/generic super::concolic-queue-insert! concolic-queue-insert!)
   (define/generic super::concolic-queue-extract! concolic-queue-extract!)

   (define (concolic-queue-empty? queue)
     (super::concolic-queue-empty? (simple-destructor-wrapper-queue queue)))
   (define (concolic-queue-insert! queue new-pending)
     (define path-keys-list
       (vector->list
        (path-constraint->key (pending-partial-inputs new-pending)
                              (pending-prediction new-pending))))
     (define correct-destruct-order?
       (for/fold ([correct? #t]
                  ;; locals : (listof (listof (or/c 'car 'cdr)))
                  [locals '()]
                  #:result correct?)
                 ([a-path-key (in-list path-keys-list)]
                  [prev-path-key (in-list (cons #f path-keys-list))])
         #:break (not correct?)
         (match a-path-key
           [(or #t #f)                (values correct? locals)]
           [(struct list-access≡ _)   (values correct? locals)]
           [(struct dispatch-else≡ _) (values correct? (cons '() locals))]
           [(struct* dispatch≡ ([key key] [kind a$≡]))
            (define new-locals (cons '() locals))
            (define correct-access?
              (match a$≡
                [(struct a$x≡ _) #t]
                [(struct a$X≡ _) #t]
                [(struct a$λ≡ _) #t]
                [(struct a$list≡ _) #t]
                [(struct a$let≡ ((struct a$%app≡ _))) #t]
                [(struct a$let≡ ((struct a$car≡ ((struct a$x≡ (idx))))))
                 (define used-eliminators
                   (list-ref new-locals idx))
                 (cond
                   ;; if a list were to be examined, it must be immediately decomposed
                   [(not (zero? idx))
                    #f]
                   [else
                    (set! new-locals (list-set new-locals idx
                                               (cons 'car used-eliminators)))
                    #t])]
                [(struct a$let≡ ((struct a$cdr≡ ((struct a$x≡ (idx))))))
                 (define used-eliminators
                   (list-ref new-locals idx))
                 (cond
                   [(member 'cdr (list-ref new-locals idx)) ;; duplicated
                    #f]
                   [else
                    (set! new-locals (list-set new-locals idx
                                               (cons 'cdr used-eliminators)))
                    #t])]))
            (values correct-access? new-locals)])))
     (when correct-destruct-order?
       (super::concolic-queue-insert!
        (simple-destructor-wrapper-queue queue)
        new-pending)))
   (define (concolic-queue-extract! queue)
     (super::concolic-queue-extract! (simple-destructor-wrapper-queue queue)))])

(define ((simple-destructor-adapter strategy))
  (simple-destructor-wrapper (strategy)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(struct bfs-queue (data)
  #:methods gen:concolic-queue
  [(define (concolic-queue-empty? queue)
     (queue-empty? (bfs-queue-data queue)))
   (define (concolic-queue-insert! queue new-pending)
     (queue-insert-last! (bfs-queue-data queue)
                         new-pending))
   (define (concolic-queue-extract! queue)
     (define-values (_queue-key new-pending)
       (queue-remove-first! (bfs-queue-data queue)))
     new-pending)])

(define (breadth-first-search-strategy)
  (bfs-queue (make-empty-queue)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(struct simple-prioritize-branch-queue (fuel
                                        [remainings #:mutable]
                                        branch-data
                                        other-data)
  #:methods gen:concolic-queue
  [(define (concolic-queue-empty? queue)
     (and (queue-empty? (simple-prioritize-branch-queue-branch-data queue))
          (queue-empty? (simple-prioritize-branch-queue-other-data queue))))
   (define (concolic-queue-insert! queue new-pending)
     (define predicted-path-constraint
       (pending-prediction new-pending))
     (cond
       [(and (not (path-constraint-empty? predicted-path-constraint))
             (branch? (last-path-condition predicted-path-constraint)))
        (queue-insert-last! (simple-prioritize-branch-queue-branch-data queue)
                            new-pending)]
       [else
        (queue-insert-last! (simple-prioritize-branch-queue-other-data queue)
                            new-pending)]))
   (define (concolic-queue-extract! queue)
     (define-values (_queue-key new-pending)
       (cond
         [(and (not (queue-empty? (simple-prioritize-branch-queue-branch-data queue)))
               (positive? (simple-prioritize-branch-queue-remainings queue)))
          (set-simple-prioritize-branch-queue-remainings!
           queue
           (sub1 (simple-prioritize-branch-queue-remainings queue)))
          (queue-remove-first! (simple-prioritize-branch-queue-branch-data queue))]
         [(and (queue-empty? (simple-prioritize-branch-queue-other-data queue))
               (zero? (simple-prioritize-branch-queue-remainings queue)))
          (queue-remove-first! (simple-prioritize-branch-queue-branch-data queue))]
         [else
          (when (zero? (simple-prioritize-branch-queue-remainings queue))
            (set-simple-prioritize-branch-queue-remainings!
             queue
             (simple-prioritize-branch-queue-fuel queue)))
          (queue-remove-first! (simple-prioritize-branch-queue-other-data queue))]))
     new-pending)])

(define ((simple-prioritize-branch-strategy fuel))
  (simple-prioritize-branch-queue fuel fuel (make-empty-queue) (make-empty-queue)))
