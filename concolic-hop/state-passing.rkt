#lang racket/base

(require racket/contract/base
         racket/contract/parametric
         racket/match)

(provide
 server?
 (contract-out
  [call-with-server ((any/c (server? . -> . any/c))
                     (#:name symbol?)
                     . ->* .
                     list?)]

  [get-local-state       (server? . -> . any/c)]
  [set-local-state!      (server? any/c . -> . any)]
  [call-with-local-state (server? any/c (-> any) . -> . any)]
  [update-local-state!   (server? (any/c . -> . any/c) . -> . any)]

  [choose*! (let ([a (new-∀/c 'a)])
              ((server? (listof a)) . ->* . a))]
  [choose! (let ([a (new-∀/c 'a)])
             ((server?) #:rest (listof a) . ->* . a))]
  [local-abort! (server? . -> . any)]))

(struct server (tag) #:transparent)
(struct request (what κ) #:transparent)
(struct done (values) #:transparent)

(struct request:get () #:transparent)
(struct request:set (value) #:transparent)
(struct request:choose (args) #:transparent)
(struct request:abort () #:transparent)

(define (call-with-server #:name [name #f]
                          initial-state
                          proc)
  (define tag
    (cond [name (make-continuation-prompt-tag name)]
          [else (make-continuation-prompt-tag)]))

  (let loop ([message (call-with-continuation-prompt
                       (λ () (done (proc (server tag))))
                       tag)]
             [current-state initial-state])
    (match message
      [(struct done (result))
       (list result)]
      [(struct request (what κ))
       (match what
         [(struct request:get ())
          (loop (κ current-state) current-state)]
         [(struct request:set (new-state))
          (loop (κ (void)) new-state)]
         [(struct request:choose (args))
          (for*/list ([arg (in-list args)]
                      [result (in-list (loop (κ arg) current-state))])
            result)]
         [(struct request:abort ())
          '()])])))

(define (send! server value)
  (define tag (server-tag server))
  (call-with-composable-continuation
   (λ (κ)
     (abort-current-continuation
      tag
      (λ ()
        (request
         value
         (λ args
           (call-with-continuation-prompt
            (λ () (apply κ args))
            tag))))))
   tag))

(define (get-local-state server)
  (send! server (request:get)))

(define (set-local-state! server new-state)
  (send! server (request:set new-state)))

(define (update-local-state! server f)
  (set-local-state! server (f (get-local-state server))))

(define (call-with-local-state server temp-state thunk)
  (define old-state (get-local-state server))
  (set-local-state! server temp-state)
  (define results (call-with-values thunk list))
  (set-local-state! server old-state)
  (apply values results))

(define (choose*! server args)
  (send! server (request:choose args)))

(define (choose! server . args)
  (choose*! server args))

(define (local-abort! server)
  (send! server (request:abort)))

(module* test racket/base
  (require racket/set
           rackunit
           (submod ".."))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      5))
   '(5))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (get-local-state server)))
   '(3))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (choose! server 1 2)))
   '(1 2))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (define n (choose! server 1 2))
      (set-local-state! server
                        (add1 (get-local-state server)))
      (cons n (get-local-state server))))
   '((1 . 4) (2 . 4)))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (define n (choose! server 1 2))
      (define m (choose! server 3 4))
      (list n m)))
   '((1 3) (1 4) (2 3) (2 4)))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (update-local-state! server sub1)
      (get-local-state server)))
   '(2))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (choose*! server '(a b c))))
   '(a b c))


  (check-equal?
   (call-with-server
    0
    (λ (server)
      (define n (choose! server 1 2))
      (when (= n 1)
        (local-abort! server))
      n))
   '(2))

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (choose*! server '())))
   '())

  (check-equal?
   (call-with-server
    3
    (λ (server)
      (define val (choose*! server '(a b c)))
      (choose*! server
                (cond
                  [(equal? val 'b) '()]
                  [else            (list val)]))))
   '(a c))

  (check-equal?
   (call-with-server
    0
    (λ (server)
      (define n (choose! server 1 2 3))
      (when (= n 2)
        (local-abort! server))
      n))
   '(1 3))

  (check-equal?
   (call-with-server
    0
    (λ (server)
      (define n (choose! server 1 2 3))
      (define m (choose! server 'a 'b 'c))
      (when (and (= n 2) (equal? m 'b))
        (local-abort! server))
      (list n m)))
   '((1 a) (1 b) (1 c)
           (2 a) (2 c)
           (3 a) (3 b) (3 c)))

  (check-equal?
   (call-with-server
    0
    (λ (server)
      (define n (choose! server 1 2 3))
      (when (= n 2)
        (local-abort! server))
      (define m (choose! server 'a 'b 'c))
      (when (equal? m 'b)
        (local-abort! server))
      (list n m)))
   '((1 a) (1 c) (3 a) (3 c)))

  ;; edit state via local-server but choose via server
  ;; because local-server is inside server, its state
  ;; should also be rolled back by server as well.
  ;;
  ;; choosing via local-server, however, will not restore
  ;; the modification to server state.
  (check-equal?
   (call-with-server
    -1
    (λ (server)
      (define inner-results
        (call-with-server
         0
         (λ (local-server)
           (set-local-state! local-server (+ 1 (get-local-state local-server)))
           (define n (choose! server 100 200 300))
           (set-local-state! local-server (+ n (get-local-state local-server)))

           (define 1A/2B/3C (choose! local-server '(1 A) '(2 B) '(3 C)))
           (set-local-state! server (+ (car 1A/2B/3C) (get-local-state server)))

           (list (get-local-state server)
                 (get-local-state local-server)
                 (cadr 1A/2B/3C)))))
      (list (get-local-state server)
            inner-results)))
   '((5 ((0 101 A)
         (2 101 B)
         (5 101 C)))
     (5 ((0 201 A)
         (2 201 B)
         (5 201 C)))
     (5 ((0 301 A)
         (2 301 B)
         (5 301 C)))))

  (let ()
    (define visited '())

    (check-equal?
     (list->set
      (call-with-server
       -2
       (λ (server)
         (define s (get-local-state server))
         (define n (choose! server 1 2 3 4))
         (set-local-state! server (+ s n))

         (when (= n 3)
           (local-abort! server))

         (define m (choose*! server '(a b c)))
         (set! visited (cons (cons n m) visited))

         (update-local-state! server (λ (t) (cons t m)))

         (define s2 (get-local-state server))
         (when (member s2 '((0 . a) (0 . c)))
           (local-abort! server))
         (cons "ok" (get-local-state server)))))
     (set
      (cons "ok" (cons -1 'a))
      (cons "ok" (cons -1 'b))
      (cons "ok" (cons -1 'c))
      (cons "ok" (cons 0 'b))
      (cons "ok" (cons 2 'a))
      (cons "ok" (cons 2 'b))
      (cons "ok" (cons 2 'c))))

    (check-equal?
     (list->set visited)
     (set (cons 1 'a) (cons 1 'b) (cons 1 'c)
          (cons 2 'a) (cons 2 'b) (cons 2 'c)
          (cons 4 'a) (cons 4 'b) (cons 4 'c)))))
