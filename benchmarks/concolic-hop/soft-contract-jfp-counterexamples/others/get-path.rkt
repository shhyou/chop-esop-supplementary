#lang racket
(module lib racket
  (provide/contract
   [path/c any/c]
   [dom/c any/c])
  (define path/c
    (->i ([msg (or/c "hd" "tl")])
	 (res (msg) (cond [(equal? msg "hd") string?]
			  [else (or/c false? path/c)]))))
  (define dom/c
    (->i ([msg (or/c "get-child")])
	 (res (msg) (string? . -> . dom/c)))))

(module get-path racket
  (provide/contract [get-path (dom/c path/c . -> . dom/c)])
  (require (submod ".." lib))
  (define (get-path root p)
    (while root p))
  (define (while cur path)
    (if (and (not (false? path)) (not (false? cur)))
        (while ((cur "get-child") (path "hd"))
          (path #|HERE|# "hd" #;"tl"))
        cur)))

(require 'get-path)
(get-path (λ (✌0)
           (if (equal? ✌0 "get-child")
             (λ (✌1)
               (λ (✌2)
                 (if (equal? ✌2 "get-child")
                   (λ (✌3) (λ (✌4) (error "unknown message: ~s" ✌4)))
                   (error "unknown message: ~s" ✌2))))
             (error "unknown message: ~s" ✌0))) (λ (✌0)
             (if (equal? ✌0 "hd")
               "a"
               (if (equal? ✌0 "tl") #f (error "unknown message: ~s" ✌0)))))
