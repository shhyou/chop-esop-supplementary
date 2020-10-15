#lang racket
(module lib racket
  (define append (λ (✌0 ✌1) (error "ASSERT_UNREACHABLE")))
  (provide/contract [append ((listof any/c) (listof any/c) . -> . (listof any/c))]))

(module flatten racket
  (provide/contract [flatten (any/c . -> . (listof any/c))])
  (require (submod ".." lib))
  (define (flatten x)
    (cond
      [(empty? x) empty]
      [(cons? x) (append [flatten (car x)] (cdr x) #|HERE|##;[flatten ])]
      [else (cons x empty)])))

(require 'flatten)
(flatten (cons 0 0))
