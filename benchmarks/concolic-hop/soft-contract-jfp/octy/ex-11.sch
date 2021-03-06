(module g racket
  (provide/contract [g ((cons/c number? number?) . -> . symbol?)]))

(module f racket
  (provide/contract [f (cons? . -> . symbol?)])
  (require (submod ".." g))
  (define (f p)
    (if (and (number? (car p)) (number? (#|HERE|# car p))) (g p) 'no)))

(require 'f)
(f •)
