(module recip racket
  (provide/contract
   [recip (number? . -> . non-zero/c)]
   [non-zero/c any/c])
  (define (recip x) (/ 1 x))
  (define non-zero/c (and/c number? (not/c zero?))))

(require 'recip)
(recip •)
