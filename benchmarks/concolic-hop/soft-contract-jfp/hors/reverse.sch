(module main racket
  (provide/contract [main (integer? . -> . integer?)])
  (define (main len)
    (let ([xs (mk-list len)])
      (if (not (= len 0)) (car (reverse xs empty)) 0)))
  
  (define (reverse l ac)
    (if (empty? l) ac (reverse (cdr l) (cons (car l) ac))))
  
  (define (mk-list n)
    (if (#|HERE|#< n 0) empty (cons n (mk-list (- n 1))))))

(require 'main)
(main •)
