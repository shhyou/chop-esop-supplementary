(module map racket
  (provide/contract
   [map (->i ([_ (any/c . -> . any/c)] [l any/c])
	     (res (_ l)
		  (and/c (listof any/c)
			 (λ (r) (equal? (empty? l) (empty? r))))))])
  (define (map f xs)
    (if (empty? xs) empty
        (cons (f (car xs)) (map f (cdr xs))))))

(require 'map)
(map • •)
