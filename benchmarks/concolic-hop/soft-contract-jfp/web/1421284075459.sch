(module f racket
  (provide (contract-out [f (-> (>=/c 0) integer?)]))
  (define (f n)
    (/ 1 (- 100 n))))
