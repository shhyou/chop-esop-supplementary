(module f racket
  (provide (contract-out [f (integer? . -> . integer?)]))
  (define (f n)
    (expt n)))

