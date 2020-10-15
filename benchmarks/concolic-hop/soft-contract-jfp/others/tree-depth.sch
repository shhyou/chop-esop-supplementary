(module tree-depth racket
  (provide
   (contract-out
    [depth (TREE/C . -> . (and/c integer? (>/c 0)))]
    [TREE/C any/c]))
  (provide leaf node)
  (struct leaf ())
  (struct node (l r))
  (define (depth t)
    (if (node? t) (+ 1 (max (depth (node-l t)) (depth (node-r t)))) 0))
  (define (max x y) (if (> x y) x y))
  (define TREE/C (or/c (struct/c leaf)
                       (struct/c node
                                 (recursive-contract TREE/C #:chaperone)
                                 (recursive-contract TREE/C #:chaperone)))))

(require 'tree-depth)
(depth •)
