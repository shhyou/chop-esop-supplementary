(module opaque racket
  (provide/contract [insert (integer? SORTED/C . -> . (and/c (non-empty-listof integer?) ne-sorted?))]
           [ne-sorted? ((non-empty-listof integer?) . -> . boolean?)]
           [SORTED/C any/c])
  (define SORTED/C (or/c empty? (and/c (non-empty-listof integer?) ne-sorted?))))

(module insertion-sort racket
  (require (submod ".." opaque))
  (provide/contract
   [sort (->i ([l (listof any/c)]) (res (l) (and/c SORTED/C (λ (r) (if (empty? l) (empty? r) (cons? r))))))])
  (define (sort xs) (foldl insert xs empty))
  (define (foldl f l b)
    (if (empty? l) b (foldl f (cdr l) (f (car l) b)))))

(require 'insertion-sort)
(sort •)
