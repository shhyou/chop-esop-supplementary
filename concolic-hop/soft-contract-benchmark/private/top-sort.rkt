#lang racket
(provide do-the-top-sort)
(require "misc.rkt")
(module+ test (require rackunit))

(require racket/contract/private/top-sort)
(define (do-the-top-sort l)
  (define elements (apply vector l))
  (define neighbors (build-neighbors elements))
  (define (failed bad-cycle)
    (error 'convert.rkt
           "found circular reference in top-level definitions~a"
           (apply string-append
                  (for/list ([i (in-list bad-cycle)])
                    (define expr (vector-ref elements i))
                    (define vars (get-defining-variables expr))
                    (define formatted-expr
                      (cond
                        [(pair? vars)
                         (format "  definition of~a"
                                 (apply string-append
                                        (for/list ([var (in-list vars)])
                                          (format " ~a" var))))]
                        [else (format "  ~a" (pretty-format expr #:mode 'write))]))
                    (format "\n  ~a\n" formatted-expr)))))
  (define sorted
    (top-sort (for/list ([e (in-list l)]
                         [i (in-naturals)])
                i)
              (λ (i) (hash-ref neighbors i '()))
              failed))
  (for/list ([i (in-list sorted)])
    (vector-ref elements i)))

(define (build-neighbors elements)
  (define neighbors (make-hash))
  (for ([e-from (in-vector elements)]
        [i-from (in-naturals)])
    (for ([e-to (in-vector elements)]
          [i-to (in-naturals)]
          #:unless (= i-from i-to))
      (when (defines-and-references? e-to e-from)
        (hash-set! neighbors i-from
                   (cons i-to (hash-ref neighbors i-from '()))))))
  neighbors)

(define (defines-and-references? a b)
  (define a-defines (get-defining-variables a))
  ;; if `a` is a definition, see
  ;; if `b` mentions the bound variable
  (let loop ([b b])
    (match b
      ;; shouldn't look for references inside
      ;; functions or the delayed part of an ->i,
      [`(λ ,x ,b) #f]
      [`(lambda ,x ,b) #f]
      [`(define (,f ,x ...) ,b ...) #f]
      [`(->i ([,(? symbol?) ,arg-ctcs] ...)
             [,(? symbol?) (,(? symbol?) ...) ,ignored])
       (for/or ([arg-ctc (in-list arg-ctcs)])
         (loop arg-ctc))]
      ;; or at struct definitions
      [`(define-struct . ,_) #f]
      [`(struct . ,_) #f]
      ;; but otherwise we just look in a dumb way
      [(? symbol?) (and (member b a-defines) #t)]
      [(? list?)
       (for/or ([b (in-list b)])
         (loop b))]
      [_ #f])))

(define (get-defining-variables tl)
  (match tl
    [`(define (,(? symbol? s) ,x ...) ,body ...)
     (list s)]
    [`(define ,(? symbol? s) ,body) (list s)]
    [`(define-ctc ,(? symbol? s) ,body) (list s)]
    [`(define-id-with-ctc
        ,ctc
        ,underscore-name
        ,name
        ,_1 ,_2)
     (list name)]
    [`(,(or 'define-struct 'struct) ,struct-name (,field-name ...))
     (define sn (struct->names tl))
     (list* (struct-names-constructor sn)
            (struct-names-predicate sn)
            (struct-names-selectors sn))]
    [_ '()]))

(module+ test

  (check-true
   (defines-and-references?
     `(define x 1)
     `(+ x 1)))

  (check-false
   (defines-and-references?
     `(+ x 1)
     `(define x 1)))

  (check-false
   (defines-and-references?
     `(define y 1)
     `(+ x 1)))

  (check-false
   (defines-and-references?
     `(+ y 1)
     `(+ x 1)))

  (check-false
   (defines-and-references?
     `(define f 1)
     `(λ (x) f)))

  (check-true
   (defines-and-references?
     `(define-id-with-ctc
        (-> integer? SORTED/C (and/c (non-empty-listof integer?) ne-sorted?))
        _insert
        insert
        bad-input
        bug)
     `insert))

  (check-true
   (defines-and-references?
     `(define ne-sorted? 5)
     `(define-id-with-ctc
        (-> integer? SORTED/C (and/c (non-empty-listof integer?) ne-sorted?))
        _insert
        insert
        bad-input
        bug)))

  (check-true
   (defines-and-references?
     `(define-struct posn (x y))
     `make-posn))
  (check-true
   (defines-and-references?
     `(define-struct posn (x y))
     `posn?))
  (check-true
   (defines-and-references?
     `(define-struct posn (x y))
     `posn-x))
  (check-true
   (defines-and-references?
     `(define-struct posn (x y))
     `posn-y))
  (check-false
   (defines-and-references?
     `(define x 1)
     `(define-struct posn (x y))))
  (check-false
   (defines-and-references?
     `(define x 1)
     `(struct posn (x y))))

  (check-equal?
   (build-neighbors
    (vector `(define f 1)))
   (make-hash))

  (check-equal?
   (do-the-top-sort
    (list
     `(define x 1)
     `(+ x 1)))
   (list
    `(define x 1)
    `(+ x 1)))

  (check-equal?
   (do-the-top-sort
    (list
     `(+ x 1)
     `(define x 1)))
   (list
    `(define x 1)
    `(+ x 1)))

  (check-equal?
   (do-the-top-sort
    (list
     `(define y 1)
     `(define x 1)))
   (list
     `(define y 1)
     `(define x 1)))

  (let ([eo
         (list
          `(define (_even? n) (if (> n 0) (_odd? (sub1 n)) #t))
          `(define (_odd? n) (if (> n n) (_even? (sub1 n)) #f))
          `(define even? (apply-ctc (-> number? boolean?) _even? bug bug even?))
          `(define odd? (apply-ctc (-> number? boolean?) _odd? bug bug odd?)))])
    (check-equal? (do-the-top-sort eo) eo)))
