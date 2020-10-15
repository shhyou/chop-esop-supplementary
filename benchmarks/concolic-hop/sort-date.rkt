#lang concolic-hop/lang

(provide (all-defined-out))

(require concolic-hop/ctc
         concolic-hop/private/concretize)

(require (only-in racket/base [sort concrete-sort]))

(define (sort-manual-wrapping xs compare)
  (concrete-sort (immediate-concretize xs)
                 (λ (x y)
                   (immediate-concretize
                    (compare x y)))))

(define-id-with-ctc (-> concretize/c
                        (-> any/c any/c concretize/c)
                        any/c)
  concrete-sort sort-with-ctc bug no-blame)

(define (date< d1 d2)
  (or (< (car d1) (car d2))
      (< (cadr d1) (cadr d2))
      (< (caddr d1) (caddr d2))))

(define-concolic-test prop-sort-date
  #:inputs
  [dates (list-of
          (list/s (integer-range 1970 2021)
                  (integer-range 1 12)
                  (integer-range 1 31)))]
  #:prop
  (prop-not-false
   (cond
     [(< (length dates) 2) #t]
     [else
      (define sorted-dates (sort-manual-wrapping dates date<))
      (define date1 (car sorted-dates))
      (define date2 (cadr sorted-dates))
      (<= (car date1) (car date2))])))

(define-concolic-test prop-sort-ctc-date
  #:inputs
  [dates (list-of
          (list/s (integer-range 1970 2021)
                  (integer-range 1 12)
                  (integer-range 1 31)))]
  #:prop
  (prop-not-false
   (cond
     [(< (length dates) 2) #t]
     [else
      (define sorted-dates (sort-with-ctc dates date<))
      (define date1 (car sorted-dates))
      (define date2 (cadr sorted-dates))
      (<= (car date1) (car date2))])))

(module* test racket/base
  (require rackunit
           concolic-hop/lib
           (submod ".."))
  (check-not-false
   (concolic-test prop-sort-date
                  #:all? #f))
  (check-not-false
   (concolic-test prop-sort-ctc-date
                  #:all? #f))

  )

(module* main racket/base
  (require (submod ".." test))
  )
