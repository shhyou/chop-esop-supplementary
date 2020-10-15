#lang s-exp "base.rkt"

(provide
 empty
 length
 append
 apply-append
 map
 foldr
 foldl
 filter
 member
 empty?
 cons?
 )

(define empty
  null)

(define empty?
  (procedure-rename null? 'empty?))

(define cons?
  (procedure-rename pair? 'cons?))

(define (length xs)
  (if (null? xs)
      0
      (+ 1 (length (cdr xs)))))

(define append
  (rosette:case-lambda
   [() '()]
   [(ys) ys]
   [(xs . yss)
    (if (null? xs)
        (rosette:apply append yss)
        (cons (car xs) (rosette:apply append (cdr xs) yss)))]))

(define (apply-append xss)
  (if (null? xss)
      '()
      (append (car xss) (apply-append (cdr xss)))))

(define (map f xs)
  (if (null? xs)
      '()
      (cons (f (car xs)) (map f (cdr xs)))))

(define (foldr f z xs)
  (if (null? xs)
      z
      (f (car xs) (foldr f z (cdr xs)))))

(define (foldl f z xs)
  (if (null? xs)
      z
      (foldl f (f (car xs) z) (cdr xs))))

(define (filter p xs)
  (if (null? xs)
      '()
      (if (p (car xs))
          (cons (car xs) (filter p (cdr xs)))
          (filter p (cdr xs)))))

(define (member v lst [is-equal? equal?])
  (if (null? lst)
      #f
      (if (is-equal? v (car lst))
          lst
          (member v (cdr lst) is-equal?))))

(module* test racket/base
  (require (submod "..")
           rackunit)
  (check-equal? (map number->string '(5 0 2 16)) '("5" "0" "2" "16"))
  (check-equal? (append '(1 2 3) '(4) '(5 6) '(7 8 9 A)) '(1 2 3 4 5 6 7 8 9 A))
  (check-equal? (apply-append '((1 2 3) (4) (5 6) (7 8 9 A))) '(1 2 3 4 5 6 7 8 9 A))
  (check-equal? (foldr cons '() '(A B C D E)) '(A B C D E))
  (check-equal? (foldl cons '() '(A B C D E)) '(E D C B A))
  (check-equal? (filter even? '(1 2 3 4 5)) '(2 4))
  (check-false  (member 5 '(1 3 4)))
  ; This test fails because 5 is equal? to 5.0 in Rosette, which is different from Racket
  ; (check-false  (member 5 '(1 3 5.0 4)))
  (check-equal? (member 5 '(1 3 5.0 4) =) '(5.0 4))
  )
