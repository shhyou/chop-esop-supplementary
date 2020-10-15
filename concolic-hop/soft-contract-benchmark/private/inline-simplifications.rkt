#lang racket
(require "inline-lib.rkt"
         (submod concolic-hop/convert-it help-inline-conver-it))
(module+ test (require rackunit))
(provide shrinking-simplifications
         expanding-simpifications
         assert-simplifications-1
         assert-simplifications-2
         valuable?
         simplify-everywhere-once
         build-initial-environment)

(define shrinking-simplifications
  (simplifications
   simplification-env
   [`(#%app (λ (,xs ...) ,e1) ,e2s ...)
    #:when (= (length xs) (length e2s))
    `(let (,@(for/list ([x (in-list xs)]
                        [e2 (in-list e2s)])
               `[,x ,e2]))
       ,e1)]

   [`(let ([,x1 ,e]) ,x2)
    #:when (equal? x1 x2)
    e]

   ;; this relies on x2 not being free in e3 (and x1 =/= x2)
   ;; which should be preserved by the fact that no two binders
   ;; are the same and there are no variables starting with
   ;; `the-prefix` in the original program
   [`(let ([,x1 (let ([,x2 ,e2]) ,e1)]) ,e3)
    `(let ([,x2 ,e2]) (let ([,x1 ,e1]) ,e3))]

   [`(#%app list-ref (#%app cons ,hd ,tl) 0) hd]
   [`(#%app list-ref (#%app cons ,hd ,tl) ,(? (integer-in 1 #f) n))
    `(#%app list-ref ,tl ,(- n 1))]

   [`(#%app record-branch-point ,e) e]

   [`(if ,(? value? v) ,thn ,els) #:when (not (equal? v #f)) thn]
   [`(if #f ,thn ,els) els]
   [`(if ,(? (λ (x) (no-error? simplification-env x)))
         (#%app error ,(? string? s1))
         (#%app error ,(? string? s2)))
    #:when (equal? s1 s2)
    `(#%app error ,s1)]
   [`(if ,(? (λ (x) (no-error? simplification-env x)))
         ,(? (λ (x) (valuable? simplification-env x)) v1)
         ,(? (λ (x) (valuable? simplification-env x)) v2))
    #:when (equal? v1 v2)
    v1]
   [`(#%app map (λ (,y1) ,y2) ,(? fact-subject? s))
    #:when (and (fact-must-be? simplification-env `(#%app list? ,s))
                (equal? y1 y2))
    s]
   [`(if (#%app procedure? ,(? symbol? x1)) (λ (,y1) (#%app ,x2 ,y2)) ,els)
    #:when (and (equal? x1 x2) (equal? y1 y2))
    `(if (#%app procedure? ,x1) ,x1 ,els)]

   [`(#%app map ,(? value? f) (#%app cons ,(? value? hd) ,(? value? tl)))
    `(#%app cons (#%app ,(freshen f) ,hd) (#%app map ,f ,tl))]
   [`(#%app map ,(? value? f) null)
    `null]
   [`(#%app map ,f (#%app map ,g ,e))
    #:when (and (unary-function-that-never-errors? simplification-env f)
                (unary-function-that-never-errors? simplification-env g))
    (define x (next-var))
    `(#%app map (λ (,x) (#%app ,f (#%app ,g ,x))) ,e)]
   [`(#%app ,(? predicate-function? p?) (#%app map ,f ,e))
    #:when (and (member p? '(null? pair?))
                (unary-function-that-never-errors? simplification-env f))
    `(#%app ,p? ,e)]

   [`(#%app length (#%app cons ,(? value? hd) ,(? value? tl)))
    `(#%app + 1 (#%app length ,tl))]
   [`(#%app length null)
    `0]
   [`(#%app car (#%app cons
                       ,(? (λ (x) (valuable? simplification-env x)) hd)
                       ,(? (λ (x) (valuable? simplification-env x)) tl)))
    hd]
   [`(#%app cdr (#%app cons
                       ,(? (λ (x) (valuable? simplification-env x)) hd)
                       ,(? (λ (x) (valuable? simplification-env x)) tl)))
    tl]
   [`(#%app car (#%app list
                       ,(? (λ (x) (valuable? simplification-env x)) hd)
                       ,(? (λ (x) (valuable? simplification-env x)) more) ...))
    hd]
   [`(#%app cdr (#%app list
                       ,(? (λ (x) (valuable? simplification-env x)) hd)
                       ,(? (λ (x) (valuable? simplification-env x)) more) ...))
    `(#%app list ,@more)]

   [`(#%app improper-list->proper-list (#%app cons ,(? value? hd) ,(? value? tl)))
    `(#%app cons ,(ensure-integer hd) (#%app improper-list->proper-list tl))]
   [`(#%app improper-list->proper-list ,(? value? arg))
    #:when (match arg
             ;; when the argument isn't a `cons`
             [`(#%cons ,hd ,tl) #f]
             [_ #t])
    `(#%app cons ,(ensure-integer arg) null)]
   [`(#%app proper-list->improper-list
            (#%app cons ,(? value? hd1) (#%app cons ,(? value? hd2) ,(? value? tl))))
    `(#%app cons ,(ensure-integer hd1)
            (#%app proper-list->improper-list
                   (#%app cons ,hd2 ,tl)))]
   [`(#%app proper-list->improper-list (#%app cons ,(? value? hd) null))
    (ensure-integer hd)]

   [`(#%app = ,(? number? n1) ,(? number? n2))
    (= n1 n2)]
   [`(#%app + ,(? number? n1) ,(? number? n2))
    (+ n1 n2)]
   [`(#%app / ,(? number? n1) ,(? (and/c number? (not/c zero?)) n2))
    (/ n1 n2)]

   [`(#%app ,(? predicate-function? p) ,(? value? v)) (δ p v)]
   [`(#%app zero? ,(? number? n))
    (zero? n)]
   [`(#%app list? ,e)
    #:when (and (not (value? e)) (is-list? simplification-env e))
    #t]
   [`(#%app procedure? ,e)
    #:when (and (not (value? e))
                (is-list? simplification-env e))
    #f]
   [`(#%app list? ,e)
    #:when (and (not (value? e)) (is-not-list? simplification-env e))
    #f]
   [`(#%app null? (#%app list ,e1 ,e2s ...))
    #:when (valuable? simplification-env `(#%app list ,e1 ,@e2s))
    #f]
   [`(#%app pair? (#%app list ,e1 ,e2s ...))
    #:when (valuable? simplification-env `(#%app list ,e1 ,@e2s))
    #t]
   [`(#%app ,(? predicate-function? p?) ,(? fact-subject? s))
    #:when (and (not (equal? p? 'list?))
                (fact-must-be? simplification-env `(#%app ,p? ,s)))
    #t]
   [`(#%app ,(? predicate-function? p?) ,(? fact-subject? s))
    #:when (and (not (equal? p? 'list?))
                (fact-cannot-be? simplification-env `(#%app ,p? ,s)))
    #f]

   [`(#%app procedure-arity-includes? ,(? fact-subject? s) ,(? natural? n))
    #:when (fact-must-be? simplification-env `(#%app procedure-arity-includes? ,s ,n))
    #t]
   [`(#%app procedure-arity-includes? ,(? fact-subject? s) ,(? natural? n))
    #:when (fact-cannot-be? simplification-env `(#%app procedure-arity-includes? ,s ,n))
    #f]

   [`(#%app string-out (#%app string-in ,e)) e]
   [`(#%app string-or-integer-out (#%app string-or-integer-in ,e)) e]
   [`(#%app string-or-integer-out ,(? natural? n))
    (string-or-integer-out n)]
   [`(#%app string-out ,(? natural? n))
    (string-out n)]

   [`(#%app equal? ,(? number? i1) ,(? number? i2)) (equal? i1 i2)]
   [`(#%app equal? ,e1 ,e2)
    #:when (and (valuable? simplification-env e1)
                (valuable? simplification-env e2)
                (different-constructors? e1 e2))
    #f]

   [`(#%app make-rectangular ,(? real? r1) ,(? real? r2))
    (make-rectangular r1 r2)]
   [`(#%app real-part ,(? number? c))
    (real-part c)]
   [`(#%app imag-part ,(? number? c))
    (imag-part c)]
   [`(#%app numerator ,(? rational? c))
    (numerator c)]
   [`(#%app denominator ,(? rational? c))
    (denominator c)]

   [`(#%app proper-list->improper-list (#%app improper-list->proper-list ,e))
    #:when (is-not-list? simplification-env e)
    e]

   ;; these aren't really like the others-- they are designed to translate
   ;; things to racket/base (so we don't have a dependency on convert-it)
   [`(#%app msg-send-error ,e '(,valid-msgs ...))
    `(#%app error "unknown message: ~s" ,e)]
   [`(#%app lump-failure ,(? string? s) ,e)
    `(#%app error 'lump ,(string-append s ": ~s") ,e)]
   ))

(define expanding-simpifications
  (simplifications
   simplification-env
   
   [`(#%app (if ,test ,thn ,els) ,args ...)
    ;; the condition isn't required for soundness,
    ;; but it avoids combinatorial blowup
    #:when (or (equal? thn `(#%app error "ASSERT_UNREACHABLE"))
               (equal? els `(#%app error "ASSERT_UNREACHABLE")))
    `(if ,test (#%app ,thn ,@(map freshen args)) (#%app ,els ,@args))]
   [`(#%app ,(? symbol? f) (if ,e1 ,e2 ,e3))
    `(if ,e1 (#%app ,f ,e2) (#%app ,f ,e3))]
   
   [`(if (if ,a ,b ,c) ,d ,e)
    `(if ,a (if ,b ,d ,e) (if ,c ,(freshen d) ,(freshen e)))]))

(define assert-simplifications-1
  (simplifications
   simplification-env

   [`(if ,e1 (#%app error "ASSERT_UNREACHABLE") ,e2)
    #:when (lost-no-information? e1 e2)
    `(let ([,(next-var) ,e1]) ,e2)]

   ;; a bit overly specialized rule!!
   [`(if (#%app ,(? predicate-function? p1) ,s1)
         (#%app error "ASSERT_UNREACHABLE")
         (if (#%app ,(? predicate-function? p2) ,s2)
             ,e1
             ,e2))
    #:when (and (equal? s1 s2)
                (pf-subsumes? p2 `(¬ ,p1)))
    `(if (#%app ,p2 ,s2)
         ,e1
         ,e2)]

   [`(if ,e1 ,e2 (#%app error "ASSERT_UNREACHABLE"))
    #:when (lost-no-information? e1 e2)
    `(let ([,(next-var) ,e1]) ,e2)]

   [`(let ([,x ,e]) (#%app error "ASSERT_UNREACHABLE"))
    #:when (valuable? simplification-env e)
    `(#%app error "ASSERT_UNREACHABLE")]

   [`(#%app ,(? (λ (x) (valuable? simplification-env x)) v) ...
            (#%app error "ASSERT_UNREACHABLE")
            ,es ...)
    `(#%app error "ASSERT_UNREACHABLE")]

   [`(if (#%app error "ASSERT_UNREACHABLE") ,e1 ,e2)
    `(#%app error "ASSERT_UNREACHABLE")]

   [`(let ([,(? symbol?) (#%app error "ASSERT_UNREACHABLE")]) ,body)
    `(#%app error "ASSERT_UNREACHABLE")]))

(define (lost-no-information? if-test if-arm)
  (match if-test
    [`(#%app ,(? predicate-function?) ,(? symbol? s))
     (not (has? s if-arm))]
    [else #t]))
(module+ test
  (check-true (lost-no-information? `(#%app procedure? x) `(+ 1 2)))
  (check-false (lost-no-information? `(#%app procedure? x) `(+ 1 x)))
  (check-true (lost-no-information? `#t `(+ 1 x))))

(define assert-simplifications-2
  (simplifications
   simplification-env
   [`(let ([,x ,e]) (#%app error "ASSERT_UNREACHABLE"))
    #:when (not (valuable? simplification-env e))
    e]))

(define (value? x)
  (let loop ([x x])
    (match x
      [`(λ (,x ...) ,e) #t]
      [`(#%app cons ,v1 ,v2) (and (loop v1) (loop v2))]
      [`(#%app list ,vs ...) (for/and ([v (in-list vs)]) (loop v))]
      [(? number?) #t]
      [(? boolean?) #t]
      [`null #t]
      [_ #f])))
(module+ test
  (check-equal? (value? `(λ (x) x)) #t)
  (check-equal? (value? `(#%app cons 1 2)) #t)
  (check-equal? (value? `(#%app cons (#%app (λ (x) x)) 2)) #f)
  (check-equal? (value? `x) #f))

(define (no-error? simplification-env x)
  (or (valuable? simplification-env x)
      (match x
        [`(#%app ,(? predicate-function? s) ,arg)
         (valuable? simplification-env arg)]
        [_ #f])))
(module+ test
  (check-true (no-error? (new-env) `(#%app boolean? x)))
  (check-false (no-error? (new-env) `(#%app unknown-function x))))

(define/contract (valuable? simplification-env x
                            #:for-subst? [for-subst? #f]
                            #:allow-lets? [allow-lets? #f])
  (->* (inline-env/c any/c)
       (#:for-subst? boolean? #:allow-lets? boolean?)
       boolean?)
  (let loop ([x x]
             [simplification-env simplification-env])
    (match x
      [`(λ (,x ...) ,e) #t]
      [`(#%app cons ,v1 ,v2) (and (loop v1 simplification-env) (loop v2 simplification-env))]
      [(? number?) #t]
      [(? boolean?) #t]
      [(? string?) #t]
      [(? symbol?) #t] ;; identifier
      [`null #t]
      [`(#%app ,(? predicate-function?) ,x) (loop x simplification-env)]
      [`(#%app equal? ,x ,y) (and (loop x simplification-env) (loop y simplification-env))]
      [`(#%app list ,args ...) (for/and ([arg (in-list args)])
                                 (loop arg simplification-env))]
      [`(#%app string-in ,x) (loop x simplification-env)]
      [`(#%app string-out ,x) (loop x simplification-env)]
      [`(#%app string-or-integer-in ,x) (loop x simplification-env)]
      [`(#%app string-or-integer-out ,x) (loop x simplification-env)]
      [`(#%app improper-list->proper-list ,x) (loop x simplification-env)]
      [`(#%app proper-list->improper-list ,x) (loop x simplification-env)]
      [`(#%app procedure-arity-includes? ,x ,y)
       (and (loop x simplification-env)
            (is-procedure? simplification-env x)
            (loop y simplification-env))]
      [`(if ,(? fact? f) ,thn ,els)
       (and (loop f simplification-env) ;; fact? might not be valuable
            (loop thn (add-fact simplification-env f #t))
            (loop els (add-fact simplification-env f #f)))]
      [`(if ,x ,y ,z)
       (and (loop x simplification-env) (loop y simplification-env) (loop z simplification-env))]
      [`(#%app map ,f ,e)
       #:when (unary-function-that-never-errors? simplification-env f)
       (is-list? simplification-env e)]
      [`(#%app numerator ,e) (is-rational? simplification-env e)]
      [`(#%app denominator ,e) (is-rational? simplification-env e)]
      [`(#%app car ,e) (is-pair? simplification-env e)]
      [`(#%app cdr ,e) (is-pair? simplification-env e)]
      [`(#%app error "ASSERT_UNREACHABLE") for-subst?]
      [`(let ([,x ,e1]) ,e2)
       #:when allow-lets?
       (and (loop e1 simplification-env)
            (loop e2 simplification-env))]
      [_ #f])))
(module+ test
  (check-equal? (valuable? (new-env) `(λ (x) x)) #t)
  (check-equal? (valuable? (new-env) `(#%app cons 1 2)) #t)
  (check-equal? (valuable? (new-env) `(#%app cons (#%app (λ (x) x)) 2)) #f)
  (check-equal? (valuable? (new-env) `x) #t)
  (check-true (valuable? (new-env) `(#%app procedure? ✌9)))
  (check-true (valuable? (new-env) `(#%app list? ✌0)))
  (check-true (valuable? (new-env)
                         `(if (#%app list? ✌0)
                              (#%app list #f ✌0)
                              (if (#%app pair? ✌0)
                                  (#%app list #t (#%app improper-list->proper-list ✌0))
                                  ✌0))))
  (check-true (valuable?
               (new-env)
               `(if (#%app list? ✌1)
                    (#%app list #f (#%app map to-integer ✌1))
                    (if (#%app pair? ✌1)
                        (#%app  list #t (#%app improper-list->proper-list ✌1))
                        (if (#%app integer? ✌1)
                            ✌1
                            (if (#%app boolean? ✌1)
                                ✌1
                                (if (#%app procedure? ✌1)
                                    (if (#%app procedure-arity-includes? ✌1 1)
                                        (λ (✌3) (#%app to-integer (#%app ✌1 ✌3)))
                                        0)
                                    0)))))))
  (check-true (valuable?
               (add-fact (new-env) `(#%app number? ✌2) #t)
               `(#%app list
                       (#%app numerator (#%app real-part ✌2))
                       (#%app denominator (#%app real-part ✌2))
                       (#%app numerator (#%app imag-part ✌2))
                       (#%app denominator (#%app imag-part ✌2)))))

  (check-true (valuable?
               (add-fact (new-env) `(#%app pair? ✌0) #t)
               `(#%app car ✌0)))

  (check-true (valuable?
               (new-env)
               `(if (#%app pair? ✌2)
                    (let ((✌3 (#%app cdr ✌2)))
                      1)
                    3)
               #:allow-lets? #t)))

(define/contract (ensure-integer n)
  (-> value? integer?)
  (if (integer? n) n 0))

(define/contract (δ p v)
  ;; this is restricted to `value?` so it can be total
  ;; there are other times we know how the predicate
  ;; tests will go that are just one-off rules
  (-> predicate-function? value? boolean?)
  (match* {p v}
    [{`boolean? (? boolean?)} #t]
    [{`procedure? `(λ (,x ...) ,e)} #t]
    [{`integer? (? integer?)} #t]
    [{`number? (? number?)} #t]
    [{`real? (? real?)} #t]
    [{`list? `(#%app cons ,hd ,tl)} (δ p tl)]
    [{`list? `(#%app list ,v ...)} #t]
    [{`list? `null} #t]
    [{`pair? `(#%app cons ,hd ,tl)} #t]
    [{`null? `null} #t]
    [{_ _} #f]))
(module+ test
  (check-true (δ 'list? '(#%app cons 1 (#%app cons 2 null))))
  (check-false (δ 'list? '(#%app cons 1 (#%app cons 2 3))))
  (check-true (δ 'pair? '(#%app cons 1 (#%app cons 2 null))))
  (check-false (δ 'pair? 'null))
  (check-false (δ 'procedure? '(#%app list #t #f))))

(define (unary-function-that-never-errors? simplification-env exp)
  (match exp
    [`(λ (,x) ,e) (valuable? simplification-env e #:allow-lets? #t)]
    [`to-integer #t]
    [_ #f]))
(module+ test
  (check-true
   (unary-function-that-never-errors?
    (new-env)
    `(λ (✌2)
       (if (#%app pair? ✌2)
           (let ((✌3 (#%app cdr ✌2)))
             1)
           3))))
  (check-true
   (unary-function-that-never-errors?
    (new-env)
    `(λ (✌2)
       (if (#%app pair? ✌2)
           (if (#%app pair? (#%app cdr ✌2))
               (let ((✌3 (#%app car (#%app cdr ✌2))))
                 (let ((✌4 (#%app cdr (#%app cdr ✌2))))
                   (if (#%app null? ✌4)
                       (if (#%app car ✌2) (#%app proper-list->improper-list ✌3) ✌3)
                       ✌2)))
               ✌2)
           (if (#%app procedure? ✌2)
               (λ (✌5) (if (#%app integer? ✌5) (#%app ✌2 ✌5) (#%app ✌2 0)))
               ✌2)))))
  (check-true
   (unary-function-that-never-errors?
    (new-env)
    `(λ (✌6)
       (if (#%app list? ✌6)
           (#%app list #f (#%app map to-integer ✌6))
           (if (#%app pair? ✌6)
               (#%app list #t (#%app improper-list->proper-list ✌6))
               (if (#%app integer? ✌6)
                   ✌6
                   (if (#%app boolean? ✌6)
                       ✌6
                       (if (#%app procedure? ✌6)
                           (if (#%app procedure-arity-includes? ✌6 1)
                               (λ (✌7) (#%app to-integer (#%app ✌6 ✌7)))
                               0)
                           0)))))))))

(define (is-list? simplification-env v)
  (let loop ([v v])
    (cond
      [(and (fact-subject? v)
            (fact-must-be? simplification-env `(#%app list? ,v)))
       #t]
      [else
       (match v
         [`(#%app list ,v ...) #t]
         [`(#%app cons ,hd ,tl) (loop tl)]
         [`(#%app map ,f ,e)
          #:when (unary-function-that-never-errors? simplification-env f)
          (loop e)]
         [_ #f])])))

(define (is-not-list? simplification-env v)
  (cond
    [(fact-subject? v) (fact-cannot-be? simplification-env `(#%app list? ,v))]
    [else #f]))

(define (is-number? simplification-env v)
  (match v
    [(? fact-subject? s) (fact-must-be? simplification-env `(#%app number? ,s))]
    [_ #f]))

(define (is-rational? simplification-env v)
  (let loop ([v v])
    (match v
      [(? fact-subject? s) (fact-must-be? simplification-env `(#%app real? ,s))]
      [`(#%app real-part ,e) (is-number? simplification-env e)]
      [`(#%app imag-part ,e) (is-number? simplification-env e)]
      [_ #f])))

(define (is-procedure? simplification-env v)
  (let loop ([v v])
    (match v
      [`(λ (,x ...) e) #t]
      [(? fact-subject? s) (fact-must-be? simplification-env `(#%app procedure? ,s))]
      [_ #f])))

(define (is-pair? simplification-env v)
  (match v
    [`(#%app cons ,hd ,tl)
     (and (valuable? simplification-env hd)
          (valuable? simplification-env tl))]
    [(? fact-subject? s) (fact-must-be? simplification-env `(#%app pair? ,s))]
    [_ #f]))

;; different-constructors? : sexp/c sexp/c -> boolean
;; #t means they are definitely different and #f means we don't know
(define (different-constructors? e1 e2)
  (define (get-constructor e)
    (match e
      [`(#%app list ,e ...) 'list]
      [(? number?) 'number]
      [else #f]))
  (define c1 (get-constructor e1))
  (define c2 (get-constructor e2))
  (and c1 c2 (not (equal? c1 c2))))



(define (apply-simplifications some-simplifications expr simplification-env)
  (for/fold ([expr expr])
            ([simplification (in-list some-simplifications)])
    (define next
      (simplification simplification-env expr))
    (cond
      [(no-match? next) expr]
      [else next])))

(define (simplify-everywhere-once some-simplifications expr #:contract [contract #f])
  (let loop ([expr expr]
             [env (build-initial-environment expr contract)])
    (define subs-rewritten
      (match expr
        [`(if ,(? fact? f) ,thn ,els)
         `(if ,(loop f env)
              ,(loop thn (add-fact env f #t))
              ,(loop els (add-fact env f #f)))]
        [(? list?)
         (for/list ([expr (in-list expr)])
           (loop expr env))]
        [else expr]))
    (apply-simplifications some-simplifications subs-rewritten
                           env)))

(module+ test
  (check-equal? (apply-simplifications
                 shrinking-simplifications
                 `(#%app boolean? (λ (✌5) (#%app error "ASSERT_UNREACHABLE")))
                 (new-env))
                #f
                (new-env))
  (check-equal? (apply-simplifications
                 shrinking-simplifications
                 `(if (#%app pair? ✌17)
                      (#%app error "ASSERT_UNREACHABLE")
                      (#%app error "ASSERT_UNREACHABLE"))
                 (new-env))
                `(#%app error "ASSERT_UNREACHABLE"))
  (check-equal? (apply-simplifications
                 shrinking-simplifications
                 `(if (#%app procedure? ✌2) (λ (✌5) (#%app ✌2 ✌5)) 37)
                 (new-env))
                `(if (#%app procedure? ✌2) ✌2 37))
  (check-equal? (apply-simplifications
                 shrinking-simplifications
                 `(#%app list? (#%app cons 0 (#%app cons 1 null)))
                 (new-env))
                #t)

  (check-equal? (apply-simplifications
                 shrinking-simplifications
                 `(#%app list? (#%app list #t (#%app improper-list->proper-list ✌0)))
                 (new-env))
                #t)

  (check-equal? (simplify-everywhere-once
                 shrinking-simplifications
                 `(if (#%app list? x)
                      (#%app list? x)
                      #f))
                `(if (#%app list? x)
                     #t
                     #f))

  (check-equal? (simplify-everywhere-once
                 shrinking-simplifications
                 `(if (#%app list? x) (#%app map (λ (y) y) x) 123))
                `(if (#%app list? x) x 123))

  (check-equal? (simplify-everywhere-once
                 shrinking-simplifications
                 `(if (#%app integer? x) (#%app list? x) 123))
                `(if (#%app integer? x) #f 123))
  (check-equal?
   (simplify-everywhere-once
    shrinking-simplifications
    `(if (#%app list? ✌0)
         (#%app list? (#%app list #f
                             (#%app map to-integer ✌0)))
         11))
   `(if (#%app list? ✌0)
        #t
        11))

  (check-equal?
   (simplify-everywhere-once
    shrinking-simplifications
    `(#%app procedure? (#%app list #f #t)))
   `#f)

  (check-equal?
   (simplify-everywhere-once
    shrinking-simplifications
    `(if (#%app list? ✌0)
         (if (#%app procedure? (#%app list #f (#%app map to-integer ✌0)))
             2 3)
         4))
   `(if (#%app list? ✌0)
        3
        4))

  (check-equal?
   (simplify-everywhere-once
    shrinking-simplifications
    `(if (#%app boolean? ✌0)
         (if (#%app procedure? ✌0)
             #t
             (#%app error "ASSERT_UNREACHABLE"))
         5))
   `(if (#%app boolean? ✌0)
        (#%app error "ASSERT_UNREACHABLE")
        5))

  (check-equal?
   (with-freshening
       (simplify-everywhere-once
        assert-simplifications-1
        (freshen
         `(if (#%app procedure? x)
              (if (#%app procedure-arity-includes? x 1)
                  #f
                  (#%app error "ASSERT_UNREACHABLE"))
              (#%app error "ASSERT_UNREACHABLE")))))
   `(if (#%app procedure? x)
        (let ([✌0 (#%app procedure-arity-includes? x 1)])
          #f)
        (#%app error "ASSERT_UNREACHABLE")))

  (check-equal?
   (with-freshening
       (simplify-everywhere-once
        assert-simplifications-1
        (freshen
         `(if (#%app boolean? x)
              (#%app error "ASSERT_UNREACHABLE")
              (if (#%app procedure? x)
                  (#%app to-integer (#%app x y))
                  (#%app error "ASSERT_UNREACHABLE"))))))
   `(if (#%app procedure? x)
        (#%app to-integer (#%app x y))
        (#%app error "ASSERT_UNREACHABLE")))

  (check-equal?
   (with-freshening
       (simplify-everywhere-once
        assert-simplifications-1
        (freshen
         `(if (#%app procedure? x2)
              (#%app error "ASSERT_UNREACHABLE")
              (if (#%app null? x2)
                  (#%app error "ASSERT_UNREACHABLE")
                  (if (#%app pair? x2)
                      (#%app list? x2)
                      (#%app error "ASSERT_UNREACHABLE")))))))
   `(if (#%app pair? x2)
        (#%app list? x2)
        (#%app error "ASSERT_UNREACHABLE")))

  (check-equal?
   (simplify-everywhere-once
    assert-simplifications-2
    `(λ (✌0)
       (let ((✌1 (#%app ✌0 0)))
         (#%app error "ASSERT_UNREACHABLE"))))
   `(λ (✌0)
      (#%app ✌0 0)))

  (check-equal?
   (simplify-everywhere-once
    shrinking-simplifications
    `(if (#%app list? ✌0)
         (if (#%app null? (#%app list #f (#%app map to-integer ✌0)))
             1
             2)
         3))
   `(if (#%app list? ✌0)
        2
        3))

  (check-equal?
   (simplify-everywhere-once
    shrinking-simplifications
    `(λ (x)
       (if (#%app integer? x)
           1
           0))
    #:contract `(-> integer? integer?))
   `(λ (x)
      1))
  
  )

(define (build-initial-environment expr contract)
  (let loop ([expr expr])
    (match expr
      [`(let ([,x ,e]) ,b) (loop b)]
      [`(λ (,(? symbol? xs) ...) ,e)
       (match contract
         [`(-> ,doms ... ,rng)
          #:when (= (length xs) (length doms))
          (for/fold ([env (new-env)])
                    ([x (in-list xs)]
                     [dom (in-list doms)])
            (define predicate (ctc->predicate dom))
            (define first-order-env
              (if predicate
                  (add-fact env `(#%app ,predicate ,x) #t)
                  env))
            (define maybe-ho-env
              (match dom
                [`(-> ,dom-args ... ,dom-rng)
                 (let loop ([expr expr])
                   (match expr
                     [`(let ([,(? symbol? let-x) (#%app ,(? symbol? f) ,arg-exps ...)]) ,body)
                      #:when (and (equal? f x)
                                  (= (length arg-exps) (length dom-args)))
                      (define dom-rng-pred (ctc->predicate dom-rng))
                      (if dom-rng-pred
                          (add-fact first-order-env `(#%app ,dom-rng-pred ,let-x) #t)
                          first-order-env)]
                     [(? list?) (for/or ([e (in-list expr)])
                                  (loop e))]
                     [_ #f]))]
                [_ #f]))
            (or maybe-ho-env first-order-env))]
         [_ (new-env)])]
      [_ (new-env)])))

(define (ctc->predicate ctc)
  (cond
    [(set-member? predicates ctc) ctc]
    [else
     (match ctc
       [`(-> ,_ ...) `procedure?]
       [`(cons/c ,_ ,_) `pair?]
       [`(listof ,_) `list?]
       [`(list/c ,_ ...) `list?]
       [`(non-empty-listof ,_) `list?]
       [_ #f])]))
