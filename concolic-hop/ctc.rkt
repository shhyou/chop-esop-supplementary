#lang concolic-hop/lang

(require (for-syntax syntax/parse racket/base
                     syntax/stx racket/struct-info)
         (only-in racket/base exn:fail
                  raise current-continuation-marks
                  object-name string-append)
         concolic-hop/lib
         (only-in concolic-hop/store
                  get-current-concrete-value)
         "private/complex-core.rkt"
         "private/struct-helper.rkt"
         "private/concretize.rkt")
(provide apply-ctc
         define-ctc
         ctc->pred
         provide-contract-out
         define-id-with-ctc)

;; pos,neg : (-> (-> any) (-> α α))
;; given an error-raising function (or one that just returns without raising an error)
;; return a projection. (If the function returns without raising an error, the projection
;; is equivalent to the identity function.)
(struct ctc (pos neg pred))

(define (apply-pos-proj a-ctc error- val)
  (((ctc-pos a-ctc) error-) val))

(define (apply-neg-proj a-ctc error- val)
  (((ctc-neg a-ctc) error-) val))

(define (ctc-swap a-ctc) (ctc (ctc-neg a-ctc) (ctc-pos a-ctc) (ctc-pred a-ctc)))

(begin-for-syntax
  (define-syntax-class blame-category
    (pattern x:id #:when (equal? (syntax-e #'x) 'bug))
    (pattern x:id #:when (equal? (syntax-e #'x) 'bad-input))
    (pattern x:id #:when (equal? (syntax-e #'x) 'no-blame))
    (pattern x:id #:when (equal? (syntax-e #'x) 'exn:fail))))

;; positive positions are considered "internal" errors (using exn:fail)
;; and negative positions are considered bugs in the program under test
(define-syntax (provide-contract-out stx)
  (syntax-parse stx
    [(_ pos:blame-category neg:blame-category (x:id ctc) ...)
     (with-syntax ([(exported-x ...) (generate-temporaries #'(x ...))])
       #'(begin
           (define exported-x (apply-ctc ctc x pos neg x)) ...
           (provide (rename-out [exported-x x] ...))))]))

(begin-for-syntax
  (struct redirect-struct (proc struct-info)
    #:property prop:procedure 0
    #:property prop:struct-info
    (λ (x)
      (redirect-struct-struct-info x))))
(define-syntax (define-id-with-ctc stx)
  (syntax-parse stx
    [(_ ctc orig-x:id new-x:id pos:blame-category neg:blame-category)
     (define lv
       (syntax-local-value #'orig-x (λ () #f)))
     (cond
       [(struct-info? lv)
        (define info (extract-struct-info lv))
        (define (wrap x)
          (if (identifier? x)
              #`#'#,x
              #f))
        (define info-as-code
          #`(list #,(wrap (list-ref info 0))
                  #,(wrap (list-ref info 1))
                  #,(wrap (list-ref info 2))
                  (list #,@(for/list ([id (in-list (list-ref info 3))])
                             (wrap id)))
                  (list #,@(for/list ([id (in-list (list-ref info 4))])
                             (wrap id)))
                  #,(wrap (list-ref info 5))))
        #`(begin
            (define id-with-contract (apply-ctc ctc orig-x pos neg new-x))
            (define-syntax new-x
              (redirect-struct
               (λ (x)
                 (syntax-parse x
                   [x:id #'id-with-contract]
                   [(_ args (... ...))
                    (with-syntax ([app (datum->syntax
                                        x
                                        '#%app)])
                      #'(app id-with-contract args (... ...)))]))
               #,info-as-code)))]
       [else
        #`(define new-x (apply-ctc ctc orig-x pos neg new-x))])]))

(define-syntax (apply-ctc stx)
  (syntax-parse stx
    [(_ ctc e pos:blame-category neg:blame-category name:id)
     #'(apply-ctc/proc (to-ctc () ctc) e 'pos 'neg 'name)]))

(define-syntax (ctc->pred stx)
  (syntax-parse stx
    [(_ ctc)
     #'(ctc-pred (to-ctc () ctc))]))

(begin-for-syntax
  (struct ctc-binding (trans id)
    #:property prop:procedure
    (struct-field-index trans))
  (define (ctc-binding-transformer stx)
    (raise-syntax-error #f
                        "misuse of a ctc bound identifier"
                        stx)))

(define-syntax (define-ctc stx)
  (syntax-parse stx
    [(_ c:id ctc)
     (with-syntax ([(c2) (generate-temporaries #'(c))])
       #'(begin
           (define c2 (to-ctc () ctc))
           (define-syntax c
             (ctc-binding ctc-binding-transformer #'c2))))]))

(define-syntax (to-ctc stx)
  (syntax-parse stx
    #:datum-literals (-> not/c and/c or/c >/c >=/c =/c listof non-empty-listof list/c cons/c any/c one-of/c false?
                         c:=/c none/c struct/c dont-care/c
                         recursive-contract
                         concretize/c)
    #:literals (λ)
    [(_ (dep:id ...) (-> dom ... rng))
     #'(ctc->i (list (to-ctc (dep ...) dom) ...) (λ ignored (to-ctc (dep ...) rng)))]
    [(_ (dep:id ...) (->i ([x dom] ...) [res (y ...) rng]))
     (define xs (syntax->list #'(x ...)))
     (define ys (syntax->list #'(y ...)))
     (unless (and (= (length xs) (length ys))
                  (for/and ([x (in-list xs)]
                            [y (in-list ys)])
                    (free-identifier=? x y)))
       (raise-syntax-error #f "expected the domain names to match the names depended on in the range"))
     #'(ctc->i (list (to-ctc (dep ...) dom) ...)
               (λ (y ...) (to-ctc/expr (dep ...) rng)))]
    [(_ (dep:id ...) false?)
     #'(ctc-flat (λ (x) (equal? x #f)))]
    [(_ (dep:id ...) x?:id)
     #:when (regexp-match #rx"[?]$" (symbol->string (syntax-e #'x?)))
     #'(ctc-flat x?)]
    [(_ (dep:id ...) s:string)
     #'(ctc-flat (λ (x) (equal? x s)))]
    [(_ (dep:id ...) (λ (x:id) e:expr))
     #'(ctc-flat (λ (x) e))]
    [(_ (dep:id ...) (and/c ctc ...))
     #'(ctc-and/c (to-ctc (dep ...) ctc) ...)]
    [(_ (dep:id ...) (or/c ctc ...))
     #'(ctc-or/c (to-ctc (dep ...) ctc) ...)]
    [(_ (dep:id ...) (not/c ctc))
     #'(ctc-not/c (to-ctc (dep ...) ctc))]
    [(_ (dep:id ...) (>/c e))
     #'(ctc->/c e)]
    [(_ (dep:id ...) (=/c e))
     #'(ctc-=/c e)]
    [(_ (dep:id ...) (c:=/c e))
     #'(ctc-c:=/c e)]
    [(_ (dep:id ...) (>=/c e))
     #'(ctc->=/c e)]
    [(_ (dep:id ...) (listof e))
     #'(ctc-listof/c (to-ctc (dep ...) e) #t)]
    [(_ (dep:id ...) (non-empty-listof e))
     #'(ctc-listof/c (to-ctc (dep ...) e) #f)]
    [(_ (dep:id ...) (list/c e ...))
     #'(ctc-list/c (to-ctc (dep ...) e) ...)]
    [(_ (dep:id ...) (cons/c e ...))
     #'(ctc-cons/c (to-ctc (dep ...) e) ...)]
    [(_ (dep:id ...) (one-of/c arg ...))
     (define args
       (for/list ([arg (in-list (syntax->list #'(arg ...)))])
         (syntax-parse arg
           ['x:id #''x]
           [s:str #'s]
           [n:number #'n])))
     #`(ctc-one-of/c #,@args)]
    [(_ (dep:id ...) any/c)
     #'ctc-any/c]
    [(_ (dep:id ...) dont-care/c)
     ;; the contract checking for dont-care/c is the
     ;; same as for any/c, ie don't do anything.
     #'ctc-any/c]
    [(_ (dep:id ...) none/c)
     #'ctc-none/c]
    [(_ (dep:id ...) (recursive-contract ref:id #:chaperone))
     #'(ctc-recursive (λ () (to-ctc (dep ...) ref)))]
    [(_ (dep:id ...) concretize/c)
     #'imp-concretize/c]
    [(_ (dep:id ...) ref:id)
     (define cb (syntax-local-value #'ref (λ () #f)))
     (cond
       [(ctc-binding? cb)
        (syntax-property (ctc-binding-id cb) 'disappeared-use (syntax-local-introduce #'ref))]
       [else
        (unless (for/or ([id (in-syntax #'(dep ...))])
                  (free-identifier=? #'ref id))
          (raise-syntax-error #f "reference to non-dep-bound identifier"
                              #'ref))
        #'ref])]
    [(_ (dep:id ...) (struct/c s:id e ...))
     (define-values (constructor predicate selectors)
       (get-relevant-struct-info 'ctc
                                 (stx-car (stx-cdr (stx-cdr stx)))
                                 #'s #'(e ...)))
     #`(ctc-struct/c 's
                     #,constructor #,predicate
                     (list #,@selectors)
                     (list (to-ctc (dep ...) e) ...))]
    [(_ (dep:id ...) e)
     (raise-syntax-error 'to-ctc "unknown contract" #'e)]))

(define-syntax (to-ctc/expr stx)
  (syntax-parse stx
    #:datum-literals (cond)
    [(_ (dep:id ...) (cond [q a] ...))
     #'(cond
         [q (to-ctc (dep ...) a)] ...)]
    [(_ (dep:id ...) e)
     #'(to-ctc (dep ...) e)]))

(define (apply-ctc/proc a-ctc value pos neg name)
  (define pos-proj ((ctc-pos a-ctc) (sym->raise-err pos name)))
  (define neg-proj ((ctc-neg a-ctc) (sym->raise-err neg name)))
  (neg-proj (pos-proj value)))

(define (sym->raise-err s name)
  (define raise-it
    (case s
      [(bug) error-bug]
      [(bad-input) error-bad-input]
      [(no-blame) void]
      [(exn:fail) raise-exn:fail]))
  (λ (s)
    (raise-it (format "~a: ~a" name s))))

(define (raise-exn:fail str)
  (raise (exn:fail str (current-continuation-marks))))

(define imp-concretize/c (ctc (λ (err) (λ (x) (immediate-concretize x)))
                              (λ (err) (λ (x) x))
                              (λ (x) #t)))

(define ctc-any/c (ctc (λ (err) (λ (x) x))
                       (λ (err) (λ (x) x))
                       (λ (x) #t)))
(define ctc-none/c
  (let ([proj
         (λ (err)
           (λ (x)
             (error-bad-input "none/c means that we give up on this input")))])
    (ctc proj proj (λ (x) #f))))

(define (ctc->i doms mk-rng)
  (define (mk-proc pos?)
    (λ (error-)
      (λ (f)
        (cond
          [(and (procedure? f) (procedure-arity-includes? f (length doms)))
           (define wrapped-f
             (λ args
               (cond
                 [(= (length args) (length doms))
                  (define contracted-arguments
                    (let loop ([args args]
                               [doms doms])
                      (cond
                        [(null? args) '()]
                        ;; this covers the case when we only have one
                        ;; projection and there is a blame we don't check
                        [(null? doms) '()]
                        [else
                         (cons (if pos?
                                   (apply-neg-proj (car doms) error- (car args))
                                   (apply-pos-proj (car doms) error- (car args)))
                               (loop (cdr args) (cdr doms)))])))
                  (define result (do-apply f contracted-arguments))
                  (define result-ctc (do-apply mk-rng contracted-arguments))
                  (if pos?
                      (apply-pos-proj result-ctc error- result)
                      (apply-neg-proj result-ctc error- result))]
                 [else
                  (begin
                    (unless pos?
                      (error- (string-append
                               (format
                                (string-append
                                 "->: contract violation (wrong number of arguments)\n"
                                 "  expected argument count: ~a\n"
                                 "  actual argument count: ~a")
                                (length doms)
                                (length args))
                               (let loop ([args args]
                                          [i 0])
                                 (cond
                                   [(null? args) ""]
                                   [else
                                    (define arg (car args))
                                    (string-append
                                     (format "\n  arg #~a: ~e\n  arg#~a: ~e"
                                             i arg
                                             i (get-current-concrete-value arg))
                                     (loop (cdr args) (+ i 1)))]))
                               (let loop ([ctcs doms]
                                          [i 0])
                                 (cond
                                   [(null? ctcs) ""]
                                   [else
                                    (define ctc (car ctcs))
                                    (string-append
                                     (format "\n  ctc #~a: ~e" i ctc)
                                     (loop (cdr ctcs) (+ i 1)))])))))
                    ;; this is a bad situation!
                    (if (< (length args) (length doms))
                        (do-apply f args)
                        (car "I don't know what to do here!!!")))])))
           (if (object-name f)
               (procedure-rename wrapped-f (object-name f))
               wrapped-f)]
          [else
           (begin
             (when pos?
               (error- "->: contract violation (wrong arity function)"))
             f)]))))

  (ctc (mk-proc #t) (mk-proc #f) #f))

(define (do-apply f args)
  (case (length args)
    [(0) (f)]
    [(1) (f (list-ref args 0))]
    [(2) (f (list-ref args 0) (list-ref args 1))]
    [(3) (f (list-ref args 0) (list-ref args 1) (list-ref args 2))]
    [(4) (f (list-ref args 0) (list-ref args 1) (list-ref args 2) (list-ref args 3))]
    [(7) (f (list-ref args 0) (list-ref args 1) (list-ref args 2) (list-ref args 3)
            (list-ref args 4) (list-ref args 5) (list-ref args 6))]
    [else
     (eprintf "ctc.rkt: ack, I wish I knew what `apply` was (~a arguments)\n" (length args))
     (car #f)]))

(define (ctc-listof/c a-ctc mt-ok?)
  (define (mk-proc pos?)
    (λ (error-)
      (λ (v)
        (cond
          [(and (list? v) (or mt-ok? (pair? v)))
           (let loop ([v v])
             (cond
               [(null? v) v]
               [else (cons (if pos?
                               (apply-pos-proj a-ctc error- (car v))
                               (apply-neg-proj a-ctc error- (car v)))
                           (loop (cdr v)))]))]
          [else
           (begin
             (when pos?
               (error- (format "expected a ~alist\n  value: ~e\n  value: ~e"
                               (if mt-ok? "" "non-empty ")
                               v
                               (get-current-concrete-value v))))
             v)]))))

  (ctc (mk-proc #t)
       (mk-proc #f)
       (and (ctc-pred a-ctc)
            (λ (x)
              (and (list? x)
                   (if mt-ok? #t (pair? x))
                   (let loop ([x x])
                     (cond
                       [(null? x) #t]
                       [else
                        (and ((ctc-pred a-ctc) (car x))
                             (loop (cdr x)))])))))))

(define (ctc-list/c . a-ctcs)
  (define (mk-proc pos?)
    (λ (error-)
      (λ (v)
        (cond
          [(list? v)
           (let loop ([v v]
                      [a-ctcs a-ctcs])
             (cond
               [(and (null? v) (null? a-ctcs)) v]
               [(and (pair? v) (pair? a-ctcs))
                (cons (if pos?
                          (apply-pos-proj (car a-ctcs) error- (car v))
                          (apply-neg-proj (car a-ctcs) error- (car v)))
                      (loop (cdr v)
                            (cdr a-ctcs)))]
               [else
                (when pos? (error- "expected a list with an appropriate number of elements"))
                v]))]
          [else
           (begin
             (when pos? (error- (format "expected a list\n  value: ~e\n  value: ~e"
                                        v
                                        (get-current-concrete-value v))))
             v)]))))

  (define all-flat?
    (let loop ([a-ctcs a-ctcs])
      (cond
        [(null? a-ctcs) #t]
        [else (and (ctc-pred (car a-ctcs))
                   (loop (cdr a-ctcs)))])))
  
  (ctc (mk-proc #t)
       (mk-proc #f)
       (and all-flat?
            (λ (x)
              (and (list? x)
                   (let loop ([a-ctcs a-ctcs]
                              [x x])
                     (cond
                       [(and (null? a-ctcs) (null? x)) #t]
                       [(and (pair? a-ctcs) (pair? x))
                        (and ((ctc-pred (car a-ctcs)) (car x))
                             (loop (cdr a-ctcs) (cdr x)))]
                       [else #f])))))))

(define (ctc-cons/c hd/c tl/c)
  (define (mk-proc pos?)
    (λ (error-)
      (λ (v)
        (cond
          [(pair? v)
           (cons (if pos?
                     (apply-pos-proj hd/c error- (car v))
                     (apply-neg-proj hd/c error- (car v)))
                 (if pos?
                     (apply-pos-proj tl/c error- (cdr v))
                     (apply-neg-proj tl/c error- (cdr v))))]
          [else
           (begin
             (when pos? (error- (format "expected a pair\n  value: ~e\n  value: ~e"
                                        v
                                        (get-current-concrete-value v))))
             v)]))))

  (ctc (mk-proc #t)
       (mk-proc #f)
       (and  (and (ctc-pred hd/c)
                  (ctc-pred tl/c)
                  (λ (x)
                    (and (pair? x)
                         ((ctc-pred hd/c) (car x))
                         ((ctc-pred tl/c) (cdr x))))))))

(define (ctc->/c n) (ctc-flat (let ([>/c-proc (λ (x) (and (real? x) (> x n)))]) >/c-proc)))
(define (ctc->=/c n) (ctc-flat (let ([>=/c-proc (λ (x) (and (real? x) (>= x n)))]) >=/c-proc)))
(define (ctc-=/c n)
  (unless (real? n)
    (raise (exn:fail
            (format "=/c: expected a real number\n  got: ~e" n)
            (current-continuation-marks))))
  (ctc-flat (let ([=/c-proc (λ (x) (and (real? x) (= x n)))]) =/c-proc)))
(define (ctc-c:=/c n)
  (cond
    [(c:real? n)
     (define (c:=/c-proc x)
       (equal? n x))
     (ctc-flat c:=/c-proc)]
    [else
     (raise (exn:fail
               (format "c:=/c: expected a real number\n  got: ~e" n)
               (current-continuation-marks)))]))

(define (ctc-one-of/c . args)
  (define (one-of? x)
    (let loop ([args args])
      (cond
        [(null? args) #f]
        [else
         (define fst (car args))
         (or (if (number? fst)
                 (and (number? x) (= fst x))
                 (equal? fst x))
             (loop (cdr args)))])))
  (ctc-flat one-of?))

(define (ctc-flat p?)
  (ctc (λ (error-) (λ (x)
                     (unless (p? x)
                       (error- (format "flat contract violation\n  contract: ~s\n  value: ~e\n  value: ~e"
                                       p?
                                       x
                                       (get-current-concrete-value x))))
                     x))
       (λ (error-) (λ (x) x))
       p?))

(define (ctc-and/c . ctcs)
  (define (mk-and/proc pos?)
    (λ (error-)
      (λ (x)
        (let loop ([x x][ctcs ctcs])
          (cond
            [(null? ctcs) x]
            [else (loop (if pos?
                            (apply-pos-proj (car ctcs) error- x)
                            (apply-neg-proj (car ctcs) error- x))
                        (cdr ctcs))])))))
  (define p?
    (let loop ([ctcs ctcs])
      (cond
        [(null? ctcs) (λ (x) #t)]
        [else
         (define p1? (ctc-pred (car ctcs)))
         (define p2? (loop (cdr ctcs)))
         (and p1? p2? (λ (x) (and (p1? x) (p2? x))))])))
  (ctc (mk-and/proc #t)
       (mk-and/proc #f)
       p?))

(define (ctc-or/c . ctcs)
  (define non-flats
    (filter (λ (x) (not (ctc-pred x))) ctcs))
  (define p?
    (let loop ([ctcs ctcs])
      (cond
        [(null? ctcs) (λ (x) #f)]
        [else
         (define p1? (ctc-pred (car ctcs)))
         (define p2? (loop (cdr ctcs)))
         (cond
           [p1? (λ (x) (or (p1? x) (p2? x)))]
           [else p2?])])))
  (cond
    [(null? non-flats)
     (ctc-flat p?)]
    [(null? (cdr non-flats))
     (define non-flat (car non-flats))
     (define (mk-and/proc pos?)
       (λ (error-)
         (λ (x)
           (cond
             [(p? x) x]
             [else
              (if pos?
                  (apply-pos-proj non-flat error- x)
                  (apply-neg-proj non-flat error- x))]))))
     (ctc (mk-and/proc #t)
          (mk-and/proc #f)
          #f)]
    [else
     (raise (exn:fail "or/c expected at most one non-flat contract" (current-continuation-marks)))]))

(define (ctc-not/c ctc)
  (define p? (ctc-pred ctc))
  (unless p?
    (raise (exn:fail "not/c expected a flat contract" (current-continuation-marks))))
  (ctc-flat (λ (x) (not (p? x)))))

(define (ctc-struct/c name constructor predicate? selectors sub-contracts)
  (define (mk-struct/c-proc pos? #:flat? flat?)
    (λ (error-)
      (λ (x)
        (cond
          [(predicate? x)
           (define arguments
             (let loop ([selectors selectors]
                        [sub-contracts sub-contracts])
               (cond
                 [(null? selectors) '()]
                 [else
                  (define sel (car selectors))
                  (define sub-ctc (car sub-contracts))
                  (define this-one
                    (if pos?
                        (apply-pos-proj sub-ctc error- (sel x))
                        (apply-neg-proj sub-ctc error- (sel x))))
                  (cons this-one (loop (cdr selectors) (cdr sub-contracts)))])))
           (if flat?
               x
               (do-apply constructor arguments))]
          [else
           (error- (format "struct/c contract violation\n  expected: ~a\n  value: ~e\n  value: ~e"
                           name
                           x
                           (get-current-concrete-value x)))]))))
  (cond
    [(andmap ctc-pred sub-contracts)
     (define (pred? x)
       (and (predicate? x)
            (let loop ([selectors selectors]
                       [sub-contracts sub-contracts])
              (cond
                [(null? selectors) #t]
                [else
                 (define sel (car selectors))
                 (define sub-ctc (car sub-contracts))
                 (and ((ctc-pred sub-ctc) (sel x))
                      (loop (cdr selectors)
                            (cdr sub-contracts)))]))))
     (ctc (mk-struct/c-proc #t #:flat? #t)
          (mk-struct/c-proc #f #:flat? #t)
          pred?)]
    [else
     (ctc (mk-struct/c-proc #t #:flat? #f)
          (mk-struct/c-proc #f #:flat? #f)
          #f)]))

(define (ctc-recursive thunk)
  (define forced? #f)
  (define forced #f)
  (define (mk-rec-proc pos?)
    (λ (error-)
      (λ (x)
        (unless forced?
          (set! forced? #t)
          (set! forced (thunk)))
        (if pos?
            (((ctc-pos forced) error-) x)
            (((ctc-neg forced) error-) x)))))
  (ctc (mk-rec-proc #t)
       (mk-rec-proc #f)
       #f))

;; when there is a bad input, we just give up on this attempt to find a bug
(define (error-bad-input message)
  (abort-concolic-execution "bad-input: ~a" message))
