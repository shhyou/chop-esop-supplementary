#lang concolic-hop/lang

(require (for-syntax syntax/parse
                     racket/sequence
                     syntax/stx
                     racket/base
                     racket/set)
         racket/stxparam
         racket/math
         concolic-hop/lib
         data/enumerate/lib
         "private/struct-helper.rkt"
         (prefix-in r: racket/base)
         (only-in concolic-hop/lang ->s or/s list-of list/s integer boolean)
         (only-in concolic-hop/store get-current-concrete-value)
         (only-in racket/base raise make-exn:fail current-continuation-marks))

#|

This code adds convertion wrappers around functions that:
 - turn n ary functions into curried / uncurried functions
 - turn thunks into functions that ignore their argument or always pass 0
 - map base values that are in `lump` positions according to the specified `define-lump`
 - map the ->i pattern used in zombie to a tuple of the methods
 - convert `cons/s` types into lists of length two
 - convert structs into lists of an appropriate length with an integer tag in the first
   element of the list. The tag is computed systematically from the name of the struct
   in order to facilitate `or/s` with different structs inside
 - it treats integer and boolean as identity conversions, for convenience

The types that are handled here have to match up with T/c definition in misc.rkt.
|#



(provide convert-it define-lump lump/s ->si cons/s
         string/s string-or-integer/s any/s none/s
         struct/s dont-care/s)

(define-syntax-parameter lump-p #f)


#|
There are three modes for the conversion of numbers controlled
by the value of the arithmetic-mode syntax parameter:

  - arithmetic is normal mode, so integer means integer and
    there aren't other kinds of numbers going around. The
    parameter is #f.

  - arithmetic is special in both sides mode, so numbers are
    actually lists of four integers (representing the numerator
    and denominator of the complex and real part of the number).
    The parameter is 'both.

  - arithmetic special on the inside (inside the engine-generated code).
    outside, complex numbers are just complex numbers but inside
    they are lists of length four as in the previous mode,
    so the conversion code has to translate back and forth. The
    parameter is 'inside

|#
;; (or/c #f 'both 'inside) -- as above
(define-syntax-parameter arithmetic-mode #f)
(define-for-syntax (not-arithmetic-mode?)
  (equal? (syntax-parameter-value #'arithmetic-mode) #f))
(define-for-syntax (both-arithmetic-mode?)
  (equal? (syntax-parameter-value #'arithmetic-mode) 'both))
(define-for-syntax (inside-arithmetic-mode?)
  (equal? (syntax-parameter-value #'arithmetic-mode) 'inside))

(begin-for-syntax
  (struct lump (in out))
  (define-syntax-class lump-element
    #:description "a number, string, or quoted symbol"
    (pattern n:number)
    (pattern s:string)
    (pattern 's:id)))

(define-syntax (define-lump stx)
  (syntax-parse stx
    [(_ l (in-val:lump-element out-val:lump-element) ...)
     #'(define-syntax l
         (lump #'(λ (x) (cond [(equal? out-val x) in-val] ... [else (lump-failure "in" x)]))
               #'(λ (x) (cond [(equal? in-val x) out-val] ... [else (lump-failure "out" x)]))))]))

(define (lump-failure which-way x)
  (define in? (equal? which-way "in"))
  (define str
    (format "lump: ~a conversion failure\n  value: ~e\n  value: ~e"
            (if in? "in to concolic" "out from concolic")
            x
            (get-current-concrete-value x)))
  (if in?
      (raise (make-exn:fail str (current-continuation-marks)))
      (abort-concolic-execution "~a" str)))

(define-syntax (convert-it stx)
  (define (lump-id->lump-p-binding lump-id)
    (define lump-code (syntax-local-value lump-id (λ () #f)))
    (unless (lump? lump-code)
      (raise-syntax-error 'convert-it
                          "expected a variable bound by `define-lump`"
                          stx
                          lump-id))
    lump-code)

  (define-splicing-syntax-class arithmetic-coercion
    #:attributes (coercion-value)
    (pattern (~seq) #:attr coercion-value #f)
    (pattern (~seq #:arithmetic-coercion-both) #:attr coercion-value 'both)
    (pattern (~seq #:arithmetic-coercion-inside) #:attr coercion-value 'inside))

  (syntax-parse stx
    [(_ val type lump-id:id ac:arithmetic-coercion)
     (define lump-code (syntax-local-value #'lump-id (λ () #f)))
     (unless (lump? lump-code)
       (raise-syntax-error 'convert-it
                           "expected a variable bound by `define-lump`"
                           stx
                           #'lump-id))
     #`(syntax-parameterize ([arithmetic-mode '#,(attribute ac.coercion-value)]
                             [lump-p #,(lump-id->lump-p-binding #'lump-id)])
         (let ([v val])
           (in/out v type out)))]
    [(_ val type ac:arithmetic-coercion)
     #`(syntax-parameterize ([arithmetic-mode '#,(attribute ac.coercion-value)])
         (let ([v val])
           (in/out v type out)))]))

(define-syntax (lump/s stx)
  (raise-syntax-error 'lump/s "used outside of convert-it" stx))
(define-syntax (->si stx)
  (raise-syntax-error '->si "used outside of convert-it" stx))
(define-syntax (cons/s stx)
  (raise-syntax-error 'cons/s "used outside of convert-it" stx))
(define-syntax (string/s stx)
  (raise-syntax-error 'string/s "used outside of convert-it" stx))
(define-syntax (string-or-integer/s stx)
  (raise-syntax-error 'string-or-integer/s "used outside of convert-it" stx))
(define-syntax (any/s stx)
  (raise-syntax-error 'any/s "used outside of convert-it" stx))
(define-syntax (none/s stx)
  (raise-syntax-error 'none/s "used outside of convert-it" stx))
(define-syntax (struct/s stx)
  (raise-syntax-error 'struct/s "used outside of convert-it" stx))
(define-syntax (dont-care/s stx)
  (raise-syntax-error 'dont-care/s "used outside of convert-it" stx))

;; this is a hack to make the expanded program use `make-rectangular`
;; to ease the implementation of inline-convert-it
(define (make-rectangular a b)
  (r:make-rectangular (get-current-concrete-value a)
                      (get-current-concrete-value b)))
(define real-part r:real-part)
(define imag-part r:imag-part)
(define numerator r:numerator)
(define denominator r:denominator)

(define-for-syntax (number->list-code val)
  #`(list (numerator (real-part #,val))
          (denominator (real-part #,val))
          (numerator (imag-part #,val))
          (denominator (imag-part #,val))))
(define-for-syntax (list->number-code val)
  #`(make-rectangular
     (/ (list-ref #,val 0)
        (if (zero? (list-ref #,val 1)) 1 (list-ref #,val 1)))
     (/ (list-ref #,val 2)
        (if (zero? (list-ref #,val 3)) 1 (list-ref #,val 3)))))

(define-syntax (in/out stx)
  (syntax-parse stx
    #:literals (->s or/s list-of list/s lump/s ->si cons/s struct/s dont-care/s
                    integer boolean string/s string-or-integer/s any/s none/s)
    ;; in means into the concolic-tester controlled space,
    ;; out means out from the concolic-tester-controlled space
    #:datum-literals (in out)
    [(_ val:id lump/s in)
     (define lump-code (syntax-parameter-value #'lump-p))
     #`(#,(lump-in lump-code) val)]
    [(_ val:id lump/s out)
     (define lump-code (syntax-parameter-value #'lump-p))
     #`(#,(lump-out lump-code) val)]

    [(_ val:id (cons/s hd-t tl-t) in)
     ;; these let*'s facilitate inline-convert-it
     #`(let* ([hd (car val)]
              [tl (cdr val)])
         (list (in/out hd hd-t in) (in/out tl tl-t in)))]
    [(_ val:id (cons/s hd-t tl-t) out)
     #`(let* ([fst (list-ref val 0)]
              [rst (list-ref val 1)])
         (cons (in/out fst hd-t out)
               (in/out rst tl-t out)))]

    ;; thunks on the outside that come in are treated as functions on the inside that ignore their input
    [(_ val:id (->s rng) in)
     #'(λ (x) (let ([res (val)]) (in/out res rng in)))]
    ;; thunks on the inside that go out are treated as functions that always get `0` as input
    [(_ val:id (->s rng) out)
     #'(λ () (let ([res (val 0)]) (in/out res rng out)))]

    [(_ val:id (->s dom rng) out)
     #'(λ (x) (let ([res (val (in/out x dom in))])
                (in/out res rng out)))]
    [(_ val:id (->s dom rng) in)
     #'(λ (x) (let ([res (val (in/out x dom out))])
                (in/out res rng in)))]

    [(_ val:id (->s dom1 dom2 ... rng) out)
     (with-syntax ([(d2-x ...) (generate-temporaries #'(dom2 ...))])
       #'(λ (d1-x d2-x ...)
           (let ([res (curry-app val (in/out d1-x dom1 in) (in/out d2-x dom2 in) ...)])
             (in/out res rng out))))]
    [(_ val:id (->s dom1 dom2 ... rng) in)
     (with-syntax ([(d2-x ...) (generate-temporaries #'(dom2 ...))])
       #'(curry-λ (d1-x d2-x ...)
                  (let ([res (val (in/out d1-x dom1 out) (in/out d2-x dom2 out) ...)])
                    (in/out res rng in))))]

    [(_ val:id (->si ([msg1:id (one-of/c1:id lits:expr ...)])
                  (res:id (msg2:id)
                          (xcond clauses ...)))
        mode)
     #:when (and (equal? (syntax-e #'xcond) 'cond)
                 (equal? (syntax-e #'one-of/c1) 'one-of/c)
                 (equal? (syntax-e #'msg1) (syntax-e #'msg2)))
     (define possibly-incomplete-clause-infos
       (filter
        values
        (for/list ([clause (in-syntax #'(clauses ...))])
          (syntax-parse clause
            [[xelse:id "error"]
             #:when (equal? (syntax-e #'xelse) 'else)
             #f]
            [[(xequal?:id msg3:id (xquote:id s2:id)) mth-t]
             #:when (and (equal? (syntax-e #'msg3) (syntax-e #'msg1))
                         (equal? (syntax-e #'xequal?) 'equal?))
             (vector (syntax-e #'s2) #'mth-t)]
            [[(xequal?:id msg3:id str:string) mth-t]
             #:when (and (equal? (syntax-e #'msg3) (syntax-e #'msg1))
                         (equal? (syntax-e #'xequal?) 'equal?))
             (vector (syntax-e #'str) #'mth-t)]
            [[xelse:id mth-t]
             #:when (equal? (syntax-e #'xelse) 'else)
             (vector #f #'mth-t)]))))

     (define all-msgs
       (for/set ([lit (in-syntax #'(lits ...))])
         (syntax-parse lit
           [(xquote s:id)
            #:when (equal? (syntax-e #'xquote) 'quote)
            (syntax-e #'s)]
           [s:str (syntax-e #'s)])))

     (define explicitly-responded-to-msgs
       (for/set ([clause-info (in-list possibly-incomplete-clause-infos)]
                 #:when (vector-ref clause-info 0))
         (vector-ref clause-info 0)))

     (define missing-msgs
       (set-subtract all-msgs explicitly-responded-to-msgs))

     (define clause-infos
       (case (set-count missing-msgs)
         [(0) possibly-incomplete-clause-infos]
         [(1) (for/list ([clause-info (in-list possibly-incomplete-clause-infos)])
                (cond
                  [(vector-ref clause-info 0) clause-info]
                  [else (vector (set-first missing-msgs)
                                (vector-ref clause-info 1))]))]
         [else (raise-syntax-error "there seem to be too many missing messages" stx)]))
     
     (define sorted-clause-infos
       (sort clause-infos string<? #:key (λ (x) (~s (vector-ref x 0)))))
     (with-syntax ([(sorted-id ...) (map (λ (x) (vector-ref x 0)) sorted-clause-infos)]
                   [(sorted-types ...) (map (λ (x) (vector-ref x 1)) sorted-clause-infos)])
       (syntax-parse #'mode
         #:datum-literals (in out)
         [out
          (with-syntax ([(n ...) (for/list ([n (in-list sorted-clause-infos)]
                                            [i (in-naturals)])
                                   i)])
            #'(λ (msg)
                (cond
                  [(equal? msg 'sorted-id)
                   (let ([v (list-ref val n)])
                     (in/out v sorted-types out))] ...
                  [else (msg-send-error msg '(sorted-id ...))])))]
         [in
          #'(list (let ([v (val 'sorted-id)])
                    (in/out v sorted-types in)) ...)]))]
    [(_ val:id (->si . more) mode)
     (raise-syntax-error 'convert-it "malformed ->si"
                         (stx-car (stx-cdr (stx-cdr stx))))]

    [(_ val:id (or/s) mode)
     (raise-syntax-error 'convert-it "expected at least two option in or/s" (stx-car (stx-cdr (stx-cdr stx))))]
    [(_ val:id (or/s _) mode)
     (raise-syntax-error 'convert-it "expected at least two option in or/s" (stx-car (stx-cdr (stx-cdr stx))))]
    [(_ val:id (or/s Ts ...) mode)
     (define list-T #f)
     (define arr-T #f)
     (define struct-Ts '())
     (define struct-ids '())
     (let loop ([Ts (syntax->list #'(Ts ...))])
       (unless (null? Ts)
         (syntax-parse (car Ts)
           #:literals (->s or/s list-of list/s ->si integer boolean struct/s any/s)
           [(or/s inner-Ts ...)
            (loop (syntax->list #'(inner-Ts ...)))]
           [(struct/s s inner-Ts ...)
            (get-relevant-struct-info 'convert-it
                                      (stx-car (stx-cdr (stx-cdr stx)))
                                      #'s
                                      #'(inner-Ts ...)) ;; call for syntax error checking
            (define matching
              (for/list ([old-s (in-list struct-ids)]
                         #:when (free-identifier=? old-s #'s))
                old-s))
            (unless (null? matching)
              (raise-syntax-error
               'convert-it
               "found two of the same struct in a single or/s"
               #f
               (car Ts)
               matching))
            (set! struct-Ts (cons (car Ts) struct-Ts))
            (set! struct-ids (cons #'s struct-ids))]
           [(->s T ...)
            (when arr-T
              (raise-syntax-error 'convert-it
                                  "found two arrows in a single or/s"
                                  #f
                                  arr-T (list (car Ts))))
            (set! arr-T (car Ts))]
           [(->si stuff ...)
            (when arr-T
              (raise-syntax-error 'convert-it
                                  "found two arrows in a single or/s"
                                  #f
                                  arr-T (list (car Ts))))
            (set! arr-T (car Ts))]
           [(list-of T ...)
            (when list-T
              (raise-syntax-error 'convert-it
                                  "found two lists in a single or/s"
                                  #f
                                  list-T (list (car Ts))))
            (set! list-T (car Ts))]
           [(list/s T ...)
            (when list-T
              (raise-syntax-error 'convert-it
                                  "found two lists in a single or/s"
                                  #f
                                  list-T (list (car Ts))))
            (set! list-T (car Ts))]
           [boolean (void)]
           [integer (void)]
           ;; any/s used to be here, but that seems bogus....
           [T
            (raise-syntax-error 'convert-it
                                (format "cannot cope with ~s in an or/s" (syntax->datum #'T))
                                (stx-car (stx-cdr (stx-cdr stx)))
                                #'T)])
         (loop (cdr Ts))))
     (when (and (pair? struct-Ts) list-T)
       (raise-syntax-error 'convert-it
                           "cannot cope with a struct and a list in the same or/s"
                           (stx-car (stx-cdr (stx-cdr stx)))))

     (define struct-clauses
       (for/list ([struct-T (in-list struct-Ts)]
                  [struct-id (in-list struct-ids)])
         (define-values (constructor predicate selectors)
           (syntax-parse struct-T
             [(struct/s s inner-Ts ...)
              (get-relevant-struct-info 'convert-it
                                        (stx-car (stx-cdr (stx-cdr stx)))
                                        #'s
                                        #'(inner-Ts ...))]))
         (case (syntax-e #'mode)
           [(in)
            #`[(#,predicate val) (in/out val #,struct-T in)]]
           [(out)
            (define n (struct-name-to-natural struct-id))
            #`[(and (list? val)
                    (= #,(+ (length selectors) 1) (length val))
                    (= (car val) #,n))
               (in/out val #,struct-T out)]])))

     (define clauses
       (append
        struct-clauses
        (filter
         values
         (list (and list-T #`[(list? val) (in/out val #,list-T mode)])
               (and arr-T #`[(procedure? val) (in/out val #,arr-T mode)])))))
     #`(cond
         #,@clauses
         [else val])]
    [(_ val:id (list-of T) out)
     (if (nothing-to-convert? #'T)
         #'val
         #'(map (λ (x) (in/out x T out)) val))]
    [(_ val:id (list-of T) in)
     #'(map (λ (x) (in/out x T in)) val)]

    [(_ val:id (list/s integer integer integer integer) out)
     #:when (inside-arithmetic-mode?)
     (list->number-code #'val)]
    [(_ val:id (list/s integer integer integer integer) in)
     #:when (inside-arithmetic-mode?)
     (number->list-code #'val)]
    [(_ val:id (list/s T ...) mode)
     (with-syntax ([(n ...) (for/list ([i (in-naturals)]
                                       [x (in-syntax #'(T ...))])
                              i)])
       #'(list (let ([x (list-ref val n)])
                 (in/out x T mode)) ...))]
    [(_ val:id integer mode) #'val]
    [(_ val:id boolean mode) #'val]
    [(_ val:id string/s in)
     #'(string-in val)]
    [(_ val:id string/s out)
     #'(string-out val)]
    [(_ val:id string-or-integer/s in)
     #'(string-or-integer-in val)]
    [(_ val:id string-or-integer/s out)
     #'(string-or-integer-out val)]

    [(_ val:id any/s mode)
     #:when (or (both-arithmetic-mode?)
                (inside-arithmetic-mode?))
     (define (encoded-number-predicate? x)
       #`(and (list? #,x)
              (= 4 (length #,x))
              (integer? (list-ref #,x 0))
              (integer? (list-ref #,x 1))
              (integer? (list-ref #,x 2))
              (integer? (list-ref #,x 3))))
     (syntax-parse #'mode
       #:datum-literals (in out)
       [out
        (cond
          [(inside-arithmetic-mode?)
           #`(cond
               [(procedure? val)
                (λ (y)
                  (val (if (number? y)
                           #,(number->list-code #'y)
                           #,(number->list-code 0))))]
               [(list? val)
                #,(list->number-code #'val)]
               [else val])]
          [(both-arithmetic-mode?)
           #`(cond
               [(procedure? val)
                (λ (y)
                  (val (if #,(encoded-number-predicate? #'y)
                           y
                           #,(number->list-code 0))))]
               [else val])])]
       [in
         (cond
          [(inside-arithmetic-mode?)
           #`(cond
               [(procedure? val)
                (if (procedure-arity-includes? val 1)
                    (λ (y)
                      (let ([res (val #,(list->number-code #'y))])
                        (if (number? res)
                            #,(number->list-code #'res)
                            #,(number->list-code 0))))
                    #,(number->list-code 0))]
               [(number? val)
                #,(number->list-code #'val)]
               [(boolean? val) val]
               [else #,(number->list-code 0)])]
          [(both-arithmetic-mode?)
           #`(cond
               [(procedure? val)
                (if (procedure-arity-includes? val 1)
                    (λ (y)
                      (let ([res (val y)])
                        (if #,(encoded-number-predicate? #'res)
                            res
                            #,(number->list-code 0))))
                    #,(number->list-code 0))]
               [(list? val)
                (if #,(encoded-number-predicate? #'val)
                    val
                    #,(number->list-code 0))]
               [(boolean? val) val]
               [else #,(number->list-code 0)])])])]

    [(_ val:id any/s mode)
     #:when (not-arithmetic-mode?)
     (syntax-parse #'mode
       #:datum-literals (in out)
       [in
        #'(cond
            [(list? val) (list #false (map to-integer val))]
            [(pair? val) (list #true (improper-list->proper-list val))]
            [(integer? val) val]
            [(boolean? val) val]
            [(procedure? val)
             (if (procedure-arity-includes? val 1)
                 (λ (x) (to-integer (val x)))
                 0)]
            [else 0])]
       [out
        #'(cond
            [(pair? val)
             (let* ([val-hd (car val)]
                    [val-tl (cdr val)])
               (if (pair? val-tl)
                   (let ([val-hd-tl (car val-tl)])
                     (if val-hd
                         (proper-list->improper-list val-hd-tl)
                         val-hd-tl))
                   val))]
            [(procedure? val)
             (λ (x) (val (if (integer? x) x 0)))]
            [else val])])]

    [(_ val:id none/s mode)
     #'val]
    [(_ val:id dont-care/s in)
     (raise-syntax-error
      'convert-it
      "dont-care/s cannot go in"
      (stx-car (stx-cdr (stx-cdr stx))))]
    [(_ val:id dont-care/s out) #'val]

    [(_ val:id (struct/s s:id T ...) in)
     (define-values (constructor predicate selectors)
       (get-relevant-struct-info 'convert-it
                                 (stx-car (stx-cdr (stx-cdr stx)))
                                 #'s
                                 #'(T ...)))
     (with-syntax ([(sel ...) selectors])
       #`(list #,(struct-name-to-natural #'s)
               (let ([x (sel val)]) (in/out x T in)) ...))]

    [(_ val:id (struct/s s:id T ...) out)
     (define-values (constructor predicate selectors)
       (get-relevant-struct-info 'convert-it
                                 (stx-car (stx-cdr (stx-cdr stx)))
                                 #'s
                                 #'(T ...)))
     (with-syntax ([(i ...) (for/list ([_ (in-list selectors)]
                                       [i (in-naturals 1)])
                              i)])
       #`(#,constructor (let ([x (list-ref val i)]) (in/out x T out)) ...))]

    [(_  val:id the-type mode)
     (raise-syntax-error 'convert-it "unknown type" #'the-type)]))

(define-for-syntax (struct-name-to-natural id)
  (+ 99900000000000
     (for/sum ([b (in-bytes (string->bytes/utf-8 (symbol->string (syntax-e id))))]
               [i (in-naturals)])
       (* b (expt 256 i)))))

(define-for-syntax (nothing-to-convert? T)
  (let loop ([T T])
    (syntax-parse T
      #:literals (->s or/s list-of list/s lump/s ->si cons/s integer boolean string/s string-or-integer/s any/s
                      dont-care/s)
      [integer (not-arithmetic-mode?)]
      [boolean #t]
      [dont-care/s #t]
      [(list-of T) (loop #'T)]
      [_ #f])))

(define (improper-list->proper-list l)
  (cond
    [(pair? l)
     (define hd (car l))
     (cons (if (integer? hd) hd 0)
           (improper-list->proper-list (cdr l)))]
    [else (list (if (integer? l) l 0))]))
(define (proper-list->improper-list l)
  ;; we know the elements of this list are all integers
  (cond
    [(pair? l)
     (define hd (car l))
     (if (null? (cdr l))
         hd
         (cons hd (proper-list->improper-list (cdr l))))]
    [else l]))
(define (to-integer n) (if (integer? n) n 0))

(define (string-in val)
  (if (string? (get-current-concrete-value val))
      (to-nat string/e (get-current-concrete-value val))
      val))
(define (string-out val)
  (if (natural? (get-current-concrete-value val))
      (from-nat string/e (get-current-concrete-value val))
      val))
(define (string-or-integer-in val)
  (if (or (string? (get-current-concrete-value val))
          (integer? (get-current-concrete-value val)))
      (to-nat (or/e string/e integer/e) (get-current-concrete-value val))
      val))
(define (string-or-integer-out val)
  (if (natural? (get-current-concrete-value val))
      (from-nat (or/e string/e integer/e) (get-current-concrete-value val))
      val))
(module+ help-inline-conver-it
  (provide string-in string-out string-or-integer-in string-or-integer-out))

(define-syntax (curry-λ stx)
  (syntax-parse stx
    [(_ (x) e) #'(λ (x) e)]
    [(_ (x y ...) e) #'(λ (x) (curry-λ (y ...) e))]))

(define-syntax (curry-app stx)
  (syntax-parse stx
    [(_ f x) #'(f x)]
    [(_ f x y ...) #'(curry-app (f x) y ...)]))

(define (msg-send-error msg sorted-ids)
  (raise (make-exn:fail (format "msg-send: unknown message ~s; expected one of ~s"
                                msg sorted-ids)
                        (current-continuation-marks))))

(module+ test
  (provide in/out arithmetic-mode
           proper-list->improper-list
           improper-list->proper-list))
