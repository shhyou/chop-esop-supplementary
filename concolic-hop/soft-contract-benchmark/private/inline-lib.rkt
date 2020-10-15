#lang racket
(provide
 (struct-out no-match)
 simplifications
 predicate-function?
 freshen with-freshening
 next-var
 check-for-prefix
 inline-env/c
 predicates
 fact-subject?
 fact?
 (contract-out
  [has? (-> symbol? any/c boolean?)]
  [new-env (-> inline-env/c)]
  [add-fact
   (-> inline-env/c
       fact?
       boolean?
       inline-env/c)]
  [fact-must-be?
   (-> inline-env/c fact? boolean?)]
  [fact-cannot-be?
   (-> inline-env/c fact? boolean?)]
  [pf-subsumes? (-> p/¬p/c p/¬p/c boolean?)]
  [current-env (parameter/c inline-env/c)]))
(require (for-syntax syntax/parse))
(module+ test (require rackunit))

(define (predicate-function? s) (set-member? predicates s))
(define p/¬p/c (or/c predicate-function? (list/c '¬ predicate-function?)))

(define (fact-subject? x)
  (let loop ([x x])
    (match x
      [(? symbol?) #t]
      [`(#%app car ,x) (loop x)]
      [`(#%app cdr ,x) (loop x)]
      [_ #f])))

(define (fact? x)
  (let loop ([x x])
    (match x
      [`(#%app ,(? predicate-function?) ,subject)
       (fact-subject? subject)]
      [`(#%app procedure-arity-includes? ,subject ,(? natural?))
       (fact-subject? subject)]
      [_ #f])))

(struct info (must cannot) #:transparent)
(define know-nothing (info (set) (set)))

(define inline-env/c
  (hash/c fact-subject?
          (struct/c info
                    (set/c (or/c predicate-function? ;; predicates that hold on the subject
                                 natural?))          ;; arity of the procedure that is the subject
                    (set/c (or/c predicate-function? ;; predicates that failed on the subject
                                 natural?)))))       ;; arity the subject cannot be

(define predicates
  (set 'boolean? 'procedure? 'integer? 'real? 'number? 'list? 'pair? 'null?))
(define (subset-of-the-predicates? s)
  (subset? s predicates))

(define (predicate->must-implied p?)
  (-> predicate-function? subset-of-the-predicates?)
  (set-union
   (set p?)
   (match p?
     [`boolean?       (set)]
     [`procedure?     (set)]
     [`integer?       (set 'real? 'number?)]
     [`real?          (set 'number?)]
     [`number?        (set)]
     [`list?          (set)]
     [`pair?          (set)]
     [`null?          (set 'list?)])))

(define (predicate->cannot-implied p?)
  (-> predicate-function? subset-of-the-predicates?)
  (set-union
   (set p?)
   (match p?
     [`boolean?       (set)]
     [`procedure?     (set)]
     [`integer?       (set)]
     [`real?          (set 'integer?)]
     [`number?        (set 'integer? 'real?)]
     [`list?          (set 'null?)]
     [`pair?          (set)]
     [`null?          (set)])))

;; if we know that some variable is `p?`,
;; what is the complete set of other predicates
;; it might (or must) also be?
(define/contract (might-also-be p?)
  (-> predicate-function? subset-of-the-predicates?)
  (match p?
    [`boolean?       (set)]
    [`procedure?     (set)]
    [`integer?       (set 'real? 'number?)]
    [`real?          (set 'integer? 'number?)]
    [`number?        (set 'integer? 'real?)]
    [`list?          (set 'null? 'pair?)]
    [`pair?          (set 'list?)]
    [`null?          (set 'list?)]))

;; if we know something must be `p?` then these are
;; the predicates that it absolutely cannot be
(define/contract (must-incompatible p?)
  (-> predicate-function? subset-of-the-predicates?)
  (set-subtract
   (set-subtract predicates
                 (set p?))
   (might-also-be p?)))
(module+ test
  (check-true (set-member? (must-incompatible 'boolean?)
                           'integer?))
  (check-true (set-member? (must-incompatible 'boolean?)
                           'procedure?))
  (check-true (set-member? (must-incompatible 'integer?)
                           'procedure?))
  (check-false (set-member? (must-incompatible 'integer?)
                            'real?)))

(define (new-env) (hash))
(define (add-fact env fact true?)
  (define-values (set-element subject) (fact->set-element+subject fact))
  (cond
    [(and (supported-subject? env subject)
          (supported-fact? env fact))
     (define previous-info (or (hash-ref env subject #f) know-nothing))
     (define new-info
       (cond
         [true?
          (struct-copy info previous-info
                       [must (set-union (if (predicate-function? set-element)
                                            (predicate->must-implied set-element)
                                            (set set-element))
                                        (info-must previous-info))])]
         [else
          (struct-copy info previous-info
                       [cannot (set-union (if (predicate-function? set-element)
                                              (predicate->cannot-implied set-element)
                                              (set set-element))
                                          (info-cannot previous-info))])]))
     (hash-set env subject new-info)]
    [else env]))

;; determines if the part inside `subject`
;; is guaranteed to be a pair.
(define (supported-subject? env subject)
  (match subject
    [(? symbol?) #t]
    [`(#%app ,(or 'car 'cdr) ,subject-inside)
     (fact-must-be? env `(#%app pair? ,subject-inside))]))

;; ensures that when we have an arity of a procedure,
;; we already know we have a procedure.
(define (supported-fact? env fact)
  (match fact
    [`(#%app ,(? predicate-function? p?) ,subject) #t]
    [`(#%app procedure-arity-includes? ,subject ,(? natural?))
     (fact-must-be? env `(#%app procedure? ,subject))]))

(define current-env (make-parameter (hash)))
(define (fact-must-be? simplification-env fact)
  (define-values (set-element subject) (fact->set-element+subject fact))
  (match-define (info must cannot)
    (or (hash-ref simplification-env subject #f) know-nothing))
  (cond
    [(set-member? must set-element)
     #t]
    [(impossibility? (remove-naturals must)
                     (remove-naturals cannot))
     #t]
    [else
     #f]))

(define (fact-cannot-be? simplification-env fact)
  (define-values (set-element subject) (fact->set-element+subject fact))
  (match-define (info must cannot)
    (or (hash-ref simplification-env subject #f) know-nothing))
  (cond
    [(set-member? cannot set-element) #t]
    [(impossibility? (remove-naturals must)
                     (remove-naturals cannot))
     #t]
    [(predicate-function? set-element)
     (or (for/or ([must-p? (in-set must)])
           (set-member? (must-incompatible must-p?) set-element))
         (and (equal? set-element 'list?)
              (set-member? cannot 'pair?)
              (set-member? cannot 'null?)))]
    [else #f]))

(define (remove-naturals s)
  (for/set ([e (in-set s)]
            #:unless (natural? e))
    e))

(define (fact->set-element+subject fact)
  (match fact
    [`(#%app ,(? predicate-function? p?) ,subject)
     (values p? subject)]
    [`(#%app procedure-arity-includes? ,subject ,(? natural? n))
     (values n subject)]))

;; determines if either the `must` set is self-incomptable
;; (meaning we took two `if` that cannot both be taken without a set!)
;; could be improved by checking to see if the cannot
;; negates something in the must set
(define/contract (impossibility? must cannot)
  (-> subset-of-the-predicates? subset-of-the-predicates? boolean?)
  (for/or ([must-p? (in-set must)])
    (for/or ([incompatible-p? (in-set (must-incompatible must-p?))])
      (set-member? must incompatible-p?))))
(module+ test
  (check-true (impossibility? (set 'procedure? 'boolean?) (set)))
  (check-false (impossibility? (set 'integer? 'real?) (set)))
  (check-true (impossibility? (set 'integer? 'boolean?) (set)))
  (check-false (impossibility? (set 'pair? 'list?) (set)))
  (check-true (impossibility? (set 'pair? 'null?) (set))))

(module+ test
  (let ([simplification-env (add-fact (new-env) `(#%app boolean? x) #t)])
    (check-true (fact-must-be? simplification-env `(#%app boolean? x)))
    (check-false (fact-must-be? simplification-env `(#%app number? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app procedure? x))))

  (let ([simplification-env (add-fact (new-env) `(#%app real? x) #t)])
    (check-false (fact-must-be? simplification-env `(#%app boolean? x)))
    (check-true (fact-must-be? simplification-env `(#%app number? x)))
    (check-true (fact-must-be? simplification-env `(#%app real? x)))
    (check-false (fact-must-be? simplification-env `(#%app integer? x))))

  (let ([simplification-env (add-fact (new-env) `(#%app null? x) #t)])
    (check-true (fact-must-be? simplification-env `(#%app null? x)))
    (check-true (fact-must-be? simplification-env `(#%app list? x)))
    (check-false (fact-must-be? simplification-env `(#%app pair? x)))
    (check-false (fact-cannot-be? simplification-env `(#%app null? x)))
    (check-false (fact-cannot-be? simplification-env `(#%app list? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app pair? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app procedure? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app boolean? x))))

  (let ([simplification-env (add-fact (new-env) `(#%app boolean? x) #f)])
    (check-true (fact-cannot-be? simplification-env `(#%app boolean? x)))
    (check-false (fact-cannot-be? simplification-env `(#%app number? x))))

  (let ([simplification-env (add-fact (new-env) `(#%app real? x) #f)])
    (check-false (fact-cannot-be? simplification-env `(#%app boolean? x)))
    (check-false (fact-cannot-be? simplification-env `(#%app number? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app real? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app integer? x))))

  (let ([simplification-env (add-fact (new-env) `(#%app null? x) #f)])
    (check-true (fact-cannot-be? simplification-env `(#%app null? x)))
    (check-false (fact-cannot-be? simplification-env `(#%app list? x)))
    (check-false (fact-cannot-be? simplification-env `(#%app pair? x)))
    (check-false (fact-must-be? simplification-env `(#%app procedure? x)))
    (check-false (fact-must-be? simplification-env `(#%app boolean? x)))
    (check-false (fact-must-be? simplification-env `(#%app number? x))))

  (let ([simplification-env (add-fact
                             (add-fact
                              (new-env)
                              `(#%app null? x) #f)
                             `(#%app pair? x) #f)])
    (check-true (fact-cannot-be? simplification-env `(#%app list? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app null? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app pair? x)))
    (check-false (fact-must-be? simplification-env `(#%app procedure? x)))
    (check-false (fact-must-be? simplification-env `(#%app boolean? x)))
    (check-false (fact-must-be? simplification-env `(#%app number? x))))

  (let ([simplification-env (add-fact (add-fact (new-env) `(#%app procedure? x) #t) `(#%app real? x) #t)])
    (check-true (fact-must-be? simplification-env `(#%app procedure? x)))
    (check-true (fact-must-be? simplification-env `(#%app real? x)))
    (check-true (fact-must-be? simplification-env `(#%app boolean? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app procedure? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app real? x)))
    (check-true (fact-cannot-be? simplification-env `(#%app boolean? x))))

  (let ([simplification-env (add-fact (add-fact (new-env) `(#%app pair? x) #t)
                                      `(#%app integer? (#%app car x)) #t)])
    (check-true (fact-must-be? simplification-env `(#%app pair? x)))
    (check-false (fact-must-be? simplification-env `(#%app integer? x)))
    (check-false (fact-must-be? simplification-env `(#%app pair? (#%app car x))))
    (check-true (fact-must-be? simplification-env `(#%app integer? (#%app car x))))
    (check-false (fact-must-be? simplification-env `(#%app pair? (#%app cdr x))))
    (check-false (fact-must-be? simplification-env `(#%app integer? (#%app cdr x)))))

  (let ([simplification-env (add-fact (new-env) `(#%app procedure-arity-includes? x 1) #t)])
    (check-false (fact-must-be? simplification-env `(#%app procedure-arity-includes? x 1)))
    (check-false (fact-cannot-be? simplification-env `(#%app procedure-arity-includes? x 1))))
  (let ([simplification-env (add-fact
                             (add-fact
                              (new-env)
                              `(#%app procedure? x) #t)
                             `(#%app procedure-arity-includes? x 1) #t)])
    (check-true (fact-must-be? simplification-env `(#%app procedure-arity-includes? x 1)))
    (check-false (fact-cannot-be? simplification-env `(#%app procedure-arity-includes? x 1))))
  (let ([simplification-env (add-fact
                             (add-fact
                              (new-env)
                              `(#%app procedure? x) #t)
                             `(#%app procedure-arity-includes? x 1) #f)])
    (check-false (fact-must-be? simplification-env `(#%app procedure-arity-includes? x 1)))
    (check-true (fact-cannot-be? simplification-env `(#%app procedure-arity-includes? x 1)))))

(struct no-match ())
(define-syntax (simplifications stx)
  (syntax-parse stx
    [(_ simplification-env:id match-clause ...)
     (with-syntax ([(procs ...)
                    (for/list ([match-clause (in-list (syntax->list #'(match-clause ...)))])
                      (quasisyntax/loc match-clause
                        (λ (simplification-env x) (match x #,match-clause [_ (no-match)]))))])
       #`(list procs ...))]))

;; determines if p/¬p/c.1 holding has more information content than
;; p/¬p/c.2 holds (but is conserative, returning #f is safe if necc.)
(define (pf-subsumes? p/¬p/c.1 p/¬p/c.2)
  (match* (p/¬p/c.1 p/¬p/c.2)
    [(`procedure? `(¬ boolean?)) #t]
    [(`procedure? `(¬ integer?)) #t]
    [(`procedure? `(¬ pair?)) #t]
    [(`procedure? `(¬ null?)) #t]
    [(`procedure? `(¬ list?)) #t]
    [(`pair? `(¬ null?)) #t]
    [(`pair? `(¬ procedure?)) #t]
    [(`integer? `(¬ procedure?)) #t]
    [(`integer? `(¬ list?)) #t]
    [(`integer? `(¬ pair?)) #t]
    [(_ _) #f]))

(define the-prefix "✌")
(define freshening-variable-index (make-parameter #f))
(define (next-var)
  (define b (freshening-variable-index))
  (unless b (error 'next-var "freshening-variable-index not set"))
  (define var (string->symbol (~a the-prefix (unbox b))))
  (set-box! b (+ (unbox b) 1))
  var)
(define-syntax-rule
  (with-freshening e)
  (parameterize ([freshening-variable-index (box 0)]) e))
(define (check-for-prefix expr)
  (let loop ([expr expr])
    (cond
      [(pair? expr) (loop (car expr)) (loop (cdr expr))]
      [(symbol? expr)
       (when (regexp-match? (regexp (~a "^" the-prefix "[0-9]*$"))
                            (symbol->string expr))
         (error 'inline-convert-it
                "cannot cope with programs whose free variables start with ~a"
                the-prefix))])))

(define (freshen expr)
  (let loop ([expr expr]
             [env (hash)])
    (match expr
      [`(let ([,x ,e1]) ,e2)
       (define nx (next-var))
       `(let ([,nx ,(loop e1 env)])
          ,(loop e2 (hash-set env x nx)))]
      [`(λ (,xs ...) ,e)
       (define nxs
         (for/list ([x (in-list xs)])
           (next-var)))
       (define new-env
         (for/fold ([env env])
                   ([x (in-list xs)]
                    [nx (in-list nxs)])
           (hash-set env x nx)))
       `(λ (,@nxs) ,(loop e new-env))]
      [(? symbol?)
       (define remapped (hash-ref env expr #f))
       (cond
         [remapped remapped]
         [else expr])]
      [`(#%app ,f-e ,x-es ...)
       `(#%app ,(loop f-e env)
               ,@(for/list ([x-e (in-list x-es)])
                   (loop x-e env)))]
      [`(if ,tst ,thn ,els)
       `(if ,(loop tst env)
            ,(loop thn env)
            ,(loop els env))]
      [`(quote ,d) `(quote ,d)]
      [(? boolean? b) b]
      [(? number? n) n]
      [(? string? s) s])))
(module+ test
  (check-equal? (with-freshening (freshen `(#%app + x y))) `(#%app + x y))
  (check-equal? (with-freshening (freshen `(λ (x) (#%app + x y)))) `(λ (✌0) (#%app + ✌0 y)))
  (check-equal? (with-freshening (freshen `(let ([x x]) x))) `(let ([✌0 x]) ✌0))
  (check-equal? (with-freshening (freshen `(let ([x x]) (let ([x x]) x))))
                `(let ([✌0 x]) (let ([✌1 ✌0]) ✌1)))
  (check-equal? (with-freshening (freshen `'closed))
                `'closed))

(define (has? id exp)
  (let loop ([exp exp])
    (cond
      [(equal? id exp) #t]
      [(pair? exp) (or (loop (car exp)) (loop (cdr exp)))]
      [else #f])))