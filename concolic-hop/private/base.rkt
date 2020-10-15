(module base "pre-base.rkt"

  (provide
   (except-out (all-from-out "pre-base.rkt")
               equal?)

   (except-out (all-defined-out)
               -equal?)

   (rename-out
    [-equal? equal?]))

  (define (-equal? v1 v2)
    (cond
      [(null? v1) (null? v2)]
      [(pair? v1) (and (pair? v2)
                       (-equal? (car v1) (car v2))
                       (-equal? (cdr v1) (cdr v2)))]
      [(boolean? v1) (and (boolean? v2) (equal? v1 v2))]
      ;; Erlang pattern matching treates integers and doubles as different values
      ;; '==' is the operator for numeric comparison
      [(integer? v1) (and (integer? v2) (equal? v1 v2))]
      [else (equal? v1 v2)]))

  (module reader syntax/module-reader
    concolic-hop/private/base))
