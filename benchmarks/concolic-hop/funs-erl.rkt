#lang concolic-hop/lang

(require (only-in concolic-hop/store
                  get-current-concrete-value)
         (only-in racket/base
                  define-logger))

#|



Translation of CutEr's ftest/src/funs.erl.


Syntax of input specifications:

- (->s T_1 T_2):            The input should be a function from T_1 to T_2
- (or/s T_1 T_2 ...):       The input should be one of T_1, T_2 ...
- (list-of T):              The input should be a list of T
- (list/s T_1 T_2 ... T_n): The input should be a list of length n where the i-th
                            element is a T_i. This is conceptually the same as tuples.


Other syntactic forms:

- error-bug:          This function raises a special exception with message "bug."
- prop-not-error-bug: This function asserts that running its argument should not produce
                      the special exception error-bug. If error-bug is ever raised, the
                      test fails.


The programs are translated with these changes applied:

1. We implement Erlang's case-of form using Racket's generic equality
   test function, equal?.

2. We replace each generic specification by a more specific one.

Substitutes for the generic function(), tuple() and any() specs:

  * function() is replaced by the equivalent of fun((domain) -> range)
    with some appropriate domain and range specification.

  * tuple() in f13a is replaced by {integer()} | {integer(),integer()} | ... |
    {integer(),integer(),integer(),integer(),integer()}.

  * any() is replaced by by actual type in the tests.

  * The type variable T in mf is instantiated to be integer().

3. The tests f5, f7, f91 and f92 are implemented as curried functions.

|#

;; -module(funs).
;; -export([f1/1, f2/3, f3/3, f41/3, f42/3, f5/4, f6/1, f7/2, f8/2,
;;          f91/3, f92/2, f10/1, f11/3, f12/1, f1ws/1, f2ws/3, f3ws/3,
;;          f5ws/4, f1hs/1, f13a/2, f13b/2, f14/2]).
;;
;; -spec f1(fun((integer()) -> integer())) -> ok.
;; f1(F) ->
;;   case F(3) of
;;     42 ->
;;       case F(10) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f1)

(define (f1 F)
  (if (equal? (F 3) 42)
      (if (equal? (F 10) 17)
          (error-bug)
          'ok)
      'ok))

(define-concolic-test prop-f1
  #:inputs
  [F (->s integer integer)]
  #:prop
  (prop-not-error-bug (λ () (f1 F))))

;; -spec f1ws(fun((integer()) -> 21..42)) -> ok.
;; f1ws(F) ->
;;   case F(3) of
;;     42 ->
;;       case F(10) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f1ws)

(define (f1ws F)
  (if (equal? (F 3) 42)
      (if (equal? (F 10) 17)
          (error-bug)
          'ok)
      'ok))

(define-concolic-test prop-f1ws
  #:inputs
  [F (->s integer (integer-range 21 42))]
  #:prop
  (prop-not-error-bug (λ () (f1ws F))))

;; -spec f1hs(fun((integer()) -> integer())) -> ok.
;; f1hs(F) ->
;;   Id = fun (X) -> X end,
;;   G = Id(F),
;;   case G(3) of
;;     42 ->
;;       case G(10) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f1hs)

(define (f1hs F)
  (define (Id X) X)
  (define G (Id F))
  (if (equal? (G 3) 42)
      (if (equal? (G 10) 17)
          (error-bug)
          'ok)
      'ok))

(define-concolic-test prop-f1hs
  #:inputs
  [F (->s integer integer)]
  #:prop
  (prop-not-error-bug (λ () (f1hs F))))

;; -spec f2(fun((integer()) -> integer()), integer(), integer()) -> ok.
;; f2(F, X, Y) ->
;;   case F(X) of
;;     42 ->
;;       case F(Y) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f2)

(define (f2 F X Y)
  (if (equal? 42 (F X))
      (if (equal? 17 (F Y))
          (error-bug)
          'ok)
      'ok))

(define-concolic-test prop-f2
  #:inputs
  [F (->s integer integer)]
  [X integer]
  [Y integer]
  #:prop
  (prop-not-error-bug (λ () (f2 F X Y))))

;; -spec f2ws(fun((integer()) -> atom()), integer(), integer()) -> ok.
;; f2ws(F, X, Y) ->
;;   case F(X) of
;;     42 ->
;;       case F(Y) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f2ws)

(define (f2ws F X Y)
  (if (equal? 42 (F X))
      (if (equal? 17 (F Y))
          (error-bug)
          'ok)
      'ok))

;; Because we do not have atom, we replace
;; atom() by [integer()] which is also open in the same spirit.
(define-concolic-test prop-f2ws
  #:inputs
  [F (->s integer (list-of integer))]
  [X integer]
  [Y integer]
  #:prop
  (prop-not-error-bug (λ () (f2 F X Y))))

;; -spec f3(fun((integer()) -> integer()), integer(), integer()) -> ok.
;; f3(F, X, Y) ->
;;   case twice(F, X) of
;;     42 ->
;;       case twice(F, Y) of
;;        17 -> error(bug);
;;        _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;
;; twice(F, X) -> F(F(X)).
;;

(provide prop-f3)

(define (f3 F X Y)
  (if (equal? 42 (twice F X))
      (if (equal? 17 (twice F Y))
          (error-bug)
          'ok)
      'ok))

(define (twice F X) (F (F X)))

(define-concolic-test prop-f3
  #:inputs
  [F (->s integer integer)]
  [X integer]
  [Y integer]
  #:prop
  (prop-not-error-bug (λ () (f3 F X Y))))

;; -spec f3ws(fun((...) -> bitstring()), integer(), integer()) -> ok.
;; f3ws(F, X, Y) ->
;;   case twice(F, X) of
;;     42 ->
;;       case twice(F, Y) of
;;        17 -> error(bug);
;;        _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

;; Similar to f2ws, we could have replace bitstring() by [integer()].
;; However, because there is no bug in this program and
;; [integer()] is open, the concolic tester will search forver.

;; -spec f41(fun((integer()) -> any()), integer(), integer()) -> ok.
;; f41(F, X, Y) ->
;;   Z = F(X),
;;   case Z(Y) of
;;     42 -> error(bug);
;;     _ -> ok
;;   end.

(provide prop-f41)

(define (f41 F X Y)
  (define Z (F X))
  (if (equal? 42 (Z Y))
      (error-bug)
      'ok))

(define-concolic-test prop-f41
  #:inputs
  ;; We do not have any(). For f41, the only sensible return type
  ;; of F is an int -> int function. We specify the return
  ;; type explicitly to be int -> int.
  [F (->s integer (->s integer integer))]
  [X integer]
  [Y integer]
  #:prop
  (prop-not-error-bug (λ () (f41 F X Y))))

;;
;; -spec f42(fun((integer()) -> any()), integer(), integer()) -> ok.
;; f42(F, X, Y) ->
;;   case (catch F(X)) of  % Catch currently doesn't stop exception propagation.
;;     {'EXIT', _} -> ok;
;;     Z ->
;;       case Z(Y) of
;;         42 -> error(bug);
;;         _ -> ok
;;       end
;;   end.
;;

;; This one is basically the same as f41.
;; We do not include exception handling in the language,
;; therefor skipping f42.

;; -spec f5(fun((integer(), integer(), integer()) -> integer()),
;;          integer(), integer(), integer()) -> ok.
;; f5(F, X, Y, Z) ->
;;   case F(X, Y, Z) of
;;     42 ->
;;       case F(Z, Y, X) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f5)

(define (f5 F X Y Z)
  (if (equal? (((F X) Y) Z) 42)
      (if (equal? (((F Z) Y) X) 17)
          (error-bug)
          'ok)
      'ok))

(define-concolic-test prop-f5
  #:inputs
  [F (->s integer (->s integer (->s integer integer)))]
  [X integer]
  [Y integer]
  [Z integer]
  #:prop
  (prop-not-error-bug (λ () (f5 F X Y Z))))

;; -spec f5ws(fun((integer(), integer(), atom()) -> integer()),
;;            integer(), integer(), integer()) -> ok.
;; f5ws(F, X, Y, Z) ->
;;   case F(X, Y, Z) of
;;     42 ->
;;       case F(Z, Y, X) of
;;         17 -> error(bug);
;;         _ -> ok
;;       end;
;;     _ -> ok
;;   end.
;;

(provide prop-f5ws)

;; Note: not an 'actual' bug: cannot reach error-bug
;; the real bug is type error.
;;
;; Therefore in the property we assume that no exception
;; should be raised and look for 'type mismatch'
;; in the error message.
;;
;; Again, we do not have atom. Therefore we replace
;; atom() by [integer()].
(define (f5ws F X Y Z)
  (if (equal? (((F X) Y) Z) 42)
      (if (equal? (((F Z) Y) X) 17)
          (error-bug "NOTTHIS")
          'ok)
      'ok))

(define-concolic-test prop-f5ws
  #:inputs
  [F (->s integer (->s integer (->s (list-of integer) integer)))]
  [X integer]
  [Y integer]
  [Z integer]
  #:prop
  (prop-not-exn (λ () (f5ws F X Y Z))))

;; -spec f6(any()) -> any().
;; f6(X) when is_function(X, 1) -> f6(X(42));
;; f6(X) when X =/= 42 -> X.
;;

(provide prop-f6)

(define (f6 X0)
  (define X (X0 0))
  (cond
    [(procedure? X) (f6 (λ (_) (X 42)))]
    [(not (equal? X 42)) X]
    ;; non-exhaustive pattern matching error
    [else (error-bug)]))

;; At the moment, top-level unions are encoded as
;; constant functions. The use-site replaces references
;; to the original input by calls to encoded constant functions
;; with a dummy argument, 0.
(define-concolic-test prop-f6
  #:inputs
  [F (->s integer
          (or/s integer (->s integer integer)))]
  #:prop
  (prop-not-error-bug (λ () (f6 F))))

;; -spec f7(fun((integer(), integer()) -> integer()), [integer()]) -> integer().
;; f7(F, L) when is_function(F, 2) ->
;;   case lists:foldl(F, 0, L) of
;;     42 -> error(bug);
;;     R -> R
;;   end.
;;

(provide prop-f7)

(define (f7 F L)
  (define R (foldl (λ (x y) ((F x) y)) 0 L))
  (if (equal? R 42)
      (error-bug)
      R))

(define-concolic-test prop-f7
  #:inputs
  [F (->s integer (->s integer integer))]
  [L (list-of integer)]
  #:prop
  (prop-not-error-bug (λ () (f7 F L))))

;; -spec f8(fun((any()) -> boolean()), [any()]) -> any().
;; f8(F, L) when is_function(F, 1) ->
;;   L1 = lists:filter(F, L),
;;   hd(L1).
;;

(provide prop-f8)

(define (f8 F L)
  (define L1 (filter F L))
  (if (null? L1) (error-bug) (car L1)))

(define-concolic-test prop-f8
  #:inputs
  [F (->s integer (->s integer integer))]
  [L (list-of integer)]
  #:prop
  (prop-not-error-bug (λ () (f8 F L))))

;; %-spec f91(fun( (any()) -> any()        ), any(), 1) -> any()
;; %       ; (fun( (any(), any()) -> any() ), any(), 2) -> any().
;; -spec f91(function(), any(), 1|2) -> any().
;; f91(F, X, 1) ->
;;   case F(X) of
;;     42 -> error(bug);
;;     R -> R
;;   end;
;; f91(F, X, 2) ->
;;   case F(X, X) of
;;     42 -> error(bug);
;;     R -> R
;;   end.

(provide prop-f91)

;; Note: we don't have multi-arity functions in the
;; current implementation. Temporarily simulate it
;; using unions.
(define (f91 F X n)
  (cond
    [(equal? n 1)
     (define R (F X))
     (if (equal? R 42)
         (error-bug)
         R)]
    [(equal? n 2)
     (define G (F X))
     (cond [(procedure? G)
            (define R (G X))
            (if (equal? R 42)
                (error-bug)
                R)]
           [else #t])]
    [else #t]))

(define-concolic-test prop-f91
  #:inputs
  [F (->s integer
          (or/s integer (->s integer integer)))]
  [X integer]
  [n (integer-range 1 2)]
  #:prop
  (prop-not-error-bug (λ () (f91 F X n))))

;;
;; %-spec f92(fun( (any()) -> any()        ), any()) -> any()
;; %       ; (fun( (any(), any()) -> any() ), any()) -> any().
;; -spec f92(function(), any()) -> any().
;; f92(F, X) when is_function(F, 1) ->
;;   case F(X) of
;;     42 -> error(bug);
;;     R -> R
;;   end;
;; f92(F, X) when is_function(F, 2) ->
;;   case F(X, X) of
;;     42 -> error(bug);
;;     R -> R
;;   end.
;;

(provide prop-f92)

(define (f92 F X)
  (define R1 (F X))
  (cond [(procedure? R1)
         (define R2 (R1 X))
         (if (equal? R2 42)
             (error-bug)
             R2)]
        [else
         (if (equal? R1 42)
             (error-bug)
             R1)]))

(define-concolic-test prop-f92
  #:inputs
  [F (->s integer
          (or/s integer (->s integer integer)))]
  [X integer]
  #:prop
  (prop-not-error-bug (λ () (f92 F X))))

;; -spec f10(fun((any()) -> any())) -> ok.
;; f10(F) ->
;;   G = fun(_) -> 1 end,
;;   case F(G) of
;;     42 -> error(bug);
;;     _ -> ok
;;   end.
;;

(provide prop-f10)

(define (f10 F)
  (define G (λ (_) 1))
  (if (equal? 42 (F G))
      (error-bug)
      'ok))

(define-concolic-test prop-f10
  #:inputs
  [F (->s (->s integer integer) integer)]
  #:prop
  (prop-not-error-bug (λ () (f10 F))))

;; -spec f11(function(), function(), any()) -> any().
;; f11(F, G, X) ->
;;   case (y(F))(X) + (y(G))(X) of
;;     9 -> error(bug);
;;     _ -> X
;;   end.
;;
;; y(F) ->
;;   G = fun(H) ->
;;       F(fun(Z) -> (H(H))(Z) end)
;;     end,
;;   G(G).
;;

(provide prop-f11)

(define (f11 F G X)
  (cond
    [(equal? (+ ((y F) X)
                ((y G) X))
             9)
     (error-bug)]
    [else X]))

(define (y F)
  (define G
    (λ (H)
      (F (λ (Z) ((H H) Z)))))
  (G G))

(define-concolic-test prop-f11
  #:inputs
  [F (->s (->s integer integer)
          (->s integer integer))]
  [G (->s (->s integer integer)
          (->s integer integer))]
  [X integer]
  #:prop
  (prop-not-error-bug (λ () (f11 F G X))))

;; -spec f12(function()) -> ok.
;; f12(F) ->
;;   case (F(fun lists:append/1))(1) of
;;     42 -> error(bug);
;;     _ -> ok
;;   end.
;;

(provide prop-f12)

(define (append-with-log xss)
  (apply-append xss))

(define (f12 f)
  (if (equal? 42 ((f append-with-log) 1))
      (error-bug)
      'ok))

(define-concolic-test prop-f12
  #:inputs ;; fun lists:append/1 is like concat, [[Int]] -> [Int]
  [F (->s  (->s (list-of (list-of integer)) (list-of integer))
           (->s integer integer))]
  #:prop
  (prop-not-error-bug (λ () (f12 F))))

;; -spec f13a(fun(({any(), any()}) -> any()), tuple()) -> any().
;; f13a(F, X) ->
;;   case F(X) of
;;     1 ->
;;       case X of
;;         {1, 2, 3} -> error(unreachable_bug);
;;         _ -> ok
;;       end;
;;     _ ->
;;       case X of
;;         {4, 2} -> error(bug);
;;         _ -> ok
;;       end
;;   end.
;;
;; -spec f13b(fun((<<_:2, _:_*4>>) -> any()), <<_:2, _:_*2>>) -> any().
;; f13b(F, X) ->
;;   case F(X) of
;;     1 ->
;;       case X of
;;         <<5:8>> -> error(unreachable_bug);
;;         _ -> ok
;;       end;
;;     _ ->
;;       case X of
;;         <<5:6>> -> error(bug);
;;         _ -> ok
;;       end
;;   end.
;;

;; f13b and f13a are similar. Because we don't support bitstring,
;; only f13a is translated.
(provide prop-f13a)

(define (f13a F X)
  (define result (F X))
  (if (equal? result 1)
      (if (equal? X '(1 2 3))
          (error-bug "UNREACHABLE_BUG")
          'ok)
      (if (equal? X (list 4 2))
          (error-bug "real bug")
          'ok)))

;; We do not have the dynamic tuple type, therefore here we
;; try to simulate it using integer tuples of length from 0 to 4
;; Moreover, tuples are encoded as finite lists
(define-concolic-test prop-f13a
  #:inputs
  [F   (->s (list/s integer integer)
            integer)]
  [X (or/s (list/s)
           (list/s integer)
           (list/s integer integer)
           (list/s integer integer integer)
           (list/s integer integer integer integer))]
  #:prop
  (prop-not-exn #:exns (list exn:fail? exn:fail:error-bug?)
                (λ () (f13a F X))))

;; -spec f14(fun(([integer(), ...]) -> [integer(), ...]), [integer(), ...]) -> ok.
;; f14(F, L) ->
;;   case F(L) of
;;     [1, 2, 3] -> error(bug);
;;     _ -> ok
;;   end.

(provide prop-f14)

(define (f14 F L)
  (cond
    [(pair? L)
     (define result (F L))
     (cond
       [(pair? result)
        (if (equal? result '(1 2 3))
            (error-bug)
            'ok)]
       [else #t])]
    [else #t]))

(define-concolic-test prop-f14
  #:inputs
  [F (->s (list-of integer)
          (list-of integer))]
  [L (list-of integer)]
  #:prop
  (prop-not-error-bug (λ () (f14 F L))))

;; -spec mf(fun((T) -> T), fun((T) -> boolean()), [T]) -> ok.
;; mf(F, P, L) ->
;;    case lists:map(F, lists:filter(P, L)) =:= lists:filter(P, lists:map(F, L)) of
;;      true -> ok;
;;      false -> error(mf_prop_fails)
;;    end.

(provide prop-mf)

(define (mf F P L)
  (define same
    (equal?
     (map F (filter P L))
     (filter P (map F L))))
  (if (equal? same #true)
      'ok
      (error-bug)))

(define-concolic-test prop-mf
  #:inputs
  [F (->s integer integer)]
  [P (->s integer boolean)]
  [L (list-of integer)]
  #:prop
  (prop-not-error-bug (λ () (mf F P L))))

(module* test racket/base
  (require rackunit
           concolic-hop/lib
           concolic-hop/strategy-queue
           "private/test-prop.rkt"
           (submod ".."))

  (test-property "f1" prop-f1)
  (test-property "f1ws" prop-f1ws
                 #:check
                 (λ (result)
                   (check-false (regexp-match? regex-failed-with-exn result))))
  (test-property "f1hs" prop-f1hs)
  (test-property "f2" prop-f2)
  (test-property "f2ws" prop-f2ws
                 #:check
                 (λ (result)
                   (check-equal? result "")))
  (test-property "f3" prop-f3)
  (test-property "f41" prop-f41)
  (test-property "f5" prop-f5)
  (test-property "f5ws" prop-f5ws
                 #:check
                 (λ (result)
                   (check-regexp-match regex-failed-with-exn result)
                   (check-regexp-match #rx"type mismatch" result)
                   (check-false (regexp-match? #rx"bug: NOTTHIS" result))))
  (test-property "f6" prop-f6
                 #:all? #t)
  (test-property "f7" prop-f7)
  (test-property "f8" prop-f8)
  (test-property "f91" prop-f91
                 #:all? #t)
  (test-property "f92" prop-f92
                 #:all? #t)
  (test-property "f10" prop-f10)
  (test-property "f11" prop-f11
                 #:path-limit 500
                 #:timeout 1
                 #:strategy (simple-prioritize-branch-strategy 1000))
  (test-property "f12" prop-f12
                 #:all? 10)
  (test-property "f13a" prop-f13a
                 #:all? 30
                 #:check
                 (λ (result)
                   (check-regexp-match regex-failed-with-exn
                                       result)
                   (check-regexp-match #rx"type mismatch"
                                       result)
                   (check-regexp-match #rx"real bug"
                                       result)
                   (check-false (regexp-match? #rx"UNREACHABLE_BUG" result))))
  (test-property "f14" prop-f14)
  (test-property "mf" prop-mf)
  )

(module* main racket/base
  (require (submod ".." test)))
