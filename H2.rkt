#lang plai

(define eight-principles
    (list
     "Know your rights."
     "Acknowledge your sources."
     "Protect your work."
     "Avoid suspicion."
     "Do your own work."
     "Never falsify a record or permit another person to do so."
     "Never fabricate data, citations, or experimental results."
     "Always tell the truth when discussing your work with your instructor."))

(print-only-errors)

(define-type fnWAE
  [num (n number?)]
  [add (lhs fnWAE?)
       (rhs fnWAE?)]
  [sub (lhs fnWAE?)
       (rhs fnWAE?)]
  [with (name symbol?)
        (bound-expr fnWAE?)
        (body-expr fnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (arg-expr list?)]
  [if0 (cond fnWAE?)
       (t fnWAE?)
       (f fnWAE?)])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name list?)
          (body fnWAE?)])


(define (mtSub) (hash))
(define (aSub name value rest)
  (hash-set rest name value))
(define (lookup name ds)
  (hash-ref ds name (lambda () (error 'interp "free identifier: get ~a" ds))))

;;---------------------------------------------------------

;; parser list? -> fnWAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (num s-expr)]
        [(symbol? s-expr)
         (id s-expr)]
        [(list? s-expr)
         (when (empty? s-expr)
           (error 'parse "the empty list is not a valid f1WAE"))
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "add")
            (add (parse (second s-expr))
                 (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "sub")
            (sub (parse (second s-expr))
                 (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (unless (symbol? (first (second s-expr)))
              (error 'parse "expected variable name, got ~a" (first (second s-expr))))
            (with (first (second s-expr))
                  (parse (second (second s-expr)))
                  (parse (third s-expr)))]
           [(if0)
            (check-pieces s-expr 4 "if0")
            (if0 (parse (second s-expr))
                 (parse (third s-expr))
                 (parse (fourth s-expr)))]
           [else
            (unless (symbol? (first s-expr))
              (error 'parse "expected function name, got ~a" (first s-expr)))
            (app (first s-expr)
                 (map parse (rest s-expr)))])]
        [else (error 'parse "expected f1WAE, got ~a" s-expr)]))


(define (check-pieces s-expr n-pieces who)
  (unless (= n-pieces (length s-expr))
    (error 'parse "expected ~a, got ~a" who s-expr)))



(test (parse `1) (num 1))
(test (parse `y) (id 'y))
(test (parse `{+ 1 2}) (add (num 1) (num 2)))
(test (parse `{- 1 2}) (sub (num 1) (num 2)))
(test (parse `{with {x 3} {+ x 2}}) (with 'x (num 3) (add (id 'x) (num 2))))
(test (parse `{f 10}) (app 'f (list (num 10))))
(test (parse `{f 10 20}) (app 'f (list (num 10) (num 20))))
(test (parse `{if0 1 2 3}) (if0 (num 1) (num 2) (num 3)))
(test/exn (parse `{+ 1 2 3}) "expected add")

; -----------------------------------------------------

;; parse-defn list -> FunDef

(define (parse-defn s-exp)
  (check-pieces s-exp 3 "parse-defn")
  (unless (equal? (first s-exp) 'deffun)
    (error 'parse-defn "expect keyword deffun"))
  (define m-ht (make-hash))
  (check-syntax (rest (second s-exp)) m-ht)
  (fundef (first (second s-exp))
          (rest (second s-exp))
          (parse (third s-exp))))

(define (check-syntax s-exp ht)
  (cond
    [(empty? s-exp) (void)]
    [else
     (if (eq? (hash-ref ht (first s-exp) #f) #f)
         (begin
           (hash-set! ht (first s-exp) "yes")
           (check-syntax (rest s-exp) ht))
         (error 'parse-defn "bad syntax: ~a" (first s-exp)))
     ]))

(test
 (parse-defn '{deffun {f x y} {+ x y}})
 (fundef 'f (list 'x 'y) (add (id 'x) (id 'y))))

(test/exn
 (parse-defn '{deffun {f x x} {+ x y}})
 "bad syntax")


(test
 (parse-defn '{deffun {f} 5})
 (fundef 'f (list) (num 5)))

(test/exn
 (parse-defn '{def {f x y} {+ x y}})
 "expect keyword deffun")

;; ----------------------------------------------------------------------

;; interp : fnWAE? (listof FunDef?) DefSub? -> number?
(define (interp an-fnwae fundefs ds)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs ds) (interp r fundefs ds))]
    [sub (l r) (- (interp l fundefs ds) (interp r fundefs ds))]
    [id (name) (lookup name ds)]
    [with (name named-expr body)
          (interp body
                  fundefs
                  (aSub name
                        (interp named-expr fundefs ds)
                        ds))]
    [if0 (cond t f)
         (if (equal? (interp cond fundefs ds) 0)
             (interp t fundefs ds)
             (interp f fundefs ds))]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (define args (map (lambda (arg) (interp arg fundefs ds)) arg-expr))
         (define param (fundef-param-name the-fundef))
         (if (equal? (length args) (length param))
             (interp (fundef-body the-fundef)
                 fundefs
                 #;(aSub (fundef-param-name the-fundef)
                       (interp arg-expr fundefs ds)
                       (mtSub))
                 (fold-arg args param fundefs ds))
             (error 'interp "wrong arity, get: ~a" args))]))


(define (fold-arg args param fundefs ds)
  (if (empty? args)
      (mtSub)
      (hash-set (fold-arg (rest args) (rest param) fundefs ds)
                (first param)
                (first args))))


;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))


;; ----------------------------------------------------------------------
;; tests from last time, updated

(define initial-def-sub (mtSub))

;; from the slides
(test/exn (interp (parse `{with {y 2}
                                {f 10}})
                  (list (parse-defn '{deffun {f x y} {+ x y}}))
                  initial-def-sub)
          "wrong arity")

;; new added for if0

(test (interp (parse '{if0 0 1 2})
              (list)
              initial-def-sub)
      1)

(test (interp (parse '{if0 1 1 2})
              (list)
              initial-def-sub)
      2)

(test (interp (parse '{if0 1 {+ 2 3} {- 6 9}})
              (list)
              initial-def-sub)
      -3)

(test (interp (parse '{if0 0 {+ 2 3} {- 6 9}})
              (list)
              initial-def-sub)
      5)

;; 5 -> 5
(test (interp (parse `5) '() initial-def-sub)
      5)
;; {+ 1 2} -> 3
(test (interp (parse `{+ 1 2}) '() initial-def-sub)
      3)
;; {- 3 4} -> -1
(test (interp (parse `{- 3 4}) '() initial-def-sub)
      -1)
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (parse `{+ {+ 1 2} {- 3 4}}) '() initial-def-sub)
      2)

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {+ x x}})
              '()
              initial-def-sub)
      6)
#|
x
|#
(test/exn (interp (parse `x) '() initial-def-sub)
          "free identifier")
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {x {- 4 3}}
         {+ x x}}}
|#
(test (interp (parse `{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {x {- 4 3}}
                               {+ x x}}})
              '()
              initial-def-sub)
      8)
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {y {- 4 3}}
         {+ y y}}}
|#
(test (interp (parse `{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {y {- 4 3}}
                               {+ y y}}})
              '()
              initial-def-sub)
      8)
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}})
              '()
              initial-def-sub)
      2)
#|
{with {x {+ 1 2}}
      {with {y {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}})
              '()
              initial-def-sub)
      6)

(test/exn (interp (parse `{f 10})
                  (list)
                  initial-def-sub)
          "undefined function")

(test (interp (parse `{f 10})
              (list (parse-defn '{deffun {f x} {- 20 {twice {twice x}}}})
                    (parse-defn '{deffun {twice y} {+ y y}}))
              initial-def-sub)
      -20)
(test (interp (parse `{f 10})
              (list (fundef 'f (list 'x)
                            (parse `{- 10 {twice {twice x}}}))
                    (fundef 'twice (list 'y)
                            (parse `{+ y y})))
              initial-def-sub)
      -30)

;-------------------------------------------------------------

;; test new written for fnWAE

(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}}))
              initial-def-sub)
      3)

(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5}))
              initial-def-sub)
      10)

(test/exn (interp (parse '{with {x y} 1})
                  (list)
                  initial-def-sub)
          "free identifier")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}}))
                  initial-def-sub)
          "bad syntax")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c}))
                  initial-def-sub)
          "undefined function")

(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}}))
                  initial-def-sub)
          "wrong arity")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c}))
                  initial-def-sub)
          "free identifier")


(test/exn (interp (parse '{f 3 4})
                  (list (parse-defn '{deffun {f a}   5})
                        (parse-defn '{deffun {f a b} {+ a b}}))
                  initial-def-sub)
          "wrong arity")

(test (interp (parse '{f 5})
              (list (parse-defn '{deffun {f a}   5})
                    (parse-defn '{deffun {f a b} {+ a b}}))
              initial-def-sub)
      5)

(test (interp (parse `{f 10 20})
              (list (parse-defn `{deffun {f x y}  {+ {twice {twice y}} {twice {twice x}}}})
                    (parse-defn `{deffun {twice y} {+ y y}}))
              initial-def-sub)
      120)

(test (interp (parse `{f 10 20 30})
              (list (parse-defn `{deffun {f x y z}  {+ {+ {twice {twice y}} {twice {twice x}}} {twice z}}})
                    (parse-defn `{deffun {twice y} {+ y y}}))
              initial-def-sub)
      180)


;; interp-expr
;; fnWAE? (listof FunDef)? -> Number?

(define (interp-expr a-fnwae fundefs)
  (interp a-fnwae fundefs initial-def-sub))


;; test on assignment description

(test (interp-expr (parse '{if0 0 1 2}) '()) 1)

(test (interp-expr (parse '{if0 1 2 3}) '()) 3)

(test (interp-expr (parse '{if0 3 2 3}) '()) 3)


;; neg? mult under fnWAE


(define mult-and-neg-deffuns (list `{deffun {neg? x} {neg-dfs x x}}
                                   `{deffun {neg-dfs x y} {if0 x 1 {if0 y 0 {neg-dfs {- x 1} {+ y 1}}}}}
                                   `{deffun {mult-abs x y} {if0 x 0 {+ {mult-abs {- x 1} y} y}}}
                                   `{deffun {mult x y} {if0 {neg? x} {if0 {neg? y} {mult-abs {- 0 x} {- 0 y}} {- 0 {mult-abs {- 0 x} y}}} {if0 {neg? y} {- 0 {mult-abs x {- 0 y}}} {mult-abs x y}}}}))



(test (interp-expr (parse '{neg? 3}) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse '{neg? 0}) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse '{neg? -8}) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '{mult 3 4}) (map parse-defn mult-and-neg-deffuns)) 12)
(test (interp-expr (parse '{mult 3 -4}) (map parse-defn mult-and-neg-deffuns)) -12)
(test (interp-expr (parse '{mult -3 4}) (map parse-defn mult-and-neg-deffuns)) -12)
(test (interp-expr (parse '{mult -3 -4}) (map parse-defn mult-and-neg-deffuns)) 12)

(test (interp-expr (parse '{mult 114514 1919810}) (map parse-defn mult-and-neg-deffuns)) 219845122340)