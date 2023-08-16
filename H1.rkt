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
       (arg-expr list?)])


(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name list?)
          (body fnWAE?)])

#|
<FunDef> ::= {deffun {<id> <id>*} <fnWAE>}
<fnWAE> ::= <num>
         | {+ <fnWAE> <fnWAE>}
         | {- <fnWAE> <fnWAE>}
         | {with {<id> <fnWAE>} <fnWAE>}
         | <id>
         | {<id> <fnWAE>*}
|#

;; parse : s-expression -> fnWAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(and (list? s-exp) (not (empty? s-exp)))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [else
            (unless (symbol? (first s-exp))
              (error 'parse
                     "expected a function name, got: ~a"
                     (first s-exp)))
            (app (first s-exp)
                 (map parse (rest s-exp)))])]
        [else
         (error 'parse "expected expression, got: ~a" s-exp)]))

(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

; -----------------------------------------------------
;; parse test
(test (parse `1)
      (num 1))
(test (parse `x)
      (id 'x))
(test (parse `{+ 1 2})
      (add (num 1) (num 2)))
(test (parse `{- 1 2})
      (sub (num 1) (num 2)))
(test (parse `{+ 1 {+ 2 3}})
      (add (num 1) (add (num 2) (num 3))))
(test (parse `{with {x 3} {+ x 2}})
      (with 'x (num 3) (add (id 'x) (num 2))))

(test (parse `{f 5})
      (app 'f (list (num 5))))

(test/exn (parse `{5 5})
          "expected a function name")

;; new test
(test (parse `{f 5 6 7})
      (app 'f (list (num 5) (num 6) (num 7))))

(test (parse `{f})
      (app 'f (list)))

(test (parse `{f 5 {+ 1 2} 7})
      (app 'f (list (num 5) (add (num 1) (num 2)) (num 7))))

(test (parse `{f 5 {+ 1 2} {with {x 3} {+ x 2}}})
      (app 'f (list (num 5) (add (num 1) (num 2)) (with 'x (num 3) (add (id 'x) (num 2))))))
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

; -----------------------------------------------------
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


; -----------------------------------------------------

;; interp : fnWAE? (listof FunDef?) -> number?
(define (interp an-fnwae fundefs)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (lhs rhs)
         (+ (interp lhs fundefs) (interp rhs fundefs))]
    [sub (lhs rhs)
         (- (interp lhs fundefs) (interp rhs fundefs))]
    [with (name named-expr body)
          (interp (subst body
                         name
                         (interp named-expr fundefs))
                  fundefs)]
    [id (name)
        (error 'interp "free identifier: ~a" name)]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (define the-fnwae (subst-args (fundef-body the-fundef)
                                       (fundef-param-name the-fundef)
                                       arg-expr
                                       fundefs))
         (if (equal? (length (fundef-param-name the-fundef)) (length arg-expr))
             (interp the-fnwae fundefs)
             (error 'interp "wrong arity: ~a" arg-expr))
         ]))


;; subst-args  fnWAE? list? list? FunDef? -> fnWAE?
(define (subst-args a-fnwae names values fundefs)
  (cond
    [(or (empty? names) (empty? values))
     a-fnwae]
    [else
     (subst (subst-args a-fnwae (rest names) (rest values) fundefs)
             (first names)
             (interp (first values) fundefs))])
  #|
  (if (or (empty? names) (empty? values))
      a-fnwae
      (subst (subst-args a-fnwae (rest names) (rest values) fundefs)
             (first names)
             (interp (first values) fundefs)))
  |#
  )


;; symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" name)]
        [(equal? (fundef-fun-name (first fundefs)) name)
         (first fundefs)]
        [else
         (lookup-fundef name (rest fundefs))]))

;; subst : fnWAE? symbol? number? -> fnWAE?
(define (subst a-fnwae name value)
  (when (symbol? value)
      (error 'interp "free identifier: ~a" name))
  (type-case fnWAE a-fnwae
    [num (n)
         a-fnwae]
    [add (l r)
         (add (subst l name value)
              (subst r name value))]
    [sub (l r)
         (sub (subst l name value)
              (subst r name value))]
    [with (name2 named-expr body)
          (with name2 (subst named-expr name value)
                (if (equal? name name2)
                    body
                    (subst body name value)))]
    [id (name2)
        (if (equal? name name2)
            (num value)
            a-fnwae)]
    [app (fun-name arg-expr)  
         (app fun-name
              ;; subst all arg-expr in app, return a list
              (reverse (subst-arg-expr arg-expr name value)))]))



(define (subst-arg-expr arg-expr name value)
  (if (empty? arg-expr)
      empty
      (append (subst-arg-expr (rest arg-expr) name value)
              (list (subst (first arg-expr) name value)))))

; -----------------------------------------------------------------

;; test from f1WAE

;; {deffun {f x}     {- 20 {twice {twice x}}}}
;; {deffun {twice y} {+ y y}}
;; {f 10}
(test (interp (parse `{f 10})
              (list (parse-defn `{deffun {f x}  {- 20 {twice {twice x}}}})
                    (parse-defn `{deffun {twice y} {+ y y}})))
      -20)

;; 5 -> 5
(test (interp (parse `5) '())
      5)
;; {+ 1 2} -> 3
(test (interp (parse `{+ 1 2}) '())
      3)
;; {- 3 4} -> -1
(test (interp (parse `{- 3 4}) '())
      -1)
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (parse `{+ {+ 1 2} {- 3 4}}) '())
      2)

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {+ x x}})
              '())
      6)
#|
x
|#
(test/exn (interp (parse `x) '())
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
              '())
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
              '())
      8)
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}})
              '())
      2)
#|
{with {x {+ 1 2}}
      {with {y {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}})
              '())
      6)


#|
substitute 10 for x in {+ 1 x}
|#
(test (subst (add (num 1) (id 'x))
             'x
             10)
      (add (num 1) (num 10)))
#|
substitute 10 for x in y
|#
(test (subst (id 'y) 'x 10)
      (id 'y))
#|
substitute 10 for x in {- 1 x}
|#
(test (subst (sub (num 1) (id 'x))
             'x
             10)
      (sub (num 1) (num 10)))
#|
substitute 10 for x in {with {y 17} x}
|#
(test (subst (with 'y (num 17) (id 'x))
             'x
             10)
      (with 'y (num 17) (num 10)))
#|
substitute 10 for x in {with {y x} y}
|#
(test (subst (with 'y (id 'x) (id 'y))
             'x
             10)
      (with 'y (num 10) (id 'y)))
#|
substitute 10 for x in {with {x y} x}
|#
(test (subst (with 'x (id 'y) (id 'x))
             'x
             10)
      (with 'x (id 'y) (id 'x)))




;-------------------------------------------------------------

;; test new written for fnWAE

(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)

(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)

(test/exn (interp (parse '{with {x y} 1})
                  (list))
          "free identifier")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")

(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")


(test/exn (interp (parse '{f 3 4})
                  (list (parse-defn '{deffun {f a}   5})
                        (parse-defn '{deffun {f a b} {+ a b}})))
          "wrong arity")

(test (interp (parse '{f 5})
              (list (parse-defn '{deffun {f a}   5})
                    (parse-defn '{deffun {f a b} {+ a b}})))
      5)

(test (interp (parse `{f 10 20})
              (list (parse-defn `{deffun {f x y}  {+ {twice {twice y}} {twice {twice x}}}})
                    (parse-defn `{deffun {twice y} {+ y y}})))
      120)

(test (interp (parse `{f 10 20 30})
              (list (parse-defn `{deffun {f x y z}  {+ {+ {twice {twice y}} {twice {twice x}}} {twice z}}})
                    (parse-defn `{deffun {twice y} {+ y y}})))
      180)