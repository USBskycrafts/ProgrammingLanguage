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

;; ----------------------------------------------------------------------------


(define-type FAE
    [num (n number?)]
    [add (lhs FAE?) (rhs FAE?)]
    [sub (lhs FAE?) (rhs FAE?)]
    [id (name symbol?)]
    [if0 (test FAE?) (then FAE?) (else FAE?)]
    [fun (param symbol?) (body FAE?)]
    [app (fun FAE?) (arg FAE?)])


(define-type FNWAE
    [W-num (n number?)]
    [W-add (lhs FNWAE?)
           (rhs FNWAE?)]
    [W-sub (lhs FNWAE?)
           (rhs FNWAE?)]
    [W-with (name symbol?)
            (named-expr FNWAE?)
            (body FNWAE?)]
    [W-id (name symbol?)]
    [W-if0 (tst FNWAE?)
           (thn FNWAE?)
           (els FNWAE?)]
    [W-fun (params (listof symbol?))
           (body FNWAE?)]
    [W-app (fun-expr  FNWAE?)
           (arg-exprs (listof FNWAE?))])
;; ----------------------------------------------------------------------------


;; parse : s-expr -> FNWAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (W-num s-expr)]
        [(symbol? s-expr)
         (W-id s-expr)]
        [(list? s-expr)
         (when (empty? s-expr)
           (error 'parse "the empty list is not a valid FWAE"))
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "+")
            (W-add (parse (second s-expr))
                 (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "-")
            (W-sub (parse (second s-expr))
                 (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (unless (symbol? (first (second s-expr)))
              (error 'parse "expected variable name, got ~a" (first (second s-expr))))
            (W-with (first (second s-expr))
                  (parse (second (second s-expr)))
                  (parse (third s-expr)))]
           [(fun)
            (check-pieces s-expr 3 "fun")
            #;(unless (> (length (second s-expr)) 0)
              (error 'parse "nullary function, got ~a" (second s-expr)))
            (W-fun (second s-expr)
                   (parse (third s-expr)))]
           [(if0)
            (check-pieces s-expr 4 "if0")
            (W-if0 (parse (second s-expr))
                   (parse (third s-expr))
                   (parse (fourth s-expr)))]
           
           [else
            #;(unless (> (length s-expr) 1)
              (error 'parse "nullary application, got ~a" (rest s-expr)))
            (W-app
             (parse (first s-expr))
             (map parse (rest s-expr)))])]
        [else
         (error 'parse "expected FWAE, got ~a" s-expr)]))

(define (check-pieces s-expr n who)
  (unless (and (list? s-expr) (= (length s-expr) n))
    (error 'parse "expected ~a, got ~a" who s-expr)))

;; ----------------------------------------------------------------------------


;; test for parser
(test (parse `{with {f {fun {x} {+ x 1}}}
                    {f 3}})
      (W-with `f
              (W-fun (list `x)
                     (W-add (W-id `x)
                            (W-num 1)))
              (W-app (W-id `f) (list (W-num 3)))))

(test (parse `{with {f {fun {x} {- x 1}}}
                    {f 3}})
      (W-with `f
              (W-fun (list `x)
                     (W-sub (W-id `x)
                            (W-num 1)))
              (W-app (W-id `f) (list (W-num 3)))))

(test (parse `{{fun {x y} {if0 x y 1}} 3 4})
      (W-app (W-fun (list `x `y)
                    (W-if0 (W-id `x) (W-id `y) (W-num 1)))
             (list (W-num 3) (W-num 4))))


(test (parse `{{{fun {x y} {fun {x y} {- x y}}} 3 4} 5 6})
      (W-app (W-app (W-fun {list `x `y}
                           {W-fun {list `x `y}
                                  {W-sub {W-id `x} {W-id `y}}})
                    (list (W-num 3) (W-num 4)))
             (list (W-num 5) (W-num 6))))

;; ----------------------------------------------------------------------------

;; compile FNWAE? -> FAE?
(define (compile a-fnwae)
  (type-case FNWAE a-fnwae
    [W-num (n) (num n)]
    [W-add (lhs rhs) (add (compile lhs)
                          (compile rhs))]
    [W-sub (lhs rhs) (sub (compile lhs)
                          (compile rhs))]
    [W-id (name) (id name)]
    [W-if0 (tst thn els) (if0 (compile tst)
                              (compile thn)
                              (compile els))]
    [W-with (name named-expr body) (app (fun name
                                             (compile body))
                                        (compile named-expr))]
    [W-fun (params body)
           (unless (> (length params) 0)
             (error `compile "nullary function at ~a" a-fnwae))
           (curring-fun params body)]
    [W-app (fun-expr arg-expr)
           (unless (> (length arg-expr) 0)
             (error `compile "nullary application at ~a" a-fnwae))
           (curring-app fun-expr (reverse arg-expr))]))


;; curring-fun listof FNWAE? FNWAE? -> FAE
(define (curring-fun params body)
  (if (equal? (length params) 1)
      (fun (first params) (compile body))
      (fun (first params) (curring-fun (rest params) body))))

;; curring-app FNWAE? listof FNWAE? -> FAE
(define (curring-app fun-expr arg-expr)
  (if (equal? (length arg-expr) 1)
      (app (compile fun-expr) (compile (first arg-expr)))
      (app (curring-app fun-expr (rest arg-expr)) (compile (first arg-expr)))))

;; ----------------------------------------------------------------------------

;; test for compile

(test (compile (parse `{+ x 1}))
      (add (id `x) (num 1)))

(test (compile (parse `{- x 1}))
      (sub (id `x) (num 1)))

(test (compile (parse `{if0 x 1 2}))
      (if0 (id `x) (num 1) (num 2)))


(test (compile (parse `{with {f {fun {x} {- x 1}}}
                             {f 3}}))
 (app (fun `f
           (app (id `f) (num 3)))
      (fun `x
           (sub (id `x) (num 1)))))


(test (compile (parse `{{fun {x y} {if0 x y 1}} 3 4}))
      (app (app (fun `x
                     (fun `y
                          (if0 (id `x) (id `y) (num 1))))
                (num 3))
           (num 4)))

(test/exn (compile (parse `{{fun {} {if0 0 2 1}} 3 4}))
          "nullary function")

(test/exn (compile (parse `{{fun {x y} {if0 x y 1}} }))
          "nullary application")


;; ----------------------------------------------------------------------------

;; Copy from lec07.rkt, CopyRight@Lukas 2023

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body FAE?)
            (ds DefSub?)])

(define-type DefSub
  [mtSub]
  [aSub (name  symbol?)
        (value FAE-Value?)
        (rest  DefSub?)])

;; interp : FAE? DefSub? -> FAE-Value?
(define (interp an-fae ds)
  (type-case FAE an-fae
    [num (n) (numV n)]
    [add (l r) (numop + l r ds)]
    [sub (l r) (numop - l r ds)]
    [id (name) (lookup name ds)]
    ;; -------------------------
    ;; new added for if0
    [if0 (test then else)
         (define test-result (interp test ds))
         (if (and (numV? test-result) (equal? (numV-n test-result) 0))
             (interp then ds)
             (interp else ds))]
    ;; -------------------------
    [fun (param-name body) (closureV param-name body ds)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (define arg-val (interp arg-expr ds))
         (type-case FAE-Value fun-val
           [closureV (param-name body closed-ds)
                     (interp body
                             (aSub param-name
                                   arg-val
                                   closed-ds))]
           [else (error 'interp "expected function, got ~a" fun-val)])]))

(define (numop op l r ds)
  (define l-val (interp l ds))
  (define r-val (interp r ds))
  (unless (and (numV? l-val) (numV? r-val))
    (error 'interp "expected number"))
  (numV (op (numV-n l-val) (numV-n r-val))))

;; lookup : symbol? DefSub? -> FAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; ----------------------------------------------------------------------------

;; test copied from lec07.rkt, CopyRight@Lukas 2023

(define initial-def-sub (mtSub))

(test (interp (compile (parse `{with {x 2} {- 1 x}}))
              initial-def-sub)
      (numV -1))

;; 5 -> 5
(test (interp (compile (parse `5))
              initial-def-sub)
      (numV 5))
;; {+ 1 2} -> 3
(test (interp (compile (parse `{+ 1 2}))
              initial-def-sub)
      (numV 3))
;; {- 3 4} -> -1
(test (interp (compile (parse `{- 3 4}))
              initial-def-sub)
      (numV -1))
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (compile (parse `{+ {+ 1 2} {- 3 4}}))
              initial-def-sub)
      (numV 2))

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {+ x x}}))
              initial-def-sub)
      (numV 6))
#|
x
|#
(test/exn (interp (compile (parse `x))
                  initial-def-sub)
          "free identifier")
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {x {- 4 3}}
         {+ x x}}}
|#
(test (interp (compile (parse `{+ {with {x {+ 1 2}}
                                        {+ x x}}
                                  {with {x {- 4 3}}
                                        {+ x x}}}))
              initial-def-sub)
      (numV 8))
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {y {- 4 3}}
         {+ y y}}}
|#
(test (interp (compile (parse `{+ {with {x {+ 1 2}}
                                        {+ x x}}
                                  {with {y {- 4 3}}
                                        {+ y y}}}))
              initial-def-sub)
      (numV 8))
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {with {x {- 4 3}}
                                           {+ x x}}}))
              initial-def-sub)
      (numV 2))
#|
{with {x {+ 1 2}}
      {with {y {- 4 3}}
            {+ x x}}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {with {y {- 4 3}}
                                           {+ x x}}}))
              initial-def-sub)
      (numV 6))

(test (interp (compile (parse `{with {f {fun {x} {+ x 1}}}
                                     {f 3}}))
              initial-def-sub)
      (numV 4))

(test (interp (compile (parse `{{fun {x} {+ x 1}} 3}))
              initial-def-sub)
      (numV 4))

(test (interp (compile (parse `{fun {x} {+ x 1}}))
              initial-def-sub)
      (closureV 'x (add (id 'x) (num 1)) (mtSub)))

(test/exn (interp (compile (parse `{1 2}))
                  initial-def-sub)
          "expected function")

(test/exn (interp (compile (parse `{+ 1 {fun {x} 10}}))
                  initial-def-sub)
          "expected number")

(test (interp (compile (parse `{with {f {with {x 3}
                                              {fun {y} {+ x y}}}}
                                     {f 5}}))
              initial-def-sub)
      (numV 8))

(test/exn (interp (compile (parse `{with {z {fun {x} {+ x y}}}
                                         {with {y 10} {z y}}}))
                  initial-def-sub)
          "free identifier")


;; ----------------------------------------------------------------------------

(define (interp-expr a-fae)
  (define value (interp a-fae initial-def-sub))
  (type-case FAE-Value value
    [numV (n) n]
    [closureV (param-name body ds) `function]))

(test/exn (interp-expr (compile (parse `{+ {fun {x} x} {1 2}})))
          "expected function")

(test (interp-expr (num 10)) 10)

(test (interp-expr (fun 'x (id 'x))) 'function)

(test (interp-expr (compile (parse `{with {f {fun {x} {- x 1}}}
                             {f 3}})))
      2)


(test (interp-expr (compile (parse `{{fun {x y} {if0 x y 1}} 3 4})))
      1)

(test (interp-expr (compile (parse `{{fun {x y} {if0 x y {+ 3 5}}} 0 4})))
      4)

(test (interp-expr (compile (parse `{{fun {x y} {if0 x {+ 3 5} y}} 0 4})))
      8)

(test (interp-expr (compile (parse `{{fun {x y} {if0 {fun {x} {+ x x}} x y}} 0 4})))
      4)

(test (interp-expr (compile (parse `{{fun {x y} {if0 {fun {x} {+ x x}} x y}} 0 4})))
      4)

(test (interp-expr (compile (parse `{{fun {x y} {if0 {fun {x} {+ x x}} {{fun {x} {+ x 1}} x} {{fun {x} {- x 1}} y}}} 0 4})))
      3)

(test (interp-expr (compile (parse `{{fun {x y} {if0 0 {{fun {x} {+ x 1}} x} {{fun {x} {- x 1}} y}}} 0 4})))
      1)


(test (interp-expr (compile (parse `{{fun {x y} {{fun {x y} {+ x y}} 3 4}} 5 6})))
      7)

(test (interp-expr (compile (parse `{{fun {x y} {+ {if0 x 3 4} {+ {if0 y 5 6} {{fun {x y} {+ x y}} 3 4}}}} 5 6})))
      17)

;; ----------------------------------------------------------------------------

;; implement for factorial and prime?


(define make-ref `{fun {body-proc}
                       {with {fX {fun {fX} {with {f {fun {x}
                                                         {{fX fX} x}}}
                                                 {body-proc f}}}}
                             {fX fX}}})

#;(define add-fun `{with {add {,make-ref {fun {add} {fun {n}
                                                       {if0 n 0 {+ n {add {- n 1}}}}}}}}
                       {add 10}})

(define neg? `{with {neg-helper {,make-ref {fun {neg-helper}
                                               {fun {x y}
                                                    {if0 x 1 {if0 y 0 {neg-helper {- x 1} {+ y 1}}}}}}}}
                    {fun {x} {neg-helper x x}}})


(define mult `{with {mult-helper {,make-ref {fun {mult-helper}
                                                 {fun {x y}
                                                      {if0 x 0 {+ {mult-helper {- x 1} y} y}}}}}}
                    {fun {x y} {if0 {,neg? x}
                                    {if0 {,neg? y}
                                         {mult-helper {- 0 x} {- 0 y}}
                                         {- 0 {mult-helper {- 0 x} y}}}
                                    {if0 {,neg? y}
                                         {- 0 {mult-helper x {- 0 y}}}
                                         {mult-helper x y}}}}})

(define factorial `{,make-ref {fun {factorial}
                                   {fun {x}
                                        {if0 {- x 1}
                                             1
                                             {,mult x {factorial {- x 1}}}}}}})


(define div-helper `{,make-ref {fun {div-helper}
                                    {fun {x y z}
                                         {if0 {,neg? {- x {,mult y {+ z 1}}}}
                                              z
                                              {div-helper x y {+ z 1}}}}}})

(define div `{fun {x y}
                  {,div-helper x y 0}})

(define mod `{fun {x y}
                  {- x {,mult {,div x y}
                             y}}})

(define or-fnwae `{fun {x y}
                        {if0 x {if0 y 0 1} 1}})
                       

(define prime-helper `{,make-ref {fun {prime-helper}
                                      {fun {x y}
                                           {if0 {- y 2}
                                                {if0 {,mod x 2}
                                                     1
                                                     0}
                                                {if0 {,or-fnwae {if0 {,mod x y} 1 0} {prime-helper x {- y 1}}}
                                                     0
                                                     1}}}}})

(define prime? `{fun {x}
                     {if0 {- x 1}
                          1
                          {if0 {,neg? {- x 4}}
                               0
                               {,prime-helper x {,div x 2}}}}})


;; ----------------------------------------------------------------------------

;; test for the function

(test (interp-expr (compile (parse make-ref)))
      `function)

(test (interp-expr (compile (parse `{,neg? 3})))
      1)

(test (interp-expr (compile (parse `{,neg? -3})))
      0)

(test (interp-expr (compile (parse `{,mult 3 4})))
      12)

(test (interp-expr (compile (parse `{,mult -3 4})))
      -12)

(test (interp-expr (compile (parse `{,mult 0 4})))
      0)

(test (interp-expr (compile (parse `{,factorial 4})))
      24)

(test (interp-expr (compile (parse `{,factorial 5})))
      120)

(test (interp-expr (compile (parse `{,div 12 3})))
      4)


(test (interp-expr (compile (parse `{,div 2 3})))
      0)

(test (interp-expr (compile (parse `{,div 24 5})))
      4)

(test (interp-expr (compile (parse `{,mod 24 5})))
      4)

(test (interp-expr (compile (parse `{,mod 25 5})))
      0)

(test (interp-expr (compile (parse `{,mod 2 3})))
      2)

(test (interp-expr (compile (parse `{,prime? 2})))
      0)

(test (interp-expr (compile (parse `{,prime? 3})))
      0)

(test (interp-expr (compile (parse `{,prime? 5})))
      0)

(test (interp-expr (compile (parse `{,prime? 6})))
      1)

(test (interp-expr (compile (parse `{,prime? 27})))
      1)

(test (interp-expr (compile (parse `{,prime? 29})))
      0)

(test (interp-expr (compile (parse `{,prime? 4})))
      1)

(test (interp-expr (compile (parse `{,prime? 9})))
      1)

(test (interp-expr (compile (parse `{,prime? 11})))
      0)

(test (interp-expr (compile (parse `{,prime? 17})))
      0)

(test (interp-expr (compile (parse `{,prime? 16})))
      1)

(test (interp-expr (compile (parse `{,prime? 1})))
      1)

#;(test (interp-expr (compile (parse add-fun)))
      55)