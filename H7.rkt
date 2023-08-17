#lang plaitypus

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

(print-only-errors #t)
;; ----------------------------------------------------------------------

(define-type TLFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TLFAE) (r : TLFAE)]
  [sub (l : TLFAE) (r : TLFAE)]
  [eql (l : TLFAE) (r : TLFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TLFAE) (thn : TLFAE) (els : TLFAE)]
  [fun (arg : symbol) (typ : Type) (body : TLFAE)]
  [app (rator : TLFAE) (rand : TLFAE)]
  [consl (fst : TLFAE) (rst : TLFAE)]
  [firstl (lst : TLFAE)]
  [restl (lst : TLFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TLFAE)]
  [makevector (size : TLFAE) (initial : TLFAE)]
  [set (vec : TLFAE) (index : TLFAE) (val : TLFAE)]
  [lengthl (col : TLFAE)]
  [get (col : TLFAE) (index : TLFAE)])

(define-type Type
  [numberT]
  [booleanT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)]
  [vectorT (typ : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------------------------------------

(define parse : (s-expression -> TLFAE)
  (lambda (s-exp)
    (cond
      [(s-exp-number? s-exp)
       (num (s-exp->number s-exp))]
      [(s-exp-symbol? s-exp)
       (case (s-exp->symbol s-exp)
         [(true)  (bool #t)]
         [(false) (bool #f)]
         [else (id (s-exp->symbol s-exp))])]
      [(s-exp-list? s-exp)
       (define as-list (s-exp->list s-exp))
       (cond [(empty? as-list)
              (error 'parse "the empty list is not a valid TLFAE")]
             [(s-exp-symbol? (first as-list))
              (case (s-exp->symbol (first as-list))
                [(+)
                 (check-pieces as-list "add" 3)
                 (add (parse (second as-list))
                      (parse (third as-list)))]
                [(-)
                 (check-pieces as-list "sub" 3)
                 (sub (parse (second as-list))
                      (parse (third as-list)))]
                [(=)
                 (check-pieces as-list "eql" 3)
                 (eql (parse (second as-list))
                      (parse (third as-list)))]
                [(if)
                 (check-pieces as-list "if" 4)
                 (ifthenelse (parse (second as-list))
                             (parse (third as-list))
                             (parse (fourth as-list)))]
                [(fun)
                 (check-pieces as-list "fun" 3)
                 (unless (s-exp-list? (second as-list))
                   (error 'parse "expected parameter list"))
                 (define param-list (s-exp->list (second as-list)))
                 (check-pieces param-list "parameter list" 3)
                 (unless (s-exp-symbol? (first param-list))
                   (error 'parse "expected symbol as parameter name"))
                 (unless (and (s-exp-symbol? (second param-list))
                              (equal? ': (s-exp->symbol (second param-list))))
                   (error 'parse "expected `:`"))
                 (fun (s-exp->symbol (first param-list))
                      (parse-type (third param-list))
                      (parse (third as-list)))]
                [(cons)
                 (check-pieces as-list "cons" 3)
                 (consl (parse (second as-list))
                        (parse (third as-list)))]
                [(first)
                 (check-pieces as-list "first" 2)
                 (firstl (parse (second as-list)))]
                [(rest)
                 (check-pieces as-list "rest" 2)
                 (restl (parse (second as-list)))]
                [(nil)
                 (check-pieces as-list "nil" 2)
                 (nil (parse-type (second as-list)))]
                [(empty?)
                 (check-pieces as-list "empty?" 2)
                 (mtl? (parse (second as-list)))]
                [(make-vector)
                 (check-pieces as-list "make-vector" 3)
                 (makevector (parse (second as-list))
                             (parse (third as-list)))]
                [(set)
                 (check-pieces as-list "set" 4)
                 (set (parse (second as-list))
                      (parse (third as-list))
                      (parse (fourth as-list)))]
                [(length)
                 (check-pieces as-list "length" 2)
                 (lengthl (parse (second as-list)))]
                [(get)
                 (check-pieces as-list "get" 3)
                 (get (parse (second as-list))
                      (parse (third as-list)))]
                [else (parse-app as-list)])]
             [else (parse-app as-list)])]
      [else
       (error 'parse "expected TLFAE")])))

(define parse-app : ((listof s-expression) -> TLFAE)
  (lambda (s-exps)
    (check-pieces s-exps "app" 2)
    (app (parse (first  s-exps))
         (parse (second s-exps)))))

(define parse-type : (s-expression -> Type)
  (lambda (s-exp)
    (cond [(and (s-exp-symbol? s-exp)
                (equal? 'number (s-exp->symbol s-exp)))
           (numberT)]
          [(and (s-exp-symbol? s-exp)
                (equal? 'boolean (s-exp->symbol s-exp)))
           (booleanT)]
          [(s-exp-list? s-exp)
           (define as-list (s-exp->list s-exp))
           (case (length as-list)
             [(2)
              (unless (s-exp-symbol? (first as-list))
                (error 'parse "expected `listof` or `vectorof`"))
              (case (s-exp->symbol (first as-list))
                [(listof)
                 (listT (parse-type (second as-list)))]
                [(vectorof)
                 (vectorT (parse-type (second as-list)))]
                [else
                 (error 'parse "expected `listof` or `vectorof`")])]
             [(3)
              (unless (and (s-exp-symbol? (second as-list))
                           (equal? '-> (s-exp->symbol (second as-list))))
                (error 'parse "expected `->`"))
              (arrowT (parse-type (first as-list))
                      (parse-type (third as-list)))]
             [else (error 'parse-type "expected type")])]
          [else (error 'parse-type "expected type")])))

(define check-pieces : ((listof s-expression) string number -> void)
  (lambda (s-exps expected n-pieces)
    (unless (= n-pieces (length s-exps))
      (error 'parse
             (string-append (string-append "expected " expected)
                            (string-append " got " (to-string s-exps)))))))

;; ----------------------------------------------------------------------

(define typecheck-expr : (TLFAE -> Type)
  (lambda (a-tlfae)
    (typecheck a-tlfae (mtEnv))))



(define typecheck : (TLFAE TypeEnv -> Type)
  (lambda (a-tlfae gamma)
    (type-case TLFAE a-tlfae
      [num (n)
           (numberT)]
      [bool (b)
            (booleanT)]
      [add (l r)
           (unless (and (numberT? (typecheck l gamma))
                        (numberT? (typecheck r gamma)))
             (error 'typecheck "expected number"))
           (numberT)]
      [sub (l r)
           (unless (and (numberT? (typecheck l gamma))
                        (numberT? (typecheck r gamma)))
             (error 'typecheck "expected number"))
           (numberT)]
      [eql (l r)
           (unless (and (numberT? (typecheck l gamma))
                        (numberT? (typecheck r gamma)))
             (error 'typecheck "expected number"))
           (booleanT)]
      [id  (name)
           (lookup-type name gamma)]
      [ifthenelse (tst thn els)
                  (define tst-type (typecheck tst gamma))
                  (define thn-type (typecheck thn gamma))
                  (define els-type (typecheck els gamma))
                  (unless (booleanT? tst-type)
                    (error 'typecheck "expected boolean"))
                  (unless (equal? thn-type els-type)
                    (error 'typecheck "type mismatch"))
                  thn-type]
      [fun (param-name param-type body)
           (arrowT param-type
                   (typecheck body
                              (aBind param-name
                                     param-type
                                     gamma)))]
      [app (fun-expr arg-expr)
           (define fun-type (typecheck fun-expr gamma))
           (define arg-type (typecheck arg-expr gamma))
           (type-case Type fun-type
             [arrowT (tau2 tau3)
                     (unless (equal? tau2 arg-type)
                       (error 'typecheck "type mismatch"))
                     tau3]
             [else
              (error 'typecheck "expected function")])]
      [consl (fst rst)
             (define rst-type (typecheck rst gamma))
             (type-case Type rst-type
               [listT (typ)
                      (unless (equal? typ (typecheck fst gamma))
                        (error 'typecheck "type mismatch"))
                      rst-type]
               [else
                (error 'typecheck "expected list")])]

      [firstl (lst)
              (type-case Type (typecheck lst gamma)
                [listT (typ)
                       typ]
                [else
                 (error 'typecheck "expected list")])]
      [restl (lst)
             (define lst-type (typecheck lst gamma))
             (unless (listT? lst-type)
               (error 'typecheck "expected list"))
             lst-type]
      [nil (typ)
           (listT typ)]
      [mtl? (lst)
            (unless (listT? (typecheck lst gamma))
              (error 'typecheck "expected list"))
            (booleanT)]
      [makevector (size initial)
                  (unless (numberT? (typecheck size gamma))
                    (error 'typecheck "expected number"))
                  (vectorT (typecheck initial gamma))]
      [set (vec index val)
           (unless (numberT? (typecheck index gamma))
             (error 'typecheck "expected number"))
           (type-case Type (typecheck vec gamma)
             [vectorT (typ)
                      (define val-type (typecheck val gamma))
                      (if (equal? typ val-type)
                          val-type
                          (error 'typecheck "type mismatch"))]
             [else
              (error 'typecheck "expected vector")])]
      [lengthl (col)
               (type-case Type (typecheck col gamma)
                 [vectorT (typ)
                          (numberT)]
                 [listT (typ)
                        (numberT)]
                 [else
                  (error 'typecheck "expected list or vector")])]
      [get (col index)
           (unless (numberT? (typecheck index gamma))
             (error 'typecheck "expected number"))
           (type-case Type (typecheck col gamma)
             [vectorT (typ)
                      typ]
             [listT (typ)
                    typ]
             [else
              (error 'typecheck "expected list or vector")])])))

(define lookup-type : (symbol TypeEnv -> Type)
  (λ (name gamma)
    (type-case TypeEnv gamma
      [mtEnv () (error 'typecheck "free identifier")]
      [aBind (name2 type rest)
             (if (equal? name name2)
                 type
                 (lookup-type name rest))])))



;; ----------------------------------------------------------------------

;; test for type checker

;; former tests

(test (typecheck-expr (parse `{{{fun {f : (number -> number)}
                                     {fun {x : number} {f x}}} ; `((number -> number) -> (number -> number))
                                {fun {x : number} {+ x 5}} ; number -> number
                                } ; (number -> number)
                               5}))
      (parse-type `number))


;; tests for if expression


(test (typecheck-expr (parse `{if {= 3 2} 4 5}))
      (parse-type `number))

(test/exn (typecheck-expr (parse `{if 3 4 5}))
      "expected boolean")

(test/exn (typecheck-expr (parse `{if {= 3 2} {= 3 3} 5}))
      "type mismatch")

(test (typecheck-expr (parse `{if {= 3 2} {= 3 4} {= 6 7}}))
      (parse-type `boolean))


;; tests for list expression


(test (typecheck-expr (parse `{nil number}))
      (parse-type `{listof number}))

(test (typecheck-expr (parse `{nil boolean}))
      (parse-type `{listof boolean}))

(test (typecheck-expr (parse `{cons {fun {f : (number -> number)}
                                     {fun {x : number} {f x}}} {nil ((number -> number) -> (number -> number))}}))
      (parse-type `{listof ((number -> number) -> (number -> number))}))

(test (typecheck-expr (parse `{first {cons {fun {f : (number -> number)}
                                                {fun {x : number} {f x}}} {nil ((number -> number) -> (number -> number))}}}))
      (parse-type `((number -> number) -> (number -> number))))


(test (typecheck-expr (parse `{rest {cons {fun {f : (number -> number)}
                                                {fun {x : number} {f x}}} {nil ((number -> number) -> (number -> number))}}}))
      (parse-type `{listof ((number -> number) -> (number -> number))}))


(test/exn (typecheck-expr (parse `{first 1}))
          "expected list")

(test/exn (typecheck-expr (parse `{rest 1}))
          "expected list")

(test (typecheck-expr (parse `{empty? {nil number}}))
      (parse-type `boolean))

(test/exn (typecheck-expr (parse `{empty? 1}))
          "expected list")

(test (typecheck-expr (parse `{get {cons 1 {nil number}} 0}))
      (parse-type `number))

(test (typecheck-expr (parse `{cons false {cons true {nil boolean}}}))
      (parse-type `{listof boolean}))

(test/exn (typecheck-expr (parse `{get {cons 1 {nil number}} true}))
      "expected number")

(test/exn (typecheck-expr (parse `{get 2 0}))
      "expected list or vector")

(test (typecheck-expr (parse `{length {cons 1 {nil number}}}))
      (parse-type `number))

(test (typecheck-expr (parse `{length {cons false {cons true {nil boolean}}}}))
      (parse-type `number))

(test/exn (typecheck-expr (parse `{length 2}))
      "expected list or vector")

;; tests for vector expression

(test (typecheck-expr (parse `{make-vector 3 4}))
      (parse-type `{vectorof number}))

(test/exn (typecheck-expr (parse `{make-vector true 4}))
      "expected number")

(test (typecheck-expr (parse `{make-vector 4 false}))
      (parse-type `{vectorof boolean}))

(test (typecheck-expr (parse `{make-vector 4 {fun {f : (number -> number)}
                                                  {fun {x : number} {f x}}}}))
      (parse-type `{vectorof ((number -> number) -> (number -> number))}))

(test (typecheck-expr (parse `{set {make-vector 4 5} 2 5}))
      (parse-type `number))

(test/exn (typecheck-expr (parse `{set {make-vector 4 5} 2 true}))
      "type mismatch")

(test/exn (typecheck-expr (parse `{set {make-vector 4 5} true 3}))
      "expected number")

(test (typecheck-expr (parse `{get {make-vector 4 5} 0}))
      (parse-type `number))

(test/exn (typecheck-expr (parse `{get {make-vector 4 5} true}))
      "expected number")

(test (typecheck-expr (parse `{length {make-vector 4 5}}))
      (parse-type `number))
