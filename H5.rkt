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

;; type EFAE
(define-type EFAE
  [num (n number?)]
  [add (lhs EFAE?)
       (rhs EFAE?)]
  [sub (lhs EFAE?)
       (rhs EFAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body EFAE?)]
  [app (fun-expr EFAE?)
       (arg-expr EFAE?)]
  [if0 (tst EFAE?)
       (thn EFAE?)
       (els EFAE?)]
  [throw (tag symbol?)
         (throw-expr EFAE?)]
  [try-catch (try-body EFAE?)
             (tag symbol?)
             (exn-name symbol?)
             (catch-body EFAE?)])

(define-type EFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body EFAE?)
            (ds DefSub?)]
  [exceptionV (tag symbol?)
              (value EFAE-Value?)])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value EFAE-Value?)
         (rest DefSub?)])

;; ----------------------------------------------------------------------------

;; parser

(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid EFAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp "add" 3)
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp "sub" 3)
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(fun)
            (check-pieces s-exp "fun" 3)
            (check-pieces (second s-exp) "parameter list" 1)
            (fun (first (second s-exp))
                 (parse (third s-exp)))]
           [(if0)
            (check-pieces s-exp "if0" 4)
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [(throw)
            (check-pieces s-exp "throw" 3)
            (throw (second s-exp)
                   (parse (third s-exp)))]
           [(try)
            (check-pieces s-exp "try" 3)
            (define catch-expr (third s-exp))
            (check-pieces catch-expr "catch" 3)
            (define tag-expr (second catch-expr))
            (check-pieces tag-expr "tag" 4)
            (try-catch (parse (second s-exp))
                       (second tag-expr)
                       (fourth tag-expr)
                       (parse (third catch-expr)))]
           [(with)
            ;; extension
            (check-pieces s-exp "with" 3)
            (app (fun (first (second s-exp))
                      (parse (third s-exp)))
                 (parse (second (second s-exp))))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "expected EFAE got ~a" s-exp)]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;; ----------------------------------------------------------------------------

;; test for parser
(test (parse `{+ 2 {try {+ 4 {throw x 5}}
                        {catch {tag x as e} {+ 3 e}}}})
      (add (num 2)
           (try-catch (add (num 4) (throw `x (num 5)))
                      `x
                      `e
                      (add (num 3) (id `e)))))

(test (parse `{+ 2 {try {+ 4 {throw x 5}}
                        {catch {tag x as e} {if0 e 1 2}}}})
      (add (num 2)
           (try-catch (add (num 4) (throw `x (num 5)))
                      `x
                      `e
                      (if0 (id `e) (num 1) (num 2)))))


(test (parse `{with {f {fun {x} {throw a {+ x 1}}}}
                    {try {throw a {+ {f 3} 10}}
                         {catch {tag a as j} {+ j 5}}}})
      (app (fun `f (try-catch (throw `a (add (app (id `f) (num 3))
                                             (num 10)))
                              `a
                              `j
                              (add (id `j) (num 5))))
           (fun `x (throw `a (add (id `x) (num 1))))))

;; ----------------------------------------------------------------------------

(define (interp-expr a-efae)
  (interp a-efae
          (mtSub)
          (λ (final-val)
            (type-case EFAE-Value final-val
              [numV (n) n]
              [closureV (param-name body ds) `function]
              [exceptionV (tag value)
                          (error `interp "missing catch at ~a" tag)]))
          (λ (final-val)
            (error `interp "missing catch"))))


(define (interp a-efae ds k ret-k)
  (type-case EFAE a-efae
    [num (n) (k (numV n))]
    [id (name) (k (lookup name ds))]
    [fun (param-name body) (k (closureV param-name body ds))]
    [add (l r) (numop + l r ds k ret-k)]
    [sub (l r) (numop - l r ds k ret-k)]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (λ (fun-val)
                   (interp arg-expr ds
                           (λ (arg-val)
                             (type-case EFAE-Value fun-val
                               [closureV (param-name body closed-ds)
                                         (interp body
                                                 (aSub param-name
                                                       arg-val
                                                       closed-ds)
                                                 ;; (λ (ret-val)
                                                 ;;   (k ret-val))
                                                 k
                                                 ret-k)]
                               [else (error 'interp "expected function, got: ~a" fun-val)]))
                           ret-k))
                 ret-k)]
    ;; new added for efae
    [if0 (tst thn els)
         (interp tst ds (λ (tst-val)
                          (type-case EFAE-Value tst-val
                            [numV (n)
                                  (if (zero? n)
                                      (interp thn ds k ret-k)
                                      (interp els ds k ret-k))]
                            [closureV (param-name body ds)
                                      (interp els ds k ret-k)]
                            [exceptionV (tag value)
                                        (ret-k tst-val)]))
                 ret-k)]
    [throw (tag throw-expr)
           (interp throw-expr ds
                   (λ (throw-value)
                     (ret-k (exceptionV tag throw-value)))
                   ret-k)
           ]
    [try-catch (try-body tag exn-name catch-body)
               (interp try-body ds k (λ (try-val)
                                       (type-case EFAE-Value try-val
                                         [exceptionV (tag-val value)
                                                     (if (equal? tag tag-val)
                                                         (interp catch-body
                                                                 (aSub exn-name
                                                                       value
                                                                       ds)
                                                                 k
                                                                 ret-k)
                                                         (ret-k try-val))]
                                         [else (error `interp "interp crashes at ~a" a-efae)])))]
    ))





;; ----------------------------------------------------------------------------

;; some helper

;; numop : (number? number? -> number?) KFAE? KFAE? DefSub?
;;         (KFAE-Value? -> KFAE-Value?)
;;         (KFAE-Value? -> KFAE-Value?)
;;            -> KFAE-Value?
(define (numop op l r ds k ret-k)
  (interp l ds
          (λ (l-val)
            (interp r ds
                    (λ (r-val)
                      (unless (numV? l-val)
                        (error 'interp "expected number, got: ~a" l-val))
                      (unless (numV? r-val)
                        (error 'interp "expected number, got: ~a" r-val))
                      (k (numV (op (numV-n l-val) (numV-n r-val)))))
                    ret-k))
          ret-k))

;; lookup : symbol? DefSub? -> KFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error "free identifier")]
    [aSub (name2 value rest)
          (if (equal? name name2)
              value
              (lookup name rest))]))

;; ----------------------------------------------------------------------------

;; test from instrction


(test (interp-expr (parse `{+ 2 {try {+ 4 {throw x 5}}
                                     {catch {tag x as e} {+ 3 e}}}}))
      10)

(test (interp-expr (parse `{try {+ 2 {try {+ 3 {throw y 5}}
                                          {catch {tag x as e} {+ 6 e}}}}
                                {catch {tag y as e} {+ 10 e}}}))
      15)

(test/exn (interp-expr (parse `{try {throw a 1} {catch {tag a as b} {throw a 1}}}))
          "missing catch")

(test (interp-expr (parse `{try {try {throw a 1} {catch {tag a as b} {throw a 1}}} {catch {tag a as b} {+ b 5}}}))
      6)

(test (interp-expr (parse `{try {try {throw a {throw c 2}} {catch {tag a as b} b}} {catch {tag c as b} {+ b 5}}}))
      7)

(test/exn (interp-expr (parse `{try {try {throw a {throw c 2}} {catch {tag a as b} b}} {catch {tag d as b} {+ b 5}}}))
          "missing catch")


(test (interp-expr (parse `{with {f {fun {x} {throw a {+ x 1}}}}
                                 {try {throw a {+ {f 3} 10}}
                                      {catch {tag a as j} {+ j 5}}}}))
      9)

(test (interp-expr (parse `{with {f {fun {x} {+ x 1}}}
                                 {try {throw a {+ {f 3} 10}}
                                      {catch {tag a as j} {+ j 5}}}}))
      19)

(test (interp-expr (parse `{with {f {fun {x} {+ x 1}}}
                                 {f 3}}))
      4)

(test (interp-expr (parse `{fun {x} {+ x 1}}))
      `function)

(test (interp-expr (parse `(if0 0 1 2)))
      1)

(test (interp-expr (parse `(if0 1 1 2)))
      2)

(test (interp-expr (parse `(+ (if0 0 (+ 10 6) 2) 5)))
      21)

(test (interp-expr (parse `(+ (if0 1 (+ 10 6) 2) 5)))
      7)

(test (interp-expr (parse `(+ ((fun (x) (if0 x 2 3)) 0) 10)))
      12)

(test (interp-expr (parse `(+ ((fun (x) (if0 x 2 3)) 1) 10)))
      13)

(test (interp-expr (parse `(+ ((fun (x) (if0 (fun (y) (+ y 1)) 2 3)) 1) 10)))
      13)

(test (interp-expr
       (parse `(if0 (try (+ 1 (if0 (throw a 1) 1 2)) (catch (tag a as x) (+ x 1))) 0 1)))
      1)

(test (interp-expr
       (parse `(if0 (try (+ 1 (if0 (throw a 1) 1 2)) (catch (tag a as x) 0)) 0 1)))
      0)