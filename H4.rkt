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

(define-type SFAE
  [num (n number?)]
  [add (lhs SFAE?)
       (rhs SFAE?)]
  [sub (lhs SFAE?)
       (rhs SFAE?)]
  [id (name symbol?)]
  [fun (param-name symbol?)
       (body SFAE?)]
  [app (fun-expr SFAE?)
       (arg-expr SFAE?)]
  [newstruct (fields list?)]
  [getstruct (struct-expr SFAE?)
             (field-id symbol?)]
  [setstruct (struct-expr SFAE?)
             (field-id symbol?)
             (new-expr SFAE?)]
  [seqn (expr1 SFAE?)
        (expr2 SFAE?)])

;; ----------------------------------------------------------------------------

(define-type Store
  [mtSto]
  [aSto (address integer?)
        (value SFAE-Value?)
        (rest Store?)])

(define-type Value*Store
  [v*s (v SFAE-Value?)
       (s Store?)])

(define-type SFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body SFAE?)
            (ds DefSub?)]
  [structV (id-address list?)])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value SFAE-Value?)
         (rest DefSub?)])
;; ----------------------------------------------------------------------------

;; parser: s-exp? -> SFAE?

(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid SFAE"))
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
           [(struct)
            (newstruct (map (lambda (pair)
                              (check-pieces pair "struct field" 2)
                              (list (first pair) (parse (second pair)))) (rest s-exp)))]
           [(get)
            (check-pieces s-exp "get" 3)
            (getstruct (parse (second s-exp))
                       (third s-exp))]
           [(set)
            (check-pieces s-exp "set" 4)
            (setstruct (parse (second s-exp))
                       (third s-exp)
                       (parse (fourth s-exp)))]
           [(seqn)
            (check-pieces s-exp "seqn" 3)
            (seqn (parse (second s-exp))
                  (parse (third s-exp)))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "expected SFAE got ~a" s-exp)]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;; ----------------------------------------------------------------------------

;; test for parser

(test (parse '{{fun {r}
                    {get r x}}
               {struct {x 1}}})
      (app (fun `r (getstruct (id `r) `x))
           (newstruct (list (list `x (num 1))))))


(test (parse '{{fun {r}
                    {seqn
                     {set r x 5}
                     {get r x}}}
               {struct {x 1}}})
      (app (fun `r (seqn (setstruct (id `r) `x (num 5))
                         (getstruct (id `r) `x)))
           (newstruct (list (list `x (num 1))))))


(test (parse '{set {struct {x 42} {y 32}} x 2})
      (setstruct (newstruct (list (list `x (num 42)) (list `y (num 32))))
                 `x
                 (num 2)))

(test (parse '{set {struct {x 42}} x 2})
      (setstruct (newstruct (list (list `x (num 42))))
                 `x
                 (num 2)))

;; ----------------------------------------------------------------------------

;; counting heap size
(define (size s)
  (cond
    [(struct? s)
     (size (struct->vector s))]
    [(vector? s)
     (for/fold ([tot 0])
               ([ele (in-vector s)])
       (+ tot (size ele)))]
    [(pair? s)
     (+ 1 (size (car s)) (size (cdr s)))]
    [else 1]))
;; ----------------------------------------------------------------------------

;; interp-expr SFAE? -> number or `function or `struct
(define (interp-expr a-sfae)
  (type-case SFAE-Value (v*s-v (interp a-sfae
                                       (mtSub)
                                       (mtSto)))
    [numV (n) n]
    [closureV (param-name body ds) `function]
    [structV (id-address) `struct]))

;; interp SFAE? -> SFAE-value
(define (interp a-sfae ds st)
  (printf "heap size is ~a\n" (size st))
  (type-case SFAE a-sfae
    [num (n) (v*s (numV n)
                  st)]
    [add (l r) (numop + l r ds st)]
    [sub (l r) (numop - l r ds st)]
    [id (name)
        (v*s (lookup name ds)
             st)]
    [fun (param-name body)
         (v*s (closureV param-name
                        body
                        ds)
              st)]
    [app (fun-expr arg-expr)
         (interp-two fun-expr arg-expr ds st
                     (λ (fun-val arg-val st3)
                       (type-case SFAE-Value fun-val
                         [closureV (param-name body body-ds)
                                   (interp body
                                           (aSub param-name
                                                 arg-val
                                                 body-ds)
                                           st3)]
                         [else (error 'interp
                                      "expected function, got: ~a" fun-val)])))]
    ;; TODO -------------
    ;; fields : (listof (listof symbol? SFAE?))
    [newstruct (fields)
               (interp-fields fields empty ds st (lambda (fields-val st3)
                                                   (v*s (structV fields-val)
                                                        st3)))]
    [getstruct (struct-expr field-id)
               (type-case Value*Store (interp struct-expr ds st)
                 [v*s (v1 st1)
                      (unless (structV? v1)
                        (error `interp "expected struct at ~a" v1))
                      (v*s (lookup-store (search-fields (structV-id-address v1) field-id) st1)
                           st1)])]
    [setstruct (struct-expr field-id new-expr)
               (interp-two struct-expr
                           new-expr
                           ds
                           st
                           (lambda (v1 v2 st3)
                             (unless (structV? v1)
                               (error `interp "expected struct at ~a" v1))
                             (define old-val (lookup-store (search-fields (structV-id-address v1) field-id) st3))
                             (define st4 (rep-store (search-fields (structV-id-address v1) field-id) v2 st3))
                             (v*s old-val
                                  st4)))]
    ;; -------------
    [seqn (expr1 expr2)
          (interp-two expr1 expr2 ds st
                      (λ (v1 v2 st3)
                        (v*s v2 st3)))]))

;; ----------------------------------------------------------------------------

;; helpers


;; search-fields -> integer?
(define (search-fields fields id)
  (when (empty? fields)
    (error `interp "unknown field for ~a" id))
  (if (equal? (first (first fields)) id)
      (second (first fields))
      (search-fields (rest fields) id)))


;; malloc : Store? -> integer?
(define (malloc st)
  (+ (max-address st) 1))
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (address v rest)
          (max address
               (max-address rest))]))

;; lookup-store : integer? Store? -> BFAE-Value?
(define (lookup-store address st)
  (type-case Store st
    [mtSto ()
           ;; This should never happen!
           (error 'interp "dangling pointer: ~a" address)]
    [aSto (address2 val rest)
          (if (= address address2)
              val
              (lookup-store address rest))]))

;; rep-store : integer? Store? -> Store?
(define (rep-store address new-val st)
  (type-case Store st
    [mtSto () (mtSto)]
    [aSto (address2 val rest)
          (define st2 (rep-store address new-val rest))
          (if (= address address2)
              (aSto address2
                    new-val
                    st2)
              (aSto address2
                    val
                    st2))]))


;; interp-two 
(define (interp-two expr1 expr2 ds st finish)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (v1 st2)
         (type-case Value*Store (interp expr2 ds st2)
           [v*s (v2 st3)
                (finish v1 v2 st3)])]))

;; interp-all (id, SFAE)* ds st function
(define (interp-fields fields-expr fields-val ds st finish)
  (if (empty? fields-expr)
      (finish fields-val st)
      (type-case Value*Store (interp (second (first fields-expr)) ds st)
        [v*s (v1 st1)
             (define new-addr (malloc st1))
             (interp-fields (rest fields-expr)
                            (cons (list (first (first fields-expr)) new-addr) fields-val)
                            ds
                            (aSto new-addr
                                  v1
                                  st1)
                            finish)])))

;; numop : (number? number? -> number?) BFAE? BFAE? DefSub? Store? -> Value*Store?
(define (numop op l r ds st)
  (interp-two l r ds st
              (λ (l-val r-val st3)
                (unless (numV? l-val)
                  (error 'interp "expected number, got ~a" l-val))
                (unless (numV? r-val)
                  (error 'interp "expected number, got ~a" r-val))
                (v*s (numV (op (numV-n l-val) (numV-n r-val)))
                     st3))))

;; lookup : symbol? DefSub? -> BFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))
;; ----------------------------------------------------------------------------

;; interp test

(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
          "unknown field")

(test/exn (interp-expr (parse '{struct {z {get 0 y}}}))
          "expected struct")


(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {struct {x 1}}}))
      1)


(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {struct {x 1}}}))
      5)

(test (interp-expr (parse '{set {struct {x 42}} x 2}))
      42)


(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}

                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}
                            {struct {a 3} {b 4}}}))      ; r1 ; r2
      5)




(test (interp-expr (parse `((fun (b) (seqn
                                      (struct
                                        (a (seqn (set b x (+ (get b x) (get b x))) 111))
                                        (b (seqn (set b x (+ (get b x) 1)) 222))
                                        (c (seqn (set b x (+ (+ (get b x) (get b x)) (get b x))) 222))
                                        (d (seqn (set b x (+ (get b x) 2)) 222)))
                                      (get b x)))
                            (struct (x 1111)))))
      6671)

(test/exn (interp-expr (parse `(set 1 x (struct (x 2)))))
          "expected struct")


;; ----------------------------------------------------------------------------



