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

(define-type Tree
    [positive-leaf (val natural?)]
    [negative-leaf (val natural?)]
    [interior-node (left Tree?) (right Tree?)])

(print-only-errors)

; contatins?
(define (contains? t v)
  (type-case Tree t
    [positive-leaf (val) (equal? val v)]
    [negative-leaf (val) (equal? val (- 0 v))]
    [interior-node (left right)(or (contains? left v) (contains? right v))]))


(test (contains?
       (interior-node (interior-node (positive-leaf 5)
                       (negative-leaf 4))
                                (positive-leaf 3))
                                -4)
true)

(test (contains?
       (interior-node (interior-node (positive-leaf 5)
                       (negative-leaf 4))
                                (positive-leaf 3))
                                3)
true)

(test (contains?
       (interior-node (interior-node (positive-leaf 5)
                       (negative-leaf 4))
                                (positive-leaf 3))
                                5)
true)

(test (contains?
       (interior-node (interior-node (positive-leaf 5)
                       (negative-leaf 4))
                                (positive-leaf 3))
                                0)
false)

; smallest
(define (smallest t)
  (type-case Tree t
    [positive-leaf (val) val]
    [negative-leaf (val) (- 0 val)]
    [interior-node (left right)
                   (if (< (smallest left) (smallest right))
                       (smallest left)
                       (smallest right))]))

(test (smallest
       (interior-node (interior-node (positive-leaf 5)
                       (negative-leaf 4))
                                (positive-leaf 3)))
-4)

(test (smallest
       (interior-node (interior-node (positive-leaf 5)
                       (negative-leaf 4))
                                (negative-leaf 9)))
-9)

(test (smallest
       (interior-node (interior-node (positive-leaf 5)
                       (positive-leaf 4))
                                (positive-leaf 3)))
3)

(test (smallest
       (interior-node (interior-node (positive-leaf 0)
                       (positive-leaf 4))
                                (positive-leaf 3)))
0)

; balance?
(define (sum t)
  (type-case Tree t
    [positive-leaf (val) val]
    [negative-leaf (val) (- 0 val)]
    [interior-node (left right)
                   (+ (sum left) (sum right))]))

(define (balanced? t)
  (zero? (sum t)))

(test (balanced?
       (interior-node (interior-node (positive-leaf 0)
                       (positive-leaf 4))
                                (positive-leaf 3)))
false)

(test (balanced?
       (interior-node (interior-node (positive-leaf 0)
                       (negative-leaf 4))
                                (positive-leaf 3)))
false)

(test (balanced?
       (interior-node (interior-node (positive-leaf 0)
                       (negative-leaf 3))
                                (positive-leaf 3)))
true)

(test (balanced?
       (interior-node (interior-node (positive-leaf 4)
                       (interior-node (positive-leaf 3)
                                      (negative-leaf 4)))
                       (negative-leaf 3)))
true)

(test (balanced?
       (interior-node (positive-leaf 0) (positive-leaf 0)))
 true)


; deep-balanced?
(define (deep-balanced? t)
  (type-case Tree t
    [positive-leaf (val) true]
    [negative-leaf (val) true]
    [interior-node (left right)
                   (and
                    (zero? (+ (sum left) (sum right)))
                    (and
                     (deep-balanced? left)
                     (deep-balanced? right)))]))

(test (deep-balanced?
       (interior-node (interior-node (positive-leaf 4)
                       (interior-node (positive-leaf 3)
                                      (negative-leaf 4)))
                       (negative-leaf 3)))
false)

(test (deep-balanced?
       (interior-node (interior-node (positive-leaf 0)
                       (interior-node (positive-leaf 3)
                                      (negative-leaf 3)))
                       (negative-leaf 0)))
true)


(test (deep-balanced?
       (interior-node (positive-leaf 3)
                       (negative-leaf 3)))
true)

(test (deep-balanced?
       (interior-node (positive-leaf 3)
                       (negative-leaf 2)))
false)

(test (deep-balanced?
       (interior-node (interior-node (positive-leaf 3)
                                     (negative-leaf 3))
                       (negative-leaf 0)))
true)

; negate
(define (negate t)
  (type-case Tree t
    [positive-leaf (val) (negative-leaf val)]
    [negative-leaf (val) (positive-leaf val)]
    [interior-node (left right)
                   (interior-node (negate left)(negate right))]))


(test (equal?
       (negate
        (interior-node (interior-node (positive-leaf 5)
                                     (negative-leaf 3))
                       (negative-leaf 7)))
       (interior-node (interior-node (negative-leaf 5)
                                     (positive-leaf 3))
                       (positive-leaf 7)))
true)

(test (equal?
       (negate
        (interior-node (interior-node (positive-leaf 5)
                                     (negative-leaf 3))
                       (negative-leaf 7)))
       (interior-node (interior-node (negative-leaf 5)
                                     (positive-leaf 3))
                       (negative-leaf 7)))
false)

; add
(define (add t v)
  (type-case Tree t
    [positive-leaf (val) (if (< val (- 0 v))
                             (negative-leaf (- 0 (+ val v)))
                             (positive-leaf (+ val v)))]
    [negative-leaf (val) (if (< v val)
                             (negative-leaf (- val v))
                             (positive-leaf (- v val)))]
    [interior-node (left right)
                   (interior-node (add left v)(add right v))]))


(test (equal?
       (add
        (interior-node (interior-node (positive-leaf 5)
                                     (negative-leaf 8))
                       (negative-leaf 3)) 5)
       (interior-node (interior-node (positive-leaf 10)
                                     (negative-leaf 3))
                       (positive-leaf 2)))
true)

(test (add (interior-node (positive-leaf 0) (positive-leaf 0)) -1)
      (interior-node (negative-leaf 1) (negative-leaf 1)))

(test (add (interior-node (positive-leaf 3) (positive-leaf 5)) -4)
      (interior-node (negative-leaf 1) (positive-leaf 1)))




; positive-thinking
(define (positive-thinking t)
  (if (is-negative? (build-positive t))
      false
      (build-positive t)))


(define (is-negative? t)
  (type-case Tree t
    [negative-leaf (val) true]
    [else false]))


(define (build-positive t)
  (type-case Tree t
    [positive-leaf (val) t]
    [negative-leaf (val) t]
    [interior-node (left right)
                   (cond
                     [(and (is-negative? (build-positive left)) (is-negative? (build-positive right))) (negative-leaf 0)]
                     [(is-negative? (build-positive left)) (build-positive right)]
                     [(is-negative? (build-positive right)) (build-positive left)]
                     [else (interior-node (build-positive left) (build-positive right))])]))

;; smoke test

;;; test 1
(test (equal?
       (positive-thinking (negative-leaf 3))
       false)
true)


;;; test 2
(test (equal?
       (positive-thinking (positive-leaf 3))
       (positive-thinking (positive-leaf 3)))
true)

;;; test 3
(test (equal?
       (positive-thinking (interior-node
                           (negative-leaf 4)
                           (negative-leaf 5)))
       false
       )
true)

;;; test 4
(test (equal?
       (positive-thinking (interior-node
                           (negative-leaf 4)
                           (positive-leaf 5)))
       (positive-leaf 5)
       )
true)


;;; test 5
(test (equal?
       (positive-thinking (interior-node
                           (interior-node
                            (negative-leaf 6)
                            (negative-leaf 7))
                           (positive-leaf 5)))
       (positive-leaf 5)
       )
true)


;;; test 6
(test (equal?
       (positive-thinking (interior-node
                           (interior-node
                            (negative-leaf 6)
                            (positive-leaf 7))
                           (positive-leaf 5)))
       (interior-node
        (positive-leaf 7)
        (positive-leaf 5))
       )
true)


;;; test 7
(test (equal?
       (positive-thinking (interior-node
                           (interior-node
                            (negative-leaf 6)
                            (positive-leaf 7))
                           (negative-leaf 5)))
       (positive-leaf 7)
       )
true)


;;; test 8
(test (equal?
       (positive-thinking (interior-node
                           (interior-node
                            (negative-leaf 6)
                            (negative-leaf 7))
                           (interior-node
                            (positive-leaf 9)
                            (positive-leaf 10))))
       (interior-node
        (positive-leaf 9)
        (positive-leaf 10))
       )
true)


;;; test 9
(test (equal?
       (positive-thinking (interior-node
                           (interior-node
                            (positive-leaf 6)
                            (negative-leaf 7))
                           (interior-node
                            (positive-leaf 9)
                            (negative-leaf 10))))
       (interior-node
        (positive-leaf 6)
        (positive-leaf 9))
       )
true)