#lang plai/gc2/collector

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
;; ----------------------------------------------------------------------

;; some useful "macro" in the heap
;; lower half heap: [4, (heap-size) / 2 + 1] higher half heap: [(heap-size) / 2 + 2, (heap-size) - 1]

(define (address-pointer) (heap-ref 0))
(define (flop) (heap-ref 1))
(define (flip-flop)
  (if (= (flop) 1)
      (heap-set! 1 0)
      (heap-set! 1 1)))
(define (front) (heap-ref 2))
(define (back) (heap-ref 3))
(define (upper-bound) (if (= (flop) 0)
                          (+ 2 (/ (heap-size) 2))
                          (heap-size)))
(define (lower-bound) (if (= (flop) 0)
                          4
                          (+ 2 (/ (heap-size) 2))))

;; ----------------------------------------------------------------------
(define (init-allocator)
  (when (= (remainder (heap-size) 2) 1)
    (error `init-allocator "heap-size must be an even number"))
  (for ([i (in-range 0 (heap-size))])
    (heap-set! i 'free))
  (heap-set! 0 4)
  (heap-set! 1 0))



;; find-free-spaces : integer? -> (or/c address #f)
(define (find-free-spaces n)
  (define addr (heap-ref 0))
  (cond
    [(< (+ addr n) (upper-bound))
     addr]
    [else #f]))



;; maybe-roots? is one of:
;; - root?
;; - #f
;; - (listof maybe-roots?)

;; malloc : size maybe-roots? maybe-roots? -> address
(define (malloc n roots1 roots2)
  (define address (find-free-spaces n))
  (cond [address
         (heap-set! 0 (+ address n))
         address]
        [else
         ;; (displayln address)
         ;; (read-line)
         (collect-garbage roots1 roots2)
         ;; (read-line)
         (define retry-address (find-free-spaces n))
         (cond [retry-address
                (heap-set! 0 (+ retry-address n))
                retry-address]
               [else
                (error `malloc "out of memory")])]))

;; collect-garbage maybe-roots? maybe-roots?
(define (collect-garbage roots1 roots2)
  (validate-heap 4)
  ;; manage heap state
  (flip-flop)
  (heap-set! 2 (lower-bound))
  (heap-set! 3 (lower-bound))
  
  (traverse/roots (get-root-set))
  (traverse/roots roots1)
  (traverse/roots roots2)
  (traverse/front)
  ;; set the addr to back of queue
  (heap-set! 0 (back))
  (clear-half)
  (validate-heap 4))

(define (clear-half)
  (flip-flop)
  (for ([i (in-range (lower-bound) (upper-bound))])
    (heap-set! i `free))
  (flip-flop))

;; traverse/front : location? -> void
(define (traverse/front)
  (if (= (front) (back))
      (void)
      (case (heap-ref (front))
        [(flat)
         (heap-set! 2 (+ (front) 2))
         (traverse/front)]
        [(cons)
         (heap-set! (+ (front) 1) (move-child (heap-ref (+ (front) 1))))
         (heap-set! (+ (front) 2) (move-child (heap-ref (+ (front) 2))))
         (heap-set! 2 (+ (front) 3))
         (traverse/front)]
        [(clos)
         (heap-set! (+ (front) 1) (heap-ref (+ (front) 1)))
         (heap-set! (+ (front) 2) (heap-ref (+ (front) 2)))
         (for ([i (in-range (heap-ref (+ (front) 2)))])
           (heap-set! (+ (front) 3 i) (move-child (heap-ref (+ (front) 3 i)))))
         (heap-set! 2 (+ (front) 3 (heap-ref (+ (front) 2))))
         (traverse/front)]
        [(free)
         (error `traverse/front "dangling pointer at ~a" (front))]
        [else
         (error `traverse/front "unexpected tag at ~a" (heap-ref (front)))])))

;; move-child : location? -> location?
(define (move-child ptr)
  (define new-addr (copy-object ptr))
  (set-forward ptr new-addr)
  new-addr)


;; traverse/roots : maybe-roots? -> void
(define (traverse/roots roots)
  (cond
    [(list? roots)
     (for ([r (in-list roots)])
       (traverse/roots r))]
    [(root? roots)
     (define new-addr (move-child (read-root roots)))
     (set-root! roots new-addr)
     (void)]
    [(false? roots)
     (void)]
    [else
     (error `traverse/roots "unexpected roots at ~a" roots)]))


;; copy-object : location? -> loaction?
(define (copy-object ptr)
  (case (heap-ref ptr)
    [(flat)
     (heap-set! (back) (heap-ref ptr))
     (heap-set! (+ (back) 1) (heap-ref (+ ptr 1)))
     (define new-address (back))
     (heap-set! 3 (+ new-address 2))
     new-address]
    [(cons)
     (heap-set! (back) (heap-ref ptr))
     (heap-set! (+ (back) 1) (heap-ref (+ ptr 1)))
     (heap-set! (+ (back) 2) (heap-ref (+ ptr 2)))
     (define new-address (back))
     (heap-set! 3 (+ new-address 3))
     new-address]
    [(clos)
     (heap-set! (back) (heap-ref ptr))
     (heap-set! (+ (back) 1) (heap-ref (+ ptr 1)))
     (heap-set! (+ (back) 2) (heap-ref (+ ptr 2)))
     (for ([i (in-range (heap-ref (+ ptr 2)))])
       (heap-set! (+ (back) i 3) (heap-ref (+ ptr i 3))))
     (define new-address (back))
     (heap-set! 3 (+ new-address 3 (heap-ref (+ ptr 2))))
     new-address]
    [(forw)
     (heap-ref (+ ptr 1))]
    [(free)
     (error `copy-object "dangling pointer at ~a" ptr)]
    [else
     (error `copy-object "unepected tag at ~a" ptr)]))

;; set-forward : location? location? -> void?
(define (set-forward ptr dst)
  (case (heap-ref ptr)
    [(forw)
     (unless (= dst (heap-ref (+ ptr 1)))
       (error `set-foward "heap broken"))]
    [(clos flat cons)
     (heap-set! ptr `forw)
     (heap-set! (+ ptr 1) dst)
     (void)]
    [(free)
     (error `set-foward "dangling pointer at ~a" ptr)]
    [else
     (error `move-object "broken heap at pointer: ~a heap-value: ~a" ptr (heap-ref ptr))]))

(define (validate-heap start)
  (when (< start (heap-size))
    (case (heap-ref start)
      [(flat)
       (validate-heap (+ start 2))]
      [(cons)
       (check-valid-pointer-at (+ start 1))
       (check-valid-pointer-at (+ start 2))
       (validate-heap (+ start 3))]
      [(clos)
       (unless (natural? (heap-ref (+ start 2)))
         (error 'validate-heap "invalid number of clos free vars @ ~a" start))
       (for ([i (in-range 0 (heap-ref (+ start 2)))])
         (check-valid-pointer-at (+ start 3 i)))
       (validate-heap (+ start 3 (heap-ref (+ start 2))))]
      [(free)
       (validate-heap (+ start 1))]
      [(forw)
       (validate-heap (+ start 2))]
      [else
       (error 'validate-heap
              "unexpected tag @ ~a" start)])))

(define (check-valid-pointer-at addr)
  (define ptr (heap-ref addr))
  (unless (and (location? ptr)
               (>= ptr (lower-bound))
               (< ptr (upper-bound))
               (member (heap-ref ptr) '(flat cons clos)))
    (error 'validate-heap "invalid pointer @ ~a" addr)))

;; ----------------------------------------------------------------------

#|
flat:    ... | 'flat | <payload> | ...
|#
;; gc:alloc-flat : flat-value -> address
(define (gc:alloc-flat value)
  (define address (malloc 2 #f #f))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : address -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : address -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected flat @ ~a" address))
  (heap-ref (+ address 1)))


#|
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
|#
;; gc:cons : root root -> address
(define (gc:cons root1 root2)
  (define address (malloc 3 root1 root2))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : address -> boolean
(define (gc:cons? address)
  (equal? (heap-ref address) 'cons))
;; gc:first : address -> address
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected cons @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : address -> address
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected cons @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : address address -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected cons @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : address address -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected cons @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) -> address
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 3 (length free-vars)) free-vars #f))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (heap-set! (+ address 2) (length free-vars))
  (for ([fv (in-list free-vars)]
        [i  (in-naturals)])
    (heap-set! (+ address 3 i) (read-root fv)))
  address)
;; gc:closure? : address -> boolean
(define (gc:closure? address)
  (equal? (heap-ref address) 'clos))
;; gc:closure-code-ptr : address -> opaque-value
(define (gc:closure-code-ptr address)
  (unless (gc:closure? address)
    (error 'gc:closure-code-ptr "expected closure @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:closure-env-ref : address integer -> address
(define (gc:closure-env-ref address i)
  (unless (gc:closure? address)
    (error 'gc:closure-env-ref "expected closure @ ~a" address))
  (heap-ref (+ address 3 i)))
