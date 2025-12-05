; Complex satisfiable QF_LIA SMT-LIB file
; Logic: QF_LIA (Quantifier-Free Linear Integer Arithmetic)
; This file uses many linear integer equalities/inequalities, ite expressions,
; and Boolean combinations while remaining in the QF_LIA fragment.
; It is intentionally syntactically varied and satisfiable.

(set-logic QF_LIA)

; Declare integer variables
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)
(declare-const x8 Int)
(declare-const x9 Int)
(declare-const x10 Int)
(declare-const x11 Int)
(declare-const x12 Int)
(declare-const x13 Int)
(declare-const x14 Int)
(declare-const x15 Int)
(declare-const x16 Int)
(declare-const x17 Int)
(declare-const x18 Int)
(declare-const x19 Int)
(declare-const x20 Int)

; --- Anchors to ensure satisfiability
(assert (= x1 5))    ; anchor x1
(assert (= x6 13))   ; anchor x6 chosen to satisfy later bounds

; --- Linear integer relations (all linear, no nonlinear variable multiplications)
(assert (= x2 (+ x1 3)))                          ; x2 = x1 + 3
(assert (= x3 (- (* 2 x1) x2)))                   ; x3 = 2*x1 - x2
; piecewise integer: x4 = if x1>0 then x1-3 else -x1+5
(assert (=> (> x1 0) (= x4 (- x1 3))))
(assert (=> (<= x1 0) (= x4 (+ (- x1) 5))))
(assert (= x5 (+ x2 x3 x4)))                      ; x5 = x2 + x3 + x4

; bounds on x6 using x5
(assert (>= x6 (+ x5 1)))                         ; x6 >= x5 + 1
(assert (<= x6 30))                               ; x6 <= 30

; --- Second block: chained integer definitions creating structure
(assert (= x7 (- (+ x1 x2) x3)))                  ; x7 = x1 + x2 - x3
(assert (= x9 (+ x7 2)))                          ; x9 = x7 + 2
(assert (= x8 (- x9 2)))                          ; x8 = x9 - 2
(assert (= x10 (- 10 (+ x7 x8))))                 ; x10 = 10 - (x7 + x8)
; x11 = x10-2 if x10>0 else x10+5
(assert (=> (> x10 0) (= x11 (- x10 2))))
(assert (=> (<= x10 0) (= x11 (+ x10 5))))
(assert (= x12 (- 3 x11)))                        ; x12 = 3 - x11

; a nontrivial summed invariant (consistent with the anchored solution)
(assert (= (+ x7 x8 x9 x10 x11 x12) 26))

; --- Third block: more piecewise integer relationships
(assert (= x13 (- x6 x1)))                        ; x13 = x6 - x1
(assert (= x14 (- x13 2)))                        ; x14 = x13 - 2
(assert (= x15 (+ x14 5)))                        ; x15 = x14 + 5
(assert (=> (>= x15 3) (= x16 3)))
(assert (=> (< x15 3) (= x16 x15)))
(assert (= x17 (+ (* -2 x16) 7)))                 ; x17 = -2*x16 + 7
(assert (= x18 (- x17 1)))                        ; x18 = x17 - 1
(assert (= x20 (+ x19 1)))                        ; small offset added to x19

; --- Extra linear constraints to increase syntactic complexity (all consistent)
(assert (>= x20 0))
(assert (< x20 10))
(assert (> x5 4))
(assert (< x3 5))
(assert (or (< x1 0) (> x1 0))) ; tautological for nonzero x1, mixes Boolean structure

; A final balanced linear equality (crafted to be consistent with anchors and definitions)
(assert (= (+ (* 2 x1) (* -1 x2) (* 3 x11) (* -1 x14)) -25))
; This corresponds to: 2*x1 - x2 + 3*x11 - x14 = -25 given the anchored solution.


; Check satisfiability and request a model
(check-sat)
(get-model)