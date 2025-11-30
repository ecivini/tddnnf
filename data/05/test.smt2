(set-logic QF_LIA)

; Integer variables
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

; Keep variables within small bounds
(assert (and (>= x -3) (<= x 3)))
(assert (and (>= y 0)  (<= y 3)))

; Branching: z depends on the sign of x
; If x >= 0 then z = y + 10, else z = y - 10
(assert (=> (>= x 0) (= z (+ y 10))))
(assert (=> (< x 0)  (= z (- y 10))))

; Additional branching via disjunction on z
(assert (or (>= z 12) (<= z -12)))

(check-sat)
(get-model)