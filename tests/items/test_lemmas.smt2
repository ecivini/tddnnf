(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

; φ
(assert
  (let ((s (+ a b)))
    (and
      ; domain/bounds
      (<= 0 a) (<= a 6)
      (<= 0 b) (<= b 6)
      (<= 0 c) (<= c 3)

      ; disjunction 1: two “opposite corners” of the grid
      (or (and (<= a 2) (>= b 4))
          (and (>= a 4) (<= b 2)))

      ; disjunction 2: either sum is exactly 6, or small-sum with c=1
      (or (= s 6)
          (and (<= s 4) (= c 1)))

      ; a negative equality to keep interactions interesting
      (not (= b c))
    )))
(check-sat)