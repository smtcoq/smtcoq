(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (not (=> (and (<= x 3) (or (not (>= y 8)) (not (>= z 10)))) (or (not (>= (+ x y) 11)) (not (>= (+ x z) 13))))))
(check-sat)
(exit)
