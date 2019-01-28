(set-logic QF_BV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 5))
(declare-fun c () (_ BitVec 9))


(assert (= #b0010 a))
(assert (= #b01101 b))
(assert (= #b001001101 c))

(assert
 (not (= (concat a b) c)))

(check-sat)
(exit)
