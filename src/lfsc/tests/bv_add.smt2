(set-logic QF_BV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))
(declare-fun d () (_ BitVec 4))

(assert (= #b0010 a))
(assert (= #b0110 b))
(assert (= #b1000 c))
(assert (= #b1100 d))

(assert
 (not (= (bvadd a b) c)))

(check-sat)
(exit)


