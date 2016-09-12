(set-logic QF_BV)
(declare-fun a () (_ BitVec 12))
(declare-fun b () (_ BitVec 12))
(declare-fun c () (_ BitVec 12))
(declare-fun d () (_ BitVec 12))

(assert (= #b000000000010 a))
(assert (= #b000000000110 b))
(assert (= #b000000001000 c))
(assert (= #b000000001100 d))

(assert
 (not (= (bvmul a b) d)))

(check-sat)
(exit)
