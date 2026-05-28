(set-logic QF_BV)
(declare-fun a () (_ BitVec 10))
(declare-fun b () (_ BitVec 10))
(declare-fun c () (_ BitVec 10))
(declare-fun d () (_ BitVec 10))

(assert (= #b0000000010 a))
(assert (= #b0000000110 b))
(assert (= #b0000001000 c))
(assert (= #b0000001100 d))

(assert
 (not (= (bvmul a b) d)))

(check-sat)
(exit)
