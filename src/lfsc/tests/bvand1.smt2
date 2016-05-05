(set-logic QF_BV)
(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 2))
(declare-fun c () (_ BitVec 2))

(assert (= (bvand a b) c))
(assert (not (= (bvand (bvand a b) c) c)))

(check-sat)
(exit)
