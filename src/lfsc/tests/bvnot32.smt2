(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))

(assert (= c (bvnot a)))
(assert (not (= (bvnot c) a)))

(check-sat)
(exit)
