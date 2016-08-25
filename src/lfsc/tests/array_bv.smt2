;; (set-logic QF_ALIA)
(set-logic QF_AUFBVLIA)

(declare-fun bv1 () (_ BitVec 4))
(declare-fun bv2 () (_ BitVec 4))

(declare-fun a () (Array (_ BitVec 4) Int))
(declare-fun b () (Array (_ BitVec 4) Int))
(declare-fun c () (Array (_ BitVec 4) Int))
(declare-fun d () (Array (_ BitVec 4) Int))

(assert (= #b0000 bv1))
(assert (= #b0001 bv2))

(assert (= c (store b bv1 4)))
(assert (= d (store (store b bv1 4) bv2 4)))

(assert (= a (store d bv2 (select b bv2))))

(assert (not (= a c)))

(check-sat)

