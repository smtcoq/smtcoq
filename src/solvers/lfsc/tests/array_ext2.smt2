;; (set-logic QF_ALIA)
(set-logic QF_AUFBVLIA)

(declare-fun bv1 () (_ BitVec 32))
(declare-fun bv2 () (_ BitVec 32))

(declare-fun bv3 () (_ BitVec 32))


(declare-fun a () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun c () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun d () (Array (_ BitVec 32) (_ BitVec 32)))

(assert (= #b00000000000000000000000000000000 bv1))
(assert (= #b00000000000000000000000000000001 bv2))
(assert (= #b00000000000000000000000000000100 bv3))



(assert (not
(=> (= c (store b bv1 bv3))
(=> (= d (store (store b bv1 bv3) bv2 bv3))

(=> (= a (store d bv2 (select b bv2)))
    
    (= a c))))))


(check-sat)

