;; (set-logic QF_ALIA)
(set-logic QF_AUFBVLIA)

(declare-fun bv1 () (_ BitVec 10))
(declare-fun bv2 () (_ BitVec 10))

(declare-fun bv3 () (_ BitVec 10))
(declare-fun bv4 () (_ BitVec 10))

(declare-fun a () (Array (_ BitVec 10) (_ BitVec 10)))
(declare-fun b () (Array (_ BitVec 10) (_ BitVec 10)))
(declare-fun c () (Array (_ BitVec 10) (_ BitVec 10)))
(declare-fun d () (Array (_ BitVec 10) (_ BitVec 10)))

(assert (= #b0000000000 bv1))
(assert (= #b0000000001 bv2))
(assert (= #b0000000100 bv3))
(assert (= #b1111111111 bv4))

(assert
 (= (bvmul bv4 bv3) bv3))



(assert (not	
(=> (= c (store b bv1 bv3))
(=> (= d (store (store b bv1 bv3) bv2 bv3))

(=> (= a (store d bv2 (select b bv2)))
    
    (= a c))))))


(check-sat)
