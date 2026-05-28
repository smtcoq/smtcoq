(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))

;; (assert (= #b01 a))
;; (assert (= #b10 b))
;; (assert (= #b00 c))
;; (assert (= #b11 d))

(declare-fun one () (_ BitVec 32))
(declare-fun max () (_ BitVec 32))

(assert (= one #b00000000000000000000000000000001))
(assert (= max #b11111111111111111111111111111111))

(assert (not (= a max)))

(assert
 (not (bvult a (bvadd a one))))

(check-sat)
