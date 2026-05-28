(set-logic QF_BV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))
(declare-fun d () (_ BitVec 4))

;; (assert (= a #b0010))
;; (assert (= b #b0110))
;; (assert (= c #b1000))
;; (assert (= d #b0010))

(assert (= #b0010 a))
(assert (= #b0110 b))
(assert (= #b1000 c))
(assert (= #b0010 d))

;; (assert (= #b1111 a))
;; (assert (= #b1111 b))
;; (assert (= #b1111 c))
;; (assert (= #b1111 d))

(assert
 (not (= (bvand (bvand a b) d) d)))

;; (assert
;;  (not (= (bvadd a b) (bvadd b (bvadd a #b1111)))))
(check-sat)
(exit)
