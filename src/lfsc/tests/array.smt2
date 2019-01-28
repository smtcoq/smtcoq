(set-logic QF_ALIA)

(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun d () (Array Int Int))

(assert (= c (store b 0 4)))

;; (assert (= d (store (store (store a 0 3) 1 (select c 0)) 2 2)))

(assert (not (= (select (store (store (store a 0 3) 1 (select c 0)) 2 2) 1) 4)))

;; (assert (= c d))

(check-sat)

