;; (set-logic QF_ALIA)
(set-logic QF_AUFBVLIA)

(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun d () (Array Int Int))

;; (assert (= c (store b 0 4)))
;; (assert (= d (store (store b 0 4) 1 4)))

;; (assert (= a (store d 1 (select b 1))))

;; (assert (not (= a c)))


(assert (not
(=> (= c (store b 0 4))
(=> (= d (store (store b 0 4) 1 4))

(=> (= a (store d 1 (select b 1)))
    
    (= a c))))))


(check-sat)

