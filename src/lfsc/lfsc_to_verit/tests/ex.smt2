;; (set-logic QF_SAT)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
;; (declare-fun f (Bool Bool) Bool)

(assert (not (=> (and (=> a b) (=> b c)) (=> a c))))

(check-sat)
