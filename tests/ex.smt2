(set-logic QF_SAT)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(assert (not (=> (and (=> a b) (=> b c)) (=> c a))))
(assert (not (=> (and (=> a b) (=> b c)) (=> a b))))

(check-sat)

                
