(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and a (and b (and c (and (or (not a) (or (not b) d)) (or (not d) (not c)))))))
(check-sat)
(exit)
