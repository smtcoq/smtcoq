(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U U) U)

(assert (not
         (=> (and (= a b) (= a c))
             (= (f a c) (f b a)))))

(check-sat)
(exit)

