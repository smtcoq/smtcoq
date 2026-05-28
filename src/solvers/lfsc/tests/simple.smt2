(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-sort U 0)

(declare-fun f (U U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)

(assert (not (= (f a b) (f b b))))
(assert (not (= (f a b) (f c b))))

(assert (or (= a b) (= a c)))
(check-sat)
(get-proof)
(exit)
