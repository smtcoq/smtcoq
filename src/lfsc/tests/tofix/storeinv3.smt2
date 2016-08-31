(set-logic QF_AUFLIA)
(set-info :source |
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)
(declare-fun i5 () Int)
(declare-fun i6 () Int)
(declare-fun i7 () Int)
(declare-fun i8 () Int)
(declare-fun i9 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (let ((?v_1 (store a1 i1 (select a2 i1))) (?v_0 (store a2 i1 (select a1 i1)))) (let ((?v_2 (store ?v_0 i2 (select ?v_1 i2))) (?v_3 (store ?v_1 i2 (select ?v_0 i2)))) (let ((?v_5 (store ?v_3 i3 (select ?v_2 i3))) (?v_4 (store ?v_2 i3 (select ?v_3 i3)))) (let ((?v_6 (store ?v_4 i4 (select ?v_5 i4))) (?v_7 (store ?v_5 i4 (select ?v_4 i4)))) (let ((?v_9 (store ?v_7 i5 (select ?v_6 i5))) (?v_8 (store ?v_6 i5 (select ?v_7 i5)))) (let ((?v_10 (store ?v_8 i6 (select ?v_9 i6))) (?v_11 (store ?v_9 i6 (select ?v_8 i6)))) (let ((?v_13 (store ?v_11 i7 (select ?v_10 i7))) (?v_12 (store ?v_10 i7 (select ?v_11 i7)))) (let ((?v_14 (store ?v_12 i8 (select ?v_13 i8))) (?v_15 (store ?v_13 i8 (select ?v_12 i8)))) (= (store ?v_15 i9 (select ?v_14 i9)) (store ?v_14 i9 (select ?v_15 i9))))))))))))
(assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
(check-sat)
(exit)
