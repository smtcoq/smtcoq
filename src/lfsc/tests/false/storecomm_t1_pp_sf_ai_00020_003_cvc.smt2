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
(declare-fun a_514 () (Array Int Int))
(declare-fun a_515 () (Array Int Int))
(declare-fun a_516 () (Array Int Int))
(declare-fun a_517 () (Array Int Int))
(declare-fun a_518 () (Array Int Int))
(declare-fun a_519 () (Array Int Int))
(declare-fun a_520 () (Array Int Int))
(declare-fun a_521 () (Array Int Int))
(declare-fun a_522 () (Array Int Int))
(declare-fun a_523 () (Array Int Int))
(declare-fun a_524 () (Array Int Int))
(declare-fun a_525 () (Array Int Int))
(declare-fun a_526 () (Array Int Int))
(declare-fun a_527 () (Array Int Int))
(declare-fun a_528 () (Array Int Int))
(declare-fun a_529 () (Array Int Int))
(declare-fun a_530 () (Array Int Int))
(declare-fun a_531 () (Array Int Int))
(declare-fun a_532 () (Array Int Int))
(declare-fun a_533 () (Array Int Int))
(declare-fun a_534 () (Array Int Int))
(declare-fun a_535 () (Array Int Int))
(declare-fun a_536 () (Array Int Int))
(declare-fun a_537 () (Array Int Int))
(declare-fun a_538 () (Array Int Int))
(declare-fun a_539 () (Array Int Int))
(declare-fun a_540 () (Array Int Int))
(declare-fun a_541 () (Array Int Int))
(declare-fun a_542 () (Array Int Int))
(declare-fun a_543 () (Array Int Int))
(declare-fun a_544 () (Array Int Int))
(declare-fun a_545 () (Array Int Int))
(declare-fun a_546 () (Array Int Int))
(declare-fun a_547 () (Array Int Int))
(declare-fun a_548 () (Array Int Int))
(declare-fun a_549 () (Array Int Int))
(declare-fun a_550 () (Array Int Int))
(declare-fun a_551 () (Array Int Int))
(declare-fun a_552 () (Array Int Int))
(declare-fun a_553 () (Array Int Int))
(declare-fun e_555 () Int)
(declare-fun e_556 () Int)
(declare-fun i_554 () Int)
(declare-fun a1 () (Array Int Int))
(declare-fun e1 () Int)
(declare-fun e10 () Int)
(declare-fun e11 () Int)
(declare-fun e12 () Int)
(declare-fun e13 () Int)
(declare-fun e14 () Int)
(declare-fun e15 () Int)
(declare-fun e16 () Int)
(declare-fun e17 () Int)
(declare-fun e18 () Int)
(declare-fun e19 () Int)
(declare-fun e2 () Int)
(declare-fun e20 () Int)
(declare-fun e3 () Int)
(declare-fun e4 () Int)
(declare-fun e5 () Int)
(declare-fun e6 () Int)
(declare-fun e7 () Int)
(declare-fun e8 () Int)
(declare-fun e9 () Int)
(declare-fun i1 () Int)
(declare-fun i10 () Int)
(declare-fun i11 () Int)
(declare-fun i12 () Int)
(declare-fun i13 () Int)
(declare-fun i14 () Int)
(declare-fun i15 () Int)
(declare-fun i16 () Int)
(declare-fun i17 () Int)
(declare-fun i18 () Int)
(declare-fun i19 () Int)
(declare-fun i2 () Int)
(declare-fun i20 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)
(declare-fun i5 () Int)
(declare-fun i6 () Int)
(declare-fun i7 () Int)
(declare-fun i8 () Int)
(declare-fun i9 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= a_514 (store a1 i1 e1)))
(assert (= a_515 (store a_514 i2 e2)))
(assert (= a_516 (store a_515 i3 e3)))
(assert (= a_517 (store a_516 i4 e4)))
(assert (= a_518 (store a_517 i5 e5)))
(assert (= a_519 (store a_518 i6 e6)))
(assert (= a_520 (store a_519 i7 e7)))
(assert (= a_521 (store a_520 i8 e8)))
(assert (= a_522 (store a_521 i9 e9)))
(assert (= a_523 (store a_522 i10 e10)))
(assert (= a_524 (store a_523 i11 e11)))
(assert (= a_525 (store a_524 i12 e12)))
(assert (= a_526 (store a_525 i13 e13)))
(assert (= a_527 (store a_526 i14 e14)))
(assert (= a_528 (store a_527 i15 e15)))
(assert (= a_529 (store a_528 i16 e16)))
(assert (= a_530 (store a_529 i17 e17)))
(assert (= a_531 (store a_530 i18 e18)))
(assert (= a_532 (store a_531 i19 e19)))
(assert (= a_533 (store a_532 i20 e20)))
(assert (= a_534 (store a1 i6 e6)))
(assert (= a_535 (store a_534 i16 e16)))
(assert (= a_536 (store a_535 i14 e14)))
(assert (= a_537 (store a_536 i13 e13)))
(assert (= a_538 (store a_537 i2 e2)))
(assert (= a_539 (store a_538 i18 e18)))
(assert (= a_540 (store a_539 i19 e19)))
(assert (= a_541 (store a_540 i12 e12)))
(assert (= a_542 (store a_541 i11 e11)))
(assert (= a_543 (store a_542 i7 e7)))
(assert (= a_544 (store a_543 i4 e4)))
(assert (= a_545 (store a_544 i9 e9)))
(assert (= a_546 (store a_545 i5 e5)))
(assert (= a_547 (store a_546 i20 e20)))
(assert (= a_548 (store a_547 i1 e1)))
(assert (= a_549 (store a_548 i10 e10)))
(assert (= a_550 (store a_549 i15 e15)))
(assert (= a_551 (store a_550 i17 e17)))
(assert (= a_552 (store a_551 i8 e8)))
(assert (= a_553 (store a_552 i3 e3)))
(assert (= e_555 (select a_533 i_554)))
(assert (= e_556 (select a_553 i_554)))
(assert (= i_554 (sk a_533 a_553)))
(assert (not (= i19 i20)))
(assert (not (= i18 i20)))
(assert (not (= i18 i19)))
(assert (not (= i17 i20)))
(assert (not (= i17 i19)))
(assert (not (= i17 i18)))
(assert (not (= i16 i20)))
(assert (not (= i16 i19)))
(assert (not (= i16 i18)))
(assert (not (= i16 i17)))
(assert (not (= i15 i20)))
(assert (not (= i15 i19)))
(assert (not (= i15 i18)))
(assert (not (= i15 i17)))
(assert (not (= i15 i16)))
(assert (not (= i14 i20)))
(assert (not (= i14 i19)))
(assert (not (= i14 i18)))
(assert (not (= i14 i17)))
(assert (not (= i14 i16)))
(assert (not (= i14 i15)))
(assert (not (= i13 i20)))
(assert (not (= i13 i19)))
(assert (not (= i13 i18)))
(assert (not (= i13 i17)))
(assert (not (= i13 i16)))
(assert (not (= i13 i15)))
(assert (not (= i13 i14)))
(assert (not (= i12 i20)))
(assert (not (= i12 i19)))
(assert (not (= i12 i18)))
(assert (not (= i12 i17)))
(assert (not (= i12 i16)))
(assert (not (= i12 i15)))
(assert (not (= i12 i14)))
(assert (not (= i12 i13)))
(assert (not (= i11 i20)))
(assert (not (= i11 i19)))
(assert (not (= i11 i18)))
(assert (not (= i11 i17)))
(assert (not (= i11 i16)))
(assert (not (= i11 i15)))
(assert (not (= i11 i14)))
(assert (not (= i11 i13)))
(assert (not (= i11 i12)))
(assert (not (= i10 i20)))
(assert (not (= i10 i19)))
(assert (not (= i10 i18)))
(assert (not (= i10 i17)))
(assert (not (= i10 i16)))
(assert (not (= i10 i15)))
(assert (not (= i10 i14)))
(assert (not (= i10 i13)))
(assert (not (= i10 i12)))
(assert (not (= i10 i11)))
(assert (not (= i9 i20)))
(assert (not (= i9 i19)))
(assert (not (= i9 i18)))
(assert (not (= i9 i17)))
(assert (not (= i9 i16)))
(assert (not (= i9 i15)))
(assert (not (= i9 i14)))
(assert (not (= i9 i13)))
(assert (not (= i9 i12)))
(assert (not (= i9 i11)))
(assert (not (= i9 i10)))
(assert (not (= i8 i20)))
(assert (not (= i8 i19)))
(assert (not (= i8 i18)))
(assert (not (= i8 i17)))
(assert (not (= i8 i16)))
(assert (not (= i8 i15)))
(assert (not (= i8 i14)))
(assert (not (= i8 i13)))
(assert (not (= i8 i12)))
(assert (not (= i8 i11)))
(assert (not (= i8 i10)))
(assert (not (= i8 i9)))
(assert (not (= i7 i20)))
(assert (not (= i7 i19)))
(assert (not (= i7 i18)))
(assert (not (= i7 i17)))
(assert (not (= i7 i16)))
(assert (not (= i7 i15)))
(assert (not (= i7 i14)))
(assert (not (= i7 i13)))
(assert (not (= i7 i12)))
(assert (not (= i7 i11)))
(assert (not (= i7 i10)))
(assert (not (= i7 i9)))
(assert (not (= i7 i8)))
(assert (not (= i6 i20)))
(assert (not (= i6 i19)))
(assert (not (= i6 i18)))
(assert (not (= i6 i17)))
(assert (not (= i6 i16)))
(assert (not (= i6 i15)))
(assert (not (= i6 i14)))
(assert (not (= i6 i13)))
(assert (not (= i6 i12)))
(assert (not (= i6 i11)))
(assert (not (= i6 i10)))
(assert (not (= i6 i9)))
(assert (not (= i6 i8)))
(assert (not (= i6 i7)))
(assert (not (= i5 i20)))
(assert (not (= i5 i19)))
(assert (not (= i5 i18)))
(assert (not (= i5 i17)))
(assert (not (= i5 i16)))
(assert (not (= i5 i15)))
(assert (not (= i5 i14)))
(assert (not (= i5 i13)))
(assert (not (= i5 i12)))
(assert (not (= i5 i11)))
(assert (not (= i5 i10)))
(assert (not (= i5 i9)))
(assert (not (= i5 i8)))
(assert (not (= i5 i7)))
(assert (not (= i5 i6)))
(assert (not (= i4 i20)))
(assert (not (= i4 i19)))
(assert (not (= i4 i18)))
(assert (not (= i4 i17)))
(assert (not (= i4 i16)))
(assert (not (= i4 i15)))
(assert (not (= i4 i14)))
(assert (not (= i4 i13)))
(assert (not (= i4 i12)))
(assert (not (= i4 i11)))
(assert (not (= i4 i10)))
(assert (not (= i4 i9)))
(assert (not (= i4 i8)))
(assert (not (= i4 i7)))
(assert (not (= i4 i6)))
(assert (not (= i4 i5)))
(assert (not (= i3 i20)))
(assert (not (= i3 i19)))
(assert (not (= i3 i18)))
(assert (not (= i3 i17)))
(assert (not (= i3 i16)))
(assert (not (= i3 i15)))
(assert (not (= i3 i14)))
(assert (not (= i3 i13)))
(assert (not (= i3 i12)))
(assert (not (= i3 i11)))
(assert (not (= i3 i10)))
(assert (not (= i3 i9)))
(assert (not (= i3 i8)))
(assert (not (= i3 i7)))
(assert (not (= i3 i6)))
(assert (not (= i3 i5)))
(assert (not (= i3 i4)))
(assert (not (= i2 i20)))
(assert (not (= i2 i19)))
(assert (not (= i2 i18)))
(assert (not (= i2 i17)))
(assert (not (= i2 i16)))
(assert (not (= i2 i15)))
(assert (not (= i2 i14)))
(assert (not (= i2 i13)))
(assert (not (= i2 i12)))
(assert (not (= i2 i11)))
(assert (not (= i2 i10)))
(assert (not (= i2 i9)))
(assert (not (= i2 i8)))
(assert (not (= i2 i7)))
(assert (not (= i2 i6)))
(assert (not (= i2 i5)))
(assert (not (= i2 i4)))
(assert (not (= i2 i3)))
(assert (not (= i1 i20)))
(assert (not (= i1 i19)))
(assert (not (= i1 i18)))
(assert (not (= i1 i17)))
(assert (not (= i1 i16)))
(assert (not (= i1 i15)))
(assert (not (= i1 i14)))
(assert (not (= i1 i13)))
(assert (not (= i1 i12)))
(assert (not (= i1 i11)))
(assert (not (= i1 i10)))
(assert (not (= i1 i9)))
(assert (not (= i1 i8)))
(assert (not (= i1 i7)))
(assert (not (= i1 i6)))
(assert (not (= i1 i5)))
(assert (not (= i1 i4)))
(assert (not (= i1 i3)))
(assert (not (= i1 i2)))
(assert (not (= e_555 e_556)))
(check-sat)
(exit)
