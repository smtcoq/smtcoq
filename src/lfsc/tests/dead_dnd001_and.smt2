(set-logic QF_UF)
(set-info :status unsat)

(declare-sort I 0)
(declare-fun f (I I) I)
(declare-fun a () I)
(declare-fun b () I)
(declare-fun c () I)


(assert
(and
 (or
  (= (f a a) a)
  (or (= (f a a) b)
      (= (f a a) c))
  )

(and
 (or
  (= (f a b) a)
  (or (= (f a b) b)
      (= (f a b) c))
  )

(and
 (or
  (= (f a c) a)
  (or (= (f a c) b)
      (= (f a c) c))
  )

(and
 (or
  (= (f b a) a)
  (or (= (f b a) b)
      (= (f b a) c))
  )

(and
 (or
  (= (f b b) a)
  (or (= (f b b) b)
      (= (f b b) c))
  )

(and
 (or
  (= (f b c) a)
  (or (= (f b c) b)
      (= (f b c) c))
  )


(and
 (or
  (= (f c a) a)
  (or (= (f c a) b)
      (= (f c a) c))
  )

(and
 (or
  (= (f c b) a)
  (or (= (f c b) b)
      (= (f c b) c))
  )

(and
 (or
  (= (f c c) a)
  (or (= (f c c) b)
      (= (f c c) c))
  )



(and
 (or
  (= (f a a) a)
  (or (= (f b b) a)
      (= (f c c) a))
  )

(and
 (or
  (= (f a a) b)
  (or (= (f b b) b)
      (= (f c c) b))
  )

(and
 (or
  (= (f a a) c)
  (or (= (f b b) c)
      (= (f c c) c))
  )



(and
 (or
  (= (f a a) a)
  (or (= (f b a) b)
      (= (f c a) c))
  )

(and
 (or
  (= (f a b) a)
  (or (= (f b b) b)
      (= (f c b) c))
  )

(and
 (or
  (= (f a c) a)
  (or (= (f b c) b)
      (= (f c c) c))
  )




(and (not (= (f a a) a))
(and (not (= (f b b) b))
(and (not (= (f c c) c))


(and
 (or
  (not (= (f a (f a a)) a))
  (or (not (= (f a (f a b)) b))
      (not (= (f a (f a c)) c)))
  )

(and
 (or
  (not (= (f b (f b a)) a)) 
  (or (not (= (f b (f b b)) b))
      (not (= (f b (f b c)) c)))
  )

(and
 (or
  (not (= (f c (f c a)) a)) 
  (or (not (= (f c (f c b)) b))
      (not (= (f c (f c c)) c)))
  )


(and  (not (= (f a a) (f b a)))
(and  (not (= (f a a) (f c a)))
(and  (not (= (f b a) (f c a)))

(and  (not (= (f a b) (f b b)))
(and  (not (= (f a b) (f c b)))
(and  (not (= (f b b) (f c b)))

(and  (not (= (f a c) (f b c)))
(and  (not (= (f a c) (f c c)))
  (not (= (f b c) (f c c))))

)))))))))))))))))))))))))))))

(check-sat)

(exit)
