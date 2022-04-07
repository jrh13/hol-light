(* ========================================================================= *)
(* Projective coordinates, (x,y,z) |-> (x/z,y/z) and (0,1,0) |-> infinity    *)
(* ========================================================================= *)

needs "EC/weierstrass.ml";;

let projective_point = define
 `projective_point f (x,y,z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f`;;

let projective_curve = define
 `projective_curve (f,a:A,b) (x,y,z) <=>
        x IN ring_carrier f /\
        y IN ring_carrier f /\
        z IN ring_carrier f /\
        ring_mul f (ring_pow f y 2) z =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 2)))
                               (ring_mul f b (ring_pow f z 3)))`;;

let weierstrass_of_projective = define
 `weierstrass_of_projective (f:A ring) (x,y,z) =
        if z = ring_0 f then NONE
        else SOME(ring_div f x z,ring_div f y z)`;;

let projective_of_weierstrass = define
 `projective_of_weierstrass (f:A ring) NONE = (ring_0 f,ring_1 f,ring_0 f) /\
  projective_of_weierstrass f (SOME(x,y)) = (x,y,ring_1 f)`;;

let projective_eq = define
 `projective_eq (f:A ring) (x,y,z) (x',y',z') <=>
        (z = ring_0 f <=> z' = ring_0 f) /\
        ring_mul f x z' = ring_mul f x' z /\
        ring_mul f y z' = ring_mul f y' z`;;

let projective_0 = new_definition
 `projective_0 (f:A ring,a:A,b:A) = (ring_0 f,ring_1 f,ring_0 f)`;;

let projective_neg = new_definition
 `projective_neg (f,a:A,b:A) (x,y,z) = (x:A,ring_neg f y:A,z:A)`;;

let projective_add = new_definition
 `projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2) =
    if z1 = ring_0 f then (x2,y2,z2)
    else if z2 = ring_0 f then (x1,y1,z1)
    else if projective_eq f (x1,y1,z1) (x2,y2,z2) then
      let t =
          ring_add f (ring_mul f a (ring_pow f z1 2))
          (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
      and u = ring_mul f y1 z1 in
      let v = ring_mul f u (ring_mul f x1 y1) in
      let w = ring_sub f (ring_pow f t 2) (ring_mul f (ring_of_num f 8) v) in
      (ring_mul f (ring_of_num f 2) (ring_mul f u w),
       ring_sub f (ring_mul f t (ring_sub f (ring_mul f (ring_of_num f 4) v) w))
       (ring_mul f (ring_of_num f 8)
       (ring_mul f (ring_pow f y1 2) (ring_pow f u 2))),
       ring_mul f (ring_of_num f 8) (ring_pow f u 3))
    else if projective_eq f (projective_neg (f,a,b) (x1,y1,z1)) (x2,y2,z2) then
      projective_0 (f,a,b)
    else
      let u = ring_sub f (ring_mul f y2 z1) (ring_mul f y1 z2)
      and v = ring_sub f (ring_mul f x2 z1) (ring_mul f x1 z2) in
      let w =
          ring_sub f
          (ring_sub f (ring_mul f (ring_pow f u 2) (ring_mul f z1 z2))
          (ring_pow f v 3))
          (ring_mul f (ring_of_num f 2)
          (ring_mul f (ring_pow f v 2) (ring_mul f x1 z2))) in
      (ring_mul f v w,
       ring_sub f
       (ring_mul f u
       (ring_sub f (ring_mul f (ring_pow f v 2) (ring_mul f x1 z2)) w))
       (ring_mul f (ring_pow f v 3) (ring_mul f y1 z2)),
       ring_mul f (ring_pow f v 3) (ring_mul f z1 z2))`;;

let PROJECTIVE_CURVE_IMP_POINT = prove
 (`!f a b p. projective_curve(f,a,b) p ==> projective_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[projective_curve; projective_point]);;

let PROJECTIVE_OF_WEIERSTRASS_POINT_EQ = prove
 (`!(f:A ring) p.
        projective_point f (projective_of_weierstrass f p) <=>
        weierstrass_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[weierstrass_point; projective_of_weierstrass] THEN
  SIMP_TAC[projective_point; RING_0; RING_1]);;

let PROJECTIVE_OF_WEIERSTRASS_POINT = prove
 (`!(f:A ring) p.
        weierstrass_point f p
        ==> projective_point f (projective_of_weierstrass f p)`,
  REWRITE_TAC[PROJECTIVE_OF_WEIERSTRASS_POINT_EQ]);;

let WEIERSTRASS_OF_PROJECTIVE_POINT = prove
 (`!(f:A ring) p.
        projective_point f p
        ==> weierstrass_point f (weierstrass_of_projective f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_projective; projective_point] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_point; RING_DIV]);;

let PROJECTIVE_OF_WEIERSTRASS_EQ = prove
 (`!(f:A ring) p q.
        field f
        ==> (projective_of_weierstrass f p = projective_of_weierstrass f q <=>
             p = q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  REWRITE_TAC[projective_of_weierstrass; option_DISTINCT; option_INJ] THEN
  SIMP_TAC[PAIR_EQ]);;

let WEIERSTRASS_OF_PROJECTIVE_EQ = prove
 (`!(f:A ring) p q.
        field f /\ projective_point f p /\ projective_point f q
        ==> (weierstrass_of_projective f p = weierstrass_of_projective f q <=>
             projective_eq f p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_point] THEN
  REWRITE_TAC[weierstrass_of_projective; projective_eq] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; option_DISTINCT]) THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; PAIR_EQ] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] FIELD_MUL_LINV)))) THEN
  ASM_REWRITE_TAC[ring_div] THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[RING_INV; FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS = prove
 (`!(f:A ring) p.
        field f /\ weierstrass_point f p
        ==> weierstrass_of_projective f (projective_of_weierstrass f p) = p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  SIMP_TAC[weierstrass_of_projective; projective_of_weierstrass;
           weierstrass_point; RING_DIV_1]);;

let PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE = prove
 (`!(f:A ring) p.
        field f /\ projective_point f p
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_of_projective f p)) p`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS;
           PROJECTIVE_OF_WEIERSTRASS_POINT_EQ;
           WEIERSTRASS_OF_PROJECTIVE_POINT]);;

let PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> (projective_curve (f,a,b) (projective_of_weierstrass f p) <=>
             weierstrass_curve (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; weierstrass_point] THEN
  REWRITE_TAC[weierstrass_curve; projective_of_weierstrass] THEN
  SIMP_TAC[projective_curve; RING_0; RING_1] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let PROJECTIVE_OF_WEIERSTRASS_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve (f,a,b) p
        ==> projective_curve (f,a,b) (projective_of_weierstrass f p)`,
  MESON_TAC[PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ;
            WEIERSTRASS_CURVE_IMP_POINT]);;

let WEIERSTRASS_OF_PROJECTIVE_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p
        ==> weierstrass_curve (f,a,b) (weierstrass_of_projective f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_projective; projective_curve] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_curve; RING_DIV] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] FIELD_MUL_LINV)))) THEN
  ASM_REWRITE_TAC[ring_div] THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[RING_INV; FIELD_IMP_INTEGRAL_DOMAIN]);;

let PROJECTIVE_POINT_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p
        ==> projective_point f (projective_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_neg; projective_point] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let PROJECTIVE_CURVE_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p
        ==> projective_curve (f,a,b) (projective_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_neg; projective_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_PROJECTIVE_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p
        ==> weierstrass_of_projective f (projective_neg (f,a,b) p) =
            weierstrass_neg (f,a,b) (weierstrass_of_projective f p)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_neg; weierstrass_of_projective;
              projective_point] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[weierstrass_neg; option_INJ; PAIR_EQ] THEN
  FIELD_TAC);;

let PROJECTIVE_EQ_NEG = prove
 (`!(f:A ring) a b p p'.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f p' /\ projective_eq f p p'
        ==> projective_eq f
              (projective_neg (f,a,b) p) (projective_neg (f,a,b) p')`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ; PROJECTIVE_POINT_NEG] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_NEG]);;

let WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> weierstrass_of_projective f
             (projective_neg (f,a,b) (projective_of_weierstrass f p)) =
            weierstrass_neg (f,a,b) p`,
  SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_NEG;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

let PROJECTIVE_OF_WEIERSTRASS_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_neg (f,a,b) p))
             (projective_neg (f,a,b) (projective_of_weierstrass f p))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           PROJECTIVE_POINT_NEG; WEIERSTRASS_POINT_NEG;
           WEIERSTRASS_OF_PROJECTIVE_NEG;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

let PROJECTIVE_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f q
        ==> projective_point f (projective_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_add; projective_point;
              projective_0; projective_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[projective_add; projective_point;
              projective_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let PROJECTIVE_CURVE_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p /\ projective_curve (f,a,b) q
        ==> projective_curve (f,a,b) (projective_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective_add; projective_curve;
              projective_0; projective_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[projective_add; projective_curve;
              projective_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_PROJECTIVE_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f q
        ==> weierstrass_of_projective f (projective_add (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_projective f p)
             (weierstrass_of_projective f q)`,
  REWRITE_TAC[FIELD_CHAR_NOT23; FORALL_PAIR_THM; projective_point] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `b:A`; `x1:A`; `y1:A`; `z1:A`;
    `x2:A`; `y2:A`; `z2:A`] THEN
  STRIP_TAC THEN REWRITE_TAC[weierstrass_of_projective; projective_add] THEN
  MAP_EVERY ASM_CASES_TAC [`z1:A = ring_0 f`; `z2:A = ring_0 f`] THEN
  ASM_REWRITE_TAC[weierstrass_of_projective; weierstrass_add] THEN
  ASM_REWRITE_TAC[projective_eq; projective_neg; projective_0] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_of_projective] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let PROJECTIVE_EQ_ADD = prove
 (`!(f:A ring) a b p p' q q'.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f p' /\
        projective_point f q /\ projective_point f q' /\
        projective_eq f p p' /\ projective_eq f q q'
        ==> projective_eq f
              (projective_add (f,a,b) p q) (projective_add (f,a,b) p' q')`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 9 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ; PROJECTIVE_POINT_ADD] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_ADD]);;

let WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_of_projective f
             (projective_add (f,a,b)
               (projective_of_weierstrass f p)
               (projective_of_weierstrass f q)) =
            weierstrass_add (f,a,b) p q`,
  SIMP_TAC[WEIERSTRASS_OF_PROJECTIVE_ADD;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;

let PROJECTIVE_OF_WEIERSTRASS_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_add (f,a,b) p q))
             (projective_add (f,a,b)
               (projective_of_weierstrass f p)
               (projective_of_weierstrass f q))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_PROJECTIVE_EQ;
           PROJECTIVE_OF_WEIERSTRASS_POINT;
           PROJECTIVE_POINT_ADD; WEIERSTRASS_POINT_ADD;
           WEIERSTRASS_OF_PROJECTIVE_ADD;
           WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]);;
