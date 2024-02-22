(* ------------------------------------------------------------------------- *)
(* Jacobian coordinates, (x,y,z) |-> (x/z^2,y/z^3) and (1,1,0) |-> infinity  *)
(* ------------------------------------------------------------------------- *)

needs "EC/weierstrass.ml";;

let jacobian_point = define
 `jacobian_point f (x,y,z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f`;;

let jacobian_curve = define
 `jacobian_curve (f,a:A,b) (x,y,z) <=>
        x IN ring_carrier f /\
        y IN ring_carrier f /\
        z IN ring_carrier f /\
        ring_pow f y 2 =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 4)))
                               (ring_mul f b (ring_pow f z 6)))`;;

let weierstrass_of_jacobian = define
 `weierstrass_of_jacobian (f:A ring) (x,y,z) =
        if z = ring_0 f then NONE
        else SOME(ring_div f x (ring_pow f z 2),
                  ring_div f y (ring_pow f z 3))`;;

let jacobian_of_weierstrass = define
 `jacobian_of_weierstrass (f:A ring) NONE = (ring_1 f,ring_1 f,ring_0 f) /\
  jacobian_of_weierstrass f (SOME(x,y)) = (x,y,ring_1 f)`;;

let jacobian_eq = define
 `jacobian_eq (f:A ring) (x,y,z) (x',y',z') <=>
        (z = ring_0 f <=> z' = ring_0 f) /\
        ring_mul f x (ring_pow f z' 2) = ring_mul f x' (ring_pow f z 2) /\
        ring_mul f y (ring_pow f z' 3) = ring_mul f y' (ring_pow f z 3)`;;

let jacobian_0 = new_definition
 `jacobian_0 (f:A ring,a:A,b:A) = (ring_1 f,ring_1 f,ring_0 f)`;;

let jacobian_neg = new_definition
 `jacobian_neg (f,a:A,b:A) (x,y,z) = (x:A,ring_neg f y:A,z:A)`;;

let jacobian_add = new_definition
 `jacobian_add (f:A ring,a,b) (x1,y1,z1) (x2,y2,z2) =
   if z1 = ring_0 f then (x2,y2,z2)
   else if z2 = ring_0 f then (x1,y1,z1)
   else if jacobian_eq f (x1,y1,z1) (x2,y2,z2) then
     let v = ring_mul f (ring_of_num f 4) (ring_mul f x1 (ring_pow f y1 2))
     and w =
       ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
       (ring_mul f a (ring_pow f z1 4)) in
     let x3 =
       ring_add f (ring_mul f (ring_neg f (ring_of_num f 2)) v)
       (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f (ring_of_num f 8)) (ring_pow f y1 4))
     (ring_mul f (ring_sub f v x3) w),
     ring_mul f (ring_of_num f 2) (ring_mul f y1 z1)
    else if jacobian_eq f (jacobian_neg (f,a,b) (x1,y1,z1)) (x2,y2,z2) then
      jacobian_0 (f,a,b)
    else
     let r = ring_mul f x1 (ring_pow f z2 2)
     and s = ring_mul f x2 (ring_pow f z1 2)
     and t = ring_mul f y1 (ring_pow f z2 3)
     and u = ring_mul f y2 (ring_pow f z1 3) in
     let v = ring_sub f s r
     and w = ring_sub f u t in
     let x3 =
         ring_add f
         (ring_sub f (ring_neg f (ring_pow f v 3))
         (ring_mul f (ring_of_num f 2) (ring_mul f r (ring_pow f v 2))))
         (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f t) (ring_pow f v 3))
     (ring_mul f (ring_sub f (ring_mul f r (ring_pow f v 2)) x3) w),
     ring_mul f v (ring_mul f z1 z2)`;;

let JACOBIAN_CURVE_IMP_POINT = prove
 (`!f a b p. jacobian_curve(f,a,b) p ==> jacobian_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[jacobian_curve; jacobian_point]);;

let JACOBIAN_OF_WEIERSTRASS_POINT_EQ = prove
 (`!(f:A ring) p.
        jacobian_point f (jacobian_of_weierstrass f p) <=>
        weierstrass_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[weierstrass_point; jacobian_of_weierstrass] THEN
  SIMP_TAC[jacobian_point; RING_0; RING_1]);;

let JACOBIAN_OF_WEIERSTRASS_POINT = prove
 (`!(f:A ring) p.
        weierstrass_point f p
        ==> jacobian_point f (jacobian_of_weierstrass f p)`,
  REWRITE_TAC[JACOBIAN_OF_WEIERSTRASS_POINT_EQ]);;

let WEIERSTRASS_OF_JACOBIAN_POINT = prove
 (`!(f:A ring) p.
        jacobian_point f p
        ==> weierstrass_point f (weierstrass_of_jacobian f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_jacobian; jacobian_point] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_point; RING_DIV; RING_POW]);;

let JACOBIAN_OF_WEIERSTRASS_EQ = prove
 (`!(f:A ring) p q.
        field f
        ==> (jacobian_of_weierstrass f p = jacobian_of_weierstrass f q <=>
             p = q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  REWRITE_TAC[jacobian_of_weierstrass; option_DISTINCT; option_INJ] THEN
  SIMP_TAC[PAIR_EQ]);;

let WEIERSTRASS_OF_JACOBIAN_EQ = prove
 (`!(f:A ring) p q.
        field f /\ jacobian_point f p /\ jacobian_point f q
        ==> (weierstrass_of_jacobian f p = weierstrass_of_jacobian f q <=>
             jacobian_eq f p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_point] THEN
  REWRITE_TAC[weierstrass_of_jacobian; jacobian_eq] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; option_DISTINCT]) THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; PAIR_EQ] THEN
  FIELD_TAC);;

let WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS = prove
 (`!(f:A ring) p.
        field f /\ weierstrass_point f p
        ==> weierstrass_of_jacobian f (jacobian_of_weierstrass f p) = p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; field] THEN
  SIMP_TAC[weierstrass_of_jacobian; jacobian_of_weierstrass;
           weierstrass_point; RING_POW_ONE; RING_DIV_1]);;

let JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN = prove
 (`!(f:A ring) p.
        field f /\ jacobian_point f p
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_of_jacobian f p)) p`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS;
           JACOBIAN_OF_WEIERSTRASS_POINT_EQ;
           WEIERSTRASS_OF_JACOBIAN_POINT]);;

let JACOBIAN_OF_WEIERSTRASS_CURVE_EQ = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> (jacobian_curve (f,a,b) (jacobian_of_weierstrass f p) <=>
             weierstrass_curve (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; weierstrass_point] THEN
  REWRITE_TAC[weierstrass_curve; jacobian_of_weierstrass] THEN
  SIMP_TAC[jacobian_curve; RING_0; RING_1] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let JACOBIAN_OF_WEIERSTRASS_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve (f,a,b) p
        ==> jacobian_curve (f,a,b) (jacobian_of_weierstrass f p)`,
  MESON_TAC[JACOBIAN_OF_WEIERSTRASS_CURVE_EQ;
            WEIERSTRASS_CURVE_IMP_POINT]);;

let WEIERSTRASS_OF_JACOBIAN_CURVE = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p
        ==> weierstrass_curve (f,a,b) (weierstrass_of_jacobian f p)`,
  SIMP_TAC[FORALL_PAIR_THM; weierstrass_of_jacobian; jacobian_curve] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[weierstrass_curve; RING_DIV; RING_POW] THEN
  FIELD_TAC);;

let JACOBIAN_POINT_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p
        ==> jacobian_point f (jacobian_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_neg; jacobian_point] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let JACOBIAN_CURVE_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p
        ==> jacobian_curve (f,a,b) (jacobian_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_neg; jacobian_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_JACOBIAN_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p
        ==> weierstrass_of_jacobian f (jacobian_neg (f,a,b) p) =
            weierstrass_neg (f,a,b) (weierstrass_of_jacobian f p)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_neg; weierstrass_of_jacobian;
              jacobian_point] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[weierstrass_neg; option_INJ; PAIR_EQ] THEN
  FIELD_TAC);;

let JACOBIAN_EQ_NEG = prove
 (`!(f:A ring) a b p p'.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f p' /\ jacobian_eq f p p'
        ==> jacobian_eq f
              (jacobian_neg (f,a,b) p) (jacobian_neg (f,a,b) p')`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ; JACOBIAN_POINT_NEG] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_NEG]);;

let WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> weierstrass_of_jacobian f
             (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p)) =
            weierstrass_neg (f,a,b) p`,
  SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_NEG;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

let JACOBIAN_OF_WEIERSTRASS_NEG = prove
 (`!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_neg (f,a,b) p))
             (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           JACOBIAN_POINT_NEG; WEIERSTRASS_POINT_NEG;
           WEIERSTRASS_OF_JACOBIAN_NEG;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

let JACOBIAN_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q
        ==> jacobian_point f (jacobian_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_add; jacobian_point;
              jacobian_0; jacobian_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_point;
              jacobian_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let JACOBIAN_CURVE_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p /\ jacobian_curve (f,a,b) q
        ==> jacobian_curve (f,a,b) (jacobian_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; jacobian_add; jacobian_curve;
              jacobian_0; jacobian_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_curve;
              jacobian_eq; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  W(MATCH_MP_TAC o INTEGRAL_DOMAIN_RULE o snd) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let WEIERSTRASS_OF_JACOBIAN_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q
        ==> weierstrass_of_jacobian f (jacobian_add (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_jacobian f p)
             (weierstrass_of_jacobian f q)`,
  REWRITE_TAC[FIELD_CHAR_NOT23; FORALL_PAIR_THM; jacobian_point] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `b:A`; `x1:A`; `y1:A`; `z1:A`;
    `x2:A`; `y2:A`; `z2:A`] THEN
  STRIP_TAC THEN REWRITE_TAC[weierstrass_of_jacobian; jacobian_add] THEN
  MAP_EVERY ASM_CASES_TAC [`z1:A = ring_0 f`; `z2:A = ring_0 f`] THEN
  ASM_REWRITE_TAC[weierstrass_of_jacobian; weierstrass_add] THEN
  ASM_REWRITE_TAC[jacobian_eq; jacobian_neg; jacobian_0] THEN
  ASM_SIMP_TAC[ring_div; RING_INV_POW] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let JACOBIAN_EQ_ADD = prove
 (`!(f:A ring) a b p p' q q'.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f p' /\
        jacobian_point f q /\ jacobian_point f q' /\
        jacobian_eq f p p' /\ jacobian_eq f q q'
        ==> jacobian_eq f
              (jacobian_add (f,a,b) p q) (jacobian_add (f,a,b) p' q')`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 9 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ; JACOBIAN_POINT_ADD] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_ADD]);;

let WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_of_jacobian f
             (jacobian_add (f,a,b)
               (jacobian_of_weierstrass f p)
               (jacobian_of_weierstrass f q)) =
            weierstrass_add (f,a,b) p q`,
  SIMP_TAC[WEIERSTRASS_OF_JACOBIAN_ADD;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

let JACOBIAN_OF_WEIERSTRASS_ADD = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_add (f,a,b) p q))
             (jacobian_add (f,a,b)
               (jacobian_of_weierstrass f p)
               (jacobian_of_weierstrass f q))`,
  SIMP_TAC[GSYM WEIERSTRASS_OF_JACOBIAN_EQ;
           JACOBIAN_OF_WEIERSTRASS_POINT;
           JACOBIAN_POINT_ADD; WEIERSTRASS_POINT_ADD;
           WEIERSTRASS_OF_JACOBIAN_ADD;
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]);;

(* ------------------------------------------------------------------------- *)
(* Some simpler variants that don't take such care over special cases.       *)
(* ------------------------------------------------------------------------- *)

let jacobian_add_unexceptional = new_definition
 `jacobian_add_unexceptional (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
   if z1 = ring_0 f then (x2,y2,z2)
   else if z2 = ring_0 f then (x1,y1,z1)
   else
     let r = ring_mul f x1 (ring_pow f z2 2)
     and s = ring_mul f x2 (ring_pow f z1 2)
     and t = ring_mul f y1 (ring_pow f z2 3)
     and u = ring_mul f y2 (ring_pow f z1 3) in
     let v = ring_sub f s r
     and w = ring_sub f u t in
     let x3 =
         ring_add f
         (ring_sub f (ring_neg f (ring_pow f v 3))
         (ring_mul f (ring_of_num f 2) (ring_mul f r (ring_pow f v 2))))
         (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f t) (ring_pow f v 3))
     (ring_mul f (ring_sub f (ring_mul f r (ring_pow f v 2)) x3) w),
     ring_mul f v (ring_mul f z1 z2)`;;

let WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL = prove
 (`!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q /\
        ~(jacobian_eq f p q)
        ==> weierstrass_of_jacobian f (jacobian_add_unexceptional (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_jacobian f p)
             (weierstrass_of_jacobian f q)`,
  REWRITE_TAC[FIELD_CHAR_NOT23; FORALL_PAIR_THM; jacobian_point] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `b:A`; `x1:A`; `y1:A`; `z1:A`;
    `x2:A`; `y2:A`; `z2:A`] THEN
  REWRITE_TAC[weierstrass_of_jacobian; jacobian_add_unexceptional] THEN
  REWRITE_TAC[jacobian_eq] THEN
  MAP_EVERY ASM_CASES_TAC [`z1:A = ring_0 f`; `z2:A = ring_0 f`] THEN
  ASM_REWRITE_TAC[weierstrass_of_jacobian; weierstrass_add] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[jacobian_neg; jacobian_0] THEN
  ASM_SIMP_TAC[ring_div; RING_INV_POW] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let jacobian_double_unexceptional = new_definition
 `jacobian_double_unexceptional (f:A ring,a:A,b:A) (x1,y1,z1) =
     let v = ring_mul f (ring_of_num f 4) (ring_mul f x1 (ring_pow f y1 2))
     and w =
       ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
       (ring_mul f a (ring_pow f z1 4)) in
     let x3 =
       ring_add f (ring_mul f (ring_neg f (ring_of_num f 2)) v)
       (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f (ring_of_num f 8)) (ring_pow f y1 4))
     (ring_mul f (ring_sub f v x3) w),
     ring_mul f (ring_of_num f 2) (ring_mul f y1 z1)`;;

let WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL = prove
 (`!(f:A ring) a b p.
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      jacobian_point f p
      ==> weierstrass_of_jacobian f (jacobian_double_unexceptional (f,a,b) p) =
          weierstrass_add (f,a,b)
           (weierstrass_of_jacobian f p)
           (weierstrass_of_jacobian f p)`,
  REWRITE_TAC[FIELD_CHAR_NOT23; FORALL_PAIR_THM; jacobian_point] THEN
  MAP_EVERY X_GEN_TAC [`f:A ring`; `a:A`; `b:A`; `x1:A`; `y1:A`; `z1:A`] THEN
  REWRITE_TAC[weierstrass_of_jacobian; jacobian_double_unexceptional] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[weierstrass_of_jacobian; weierstrass_add] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[jacobian_neg; jacobian_0] THEN
  ASM_SIMP_TAC[ring_div; RING_INV_POW] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;
