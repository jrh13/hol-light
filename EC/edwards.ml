(* ========================================================================= *)
(* Twisted Edwards curves in general, a * x^2 + y^2 = 1 + d * x^2 * y^2.     *)
(* ========================================================================= *)

needs "EC/misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic definitions and naive cardinality bounds.                           *)
(* ------------------------------------------------------------------------- *)

let edwards_point = define
 `edwards_point f (x:A,y) <=>
        x IN ring_carrier f /\ y IN ring_carrier f`;;

let edwards_curve = define
 `edwards_curve(f:A ring,a:A,d:A) (x,y) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_add f (ring_mul f a (ring_pow f x 2)) (ring_pow f y 2) =
        ring_add f (ring_1 f)
          (ring_mul f d (ring_mul f (ring_pow f x 2) (ring_pow f y 2)))`;;

let edwards_nonsingular = define
 `edwards_nonsingular (f:A ring,a:A,d:A) <=>
        (?b. b IN ring_carrier f /\ ring_pow f b 2 = a) /\
        (d = ring_0 f \/ ~(?c. c IN ring_carrier f /\ ring_pow f c 2 = d))`;;

let edwards_0 = define
 `edwards_0 (f:A ring,a:A,d:A) = (ring_0 f,ring_1 f)`;;

let edwards_neg = define
 `edwards_neg (f:A ring,a:A,d:A) (x,y:A) = (ring_neg f x,y)`;;

let edwards_add = define
 `edwards_add (f:A ring,a:A,d:A) (x1,y1) (x2,y2) =
   ring_div f (ring_add f (ring_mul f x1 y2) (ring_mul f y1 x2))
   (ring_add f (ring_1 f)
   (ring_mul f d (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2))))),
   ring_div f
   (ring_sub f (ring_mul f y1 y2) (ring_mul f a (ring_mul f x1 x2)))
   (ring_sub f (ring_1 f)
   (ring_mul f d (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2)))))`;;

let edwards_group = define
 `edwards_group (f:A ring,a:A,d:A) =
        group(edwards_curve(f,a,d),
              edwards_0(f,a,d),
              edwards_neg(f,a,d),
              edwards_add(f,a,d))`;;

let EDWARDS_NONSINGULAR_ALT = prove
 (`!f a (d:A).
    field f /\ a IN ring_carrier f /\ d IN ring_carrier f
    ==> (edwards_nonsingular (f,a,d) <=>
        (?b. b IN ring_carrier f /\ ring_pow f b 2 = a) /\
        ~(?c. c IN ring_carrier f /\ ~(c = ring_0 f) /\ ring_pow f c 2 = d))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[edwards_nonsingular] THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `d:A = ring_0 f` THEN ASM_REWRITE_TAC[] THENL
   [FIELD_TAC; AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIELD_TAC);;

let FINITE_EDWARDS_CURVE = prove
 (`!f a d:A. field f /\ FINITE(ring_carrier f)
             ==> FINITE(edwards_curve(f,a,d))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `{(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f}` THEN
  ASM_SIMP_TAC[FINITE_PRODUCT] THEN
  REWRITE_TAC[edwards_curve; SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  SIMP_TAC[edwards_curve; IN]);;

let CARD_BOUND_EDWARDS_CURVE = prove
 (`!f a d:A. field f /\ FINITE(ring_carrier f) /\
             a IN ring_carrier f /\ d IN ring_carrier f /\
             edwards_nonsingular(f,a,d)
             ==> CARD(edwards_curve(f,a,d)) <= 2 * CARD(ring_carrier f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_SUBSET; CARD_SUBSET; LE_TRANS]
   `!s. t SUBSET s /\ FINITE s /\ CARD s <= n ==> CARD t <= n`) THEN
  EXISTS_TAC
   `{(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
             ring_pow f y 2 =
             ring_div f (ring_sub f (ring_1 f)
                            (ring_mul f a (ring_pow f x 2)))
                        (ring_sub f (ring_1 f)
                            (ring_mul f d (ring_pow f x 2)))}`THEN
  ASM_SIMP_TAC[FINITE_QUADRATIC_CURVE; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SYM o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards_nonsingular]) THEN
  REWRITE_TAC[NOT_EXISTS_THM; RIGHT_OR_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `ring_inv f x:A` o CONJUNCT2) THEN
  ASM_SIMP_TAC[RING_INV] THEN FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Proof of the group properties by algebraic brute force. We do use a bit   *)
(* more delicacy than calling FIELD_TAC in order to avoid assuming anything  *)
(* about the characteristic of the field.                                    *)
(* ------------------------------------------------------------------------- *)

let EDWARDS_NONSINGULAR_DENOMINATORS = prove
 (`!f a (d:A) x1 y1 x2 y2.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2)
        ==> ~(ring_add f (ring_1 f)
              (ring_mul f d
                 (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2)))) =
              ring_0 f) /\
            ~(ring_sub f (ring_1 f)
              (ring_mul f d
                 (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2)))) =
              ring_0 f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[edwards_curve; GSYM DE_MORGAN_THM] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  UNDISCH_TAC `edwards_nonsingular(f,a:A,d)` THEN
  ASM_SIMP_TAC[EDWARDS_NONSINGULAR_ALT] THEN
  REWRITE_TAC[TAUT `~(p /\ ~q) <=> p ==> q`; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  MATCH_MP_TAC(MESON[] `!a b. P a \/ P b ==> ?x. P x`) THEN
  EXISTS_TAC `ring_inv f (ring_mul f x1 y2):A` THEN
  EXISTS_TAC `ring_inv f (ring_mul f e (ring_mul f x1 x2)):A` THEN
  ASM_SIMP_TAC[RING_INV; RING_MUL] THEN FIELD_TAC);;

let EDWARDS_NONSINGULAR_DENOMINATORS_POINTS =
  GEN_REWRITE_RULE (funpow 4 BINDER_CONV) [FORALL_UNPAIR_THM]
   (GEN_REWRITE_RULE (funpow 3 BINDER_CONV) [FORALL_UNPAIR_THM]
      EDWARDS_NONSINGULAR_DENOMINATORS);;

let EDWARDS_CURVE_IMP_POINT = prove
 (`!f a d p. edwards_curve(f,a,d) p ==> edwards_point f p`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[edwards_curve; edwards_point]);;

let EDWARDS_POINT_NEG = prove
 (`!(f:A ring) a d p.
        edwards_point f p
        ==> edwards_point f (edwards_neg (f,a,d) p)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  SIMP_TAC[edwards_neg; edwards_point; RING_NEG]);;

let EDWARDS_POINT_ADD = prove
 (`!(f:A ring) a d p q.
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_point f p /\ edwards_point f q
        ==> edwards_point f (edwards_add (f,a,d) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  SIMP_TAC[edwards_add; edwards_point; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[edwards_point]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let EDWARDS_CURVE_0 = prove
 (`!f a d:A.
        a IN ring_carrier f /\ d IN ring_carrier f
        ==> edwards_curve(f,a,d) (edwards_0(f,a,d))`,
  REWRITE_TAC[edwards_curve; edwards_0] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN RING_TAC);;

let EDWARDS_CURVE_NEG = prove
 (`!f a (d:A) p.
        integral_domain f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_curve(f,a,d) p
        ==> edwards_curve(f,a,d) (edwards_neg (f,a,d) p)`,
  SIMP_TAC[FORALL_PAIR_THM; RING_NEG; edwards_curve; edwards_neg] THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGRAL_DOMAIN_RULE);;

let EDWARDS_CURVE_ADD = prove
 (`!f a (d:A) p q.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p /\ edwards_curve(f,a,d) q
        ==> edwards_curve(f,a,d) (edwards_add (f,a,d) p q)`,
  REWRITE_TAC[FORALL_PAIR_THM; edwards_curve; edwards_add; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`]
    EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN
  FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [edwards_nonsingular]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  RING_PULL_DIV_TAC THEN RING_TAC);;

let EDWARDS_ADD_LID = prove
 (`!f a (d:A) p.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_curve(f,a,d) p
        ==> edwards_add(f,a,d) (edwards_0 (f,a,d)) p = p`,
  REWRITE_TAC[FORALL_PAIR_THM; edwards_curve; edwards_add;
              edwards_0; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC);;

let EDWARDS_ADD_LNEG = prove
 (`!f a (d:A) p.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p
        ==> edwards_add(f,a,d) (edwards_neg (f,a,d) p) p = edwards_0(f,a,d)`,
  REWRITE_TAC[FORALL_PAIR_THM; edwards_curve; edwards_add;
              edwards_neg; edwards_0; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`f:A ring`; `a:A`; `d:A`; `x:A`; `y:A`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`f:A ring`; `a:A`; `d:A`;
                `edwards_neg (f,a,d) (x,y):A#A`; `(x,y):A#A`]
        EDWARDS_NONSINGULAR_DENOMINATORS_POINTS) THEN
  ASM_REWRITE_TAC[edwards_curve; edwards_neg] THEN
  FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [edwards_nonsingular]) THEN
  ANTS_TAC THEN REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC);;

let EDWARDS_ADD_SYM = prove
 (`!f a (d:A) p q.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p /\ edwards_curve(f,a,d) q
        ==> edwards_add (f,a,d) p q = edwards_add (f,a,d) q p`,
  REWRITE_TAC[FORALL_PAIR_THM; edwards_curve; edwards_add; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`]
    EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  MP_TAC(SPECL [`f:A ring`; `a:A`; `d:A`; `x2:A`; `y2:A`; `x1:A`; `y1:A`]
    EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN
  FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [edwards_nonsingular]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  RING_PULL_DIV_TAC THEN RING_TAC);;

let EDWARDS_ADD_ASSOC = prove
 (`!f a (d:A) p q r.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p /\ edwards_curve(f,a,d) q /\
        edwards_curve(f,a,d) r
        ==> edwards_add (f,a,d) p (edwards_add (f,a,d) q r) =
            edwards_add (f,a,d) (edwards_add (f,a,d) p q) r`,
  let lemma = prove
   (`field f /\
     x1 IN ring_carrier f /\ y1 IN ring_carrier f /\
     x2 IN ring_carrier f /\ y2 IN ring_carrier f /\
     ~(y1 = ring_0 f \/ y2 = ring_0 f) /\
     ring_mul f x1 y2 = ring_mul f x2 y1
     ==> ring_div f x1 y1 = ring_div f x2 y2`,
    FIELD_TAC) in
  REWRITE_TAC[FORALL_PAIR_THM; edwards_curve; edwards_add; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`;
    `x2:A`; `y2:A`; `x3:A`; `y3:A`] THEN
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 4 (CONJ_TAC THENL [RING_CARRIER_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EDWARDS_NONSINGULAR_DENOMINATORS o
        snd) THEN
    (ANTS_TAC THENL [ALL_TAC; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]) THEN
    REWRITE_TAC[GSYM edwards_add] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC EDWARDS_CURVE_ADD) THEN
    ASM_REWRITE_TAC[edwards_curve] THEN ASM_MESON_TAC[DIVIDES_REFL];
    ALL_TAC;
    REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) EDWARDS_NONSINGULAR_DENOMINATORS o
        snd) THEN
    (ANTS_TAC THENL [ALL_TAC; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)]) THEN
    REWRITE_TAC[GSYM edwards_add] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC EDWARDS_CURVE_ADD) THEN
    ASM_REWRITE_TAC[edwards_curve] THEN ASM_MESON_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `(x1,y1):A#A`; `(x2,y2):A#A`]
        EDWARDS_NONSINGULAR_DENOMINATORS_POINTS) THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `(x2,y2):A#A`; `(x3,y3):A#A`]
        EDWARDS_NONSINGULAR_DENOMINATORS_POINTS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
  RING_PULL_DIV_TAC THEN RING_TAC);;

let EDWARDS_GROUP = prove
 (`!f a (d:A).
      field f /\
      a IN ring_carrier f /\ d IN ring_carrier f /\
      edwards_nonsingular(f,a,d)
      ==> group_carrier(edwards_group(f,a,d)) = edwards_curve(f,a,d) /\
          group_id(edwards_group(f,a,d)) = edwards_0(f,a,d) /\
          group_inv(edwards_group(f,a,d)) = edwards_neg(f,a,d) /\
          group_mul(edwards_group(f,a,d)) = edwards_add(f,a,d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul; GSYM PAIR_EQ] THEN
  REWRITE_TAC[edwards_group; GSYM(CONJUNCT2 group_tybij)] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN REWRITE_TAC[edwards_curve; edwards_0] THEN
    REWRITE_TAC[RING_0; RING_1] THEN RING_TAC;
    REWRITE_TAC[IN] THEN
    ASM_SIMP_TAC[EDWARDS_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[EDWARDS_CURVE_ADD];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[EDWARDS_ADD_ASSOC];
    REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[EDWARDS_ADD_LID; EDWARDS_ADD_SYM; EDWARDS_CURVE_0];
    REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[EDWARDS_ADD_LNEG; EDWARDS_ADD_SYM; EDWARDS_CURVE_NEG;
                  FIELD_IMP_INTEGRAL_DOMAIN]]);;

let ABELIAN_EDWARDS_GROUP = prove
 (`!f a (d:A).
      field f /\
      a IN ring_carrier f /\ d IN ring_carrier f /\
      edwards_nonsingular(f,a,d)
      ==> abelian_group(edwards_group(f,a,d))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[abelian_group; EDWARDS_GROUP] THEN
  REWRITE_TAC[IN] THEN ASM_MESON_TAC[EDWARDS_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Characterizing low-order points on an Edwards curve.                      *)
(* ------------------------------------------------------------------------- *)

let EDWARDS_GROUP_ORDER_EQ_2 = prove
 (`!f (a:A) d p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        p IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) p = 2 <=>
             p = (ring_0 f,ring_neg f (ring_1 f)))`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_2_ALT] THEN
  ASM_SIMP_TAC[EDWARDS_GROUP; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_PAIR_THM; edwards_0; edwards_neg; PAIR_EQ; IN] THEN
  REWRITE_TAC[edwards_curve] THEN FIELD_TAC);;

let EDWARDS_GROUP_ORDER_EQ_4_EQUIV = prove
 (`!f (a:A) d x y.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        (x,y) IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) (x,y) = 4 <=>
             ring_mul f a (ring_pow f x 2) = ring_1 f /\ y = ring_0 f)`,
  REWRITE_TAC[ARITH_RULE `4 = 2 * 2`] THEN
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_MUL; DIVIDES_2; ARITH_EQ; ARITH_EVEN] THEN
  SIMP_TAC[EDWARDS_GROUP_ORDER_EQ_2; GROUP_POW] THEN
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[GROUP_POW_2; FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[EDWARDS_GROUP] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[edwards_curve; edwards_add; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `x:A`; `y:A`; `x:A`; `y:A`]
    EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN FIELD_TAC);;

let EDWARDS_GROUP_ORDER_EQ_4 = prove
 (`!f (a:A) d a' p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        a' IN ring_carrier f /\ ring_mul f a (ring_pow f a' 2) = ring_1 f /\
        edwards_nonsingular (f,a,d) /\
        p IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) p = 4 <=>
             p = (a',ring_0 f) \/ p = (ring_neg f a',ring_0 f))`,
  REWRITE_TAC[ARITH_RULE `4 = 2 * 2`] THEN
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_MUL; DIVIDES_2; ARITH_EQ; ARITH_EVEN] THEN
  SIMP_TAC[EDWARDS_GROUP_ORDER_EQ_2; GROUP_POW] THEN
  REPLICATE_TAC 4 GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[GROUP_POW_2; FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[EDWARDS_GROUP] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[edwards_curve; edwards_add; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `x:A`; `y:A`; `x:A`; `y:A`]
    EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN FIELD_TAC);;

let EDWARDS_GROUP_ORDER_EQ_8_EQUIV = prove
 (`!f (a:A) d x y.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        (x,y) IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) (x,y) = 8 <=>
             ring_mul f a (ring_pow f x 2) = ring_pow f y 2 /\
             ring_mul f (ring_of_num f 4)
                        (ring_mul f (ring_pow f a 2) (ring_pow f x 4)) =
             ring_pow f (ring_add f (ring_1 f)
                          (ring_mul f a (ring_mul f d (ring_pow f x 4)))) 2)`,
  REWRITE_TAC[ARITH_RULE `8 = 2 * 4`] THEN
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_MUL; DIVIDES_2; ARITH_EQ; ARITH_EVEN] THEN
  SIMP_TAC[GROUP_POW; REWRITE_RULE[PAIR]
     (GEN_REWRITE_RULE (funpow 3 BINDER_CONV) [FORALL_UNPAIR_THM]
     EDWARDS_GROUP_ORDER_EQ_4_EQUIV)] THEN
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[GROUP_POW_2; FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[EDWARDS_GROUP] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[edwards_curve; edwards_add; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `x:A`; `y:A`; `x:A`; `y:A`]
    EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN FIELD_TAC);;
