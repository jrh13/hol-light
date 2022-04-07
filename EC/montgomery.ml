(* ========================================================================= *)
(* Montgomery curves in general, B * y^2 = x^3 + A * x^2 + x.                *)
(* ========================================================================= *)

needs "EC/misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic definitions and naive cardinality bounds.                           *)
(* ------------------------------------------------------------------------- *)

let montgomery_point = define
 `(montgomery_point f NONE <=> T) /\
  (montgomery_point f (SOME(x:A,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f)`;;

let montgomery_curve = define
 `(montgomery_curve(f:A ring,a:A,b:A) NONE <=> T) /\
  (montgomery_curve(f:A ring,a:A,b:A) (SOME(x,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_mul f b (ring_pow f y 2) =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_pow f x 2)) x))`;;

let montgomery_nonsingular = define
 `montgomery_nonsingular (f:A ring,a:A,b:A) <=>
        ~(b = ring_0 f) /\ ~(ring_pow f a 2 = ring_of_num f 4)`;;

let montgomery_neg = define
 `(montgomery_neg (f:A ring,a:A,b:A) NONE = NONE) /\
  (montgomery_neg (f:A ring,a:A,b:A) (SOME(x:A,y)) = SOME(x,ring_neg f y))`;;

let montgomery_add = define
 `(!y. montgomery_add (f:A ring,a:A,b:A) NONE y = y) /\
  (!x. montgomery_add (f:A ring,a:A,b:A) x NONE = x) /\
  (!x1 y1 x2 y2.
        montgomery_add (f:A ring,a:A,b:A) (SOME(x1,y1)) (SOME(x2,y2)) =
        if x1 = x2 then
          if y1 = y2 /\ ~(y1 = ring_0 f) then
            let l = ring_div f
                (ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
                            (ring_add f (ring_mul f (ring_of_num f 2)
                                                    (ring_mul f a x1))
                                        (ring_of_num f 1)))
                (ring_mul f (ring_of_num f 2) (ring_mul f b y1)) in
            let x3 = ring_sub f (ring_sub f (ring_mul f b (ring_pow f l 2)) a)
                                (ring_mul f (ring_of_num f 2) x1) in
            let y3 = ring_sub f (ring_mul f l (ring_sub f x1 x3)) y1 in
            SOME(x3,y3)
          else NONE
        else
          let l = ring_div f (ring_sub f y2 y1) (ring_sub f x2 x1) in
          let x3 = ring_sub f (ring_sub f (ring_mul f b (ring_pow f l 2)) a)
                              (ring_add f x1 x2) in
          let y3 = ring_sub f (ring_mul f l (ring_sub f x1 x3)) y1 in
          SOME(x3,y3))`;;

let montgomery_group = define
 `montgomery_group (f:A ring,a:A,b:A) =
        group(montgomery_curve(f,a,b),
              NONE,
              montgomery_neg(f,a,b),
              montgomery_add(f,a,b))`;;

let FINITE_MONTGOMERY_CURVE = prove
 (`!f a b:A. field f /\ FINITE(ring_carrier f)
             ==> FINITE(montgomery_curve(f,a,b))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE SOME {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f} UNION
    {NONE}` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_SING; FINITE_PRODUCT] THEN
  REWRITE_TAC[montgomery_curve; SUBSET; FORALL_OPTION_THM;
              IN_UNION; IN_SING; IN_IMAGE; option_INJ; FORALL_PAIR_THM;
              IN_ELIM_PAIR_THM; UNWIND_THM1] THEN
  SIMP_TAC[montgomery_curve; IN]);;

let CARD_BOUND_MONTGOMERY_CURVE = prove
 (`!f a b:A. field f /\ FINITE(ring_carrier f) /\
             a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f)
             ==> CARD(montgomery_curve(f,a,b))
                   <= 2 * CARD(ring_carrier f) + 1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_SUBSET; CARD_SUBSET; LE_TRANS]
   `!s. t SUBSET s /\ FINITE s /\ CARD s <= n ==> CARD t <= n`) THEN
  EXISTS_TAC
   `IMAGE SOME
     {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
              ring_pow f y 2 =
              ring_div f (ring_add f (ring_pow f x 3)
                           (ring_add f (ring_mul f a (ring_pow f x 2)) x)) b}
    UNION {NONE}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[montgomery_curve; SUBSET; FORALL_OPTION_THM;
      IN_UNION; IN_SING; IN_IMAGE; option_INJ; FORALL_PAIR_THM;
      IN_ELIM_PAIR_THM; UNWIND_THM1] THEN
    REWRITE_TAC[option_DISTINCT; IN_CROSS] THEN
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
    ASM_REWRITE_TAC[montgomery_curve] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIELD_TAC;
    MATCH_MP_TAC FINITE_CARD_LE_UNION] THEN
  REWRITE_TAC[FINITE_SING; CARD_SING; LE_REFL] THEN
  MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
  MATCH_MP_TAC FINITE_QUADRATIC_CURVE THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* A stronger form of nonsingularity, implying not only that the core cubic  *)
(* doesn't have repeated roots but has no roots at all except for (0,0).     *)
(* ------------------------------------------------------------------------- *)

let montgomery_strongly_nonsingular = define
  `montgomery_strongly_nonsingular(f,a:A,b:A) <=>
      ~(b = ring_0 f) /\
      ~(?z. z IN ring_carrier f /\
            ring_pow f z 2 = ring_sub f (ring_pow f a 2) (ring_of_num f 4))`;;

let MONTGOMERY_STRONGLY_NONSINGULAR = prove
 (`!f a b:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f
        ==> (montgomery_strongly_nonsingular(f,a,b) <=>
             !x y. montgomery_curve(f,a,b) (SOME(x,y))
                   ==> (y = ring_0 f <=> x = ring_0 f))`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[montgomery_strongly_nonsingular] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT
   `p ==> (q <=> r) <=> (r ==> p ==> q) /\ (q ==> p ==> r)`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[montgomery_curve] THEN BINOP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> q) /\ (p ==> ~q) ==> (~p <=> q)`) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC;
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o SPEC `ring_1 f:A`) THEN
      REWRITE_TAC[NOT_IMP] THEN
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC];
    REWRITE_TAC[GSYM NOT_EXISTS_THM; montgomery_curve;
                TAUT `p ==> q <=> ~(p /\ ~q)`] THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ring_div f (ring_sub f z a) (ring_of_num f 2):A`;
      DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ring_add f (ring_mul f (ring_of_num f 2) x) a:A`] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC]);;

let MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR = prove
 (`!f a b:A.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_strongly_nonsingular(f,a,b)
        ==> montgomery_nonsingular(f,a,b)`,
  REWRITE_TAC[montgomery_strongly_nonsingular; montgomery_nonsingular] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_0 f:A`) THEN
  ASM_REWRITE_TAC[RING_0] THEN RING_TAC);;

(* ------------------------------------------------------------------------- *)
(* Proof of the group properties. This is just done by algebraic brute       *)
(* force except for the use of ASSOCIATIVITY_LEMMA to reduce the explosion   *)
(* of case distinctions.                                                     *)
(* ------------------------------------------------------------------------- *)

let MONTGOMERY_CURVE_IMP_POINT = prove
 (`!f a b p. montgomery_curve(f,a,b) p ==> montgomery_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[montgomery_curve; montgomery_point]);;

let MONTGOMERY_POINT_NEG = prove
 (`!(f:A ring) a b p.
        montgomery_point f p
        ==> montgomery_point f (montgomery_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[montgomery_neg; montgomery_point; RING_NEG]);;

let MONTGOMERY_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_point f p /\ montgomery_point f q
        ==> montgomery_point f (montgomery_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[montgomery_add; montgomery_point; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_point]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let MONTGOMERY_CURVE_0 = prove
 (`!f a b:A. montgomery_curve(f,a,b) NONE`,
  REWRITE_TAC[montgomery_curve]);;

let MONTGOMERY_CURVE_NEG = prove
 (`!f a (b:A) p.
        integral_domain f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p
        ==> montgomery_curve(f,a,b) (montgomery_neg (f,a,b) p)`,
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_NEG;
              montgomery_curve; montgomery_neg] THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGRAL_DOMAIN_RULE);;

let MONTGOMERY_CURVE_ADD = prove
 (`!f a (b:A) p q.
        field f /\ ~(ring_char f = 2) /\
        montgomery_nonsingular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p /\ montgomery_curve(f,a,b) q
        ==> montgomery_curve(f,a,b) (montgomery_add (f,a,b) p q)`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
           montgomery_nonsingular; montgomery_curve; montgomery_add] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[montgomery_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MONTGOMERY_ADD_LNEG = prove
 (`!f a (b:A) p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p
        ==> montgomery_add(f,a,b) (montgomery_neg (f,a,b) p) p = NONE`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              montgomery_curve; montgomery_neg; montgomery_add] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC);;

let MONTGOMERY_ADD_SYM = prove
 (`!f a (b:A) p q.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p /\ montgomery_curve(f,a,b) q
        ==> montgomery_add (f,a,b) p q = montgomery_add (f,a,b) q p`,
  REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              montgomery_curve; montgomery_add] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT LET_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC);;

let MONTGOMERY_ADD_ASSOC = prove
 (`!f a (b:A) p q r.
        field f /\ ~(ring_char f = 2) /\
        montgomery_nonsingular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p /\
        montgomery_curve(f,a,b) q /\
        montgomery_curve(f,a,b) r
        ==> montgomery_add (f,a,b) p (montgomery_add (f,a,b) q r) =
            montgomery_add (f,a,b) (montgomery_add (f,a,b) p q) r`,
  let assoclemma = prove
   (`!f (a:A) b x1 y1 x2 y2.
          field f /\
          montgomery_nonsingular(f,a,b) /\
          a IN ring_carrier f /\ b IN ring_carrier f /\
          montgomery_curve(f,a,b) (SOME(x1,y1)) /\
          montgomery_curve(f,a,b) (SOME(x2,y2))
          ==> (~(SOME(x2,y2) = SOME(x1,y1)) /\
               ~(SOME(x2,y2) = montgomery_neg (f,a,b) (SOME(x1,y1))) <=>
               ~(x1 = x2))`,
    REWRITE_TAC[montgomery_nonsingular] THEN
    REWRITE_TAC[montgomery_curve; montgomery_neg; option_INJ; PAIR_EQ] THEN
    FIELD_TAC) in
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `f:A ring` THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; RIGHT_IMP_FORALL_THM] THEN
  MATCH_MP_TAC ASSOCIATIVITY_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`montgomery_neg(f,a:A,b)`; `NONE:(A#A)option`] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC(CONJUNCT1 montgomery_curve :: CONJUNCT1 montgomery_neg ::
              fst(chop_list 2 (CONJUNCTS montgomery_add))) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [REPEAT CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`] THEN REPEAT CONJ_TAC THEN
    TRY(MAP_EVERY X_GEN_TAC [`x2:A`; `y2:A`]) THEN REPEAT CONJ_TAC THEN
    TRY(MAP_EVERY X_GEN_TAC [`x3:A`; `y3:A`]) THEN REPEAT CONJ_TAC;
    MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`; `x3:A`; `y3:A`] THEN
    ASM_SIMP_TAC[assoclemma; DE_MORGAN_THM] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[montgomery_curve] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[montgomery_add]] THEN
  REWRITE_TAC[montgomery_curve; montgomery_add; montgomery_neg] THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT LET_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[montgomery_curve; montgomery_add; montgomery_neg] THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT LET_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
    (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
               is_var(rand(concl th))))) THEN
  TRY RING_CARRIER_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[montgomery_nonsingular]) THEN FIELD_TAC THEN
  NOT_RING_CHAR_DIVIDES_TAC);;

let MONTGOMERY_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> group_carrier(montgomery_group(f,a,b)) = montgomery_curve(f,a,b) /\
          group_id(montgomery_group(f,a,b)) = NONE /\
          group_inv(montgomery_group(f,a,b)) = montgomery_neg(f,a,b) /\
          group_mul(montgomery_group(f,a,b)) = montgomery_add(f,a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul; GSYM PAIR_EQ] THEN
  REWRITE_TAC[montgomery_group; GSYM(CONJUNCT2 group_tybij)] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN; montgomery_curve];
    REWRITE_TAC[IN] THEN
    ASM_SIMP_TAC[MONTGOMERY_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[MONTGOMERY_CURVE_ADD];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[MONTGOMERY_ADD_ASSOC];
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; montgomery_add];
    REWRITE_TAC[IN] THEN GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(MESON[]
     `x = a /\ x = y ==> x = a /\ y = a`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[MONTGOMERY_ADD_LNEG];
      MATCH_MP_TAC MONTGOMERY_ADD_SYM THEN
      ASM_SIMP_TAC[MONTGOMERY_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN]]]);;

let ABELIAN_MONTGOMERY_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> abelian_group(montgomery_group(f,a,b))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[abelian_group; MONTGOMERY_GROUP] THEN
  REWRITE_TAC[IN] THEN ASM_MESON_TAC[MONTGOMERY_ADD_SYM]);;
