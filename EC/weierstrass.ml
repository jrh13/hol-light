(* ========================================================================= *)
(* The general notion of an elliptic curve, in the basic Weierstrass form.   *)
(* We use the option type to augment it with the "point at infinity" NONE.   *)
(* Follows Washington "Elliptic Curves, Number Theory and Cryptography" p14. *)
(*                                                                           *)
(*         y^2 = x^3 + a * x + b   over some field F                         *)
(*                                                                           *)
(* This isn't general enough for working over characteristics 2 and 3.       *)
(* ========================================================================= *)

needs "EC/misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic definitions and naive cardinality bounds.                           *)
(* ------------------------------------------------------------------------- *)

let weierstrass_point = define
 `(weierstrass_point f NONE <=> T) /\
  (weierstrass_point f (SOME(x:A,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f)`;;

let weierstrass_curve = define
 `(weierstrass_curve(f:A ring,a:A,b:A) NONE <=> T) /\
  (weierstrass_curve(f:A ring,a:A,b:A) (SOME(x,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_pow f y 2 =
        ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b))`;;

let weierstrass_neg = define
 `(weierstrass_neg (f:A ring,a:A,b:A) NONE = NONE) /\
  (weierstrass_neg (f:A ring,a:A,b:A) (SOME(x:A,y)) = SOME(x,ring_neg f y))`;;

let weierstrass_add = define
 `(!y. weierstrass_add (f:A ring,a:A,b:A) NONE y = y) /\
  (!x. weierstrass_add (f:A ring,a:A,b:A) x NONE = x) /\
  (!x1 y1 x2 y2.
        weierstrass_add (f:A ring,a:A,b:A) (SOME(x1,y1)) (SOME(x2,y2)) =
        if x1 = x2 then
          if y1 = y2 /\ ~(y1 = ring_0 f) then
            let m = ring_div f
              (ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2)) a)
              (ring_mul f (ring_of_num f 2) y1) in
            let x3 = ring_sub f (ring_pow f m 2)
                                (ring_mul f (ring_of_num f 2) x1) in
            let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in
            SOME(x3,y3)
          else NONE
        else
          let m = ring_div f (ring_sub f y2 y1) (ring_sub f x2 x1) in
          let x3 = ring_sub f (ring_pow f m 2)
                              (ring_add f x1 x2) in
          let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in
          SOME(x3,y3))`;;

let weierstrass_nonsingular = define
 `weierstrass_nonsingular (f:A ring,a:A,b:A) <=>
        ~(ring_add f (ring_mul f (ring_of_num f 4) (ring_pow f a 3))
                     (ring_mul f (ring_of_num f 27) (ring_pow f b 2)) =
          ring_0 f)`;;

let weierstrass_group = define
 `weierstrass_group (f:A ring,a:A,b:A) =
        group(weierstrass_curve(f,a,b),
              NONE,
              weierstrass_neg(f,a,b),
              weierstrass_add(f,a,b))`;;

let (FINITE_WEIERSTRASS_CURVE,CARD_BOUND_WEIERSTRASS_CURVE) =
 (CONJ_PAIR o prove)
 (`(!f a b:A. field f /\ FINITE(ring_carrier f)
              ==> FINITE(weierstrass_curve(f,a,b))) /\
   (!f a b:A. field f /\ FINITE(ring_carrier f)
              ==> CARD(weierstrass_curve(f,a,b))
                   <= 2 * CARD(ring_carrier f) + 1)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC FINITE_CARD_LE_SUBSET THEN EXISTS_TAC
   `IMAGE SOME
     {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
              ring_pow f y 2 =
              ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b)}
    UNION {NONE}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[weierstrass_curve; SUBSET; FORALL_OPTION_THM;
      IN_UNION; IN_SING; IN_IMAGE; option_INJ; FORALL_PAIR_THM;
      IN_ELIM_PAIR_THM; UNWIND_THM1] THEN
    REWRITE_TAC[option_DISTINCT; IN_CROSS] THEN REWRITE_TAC[IN] THEN
    REWRITE_TAC[weierstrass_curve] THEN SIMP_TAC[IN];
    MATCH_MP_TAC FINITE_CARD_LE_UNION] THEN
  REWRITE_TAC[FINITE_SING; CARD_SING; LE_REFL] THEN
  MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
  MATCH_MP_TAC FINITE_QUADRATIC_CURVE THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Proof of the group properties. This is just done by algebraic brute       *)
(* force except for the use of ASSOCIATIVITY_LEMMA to reduce the explosion   *)
(* of case distinctions.                                                     *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_CURVE_IMP_POINT = prove
 (`!f a b p. weierstrass_curve(f,a,b) p ==> weierstrass_point f p`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[weierstrass_curve; weierstrass_point]);;

let WEIERSTRASS_POINT_NEG = prove
 (`!(f:A ring) a b p.
        weierstrass_point f p
        ==> weierstrass_point f (weierstrass_neg (f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[weierstrass_neg; weierstrass_point; RING_NEG]);;

let WEIERSTRASS_POINT_ADD = prove
 (`!(f:A ring) a b p q.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_point f (weierstrass_add (f,a,b) p q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[weierstrass_add; weierstrass_point; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[weierstrass_point]) THEN
  REPEAT STRIP_TAC THEN RING_CARRIER_TAC);;

let WEIERSTRASS_CURVE_0 = prove
 (`!f a b:A. weierstrass_curve(f,a,b) NONE`,
  REWRITE_TAC[weierstrass_curve]);;

let WEIERSTRASS_CURVE_NEG = prove
 (`!f a (b:A) p.
        integral_domain f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p
        ==> weierstrass_curve(f,a,b) (weierstrass_neg (f,a,b) p)`,
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_NEG;
              weierstrass_curve; weierstrass_neg] THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGRAL_DOMAIN_RULE);;

let WEIERSTRASS_CURVE_ADD = prove
 (`!f a (b:A) p q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\ weierstrass_curve(f,a,b) q
        ==> weierstrass_curve(f,a,b) (weierstrass_add (f,a,b) p q)`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              weierstrass_curve; weierstrass_add] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[weierstrass_curve] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    SUBGOAL_THEN `~(ring_of_num f 2:A = ring_0 f)` ASSUME_TAC THENL
     [FIELD_TAC; RING_PULL_DIV_TAC THEN RING_TAC];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_curve] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let WEIERSTRASS_ADD_LNEG = prove
 (`!f a (b:A) p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p
        ==> weierstrass_add(f,a,b) (weierstrass_neg (f,a,b) p) p = NONE`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              weierstrass_curve; weierstrass_neg; weierstrass_add] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC);;

let WEIERSTRASS_ADD_SYM = prove
 (`!f a (b:A) p q.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\ weierstrass_curve(f,a,b) q
        ==> weierstrass_add (f,a,b) p q = weierstrass_add (f,a,b) q p`,
  REPLICATE_TAC 3 GEN_TAC THEN
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; RING_ADD;
              weierstrass_curve; weierstrass_add] THEN
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

let WEIERSTRASS_ADD_ASSOC = prove
 (`!f a (b:A) p q r.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        weierstrass_nonsingular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\
        weierstrass_curve(f,a,b) q /\
        weierstrass_curve(f,a,b) r
        ==> weierstrass_add (f,a,b) p (weierstrass_add (f,a,b) q r) =
            weierstrass_add (f,a,b) (weierstrass_add (f,a,b) p q) r`,
  let assoclemma = prove
   (`!f (a:A) b x1 y1 x2 y2.
          field f /\
          a IN ring_carrier f /\ b IN ring_carrier f /\
          weierstrass_curve(f,a,b) (SOME(x1,y1)) /\
          weierstrass_curve(f,a,b) (SOME(x2,y2))
          ==> (~(SOME(x2,y2) = SOME(x1,y1)) /\
               ~(SOME(x2,y2) = weierstrass_neg (f,a,b) (SOME(x1,y1))) <=>
               ~(x1 = x2))`,
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_INJ; PAIR_EQ] THEN
    FIELD_TAC) in
  REWRITE_TAC[FIELD_CHAR_NOT23] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `f:A ring` THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; RIGHT_IMP_FORALL_THM] THEN
  MATCH_MP_TAC ASSOCIATIVITY_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`weierstrass_neg(f,a:A,b)`; `NONE:(A#A)option`] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC(CONJUNCT1 weierstrass_curve :: CONJUNCT1 weierstrass_neg ::
              fst(chop_list 2 (CONJUNCTS weierstrass_add))) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [REPEAT CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`] THEN
    TRY(MAP_EVERY X_GEN_TAC [`x2:A`; `y2:A`]) THEN
    TRY(MAP_EVERY X_GEN_TAC [`x3:A`; `y3:A`]);
    MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`; `x3:A`; `y3:A`] THEN
    ASM_SIMP_TAC[assoclemma; DE_MORGAN_THM] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[weierstrass_curve] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[weierstrass_add]] THEN
  REWRITE_TAC[weierstrass_curve; weierstrass_add; weierstrass_neg] THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT LET_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[weierstrass_curve; weierstrass_add; weierstrass_neg] THEN
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
  (FIELD_TAC ORELSE
   (RULE_ASSUM_TAC(REWRITE_RULE[weierstrass_nonsingular]) THEN FIELD_TAC)) THEN
  NOT_RING_CHAR_DIVIDES_TAC);;

let WEIERSTRASS_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      weierstrass_nonsingular(f,a,b)
      ==> group_carrier(weierstrass_group(f,a,b)) = weierstrass_curve(f,a,b) /\
          group_id(weierstrass_group(f,a,b)) = NONE /\
          group_inv(weierstrass_group(f,a,b)) = weierstrass_neg(f,a,b) /\
          group_mul(weierstrass_group(f,a,b)) = weierstrass_add(f,a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul; GSYM PAIR_EQ] THEN
  REWRITE_TAC[weierstrass_group; GSYM(CONJUNCT2 group_tybij)] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN; weierstrass_curve];
    REWRITE_TAC[IN] THEN
    ASM_SIMP_TAC[WEIERSTRASS_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[WEIERSTRASS_CURVE_ADD];
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[WEIERSTRASS_ADD_ASSOC];
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; weierstrass_add];
    REWRITE_TAC[IN] THEN GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(MESON[]
     `x = a /\ x = y ==> x = a /\ y = a`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[WEIERSTRASS_ADD_LNEG];
      MATCH_MP_TAC WEIERSTRASS_ADD_SYM THEN
      ASM_SIMP_TAC[WEIERSTRASS_CURVE_NEG; FIELD_IMP_INTEGRAL_DOMAIN]]]);;

(* ------------------------------------------------------------------------- *)
(* Easily computable endomorphisms in some special Weierstrass curves.       *)
(* (x,y) |-> (c * x,y) where c^3 = 1 for curves y^2 = x^3 + b.               *)
(* (x,y) |-> (-x, c * y) where c^4 = 1 for curves y^2 = x^3 + a * x.         *)
(* ------------------------------------------------------------------------- *)

let weierstrass_triplex = define
 `weierstrass_triplex f (c:A) NONE = NONE /\
  weierstrass_triplex f c (SOME(x:A,y:A)) = SOME(ring_mul f c x,y)`;;

let GROUP_ENDOMORPHISM_TRIPLEX = prove
 (`!f a b c:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_nonsingular (f,a,b) /\
        c IN ring_carrier f /\ ring_pow f c 3 = ring_1 f /\ a = ring_0 f
        ==> group_endomorphism (weierstrass_group(f,a,b))
                               (weierstrass_triplex f c)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:A = ring_0 f` THEN
  ASM_SIMP_TAC[group_endomorphism; GROUP_HOMOMORPHISM] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; WEIERSTRASS_GROUP; GROUP_ID] THEN
  POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[FIELD_CHAR_NOT23] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; IN] THEN
  REWRITE_TAC[weierstrass_curve; weierstrass_triplex; weierstrass_add] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_triplex] THEN
  TRY RING_CARRIER_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[weierstrass_nonsingular]) THEN FIELD_TAC);;

let weierstrass_quady = define
 `weierstrass_quady f (c:A) NONE = NONE /\
  weierstrass_quady f c (SOME(x:A,y:A)) = SOME(ring_neg f x,ring_mul f c y)`;;

let GROUP_ENDOMORPHISM_QUADY = prove
 (`!f a b c:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_nonsingular (f,a,b) /\
        c IN ring_carrier f /\ b = ring_0 f /\
        ring_pow f c 4 = ring_1 f /\ ~(ring_pow f c 2 = ring_1 f)
        ==> group_endomorphism (weierstrass_group(f,a,b))
                               (weierstrass_quady f c)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:A = ring_0 f` THEN
  ASM_SIMP_TAC[group_endomorphism; GROUP_HOMOMORPHISM] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; WEIERSTRASS_GROUP; GROUP_ID] THEN
  POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[FIELD_CHAR_NOT23] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; IN] THEN
  REWRITE_TAC[weierstrass_curve; weierstrass_quady; weierstrass_add] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT LET_TAC THEN REWRITE_TAC[weierstrass_quady] THEN
  TRY RING_CARRIER_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[weierstrass_nonsingular]) THEN FIELD_TAC THEN
  NOT_RING_CHAR_DIVIDES_TAC);;
