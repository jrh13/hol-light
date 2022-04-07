(* ========================================================================= *)
(* The SECG-recommended elliptic curve secp192k1.                            *)
(* ========================================================================= *)

needs "EC/weierstrass.ml";;
needs "EC/excluderoots.ml";;
needs "EC/computegroup.ml";;

add_curve weierstrass_curve;;
add_curveneg weierstrass_neg;;
add_curveadd weierstrass_add;;

(* ------------------------------------------------------------------------- *)
(* The SECG curve parameters, copied from the SEC 2 document.                *)
(* See https://www.secg.org/sec2-v2.pdf                                      *)
(* ------------------------------------------------------------------------- *)

let p_192k1 = define `p_192k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFEE37`;;
let n_192k1 = define `n_192k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFE26F2FC170F69466A74DEFD8D`;;
let G_192K1 = define `G_192K1 = SOME(&0xDB4FF10EC057E9AE26B07D0280B7F4341DA5D1B1EAE06C7D:int,&0x9B2F2F6D9C5628A7844163D015BE86344082AA88D95E2F9D:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_192K1 = prove
 (`p_192k1 = 2 EXP 192 - 2 EXP 32 - 4553`,
  REWRITE_TAC[p_192k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_192K1_ALT = prove
 (`p_192k1 =
   2 EXP 192 - 2 EXP 32 - 2 EXP 12 - 2 EXP 8 - 2 EXP 7 - 2 EXP 6 - 2 EXP 3 - 1`,
  REWRITE_TAC[p_192k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P192K1 = time prove
 (`prime p_192k1`,
  REWRITE_TAC[p_192k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "37"; "41"; "43";
   "47"; "61"; "79"; "103"; "149"; "193"; "251"; "281"; "487"; "563"; "1559";
   "2473"; "2683"; "3119"; "7057"; "393721"; "706151"; "3651619"; "8473813";
   "14606477"; "2307823367"; "11113956389"; "16189543961"; "138580737803";
   "1295233555201613"; "10489845818524887021689201254173392444641"]);;

let PRIME_N192K1 = time prove
 (`prime n_192k1`,
  REWRITE_TAC[n_192k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "41"; "59";
   "73"; "83"; "97"; "137"; "167"; "443"; "971"; "2341"; "4933"; "11519";
   "29131"; "54151"; "169361"; "444791"; "445097"; "552913"; "815669";
   "866417"; "1611297632578441"; "31767070186748510944261247684750677";
   "434093022356392396149847294750353440317757907331";
   "143250697377609490729449607267616635304860109419231"]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p192k1_group = define
 `p192k1_group = weierstrass_group(integer_mod_ring p_192k1,&0,&3)`;;

let P192K1_GROUP = prove
 (`group_carrier p192k1_group =
     weierstrass_curve(integer_mod_ring p_192k1,&0,&3) /\
   group_id p192k1_group =
     NONE /\
   group_inv p192k1_group =
     weierstrass_neg(integer_mod_ring p_192k1,&0,&3) /\
   group_mul p192k1_group =
     weierstrass_add(integer_mod_ring p_192k1,&0,&3)`,
  REWRITE_TAC[p192k1_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P192K1] THEN
  REWRITE_TAC[p_192k1; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_192k1] P192K1_GROUP;;

let NO_ROOTS_192K1 = prove
 (`!x:int. ~((x pow 3 + &3 == &0) (mod &p_192k1))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P192K1 [p_192k1]);;

let GENERATOR_IN_GROUP_CARRIER_192K1 = prove
 (`G_192K1 IN group_carrier p192k1_group`,
  REWRITE_TAC[G_192K1] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G192K1 = prove
 (`group_element_order p192k1_group G_192K1 = n_192k1`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_192K1; PRIME_N192K1] THEN
  REWRITE_TAC[G_192K1; el 1 (CONJUNCTS P192K1_GROUP);
              option_DISTINCT] THEN
  REWRITE_TAC[n_192k1] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_192K1 = prove
 (`FINITE(group_carrier p192k1_group)`,
  REWRITE_TAC[P192K1_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING;
              FIELD_INTEGER_MOD_RING; PRIME_P192K1] THEN
  REWRITE_TAC[p_192k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P192K1_GROUP = prove
 (`group_carrier p192k1_group HAS_SIZE n_192k1`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_192K1:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_192K1;
              GROUP_ELEMENT_ORDER_G192K1;
              FINITE_GROUP_CARRIER_192K1] THEN
  REWRITE_TAC[P192K1_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P192K1] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_192k1] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_192k1; ARITH] THEN
    REWRITE_TAC[n_192k1] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_192k1; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_192K1) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_192k1; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P192K1_GROUP = prove
 (`subgroup_generated p192k1_group {G_192K1} = p192k1_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_192K1;
           FINITE_GROUP_CARRIER_192K1] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G192K1;
              REWRITE_RULE[HAS_SIZE] SIZE_P192K1_GROUP]);;

let CYCLIC_P192K1_GROUP = prove
 (`cyclic_group p192k1_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P192K1_GROUP]);;

let ABELIAN_P192K1_GROUP = prove
 (`abelian_group p192k1_group`,
  MESON_TAC[CYCLIC_P192K1_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
