(* ========================================================================= *)
(* The NIST-recommended elliptic curve P-192, aka secp192r1.                 *)
(* ========================================================================= *)

needs "EC/weierstrass.ml";;
needs "EC/excluderoots.ml";;
needs "EC/computegroup.ml";;

add_curve weierstrass_curve;;
add_curveneg weierstrass_neg;;
add_curveadd weierstrass_add;;

(* ------------------------------------------------------------------------- *)
(* The NIST curve parameters, copied from the NIST FIPS 186-4 document.      *)
(* See https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf            *)
(* ------------------------------------------------------------------------- *)

let p_192 = new_definition `p_192 = 6277101735386680763835789423207666416083908700390324961279`;;
let n_192 = new_definition `n_192 = 6277101735386680763835789423176059013767194773182842284081`;;
let SEED_192 = new_definition `SEED_192 = 0x3045ae6fc8422f64ed579528d38120eae12196d5`;;
let c_192 = new_definition `c_192 = 0x3099d2bbbfcb2538542dcd5fb078b6ef5f3d6fe2c745de65`;;
let b_192 = new_definition `b_192 = 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1`;;
let G_192 = new_definition `G_192 = SOME(&0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012:int,&0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_192 = prove
 (`p_192 = 2 EXP 192 - 2 EXP 64 - 1`,
  REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P192 = time prove
 (`prime p_192`,
  REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
   ["2"; "3"; "5"; "7"; "11"; "17"; "19"; "23"; "29"; "31"; "37"; "41"; "43";
   "47"; "59"; "61"; "101"; "103"; "151"; "163"; "191"; "229"; "283"; "607";
   "619"; "631"; "907"; "2477"; "54251"; "149309"; "275729"; "379787";
   "723127"; "8413201"; "11393611"; "252396031"; "455827231987";
   "108341181769254293"; "5933177618131140283";
   "288626509448065367648032903"]);;

let PRIME_N192 = time prove
 (`prime n_192`,
  REWRITE_TAC[n_192] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "29"; "31"; "43"; "47"; "59";
   "61"; "71"; "73"; "103"; "199"; "239"; "331"; "439"; "547"; "569"; "881";
   "1031"; "1693"; "1889"; "2063"; "2389"; "4127"; "6829"; "51419"; "53197";
   "54623"; "60449"; "15716741"; "46245989"; "51920273"; "103840547";
   "7244839476697597"; "7532705587894727"; "9564682313913860059195669";
   "3433859179316188682119986911"]);;

(* ------------------------------------------------------------------------- *)
(* Basic sanity check on the (otherwise unused) c parameter.                 *)
(* ------------------------------------------------------------------------- *)

let SANITY_CHECK_192 = prove
 (`(&b_192 pow 2 * &c_192:int == -- &27) (mod &p_192)`,
  REWRITE_TAC[G_192; p_192; b_192; c_192] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p192_group = define
 `p192_group =
   weierstrass_group
    (integer_mod_ring p_192,
     ring_neg (integer_mod_ring p_192) (&3),
     &b_192)`;;

let P192_GROUP = prove
 (`group_carrier p192_group =
     weierstrass_curve
      (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192) /\
   group_id p192_group =
     NONE /\
   group_inv p192_group =
     weierstrass_neg
      (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192) /\
   group_mul p192_group =
     weierstrass_add
      (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192)`,
  REWRITE_TAC[p192_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P192] THEN
  REWRITE_TAC[p_192; b_192; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_192; b_192] P192_GROUP;;

let NO_ROOTS_P192 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_192 == &0) (mod &p_192))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P192 [p_192;b_192]);;

let GENERATOR_IN_GROUP_CARRIER_192 = prove
 (`G_192 IN group_carrier p192_group`,
  REWRITE_TAC[G_192] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G192 = prove
 (`group_element_order p192_group G_192 = n_192`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_192;
           PRIME_N192] THEN
  REWRITE_TAC[G_192; el 1 (CONJUNCTS P192_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_192] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_192 = prove
 (`FINITE(group_carrier p192_group)`,
  REWRITE_TAC[P192_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P192] THEN
  REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P192_GROUP = prove
 (`group_carrier p192_group HAS_SIZE n_192`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_192:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_192; GROUP_ELEMENT_ORDER_G192;
              FINITE_GROUP_CARRIER_192] THEN
  REWRITE_TAC[P192_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P192] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_192] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_192; ARITH] THEN
    REWRITE_TAC[n_192] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_192; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P192) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_192; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P192_GROUP = prove
 (`subgroup_generated p192_group {G_192} = p192_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_192;
           FINITE_GROUP_CARRIER_192] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G192;
              REWRITE_RULE[HAS_SIZE] SIZE_P192_GROUP]);;

let CYCLIC_P192_GROUP = prove
 (`cyclic_group p192_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P192_GROUP]);;

let ABELIAN_P192_GROUP = prove
 (`abelian_group p192_group`,
  MESON_TAC[CYCLIC_P192_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
