(* ========================================================================= *)
(* The NIST-recommended elliptic curve P-256, aka secp256r1.                 *)
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

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;
let n_256 = new_definition `n_256 = 115792089210356248762697446949407573529996955224135760342422259061068512044369`;;
let SEED_256 = new_definition `SEED_256 = 0xc49d360886e704936a6678e1139d26b7819f7e90`;;
let c_256 = new_definition `c_256 = 0x7efba1662985be9403cb055c75d4f7e0ce8d84a9c5114abcaf3177680104fa0d`;;
let b_256 = new_definition `b_256 = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b`;;
let G_256 = new_definition `G_256 = SOME(&0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296:int,&0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_256 = prove
 (`p_256 = 2 EXP 256 - 2 EXP 224 + 2 EXP 192 + 2 EXP 96 - 1`,
  REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P256 = time prove
 (`prime p_256`,
  REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "43"; "53"; "107"; "157";
   "173"; "181"; "197"; "241"; "257"; "313"; "641"; "661"; "727"; "757";
   "919"; "1087"; "1531"; "2411"; "3677"; "3769"; "4349"; "17449"; "18169";
   "65537"; "78283"; "490463"; "704251"; "6700417"; "204061199";
   "34282281433"; "66417393611"; "11290956913871"; "46076956964474543";
   "774023187263532362759620327192479577272145303";
   "835945042244614951780389953367877943453916927241"]);;

let PRIME_N256 = time prove
 (`prime n_256`,
  REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "29"; "31"; "37"; "41"; "43";
   "71"; "97"; "127"; "131"; "151"; "229"; "263"; "311"; "337"; "373"; "727";
   "1201"; "1297"; "1511"; "3023"; "3407"; "9547"; "16879"; "17449"; "38189";
   "104471"; "126241"; "155317"; "3969899"; "9350987"; "187019741";
   "191039911"; "311245691"; "622491383"; "1002328039319";
   "208150935158385979"; "2624747550333869278416773953"]);;

(* ------------------------------------------------------------------------- *)
(* Basic sanity check on the (otherwise unused) c parameter.                 *)
(* ------------------------------------------------------------------------- *)

let SANITY_CHECK_256 = prove
 (`(&b_256 pow 2 * &c_256:int == -- &27) (mod &p_256)`,
  REWRITE_TAC[G_256; p_256; b_256; c_256] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p256_group = define
 `p256_group =
   weierstrass_group
    (integer_mod_ring p_256,
     ring_neg (integer_mod_ring p_256) (&3),
     &b_256)`;;

let P256_GROUP = prove
 (`group_carrier p256_group =
     weierstrass_curve
      (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256) /\
   group_id p256_group =
     NONE /\
   group_inv p256_group =
     weierstrass_neg
      (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256) /\
   group_mul p256_group =
     weierstrass_add
      (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256)`,
  REWRITE_TAC[p256_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P256] THEN
  REWRITE_TAC[p_256; b_256; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_256; b_256] P256_GROUP;;

let NO_ROOTS_P256 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_256 == &0) (mod &p_256))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P256 [p_256;b_256]);;

let GENERATOR_IN_GROUP_CARRIER_256 = prove
 (`G_256 IN group_carrier p256_group`,
  REWRITE_TAC[G_256] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G256 = prove
 (`group_element_order p256_group G_256 = n_256`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_256;
           PRIME_N256] THEN
  REWRITE_TAC[G_256; el 1 (CONJUNCTS P256_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_256] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_256 = prove
 (`FINITE(group_carrier p256_group)`,
  REWRITE_TAC[P256_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
  REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P256_GROUP = prove
 (`group_carrier p256_group HAS_SIZE n_256`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_256:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_256; GROUP_ELEMENT_ORDER_G256;
              FINITE_GROUP_CARRIER_256] THEN
  REWRITE_TAC[P256_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P256] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_256; ARITH] THEN
    REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_256; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P256) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_256; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P256_GROUP = prove
 (`subgroup_generated p256_group {G_256} = p256_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_256;
           FINITE_GROUP_CARRIER_256] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G256;
              REWRITE_RULE[HAS_SIZE] SIZE_P256_GROUP]);;

let CYCLIC_P256_GROUP = prove
 (`cyclic_group p256_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P256_GROUP]);;

let ABELIAN_P256_GROUP = prove
 (`abelian_group p256_group`,
  MESON_TAC[CYCLIC_P256_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
