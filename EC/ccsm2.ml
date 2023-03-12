(* ========================================================================= *)
(* The GM/T 0003.1 SM2 elliptic curve for commercial cryptography.           *)
(* ========================================================================= *)

needs "EC/weierstrass.ml";;
needs "EC/excluderoots.ml";;
needs "EC/computegroup.ml";;

add_curve weierstrass_curve;;
add_curveneg weierstrass_neg;;
add_curveadd weierstrass_add;;

(* ------------------------------------------------------------------------- *)
(* The curve parameters, with a = -3 assumed.                                *)
(* ------------------------------------------------------------------------- *)

(*** Taken from Table 11 in section 5.2.9 of
https://trustedcomputinggroup.org/wp-content/uploads/TCGAlgorithmRegistry_Rev01.15.pdf
*** except we just consider a = -3 modulo the prime so don't represent it explicitly.
***)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;
let n_sm2 = new_definition `n_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123`;;
let b_sm2 = new_definition `b_sm2 = 0x28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93`;;
let g_sm2 = new_definition `g_sm2 = SOME(&0x32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7:int,&0xBC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0:int)`;;

let ccsm2 = define
 `ccsm2 =
    (integer_mod_ring p_sm2,
     ring_neg (integer_mod_ring p_sm2) (&3),
     &b_sm2:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_SM2 = prove
 (`p_sm2 = 2 EXP 256 - 2 EXP 224 - 2 EXP 96 + 2 EXP 64 - 1`,
  REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_PSM2 = time prove
 (`prime p_sm2`,
  REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "43";
   "53"; "61"; "67"; "71"; "73"; "79"; "97"; "101"; "103"; "137"; "241";
   "337"; "367"; "571"; "743"; "769"; "823"; "1213"; "1447"; "2273"; "2473";
   "4547"; "5303"; "5711"; "30223"; "34511"; "54983"; "71209"; "179429";
   "363761"; "3079049"; "6158099"; "8214737"; "3017783777"; "348253387243";
   "4641351449027"; "417514796639753"; "4773264379806847";
   "66013261729388519804782124120027";
   "115792089210356248756420345214020892766250353991924191454421193933289684991999"]);;

let PRIME_NSM2 = time prove
 (`prime n_sm2`,
  REWRITE_TAC[n_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "29"; "31"; "41"; "43"; "53";
   "59"; "61"; "71"; "79"; "83"; "89"; "101"; "103"; "127"; "179"; "181";
   "233"; "251"; "359"; "431"; "719"; "1013"; "3037"; "3049"; "4957"; "5801";
   "7759"; "12149"; "14057"; "84163"; "110899"; "9061163"; "10042883";
   "17965699"; "107615843"; "117774739"; "1413296869"; "2566129871";
   "2368433183657"; "5636460199499"; "101456283590983"; "3258964060712033";
   "18120927127286907576013935251791662753637";
   "125197554539772723432468576818475380947471091418362477724521";
   "115792089210356248756420345214020892766061623724957744567843809356293439045923"]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let sm2_group = define
 `sm2_group =
   weierstrass_group
    (integer_mod_ring p_sm2,
     ring_neg (integer_mod_ring p_sm2) (&3),
     &b_sm2)`;;

let SM2_GROUP = prove
 (`group_carrier sm2_group =
     weierstrass_curve
      (integer_mod_ring p_sm2,ring_neg (integer_mod_ring p_sm2) (&3),&b_sm2) /\
   group_id sm2_group =
     NONE /\
   group_inv sm2_group =
     weierstrass_neg
      (integer_mod_ring p_sm2,ring_neg (integer_mod_ring p_sm2) (&3),&b_sm2) /\
   group_mul sm2_group =
     weierstrass_add
      (integer_mod_ring p_sm2,ring_neg (integer_mod_ring p_sm2) (&3),&b_sm2)`,
  REWRITE_TAC[sm2_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_PSM2] THEN
  REWRITE_TAC[p_sm2; b_sm2; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_sm2; b_sm2] SM2_GROUP;;

let NO_ROOTS_SM2 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_sm2 == &0) (mod &p_sm2))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_PSM2 [p_sm2;b_sm2]);;

let GENERATOR_IN_GROUP_CARRIER_SM2 = prove
 (`g_sm2 IN group_carrier sm2_group`,
  REWRITE_TAC[g_sm2] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_SM2 = prove
 (`group_element_order sm2_group g_sm2 = n_sm2`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_SM2;
           PRIME_NSM2] THEN
  REWRITE_TAC[g_sm2; el 1 (CONJUNCTS SM2_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_sm2] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_SM2 = prove
 (`FINITE(group_carrier sm2_group)`,
  REWRITE_TAC[SM2_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_PSM2] THEN
  REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_SM2_GROUP = prove
 (`group_carrier sm2_group HAS_SIZE n_sm2`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `g_sm2:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_SM2; GROUP_ELEMENT_ORDER_SM2;
              FINITE_GROUP_CARRIER_SM2] THEN
  REWRITE_TAC[SM2_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_PSM2] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_sm2; ARITH] THEN
    REWRITE_TAC[n_sm2] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_sm2; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_SM2) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_sm2; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_SM2_GROUP = prove
 (`subgroup_generated sm2_group {g_sm2} = sm2_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_SM2;
           FINITE_GROUP_CARRIER_SM2] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_SM2;
              REWRITE_RULE[HAS_SIZE] SIZE_SM2_GROUP]);;

let CYCLIC_SM2_GROUP = prove
 (`cyclic_group sm2_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_SM2_GROUP]);;

let ABELIAN_SM2_GROUP = prove
 (`abelian_group sm2_group`,
  MESON_TAC[CYCLIC_SM2_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
