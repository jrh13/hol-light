(* ========================================================================= *)
(* The SECG-recommended elliptic curve secp224k1.                            *)
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

let p_224k1 = define `p_224k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFE56D`;;
let n_224k1 = define `n_224k1 = 0x010000000000000000000000000001DCE8D2EC6184CAF0A971769FB1F7`;;
let G_224K1 = define `G_224K1 = SOME(&0xA1455B334DF099DF30FC28A169A467E9E47075A90F7E650EB6B7A45C:int,&0x7E089FED7FBA344282CAFBD6F7E319F7C0B0BD59E2CA4BDB556D61A5:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_224K1 = prove
 (`p_224k1 = 2 EXP 224 - 2 EXP 32 - 6803`,
  REWRITE_TAC[p_224k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_224K1_ALT = prove
 (`p_224k1 =
   2 EXP 224 - 2 EXP 32 - 2 EXP 12 -
   2 EXP 11 - 2 EXP 9 - 2 EXP 7 - 2 EXP 4 - 2 - 1`,
  REWRITE_TAC[p_224k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P224K1 = time prove
 (`prime p_224k1`,
  REWRITE_TAC[p_224k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "19"; "23"; "29"; "37"; "41"; "47"; "59";
   "79"; "83"; "89"; "101"; "113"; "131"; "163"; "167"; "227"; "419"; "821";
   "1163"; "1471"; "1601"; "1777"; "3001"; "3137"; "10663"; "10903"; "14983";
   "17293"; "21347"; "43613"; "48847"; "82837"; "7599533"; "42252061";
   "17042913689"; "34085827379"; "156976040219402488243";
   "31670999344427766303479"; "30974237358850355444802463";
   "9743875111334057846550285755748171501325144788037"]);;

let PRIME_N224K1 = time prove
 (`prime n_224k1`,
  REWRITE_TAC[n_224k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "31"; "41"; "61"; "73";
   "151"; "163"; "191"; "193"; "239"; "311"; "353"; "367"; "479"; "1013";
   "1511"; "2027"; "3023"; "3067"; "9199"; "9923"; "17573"; "34231"; "59539";
   "120047"; "252913"; "478453"; "2218883"; "2396171"; "4167731"; "4437767";
   "10083949"; "12019933"; "21244693"; "33341849"; "6058046233";
   "24281921209346341"; "58597812472881879287";
   "2514514399252200308862687893991356095647329471";
   "4493324444525106632444502514503273391085054513853345758165826444713"]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p224k1_group = define
 `p224k1_group = weierstrass_group(integer_mod_ring p_224k1,&0,&5)`;;

let P224K1_GROUP = prove
 (`group_carrier p224k1_group =
     weierstrass_curve(integer_mod_ring p_224k1,&0,&5) /\
   group_id p224k1_group =
     NONE /\
   group_inv p224k1_group =
     weierstrass_neg(integer_mod_ring p_224k1,&0,&5) /\
   group_mul p224k1_group =
     weierstrass_add(integer_mod_ring p_224k1,&0,&5)`,
  REWRITE_TAC[p224k1_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P224K1] THEN
  REWRITE_TAC[p_224k1; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_224k1] P224K1_GROUP;;

let NO_ROOTS_224K1 = prove
 (`!x:int. ~((x pow 3 + &5 == &0) (mod &p_224k1))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P224K1 [p_224k1]);;

let GENERATOR_IN_GROUP_CARRIER_224K1 = prove
 (`G_224K1 IN group_carrier p224k1_group`,
  REWRITE_TAC[G_224K1] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G224K1 = prove
 (`group_element_order p224k1_group G_224K1 = n_224k1`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_224K1; PRIME_N224K1] THEN
  REWRITE_TAC[G_224K1; el 1 (CONJUNCTS P224K1_GROUP);
              option_DISTINCT] THEN
  REWRITE_TAC[n_224k1] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_P224K1 = prove
 (`FINITE(group_carrier p224k1_group)`,
  REWRITE_TAC[P224K1_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING;
              FIELD_INTEGER_MOD_RING; PRIME_P224K1] THEN
  REWRITE_TAC[p_224k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P224K1_GROUP = prove
 (`group_carrier p224k1_group HAS_SIZE n_224k1`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_224K1:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_224K1;
              GROUP_ELEMENT_ORDER_G224K1;
              FINITE_GROUP_CARRIER_P224K1] THEN
  REWRITE_TAC[P224K1_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P224K1] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_224k1] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_224k1; ARITH] THEN
    REWRITE_TAC[n_224k1] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_224k1; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_224K1) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_224k1; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let P224K1_GROUP_ORDER = prove
 (`CARD(group_carrier p224k1_group) = n_224k1`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] SIZE_P224K1_GROUP]);;

let P224K1_GROUP_ELEMENT_ORDER = prove
 (`!P. P IN group_carrier p224k1_group
       ==> group_element_order p224k1_group P =
           if P = group_id p224k1_group then 1 else n_224k1`,
  MESON_TAC[SIZE_P224K1_GROUP; HAS_SIZE; GROUP_ELEMENT_ORDER_PRIME;
            PRIME_N224K1]);;

let GENERATED_P224K1_GROUP = prove
 (`subgroup_generated p224k1_group {G_224K1} = p224k1_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_224K1;
           FINITE_GROUP_CARRIER_P224K1] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G224K1;
              REWRITE_RULE[HAS_SIZE] SIZE_P224K1_GROUP]);;

let CYCLIC_P224K1_GROUP = prove
 (`cyclic_group p224k1_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P224K1_GROUP]);;

let ABELIAN_P224K1_GROUP = prove
 (`abelian_group p224k1_group`,
  MESON_TAC[CYCLIC_P224K1_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
