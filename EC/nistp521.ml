(* ========================================================================= *)
(* The NIST-recommended elliptic curve P-521, aka secp521r1.                 *)
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

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;
let n_521 = new_definition `n_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449`;;
let SEED_521 = new_definition `SEED_521 = 0xd09e8800291cb85396cc6717393284aaa0da64ba`;;
let c_521 = new_definition `c_521 = 0x0b48bfa5f420a34949539d2bdfc264eeeeb077688e44fbf0ad8f6d0edb37bd6b533281000518e19f1b9ffbe0fe9ed8a3c2200b8f875e523868c70c1e5bf55bad637`;;
let b_521 = new_definition `b_521 = 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00`;;
let G_521 = new_definition `G_521 = SOME(&0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66:int,&0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P521 = time prove
 (`prime p_521`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "43"; "53"; "59"; "61"; "79"; "89"; "103"; "109"; "113"; "131"; "151";
   "157"; "173"; "179"; "223"; "227"; "257"; "277"; "317"; "347"; "397";
   "521"; "683"; "1051"; "1237"; "1381"; "1433"; "1613"; "1663"; "2437";
   "2731"; "3191"; "8191"; "23609"; "28793"; "42641"; "49481"; "51481";
   "61681"; "409891"; "858001"; "2995763"; "5746001"; "7623851"; "8620289";
   "9211861"; "34110701"; "308761441"; "2400573761"; "2534364967";
   "24098228377"; "65427463921"; "674750394557"; "108140989558681";
   "145295143558111"; "361725589517273017"; "173308343918874810521923841"]);;

let PRIME_N521 = time prove
 (`prime n_521`,
  REWRITE_TAC[n_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "47"; "53"; "59"; "61"; "71"; "73"; "79"; "97"; "109"; "113"; "127";
   "131"; "157"; "181"; "191"; "193"; "227"; "229"; "233"; "241"; "257";
   "263"; "277"; "281"; "311"; "421"; "547"; "593"; "641"; "659"; "811";
   "877"; "1187"; "1283"; "1543"; "5449"; "6043"; "9227"; "10861"; "14461";
   "15601"; "17293"; "17467"; "20341"; "65677"; "92581"; "133279"; "161969";
   "370471"; "495527"; "777241"; "6937379"; "8196883"; "10577321";
   "10924559"; "19353437"; "186406729"; "1458105463"; "101785224689";
   "43800962361397"; "60018716061994831"; "88599952463812275001";
   "3473195323567808068309"; "4239602065187190872179";
   "1647781915921980690468599"; "144471089338257942164514676806340723";
   "7427946019382605513260578233234962521";
   "15994076126984618329123851002118749004583184815459808099";
   "3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511";
   "3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943"]);;

(* ------------------------------------------------------------------------- *)
(* Basic sanity check on the (otherwise unused) c parameter.                 *)
(* ------------------------------------------------------------------------- *)

let SANITY_CHECK_521 = prove
 (`(&b_521 pow 2 * &c_521:int == -- &27) (mod &p_521)`,
  REWRITE_TAC[G_521; p_521; b_521; c_521] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p521_group = define
 `p521_group =
   weierstrass_group
    (integer_mod_ring p_521,
     ring_neg (integer_mod_ring p_521) (&3),
     &b_521)`;;

let P521_GROUP = prove
 (`group_carrier p521_group =
     weierstrass_curve
      (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521) /\
   group_id p521_group =
     NONE /\
   group_inv p521_group =
     weierstrass_neg
      (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521) /\
   group_mul p521_group =
     weierstrass_add
      (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521)`,
  REWRITE_TAC[p521_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P521] THEN
  REWRITE_TAC[p_521; b_521; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_521; b_521] P521_GROUP;;

let NO_ROOTS_P521 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_521 == &0) (mod &p_521))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P521 [p_521;b_521]);;

let GENERATOR_IN_GROUP_CARRIER_521 = prove
 (`G_521 IN group_carrier p521_group`,
  REWRITE_TAC[G_521] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G521 = prove
 (`group_element_order p521_group G_521 = n_521`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_521;
           PRIME_N521] THEN
  REWRITE_TAC[G_521; el 1 (CONJUNCTS P521_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_521] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_521 = prove
 (`FINITE(group_carrier p521_group)`,
  REWRITE_TAC[P521_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P521_GROUP = prove
 (`group_carrier p521_group HAS_SIZE n_521`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_521:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_521; GROUP_ELEMENT_ORDER_G521;
              FINITE_GROUP_CARRIER_521] THEN
  REWRITE_TAC[P521_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P521] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_521; ARITH] THEN
    REWRITE_TAC[n_521] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_521; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P521) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_521; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P521_GROUP = prove
 (`subgroup_generated p521_group {G_521} = p521_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_521;
           FINITE_GROUP_CARRIER_521] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G521;
              REWRITE_RULE[HAS_SIZE] SIZE_P521_GROUP]);;

let CYCLIC_P521_GROUP = prove
 (`cyclic_group p521_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P521_GROUP]);;

let ABELIAN_P521_GROUP = prove
 (`abelian_group p521_group`,
  MESON_TAC[CYCLIC_P521_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
