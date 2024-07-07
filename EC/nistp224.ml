(* ========================================================================= *)
(* The NIST-recommended elliptic curve P-224, aka secp224r1.                 *)
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

let p_224 = new_definition `p_224 = 26959946667150639794667015087019630673557916260026308143510066298881`;;
let n_224 = new_definition `n_224 = 26959946667150639794667015087019625940457807714424391721682722368061`;;
let SEED_224 = new_definition `SEED_224 = 0xbd71344799d5c7fcdc45b59fa3b9ab8f6a948bc5`;;
let c_224 = new_definition `c_224 = 0x5b056c7e11dd68f40469ee7f3c7a7d74f7d121116506d031218291fb`;;
let b_224 = new_definition `b_224 = 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4`;;
let G_224 = new_definition `G_224 = SOME(&0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21:int,&0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_224 = prove
 (`p_224 = 2 EXP 224 - 2 EXP 96 + 1`,
  REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P224 = time prove
 (`prime p_224`,
  REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "17"; "23"; "31"; "43"; "47"; "173"; "257";
   "347"; "373"; "641"; "727"; "16657"; "17449"; "65537"; "166571"; "274177";
   "2998279"; "6700417"; "67280421310721"]);;

let PRIME_N224 = time prove
 (`prime n_224`,
  REWRITE_TAC[n_224] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "23"; "29"; "31"; "37"; "41"; "43";
   "47"; "61"; "67"; "89"; "101"; "127"; "139"; "173"; "239"; "269"; "347";
   "349"; "509"; "631"; "659"; "1303"; "1319"; "2089"; "2153"; "2707";
   "3433"; "10909"; "20599"; "30859"; "85999"; "87739"; "145091"; "166823";
   "11105363"; "13928737"; "821796863"; "432621809776543";
   "136401162692544977256234449"; "34646440928557194402992574983797";
   "375503554633724504423937478103159147573209";
   "50520606258875818707470860153287666700917696099933389351507"]);;

(* ------------------------------------------------------------------------- *)
(* Basic sanity check on the (otherwise unused) c parameter.                 *)
(* ------------------------------------------------------------------------- *)

let SANITY_CHECK_224 = prove
 (`(&b_224 pow 2 * &c_224:int == -- &27) (mod &p_224)`,
  REWRITE_TAC[G_224; p_224; b_224; c_224] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p224_group = define
 `p224_group =
   weierstrass_group
    (integer_mod_ring p_224,
     ring_neg (integer_mod_ring p_224) (&3),
     &b_224)`;;

let P224_GROUP = prove
 (`group_carrier p224_group =
     weierstrass_curve
      (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224) /\
   group_id p224_group =
     NONE /\
   group_inv p224_group =
     weierstrass_neg
      (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224) /\
   group_mul p224_group =
     weierstrass_add
      (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224)`,
  REWRITE_TAC[p224_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P224] THEN
  REWRITE_TAC[p_224; b_224; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_224; b_224] P224_GROUP;;

let NO_ROOTS_P224 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_224 == &0) (mod &p_224))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P224 [p_224;b_224]);;

let GENERATOR_IN_GROUP_CARRIER_224 = prove
 (`G_224 IN group_carrier p224_group`,
  REWRITE_TAC[G_224] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G224 = prove
 (`group_element_order p224_group G_224 = n_224`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_224;
           PRIME_N224] THEN
  REWRITE_TAC[G_224; el 1 (CONJUNCTS P224_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_224] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_P224 = prove
 (`FINITE(group_carrier p224_group)`,
  REWRITE_TAC[P224_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P224] THEN
  REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P224_GROUP = prove
 (`group_carrier p224_group HAS_SIZE n_224`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_224:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_224; GROUP_ELEMENT_ORDER_G224;
              FINITE_GROUP_CARRIER_P224] THEN
  REWRITE_TAC[P224_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P224] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_224] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_224; ARITH] THEN
    REWRITE_TAC[n_224] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_224; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P224) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_224; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let P256_GROUP_ORDER = prove
 (`CARD(group_carrier p224_group) = n_224`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] SIZE_P224_GROUP]);;

let P224_GROUP_ELEMENT_ORDER = prove
 (`!P. P IN group_carrier p224_group
       ==> group_element_order p224_group P =
           if P = group_id p224_group then 1 else n_224`,
  MESON_TAC[SIZE_P224_GROUP; HAS_SIZE; GROUP_ELEMENT_ORDER_PRIME; PRIME_N224]);;

let GENERATED_P224_GROUP = prove
 (`subgroup_generated p224_group {G_224} = p224_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_224;
           FINITE_GROUP_CARRIER_P224] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G224;
              REWRITE_RULE[HAS_SIZE] SIZE_P224_GROUP]);;

let CYCLIC_P224_GROUP = prove
 (`cyclic_group p224_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P224_GROUP]);;

let ABELIAN_P224_GROUP = prove
 (`abelian_group p224_group`,
  MESON_TAC[CYCLIC_P224_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
