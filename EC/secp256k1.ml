(* ========================================================================= *)
(* The SECG-recommended elliptic curve secp256k1.                            *)
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

let p_256k1 = define `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;
let n_256k1 = define `n_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`;;
let G_256K1 = define `G_256K1 = SOME(&0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798:int,&0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8:int)`;;

(* ------------------------------------------------------------------------- *)
(* Also parameters beta and lambda for an endomorphism.                      *)
(* ------------------------------------------------------------------------- *)

let p256k1_beta = define `p256k1_beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee`;;
let p256k1_lambda = define `p256k1_lambda = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)

let P_256K1 = prove
 (`p_256k1 = 2 EXP 256 - 2 EXP 32 - 977`,
  REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_256K1_ALT = prove
 (`p_256k1 =
   2 EXP 256 - 2 EXP 32 - 2 EXP 9 - 2 EXP 8 - 2 EXP 7 - 2 EXP 6 - 2 EXP 4 - 1`,
  REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P256K1 = time prove
 (`prime p_256k1`,
  REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "29"; "31"; "41"; "53"; "67";
   "83"; "97"; "101"; "103"; "131"; "239"; "271"; "419"; "443"; "887"; "971";
   "1373"; "1627"; "2621"; "2657"; "4423"; "5323"; "7723"; "13441"; "20113";
   "24809"; "41201"; "96557"; "1206781"; "7240687"; "13331831"; "107590001";
   "173378833005251801"; "22149492674086928081353";
   "132896956044521568488119"; "255515944373312847190720520512484175977";
   "205115282021455665897114700593932402728804164701536103180137503955397371"]);;

let PRIME_N256K1 = time prove
 (`prime n_256k1`,
  REWRITE_TAC[n_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "37"; "41"; "59";
   "67"; "73"; "97"; "109"; "113"; "149"; "199"; "293"; "461"; "631"; "797";
   "1409"; "1871"; "2011"; "2731"; "2861"; "4051"; "9349"; "16699"; "28181";
   "85831"; "120233"; "305873"; "1627771"; "4681609"; "44706919";
   "545358713"; "297159362677"; "107361793816595537";
   "174723607534414371449"; "29047611873442575647497758179";
   "341948486974166000522343609283189"]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p256k1_group = define
 `p256k1_group = weierstrass_group(integer_mod_ring p_256k1,&0,&7)`;;

let P256K1_GROUP = prove
 (`group_carrier p256k1_group =
     weierstrass_curve(integer_mod_ring p_256k1,&0,&7) /\
   group_id p256k1_group =
     NONE /\
   group_inv p256k1_group =
     weierstrass_neg(integer_mod_ring p_256k1,&0,&7) /\
   group_mul p256k1_group =
     weierstrass_add(integer_mod_ring p_256k1,&0,&7)`,
  REWRITE_TAC[p256k1_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P256K1] THEN
  REWRITE_TAC[p_256k1; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_256k1] P256K1_GROUP;;

let NO_ROOTS_256K1 = prove
 (`!x:int. ~((x pow 3 + &7 == &0) (mod &p_256k1))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P256K1 [p_256k1]);;

let GENERATOR_IN_GROUP_CARRIER_256K1 = prove
 (`G_256K1 IN group_carrier p256k1_group`,
  REWRITE_TAC[G_256K1] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G256K1 = prove
 (`group_element_order p256k1_group G_256K1 = n_256k1`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_256K1; PRIME_N256K1] THEN
  REWRITE_TAC[G_256K1; el 1 (CONJUNCTS P256K1_GROUP);
              option_DISTINCT] THEN
  REWRITE_TAC[n_256k1] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_256K1 = prove
 (`FINITE(group_carrier p256k1_group)`,
  REWRITE_TAC[P256K1_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING;
              FIELD_INTEGER_MOD_RING; PRIME_P256K1] THEN
  REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P256K1_GROUP = prove
 (`group_carrier p256k1_group HAS_SIZE n_256k1`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_256K1:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_256K1;
              GROUP_ELEMENT_ORDER_G256K1;
              FINITE_GROUP_CARRIER_256K1] THEN
  REWRITE_TAC[P256K1_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P256K1] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_256k1; ARITH] THEN
    REWRITE_TAC[n_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_256k1; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_256K1) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_256k1; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P256K1_GROUP = prove
 (`subgroup_generated p256k1_group {G_256K1} = p256k1_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_256K1;
           FINITE_GROUP_CARRIER_256K1] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G256K1;
              REWRITE_RULE[HAS_SIZE] SIZE_P256K1_GROUP]);;

let CYCLIC_P256K1_GROUP = prove
 (`cyclic_group p256k1_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P256K1_GROUP]);;

let ABELIAN_P256K1_GROUP = prove
 (`abelian_group p256k1_group`,
  MESON_TAC[CYCLIC_P256K1_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* Easily computable endomorphism of secp256k1 curve.                        *)
(* ------------------------------------------------------------------------- *)

let GROUP_ENDOMORPHISM_TRIPLEX_BETA = prove
 (`group_endomorphism p256k1_group
        (weierstrass_triplex (integer_mod_ring p_256k1) (&p256k1_beta))`,
  REWRITE_TAC[p256k1_group] THEN MATCH_MP_TAC GROUP_ENDOMORPHISM_TRIPLEX THEN
  SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; INTEGER_MOD_RING_POW;
           p_256k1; IN_INSERT; FIELD_INTEGER_MOD_RING; ARITH; p256k1_beta;
           IN_ELIM_THM; weierstrass_nonsingular; INTEGER_MOD_RING_OF_NUM] THEN
  REWRITE_TAC[REWRITE_RULE[p_256k1] PRIME_P256K1] THEN
  CONV_TAC INT_REDUCE_CONV);;

let P256K1_TRIPLEX_BETA = prove
 (`!x. x IN group_carrier p256k1_group
       ==> weierstrass_triplex (integer_mod_ring p_256k1) (&p256k1_beta) x =
           group_pow p256k1_group x p256k1_lambda`,
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM GENERATED_P256K1_GROUP] THEN
  MATCH_MP_TAC  GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS THEN
  EXISTS_TAC `p256k1_group` THEN
  SIMP_TAC[ABELIAN_GROUP_HOMOMORPHISM_POWERING; ABELIAN_P256K1_GROUP] THEN
  REWRITE_TAC[GSYM group_endomorphism] THEN
  REWRITE_TAC[GROUP_ENDOMORPHISM_TRIPLEX_BETA; ETA_AX] THEN
  REWRITE_TAC[IMP_CONJ_ALT; IN_SING; FORALL_UNWIND_THM2] THEN
  DISCH_TAC THEN
  SIMP_TAC[weierstrass_triplex; p256k1_beta; p256k1_lambda; G_256K1] THEN
  CONV_TAC(RAND_CONV ECGROUP_POW_CONV) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING; p_256k1] THEN CONV_TAC INT_REDUCE_CONV);;
