(* ========================================================================= *)
(* The NIST-recommended elliptic curve P-384, aka secp384r1.                 *)
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

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;
let n_384 = new_definition `n_384 = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643`;;
let SEED_384 = new_definition `SEED_384 = 0xa335926aa319a27a1d00896a6773a4827acdac73`;;
let c_384 = new_definition `c_384 = 0x79d1e655f868f02fff48dcdee14151ddb80643c1406d0ca10dfe6fc52009540a495e8042ea5f744f6e184667cc722483`;;
let b_384 = new_definition `b_384 = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef`;;
let G_384 = new_definition `G_384 = SOME(&0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7:int,&0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f:int)`;;

let nistp384 = define
 `nistp384 =
    (integer_mod_ring p_384,
     ring_neg (integer_mod_ring p_384) (&3),
     &b_384:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and group order.                    *)
(* ------------------------------------------------------------------------- *)


let P_384 = prove
 (`p_384 = 2 EXP 384 - 2 EXP 128 - 2 EXP 96 + 2 EXP 32 - 1`,
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P384 = time prove
 (`prime p_384`,
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "41"; "43"; "47";
   "59"; "61"; "67"; "73"; "79"; "97"; "131"; "139"; "157"; "181"; "211";
   "233"; "263"; "271"; "293"; "599"; "661"; "881"; "937"; "1033"; "1373";
   "1579"; "2213"; "3253"; "3517"; "6317"; "8389"; "21407"; "38557";
   "312289"; "336757"; "363557"; "568151"; "6051631"; "105957871";
   "246608641"; "513928823"; "532247449"; "2862218959"; "53448597593";
   "807145746439"; "44925942675193"; "1357291859799823621";
   "529709925838459440593"; "35581458644053887931343";
   "23964610537191310276190549303"; "862725979338887169942859774909";
   "20705423504133292078628634597817";
   "413244619895455989650825325680172591660047";
   "12397338596863679689524759770405177749801411";
   "19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097"]);;

let PRIME_N384 = time prove
 (`prime n_384`,
  REWRITE_TAC[n_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "43"; "47"; "53"; "59"; "73"; "79"; "89"; "97"; "107"; "113"; "149";
   "151"; "163"; "173"; "179"; "181"; "233"; "251"; "311"; "347"; "421";
   "491"; "653"; "659"; "881"; "1087"; "1117"; "1553"; "3739"; "4349";
   "8699"; "16979"; "34429"; "37447"; "64901"; "248431"; "330563"; "455737";
   "1276987"; "8463023"; "9863677"; "154950581"; "272109983"; "290064143";
   "228572385721"; "1436833069313"; "23314383343543"; "37344768852931";
   "55942463741690639"; "426632512014427833817"; "120699720968197491947347";
   "1124679999981664229965379347"; "1495199339761412565498084319";
   "17942392077136950785977011829";
   "1059392654943455286185473617842338478315215895509773412096307";
   "3055465788140352002733946906144561090641249606160407884365391979704929268480326390471"]);;

(* ------------------------------------------------------------------------- *)
(* Basic sanity check on the (otherwise unused) c parameter.                 *)
(* ------------------------------------------------------------------------- *)

let SANITY_CHECK_384 = prove
 (`(&b_384 pow 2 * &c_384:int == -- &27) (mod &p_384)`,
  REWRITE_TAC[G_384; p_384; b_384; c_384] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let p384_group = define
 `p384_group =
   weierstrass_group
    (integer_mod_ring p_384,
     ring_neg (integer_mod_ring p_384) (&3),
     &b_384)`;;

let P384_GROUP = prove
 (`group_carrier p384_group =
     weierstrass_curve
      (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384) /\
   group_id p384_group =
     NONE /\
   group_inv p384_group =
     weierstrass_neg
      (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384) /\
   group_mul p384_group =
     weierstrass_add
      (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384)`,
  REWRITE_TAC[p384_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P384] THEN
  REWRITE_TAC[p_384; b_384; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [p_384; b_384] P384_GROUP;;

let NO_ROOTS_P384 = prove
 (`!x:int. ~((x pow 3 - &3 * x + &b_384 == &0) (mod &p_384))`,
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P384 [p_384;b_384]);;

let GENERATOR_IN_GROUP_CARRIER_384 = prove
 (`G_384 IN group_carrier p384_group`,
  REWRITE_TAC[G_384] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_G384 = prove
 (`group_element_order p384_group G_384 = n_384`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME; GENERATOR_IN_GROUP_CARRIER_384;
           PRIME_N384] THEN
  REWRITE_TAC[G_384; el 1 (CONJUNCTS P384_GROUP); option_DISTINCT] THEN
  REWRITE_TAC[n_384] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FINITE_GROUP_CARRIER_384 = prove
 (`FINITE(group_carrier p384_group)`,
  REWRITE_TAC[P384_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING; PRIME_P384] THEN
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZE_P384_GROUP = prove
 (`group_carrier p384_group HAS_SIZE n_384`,
  MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
  EXISTS_TAC `G_384:(int#int)option` THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_384; GROUP_ELEMENT_ORDER_G384;
              FINITE_GROUP_CARRIER_384] THEN
  REWRITE_TAC[P384_GROUP] THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_BOUND_WEIERSTRASS_CURVE o lhand o snd) THEN
    REWRITE_TAC[FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING] THEN
    REWRITE_TAC[PRIME_P384] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)] THEN
    SIMP_TAC[CARD_INTEGER_MOD_RING; p_384; ARITH] THEN
    REWRITE_TAC[n_384] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[FORALL_OPTION_THM; IN; FORALL_PAIR_THM] THEN
    REWRITE_TAC[weierstrass_curve; weierstrass_neg; option_DISTINCT] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_384; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC(SPEC `x:int` NO_ROOTS_P384) THEN
    REWRITE_TAC[INT_ARITH `y - &3 * x + b:int = y + (-- &3) * x + b`] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; p_384; INT_REM_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)`)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[INT_REM_LT]; ALL_TAC] THEN
    REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
     `(--y:int == y) (mod p) <=> p divides (&2 * y)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `p divides (a * b:int) ==> coprime(a,p) ==> p divides b`)) THEN
    REWRITE_TAC[GSYM num_coprime; ARITH; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]);;

let GENERATED_P384_GROUP = prove
 (`subgroup_generated p384_group {G_384} = p384_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           GENERATOR_IN_GROUP_CARRIER_384;
           FINITE_GROUP_CARRIER_384] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_G384;
              REWRITE_RULE[HAS_SIZE] SIZE_P384_GROUP]);;

let CYCLIC_P384_GROUP = prove
 (`cyclic_group p384_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_P384_GROUP]);;

let ABELIAN_P384_GROUP = prove
 (`abelian_group p384_group`,
  MESON_TAC[CYCLIC_P384_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
