(* ========================================================================= *)
(* wei25519, a Weierstrass-coordinate version of curve25519, described in    *)
(* https://datatracker.ietf.org/doc/draft-ietf-lwig-curve-representations/   *)
(* ========================================================================= *)

needs "EC/weierstrass.ml";;
needs "EC/excluderoots.ml";;
needs "EC/computegroup.ml";;

add_curve weierstrass_curve;;
add_curveneg weierstrass_neg;;
add_curveadd weierstrass_add;;

(* ------------------------------------------------------------------------- *)
(* Parameters for the wei25519 curve, taken from the document                *)
(* https://datatracker.ietf.org/doc/draft-ietf-lwig-curve-representations/   *)
(* Here  n_25519 is the large prime factor of the group order, the full      *)
(* group order being 8 * n_25519. Likewise G_25519 is the generator of the   *)
(* prime order subgroup and GG_25519 is a generator for the full group.      *)
(* ------------------------------------------------------------------------- *)

let p_25519 = define`p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;
let n_25519 = define`n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;
let a_25519 = define`a_25519 = 19298681539552699237261830834781317975544997444273427339909597334573241639236`;;
let b_25519 = define`b_25519 = 55751746669818908907645289078257140818241103727901012315294400837956729358436`;;
let G_25519 = define `G_25519 = SOME(&0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaad245a:int,&0x20ae19a1b8a086b4e01edd2c7748d14c923d4d7e6d7c61b229e9c5a27eced3d9:int)`;;
let GG_25519 = define `GG_25519 = SOME(&26209954324546670665403455918906049867068731898706945806410342575476729061509:int,&35197529511187359173101698576797651179158701633820552795916138355302448607023:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and (sub)group order.               *)
(* ------------------------------------------------------------------------- *)

let P_25519 = prove
 (`p_25519 = 2 EXP 255 - 19`,
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let N_25519 = prove
 (`n_25519 = 2 EXP 252 + 27742317777372353535851937790883648493`,
  REWRITE_TAC[n_25519] THEN ARITH_TAC);;

let PRIME_P25519 = prove
 (`prime p_25519`,
  REWRITE_TAC[p_25519] THEN (CONV_TAC o PRIME_RULE)
   ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
    "43"; "47"; "53"; "59"; "83"; "97"; "103"; "107"; "127"; "131"; "173";
    "223"; "239"; "353"; "419"; "479"; "487"; "991"; "1723"; "2437"; "3727";
    "4153"; "9463"; "32573"; "37853"; "57467"; "65147"; "75707"; "132049";
    "430751"; "569003"; "1923133"; "8574133"; "2773320623"; "72106336199";
    "1919519569386763"; "31757755568855353";
    "75445702479781427272750846543864801";
    "74058212732561358302231226437062788676166966415465897661863160754340907"]);;

let PRIME_N25519 = prove
 (`prime n_25519`,
  REWRITE_TAC[n_25519] THEN (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "41"; "43"; "47"; "67";
   "73"; "79"; "113"; "269"; "307"; "1361"; "1723"; "2551"; "2851"; "2939";
   "3797"; "5879"; "17231"; "22111"; "30703"; "34123"; "41081"; "82163";
   "132667"; "137849"; "409477"; "531581"; "1224481"; "14741173"; "58964693";
   "292386187"; "213441916511"; "1257559732178653"; "4434155615661930479";
   "3044861653679985063343"; "172054593956031949258510691";
   "198211423230930754013084525763697";
   "19757330305831588566944191468367130476339";
   "276602624281642239937218680557139826668747";
   "7237005577332262213973186563042994240857116359379907606001950938285454250989"]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let wei25519_group = define
 `wei25519_group =
    weierstrass_group(integer_mod_ring p_25519,&a_25519,&b_25519)`;;

let WEI25519_GROUP = prove
 (`group_carrier wei25519_group =
     weierstrass_curve(integer_mod_ring p_25519,&a_25519,&b_25519) /\
   group_id wei25519_group =
     NONE /\
   group_inv wei25519_group =
     weierstrass_neg(integer_mod_ring p_25519,&a_25519,&b_25519) /\
   group_mul wei25519_group =
     weierstrass_add(integer_mod_ring p_25519,&a_25519,&b_25519)`,
  REWRITE_TAC[wei25519_group] THEN
  MATCH_MP_TAC WEIERSTRASS_GROUP THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; INTEGER_MOD_RING_CHAR; PRIME_P25519] THEN
  REWRITE_TAC[a_25519; b_25519; p_25519; weierstrass_nonsingular] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [a_25519; b_25519; p_25519] WEI25519_GROUP;;

let FINITE_GROUP_CARRIER_WEI25519 = prove
 (`FINITE(group_carrier wei25519_group)`,
  REWRITE_TAC[WEI25519_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING;
              FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let GENERATOR_IN_GROUP_CARRIER_WEI25519 = prove
 (`G_25519 IN group_carrier wei25519_group`,
  REWRITE_TAC[G_25519] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_WEI25519_G25519 = prove
 (`group_element_order wei25519_group G_25519 = n_25519`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_WEI25519; PRIME_N25519] THEN
  REWRITE_TAC[G_25519; el 1 (CONJUNCTS WEI25519_GROUP);
              option_DISTINCT] THEN
  REWRITE_TAC[n_25519] THEN CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN
  REFL_TAC);;

let FULLGENERATOR_IN_GROUP_CARRIER_WEI25519 = prove
 (`GG_25519 IN group_carrier wei25519_group`,
  REWRITE_TAC[GG_25519] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_WEI25519_GG25519 = prove
 (`group_element_order wei25519_group GG_25519 = 8 * n_25519`,
  ABBREV_TAC
   `h = SOME
     (&784994156384216107199399111990385161439916830893843497063691184659069321411,
      &10506421237558716435988711236408671798265365380393424752549290025458740468278)
    :(int#int)option` THEN
  SUBGOAL_THEN
   `h IN group_carrier wei25519_group /\
    group_element_order wei25519_group h = 8`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [CONV_TAC ECGROUP_CARRIER_CONV;
      SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_ALT; ARITH]] THEN
    DISCH_TAC THEN REWRITE_TAC[WEI25519_GROUP] THEN CONJ_TAC THENL
     [CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(RAND_CONV(LAND_CONV ECGROUP_POW_CONV)) THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `GG_25519 = group_mul wei25519_group h G_25519` SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[G_25519; GG_25519] THEN
    CONV_TAC(RAND_CONV ECGROUP_MUL_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_ELEMENT_ORDER_MUL_EQ o
    lhand o snd) THEN
  ASM_REWRITE_TAC[GROUP_ELEMENT_ORDER_WEI25519_G25519] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_WEI25519] THEN CONJ_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[G_25519] THEN
    CONV_TAC(BINOP_CONV ECGROUP_MUL_CONV) THEN REFL_TAC;
    REWRITE_TAC[n_25519] THEN CONV_TAC COPRIME_CONV]);;

let SIZE_WEI25519_GROUP = prove
 (`group_carrier wei25519_group HAS_SIZE (8 * n_25519)`,
  REWRITE_TAC[HAS_SIZE; FINITE_GROUP_CARRIER_WEI25519] THEN
  MP_TAC(ISPECL [`wei25519_group`; `GG_25519`]
    GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
  REWRITE_TAC[FINITE_GROUP_CARRIER_WEI25519;
              FULLGENERATOR_IN_GROUP_CARRIER_WEI25519] THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM;
               GROUP_ELEMENT_ORDER_WEI25519_GG25519] THEN
  X_GEN_TAC `d:num` THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (ARITH_RULE `d = 0 \/ d = 1 \/ 2 <= d`) THEN
  ASM_SIMP_TAC[CARD_EQ_0; FINITE_GROUP_CARRIER_WEI25519;
               MULT_CLAUSES; GROUP_CARRIER_NONEMPTY] THEN
  MATCH_MP_TAC(ARITH_RULE
   `s < 16 * n /\ 2 * n <= d * n ==> s = (8 * n) * d ==> x = 8 * n`) THEN
  REWRITE_TAC[LE_MULT_RCANCEL; n_25519; ARITH_EQ] THEN
  ASM_REWRITE_TAC[GSYM n_25519; WEI25519_GROUP] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_BOUND_WEIERSTRASS_CURVE o
    lhand o snd) THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  SIMP_TAC[FINITE_INTEGER_MOD_RING; CARD_INTEGER_MOD_RING;
           n_25519; p_25519; ARITH_EQ] THEN
  ARITH_TAC);;

let GENERATED_WEI25519_GROUP = prove
 (`subgroup_generated wei25519_group {GG_25519} = wei25519_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           FULLGENERATOR_IN_GROUP_CARRIER_WEI25519;
           FINITE_GROUP_CARRIER_WEI25519] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_WEI25519_GG25519;
              REWRITE_RULE[HAS_SIZE] SIZE_WEI25519_GROUP]);;

let CYCLIC_WEI25519_GROUP = prove
 (`cyclic_group wei25519_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_WEI25519_GROUP]);;

let ABELIAN_WEI25519_GROUP = prove
 (`abelian_group wei25519_group`,
  MESON_TAC[CYCLIC_WEI25519_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
