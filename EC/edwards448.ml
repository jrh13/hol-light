(* ========================================================================= *)
(* The Edwards curve commonly known as Goldilocks, edwards448.               *)
(* ========================================================================= *)

needs "EC/edwards.ml";;
needs "EC/excluderoots.ml";;
needs "EC/computegroup.ml";;

add_curve edwards_curve;;
add_curvezero edwards_0;;
add_curveneg edwards_neg;;
add_curveadd edwards_add;;

(* ------------------------------------------------------------------------- *)
(* Parameters for the edwards448 curve, based on the original Mike Hamburg   *)
(* paper "Ed448-Goldilocks" (https://eprint.iacr.org/2015/625.pdf).          *)
(* Here  n_448 is the large prime factor of the group order, the full        *)
(* group order being 4 * n_448. Likewise E_448 is the generator of the       *)
(* prime order subgroup and EE_448 is a generator for the full group.        *)
(* We use e_448 instead of a_448 as the name, to reserve the latter for any  *)
(* Weierstrass variants we might also add.                                   *)
(* ------------------------------------------------------------------------- *)

let p_448 = define `p_448 = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439`;;
let n_448 = define `n_448 = 181709681073901722637330951972001133588410340171829515070372549795146003961539585716195755291692375963310293709091662304773755859649779`;;
let e_448 = define`e_448 = 1`;;
let d_448 = define`d_448 = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018326358`;;
let E_448 = define `E_448 = (&0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa955555555555555555555555555555555555555555555555555555555:int, &0xae05e9634ad7048db359d6205086c2b0036ed7a035884dd7b7e36d728ad8c4b80d6565833a2a3098bbbcb2bed1cda06bdaeafbcdea9386ed:int)`;;
let EE_448 = define `EE_448 = (&494088759867433727674302672526735089350544552303727723746126484473087719117037293890093462157703888342865036477787453078312060500281069:int,&242279574765202296849774602629334844784547120229106020093830066393555416020021691321995239242950195063812052916896239502005235079621290:int)`;;

(* ------------------------------------------------------------------------- *)
(* Some other equally usable basepoints.                                     *)
(*                                                                           *)
(*  - E_448 above is in the (revised version of) the original paper          *)
(*    https://eprint.iacr.org/2015/625.pdf                                   *)
(*                                                                           *)
(*  - F_448 is the one standardized here:                                    *)
(*    https://www.rfc-editor.org/rfc/rfc7748                                 *)
(*    https://datatracker.ietf.org/doc/html/                                 *)
(*       draft-ietf-lwig-curve-representations-23                            *)
(*                                                                           *)
(*  - H_448 is the one given in Hamburg's own                                *)
(*    http://ed448goldilocks.sourceforge.net/spec/                           *)
(* ------------------------------------------------------------------------- *)

let F_448 = define `F_448 = (&0x4f1970c66bed0ded221d15a622bf36da9e146570470f1767ea6de324a3d3a46412ae1af72ab66511433b80e18b00938e2626a82bc70cc05e:int,&0x693f46716eb6bc248876203756c9c7624bea73736ca3984087789c1e05a0c2d73ad3ff1ce67c39c4fdbd132c4ed7c8ad9808795bf230fa14:int)`;;

let H_448 = define `H_448 = (&117812161263436946737282484343310064665180535357016373416879082147939404277809514858788439644911793978499419995990477371552926308078495:int,&19:int)`;;

(* ------------------------------------------------------------------------- *)
(* Primality of the field characteristic and (sub)group order.               *)
(* ------------------------------------------------------------------------- *)

let P_448 = prove
 (`p_448 = 2 EXP 448 - 2 EXP 224 - 1`,
  REWRITE_TAC[p_448] THEN ARITH_TAC);;

let N_448 = prove
 (`n_448 = 2 EXP 446 - 0x8335dc163bb124b65129c96fde933d8d723a70aadc873d6d54a7bb0d`,
  REWRITE_TAC[n_448] THEN ARITH_TAC);;

let PRIME_P448 = prove
 (`prime p_448`,
  REWRITE_TAC[p_448] THEN (CONV_TAC o PRIME_RULE)
 ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "43"; "59"; "61"; "67"; "109"; "137"; "149"; "151"; "197"; "223"; "229";
   "271"; "443"; "463"; "593"; "613"; "641"; "727"; "1481"; "1549"; "1979";
   "2437"; "2531"; "2683"; "2963"; "6197"; "9749"; "17449"; "18287"; "47497";
   "116989"; "189989"; "196687"; "217003"; "379979"; "411743"; "1466449";
   "1609403"; "2916841"; "6700417"; "36753053"; "1255525949"; "1335912079";
   "1764234391"; "3402277943"; "32061889897"; "25136521679249";
   "97859369123353"; "34741861125639557"; "36131535570665139281";
   "1469495262398780123809"; "167773885276849215533569";
   "596242599987116128415063"; "37414057161322375957408148834323969"]);;

let PRIME_N448 = prove
 (`prime n_448`,
  REWRITE_TAC[n_448] THEN (CONV_TAC o PRIME_RULE)
 ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "31"; "41"; "43"; "53";
   "61"; "67"; "71"; "79"; "83"; "89"; "97"; "101"; "113"; "137"; "167";
   "173"; "179"; "193"; "197"; "311"; "337"; "347"; "373"; "431"; "691";
   "821"; "991"; "1609"; "1933"; "2239"; "3217"; "3449"; "4051"; "6577";
   "14221"; "16657"; "34483"; "41389"; "51473"; "64817"; "74551"; "142211";
   "227393"; "766223"; "816763"; "894613"; "3009341"; "3578453"; "4847597";
   "7156907"; "9801157"; "15643211"; "35796097"; "47840521"; "671065561";
   "765448337"; "8464734851"; "342682509629"; "95024118539459";
   "760192948315673"; "2746144996771313789";
   "163131120638915058577002756917"; "929098197455246849020086750707";
   "6730519843040614479184435237013"; "3591893631361984318311655378233263";
   "392279121964710096549298451519713063";
   "547972593843380542316719287015009101629889568888367769396279985548530313239"]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group and proof of its key properties.            *)
(* ------------------------------------------------------------------------- *)

let edwards448_group = define
 `edwards448_group =
    edwards_group(integer_mod_ring p_448,&e_448,&d_448)`;;

let EDWARDS_NONSINGULAR_448 = prove
 (`edwards_nonsingular (integer_mod_ring p_448,&e_448,&d_448)`,
  REWRITE_TAC[edwards_nonsingular; INTEGER_MOD_RING_ROOT_EXISTS] THEN
  SIMP_TAC[INTEGER_MOD_RING; INT_OF_NUM_EQ; e_448; d_448; p_448] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[EULER_CRITERION; REWRITE_RULE[p_448] PRIME_P448] THEN
  CONV_TAC(DEPTH_CONV
   (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let EDWARDS448_GROUP = prove
 (`group_carrier edwards448_group =
     edwards_curve(integer_mod_ring p_448,&e_448,&d_448) /\
   group_id edwards448_group =
     edwards_0(integer_mod_ring p_448,&e_448,&d_448) /\
   group_inv edwards448_group =
     edwards_neg(integer_mod_ring p_448,&e_448,&d_448) /\
   group_mul edwards448_group =
     edwards_add(integer_mod_ring p_448,&e_448,&d_448)`,
  REWRITE_TAC[edwards448_group] THEN MATCH_MP_TAC EDWARDS_GROUP THEN
  REWRITE_TAC[EDWARDS_NONSINGULAR_448] THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P448] THEN
  REWRITE_TAC[e_448; d_448; p_448] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV);;

add_ecgroup [e_448; d_448; p_448] EDWARDS448_GROUP;;

let FINITE_GROUP_CARRIER_EDWARDS448 = prove
 (`FINITE(group_carrier edwards448_group)`,
  REWRITE_TAC[EDWARDS448_GROUP] THEN MATCH_MP_TAC FINITE_EDWARDS_CURVE THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_RING;
              FIELD_INTEGER_MOD_RING; PRIME_P448] THEN
  REWRITE_TAC[p_448] THEN CONV_TAC NUM_REDUCE_CONV);;

let GENERATOR_IN_GROUP_CARRIER_EDWARDS448 = prove
 (`E_448 IN group_carrier edwards448_group`,
  REWRITE_TAC[E_448] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_EDWARDS448_E448 = prove
 (`group_element_order edwards448_group E_448 = n_448`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_EDWARDS448; PRIME_N448] THEN
  REWRITE_TAC[E_448; el 1 (CONJUNCTS EDWARDS448_GROUP)] THEN
  REWRITE_TAC[edwards_0; PAIR_EQ; INTEGER_MOD_RING] THEN
  REWRITE_TAC[n_448; p_448] THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC);;

let GENERATOR_IN_GROUP_CARRIER_F448 = prove
 (`F_448 IN group_carrier edwards448_group`,
  REWRITE_TAC[F_448] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_EDWARDS448_F448 = prove
 (`group_element_order edwards448_group F_448 = n_448`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_F448; PRIME_N448] THEN
  REWRITE_TAC[F_448; el 1 (CONJUNCTS EDWARDS448_GROUP)] THEN
  REWRITE_TAC[edwards_0; PAIR_EQ; INTEGER_MOD_RING] THEN
  REWRITE_TAC[n_448; p_448] THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC);;

let GENERATOR_IN_GROUP_CARRIER_H448 = prove
 (`H_448 IN group_carrier edwards448_group`,
  REWRITE_TAC[H_448] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_EDWARDS448_H448 = prove
 (`group_element_order edwards448_group H_448 = n_448`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_PRIME;
           GENERATOR_IN_GROUP_CARRIER_H448; PRIME_N448] THEN
  REWRITE_TAC[H_448; el 1 (CONJUNCTS EDWARDS448_GROUP)] THEN
  REWRITE_TAC[edwards_0; PAIR_EQ; INTEGER_MOD_RING] THEN
  REWRITE_TAC[n_448; p_448] THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC);;

let EDWARDS448_ORDER_1 = prove
 (`{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 1} = {(&0,&1)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_SING] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(MESON[]
   `!a'. a' IN G /\ (x IN G ==> (P x <=> x = a')) /\ a' = a
         ==> (x IN G /\ P x <=> x = a)`) THEN
  EXISTS_TAC `group_id edwards448_group` THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_EQ_1; GROUP_ID] THEN
  REWRITE_TAC[EDWARDS448_GROUP; edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_448; PAIR_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let EDWARDS448_ORDER_2 = prove
 (`{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 2} = {(&0,&p_448 - &1)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_SING] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(MESON[]
   `a IN G /\ (x IN G ==> (P x <=> x = a))
    ==> (x IN G /\ P x <=> x = a)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EDWARDS448_GROUP; IN] THEN REWRITE_TAC[edwards_curve] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; p_448; d_448] THEN
    CONV_TAC(DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV));
    DISCH_TAC] THEN
  REWRITE_TAC[edwards448_group] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)  EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_448] THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P448] THEN
    ASM_REWRITE_TAC[GSYM edwards448_group; INTEGER_MOD_RING_CHAR] THEN
    REWRITE_TAC[e_448; d_448; p_448; GSYM INT_OF_NUM_EQ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ; p_448] THEN
  CONV_TAC(DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)));;

let EDWARDS448_ORDER_4 = prove
 (`{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 4} =
   {(&1,&0), (&p_448 - &1,&0)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(MESON[]
   `(a IN G /\ b IN G) /\ (x IN G ==> (P x <=> x = a \/ x = b))
    ==> (x IN G /\ P x <=> x = a \/ x = b)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EDWARDS448_GROUP; IN] THEN REWRITE_TAC[edwards_curve] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; p_448; d_448; e_448] THEN
    CONV_TAC(DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV));
    DISCH_TAC] THEN
  REWRITE_TAC[edwards448_group] THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_448`; `&e_448:int`; `&d_448:int`; `&1:int`;
    `(x,y):int#int`]
   EDWARDS_GROUP_ELEMENT_ORDER_EQ_4) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_448] THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P448] THEN
    ASM_REWRITE_TAC[GSYM edwards448_group; INTEGER_MOD_RING_CHAR] THEN
    REWRITE_TAC[e_448; d_448; p_448; GSYM INT_OF_NUM_EQ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    CONV_TAC(DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV));
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ; p_448] THEN
  CONV_TAC(DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)));;

let EDWARDS448_ORDER_8 = prove
 (`{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 8} = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN DISCH_TAC THEN
  REWRITE_TAC[edwards448_group] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)  EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV o
    rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_448] THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P448] THEN
    ASM_REWRITE_TAC[GSYM edwards448_group; INTEGER_MOD_RING_CHAR] THEN
    REWRITE_TAC[e_448; d_448; p_448; GSYM INT_OF_NUM_EQ] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[INT_REM_EQ] THEN
  ABBREV_TAC `z:int = x pow 4` THEN
  REWRITE_TAC[e_448; d_448; INT_MUL_ASSOC] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM d_448] THEN DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(&4 * z:int == (&1 + d * z) pow 2) (mod p)
    ==> ((d pow 2 * z + (d - &2)) pow 2 == &4 * (p + &1 - d)) (mod p)`)) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
  SPEC_TAC(`&d_448 pow 2 * z + &d_448 - &2:int`,`w:int`) THEN
  REWRITE_TAC[GSYM INT_FORALL_ABS] THEN
  REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN
  REWRITE_TAC[p_448; d_448] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  SIMP_TAC[EULER_CRITERION; REWRITE_RULE[p_448] PRIME_P448] THEN
  CONV_TAC(DEPTH_CONV
   (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448 = prove
 (`EE_448 IN group_carrier edwards448_group`,
  REWRITE_TAC[EE_448] THEN CONV_TAC ECGROUP_CARRIER_CONV);;

let GROUP_ELEMENT_ORDER_EDWARDS448_EE448 = prove
 (`group_element_order edwards448_group EE_448 = 4 * n_448`,
  ABBREV_TAC `h = (&1,&0):int#int` THEN
  SUBGOAL_THEN
   `h IN group_carrier edwards448_group /\
    group_element_order edwards448_group h = 4`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE
     `h IN s /\ P h <=> h IN {x | x IN s /\ P x}`] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[EDWARDS448_ORDER_4; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `EE_448 = group_mul edwards448_group h E_448` SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[E_448; EE_448] THEN
    CONV_TAC(RAND_CONV ECGROUP_MUL_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_ELEMENT_ORDER_MUL_EQ o
    lhand o snd) THEN
  ASM_REWRITE_TAC[GROUP_ELEMENT_ORDER_EDWARDS448_E448] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_EDWARDS448] THEN CONJ_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[E_448] THEN
    CONV_TAC(BINOP_CONV ECGROUP_MUL_CONV) THEN REFL_TAC;
    REWRITE_TAC[n_448] THEN CONV_TAC COPRIME_CONV]);;

let SIZE_EDWARDS448_GROUP = prove
 (`group_carrier edwards448_group HAS_SIZE (4 * n_448)`,
  REWRITE_TAC[HAS_SIZE; FINITE_GROUP_CARRIER_EDWARDS448] THEN
  MP_TAC(ISPECL [`edwards448_group`; `EE_448`]
    GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
  REWRITE_TAC[FINITE_GROUP_CARRIER_EDWARDS448;
              FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448] THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM;
              GROUP_ELEMENT_ORDER_EDWARDS448_EE448] THEN
  X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0; MULT_CLAUSES; GROUP_CARRIER_NONEMPTY;
               FINITE_GROUP_CARRIER_EDWARDS448] THEN
  ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `d = 2` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(ARITH_RULE
      `~(s = 8 * n) ==> s = (4 * n) * 2 ==> u:num = v`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`edwards448_group`; `2`; `3`] SYLOW_THEOREM) THEN
    ASM_REWRITE_TAC[FINITE_GROUP_CARRIER_EDWARDS448; PRIME_2; NOT_IMP] THEN
    REWRITE_TAC[n_448] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(LAND_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:int#int->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `CARD(h:int#int->bool) <= 4` MP_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
    TRANS_TAC LE_TRANS
     `CARD{(&0:int,&1:int), (&0,&p_448 - &1), (&1,&0), (&p_448 - &1,&0)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:int#int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subgroup_generated edwards448_group h`; `p:int#int`]
      GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
    ASM_SIMP_TAC[FINITE_SUBGROUP_GENERATED; FINITE_GROUP_CARRIER_EDWARDS448;
                 CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    REWRITE_TAC[GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED] THEN
    SIMP_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 3`); DIVIDES_PRIMEPOW; PRIME_2] THEN
    REWRITE_TAC[ARITH_RULE `i <= 3 <=> i < 4`; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `x IN group_carrier G /\
      {y | y IN group_carrier G /\ group_element_order G y = n} SUBSET s
      ==> group_element_order G x = n ==> x IN s`) THEN
    REWRITE_TAC[EDWARDS448_ORDER_1; EDWARDS448_ORDER_2;
                EDWARDS448_ORDER_4; EDWARDS448_ORDER_8] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(ARITH_RULE
     `n * 3 <= n * d /\ s < 3 * n ==> s = n * d ==> u:num = v`) THEN
    REWRITE_TAC[n_448] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM n_448; EDWARDS448_GROUP] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_BOUND_EDWARDS_CURVE o
      lhand o snd) THEN
    REWRITE_TAC[EDWARDS_NONSINGULAR_448] THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P448] THEN
     SIMP_TAC[FINITE_INTEGER_MOD_RING; CARD_INTEGER_MOD_RING;
             IN_INTEGER_MOD_RING_CARRIER; n_448; p_448; d_448;
             INTEGER_MOD_RING; e_448; INT_OF_NUM_CLAUSES; ARITH_EQ] THEN
    ARITH_TAC]);;

let GENERATED_EDWARDS448_GROUP = prove
 (`subgroup_generated edwards448_group {EE_448} = edwards448_group`,
  SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER;
           FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448;
           FINITE_GROUP_CARRIER_EDWARDS448] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_EDWARDS448_EE448;
              REWRITE_RULE[HAS_SIZE] SIZE_EDWARDS448_GROUP]);;

let CYCLIC_EDWARDS448_GROUP = prove
 (`cyclic_group edwards448_group`,
  MESON_TAC[CYCLIC_GROUP_ALT; GENERATED_EDWARDS448_GROUP]);;

let ABELIAN_EDWARDS448_GROUP = prove
 (`abelian_group edwards448_group`,
  MESON_TAC[CYCLIC_EDWARDS448_GROUP; CYCLIC_IMP_ABELIAN_GROUP]);;
