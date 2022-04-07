(* ========================================================================= *)
(* The three forms of curve25519 related via isomorphisms.                   *)
(* ========================================================================= *)

needs "EC/edmont.ml";;
needs "EC/montwe.ml";;
needs "EC/edwards25519.ml";;
needs "EC/curve25519.ml";;
needs "EC/wei25519.ml";;

(* ------------------------------------------------------------------------- *)
(* Extra scaling factor.                                                     *)
(* ------------------------------------------------------------------------- *)

(***
https://datatracker.ietf.org/doc/html/draft-ietf-lwig-curve-representations-23
In terms of the other parameters c_25519 = sqrt(-(A_25519+2)/B_25519)
***)

let c_25519 = define `c_25519 = 51042569399160536130206135233146329284152202253034631822681833788666877215207`;;

(* ------------------------------------------------------------------------- *)
(* Mappings between Edwards and Montgomery forms.                            *)
(* ------------------------------------------------------------------------- *)

let curve25519_of_edwards25519 = define
 `curve25519_of_edwards25519 =
        montgomery_of_edwards (integer_mod_ring p_25519) (&c_25519)`;;

let edwards25519_of_curve25519 = define
 `edwards25519_of_curve25519 =
        edwards_of_montgomery (integer_mod_ring p_25519) (&c_25519)`;;

let MCURVE_OF_ECURVE_25519 = prove
 (`mcurve_of_ecurve (integer_mod_ring p_25519,&e_25519,&d_25519) (&c_25519) =
   (integer_mod_ring p_25519,&A_25519,&1)`,
  REWRITE_TAC[mcurve_of_ecurve; PAIR_EQ] THEN
  REWRITE_TAC[p_25519; A_25519; e_25519; d_25519; c_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN REWRITE_TAC[]);;

let GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 = prove
 (`group_isomorphisms
      (edwards25519_group,curve25519_group)
      (curve25519_of_edwards25519,edwards25519_of_curve25519)`,
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`; `&c_25519:int`]
   GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP) THEN
  REWRITE_TAC[GSYM curve25519_of_edwards25519; GSYM edwards25519_of_curve25519;
              GSYM curve25519_group; GSYM edwards25519_group;
              MCURVE_OF_ECURVE_25519] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[EDWARD_NONSINGULAR_25519] THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CHAR; GSYM INT_OF_NUM_EQ] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING] THEN
  REWRITE_TAC[p_25519; e_25519; d_25519; c_25519] THEN
  CONV_TAC INT_REDUCE_CONV);;

let ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519 = prove
 (`edwards25519_group isomorphic_group curve25519_group`,
  MP_TAC GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 THEN
  MESON_TAC[isomorphic_group; GROUP_ISOMORPHISMS_IMP_ISOMORPHISM]);;

let ISOMORPHIC_GROUPS_CURVE25519_EDWARDS25519 = prove
 (`curve25519_group isomorphic_group edwards25519_group`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519]);;

let CURVE25519_OF_EDWARDS25519_E25519 = prove
 (`curve25519_of_edwards25519 E_25519 = C_25519`,
  REWRITE_TAC[curve25519_of_edwards25519; montgomery_of_edwards;
    C_25519; E_25519; PAIR_EQ; p_25519; e_25519; d_25519; c_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

let CURVE25519_OF_EDWARDS25519_EE25519 = prove
 (`curve25519_of_edwards25519 EE_25519 = CC_25519`,
  REWRITE_TAC[curve25519_of_edwards25519; montgomery_of_edwards;
    CC_25519; EE_25519; PAIR_EQ; p_25519; e_25519; d_25519; c_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

let EDWARDS25519_OF_CURVE25519_C25519 = prove
 (`edwards25519_of_curve25519 C_25519 = E_25519`,
  REWRITE_TAC[edwards25519_of_curve25519; edwards_of_montgomery;
     C_25519; E_25519; PAIR_EQ; p_25519; e_25519; d_25519; c_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

let EDWARDS25519_OF_CURVE25519_CC25519 = prove
 (`edwards25519_of_curve25519 CC_25519 = EE_25519`,
  REWRITE_TAC[edwards25519_of_curve25519; edwards_of_montgomery;
    CC_25519; EE_25519; PAIR_EQ; p_25519; e_25519; d_25519; c_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Mappings between Montgomery and Weierstrass forms.                        *)
(* ------------------------------------------------------------------------- *)

let wei25519_of_curve25519 = define
 `wei25519_of_curve25519 =
        weierstrass_of_montgomery (integer_mod_ring p_25519,&A_25519,&1)`;;

let curve25519_of_wei25519 = define
 `curve25519_of_wei25519 =
        montgomery_of_weierstrass (integer_mod_ring p_25519,&A_25519,&1)`;;

let WCURVE_OF_MCURVE_25519 = prove
 (`wcurve_of_mcurve(integer_mod_ring p_25519,&A_25519,&1) =
   (integer_mod_ring p_25519,&a_25519,&b_25519)`,
  REWRITE_TAC[wcurve_of_mcurve; p_25519; PAIR_EQ;
              a_25519; b_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  REWRITE_TAC[]);;

let GROUP_ISOMORPHISMS_CURVE25519_WEI25519 = prove
 (`group_isomorphisms
      (curve25519_group,wei25519_group)
      (wei25519_of_curve25519,curve25519_of_wei25519)`,
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&A_25519:int`; `&1:int`]
   GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP) THEN
  REWRITE_TAC[GSYM wei25519_of_curve25519; GSYM curve25519_of_wei25519;
              GSYM wei25519_group; GSYM curve25519_group;
              WCURVE_OF_MCURVE_25519] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[montgomery_nonsingular] THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CHAR; GSYM INT_OF_NUM_EQ] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_25519; A_25519] THEN CONV_TAC INT_REDUCE_CONV);;

let ISOMORPHIC_GROUPS_CURVE25519_WEI25519 = prove
 (`curve25519_group isomorphic_group wei25519_group`,
  MP_TAC GROUP_ISOMORPHISMS_CURVE25519_WEI25519 THEN
  MESON_TAC[isomorphic_group; GROUP_ISOMORPHISMS_IMP_ISOMORPHISM]);;

let ISOMORPHIC_GROUPS_WEI25519_CURVE25519 = prove
 (`wei25519_group isomorphic_group curve25519_group`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[ISOMORPHIC_GROUPS_CURVE25519_WEI25519]);;

let WEI25519_OF_CURVE25519_C25519 = prove
 (`wei25519_of_curve25519 C_25519 = G_25519`,
  REWRITE_TAC[wei25519_of_curve25519; weierstrass_of_montgomery;
     C_25519; G_25519; PAIR_EQ; p_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

let WEI25519_OF_CURVE25519_CC25519 = prove
 (`wei25519_of_curve25519 CC_25519 = GG_25519`,
  REWRITE_TAC[wei25519_of_curve25519; weierstrass_of_montgomery;
     CC_25519; GG_25519; PAIR_EQ; p_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

let CURVE25519_OF_WEI25519_G25519 = prove
 (`curve25519_of_wei25519 G_25519 = C_25519`,
  REWRITE_TAC[curve25519_of_wei25519; montgomery_of_weierstrass;
     C_25519; G_25519; PAIR_EQ; p_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;

let CURVE25519_OF_WEI25519_GG25519 = prove
 (`curve25519_of_wei25519 GG_25519 = CC_25519`,
  REWRITE_TAC[curve25519_of_wei25519; montgomery_of_weierstrass;
     CC_25519; GG_25519; PAIR_EQ; p_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  CONV_TAC INT_REDUCE_CONV);;
