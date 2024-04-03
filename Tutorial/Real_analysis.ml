needs "Library/analysis.ml";;
needs "Library/transc.ml";;

let cheb = define
 `(!x. cheb 0 x = &1) /\
  (!x. cheb 1 x = x) /\
  (!n x. cheb (n + 2) x = &2 * x * cheb (n + 1) x - cheb n x)`;;

let CHEB_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;

let CHEB_COS = prove
 (`!n x. cheb n (cos x) = cos(&n * x)`,
  MATCH_MP_TAC CHEB_INDUCT THEN
  REWRITE_TAC[cheb; REAL_MUL_LZERO; REAL_MUL_LID; COS_0] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_MUL_LID; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[COS_ADD; COS_DOUBLE; SIN_DOUBLE] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let CHEB_RIPPLE = prove
 (`!x. abs(x) <= &1 ==> abs(cheb n x) <= &1`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
  MESON_TAC[CHEB_COS; ACS_COS; COS_BOUNDS]);;

let NUM_ADD2_CONV =
  let add_tm = `(+):num->num->num`
  and two_tm = `2` in
  fun tm ->
    let m = mk_numeral(dest_numeral tm -/ Num.num_of_int 2) in
    let tm' = mk_comb(mk_comb(add_tm,m),two_tm) in
    SYM(NUM_ADD_CONV tm');;

let CHEB_CONV =
  let [pth0;pth1;pth2] = CONJUNCTS cheb in
  let rec conv tm =
   (GEN_REWRITE_CONV I [pth0; pth1] ORELSEC
    (LAND_CONV NUM_ADD2_CONV THENC
     GEN_REWRITE_CONV I [pth2] THENC
     COMB2_CONV
      (funpow 3 RAND_CONV ((LAND_CONV NUM_ADD_CONV) THENC conv))
      conv THENC
     REAL_POLY_CONV)) tm in
  conv;;

CHEB_CONV `cheb 8 x`;;

let CHEB_2N1 = prove
 (`!n x. ((x - &1) * (cheb (2 * n + 1) x - &1) =
          (cheb (n + 1) x - cheb n x) pow 2) /\
         (&2 * (x pow 2 - &1) * (cheb (2 * n + 2) x - &1) =
          (cheb (n + 2) x - cheb n x) pow 2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC CHEB_INDUCT THEN
  REWRITE_TAC[ARITH; cheb; CHEB_CONV `cheb 2 x`; CHEB_CONV `cheb 3 x`] THEN
  REPEAT(CHANGED_TAC
   (REWRITE_TAC[GSYM ADD_ASSOC; LEFT_ADD_DISTRIB; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `n + 5 = (n + 3) + 2`;
                ARITH_RULE `n + 4 = (n + 2) + 2`;
                ARITH_RULE `n + 3 = (n + 1) + 2`;

                cheb])) THEN
  CONV_TAC REAL_RING);;

let IVT_LEMMA1 = prove
 (`!f. (!x. f contl x)
       ==> !x y. f(x) <= &0 /\ &0 <= f(y) ==> ?x. f(x) = &0`,
  ASM_MESON_TAC[IVT; IVT2; REAL_LE_TOTAL]);;

let IVT_LEMMA2 = prove
 (`!f. (!x. f contl x) /\ (?x. f(x) <= x) /\ (?y. y <= f(y)) ==> ?x. f(x) = x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `\x. f x - x` IVT_LEMMA1) THEN
  ASM_SIMP_TAC[CONT_SUB; CONT_X] THEN
  SIMP_TAC[REAL_LE_SUB_LADD; REAL_LE_SUB_RADD; REAL_SUB_0; REAL_ADD_LID] THEN
  ASM_MESON_TAC[]);;

let SARKOVSKII_TRIVIAL = prove
 (`!f:real->real. (!x. f contl x) /\ (?x. f(f(f(x))) = x) ==> ?x. f(x) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_LEMMA2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC
   (MESON[] `P x \/ P (f x) \/ P (f(f x)) ==> ?x:real. P x`) THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN REAL_ARITH_TAC);;
