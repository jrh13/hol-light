(* ========================================================================= *)
(* The Bernstein-Yang "divstep" iteration for gcd, modular inverse etc.      *)
(*            https://gcd.cr.yp.to/safegcd-20190413.pdf                      *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/integer.ml";;

(* ------------------------------------------------------------------------- *)
(* The core divstep iteration for integers f and g (section 8, page 21).     *)
(* Here d is a real number, to allow possibilities like d = 1/2.             *)
(* ------------------------------------------------------------------------- *)

let divstep = new_definition
  `divstep(d:real,f:int,g:int) =
        if d > &0 /\ g rem &2 = &1
        then &1 - d, g, (g - f) div &2
        else &1 + d, f, (g + (g rem &2) * f) div &2`;;

(* ------------------------------------------------------------------------- *)
(* As remarked in 8.2, page 22, we can subdivide into separate operations.   *)
(* ------------------------------------------------------------------------- *)

let divstep1 = new_definition
  `divstep1(d:real,f:int,g:int) =
        if d > &0 /\ g rem &2 = &1
        then --d, g, --f
        else d, f, g`;;

let divstep2 = new_definition
 `divstep2(d:real,f:int,g:int) =
        &1 + d,f,(g + (g rem &2) * f) div &2`;;

let DIVSTEP1_DIVSTEP2 = prove
 (`!d f g.
        f rem &2 = &1
        ==> (divstep2 o divstep1) (d,f,g) = divstep (d,f,g)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM; divstep1; divstep] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[divstep2] THEN
  ASM_REWRITE_TAC[INT_REM_LNEG; PAIR_EQ] THEN
  CONJ_TAC THENL [INT_ARITH_TAC; CONV_TAC INT_REDUCE_CONV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Invariants: f stays odd, g stays zero if hit, the gcds stay the same.     *)
(* ------------------------------------------------------------------------- *)

let DIVSTEP_STAYS_ODD = prove
 (`!d f g d' f' g'.
        f rem &2 = &1 /\
        divstep(d,f,g) = d',f',g'
        ==> f' rem &2 = &1`,
  REWRITE_TAC[divstep] THEN MESON_TAC[PAIR_EQ]);;

let DIVSTEP_STAYS_ZERO = prove
 (`!d f g d' f' g'.
        g = &0 /\
        divstep(d,f,g) = d',f',g'
        ==> g' = &0`,
  SIMP_TAC[divstep; IMP_CONJ; INT_REM_ZERO; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID; INT_DIV_ZERO; PAIR_EQ] THEN
  MESON_TAC[]);;

let DIVSTEP_MAINTAINS_GCD = prove
 (`!d f g d' f' g'.
        f rem &2 = &1 /\
        divstep(d,f,g) = d',f',g'
        ==> gcd(f',g') = gcd(f,g)`,
  let lemma = prove
   (`!m n. m rem &2 = &1 /\ n rem &2 = &0 ==> gcd(m,n div &2) = gcd(m,n)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_REM_EQ_0]) THEN
    REWRITE_TAC[GSYM(CONJUNCT1 INT_MUL_DIV_EQ)] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC INT_GCD_EQ THEN GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
     `coprime(k:int,m)
      ==> (d divides m /\ d divides p <=>
           d divides m /\ d divides (k * p))`) THEN
    MP_TAC(SPECL [`m:int`; `&2:int`] INT_DIVISION_SIMP) THEN
    ASM_REWRITE_TAC[] THEN SPEC_TAC(`&2:int`,`p:int`) THEN
    CONV_TAC INTEGER_RULE) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [divstep]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ONCE_REWRITE_TAC[GSYM INT_SUB_REM; GSYM INT_ADD_REM] THEN
  MP_TAC(SPEC `g:int` INT_REM_2_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  TRY(DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC INT_GCD_EQ THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Sizes; cf the remarks on p22.                                             *)
(* ------------------------------------------------------------------------- *)

let DIVSTEP_RANGE_2SCOMPLEMENT = prove
 (`!d f g d' f' g' n.
        f rem &2 = &1 /\
        divstep(d,f,g) = d',f',g' /\
        --(&2 pow n) <= f /\ f < &2 pow n /\
        --(&2 pow n) <= g /\ g < &2 pow n
        ==> --(&2 pow n) <= f' /\ f' < &2 pow n /\
            --(&2 pow n) <= g' /\ g' < &2 pow n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [divstep]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LE_DIV_EQ; INT_ARITH `&0:int < &2`] THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_THEN SUBST1_TAC (SPEC `g:int` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_RANGE_SIGNMAGNITUDE = prove
 (`!d f g d' f' g' n.
        f rem &2 = &1 /\
        divstep(d,f,g) = d',f',g' /\
        --(&2 pow n) < f /\ f < &2 pow n /\
        --(&2 pow n) < g /\ g < &2 pow n
        ==> --(&2 pow n) < f' /\ f' < &2 pow n /\
            --(&2 pow n) < g' /\ g' < &2 pow n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [divstep]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LT_DIV_EQ; INT_ARITH `&0:int < &2`] THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_THEN SUBST1_TAC (SPEC `g:int` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extend invariant lemmas to n-fold iteration of divstep.                   *)
(* ------------------------------------------------------------------------- *)

let ITER_DIVSTEP_ODD = prove
 (`!n d f g d' f' g'.
        f rem &2 = &1 /\
        ITER n divstep (d,f,g) = d',f',g'
        ==> f' rem &2 = &1`,
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER_ALT; PAIR_EQ] THENL
   [MESON_TAC[]; REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM_METIS_TAC[DIVSTEP_STAYS_ODD; PAIR]);;

let ITER_DIVSTEP_ZERO = prove
 (`!n d f g d' f' g'.
        g = &0 /\
        ITER n divstep (d,f,g) = d',f',g'
        ==> g' = &0`,
  INDUCT_TAC THEN REWRITE_TAC[ITER_ALT; PAIR_EQ] THENL
   [MESON_TAC[]; REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM_METIS_TAC[DIVSTEP_STAYS_ZERO; PAIR]);;

let ITER_DIVSTEP_GCD = prove
 (`!n d f g d' f' g'.
        f rem &2 = &1 /\
        ITER n divstep (d,f,g) = d',f',g'
        ==> gcd(f',g') = gcd(f,g)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER_ALT; PAIR_EQ] THEN
  ASM_METIS_TAC[DIVSTEP_STAYS_ODD; DIVSTEP_MAINTAINS_GCD; PAIR]);;

(* ------------------------------------------------------------------------- *)
(* So we can express termination with g = 0 in two equivalent ways.          *)
(* ------------------------------------------------------------------------- *)

let ITER_DIVSTEP_BOUND_ALT = prove
 (`!t m. (?n. n <= m /\ SND(SND(ITER n divstep t)) = &0) <=>
         SND(SND(ITER m divstep t)) = &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[LE_REFL]] THEN
  REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  SIMP_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ITER_ADD)] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SPEC_TAC(`ITER n divstep t`,`q:real#int#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[ITER_DIVSTEP_ZERO; PAIR]);;
