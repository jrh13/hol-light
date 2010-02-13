(* ========================================================================= *)
(* Inclusion-exclusion principle, the usual and generalized forms.           *)
(* ========================================================================= *)

needs "Library/products.ml";;

(* ------------------------------------------------------------------------- *)
(* Simple set theory lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let SUBSET_INSERT_EXISTS = prove
 (`!s x:A t. s SUBSET (x INSERT t) <=>
                s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(a /\ ~b ==> c) ==> a ==> b \/ c`) THEN
  DISCH_TAC THEN EXISTS_TAC `s DELETE (x:A)` THEN ASM SET_TAC[]);;

let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Analogous principle for real numbers.                                     *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_REAL = prove
 (`!f s:A->bool.
        FINITE s
        ==> product s (\x. &1 - f x) =
            sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * product t f)`,
  let lemma = prove
   (`{t | ?u. u SUBSET s /\ t = x INSERT u} =
     IMAGE (\s. x INSERT s) {t | t SUBSET s}`,
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[]) in
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUBSET_EMPTY; SUM_SING; CARD_CLAUSES; real_pow;
           SET_RULE `{x | x = a} = {a}`; REAL_MUL_RID] THEN
  REWRITE_TAC[SUBSET_INSERT_EXISTS] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `{t | p t \/ q t} = {t | p t} UNION {t | q t}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET; lemma; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM lemma] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_SUB_RDISTRIB; REAL_MUL_LID; real_sub] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lemma] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[o_THM; IN_ELIM_THM] THEN X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(t:A->bool) /\ ~(x IN t)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Characteristic functions (real).                                          *)
(* ------------------------------------------------------------------------- *)

let char = new_definition
 `char s = \x. if x IN s then &1 else &0`;;

let CARD_CHAR = prove
 (`!s t. FINITE t /\ s SUBSET t ==> &(CARD s) = sum t (char s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_SUBSET) THEN
  ASM_SIMP_TAC[CARD_EQ_SUM] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
  ASM_SIMP_TAC[char]);;

let CHAR_INTER = prove
 (`!s t. char(s INTER t) x = char s x * char t x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[char; IN_INTER] THEN REAL_ARITH_TAC);;

let CHAR_INTERS = prove
 (`!s. FINITE s /\ (!k. k IN s ==> FINITE k)
       ==> char (INTERS s) x = product s (\k. char k x)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[INTERS_INSERT; IN_INSERT; PRODUCT_CLAUSES] THEN
  CONJ_TAC THENL [REWRITE_TAC[INTERS_0; char; IN_UNIV]; ALL_TAC] THEN
  SIMP_TAC[CHAR_INTER]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main version of inclusion-exclusion.                            *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum {t | t SUBSET s /\ ~(t = {})}
                    (\t. (-- &1) pow (CARD t + 1) * &(CARD(INTERS t)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t:(A->bool)->bool | t SUBSET s /\ ~(t = {})}
                  (\t. if t = {} then -- &(CARD(UNIONS s))
                       else -- &1 pow (CARD t + 1) * &(CARD(INTERS t)))` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_EQ]] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ ~(x = a)} = {x | P x} DELETE a`] THEN
  ASM_SIMP_TAC[SUM_DELETE; FINITE_POWERSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ARITH `a = b - --a <=> --b = &0`; GSYM SUM_NEG] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_RID] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t:(A->bool)->bool | t SUBSET s}
                  (\t. -- &1 pow (CARD t) *
                       sum (UNIONS s) (\x. product t (\k. char k x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:(A->bool)->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PRODUCT_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_UNIONS; CARD_CLAUSES] THEN
    REWRITE_TAC[real_pow; REAL_MUL_LID] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum (UNIONS s) (char(INTERS t:A->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_CHAR THEN
      ASM_SIMP_TAC[FINITE_UNIONS] THEN ASM SET_TAC[];
      MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC CHAR_INTERS THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]]];
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_POWERSET] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum (UNIONS s) (\x:A. product s (\k:A->bool. &1 - char k x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INCLUSION_EXCLUSION_REAL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUM_EQ_0 THEN
      REWRITE_TAC[IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
      ASM_SIMP_TAC[PRODUCT_EQ_0; REAL_SUB_0] THEN MESON_TAC[char]]]);;

(* ------------------------------------------------------------------------- *)
(* A more conventional form.                                                 *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_USUAL = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum (1..CARD s) (\n. (-- &1) pow (n + 1) *
                                     sum {t | t SUBSET s /\ t HAS_SIZE n}
                                         (\t. &(CARD(INTERS t))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INCLUSION_EXCLUSION] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) (ISPEC `CARD` SUM_IMAGE_GEN) o
     lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(MESON[] `s = t /\ sum t f = sum t g ==> sum s f = sum t g`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
    REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
    ASM_MESON_TAC[CHOOSE_SUBSET; CARD_SUBSET; FINITE_SUBSET; CARD_EQ_0;
                  HAS_SIZE];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[CARD_EQ_0; ARITH_RULE `~(1 <= 0)`; FINITE_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* A combinatorial lemma about subsets of a finite set.                      *)
(* ------------------------------------------------------------------------- *)

let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

let CARD_ADJUST_LEMMA = prove
 (`!f:A->B s x y.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        x = y + CARD (IMAGE f s)
        ==> x = y + CARD s`,
  MESON_TAC[CARD_IMAGE_INJ]);;

let CARD_SUBSETS_STEP = prove
 (`!x:A s. FINITE s /\ ~(x IN s) /\ u SUBSET s
           ==> CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ ODD(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} /\
               CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ EVEN(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:A`,`:B`] CARD_ADJUST_LEMMA) THEN
  EXISTS_TAC `\u. (x:A) INSERT u` THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
   ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; FINITE_INSERT] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
     REWRITE_TAC[TAUT `~(a /\ b) <=> b ==> ~a`; FORALL_IN_IMAGE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
   GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A->bool` THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNION; SUBSET_INSERT_EXISTS] THEN
   REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
   REWRITE_TAC[RIGHT_OR_DISTRIB; LEFT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
   AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
   X_GEN_TAC `v:A->bool` THEN
   ASM_CASES_TAC `t = (x:A) INSERT v` THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(v:A->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
   BINOP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET]));;

let CARD_SUBSUPERSETS_EVEN_ODD = prove
 (`!s u:A->bool.
        FINITE u /\ s PSUBSET u
        ==> CARD {t | s SUBSET t /\ t SUBSET u /\ EVEN(CARD t)} =
            CARD {t | s SUBSET t /\ t SUBSET u /\ ODD(CARD t)}`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `CARD(u:A->bool)` THEN
  REWRITE_TAC[PSUBSET_MEMBER] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  MP_TAC(SET_RULE `~((x:A) IN (u DELETE x))`) THEN
  ABBREV_TAC `v:A->bool = u DELETE x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE v /\ (s:A->bool) SUBSET v` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[FINITE_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSETS_STEP] THEN ASM_CASES_TAC `s:A->bool = v` THENL
   [REWRITE_TAC[CONJ_ASSOC; SUBSET_ANTISYM_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM;
    ASM_SIMP_TAC[CARD_CLAUSES; LT; PSUBSET]]);;

let SUM_ALTERNATING_CANCELS = prove
 (`!s:A->bool f.
        FINITE s /\
        CARD {x | x IN s /\ EVEN(f x)} = CARD {x | x IN s /\ ODD(f x)}
        ==> sum s (\x. (-- &1) pow (f x)) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x | x IN s /\ EVEN(f x)} (\x. (-- &1) pow (f x)) +
              sum {x:A | x IN s /\ ODD(f x)} (\x. (-- &1) pow (f x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_EVEN; SUM_CONST;
               FINITE_RESTRICT; REAL_ARITH `x * &1 + x * -- &1 = &0`]);;

(* ------------------------------------------------------------------------- *)
(* Hence a general "Moebius inversion" inclusion-exclusion principle.        *)
(* This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_SYMMETRIC = prove
 (`!f g:(A->bool)->real.
    (!s. FINITE s
         ==> g(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * f(t)))
    ==> !s. FINITE s
            ==> f(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * g(t))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t:A->bool | t SUBSET s}
                  (\t. (-- &1) pow (CARD t) *
                       sum {u | u IN {u | u SUBSET s} /\ u SUBSET t}
                           (\u. (-- &1) pow (CARD u) * f(u)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; SET_RULE
     `s SUBSET t ==> (u SUBSET t /\ u SUBSET s <=> u SUBSET s)`] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_RESTRICT o lhs o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RMUL; IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {u | u SUBSET s} (\u:A->bool. if u = s then f(s) else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_DELTA; IN_ELIM_THM; SUBSET_REFL]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUBSET_ANTISYM_EQ; SET_RULE `{x | x = a} = {a}`] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; REAL_POW_ONE; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN REPEAT DISJ1_TAC THEN
  MATCH_MP_TAC SUM_ALTERNATING_CANCELS THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
  MATCH_MP_TAC CARD_SUBSUPERSETS_EVEN_ODD THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The more typical non-symmetric version.                                   *)
(* ------------------------------------------------------------------------- *)

let INCLUSION_EXCLUSION_MOBIUS = prove
 (`!f g:(A->bool)->real.
        (!s. FINITE s ==> g(s) = sum {t | t SUBSET s} f)
        ==> !s. FINITE s
                ==> f(s) = sum {t | t SUBSET s}
                               (\t. (-- &1) pow (CARD s - CARD t) * g(t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. -- &1 pow CARD(t:A->bool) * f t`; `g:(A->bool)->real`]
                INCLUSION_EXCLUSION_SYMMETRIC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[EVEN_ADD; REAL_POW_ONE; REAL_POW_NEG; REAL_MUL_LID; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) ((-- &1) pow (CARD(s:A->bool)))`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; GSYM MULT_2] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_ARITH `~(-- &1 = &0)`; CARD_SUBSET] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC);;
