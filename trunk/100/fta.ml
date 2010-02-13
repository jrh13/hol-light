(* ========================================================================= *)
(* The fundamental theorem of arithmetic (unique prime factorization).       *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Definition of iterated product.                                           *)
(* ------------------------------------------------------------------------- *)

let nproduct = new_definition `nproduct = iterate ( * )`;;

let NPRODUCT_CLAUSES = prove
 (`(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_EQ_1_EQ = prove
 (`!s f. FINITE s ==> (nproduct s f = 1 <=> !x. x IN s ==> f(x) = 1)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT; MULT_EQ_1; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

let NPRODUCT_SPLITOFF = prove
 (`!x:A f s. FINITE s
             ==> nproduct s f =
                 (if x IN s then f(x) else 1) * nproduct (s DELETE x) f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; SET_RULE `~(x IN s) ==> s DELETE x = s`] THEN
  SUBGOAL_THEN `s = (x:A) INSERT (s DELETE x)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th] THEN
              ASM_SIMP_TAC[NPRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]);;

let NPRODUCT_SPLITOFF_HACK = prove
 (`!x:A f s. nproduct s f =
             if FINITE s then
               (if x IN s then f(x) else 1) * nproduct (s DELETE x) f
             else nproduct s f`,
  REPEAT STRIP_TAC THEN MESON_TAC[NPRODUCT_SPLITOFF]);;

let NPRODUCT_EQ = prove
 (`!f g s. FINITE s /\ (!x. x IN s ==> f x = g x)
           ==> nproduct s f = nproduct s g`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT]);;

let NPRODUCT_EQ_GEN = prove
 (`!f g s t. FINITE s /\ s = t /\ (!x. x IN s ==> f x = g x)
             ==> nproduct s f = nproduct t g`,
  MESON_TAC[NPRODUCT_EQ]);;

let PRIME_DIVIDES_NPRODUCT = prove
 (`!p s f. prime p /\ FINITE s /\ p divides (nproduct s f)
           ==> ?x. x IN s /\ p divides (f x)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[PRIME_DIVPROD; DIVIDES_ONE; PRIME_1]);;

let NPRODUCT_CANCEL_PRIME = prove
 (`!s p m f j.
        p EXP j * nproduct (s DELETE p) (\p. p EXP (f p)) = p * m
        ==> prime p /\ FINITE s /\ (!x. x IN s ==> prime x)
            ==> ~(j = 0) /\
                p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(j = 0) ==> j = SUC(j - 1)`)) THEN
    REWRITE_TAC[SUC_SUB1; EXP; GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
    MESON_TAC[PRIME_0]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s DELETE (p:num)`; `\p. p EXP (f p)`]
                 PRIME_DIVIDES_NPRODUCT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[divides; FINITE_DELETE]; ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[PRIME_1; prime; PRIME_DIVEXP]);;

(* ------------------------------------------------------------------------- *)
(* Fundamental Theorem of Arithmetic.                                        *)
(* ------------------------------------------------------------------------- *)

let FTA = prove
 (`!n. ~(n = 0)
       ==> ?!i. FINITE {p | ~(i p = 0)} /\
                (!p. ~(i p = 0) ==> prime p) /\
                n = nproduct {p | ~(i p = 0)} (\p. p EXP (i p))`,
  ONCE_REWRITE_TAC[ARITH_RULE `n = nproduct s f <=> nproduct s f = n`] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
    SIMP_TAC[NPRODUCT_EQ_1_EQ; EXP_EQ_1; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [EXISTS_TAC `\n:num. 0` THEN
      REWRITE_TAC[SET_RULE `{p | F} = {}`; FINITE_RULES];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `q:num` THEN ASM_CASES_TAC `q = 1` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PRIME_1]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  REWRITE_TAC[divides; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `m:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[PRIME_FACTOR_LT]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\q:num. if q = p then i(q) + 1 else i(q)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `p INSERT {p:num | ~(i p = 0)}` THEN
      ASM_SIMP_TAC[SUBSET; FINITE_INSERT; IN_INSERT; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPEC `p:num` NPRODUCT_SPLITOFF_HACK) THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ADD_EQ_0; ARITH] THEN
    REWRITE_TAC[MULT_ASSOC] THEN BINOP_TAC THENL
     [ASM_CASES_TAC `(i:num->num) p = 0` THEN
      ASM_REWRITE_TAC[EXP_ADD; EXP_1; EXP; MULT_AC];
      ALL_TAC] THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN RULE_ASSUM_TAC(SIMP_RULE[]) THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; EXTENSION; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:num` NPRODUCT_SPLITOFF_HACK) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[TAUT
   `p /\ q /\ ((if p then x else y) = z) <=> p /\ q /\ x = z`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[EXP] `(if ~(x = 0) then p EXP x else 1) = p EXP x`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num->num`; `k:num->num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\i:num. if i = p then j(i) - 1 else j(i)`;
    `\i:num. if i = p then k(i) - 1 else k(i)`]) THEN
  REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP NPRODUCT_CANCEL_PRIME)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `!j k. {q | ~((if q = p then j q else k q) = 0)} DELETE p =
          {q | ~(k q = 0)} DELETE p`] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`~(j(p:num) = 0)`; `~(k(p:num) = 0)`] THEN ARITH_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | ~(j p = 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_MESON_TAC[SUB_0];
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(SYM th) THEN AP_TERM_TAC) THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[IN_DELETE; IN_ELIM_THM];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | ~(k p = 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_MESON_TAC[SUB_0];
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(SYM th) THEN AP_TERM_TAC) THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[IN_DELETE; IN_ELIM_THM]]);;
