(* ========================================================================= *)
(* Arithmetization of syntax and Tarski's theorem.                           *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* This is to fake the fact that we might really be using strings.           *)
(* ------------------------------------------------------------------------- *)

let number = new_definition
 `number(x) = 2 * (x DIV 2) + (1 - x MOD 2)`;;

let denumber = new_definition
 `denumber = number`;;

let NUMBER_DENUMBER = prove
 (`(!s. denumber(number s) = s) /\
   (!n. number(denumber n) = n)`,
  REWRITE_TAC[number; denumber] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[ARITH_RULE `x < 2 ==> (2 * y + x) DIV 2 = y`;
           MOD_MULT_ADD; MOD_LT; GSYM DIVISION; ARITH_EQ;
           ARITH_RULE `1 - m < 2`; ARITH_RULE `x < 2 ==> 1 - (1 - x) = x`]);;

let NUMBER_INJ = prove
 (`!x y. number(x) = number(y) <=> x = y`,
  MESON_TAC[NUMBER_DENUMBER]);;

let NUMBER_SURJ = prove
 (`!y. ?x. number(x) = y`,
  MESON_TAC[NUMBER_DENUMBER]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetization.                                                          *)
(* ------------------------------------------------------------------------- *)

let gterm = new_recursive_definition term_RECURSION
  `(gterm (V x) = NPAIR 0 (number x)) /\
   (gterm Z = NPAIR 1 0) /\
   (gterm (Suc t) = NPAIR 2 (gterm t)) /\
   (gterm (s ++ t) = NPAIR 3 (NPAIR (gterm s) (gterm t))) /\
   (gterm (s ** t) = NPAIR 4 (NPAIR (gterm s) (gterm t)))`;;

let gform = new_recursive_definition form_RECURSION
  `(gform False = NPAIR 0 0) /\
   (gform True = NPAIR 0 1) /\
   (gform (s === t) = NPAIR 1 (NPAIR (gterm s) (gterm t))) /\
   (gform (s << t) = NPAIR 2 (NPAIR (gterm s) (gterm t))) /\
   (gform (s <<= t) = NPAIR 3 (NPAIR (gterm s) (gterm t))) /\
   (gform (Not p) = NPAIR 4 (gform p)) /\
   (gform (p && q) = NPAIR 5 (NPAIR (gform p) (gform q))) /\
   (gform (p || q) = NPAIR 6 (NPAIR (gform p) (gform q))) /\
   (gform (p --> q) = NPAIR 7 (NPAIR (gform p) (gform q))) /\
   (gform (p <-> q) = NPAIR 8 (NPAIR (gform p) (gform q))) /\
   (gform (!! x p) = NPAIR 9 (NPAIR (number x) (gform p))) /\
   (gform (?? x p) = NPAIR 10 (NPAIR (number x) (gform p)))`;;

(* ------------------------------------------------------------------------- *)
(* Injectivity.                                                              *)
(* ------------------------------------------------------------------------- *)

let GTERM_INJ = prove
 (`!s t. (gterm s = gterm t) <=> (s = t)`,
  MATCH_MP_TAC term_INDUCT THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC;
    GEN_TAC THEN DISCH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC] THEN
  MATCH_MP_TAC term_INDUCT THEN
  ASM_REWRITE_TAC[term_DISTINCT; term_INJ; gterm;
                  NPAIR_INJ; NUMBER_INJ; ARITH_EQ]);;

let GFORM_INJ = prove
 (`!p q. (gform p = gform q) <=> (p = q)`,
  MATCH_MP_TAC form_INDUCT THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ALL_TAC;
    GEN_TAC THEN GEN_TAC;
    GEN_TAC THEN GEN_TAC;
    GEN_TAC THEN GEN_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC] THEN
  MATCH_MP_TAC form_INDUCT THEN
  ASM_REWRITE_TAC[form_DISTINCT; form_INJ; gform; NPAIR_INJ; ARITH_EQ] THEN
  REWRITE_TAC[GTERM_INJ; NUMBER_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Useful case theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let GTERM_CASES = prove
 (`((gterm u = NPAIR 0 (number x)) <=> (u = V x)) /\
   ((gterm u = NPAIR 1 0) <=> (u = Z)) /\
   ((gterm u = NPAIR 2 n) <=> (?t. (u = Suc t) /\ (gterm t = n))) /\
   ((gterm u = NPAIR 3 (NPAIR m n)) <=>
          (?s t. (u = s ++ t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gterm u = NPAIR 4 (NPAIR m n)) <=>
          (?s t. (u = s ** t) /\ (gterm s = m) /\ (gterm t = n)))`,
  STRUCT_CASES_TAC(SPEC `u:term` term_CASES) THEN
  ASM_REWRITE_TAC[gterm; NPAIR_INJ; ARITH_EQ; NUMBER_INJ;
                  term_DISTINCT; term_INJ] THEN
  MESON_TAC[]);;

let GFORM_CASES = prove
 (`((gform r = NPAIR 0 0) <=> (r = False)) /\
   ((gform r = NPAIR 0 1) <=> (r = True)) /\
   ((gform r = NPAIR 1 (NPAIR m n)) <=>
        (?s t. (r = s === t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gform r = NPAIR 2 (NPAIR m n)) <=>
        (?s t. (r = s << t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gform r = NPAIR 3 (NPAIR m n)) <=>
        (?s t. (r = s <<= t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gform r = NPAIR 4 n) = (?p. (r = Not p) /\ (gform p = n))) /\
   ((gform r = NPAIR 5 (NPAIR m n)) <=>
        (?p q. (r = p && q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 6 (NPAIR m n)) <=>
        (?p q. (r = p || q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 7 (NPAIR m n)) <=>
        (?p q. (r = p --> q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 8 (NPAIR m n)) <=>
        (?p q. (r = p <-> q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 9 (NPAIR (number x) n)) <=>
        (?p. (r = !!x p) /\ (gform p = n))) /\
   ((gform r = NPAIR 10 (NPAIR (number x) n)) <=>
        (?p. (r = ??x p) /\ (gform p = n)))`,
  STRUCT_CASES_TAC(SPEC `r:form` form_CASES) THEN
  ASM_REWRITE_TAC[gform; NPAIR_INJ; ARITH_EQ; NUMBER_INJ;
                  form_DISTINCT; form_INJ] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Definability of "godel number of numeral n".                              *)
(* ------------------------------------------------------------------------- *)

let gnumeral = new_definition
  `gnumeral m n = (gterm(numeral m) = n)`;;

let arith_gnumeral1 = new_definition
 `arith_gnumeral1 a b = formsubst ((3 |-> a) ((4 |-> b) V))
       (??0 (??1
       (V 3 === arith_pair (V 0) (V 1) &&
        V 4 === arith_pair (Suc(V 0)) (arith_pair (numeral 2) (V 1)))))`;;

let ARITH_GNUMERAL1 = prove
 (`!v a b. holds v (arith_gnumeral1 a b) <=>
                ?x y. termval v a = NPAIR x y /\
                      termval v b = NPAIR (SUC x) (NPAIR 2 y)`,
  REWRITE_TAC[arith_gnumeral1; holds; HOLDS_FORMSUBST] THEN
  REWRITE_TAC[termval; ARITH_EQ; o_THM; valmod; ARITH_PAIR; TERMVAL_NUMERAL]);;

let FV_GNUMERAL1 = prove
 (`!s t. FV(arith_gnumeral1 s t) = FVT s UNION FVT t`,
  REWRITE_TAC[arith_gnumeral1] THEN FV_TAC[FVT_PAIR; FVT_NUMERAL]);;

let arith_gnumeral1' = new_definition
 `arith_gnumeral1' x y = arith_rtc arith_gnumeral1 x y`;;

let ARITH_GNUMERAL1' = prove
 (`!v s t. holds v (arith_gnumeral1' s t) <=>
              RTC (\a b. ?x y. a = NPAIR x y /\
                               b = NPAIR (SUC x) (NPAIR 2 y))
                  (termval v s) (termval v t)`,
  REWRITE_TAC[arith_gnumeral1'] THEN MATCH_MP_TAC ARITH_RTC THEN
  REWRITE_TAC[ARITH_GNUMERAL1]);;

let FV_GNUMERAL1' = prove
 (`!s t. FV(arith_gnumeral1' s t) = FVT s UNION FVT t`,
  SIMP_TAC[arith_gnumeral1'; FV_RTC; FV_GNUMERAL1]);;

let arith_gnumeral = new_definition
 `arith_gnumeral n p =
        formsubst ((0 |-> n) ((1 |-> p) V))
            (arith_gnumeral1' (arith_pair Z (numeral 3))
                              (arith_pair (V 0) (V 1)))`;;

let ARITH_GNUMERAL = prove
 (`!v s t. holds v (arith_gnumeral s t) <=>
            gnumeral (termval v s) (termval v t)`,
  REWRITE_TAC[arith_gnumeral; holds; HOLDS_FORMSUBST;
              ARITH_GNUMERAL1'; ARITH_PAIR; TERMVAL_NUMERAL] THEN
  REWRITE_TAC[termval; ARITH_EQ; o_THM; valmod] THEN
  MP_TAC(INST
   [`(gterm o numeral)`,`fn:num->num`;
    `3`,`e:num`;
    `\a:num b:num. NPAIR 2 a`,`f:num->num->num`] PRIMREC_SIGMA) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[gterm; numeral; o_THM] THEN REWRITE_TAC[NPAIR; ARITH];
    SIMP_TAC[gnumeral; o_THM]]);;

let FV_GNUMERAL = prove
 (`!s t. FV(arith_gnumeral s t) =  FVT(s) UNION FVT(t)`,
  REWRITE_TAC[arith_gnumeral] THEN
  FV_TAC[FV_GNUMERAL1'; FVT_PAIR; FVT_NUMERAL]);;

(* ------------------------------------------------------------------------- *)
(* Diagonal substitution.                                                    *)
(* ------------------------------------------------------------------------- *)

let qdiag = new_definition
  `qdiag x q = qsubst (x,numeral(gform q)) q`;;

let arith_qdiag = new_definition
  `arith_qdiag x s t =
        formsubst ((1 |-> s) ((2 |-> t) V))
        (?? 3
           (arith_gnumeral (V 1) (V 3) &&
            arith_pair (numeral 10)  (arith_pair (numeral(number x))
                                                 (arith_pair (numeral 5)
              (arith_pair (arith_pair (numeral 1)
       (arith_pair (arith_pair (numeral 0) (numeral(number x))) (V 3)))
                   (V 1)))) ===
        V 2))`;;

let QDIAG_FV = prove
 (`FV(qdiag x q) = FV(q) DELETE x`,
  REWRITE_TAC[qdiag; FV_QSUBST; FVT_NUMERAL; UNION_EMPTY]);;

let HOLDS_QDIAG = prove
 (`!v x q. holds v (qdiag x q) = holds ((x |-> gform q) v) q`,
  SIMP_TAC[qdiag; HOLDS_QSUBST; FVT_NUMERAL; NOT_IN_EMPTY; TERMVAL_NUMERAL]);;

let ARITH_QDIAG = prove
 (`(termval v s = gform p)
   ==> (holds v (arith_qdiag x s t) <=> (termval v t = gform(qdiag x p)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[qdiag; qsubst; arith_qdiag; gform; gterm] THEN
  ASM_REWRITE_TAC[HOLDS_FORMSUBST; holds; termval; TERMVAL_NUMERAL;
   gnumeral; ARITH_GNUMERAL; ARITH_PAIR] THEN
  ASM_REWRITE_TAC[o_DEF; valmod; ARITH_EQ; termval] THEN MESON_TAC[]);;

let FV_QDIAG = prove
 (`!x s t. FV(arith_qdiag x s t) = FVT(s) UNION FVT(t)`,
  REWRITE_TAC[arith_qdiag; FORMSUBST_FV; FV; FV_GNUMERAL; FVT_PAIR;
              UNION_EMPTY; FVT_NUMERAL; FVT; TERMSUBST_FVT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[DISJ_ACI; IN_DELETE; IN_UNION; IN_SING] THEN
  REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM; GSYM CONJ_ASSOC; UNWIND_THM2; ARITH_EQ] THEN
  REWRITE_TAC[valmod; ARITH_EQ; DISJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Hence diagonalization of a predicate.                                     *)
(* ------------------------------------------------------------------------- *)

let diagonalize = new_definition
  `diagonalize x q =
        let y = VARIANT(x INSERT FV(q)) in
        ??y (arith_qdiag x (V x) (V y) && formsubst ((x |-> V y) V) q)`;;

let FV_DIAGONALIZE = prove
 (`!x q. FV(diagonalize x q) = x INSERT (FV q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diagonalize] THEN LET_TAC THEN
  REWRITE_TAC[FV; FV_QDIAG; FORMSUBST_FV; EXTENSION; IN_INSERT; IN_DELETE;
              IN_UNION; IN_ELIM_THM; FVT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `u:num` THEN
  SUBGOAL_THEN `~(y = x) /\ !z. z IN FV(q) ==> ~(y = z)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[VARIANT_FINITE; FINITE_INSERT; FV_FINITE; IN_INSERT];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:num = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u:num = y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[valmod; COND_RAND; FVT; IN_SING; COND_EXPAND] THEN
  ASM_MESON_TAC[]);;

let ARITH_DIAGONALIZE = prove
 (`(v x = gform p)
   ==> !q. holds v (diagonalize x q) <=> holds ((x |-> gform(qdiag x p)) v) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diagonalize] THEN LET_TAC THEN
  REWRITE_TAC[holds] THEN
  SUBGOAL_THEN `!a. holds ((y |-> a) v) (arith_qdiag x (V x) (V y)) <=>
                    (termval ((y |-> a) v) (V y) = gform(qdiag x p))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC ARITH_QDIAG THEN REWRITE_TAC[termval; valmod] THEN
    SUBGOAL_THEN `~(x:num = y)` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[VARIANT_FINITE; FINITE_INSERT; FV_FINITE; IN_INSERT];
    ALL_TAC] THEN
  REWRITE_TAC[HOLDS_FORMSUBST; termval; VALMOD_BASIC; UNWIND_THM2] THEN
  MATCH_MP_TAC HOLDS_VALUATION THEN
  X_GEN_TAC `u:num` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; termval; valmod] THEN
  COND_CASES_TAC THEN REWRITE_TAC[termval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[VARIANT_FINITE; FINITE_INSERT; FV_FINITE; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* And hence the fixed point.                                                *)
(* ------------------------------------------------------------------------- *)

let fixpoint = new_definition
  `fixpoint x q = qdiag x (diagonalize x q)`;;

let FV_FIXPOINT = prove
 (`!x p. FV(fixpoint x p) = FV(p) DELETE x`,
  REWRITE_TAC[fixpoint; FV_QDIAG; QDIAG_FV; FV_DIAGONALIZE;
              FVT_NUMERAL] THEN
  SET_TAC[]);;

let HOLDS_FIXPOINT = prove
 (`!x p v. holds v (fixpoint x p) <=>
           holds ((x |-> gform(fixpoint x p)) v) p`,
  REPEAT GEN_TAC THEN SIMP_TAC[fixpoint; holds; HOLDS_QDIAG] THEN
  SUBGOAL_THEN
   `((x |-> gform(diagonalize x p)) v) x = gform (diagonalize x p)`
  MP_TAC THENL [REWRITE_TAC[VALMOD_BASIC]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ARITH_DIAGONALIZE th]) THEN
  REWRITE_TAC[VALMOD_VALMOD_BASIC]);;

let HOLDS_IFF_FIXPOINT = prove
 (`!x p v. holds v
        (fixpoint x p <-> qsubst (x,numeral(gform(fixpoint x p))) p)`,
  SIMP_TAC[holds; HOLDS_FIXPOINT; HOLDS_QSUBST; FVT_NUMERAL; NOT_IN_EMPTY;
           TERMVAL_NUMERAL]);;

let CARNAP = prove
 (`!x q. ?p. (FV(p) = FV(q) DELETE x) /\
             arithtrue (p <-> qsubst (x,numeral(gform p)) q)`,
  REPEAT GEN_TAC THEN EXISTS_TAC `fixpoint x q` THEN
  REWRITE_TAC[arithtrue; HOLDS_IFF_FIXPOINT; FV_FIXPOINT]);;

(* ------------------------------------------------------------------------- *)
(* Hence Tarski's theorem on the undefinability of truth.                    *)
(* ------------------------------------------------------------------------- *)

let definable_by = new_definition
  `definable_by P s <=> ?p x. P p /\ (!v. holds v p <=> (v(x)) IN s)`;;

let definable = new_definition
  `definable s <=> ?p x. !v. holds v p <=> (v(x)) IN s`;;

let TARSKI_THEOREM = prove
 (`~(definable {gform p | arithtrue p})`,
  REWRITE_TAC[definable; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:form`; `x:num`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:num`; `Not p`] CARNAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:form` (MP_TAC o CONJUNCT2)) THEN
  SIMP_TAC[arithtrue; holds; HOLDS_QSUBST; FVT_NUMERAL; NOT_IN_EMPTY] THEN
  ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[VALMOD_BASIC; TERMVAL_NUMERAL] THEN
  REWRITE_TAC[arithtrue; GFORM_INJ] THEN MESON_TAC[]);;
