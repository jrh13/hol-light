(* ========================================================================= *)
(* First order logic based on the language of arithmetic.                    *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Syntax of terms.                                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("++",(20,"right"));;
parse_as_infix("**",(22,"right"));;

let term_INDUCT,term_RECURSION = define_type
  "term = Z
        | V num
        | Suc term
        | ++ term term
        | ** term term";;

let term_CASES = prove_cases_thm term_INDUCT;;

let term_DISTINCT = distinctness "term";;

let term_INJ = injectivity "term";;

(* ------------------------------------------------------------------------- *)
(* Syntax of formulas.                                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("===",(18,"right"));;
parse_as_infix("<<",(18,"right"));;
parse_as_infix("<<=",(18,"right"));;

parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(15,"right"));;
parse_as_infix("-->",(14,"right"));;
parse_as_infix("<->",(13,"right"));;

let form_INDUCT,form_RECURSION = define_type
  "form = False
        | True
        | === term term
        | << term term
        | <<= term term
        | Not form
        | && form form
        | || form form
        | --> form form
        | <-> form form
        | !! num form
        | ?? num form";;

let form_CASES = prove_cases_thm form_INDUCT;;

let form_DISTINCT = distinctness "form";;

let form_INJ = injectivity "form";;

(* ------------------------------------------------------------------------- *)
(* Semantics of terms and formulas in the standard model.                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|->",(22,"right"));;

let valmod = new_definition
  `(x |-> a) (v:A->B) = \y. if y = x then a else v(y)`;;

let termval = new_recursive_definition term_RECURSION
  `(termval v Z = 0) /\
   (termval v (V n) = v(n)) /\
   (termval v (Suc t) = SUC (termval v t)) /\
   (termval v (s ++ t) = termval v s + termval v t) /\
   (termval v (s ** t) = termval v s * termval v t)`;;

let holds = new_recursive_definition form_RECURSION
  `(holds v False <=> F) /\
   (holds v True <=> T) /\
   (holds v (s === t) <=> (termval v s = termval v t)) /\
   (holds v (s << t) <=> (termval v s < termval v t)) /\
   (holds v (s <<= t) <=> (termval v s <= termval v t)) /\
   (holds v (Not p) <=> ~(holds v p)) /\
   (holds v (p && q) <=> holds v p /\ holds v q) /\
   (holds v (p || q) <=> holds v p \/ holds v q) /\
   (holds v (p --> q) <=> holds v p ==> holds v q) /\
   (holds v (p <-> q) <=> (holds v p <=> holds v q)) /\
   (holds v (!! x p) <=> !a. holds ((x|->a) v) p) /\
   (holds v (?? x p) <=> ?a. holds ((x|->a) v) p)`;;

let arithtrue = new_definition
  `arithtrue p <=> !v. holds v p`;;

let VALMOD = prove
 (`!v x y a. ((x |-> y) v) a = if a = x then y else v(a)`,
  REWRITE_TAC[valmod]);;

let VALMOD_BASIC = prove
 (`!v x y. (x |-> y) v x = y`,
  REWRITE_TAC[valmod]);;

let VALMOD_VALMOD_BASIC = prove
 (`!v a b x. (x |-> a) ((x |-> b) v) = (x |-> a) v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let VALMOD_REPEAT = prove
 (`!v x. (x |-> v(x)) v = v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

let FORALL_VALMOD = prove
 (`!x. (!v a. P((x |-> a) v)) <=> (!v. P v)`,
  MESON_TAC[VALMOD_REPEAT]);;

let VALMOD_SWAP = prove
 (`!v x y a b.
     ~(x = y) ==> ((x |-> a) ((y |-> b) v) = (y |-> b) ((x |-> a) v))`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

let VALMOD_TRIVIAL = prove
 (`!v x. v x = t ==> (x |-> t) v = v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Assignment.                                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|=>",(22,"right"));;

let assign = new_definition
 `(x |=> a) = (x |-> a) V`;;

let ASSIGN = prove
 (`!x y a. (x |=> a) y = if y = x then a else V(y)`,
  REWRITE_TAC[assign; valmod]);;

let ASSIGN_TRIV = prove
 (`!x. (x |=> V x) = V`,
  REWRITE_TAC[VALMOD_REPEAT; assign]);;

(* ------------------------------------------------------------------------- *)
(* Variables in a term and free variables in a formula.                      *)
(* ------------------------------------------------------------------------- *)

let FVT = new_recursive_definition term_RECURSION
  `(FVT Z = {}) /\
   (FVT (V n) = {n}) /\
   (FVT (Suc t) = FVT t) /\
   (FVT (s ++ t) = (FVT s) UNION (FVT t)) /\
   (FVT (s ** t) = (FVT s) UNION (FVT t))`;;

let FV = new_recursive_definition form_RECURSION
  `(FV False = {}) /\
   (FV True = {}) /\
   (FV (s === t) = (FVT s) UNION (FVT t)) /\
   (FV (s << t) = (FVT s) UNION (FVT t)) /\
   (FV (s <<= t) = (FVT s) UNION (FVT t)) /\
   (FV (Not p) = FV p) /\
   (FV (p && q) = (FV p) UNION (FV q)) /\
   (FV (p || q) = (FV p) UNION (FV q)) /\
   (FV (p --> q) = (FV p) UNION (FV q)) /\
   (FV (p <-> q) = (FV p) UNION (FV q)) /\
   (FV (!!x p) = (FV p) DELETE x) /\
   (FV (??x p) = (FV p) DELETE x)`;;

let FVT_FINITE = prove
 (`!t. FINITE(FVT t)`,
  MATCH_MP_TAC term_INDUCT THEN
  SIMP_TAC[FVT; FINITE_RULES; FINITE_INSERT; FINITE_UNION]);;

let FV_FINITE = prove
 (`!p. FINITE(FV p)`,
  MATCH_MP_TAC form_INDUCT THEN
  SIMP_TAC[FV; FVT_FINITE; FINITE_RULES; FINITE_DELETE; FINITE_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Logical axioms.                                                           *)
(* ------------------------------------------------------------------------- *)

let axiom_RULES,axiom_INDUCT,axiom_CASES = new_inductive_definition
 `(!p q. axiom(p --> (q --> p))) /\
  (!p q r. axiom((p --> q --> r) --> (p --> q) --> (p --> r))) /\
  (!p. axiom(((p --> False) --> False) --> p)) /\
  (!x p q. axiom((!!x (p --> q)) --> (!!x p) --> (!!x q))) /\
  (!x p. ~(x IN FV p) ==> axiom(p --> !!x p)) /\
  (!x t. ~(x IN FVT t) ==> axiom(??x (V x === t))) /\
  (!t. axiom(t === t)) /\
  (!s t. axiom((s === t) --> (Suc s === Suc t))) /\
  (!s t u v. axiom(s === t --> u === v --> s ++ u === t ++ v)) /\
  (!s t u v. axiom(s === t --> u === v --> s ** u === t ** v)) /\
  (!s t u v. axiom(s === t --> u === v --> s === u --> t === v)) /\
  (!s t u v. axiom(s === t --> u === v --> s << u --> t << v)) /\
  (!s t u v. axiom(s === t --> u === v --> s <<= u --> t <<= v)) /\
  (!p q. axiom((p <-> q) --> p --> q)) /\
  (!p q. axiom((p <-> q) --> q --> p)) /\
  (!p q. axiom((p --> q) --> (q --> p) --> (p <-> q))) /\
  axiom(True <-> (False --> False)) /\
  (!p. axiom(Not p <-> (p --> False))) /\
  (!p q. axiom((p && q) <-> (p --> q --> False) --> False)) /\
  (!p q. axiom((p || q) <-> Not(Not p && Not q))) /\
  (!x p. axiom((??x p) <-> Not(!!x (Not p))))`;;

(* ------------------------------------------------------------------------- *)
(* Deducibility from additional set of nonlogical axioms.                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|--",(11,"right"));;

let proves_RULES,proves_INDUCT,proves_CASES = new_inductive_definition
  `(!p. axiom p \/ p IN A ==> A |-- p) /\
   (!p q. A |-- (p --> q) /\ A |-- p ==> A |-- q) /\
   (!p x. A |-- p ==> A |-- (!!x p))`;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let TERMVAL_VALUATION = prove
 (`!t v v'. (!x. x IN FVT(t) ==> (v'(x) = v(x)))
            ==> (termval v' t = termval v t)`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval; FVT; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let HOLDS_VALUATION = prove
 (`!p v v'.
      (!x. x IN (FV p) ==> (v'(x) = v(x)))
      ==> (holds v' p <=> holds v p)`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[FV; holds; IN_UNION; IN_DELETE] THEN
  SIMP_TAC[TERMVAL_VALUATION] THEN
  REWRITE_TAC[valmod] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let TERMVAL_VALMOD_OTHER = prove
 (`!v x a t. ~(x IN FVT t) ==> (termval ((x |-> a) v) t = termval v t)`,
  MESON_TAC[TERMVAL_VALUATION; VALMOD]);;

let HOLDS_VALMOD_OTHER = prove
 (`!v x a p. ~(x IN FV p) ==> (holds ((x |-> a) v) p <=> holds v p)`,
  MESON_TAC[HOLDS_VALUATION; VALMOD]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness.                                                       *)
(* ------------------------------------------------------------------------- *)

let AXIOMS_TRUE = prove
 (`!p. axiom p ==> arithtrue p`,
  MATCH_MP_TAC axiom_INDUCT THEN
  REWRITE_TAC[arithtrue] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[holds] THENL
   [CONV_TAC TAUT;
    CONV_TAC TAUT;
    SIMP_TAC[];
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN
    REWRITE_TAC[valmod] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `termval v t` THEN
    REWRITE_TAC[termval; valmod] THEN
    MATCH_MP_TAC TERMVAL_VALUATION THEN
    GEN_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    SIMP_TAC[termval];
    CONV_TAC TAUT;
    CONV_TAC TAUT;
    CONV_TAC TAUT;
    MESON_TAC[]]);;

let THEOREMS_TRUE = prove
 (`!A p. (!q. q IN A ==> arithtrue q) /\ A |-- p ==> arithtrue p`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC proves_INDUCT THEN
  ASM_SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[IN; AXIOMS_TRUE] THEN
  SIMP_TAC[holds; arithtrue]);;

(* ------------------------------------------------------------------------- *)
(* Variant variables for use in renaming substitution.                       *)
(* ------------------------------------------------------------------------- *)

let MAX_SYM = prove
 (`!x y. MAX x y = MAX y x`,
  ARITH_TAC);;

let MAX_ASSOC = prove
 (`!x y z. MAX x (MAX y z) = MAX (MAX x y) z`,
  ARITH_TAC);;

let SETMAX = new_definition
  `SETMAX s = ITSET MAX s 0`;;

let VARIANT = new_definition
  `VARIANT s = SETMAX s + 1`;;

let SETMAX_LEMMA = prove
 (`(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = if x IN s then SETMAX s
                                  else MAX x (SETMAX s)))`,
  REWRITE_TAC[SETMAX] THEN MATCH_MP_TAC FINITE_RECURSION THEN
  REWRITE_TAC[MAX] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`x:num <= s`; `y:num <= s`; `x:num <= y`; `y <= x`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_CASES; LE_TRANS; LE_ANTISYM]);;

let SETMAX_MEMBER = prove
 (`!s. FINITE s ==> !x. x IN s ==> x <= SETMAX s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC [SETMAX_LEMMA] THEN
  ASM_REWRITE_TAC[MAX] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  ASM_MESON_TAC[LE_CASES; LE_TRANS]);;

let SETMAX_THM = prove
 (`(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = MAX x (SETMAX s)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SETMAX_LEMMA] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MAX] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[SETMAX_MEMBER]);;

let SETMAX_UNION = prove
 (`!s t. FINITE(s UNION t)
         ==> (SETMAX(s UNION t) = MAX (SETMAX s) (SETMAX t))`,
  let lemma = prove(`(x INSERT s) UNION t = x INSERT (s UNION t)`,SET_TAC[]) in
  SUBGOAL_THEN `!t. FINITE(t) ==> !s. FINITE(s) ==>
                        (SETMAX(s UNION t) = MAX (SETMAX s) (SETMAX t))`
   (fun th -> MESON_TAC[th; FINITE_UNION]) THEN
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; SETMAX_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAX; LE_0]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lemma] THEN
  ASM_SIMP_TAC [SETMAX_THM; FINITE_UNION] THEN
  REWRITE_TAC[MAX_ASSOC]);;

let VARIANT_FINITE = prove
 (`!s:num->bool. FINITE(s) ==> ~(VARIANT(s) IN s)`,
  REWRITE_TAC[VARIANT] THEN
  MESON_TAC[SETMAX_MEMBER; ARITH_RULE `~(x + 1 <= x)`]);;

let VARIANT_THM = prove
 (`!p. ~(VARIANT(FV p) IN FV(p))`,
  GEN_TAC THEN MATCH_MP_TAC VARIANT_FINITE THEN REWRITE_TAC[FV_FINITE]);;

let NOT_IN_VARIANT = prove
 (`!s t. FINITE s /\ t SUBSET s ==> ~(VARIANT(s) IN t)`,
  MESON_TAC[SUBSET; VARIANT_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* Substitution within terms.                                                *)
(* ------------------------------------------------------------------------- *)

let termsubst = new_recursive_definition term_RECURSION
 `(termsubst v Z = Z) /\
  (!x. termsubst v (V x) = v(x)) /\
  (!t. termsubst v (Suc t) = Suc(termsubst v t)) /\
  (!s t. termsubst v (s ++ t) = termsubst v s ++ termsubst v t) /\
  (!s t. termsubst v (s ** t) = termsubst v s ** termsubst v t)`;;

let TERMVAL_TERMSUBST = prove
 (`!v i t. termval v (termsubst i t) = termval (termval v o i) t`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN SIMP_TAC[termval; termsubst; o_THM]);;

let TERMSUBST_TERMSUBST = prove
 (`!i j t. termsubst j (termsubst i t) = termsubst (termsubst j o i) t`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN SIMP_TAC[termval; termsubst; o_THM]);;

let TERMSUBST_TRIV = prove
 (`!t. termsubst V t = t`,
  MATCH_MP_TAC term_INDUCT THEN SIMP_TAC[termsubst]);;

let TERMSUBST_EQ = prove
 (`!t v v'. (!x. x IN (FVT t) ==> (v'(x) = v(x)))
            ==> (termsubst v' t = termsubst v t)`,
  MATCH_MP_TAC term_INDUCT THEN
  SIMP_TAC[termsubst; FVT; IN_SING; IN_UNION] THEN MESON_TAC[]);;

let TERMSUBST_FVT = prove
 (`!t i. FVT(termsubst i t) = {x | ?y. y IN FVT(t) /\ x IN FVT(i y)}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[FVT; termsubst] THEN
  REWRITE_TAC[IN_UNION; IN_SING; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let TERMSUBST_ASSIGN = prove
 (`!x s t. ~(x IN FVT t) ==> (termsubst (x |=> s) t = t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM TERMSUBST_TRIV] THEN
  MATCH_MP_TAC TERMSUBST_EQ THEN
  REWRITE_TAC[ASSIGN] THEN ASM_MESON_TAC[]);;

let TERMSUBST_TRIVIAL = prove
 (`!v t. (!x. x IN FVT t ==> v x = V x) ==> termsubst v t = t`,
  MESON_TAC[TERMSUBST_EQ; TERMSUBST_TRIV]);;

(* ------------------------------------------------------------------------- *)
(* Formula substitution --- somewhat less trivial.                           *)
(* ------------------------------------------------------------------------- *)

let formsubst = new_recursive_definition form_RECURSION
  `(formsubst v False = False) /\
   (formsubst v True = True) /\
   (formsubst v (s === t) = termsubst v s === termsubst v t) /\
   (formsubst v (s << t) = termsubst v s << termsubst v t) /\
   (formsubst v (s <<= t) = termsubst v s <<= termsubst v t) /\
   (formsubst v (Not p) = Not(formsubst v p)) /\
   (formsubst v (p && q) = formsubst v p && formsubst v q) /\
   (formsubst v (p || q) = formsubst v p || formsubst v q) /\
   (formsubst v (p --> q) = formsubst v p --> formsubst v q) /\
   (formsubst v (p <-> q) = formsubst v p <-> formsubst v q) /\
   (formsubst v (!!x q) =
        let z = if ?y. y IN FV(!!x q) /\ x IN FVT(v(y))
                then VARIANT(FV(formsubst ((x |-> V x) v) q)) else x in
        !!z (formsubst ((x |-> V(z)) v) q)) /\
   (formsubst v (??x q) =
        let z = if ?y. y IN FV(??x q) /\ x IN FVT(v(y))
                then VARIANT(FV(formsubst ((x |-> V x) v) q)) else x in
        ??z (formsubst ((x |-> V(z)) v) q))`;;

let FORMSUBST_PROPERTIES = prove
 (`!p. (!i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}) /\
       (!i v. holds v (formsubst i p) = holds (termval v o i) p)`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[FV; holds; formsubst; TERMSUBST_FVT; IN_ELIM_THM; NOT_IN_EMPTY;
              IN_UNION; TERMVAL_TERMSUBST] THEN
  REPEAT(CONJ_TAC THENL [MESON_TAC[];ALL_TAC]) THEN CONJ_TAC THEN
  (MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN STRIP_TAC THEN
   REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `i:num->term` THEN
   LET_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `~(?y. y IN (FV(p) DELETE x) /\ z IN FVT(i y))`
   ASSUME_TAC THENL
    [EXPAND_TAC "z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPEC `formsubst ((x |-> V x) i) p` VARIANT_THM) THEN
     ASM_REWRITE_TAC[valmod; IN_DELETE; CONTRAPOS_THM] THEN
     MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
     ALL_TAC] THEN
   CONJ_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[FV; IN_DELETE; holds] THENL
    [REWRITE_TAC[LEFT_AND_EXISTS_THM; valmod] THEN AP_TERM_TAC THEN
     ABS_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[FVT; IN_SING; IN_DELETE];
     AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
     GEN_TAC THEN REWRITE_TAC[valmod; o_DEF] THEN COND_CASES_TAC THEN
     ASM_REWRITE_TAC[termval] THEN DISCH_TAC THEN
     MATCH_MP_TAC TERMVAL_VALUATION THEN GEN_TAC THEN
     REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[IN_DELETE]]));;

let FORMSUBST_FV = prove
 (`!p i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}`,
  REWRITE_TAC[FORMSUBST_PROPERTIES]);;

let HOLDS_FORMSUBST = prove
 (`!p i v. holds v (formsubst i p) <=> holds (termval v o i) p`,
  REWRITE_TAC[FORMSUBST_PROPERTIES]);;

let FORMSUBST_EQ = prove
 (`!p i j. (!x. x IN FV(p) ==> (i(x) = j(x)))
           ==> (formsubst i p = formsubst j p)`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[FV; formsubst; IN_UNION; IN_DELETE] THEN
  SIMP_TAC[] THEN REWRITE_TAC[CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [MESON_TAC[TERMSUBST_EQ]; ALL_TAC] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN
  (DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num->term`; `j:num->term`] THEN
   DISCH_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; form_INJ] THEN
   MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN SIMP_TAC[] THEN
   CONJ_TAC THENL
    [ALL_TAC;
     DISCH_THEN(K ALL_TAC) THEN FIRST_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[valmod] THEN ASM_SIMP_TAC[]] THEN
   AP_THM_TAC THEN BINOP_TAC THENL
    [ASM_MESON_TAC[];
     AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[valmod] THEN ASM_MESON_TAC[]]));;

let FORMSUBST_TRIV = prove
 (`!p. formsubst V p = p`,
  MATCH_MP_TAC form_INDUCT THEN
  SIMP_TAC[formsubst; TERMSUBST_TRIV] THEN
  REWRITE_TAC[FVT; IN_SING; FV; IN_DELETE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; VALMOD_REPEAT] THEN
  ASM_MESON_TAC[]);;

let FORMSUBST_TRIVIAL = prove
 (`!v p. (!x. x IN FV(p) ==> v x = V x) ==> formsubst v p = p`,
  MESON_TAC[FORMSUBST_EQ; FORMSUBST_TRIV]);;

(* ------------------------------------------------------------------------- *)
(* Predicate ensuring that a substitution will not cause variable renaming.  *)
(* ------------------------------------------------------------------------- *)

let safe_for = new_definition
 `safe_for x v <=> !y. x IN FVT(v y) ==> y = x`;;

let SAFE_FOR_V = prove
 (`!x. safe_for x V`,
  SIMP_TAC[safe_for; FVT; IN_SING]);;

let SAFE_FOR_VALMOD = prove
 (`!v x y t. safe_for x v /\ (x IN FVT t ==> y = x)
             ==> safe_for x ((y |-> t) v)`,
  REWRITE_TAC[safe_for; VALMOD] THEN MESON_TAC[]);;

let SAFE_FOR_ASSIGN = prove
 (`!x y t. safe_for x (y |=> t) <=> x IN FVT t ==> y = x`,
  REWRITE_TAC[safe_for; ASSIGN] THEN MESON_TAC[FVT; IN_SING]);;

let FORMSUBST_SAFE_FOR = prove
 (`(!v x p. safe_for x v
            ==> formsubst v (!! x p) = !!x (formsubst ((x |-> V x) v) p)) /\
   (!v x p. safe_for x v
            ==> formsubst v (?? x p) = ??x (formsubst ((x |-> V x) v) p))`,
  REWRITE_TAC[safe_for; formsubst; LET_DEF; LET_END_DEF; FV] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Quasi-substitution.                                                       *)
(* ------------------------------------------------------------------------- *)

let qsubst = new_definition
 `qsubst (x,t) p = ??x (V x === t && p)`;;

let FV_QSUBST = prove
 (`!x n p. FV(qsubst (x,t) p) = (FV(p) UNION FVT(t)) DELETE x`,
  REWRITE_TAC[qsubst; FV; FVT] THEN SET_TAC[]);;

let HOLDS_QSUBST = prove
 (`!v t p v. ~(x IN FVT(t))
             ==> (holds v (qsubst (x,t) p) <=>
                  holds ((x |-> termval v t) v) p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!v z. termval ((x |-> z) v) t = termval v t` ASSUME_TAC THENL
   [REWRITE_TAC[valmod] THEN ASM_MESON_TAC[TERMVAL_VALUATION];
    ASM_REWRITE_TAC[holds; qsubst; termval; VALMOD_BASIC; UNWIND_THM2]]);;

(* ------------------------------------------------------------------------- *)
(* The numeral mapping.                                                      *)
(* ------------------------------------------------------------------------- *)

let numeral = new_recursive_definition num_RECURSION
  `(numeral 0 = Z) /\
   (!n. numeral (SUC n) = Suc(numeral n))`;;

let TERMVAL_NUMERAL = prove
 (`!v n. termval v (numeral n) = n`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[termval;numeral]);;

let FVT_NUMERAL = prove
 (`!n. FVT(numeral n) = {}`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[FVT; numeral]);;

(* ------------------------------------------------------------------------- *)
(* Closed-ness.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed = new_definition
  `closed p <=> (FV p = {})`;;
