(* ========================================================================= *)
(* Formalization of semantics and basic model theory of first order logic.   *)
(* ========================================================================= *)

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  check((=) s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;

let LIST_UNION = new_recursive_definition list_RECURSION
  `(LIST_UNION [] = {}) /\
   (LIST_UNION (CONS h t) = h UNION (LIST_UNION t))`;;

let LIST_UNION_FINITE = prove
 (`!l. ALL FINITE l ==> FINITE(LIST_UNION l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_UNION; FINITE_RULES] THEN
  REWRITE_TAC[FINITE_UNION; ALL] THEN ASM_MESON_TAC[]);;

let IN_LIST_UNION = prove
 (`!x l. x IN (LIST_UNION l) <=> EX (\s. x IN s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_UNION; EX; NOT_IN_EMPTY; IN_UNION]);;

let LIST_UNION_APPEND = prove
 (`!l1 l2. LIST_UNION(APPEND l1 l2) = (LIST_UNION l1) UNION (LIST_UNION l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LIST_UNION; APPEND; UNION_EMPTY; GSYM UNION_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Nested type of terms.                                                     *)
(* ------------------------------------------------------------------------- *)

let term_raw_INDUCT,term_raw_RECURSION = define_type
  "term = V num | Fn num (term list)";;

(* ------------------------------------------------------------------------- *)
(* Manually extract "nested" version of induction and recursion.             *)
(* One day, this will be automated; it's really pretty trivial.              *)
(* ------------------------------------------------------------------------- *)

let term_INDUCT = prove
 (`!P. (!v. P(V v)) /\ (!s l. ALL P l ==> P(Fn s l)) ==> !t. P t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:term->bool`; `ALL(P:term->bool)`] term_raw_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

let term_RECURSION = prove
 (`!f h. ?fn:term->Z.
        (!v. fn(V v) = f v) /\
        (!s l. fn(Fn s l) = h s l (MAP fn l))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->Z`; `h:num->(term)list->(Z)list->Z`;
                 `[]:(Z)list`; `\(x:term) (y:term list) (z:Z) (w:Z list).
                                CONS z w`] term_raw_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mf:(term)list->(Z)list`
        (X_CHOOSE_THEN `fn:term ->Z` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `fn:term ->Z` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN X_GEN_TAC `l:term list` THEN AP_TERM_TAC THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

(* ------------------------------------------------------------------------- *)
(* General Skolemizing hack to allow fixed initial parameters in nested      *)
(* recursive defs. Note that (prima facie) variable ones aren't justified.   *)
(* ------------------------------------------------------------------------- *)

let new_nested_recursive_definition ax tm =
  let expat = lhand(snd(strip_forall(hd(conjuncts tm)))) in
  let ev,allargs = strip_comb expat in
  let pargs = butlast allargs in
  let tm' = mk_exists(ev,list_mk_forall(pargs,tm)) in
  let rawprover = prove_recursive_functions_exist ax in
  let eth = prove(tm',
                  REWRITE_TAC[GSYM SKOLEM_THM] THEN
                  REPEAT GEN_TAC THEN
                  W(ACCEPT_TAC o rawprover o snd o dest_exists o snd)) in
  SPECL pargs (new_specification [fst(dest_var ev)] eth);;

(* ------------------------------------------------------------------------- *)
(* Standard consequences.                                                    *)
(* ------------------------------------------------------------------------- *)

let term_INJ = prove_constructors_injective term_RECURSION;;

let term_DISTINCT = prove_constructors_distinct term_RECURSION;;

let term_CASES = prove_cases_thm term_INDUCT;;

(* ------------------------------------------------------------------------- *)
(* Definition of formulas.                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(13,"right"));;

let form_INDUCTION,form_RECURSION =
  define_type "form = False
                    | Atom num (term list)
                    | --> form form
                    | !! num form";;

let form_INJ = prove_constructors_injective form_RECURSION;;

let form_DISTINCT = prove_constructors_distinct form_RECURSION;;

let form_CASES = prove_cases_thm form_INDUCTION;;

(* ------------------------------------------------------------------------- *)
(* Definitions of other connectives.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(14,"right"));;
parse_as_infix("<->",(12,"right"));;

let Not_DEF = new_definition
  `Not p = p --> False`;;

let True_DEF = new_definition
  `True = Not False`;;

let Or_DEF = new_definition
  `p || q = (p --> q) --> q`;;

let And_DEF = new_definition
  `p && q = Not (Not p || Not q)`;;

let Iff_DEF = new_definition
  `(p <-> q) = (p --> q) && (q --> p)`;;

let Exists_DEF = new_definition
  `?? x p = Not(!!x (Not p))`;;

(* ------------------------------------------------------------------------- *)
(* The language of a term, formula and set of formulas.                      *)
(* ------------------------------------------------------------------------- *)

let functions_term = new_recursive_definition term_RECURSION
  `(!v. functions_term (V v) = {}) /\
   (!f l. functions_term (Fn f l) =
        (f,LENGTH l) INSERT (LIST_UNION (MAP functions_term l)))`;;

let functions_form = new_recursive_definition form_RECURSION
  `(functions_form False = {}) /\
   (functions_form (Atom a l) = LIST_UNION (MAP functions_term l)) /\
   (functions_form (p --> q) = (functions_form p) UNION (functions_form q)) /\
   (functions_form (!! x p) = functions_form p)`;;

let predicates_form = new_recursive_definition form_RECURSION
  `(predicates_form False = {}) /\
   (predicates_form (Atom a l) = {(a,LENGTH l)}) /\
   (predicates_form (p --> q) =
        (predicates_form p) UNION (predicates_form q)) /\
   (predicates_form (!! x p) = predicates_form p)`;;

let functions = new_definition
  `functions fms = UNIONS {functions_form f | f IN fms}`;;

let predicates = new_definition
  `predicates fms = UNIONS {predicates_form f | f IN fms}`;;

let language = new_definition
  `language fms = functions fms, predicates fms`;;

let FUNCTIONS_SING = prove
 (`functions {p} = functions_form p`,
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY;
              functions; IN_ELIM_THM; IN_UNIONS] THEN
  MESON_TAC[]);;

let LANGUAGE_1 = prove
 (`language {p} = functions_form p,predicates_form p`,
  REWRITE_TAC[language; functions; predicates; PAIR_EQ] THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Selecting the bits of an interpretation: domain, functions and relations. *)
(* ------------------------------------------------------------------------- *)

let Dom_DEF = new_definition
  `Dom (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = D`;;

let Fun_DEF = new_definition
  `Fun (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = Funs`;;

let Pred_DEF = new_definition
  `Pred (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = Preds`;;

let MODEL_EQ = prove
 (`(M = M') <=> (Dom M = Dom M') /\ (Fun M = Fun M') /\ (Pred M = Pred M')`,
  let detrip = prove(`p = FST(p),FST(SND p),SND(SND p)`,REWRITE_TAC[]) in
  ONCE_REWRITE_TAC[detrip] THEN PURE_REWRITE_TAC[PAIR_EQ; Dom_DEF; Fun_DEF; Pred_DEF] THEN
  REWRITE_TAC[]);;

let MODEL_DECOMP = prove
 (`M = Dom M,Fun M,Pred M`,
  REWRITE_TAC[MODEL_EQ] THEN REWRITE_TAC[Dom_DEF; Fun_DEF; Pred_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Free variables and bound variables.                                       *)
(* ------------------------------------------------------------------------- *)

let FVT = new_recursive_definition term_RECURSION
  `(!x. FVT (V x) = {x}) /\
   (!f l. FVT (Fn f l) = LIST_UNION (MAP FVT l))`;;

let FV = new_recursive_definition form_RECURSION
  `(FV False = {}) /\
   (!a l. FV (Atom a l) = LIST_UNION (MAP FVT l)) /\
   (!p q. FV (p --> q) = FV p UNION FV q) /\
   (!x p. FV (!! x p) = FV p DELETE x)`;;

let BV = new_recursive_definition form_RECURSION
  `(BV False = {}) /\
   (!a l. BV (Atom a l) = {}) /\
   (!p q. BV (p --> q) = BV p UNION BV q) /\
   (!x p. BV (!! x p) = x INSERT BV p)`;;

let FVT_FINITE = prove
 (`!t. FINITE(FVT t)`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[FVT; FINITE_RULES; FINITE_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_UNION_FINITE THEN
  ASM_REWRITE_TAC[ALL_MAP; o_DEF]);;

let FV_FINITE = prove
 (`!p. FINITE(FV p)`,
  MATCH_MP_TAC form_INDUCTION THEN
  ASM_REWRITE_TAC[FV; FINITE_RULES; FINITE_UNION; FINITE_DELETE] THEN
  GEN_TAC THEN MATCH_MP_TAC LIST_UNION_FINITE THEN
  REWRITE_TAC[ALL_MAP; FVT_FINITE; o_DEF; ALL_T]);;

let BV_FINITE = prove
 (`!p. FINITE(BV p)`,
  MATCH_MP_TAC form_INDUCTION THEN
  ASM_REWRITE_TAC[BV; FINITE_RULES; FINITE_UNION; FINITE_INSERT]);;

let FV_EXISTS = prove
 (`FV(??x p) = FV(p) DELETE x`,
  REWRITE_TAC[Exists_DEF; Not_DEF; FV] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Modifier for a valuation.                                                 *)
(* ------------------------------------------------------------------------- *)

let valmod = new_definition
  `valmod (x,a) v = \y. if y = x then a else v y`;;

let VALMOD_CLAUSES = prove
 (`(!v a k. valmod (k,a) v k = a) /\
   (!v a k x. ~(x = k) ==> (valmod (k,a) v x = v x))`,
  REWRITE_TAC[valmod] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let VALMOD_TRIV = prove
 (`!v x. valmod (x,v x) v = v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let VALMOD_VALMOD = prove
 (`!v a x b. valmod (x,a) (valmod (x,b) v) = valmod (x,a) v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valmod] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* Acceptability of a valuation.                                             *)
(* ------------------------------------------------------------------------- *)

let valuation = new_definition
  `valuation(M) v <=> !x:num. v(x) IN Dom(M)`;;

let VALUATION_VALMOD = prove
 (`!M a v. valuation(M) v /\ a IN Dom(M) ==> valuation(M) (valmod (x,a) v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valuation; valmod] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let VALUATION_IS_VALMOD = prove
 (`!v x. valmod(x,v x) v = v`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interpretation of terms and formulas w.r.t. interpretation and valuation. *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("satisfies",(10,"right"));;

let termval = new_nested_recursive_definition term_RECURSION
  `(!x. termval M v (V x) = v(x)) /\
   (!f l. termval M v (Fn f l) = Fun(M) f (MAP (termval M v) l))`;;

let holds = new_recursive_definition form_RECURSION
  `(holds M v False <=> F) /\
   (!a l. holds M v (Atom a l) <=> Pred(M) a (MAP (termval M v) l)) /\
   (!p q. holds M v (p --> q) <=> holds M v p ==> holds M v q) /\
   (!x p. holds M v (!! x p) <=>
                !a. a IN Dom(M) ==> holds M (valmod (x,a) v) p)`;;

let hold = new_definition
  `hold M v fms <=> !p. p IN fms ==> holds M v p`;;

let satisfies = new_definition
  `M satisfies fms <=> !v p. valuation(M) v /\ p IN fms ==> holds M v p`;;

let SATISFIES_1 = prove
 (`M satisfies {p} <=> !v. valuation(M) v ==> holds M v p`,
  REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Clauses for derived constructs.                                           *)
(* ------------------------------------------------------------------------- *)

let HOLDS = prove
 (`(holds M v False <=> F) /\
   (holds M v True <=> T) /\
   (!a l. holds M v (Atom a l) <=> Pred(M) a (MAP (termval M v) l)) /\
   (!p. holds M v (Not p) <=> ~(holds M v p)) /\
   (!p q. holds M v (p || q) <=> holds M v p \/ holds M v q) /\
   (!p q. holds M v (p && q) <=> holds M v p /\ holds M v q) /\
   (!p q. holds M v (p --> q) <=> holds M v p ==> holds M v q) /\
   (!p q. holds M v (p <-> q) <=> (holds M v p = holds M v q)) /\
   (!x p. holds M v (!! x p) <=>
                !a. a IN Dom(M) ==> holds M (valmod (x,a) v) p) /\
   (!x p. holds M v (?? x p) <=>
                ?a. a IN Dom(M) /\ holds M (valmod (x,a) v) p)`,
  REWRITE_TAC[Not_DEF; True_DEF; Or_DEF; And_DEF; Iff_DEF; Exists_DEF; holds] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Prove that only values given to free variables by the valuation matter.   *)
(* ------------------------------------------------------------------------- *)

let TERMVAL_VALUATION = prove
 (`!M t (v:num->A) v'.
        (!x. x IN (FVT t) ==> (v'(x) = v(x)))
             ==> (termval M v' t = termval M v t)`,
  let lemma = prove
   (`!l t x. x IN FVT t /\ MEM t l
             ==>  x IN LIST_UNION (MAP FVT l)`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; IN_UNION; MEM] THEN
    ASM_MESON_TAC[]) in
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[FVT; termval] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[ALL; LIST_UNION; MAP; IN_UNION] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CONS_11] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MAP_EQ THEN MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC `\t. !(v:num->A) v'.
                (!x. x IN FVT t ==> (v' x = v x))
                ==> (termval M v' t :A = termval M v t)` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[lemma]]]);;

let HOLDS_VALUATION = prove
 (`!M p (v:num->A) v'.
      (!x. x IN (FV p) ==> (v'(x) = v(x)))
             ==> (holds M v' p <=> holds M v p)`,
  GEN_TAC THEN MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[FV; HOLDS; IN_UNION; IN_DELETE] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `l:term list` THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`l:term list`,`l:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; IN_UNION] THEN
    ASM_MESON_TAC[TERMVAL_VALUATION];
    MESON_TAC[];
    X_GEN_TAC `p:num` THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num = p` THEN
    ASM_REWRITE_TAC[valmod] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Note that these are delicate given the fixed type of interpretations.     *)
(* ------------------------------------------------------------------------- *)

let satisfiable = new_definition
  `satisfiable (U:A->bool) fms <=>
   ?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        ~(Dom M = {}) /\ M satisfies fms`;;

let valid = new_definition
  `valid (U:A->bool) fms <=>
   !M:(A->bool)#(num->A list->A)#(num->A list->bool).
        M satisfies fms`;;

let entails = new_definition
  `entails (U:A->bool) A p <=>
   !(M:(A->bool)#(num->A list->A)#(num->A list->bool)) v.
        hold M v A ==> holds M v p`;;

let equivalent = new_definition
  `equivalent (U:A->bool) p q <=>
   !(M:(A->bool)#(num->A list->A)#(num->A list->bool)) v.
        holds M v p <=> holds M v q`;;

(* ------------------------------------------------------------------------- *)
(* Quality of being an interpretation for a language.                        *)
(* ------------------------------------------------------------------------- *)

let interpretation = new_definition
  `interpretation (fns:(num#num)->bool,preds:(num#num)->bool) M <=>
     !f l. (f,LENGTH l) IN fns /\ ALL (\x. x IN Dom(M)) l
           ==> (Fun(M) f l) IN Dom(M)`;;


let INTERPRETATION_TERMVAL = prove
 (`!any:num#num->bool M v t.
        interpretation (functions_term t,any) M /\
        valuation(M) v
        ==> termval M v t IN Dom(M)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[interpretation] THEN
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[termval] THEN CONJ_TAC THENL
   [REWRITE_TAC[valuation] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LENGTH_MAP; functions_term; IN_INSERT] THEN
    REWRITE_TAC[ALL_MAP] THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC ALL_IMP THEN
    FIRST_ASSUM(EXISTS_TAC o lhand o concl) THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[functions_term] THEN
    REWRITE_TAC[IN_INSERT] THEN DISJ2_TAC THEN
    UNDISCH_TAC `MEM (x:term) l` THEN
    SPEC_TAC(`l:term list`,`l:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
    REWRITE_TAC[LIST_UNION; MAP; IN_UNION] THEN ASM_MESON_TAC[]]);;

let INTERPRETATION_SUBLANGUAGE = prove
 (`!M funs1 funs2 preds1 preds2.
        funs2 SUBSET funs1
        ==> interpretation (funs1,preds1) M
            ==> interpretation (funs2,preds2) M`,
  GEN_TAC THEN REWRITE_TAC[interpretation; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Substitution in terms.                                                    *)
(* ------------------------------------------------------------------------- *)

let termsubst = new_nested_recursive_definition term_RECURSION
 `(!x. termsubst v (V x) = v(x)) /\
  (!f l. termsubst v (Fn f l) = Fn f (MAP (termsubst v) l))`;;

let TERMSUBST_TERMVAL = prove
 (`!M. (Fun(M) = Fn) ==> !v t. termsubst v t = termval M v t`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  ASM_REWRITE_TAC[termsubst; termval] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[]);;

let TERMVAL_TRIV = prove
 (`!M. (Fun(M) = Fn) ==> !t. termval M V t = t`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  ASM_REWRITE_TAC[termval] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC[]);;

let TERMVAL_TERMSUBST = prove
 (`!M v i t. termval M v (termsubst i t) = termval M (termval M v o i) t`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[termval; termsubst; o_THM] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
  MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[o_THM]);;

let TERMSUBST_TERMSUBST = prove
 (`!i j t. termsubst j (termsubst i t) = termsubst (termsubst j o i) t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termsubst; o_THM] THEN REWRITE_TAC[GSYM MAP_o] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[o_THM]);;

let TERMSUBST_TRIV = prove
 (`!t. termsubst V t = t`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[termsubst] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC[]);;

let TERMSUBST_VALUATION = prove
 (`!t v v'. (!x. x IN (FVT t) ==> (v'(x) = v(x)))
            ==> (termsubst v' t = termsubst v t)`,
  MP_TAC(ISPEC `Dom(a,Fn,b),Fn,Pred(a,Fn,b)` TERMSUBST_TERMVAL) THEN
  REWRITE_TAC[Fun_DEF] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[TERMVAL_VALUATION]);;

let TERMSUBST_FVT = prove
 (`!t i. FVT(termsubst i t) = {x | ?y. y IN FVT(t) /\ x IN FVT(i y)}`,
  let lemma1 = prove
   (`{x | ?y. y IN (s UNION t) /\ P x y} =
     {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}`,
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]) in
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[FVT; termsubst] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY; EXTENSION] THEN
    MESON_TAC[];
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION] THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[ALL] THEN STRIP_TAC THEN X_GEN_TAC `i:num->term` THEN
    REWRITE_TAC[lemma1] THEN BINOP_TAC THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`i:num->term`,`i:num->term`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Choice of a new variable.                                                 *)
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

(* ------------------------------------------------------------------------- *)
(* Substitution in formulas.                                                 *)
(* ------------------------------------------------------------------------- *)

let formsubst = new_recursive_definition form_RECURSION
  `(formsubst v False = False) /\
   (formsubst v (Atom p l) = Atom p (MAP (termsubst v) l)) /\
   (formsubst v (q --> r) = (formsubst v q --> formsubst v r)) /\
   (formsubst v (!!x q) =
        let v' = valmod (x,V x) v in
        let z = if ?y. y IN FV(!!x q) /\ x IN FVT(v'(y))
                then VARIANT(FV(formsubst v' q)) else x in
        !!z (formsubst (valmod (x,V(z)) v) q))`;;

let FORMSUBST_TRIV = prove
 (`!p. formsubst V p = p`,
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[formsubst] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
    REWRITE_TAC[TERMSUBST_TRIV; ALL_T];
    REWRITE_TAC[VALMOD_TRIV; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; FV; IN_DELETE] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; EQ_SYM_EQ; TAUT `~(~p /\ p)`] THEN
    ASM_REWRITE_TAC[VALMOD_TRIV]]);;

let FORMSUBST_VALUATION = prove
 (`!p v v'. (!x. x IN (FV p) ==> (v'(x) = v(x)))
            ==> (formsubst v' p = formsubst v p)`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[FV; formsubst; IN_UNION; IN_DELETE] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `l:term list` THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`l:term list`,`l:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION; IN_UNION] THEN
    ASM_MESON_TAC[TERMSUBST_VALUATION];
    MESON_TAC[];
    X_GEN_TAC `p:num` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN
     `(?y. (y IN FV a1 /\ ~(y = p)) /\ p IN FVT (valmod (p,V p) v' y)) <=>
      (?y. (y IN FV a1 /\ ~(y = p)) /\ p IN FVT (valmod (p,V p) v y))`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN ABS_TAC THEN
      MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
      DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
      REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VALMOD_VALMOD] THENL
     [BINOP_TAC THENL
       [AP_TERM_TAC THEN AP_TERM_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        GEN_TAC THEN REWRITE_TAC[valmod] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN
        X_GEN_TAC `x:num` THEN DISCH_TAC THEN
        REWRITE_TAC[valmod] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        X_GEN_TAC `y:num` THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[]];
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      GEN_TAC THEN REWRITE_TAC[valmod] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]]]);;

let FORMSUBST_FV = prove
 (`!p i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}`,
  let lemma1 = prove
   (`{x | ?y. y IN (s UNION t) /\ P x y} =
     {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}`,
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]) in
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[formsubst; FV] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM];
    REWRITE_TAC[GSYM MAP_o; o_DEF; TERMSUBST_FVT] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_UNION; MAP] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNION] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNION] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[FV; VALMOD_VALMOD] THENL
     [MP_TAC(SPEC `formsubst (valmod (a0,V a0) i) a1` VARIANT_THM) THEN
      ABBREV_TAC `a0' = VARIANT (FV (formsubst (valmod (a0,V a0) i) a1))`;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
    REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; IN_DELETE] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Important lemmas about substitution and renaming.                         *)
(* ------------------------------------------------------------------------- *)

let HOLDS_FORMSUBST = prove
 (`!p i v. holds M (v:num->A) (formsubst i p) <=>
           holds M (termval M v o i) p`,
  MATCH_MP_TAC form_INDUCTION THEN
  ASM_REWRITE_TAC[formsubst; holds] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[o_THM; TERMVAL_TERMSUBST; ALL_T]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; HOLDS] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a ==> b <=> a ==> c)`) THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[VALMOD_VALMOD] THEN
  MATCH_MP_TAC HOLDS_VALUATION THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; valmod] THEN
  (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM valmod] THENL
   [REWRITE_TAC[termval; valmod]; ALL_TAC]) THEN
  MATCH_MP_TAC TERMVAL_VALUATION THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[valmod] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN `~(y IN FV(formsubst (valmod (a0,V a0) i) a1))`
    MP_TAC THENL [EXPAND_TAC "y" THEN REWRITE_TAC[VARIANT_THM]; ALL_TAC] THEN
    REWRITE_TAC[FORMSUBST_FV] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[FV; IN_DELETE] THEN
    REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]);;

let HOLDS_FORMSUBST1 = prove
 (`!x t p v. holds M (v:num->A) (formsubst (valmod (x,t) V) p) <=>
             holds M (valmod (x,termval M v t) v) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOLDS_FORMSUBST] THEN
  MATCH_MP_TAC HOLDS_VALUATION THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  REWRITE_TAC[valmod; o_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[termval]);;

let HOLDS_RENAME = prove
 (`!x y p v. holds M (v:num->A) (formsubst (valmod (x,V y) V) p) <=>
             holds M (valmod (x,v(y)) v) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOLDS_FORMSUBST1] THEN
  MATCH_MP_TAC HOLDS_VALUATION THEN REWRITE_TAC[termval]);;

let HOLDS_ALPHA_FORALL = prove
 (`!x y p v. ~(y IN FV(!!x p))
             ==> (holds M v (!!y (formsubst (valmod (x,V y) V) p)) <=>
                  holds M (v:num->A) (!!x p))`,
  REWRITE_TAC[FV; IN_DELETE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOLDS; HOLDS_FORMSUBST] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC HOLDS_VALUATION THEN
  GEN_TAC THEN REWRITE_TAC[valmod; termval; o_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[valmod; termval] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HOLDS_ALPHA_EXISTS = prove
 (`!x y p v. ~(y IN FV(??x p))
              ==> (holds M v (??y (formsubst (valmod (x,V y) V) p)) <=>
                   holds M (v:num->A) (??x p))`,
  REWRITE_TAC[FV; Exists_DEF; Not_DEF; IN_DELETE; UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOLDS; HOLDS_FORMSUBST] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
  GEN_TAC THEN REWRITE_TAC[valmod; termval; o_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[valmod; termval] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FORMSUBST_RENAME = prove
 (`!p x y. FV(formsubst (valmod (x,V y) V) p) DELETE y =
           (FV(p) DELETE x) DELETE y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FORMSUBST_FV] THEN
  REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM] THEN
  GEN_TAC THEN REWRITE_TAC[valmod] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for the logical language.                              *)
(* ------------------------------------------------------------------------- *)

let TERMSUBST_FUNCTIONS_TERM = prove
 (`!t i. functions_term(termsubst i t) =
         functions_term t UNION
         {x | ?y. y IN FVT(t) /\ x IN functions_term(i y)}`,
  let lemma1 = prove
   (`{x | ?y. y IN (s UNION t) /\ P x y} =
     {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}`,
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]) in
  let lemma2 = prove
   (`(s = a UNION c) /\ (t = b UNION d)
     ==> (s UNION t = (a UNION b) UNION (c UNION d))`,
    SET_TAC[]) in
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[functions_term; termsubst; FVT] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY; EXTENSION] THEN
    MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN SUBGOAL_THEN
   `!l.
     ALL
     (\t. !i. functions_term (termsubst i t) =
              functions_term t UNION
              {x | ?y. y IN FVT t /\ x IN functions_term (i y)}) l
     ==> (!i. LIST_UNION (MAP functions_term (MAP (termsubst i) l)) =
              LIST_UNION (MAP functions_term l) UNION
              {x | ?y. y IN LIST_UNION (MAP FVT l) /\
                       x IN functions_term (i y)})`
  ASSUME_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN(fun th -> REWRITE_TAC[th])) THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNION; LENGTH_MAP; DISJ_ACI]] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION] THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INSERT; SUBSET;
                  IN_ELIM_THM; IN_UNION];
      ALL_TAC] THEN
  REWRITE_TAC[ALL] THEN STRIP_TAC THEN X_GEN_TAC `i:num->term` THEN
  REWRITE_TAC[lemma1; LENGTH; LENGTH_MAP] THEN
  MATCH_MP_TAC lemma2 THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  SPEC_TAC(`i:num->term`,`i:num->term`) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let FORMSUBST_FUNCTIONS_FORM = prove
 (`!p i. functions_form(formsubst i p) =
         functions_form p UNION
         {x | ?y. y IN FV(p) /\ x IN functions_term(i y)}`,
  let lemma1 = prove
   (`{x | ?y. y IN (s UNION t) /\ P x y} =
     {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}`,
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]) in
  let lemma2 = prove
   (`(a UNION b) UNION (c UNION d) = (a UNION c) UNION (b UNION d)`,
    REWRITE_TAC[EXTENSION; IN_UNION; DISJ_ACI]) in
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[formsubst; functions_form; FV] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; NOT_IN_EMPTY; IN_ELIM_THM];
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_UNION] THENL
     [REWRITE_TAC[NOT_IN_EMPTY; EXTENSION; IN_UNION; IN_ELIM_THM];
      ALL_TAC] THEN
    X_GEN_TAC `i:num->term` THEN REWRITE_TAC[lemma1] THEN
    ONCE_REWRITE_TAC[lemma2] THEN
    BINOP_TAC THEN ASM_REWRITE_TAC[TERMSUBST_FUNCTIONS_TERM];
    REWRITE_TAC[lemma1] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[lemma2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[functions_form; LET_DEF; LET_END_DEF; VALMOD_VALMOD] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[valmod] THEN
  CONV_TAC(DEPTH_CONV COND_ELIM_CONV) THEN
  REWRITE_TAC[functions_term; NOT_IN_EMPTY; IN_INSERT; IN_DELETE] THEN
  REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `y:num = a0` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let FORMSUBST_FUNCTIONS_FORM_1 = prove
 (`!x t p. x IN FV(p)
           ==> (functions_form(formsubst (valmod (x,t) V) p) =
                functions_form p UNION functions_term t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[FORMSUBST_FUNCTIONS_FORM] THEN
  REWRITE_TAC[valmod] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  REWRITE_TAC[functions_term; NOT_IN_EMPTY] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* And of course we never change the predicates.                             *)
(* ------------------------------------------------------------------------- *)

let FORMSUBST_PREDICATES = prove
 (`!p i. predicates_form(formsubst i p) = predicates_form p`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[predicates_form; formsubst; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Special case of renaming preserves language.                              *)
(* ------------------------------------------------------------------------- *)

let FORMSUBST_LANGUAGE_RENAME = prove
 (`language {(formsubst (valmod (x,V y) V) p)} = language {p}`,
  REWRITE_TAC[LANGUAGE_1; FORMSUBST_PREDICATES; FORMSUBST_FUNCTIONS_FORM] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  REWRITE_TAC[valmod] THEN CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  REWRITE_TAC[functions_term; NOT_IN_EMPTY] THEN
  REWRITE_TAC[TAUT `~p /\ p <=> F`]);;

(* ------------------------------------------------------------------------- *)
(* Invariance under change of language.                                      *)
(* ------------------------------------------------------------------------- *)

let TERMVAL_FUNCTIONS = prove
 (`!M t. (!f zs. (f,LENGTH zs) IN functions_term t
                 ==> (Fun(M) f zs = Fun(M') f zs))
         ==> !v:num->A. termval M v t = termval M' v t`,
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[termval; functions_term] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP (termval M (v:num->A)) l =
                 MAP (termval M' v) l`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN
    MATCH_MP_TAC ALL_IMP THEN
    FIRST_ASSUM(EXISTS_TAC o lhand o concl) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> SPEC_TAC(`v:num->A`,`v:num->A`) THEN
                         MATCH_MP_TAC th) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INSERT] THEN DISJ2_TAC THEN
    UNDISCH_TAC `MEM (x:term) l` THEN
    SPEC_TAC(`l:term list`,`l:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
    REWRITE_TAC[LIST_UNION; MAP; IN_UNION] THEN ASM_MESON_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
    REWRITE_TAC[LENGTH_MAP]]);;

let HOLDS_FUNCTIONS = prove
 (`!M M' p. (Dom(M) = Dom(M')) /\
            (!P zs. Pred(M) P zs = Pred(M') P zs) /\
            (!f zs. (f,LENGTH zs) IN functions_form p
                    ==> (Fun(M) f zs = Fun(M') f zs))
            ==> !v:num->A. holds M v p <=> holds M' v p`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[holds] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN
    UNDISCH_TAC `!f zs.
           f,LENGTH zs IN functions_form (Atom a0 a1)
           ==> (Fun M f zs :A = Fun M' f zs)` THEN
    REWRITE_TAC[functions_form] THEN
    SPEC_TAC(`a1:term list`,`a1:term list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_UNION; MAP; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_UNION; CONS_11] THEN REPEAT STRIP_TAC THENL
     [SPEC_TAC(`v:num->A`,`v:num->A`) THEN MATCH_MP_TAC TERMVAL_FUNCTIONS THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    BINOP_TAC THEN SPEC_TAC(`v:num->A`,`v:num->A`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[functions_form; IN_UNION];
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC(`valmod (a0,a) (v:num->A)`,`v:num->A`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[functions_form]]);;

let HOLDS_PREDICATES = prove
 (`!M M' p. (Dom(M) = Dom(M')) /\
            (!f zs. Fun(M) f zs = Fun(M') f zs) /\
            (!P zs. (P,LENGTH zs) IN predicates_form p
                    ==> (Pred(M) P zs = Pred(M') P zs))
            ==> !v:num->A. holds M v p <=> holds M' v p`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[holds] THEN
  REWRITE_TAC[predicates_form; IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `MAP (termval M' (v:num->A)) a1 = MAP (termval M (v:num->A)) a1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN
      SUBGOAL_THEN `!x. termval M' (v:num->A) x = termval M (v:num->A) x`
       (fun th -> REWRITE_TAC[th; ALL_T]) THEN
      GEN_TAC THEN SPEC_TAC(`v:num->A`,`v:num->A`) THEN
      MATCH_MP_TAC TERMVAL_FUNCTIONS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LENGTH_MAP];
    ASM_MESON_TAC[];
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC(`valmod (a0,a) (v:num->A)`,`v:num->A`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Triviality of universal closure.                                          *)
(* ------------------------------------------------------------------------- *)

let HOLDS_UCLOSE = prove
 (`!M x p. (!v:num->A. valuation(M) v ==> holds M v (!!x p)) <=>
           (Dom M = EMPTY) \/ !v. valuation(M) v ==> holds M v p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[holds] THEN
  ASM_CASES_TAC `Dom(M):A->bool = EMPTY` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[VALUATION_IS_VALMOD; VALUATION_VALMOD; valuation]);;

(* ------------------------------------------------------------------------- *)
(* Sort of trivial upward LS theorem without equality.                       *)
(* ------------------------------------------------------------------------- *)

let MODEL_DUPLICATE = prove
 (`!M fns preds D.
        interpretation(fns,preds) M /\
        (Dom(M) SUBSET D) /\
        ~(Dom(M):A->bool = {})
        ==> ?M'. interpretation(fns,preds) M' /\
                 (Dom(M') = D) /\
                 !s. functions s SUBSET fns /\
                     predicates s SUBSET preds
                     ==> (M' satisfies s <=> M satisfies s)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `i = \x. if x IN Dom(M) then x else @z:A. z IN Dom(M)` THEN
  ABBREV_TAC `M' = (D:A->bool,
                   (\f args. Fun(M) f (MAP (i:A->A) args)),
                   (\P args. Pred(M) P (MAP i args)))` THEN
  W(EXISTS_TAC o fst o dest_exists o snd) THEN
  SUBGOAL_THEN `!x. (i:A->A) x IN Dom(M)` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN EXPAND_TAC "i" THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SELECT_CONV THEN
    UNDISCH_TAC `~(Dom(M) = ({}:A->bool))` THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a /\ c) ==> a /\ b /\ c`) THEN
  CONJ_TAC THENL [EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF]; ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [interpretation]) THEN
    ASM_REWRITE_TAC[interpretation] THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Fun_DEF] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
    UNDISCH_TAC `ALL (\x:A. x IN D) l` THEN
    REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
    ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. functions_term t SUBSET fns
        ==> !v:num->A. (i:A->A) (termval M' v t) = termval M (i o v) t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[termval; o_THM] THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Fun_DEF] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MAP_o] THEN
    MAP_EVERY X_GEN_TAC [`P:num`; `args:term list`] THEN
    REWRITE_TAC[functions_term; SUBSET; IN_LIST_UNION; IN_INSERT] THEN
    REWRITE_TAC[GSYM EX_MEM; GSYM ALL_MEM] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:num,LENGTH(args:term list)) IN fns` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!t. MEM t args ==> functions_term t SUBSET fns`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[MEM_MAP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!t. MEM t args
          ==> !v:num->A. (i:A->A) (termval M' v t) = termval M (i o v) t`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `v:num->A` THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `Fun M P (MAP ((i:A->A) o termval M' (v:num->A)) args)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [SYM th]) THEN
      SUBGOAL_THEN `Fun M P (MAP ((i:A->A) o termval M' (v:num->A)) args) IN
                    Dom(M)`
        (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [interpretation]) THEN
      ASM_REWRITE_TAC[LENGTH_MAP] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      REWRITE_TAC[MEM_MAP; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. functions_form p SUBSET fns
        ==> !v:num->A. holds M' v p <=> holds M ((i:A->A) o v) p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[holds; functions_form] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_LIST_UNION; GSYM EX_MEM; MEM_MAP] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "M'" THEN REWRITE_TAC[Pred_DEF] THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
      MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[SUBSET; IN_UNION] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:num->A` THEN
    SUBGOAL_THEN
     `!a. i o valmod (x,a) (v:num->A) = valmod (x,i(a)) ((i:A->A) o v)`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
      REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:A. x IN Dom(M) ==> (i x = x)` MP_TAC THENL
     [EXPAND_TAC "i" THEN SIMP_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `s:form->bool` THEN STRIP_TAC THEN REWRITE_TAC[satisfies] THEN
  REWRITE_TAC[valuation] THEN EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `p:form` THEN
  ASM_CASES_TAC `p:form IN s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `functions_form p SUBSET fns` ASSUME_TAC THENL
   [UNDISCH_TAC `functions s SUBSET fns` THEN
    REWRITE_TAC[functions; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `v:num->A` THENL
   [DISCH_TAC THEN SUBGOAL_THEN `v:num->A = i o v` SUBST1_TAC THENL
     [EXPAND_TAC "i" THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[SUBSET];
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_THM]]);;
