(* ========================================================================= *)
(* Set-theoretic hierarchy for modelling HOL inside itself.                  *)
(* ========================================================================= *)

let INJ_LEMMA = prove
 (`(!x y. (f x = f y) ==> (x = y)) <=> (!x y. (f x = f y) <=> (x = y))`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful to have a niceish "function update" notation.                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("|->",(12,"right"));;

let valmod = new_definition
  `(x |-> a) (v:A->B) = \y. if y = x then a else v(y)`;;

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
 (`!x. (!v a. P((x |-> a) v)) = (!v. P v)`,
  MESON_TAC[VALMOD_REPEAT]);;

let VALMOD_SWAP = prove
 (`!v x y a b.
     ~(x = y) ==> ((x |-> a) ((y |-> b) v) = (y |-> b) ((x |-> a) v))`,
  REWRITE_TAC[valmod; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A dummy finite type inadequately modelling ":ind".                        *)
(* ------------------------------------------------------------------------- *)

let ind_model_tybij =
  let th = prove(`?x. x IN @s:num->bool. ~(s = {}) /\ FINITE s`,
                 MESON_TAC[MEMBER_NOT_EMPTY; IN_SING; FINITE_RULES]) in
  new_type_definition "ind_model" ("mk_ind","dest_ind") th;;

(* ------------------------------------------------------------------------- *)
(* Introduce a type whose universe is "inaccessible" starting from           *)
(* "ind_model". Since "ind_model" is finite, we can just use any             *)
(* infinite set. In order to make "ind_model" infinite, we would need        *)
(* a new axiom. In order to keep things generic we try to deduce             *)
(* everything from this one uniform "axiom". Note that even in the           *)
(* infinite case, this can still be a small set in ZF terms, not a real      *)
(* inaccessible cardinal.                                                    *)
(* ------------------------------------------------------------------------- *)

(****** Here's what we'd do in the infinite case

 new_type("I",0);;

 let I_AXIOM = new_axiom
  `UNIV:ind_model->bool <_c UNIV:I->bool /\
   (!s:A->bool. s <_c UNIV:I->bool ==> {t | t SUBSET s} <_c UNIV:I->bool)`;;

 *******)

let inacc_tybij =
  let th = prove
   (`?x:num. x IN UNIV`,REWRITE_TAC[IN_UNIV]) in
  new_type_definition "I" ("mk_I","dest_I") th;;

let I_AXIOM = prove
 (`UNIV:ind_model->bool <_c UNIV:I->bool /\
   (!s:A->bool. s <_c UNIV:I->bool ==> {t | t SUBSET s} <_c UNIV:I->bool)`,
  let lemma = prove
   (`!s. s <_c UNIV:I->bool <=> FINITE s`,
    GEN_TAC THEN REWRITE_TAC[FINITE_CARD_LT] THEN
    MATCH_MP_TAC CARD_LT_CONG THEN REWRITE_TAC[CARD_EQ_REFL] THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM; le_c; IN_UNIV] THEN
    MESON_TAC[inacc_tybij; IN_UNIV]) in
  REWRITE_TAC[lemma; FINITE_POWERSET] THEN
  SUBGOAL_THEN `UNIV = IMAGE mk_ind (@s. ~(s = {}) /\ FINITE s)`
  SUBST1_TAC THENL
   [MESON_TAC[EXTENSION; IN_IMAGE; IN_UNIV; ind_model_tybij];
    MESON_TAC[FINITE_IMAGE; NOT_INSERT_EMPTY; FINITE_RULES]]);;

(* ------------------------------------------------------------------------- *)
(* I is infinite and therefore admits an injective pairing.                  *)
(* ------------------------------------------------------------------------- *)

let I_INFINITE = prove
 (`INFINITE(UNIV:I->bool)`,
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{n | n < CARD(UNIV:I->bool) - 1}` (CONJUNCT2 I_AXIOM)) THEN
  ASM_SIMP_TAC[CARD_LT_CARD; FINITE_NUMSEG_LT; FINITE_POWERSET] THEN
  SIMP_TAC[CARD_NUMSEG_LT; CARD_POWERSET; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `~(CARD(UNIV:I->bool) = 0)` MP_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; GSYM MEMBER_NOT_EMPTY; IN_UNIV]; ALL_TAC] THEN
  SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 < n`; NOT_LT] THEN
  MATCH_MP_TAC(ARITH_RULE `a - 1 < b ==> ~(a = 0) ==> a <= b`) THEN
  SPEC_TAC(`CARD(UNIV:I->bool) - 1`,`n:num`) THEN POP_ASSUM(K ALL_TAC) THEN
  INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN POP_ASSUM MP_TAC THEN
  ARITH_TAC);;

let I_PAIR_EXISTS = prove
 (`?f:I#I->I. !x y. (f x = f y) ==> (x = y)`,
  SUBGOAL_THEN `UNIV:I#I->bool <=_c UNIV:I->bool` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[le_c; IN_UNIV]] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  MP_TAC(MATCH_MP CARD_SQUARE_INFINITE I_INFINITE) THEN
  MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; mul_c; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[PAIR]);;

let I_PAIR = REWRITE_RULE[INJ_LEMMA]
 (new_specification ["I_PAIR"] I_PAIR_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* It also admits injections from "bool" and "ind_model".                    *)
(* ------------------------------------------------------------------------- *)

let CARD_BOOL_LT_I = prove
 (`UNIV:bool->bool <_c UNIV:I->bool`,
  REWRITE_TAC[GSYM CARD_NOT_LE] THEN
  DISCH_TAC THEN MP_TAC I_INFINITE THEN REWRITE_TAC[INFINITE] THEN
  SUBGOAL_THEN `FINITE(UNIV:bool->bool)`
   (fun th -> ASM_MESON_TAC[th; CARD_LE_FINITE]) THEN
  SUBGOAL_THEN `UNIV:bool->bool = {F,T}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT] THEN MESON_TAC[];
    SIMP_TAC[FINITE_RULES]]);;

let I_BOOL_EXISTS = prove
 (`?f:bool->I. !x y. (f x = f y) ==> (x = y)`,
  MP_TAC(MATCH_MP CARD_LT_IMP_LE CARD_BOOL_LT_I) THEN
  SIMP_TAC[lt_c; le_c; IN_UNIV]);;

let I_BOOL = REWRITE_RULE[INJ_LEMMA]
 (new_specification ["I_BOOL"] I_BOOL_EXISTS);;

let I_IND_EXISTS = prove
 (`?f:ind_model->I. !x y. (f x = f y) ==> (x = y)`,
  MP_TAC(CONJUNCT1 I_AXIOM) THEN SIMP_TAC[lt_c; le_c; IN_UNIV]);;

let I_IND = REWRITE_RULE[INJ_LEMMA]
 (new_specification ["I_IND"] I_IND_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* And the injection from powerset of any accessible set.                    *)
(* ------------------------------------------------------------------------- *)

let I_SET_EXISTS = prove
 (`!s:I->bool.
        s <_c UNIV:I->bool
        ==> ?f:(I->bool)->I. !t u. t SUBSET s /\ u SUBSET s /\ (f t = f u)
                                   ==> (t = u)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP(CONJUNCT2 I_AXIOM)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CARD_LT_IMP_LE) THEN
  REWRITE_TAC[le_c; IN_UNIV; IN_ELIM_THM]);;

let I_SET = new_specification ["I_SET"]
 (REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] I_SET_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Define a type for "levels" of our set theory.                             *)
(* ------------------------------------------------------------------------- *)

let setlevel_INDUCT,setlevel_RECURSION = define_type
 "setlevel = Ur_bool
           | Ur_ind
           | Powerset setlevel
           | Cartprod setlevel setlevel";;

let setlevel_DISTINCT = distinctness "setlevel";;
let setlevel_INJ = injectivity "setlevel";;

(* ------------------------------------------------------------------------- *)
(* Now define a subset of I corresponding to each.                           *)
(* ------------------------------------------------------------------------- *)

let setlevel = new_recursive_definition setlevel_RECURSION
 `(setlevel Ur_bool = IMAGE I_BOOL UNIV) /\
  (setlevel Ur_ind = IMAGE I_IND UNIV) /\
  (setlevel (Cartprod l1 l2) =
           IMAGE I_PAIR {x,y | x IN setlevel l1 /\ y IN setlevel l2}) /\
  (setlevel (Powerset l) = IMAGE (I_SET (setlevel l))
                                 {s | s SUBSET (setlevel l)})`;;

(* ------------------------------------------------------------------------- *)
(* Show they all satisfy the cardinal limits.                                *)
(* ------------------------------------------------------------------------- *)

let SETLEVEL_CARD = prove
 (`!l. setlevel l <_c UNIV:I->bool`,
  MATCH_MP_TAC setlevel_INDUCT THEN REWRITE_TAC[setlevel] THEN
  REPEAT CONJ_TAC THENL
   [TRANS_TAC CARD_LET_TRANS `UNIV:bool->bool` THEN
    REWRITE_TAC[CARD_LE_IMAGE; CARD_BOOL_LT_I];
    TRANS_TAC CARD_LET_TRANS `UNIV:ind_model->bool` THEN
    REWRITE_TAC[CARD_LE_IMAGE; I_AXIOM];
    X_GEN_TAC `l:setlevel` THEN DISCH_TAC THEN
    TRANS_TAC CARD_LET_TRANS `{s | s SUBSET (setlevel l)}` THEN
    ASM_SIMP_TAC[I_AXIOM; CARD_LE_IMAGE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l1:setlevel`; `l2:setlevel`] THEN STRIP_TAC THEN
  TRANS_TAC CARD_LET_TRANS `setlevel l1 *_c setlevel l2` THEN
  ASM_SIMP_TAC[CARD_MUL_LT_INFINITE; I_INFINITE; GSYM mul_c; CARD_LE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Hence the injectivity of the mapping from powerset.                       *)
(* ------------------------------------------------------------------------- *)

let I_SET_SETLEVEL = prove
 (`!l s t. s SUBSET setlevel l /\ t SUBSET setlevel l /\
          (I_SET (setlevel l) s = I_SET (setlevel l) t)
          ==> (s = t)`,
  MESON_TAC[SETLEVEL_CARD; I_SET]);;

(* ------------------------------------------------------------------------- *)
(* Now our universe of sets and (ur)elements.                                *)
(* ------------------------------------------------------------------------- *)

let universe = new_definition
 `universe = {(t,x) | x IN setlevel t}`;;

(* ------------------------------------------------------------------------- *)
(* Define an actual type V.                                                  *)
(*                                                                           *)
(* This satisfies a suitable number of the ZF axioms. It isn't extensional   *)
(* but we could then construct a quotient structure if desired. Anyway it's  *)
(* only empty sets that aren't. A more significant difference is that we     *)
(* have urelements and the hierarchy levels are all distinct rather than     *)
(* being cumulative.                                                         *)
(* ------------------------------------------------------------------------- *)

let v_tybij =
  let th = prove
   (`?a. a IN universe`,
    EXISTS_TAC `Ur_bool,I_BOOL T` THEN
    REWRITE_TAC[universe; IN_ELIM_THM; PAIR_EQ; CONJ_ASSOC;
                ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1;
                setlevel; IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[]) in
  new_type_definition "V" ("mk_V","dest_V") th;;

let V_TYBIJ = prove
 (`!l e. e IN setlevel l <=> (dest_V(mk_V(l,e)) = (l,e))`,
  REWRITE_TAC[GSYM(CONJUNCT2 v_tybij)] THEN
  REWRITE_TAC[IN_ELIM_THM; universe; FORALL_PAIR_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Drop a level; test if something is a set.                                 *)
(* ------------------------------------------------------------------------- *)

let droplevel = new_recursive_definition setlevel_RECURSION
  `droplevel(Powerset l) = l`;;

let isasetlevel = new_recursive_definition setlevel_RECURSION
 `(isasetlevel Ur_bool = F) /\
  (isasetlevel Ur_ind = F) /\
  (isasetlevel (Cartprod l1 l2) = F) /\
  (isasetlevel (Powerset l) = T)`;;

(* ------------------------------------------------------------------------- *)
(* Define some useful inversions.                                            *)
(* ------------------------------------------------------------------------- *)

let level = new_definition
 `level x = FST(dest_V x)`;;

let element = new_definition
 `element x = SND(dest_V x)`;;

let ELEMENT_IN_LEVEL = prove
 (`!x. (element x) IN setlevel(level x)`,
  REWRITE_TAC[V_TYBIJ; v_tybij; level; element; PAIR]);;

let SET = prove
 (`!x. mk_V(level x,element x) = x`,
 REWRITE_TAC[level; element; PAIR; v_tybij]);;

let set = new_definition
 `set x = @s. s SUBSET (setlevel(droplevel(level x))) /\
              (I_SET (setlevel(droplevel(level x))) s = element x)`;;

let isaset = new_definition
 `isaset x <=> ?l. level x = Powerset l`;;

(* ------------------------------------------------------------------------- *)
(* Now all the critical relations.                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<:",(11,"right"));;

let inset = new_definition
 `x <: s <=> (level s = Powerset(level x)) /\ (element x) IN (set s)`;;

parse_as_infix("<=:",(12,"right"));;

let subset_def = new_definition
 `s <=: t <=> (level s = level t) /\ !x. x <: s ==> x <: t`;;

(* ------------------------------------------------------------------------- *)
(* If something has members, it's a set.                                     *)
(* ------------------------------------------------------------------------- *)

let MEMBERS_ISASET = prove
 (`!x s. x <: s ==> isaset s`,
  REWRITE_TAC[inset; isaset] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Each level is nonempty.                                                   *)
(* ------------------------------------------------------------------------- *)

let LEVEL_NONEMPTY = prove
 (`!l. ?x. x IN setlevel l`,
  REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
  MATCH_MP_TAC setlevel_INDUCT THEN REWRITE_TAC[setlevel; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIV] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; IN_ELIM_THM] THEN
  MESON_TAC[EMPTY_SUBSET]);;

let LEVEL_SET_EXISTS = prove
 (`!l. ?s. level s = l`,
  MP_TAC LEVEL_NONEMPTY THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[level] THEN MESON_TAC[FST; PAIR; V_TYBIJ]);;

(* ------------------------------------------------------------------------- *)
(* Empty sets (or non-sets, of course) exist at all set levels.              *)
(* ------------------------------------------------------------------------- *)

let MK_V_CLAUSES = prove
 (`e IN setlevel l
   ==> (level(mk_V(l,e)) = l) /\ (element(mk_V(l,e)) = e)`,
  REWRITE_TAC[level; element; PAIR; GSYM PAIR_EQ; V_TYBIJ]);;

let MK_V_SET = prove
 (`s SUBSET setlevel l
   ==> (set(mk_V(Powerset l,I_SET (setlevel l) s)) = s) /\
       (level(mk_V(Powerset l,I_SET (setlevel l) s)) = Powerset l) /\
       (element(mk_V(Powerset l,I_SET (setlevel l) s)) = I_SET (setlevel l) s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `I_SET (setlevel l) s IN setlevel(Powerset l)` ASSUME_TAC THENL
   [REWRITE_TAC[setlevel; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MK_V_CLAUSES; set] THEN
  SUBGOAL_THEN `I_SET (setlevel l) s IN setlevel(Powerset l)` ASSUME_TAC THENL
   [REWRITE_TAC[setlevel; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MK_V_CLAUSES; droplevel] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[I_SET_SETLEVEL]);;

let EMPTY_EXISTS = prove
 (`!l. ?s. (level s = l) /\ !x. ~(x <: s)`,
  MATCH_MP_TAC setlevel_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC; ALL_TAC;
    X_GEN_TAC `l:setlevel` THEN DISCH_THEN(K ALL_TAC) THEN
    EXISTS_TAC `mk_V(Powerset l,I_SET (setlevel l) {})` THEN
    SIMP_TAC[inset; MK_V_CLAUSES; MK_V_SET; EMPTY_SUBSET; NOT_IN_EMPTY];
    ALL_TAC] THEN
 MESON_TAC[LEVEL_SET_EXISTS; MEMBERS_ISASET; isaset;
           setlevel_DISTINCT]);;

let EMPTY_SET = new_specification ["emptyset"]
        (REWRITE_RULE[SKOLEM_THM] EMPTY_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Comprehension principle, with no change of levels.                        *)
(* ------------------------------------------------------------------------- *)

let COMPREHENSION_EXISTS = prove
 (`!s p. ?t. (level t = level s) /\ !x. x <: t <=> x <: s /\ p x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `isaset s` THENL
   [ALL_TAC; ASM_MESON_TAC[MEMBERS_ISASET]] THEN
  POP_ASSUM(X_CHOOSE_TAC `l:setlevel` o REWRITE_RULE[isaset]) THEN
  MP_TAC(SPEC `s:V` ELEMENT_IN_LEVEL) THEN
  ASM_REWRITE_TAC[setlevel; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:I->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mk_V(Powerset l,
                   I_SET(setlevel l)
                   {i | i IN u /\ p(mk_V(l,i))})` THEN
  SUBGOAL_THEN `{i | i IN u /\ p (mk_V (l,i))} SUBSET (setlevel l)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MK_V_SET; inset] THEN X_GEN_TAC `x:V` THEN
  REWRITE_TAC[setlevel_INJ] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[SET; MK_V_SET]);;

parse_as_infix("suchthat",(21,"left"));;

let SUCHTHAT = new_specification ["suchthat"]
     (REWRITE_RULE[SKOLEM_THM] COMPREHENSION_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Each setlevel exists as a set.                                            *)
(* ------------------------------------------------------------------------- *)

let SETLEVEL_EXISTS = prove
 (`!l. ?s. (level s = Powerset l) /\
           !x. x <: s <=> (level x = l) /\ element(x) IN setlevel l`,
  GEN_TAC THEN
  EXISTS_TAC `mk_V(Powerset l,I_SET (setlevel l) (setlevel l))` THEN
  SIMP_TAC[MK_V_SET; SUBSET_REFL; inset; setlevel_INJ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Conversely, set(s) belongs in the appropriate level.                      *)
(* ------------------------------------------------------------------------- *)

let SET_DECOMP = prove
 (`!s. isaset s
       ==> (set s) SUBSET (setlevel(droplevel(level s))) /\
           (I_SET (setlevel(droplevel(level s))) (set s) = element s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[isaset] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:setlevel`) THEN
  REWRITE_TAC[set] THEN CONV_TAC SELECT_CONV THEN
  ASM_REWRITE_TAC[setlevel; droplevel] THEN
  MP_TAC(SPEC `s:V` ELEMENT_IN_LEVEL) THEN
  ASM_REWRITE_TAC[setlevel; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let SET_SUBSET_SETLEVEL = prove
 (`!s. isaset s ==> set(s) SUBSET setlevel(droplevel(level s))`,
  MESON_TAC[SET_DECOMP]);;

(* ------------------------------------------------------------------------- *)
(* Power set exists.                                                         *)
(* ------------------------------------------------------------------------- *)

let POWERSET_EXISTS = prove
 (`!s. ?t. (level t = Powerset(level s)) /\ !x. x <: t <=> x <=: s`,
  GEN_TAC THEN ASM_CASES_TAC `isaset s` THENL
   [FIRST_ASSUM(MP_TAC o GSYM o MATCH_MP SET_DECOMP) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isaset]) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:setlevel` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[droplevel] THEN STRIP_TAC THEN
    X_CHOOSE_THEN `t:V` STRIP_ASSUME_TAC
      (SPEC `Powerset l` SETLEVEL_EXISTS) THEN
    MP_TAC(SPECL [`t:V`; `\v. !x. x <: v ==> x <: s`]
      COMPREHENSION_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:V` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[subset_def] THEN
    ASM_MESON_TAC[ELEMENT_IN_LEVEL];
    MP_TAC(SPEC `level s` SETLEVEL_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:V` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[subset_def] THEN
    ASM_MESON_TAC[ELEMENT_IN_LEVEL; MEMBERS_ISASET; isaset]]);;

let POWERSET = new_specification ["powerset"]
     (REWRITE_RULE[SKOLEM_THM] POWERSET_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Pairing operation.                                                        *)
(* ------------------------------------------------------------------------- *)

let pair = new_definition
 `pair x y =
        mk_V(Cartprod (level x) (level y),I_PAIR(element x,element y))`;;

let PAIR_IN_LEVEL = prove
 (`!x y l m. x IN setlevel l /\ y IN setlevel m
             ==> I_PAIR(x,y) IN setlevel (Cartprod l m)`,
  REWRITE_TAC[setlevel; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let DEST_MK_PAIR = prove
 (`dest_V(mk_V(Cartprod (level x) (level y),I_PAIR(element x,element y))) =
        Cartprod (level x) (level y),I_PAIR(element x,element y)`,
  REWRITE_TAC[GSYM V_TYBIJ] THEN SIMP_TAC[PAIR_IN_LEVEL; ELEMENT_IN_LEVEL]);;

let PAIR_INJ = prove
 (`!x1 y1 x2 y2. (pair x1 y1 = pair x2 y2) <=> (x1 = x2) /\ (y1 = y2)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[pair] THEN
  DISCH_THEN(MP_TAC o AP_TERM `dest_V`) THEN REWRITE_TAC[DEST_MK_PAIR] THEN
  REWRITE_TAC[setlevel_INJ; PAIR_EQ; I_PAIR] THEN
  REWRITE_TAC[level; element] THEN MESON_TAC[PAIR; CONJUNCT1 v_tybij]);;

let LEVEL_PAIR = prove
 (`!x y. level(pair x y) = Cartprod (level x) (level y)`,
  REWRITE_TAC[level;
              REWRITE_RULE[DEST_MK_PAIR] (AP_TERM `dest_V` (SPEC_ALL pair))]);;

(* ------------------------------------------------------------------------- *)
(* Decomposition functions.                                                  *)
(* ------------------------------------------------------------------------- *)

let fst_def = new_definition
  `fst p = @x. ?y. p = pair x y`;;

let snd_def = new_definition
  `snd p = @y. ?x. p = pair x y`;;

let PAIR_CLAUSES = prove
 (`!x y. (fst(pair x y) = x) /\ (snd(pair x y) = y)`,
  REWRITE_TAC[fst_def; snd_def] THEN MESON_TAC[PAIR_INJ]);;

(* ------------------------------------------------------------------------- *)
(* And the Cartesian product space.                                          *)
(* ------------------------------------------------------------------------- *)

let CARTESIAN_EXISTS = prove
 (`!s t. ?u. (level u =
                  Powerset(Cartprod (droplevel(level s))
                                    (droplevel(level t)))) /\
                 !z. z <: u <=> ?x y. (z = pair x y) /\ x <: s /\ y <: t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `isaset s` THENL
   [ALL_TAC; ASM_MESON_TAC[EMPTY_EXISTS; MEMBERS_ISASET]] THEN
  SUBGOAL_THEN `?l. (level s = Powerset l)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[isaset]; ALL_TAC] THEN
  ASM_CASES_TAC `isaset t` THENL
   [ALL_TAC; ASM_MESON_TAC[EMPTY_EXISTS; MEMBERS_ISASET]] THEN
  SUBGOAL_THEN `?m. (level t = Powerset m)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[isaset]; ALL_TAC] THEN
  MP_TAC(SPEC `Cartprod l m` SETLEVEL_EXISTS) THEN
  ASM_REWRITE_TAC[droplevel] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:V` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`u:V`; `\z. ?x y. (z = pair x y) /\ x <: s /\ y <: t`]
               COMPREHENSION_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:V` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:V` THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> a) ==> ((a /\ b) /\ c <=> c)`) THEN
  CONJ_TAC THENL [MESON_TAC[ELEMENT_IN_LEVEL]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LEVEL_PAIR] THEN BINOP_TAC THEN
  ASM_MESON_TAC[inset; setlevel_INJ]);;

let PRODUCT = new_specification ["product"]
       (REWRITE_RULE[SKOLEM_THM] CARTESIAN_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Extensionality for sets at the same level.                                *)
(* ------------------------------------------------------------------------- *)

let IN_SET_ELEMENT = prove
 (`!s. isaset s /\ e IN set(s)
       ==> ?x. (e = element x) /\ (level s = Powerset(level x)) /\ x <: s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `l:setlevel` o REWRITE_RULE[isaset]) THEN
  EXISTS_TAC `mk_V(l,e)` THEN REWRITE_TAC[inset] THEN
  SUBGOAL_THEN `e IN setlevel l` (fun t -> ASM_SIMP_TAC[t; MK_V_CLAUSES]) THEN
  ASM_MESON_TAC[SET_SUBSET_SETLEVEL; SUBSET; droplevel]);;

let SUBSET_ALT = prove
 (`isaset s /\ isaset t
   ==> (s <=: t <=> (level s = level t) /\ set(s) SUBSET set(t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subset_def; inset] THEN
  ASM_CASES_TAC `level s = level t` THEN ASM_REWRITE_TAC[SUBSET] THEN
  STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_MESON_TAC[IN_SET_ELEMENT]);;

let SUBSET_ANTISYM_LEVEL = prove
 (`!s t. isaset s /\ isaset t /\ s <=: t /\ t <=: s ==> (s = t)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[SUBSET_ALT]  THEN
  EVERY_ASSUM(MP_TAC o GSYM o MATCH_MP SET_DECOMP) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:V` SET) THEN MP_TAC(SPEC `t:V` SET) THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  AP_TERM_TAC THEN BINOP_TAC THEN ASM_MESON_TAC[SUBSET_ANTISYM]);;

let EXTENSIONALITY_LEVEL = prove
 (`!s t. isaset s /\ isaset t /\ (level s = level t) /\ (!x. x <: s <=> x <: t)
         ==> (s = t)`,
  MESON_TAC[SUBSET_ANTISYM_LEVEL; subset_def]);;

(* ------------------------------------------------------------------------- *)
(* And hence for any nonempty sets.                                          *)
(* ------------------------------------------------------------------------- *)

let EXTENSIONALITY_NONEMPTY = prove
 (`!s t. (?x. x <: s) /\ (?x. x <: t) /\ (!x. x <: s <=> x <: t)
         ==> (s = t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTENSIONALITY_LEVEL THEN
  ASM_MESON_TAC[MEMBERS_ISASET; inset]);;

(* ------------------------------------------------------------------------- *)
(* Union set exists. I don't need this but if might be a sanity check.       *)
(* ------------------------------------------------------------------------- *)

let UNION_EXISTS = prove
 (`!s. ?t. (level t = droplevel(level s)) /\
           !x. x <: t <=> ?u. x <: u /\ u <: s`,
  GEN_TAC THEN ASM_CASES_TAC `isaset s` THENL
   [ALL_TAC;
    MP_TAC(SPEC `droplevel(level s)` EMPTY_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[MEMBERS_ISASET]] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `l:setlevel` o REWRITE_RULE[isaset]) THEN
  ASM_REWRITE_TAC[droplevel] THEN ASM_CASES_TAC `?m. l = Powerset m` THENL
   [ALL_TAC;
    MP_TAC(SPEC `l:setlevel` EMPTY_EXISTS) THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[inset] THEN
    ASM_MESON_TAC[setlevel_INJ]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:setlevel` SUBST_ALL_TAC) THEN
  MP_TAC(SPEC `m:setlevel` SETLEVEL_EXISTS) THEN
  ASM_REWRITE_TAC[droplevel] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:V` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`t:V`; `\x. ?u. x <: u /\ u <: s`]
      COMPREHENSION_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[inset; ELEMENT_IN_LEVEL; setlevel_INJ]);;

let SETUNION = new_specification ["setunion"]
        (REWRITE_RULE[SKOLEM_THM] UNION_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Boolean stuff.                                                            *)
(* ------------------------------------------------------------------------- *)

let true_def = new_definition
 `true = mk_V(Ur_bool,I_BOOL T)`;;

let false_def = new_definition
 `false = mk_V(Ur_bool,I_BOOL F)`;;

let boolset = new_definition
 `boolset =
     mk_V(Powerset Ur_bool,I_SET (setlevel Ur_bool) (setlevel Ur_bool))`;;

let IN_BOOL = prove
 (`!x. x <: boolset <=> (x = true) \/ (x = false)`,
  REWRITE_TAC[inset; boolset; true_def; false_def] THEN
  SIMP_TAC[MK_V_SET; SUBSET_REFL] THEN
  REWRITE_TAC[setlevel_INJ; setlevel] THEN
  SUBGOAL_THEN `IMAGE I_BOOL UNIV = {I_BOOL F,I_BOOL T}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[I_BOOL];
    ALL_TAC] THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV o LAND_CONV) [GSYM SET] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `!b. (I_BOOL b) IN setlevel Ur_bool` ASSUME_TAC THENL
   [REWRITE_TAC[setlevel; IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ASM_MESON_TAC[V_TYBIJ; ELEMENT_IN_LEVEL; PAIR_EQ]]);;

let TRUE_NE_FALSE = prove
 (`~(true = false)`,
  REWRITE_TAC[true_def; false_def] THEN
  DISCH_THEN(MP_TAC o AP_TERM `dest_V`) THEN
  SUBGOAL_THEN `!b. (I_BOOL b) IN setlevel Ur_bool` ASSUME_TAC THENL
   [REWRITE_TAC[setlevel; IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ASM_MESON_TAC[V_TYBIJ; I_BOOL; PAIR_EQ]]);;

let BOOLEAN_EQ = prove
 (`!x y. x <: boolset /\ y <: boolset /\
         ((x = true) <=> (y = true))
         ==> (x = y)`,
  MESON_TAC[TRUE_NE_FALSE; IN_BOOL]);;

(* ------------------------------------------------------------------------- *)
(* Ind stuff.                                                                *)
(* ------------------------------------------------------------------------- *)

let indset = new_definition
 `indset = mk_V(Powerset Ur_ind,I_SET (setlevel Ur_ind) (setlevel Ur_ind))`;;

let INDSET_IND_MODEL = prove
 (`?f. (!i:ind_model. f(i) <: indset) /\ (!i j. (f i = f j) ==> (i = j))`,
  EXISTS_TAC `\i. mk_V(Ur_ind,I_IND i)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. (I_IND i) IN setlevel Ur_ind` ASSUME_TAC THENL
   [REWRITE_TAC[setlevel; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MK_V_SET; SUBSET_REFL; inset; indset; MK_V_CLAUSES] THEN
  ASM_MESON_TAC[V_TYBIJ; I_IND; ELEMENT_IN_LEVEL; PAIR_EQ]);;

let INDSET_INHABITED = prove
 (`?x. x <: indset`,
  MESON_TAC[INDSET_IND_MODEL]);;

(* ------------------------------------------------------------------------- *)
(* Axiom of choice (this is trivially so in HOL anyway, but...)              *)
(* ------------------------------------------------------------------------- *)

let ch =
  let th = prove
   (`?ch. !s. (?x. x <: s) ==> ch(s) <: s`,
    REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]) in
  new_specification ["ch"] th;;

(* ------------------------------------------------------------------------- *)
(* Sanity check lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let IN_POWERSET = prove
 (`!x s. x <: powerset s <=> x <=: s`,
  MESON_TAC[POWERSET]);;

let IN_PRODUCT = prove
 (`!z s t. z <: product s t <=> ?x y. (z = pair x y) /\ x <: s /\ y <: t`,
  MESON_TAC[PRODUCT]);;

let IN_COMPREHENSION = prove
 (`!p s x. x <: s suchthat p <=> x <: s /\ p x`,
  MESON_TAC[SUCHTHAT]);;

let PRODUCT_INHABITED = prove
 (`(?x. x <: s) /\ (?y. y <: t) ==> ?z. z <: product s t`,
  MESON_TAC[IN_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Definition of function space.                                             *)
(* ------------------------------------------------------------------------- *)

let funspace = new_definition
  `funspace s t =
      powerset(product s t) suchthat
      (\u. !x. x <: s ==> ?!y. pair x y <: u)`;;

let apply_def = new_definition
  `apply f x = @y. pair x y <: f`;;

let abstract = new_definition
  `abstract s t f =
        (product s t) suchthat (\z. !x y. (pair x y = z) ==> (y = f x))`;;

let APPLY_ABSTRACT = prove
 (`!x s t. x <: s /\ f(x) <: t ==> (apply(abstract s t f) x = f(x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[apply_def; abstract; IN_PRODUCT; SUCHTHAT] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[PAIR_INJ] THEN
  ASM_MESON_TAC[]);;

let APPLY_IN_RANSPACE = prove
 (`!f x s t. x <: s /\ f <: funspace s t ==> apply f x <: t`,
  REWRITE_TAC[funspace; SUCHTHAT; IN_POWERSET; IN_PRODUCT; subset_def] THEN
  REWRITE_TAC[apply_def] THEN MESON_TAC[PAIR_INJ]);;

let ABSTRACT_IN_FUNSPACE = prove
 (`!f x s t. (!x. x <: s ==> f(x) <: t)
             ==> abstract s t f <: funspace s t`,
  REWRITE_TAC[funspace; abstract; SUCHTHAT; IN_POWERSET; IN_PRODUCT;
              subset_def; PAIR_INJ] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1; EXISTS_REFL] THEN MESON_TAC[]);;

let FUNSPACE_INHABITED = prove
 (`!s t. ((?x. x <: s) ==> (?y. y <: t)) ==> ?f. f <: funspace s t`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `abstract s t (\x. @y. y <: t)` THEN
  MATCH_MP_TAC ABSTRACT_IN_FUNSPACE THEN ASM_MESON_TAC[]);;

let ABSTRACT_EQ = prove
 (`!s t1 t2 f g.
        (?x. x <: s) /\
        (!x. x <: s ==> f(x) <: t1 /\ g(x) <: t2 /\ (f x = g x))
        ==> (abstract s t1 f = abstract s t2 g)`,
  REWRITE_TAC[abstract] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTENSIONALITY_NONEMPTY THEN
  REWRITE_TAC[SUCHTHAT; IN_PRODUCT] THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  SIMP_TAC[TAUT `(a /\ b /\ c) /\ d <=> ~(a ==> b /\ c ==> ~d)`] THEN
  REWRITE_TAC[PAIR_INJ] THEN SIMP_TAC[LEFT_FORALL_IMP_THM] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_INJ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  REWRITE_TAC[NOT_IMP] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_INJ] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Special case of treating a Boolean function as a set.                     *)
(* ------------------------------------------------------------------------- *)

let boolean = new_definition
  `boolean b = if b then true else false`;;

let holds = new_definition
  `holds s x <=> (apply s x = true)`;;

let BOOLEAN_IN_BOOLSET = prove
 (`!b. boolean b <: boolset`,
  REWRITE_TAC[boolean] THEN MESON_TAC[IN_BOOL]);;

let BOOLEAN_EQ_TRUE = prove
 (`!b. (boolean b = true) <=> b`,
  REWRITE_TAC[boolean] THEN MESON_TAC[TRUE_NE_FALSE]);;
