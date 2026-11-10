(* ========================================================================= *)
(* Possibly infinite lists ("lazy lists").                                   *)
(*                                                                           *)
(* The type A llist is the disjoint sum of A list and num->A, with the       *)
(* conversions llist_of_list and llist_of_seq as its two constructors. On    *)
(* top of this come the usual constructors LNIL and LCONS, extensionality    *)
(* (LLIST_EQ), corecursion with uniqueness (LCOREC and LUNFOLD), and         *)
(* coinduction by bisimulation (LLIST_COINDUCT and LLIST_COINDUCT_TAC).      *)
(* Each operation is defined in whichever way makes its theorems simplest:   *)
(* by cases on the representation if it acts separately on lists and on      *)
(* sequences, and by recursion or corecursion otherwise, with the algebraic  *)
(* laws proved by coinduction where that is simpler.                         *)
(* ========================================================================= *)

needs "Library/iter.ml";;

(* ------------------------------------------------------------------------- *)
(* Two operations on options: THE extracts the value from SOME, and          *)
(* OPTION_MAP is the analog of MAP.                                          *)
(* ------------------------------------------------------------------------- *)

let THE = new_recursive_definition option_RECURSION
 `THE(SOME (x:A)) = x`;;

let OPTION_MAP = new_recursive_definition option_RECURSION
 `(!f. OPTION_MAP (f:A->B) NONE = NONE) /\
  (!f x. OPTION_MAP (f:A->B) (SOME x) = SOME (f x))`;;

let option_CASES = prove
 (`!x:A option. x = NONE \/ ?a. x = SOME a`,
  MATCH_MP_TAC option_INDUCT THEN MESON_TAC[]);;

let OPTION_MAP_EQ_NONE = prove
 (`!(f:A->B) x. OPTION_MAP f x = NONE <=> x = NONE`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP; option_DISTINCT]);;

let OPTION_MAP_EQ_SOME = prove
 (`!(f:A->B) x y. OPTION_MAP f x = SOME y <=> ?a. x = SOME a /\ y = f a`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let OPTION_MAP_ID = prove
 (`!x:A option. OPTION_MAP (\a. a) x = x`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_MAP]);;

let OPTION_MAP_o = prove
 (`!(f:B->C) (g:A->B) x.
        OPTION_MAP f (OPTION_MAP g x) = OPTION_MAP (f o g) x`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* The type, with the conversions from lists and sequences as constructors.  *)
(* ------------------------------------------------------------------------- *)

let llist_INDUCT,llist_RECURSION = define_type
 "llist = llist_of_list (A list) | llist_of_seq (num->A)";;

let LLIST_OF_LIST_11 = prove
 (`!l1 l2:A list. llist_of_list l1 = llist_of_list l2 <=> l1 = l2`,
  REWRITE_TAC[injectivity "llist"]);;

let LLIST_OF_SEQ_11 = prove
 (`!f g:num->A. llist_of_seq f = llist_of_seq g <=> f = g`,
  REWRITE_TAC[injectivity "llist"]);;

let LLIST_OF_LIST_NEQ_SEQ = prove
 (`!(l:A list) f. ~(llist_of_list l = llist_of_seq f)`,
  REWRITE_TAC[distinctness "llist"]);;

let LLIST_LIST_OR_SEQ = prove
 (`!l:A llist. (?xs. l = llist_of_list xs) \/ (?f. l = llist_of_seq f)`,
  ACCEPT_TAC(cases "llist"));;

(* Equations between representations, and case analysis on them. The cases   *)
(* are named xs for a list and f for a sequence.                             *)

let LLIST_REP_EQ = CONJ (injectivity "llist")
  (CONJ (distinctness "llist") (GSYM(distinctness "llist")));;

let LLIST_REP_CASES_TAC tm =
  DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC) (CHOOSE_THEN SUBST_ALL_TAC)
   (ISPEC tm LLIST_LIST_OR_SEQ);;

(* ------------------------------------------------------------------------- *)
(* Constructors, elements and destructors.                                   *)
(* ------------------------------------------------------------------------- *)

let LNIL_DEF = new_definition
 `LNIL = llist_of_list ([]:A list)`;;

let LCONS_DEF = define
 `(LCONS (h:A) (llist_of_list l) = llist_of_list (CONS h l)) /\
  (LCONS h (llist_of_seq f) =
   llist_of_seq (\n. if n = 0 then h else f(n - 1)))`;;

let LLIST_OF_LIST = prove
 (`llist_of_list [] = (LNIL:A llist) /\
   !h:A t. llist_of_list (CONS h t) = LCONS h (llist_of_list t)`,
  REWRITE_TAC[LNIL_DEF; LCONS_DEF]);;

let LNTH_DEF = define
 `(LNTH n (llist_of_list l) =
   if n < LENGTH l then SOME (EL n l:A) else NONE) /\
  (LNTH n (llist_of_seq f) = SOME (f n))`;;

let LNTH = prove
 (`(!n. LNTH n (LNIL:A llist) = NONE) /\
   (!h:A t. LNTH 0 (LCONS h t) = SOME h) /\
   (!n h:A t. LNTH (SUC n) (LCONS h t) = LNTH n t)`,
  REWRITE_TAC[LNIL_DEF; LNTH_DEF; LENGTH; CONJUNCT1 LT] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `t:A llist` THEN
  REWRITE_TAC[LCONS_DEF; LNTH_DEF; LENGTH; LT_0; LT_SUC; EL; HD; TL;
              NOT_SUC; SUC_SUB1]);;

let LLIST_EQ = prove
 (`!l1 l2:A llist. l1 = l2 <=> !n. LNTH n l1 = LNTH n l2`,
  let lemma = prove
   (`!l1 l2:A list.
        (!n. LNTH n (llist_of_list l1) = LNTH n (llist_of_list l2)) <=>
        l1 = l2`,
    REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
    REWRITE_TAC[LNTH_DEF] THEN DISCH_TAC THEN REWRITE_TAC[LIST_EQ] THEN
    SUBGOAL_THEN `LENGTH(l1:A list) = LENGTH(l2:A list)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `LENGTH(l1:A list)` th) THEN
                              MP_TAC(SPEC `LENGTH(l2:A list)` th)) THEN
      REWRITE_TAC[LT_REFL] THEN
      REPEAT(COND_CASES_TAC THEN
             REWRITE_TAC[option_DISTINCT; GSYM option_DISTINCT]) THEN
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[option_INJ]])
  and lemma' = prove
   (`!(xs:A list) f.
        ~(!n. LNTH n (llist_of_list xs) = LNTH n (llist_of_seq f)) /\
        ~(!n. LNTH n (llist_of_seq f) = LNTH n (llist_of_list xs))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN CONJ_TAC THEN
    EXISTS_TAC `LENGTH(xs:A list)` THEN
    REWRITE_TAC[LNTH_DEF; LT_REFL; option_DISTINCT; GSYM option_DISTINCT]) in
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  LLIST_REP_CASES_TAC `l2:A llist` THEN
  REWRITE_TAC[lemma; LLIST_REP_EQ; lemma'] THEN
  REWRITE_TAC[LNTH_DEF; option_INJ; FUN_EQ_THM]);;

let LLIST_OF_SEQ = prove
 (`!f:num->A. llist_of_seq f = LCONS (f 0) (llist_of_seq (\n. f (SUC n)))`,
  REWRITE_TAC[LCONS_DEF; LLIST_OF_SEQ_11; FUN_EQ_THM] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1]);;

let LLIST_CASES = prove
 (`!l:A llist. l = LNIL \/ ?h t. l = LCONS h t`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THENL
   [STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES) THEN
    REWRITE_TAC[LNIL_DEF] THEN MESON_TAC[LCONS_DEF];
    MESON_TAC[LLIST_OF_SEQ]]);;

let NOT_LCONS_LNIL = prove
 (`!h:A t. ~(LCONS h t = LNIL)`,
  REWRITE_TAC[LLIST_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LNTH; option_DISTINCT]);;

let LCONS_11 = prove
 (`!(h1:A) h2 t1 t2. LCONS h1 t1 = LCONS h2 t2 <=> h1 = h2 /\ t1 = t2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[LLIST_EQ] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(GEN `n:num` (SPEC `SUC n` th))) THEN
  REWRITE_TAC[LNTH; option_INJ] THEN SIMP_TAC[]);;

let LHD_DEF = new_definition
 `LHD (l:A llist) = THE(LNTH 0 l)`;;

let LHD = prove
 (`!h:A t. LHD(LCONS h t) = h`,
  REWRITE_TAC[LHD_DEF; LNTH; THE]);;

let LTL_DEF = define
 `(LTL (llist_of_list l) =
   llist_of_list (if l = [] then [] else TL l:A list)) /\
  (LTL (llist_of_seq f) = llist_of_seq (\n. f (SUC n)))`;;

let LTL = prove
 (`LTL(LNIL:A llist) = LNIL /\ !h:A t. LTL(LCONS h t) = t`,
  REWRITE_TAC[LNIL_DEF; LTL_DEF] THEN REPEAT GEN_TAC THEN
  LLIST_REP_CASES_TAC `t:A llist` THEN
  REWRITE_TAC[LCONS_DEF; LTL_DEF; NOT_CONS_NIL; TL; NOT_SUC; SUC_SUB1;
              ETA_AX]);;

let LCONS_LHD_LTL = prove
 (`!l:A llist. ~(l = LNIL) ==> LCONS (LHD l) (LTL l) = l`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:A llist` LLIST_CASES) THEN
  REWRITE_TAC[LHD; LTL]);;

let LNTH_NONE_MONO = prove
 (`!(l:A llist) m n. LNTH m l = NONE /\ m <= n ==> LNTH n l = NONE`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LNTH_DEF; option_DISTINCT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Append, by cases on the representation; corecursion is defined with it.   *)
(* ------------------------------------------------------------------------- *)

let LAPPEND_DEF = define
 `(LAPPEND (llist_of_list l1) (llist_of_list l2) =
   llist_of_list (APPEND l1 l2)) /\
  (LAPPEND (llist_of_list l1) (llist_of_seq f) =
   llist_of_seq (\n. if n < LENGTH l1 then EL n l1
                     else f (n - LENGTH l1):A)) /\
  (LAPPEND (llist_of_seq f) l = llist_of_seq f)`;;

let LAPPEND = prove
 (`(!l:A llist. LAPPEND LNIL l = l) /\
   (!h:A t l. LAPPEND (LCONS h t) l = LCONS h (LAPPEND t l))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [LLIST_REP_CASES_TAC `l:A llist` THEN
    REWRITE_TAC[LNIL_DEF; LAPPEND_DEF; APPEND; LENGTH; CONJUNCT1 LT; SUB_0;
                ETA_AX];
    LLIST_REP_CASES_TAC `t:A llist` THEN
    REWRITE_TAC[LCONS_DEF; LAPPEND_DEF] THEN
    LLIST_REP_CASES_TAC `l:A llist` THEN
    REWRITE_TAC[LAPPEND_DEF; LCONS_DEF; APPEND; LLIST_REP_EQ; FUN_EQ_THM] THEN
    INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; LT_0; LT_SUC; EL; HD; TL; SUB_SUC; NOT_SUC;
                SUC_SUB1]]);;

(* ------------------------------------------------------------------------- *)
(* Corecursion. If the unfolding stops, the result is a finite prefix        *)
(* followed by the given final llist; otherwise it is an infinite sequence.  *)
(* ------------------------------------------------------------------------- *)

let LCOREC_DEF = new_definition
 `LCOREC p e h t (x:B) =
  if ?n. p (ITER n t x)
  then LAPPEND
        (llist_of_list
          (list_of_seq (\i. h (ITER i t x)) ((minimal) (\n. p (ITER n t x)))))
        (e (ITER ((minimal) (\n. p (ITER n t x))) t x))
  else llist_of_seq (\i. h (ITER i t x)):A llist`;;

let LCOREC = prove
 (`!p e h t (x:B).
        LCOREC p e h t x:A llist =
        if p x then e x else LCONS (h x) (LCOREC p e h t (t x))`,
  let MINIMAL_SUC = prove
   (`!P. ~P 0 /\ (?n. P n) ==> (minimal) P = SUC((minimal) (\n. P(SUC n)))`,
    GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `?n. P(SUC n)` ASSUME_TAC THENL
     [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
    MP_TAC(SPEC `P:num->bool` MINIMAL) THEN
    MP_TAC(SPEC `\n. (P:num->bool)(SUC n)` MINIMAL) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`(minimal) P`,`m:num`) THEN
    SPEC_TAC(`(minimal) (\n. (P:num->bool)(SUC n))`,`k:num`) THEN
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `m:num` num_CASES) THEN STRIP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[SUC_INJ] THEN
    REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN ASM_MESON_TAC[LT_SUC]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[LCOREC_DEF] THEN
  ASM_CASES_TAC `(p:B->bool) x` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `?n. (p:B->bool) (ITER n t x)` (fun th -> REWRITE_TAC[th])
    THENL [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ITER]; ALL_TAC] THEN
    SUBGOAL_THEN `(minimal) (\n. (p:B->bool) (ITER n t x)) = 0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(MESON[MINIMAL; LT_NZ] `!P. P 0 ==> (minimal) P = 0`) THEN
      ASM_REWRITE_TAC[ITER];
      ALL_TAC] THEN
    REWRITE_TAC[list_of_seq; ITER; LLIST_OF_LIST; LAPPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(?n. (p:B->bool) (ITER n t x)) <=> (?n. p (ITER n t (t x)))`
  SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
      STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
      ASM_REWRITE_TAC[ITER_ALT] THEN MESON_TAC[];
      MESON_TAC[ITER_ALT]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ALL_TAC; GEN_REWRITE_TAC LAND_CONV [LLIST_OF_SEQ] THEN
    REWRITE_TAC[ITER_ALT]] THEN
  MP_TAC(ISPEC `\n. (p:B->bool) (ITER n t x)` MINIMAL_SUC) THEN
  REWRITE_TAC[ITER_ALT] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[ITER_ALT]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ; o_DEF; ITER_ALT; LLIST_OF_LIST; LAPPEND]);;

let LCOREC_UNIQUE = prove
 (`!p e h t (g:B->A llist).
        (!x. g x = if p x then e x else LCONS (h x) (g (t x)))
        ==> g = LCOREC p e h t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM; LLIST_EQ] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN X_GEN_TAC `x:B` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LCOREC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LNTH] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let LUNFOLD_DEF = new_definition
 `LUNFOLD p h t = LCOREC p (\x:B. LNIL:A llist) h t`;;

let LUNFOLD = prove
 (`!p h t (x:B).
        LUNFOLD p h t x:A llist =
        if p x then LNIL else LCONS (h x) (LUNFOLD p h t (t x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LUNFOLD_DEF] THEN
  GEN_REWRITE_TAC LAND_CONV [LCOREC] THEN REWRITE_TAC[]);;

let LUNFOLD_UNIQUE = prove
 (`!p h t (g:B->A llist).
        (!x. g x = if p x then LNIL else LCONS (h x) (g (t x)))
        ==> g = LUNFOLD p h t`,
  REWRITE_TAC[LUNFOLD_DEF] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC LCOREC_UNIQUE THEN REWRITE_TAC[] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Coinduction: bisimilar llists are equal.                                  *)
(* ------------------------------------------------------------------------- *)

let LLIST_COINDUCT = prove
 (`!R:A llist->A llist->bool.
        (!l1 l2. R l1 l2
                 ==> l1 = LNIL /\ l2 = LNIL \/
                     ?h t1 t2. l1 = LCONS h t1 /\ l2 = LCONS h t2 /\ R t1 t2)
        ==> !l1 l2. R l1 l2 ==> l1 = l2`,
  GEN_TAC THEN DISCH_THEN(fun bisim ->
    SUBGOAL_THEN `!n l1 l2:A llist. R l1 l2 ==> LNTH n l1 = LNTH n l2`
     (fun th -> MESON_TAC[th; LLIST_EQ]) THEN
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP bisim) THEN
    ASM_REWRITE_TAC[LNTH] THEN ASM_MESON_TAC[]));;

let LLIST_STRONG_COINDUCT = prove
 (`!R:A llist->A llist->bool.
        (!l1 l2. R l1 l2
                 ==> l1 = LNIL /\ l2 = LNIL \/
                     ?h t1 t2. l1 = LCONS h t1 /\ l2 = LCONS h t2 /\
                               (R t1 t2 \/ t1 = t2))
        ==> !l1 l2. R l1 l2 ==> l1 = l2`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\l1 l2:A llist. R l1 l2 \/ l1 = l2` LLIST_COINDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[] THEN MESON_TAC[LLIST_CASES]]);;

(* ------------------------------------------------------------------------- *)
(* Proof tools. LLIST_CASES_TAC splits a goal according to whether a given   *)
(* llist is LNIL or an LCONS, substituting it in the assumptions too.        *)
(*                                                                           *)
(* LLIST_COINDUCT_TAC proves an equation !vs. [P ==>] l = r by coinduction,  *)
(* for the relation \l1 l2. ?vs. [P /\] l1 = l /\ l2 = r. The goal left is   *)
(* that for any such vs, either l and r are both LNIL or they are LCONSes    *)
(* with the same head and with tails related or equal. LLIST_BISIM_TAC then  *)
(* simplifies the cases where l and r are given as LNIL or LCONSes, which    *)
(* usually leaves a goal that MESON can solve. LLIST_COINDUCT_UNFOLD_TAC thl *)
(* also rewrites l and r once with thl, e.g. with the unfolding of a         *)
(* corecursive definition.                                                   *)
(* ------------------------------------------------------------------------- *)

let LLIST_CASES_TAC tm =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
   (ISPEC tm LLIST_CASES);;

let LLIST_COINDUCT_UNFOLD_TAC thl : tactic =
  let unfold = if thl = [] then I
               else CONV_RULE(RAND_CONV(PURE_ONCE_REWRITE_CONV thl)) in
  let rec prove_exists tm wits th =
    match wits with
      [] -> th
    | w::ws -> let x,b = dest_exists tm in
               EXISTS (tm,w) (prove_exists (vsubst [w,x] b) ws th) in
  fun (asl,w) ->
    let vs,bod = strip_forall w in
    let hyps,eqn = if is_imp bod then dest_imp bod else `T`,bod in
    let l,r = dest_eq eqn in
    let ty = type_of l in
    let avoids = itlist (union o frees o concl o snd) asl (variables w) in
    let names = map (fst o dest_var) avoids in
    let rec fresh s = if mem s names then fresh (s^"'") else s in
    let l1 = mk_var(fresh "l1",ty) and l2 = mk_var(fresh "l2",ty) in
    let eqs = mk_conj(mk_eq(l1,l),mk_eq(l2,r)) in
    let body = if is_imp bod then mk_conj(hyps,eqs) else eqs in
    let rel = list_mk_abs([l1;l2],list_mk_exists(vs,body)) in
    let th = CONV_RULE
      (LAND_CONV(GEN_ALPHA_CONV l1 THENC BINDER_CONV(GEN_ALPHA_CONV l2)) THENC
       TOP_DEPTH_CONV BETA_CONV) (ISPEC rel LLIST_STRONG_COINDUCT) in
    let ant = lhand(concl th) in
    let th2 = SPECL [l;r] (UNDISCH th) in
    let rth = CONJ (REFL l) (REFL r) in
    let bth = if is_imp bod then CONJ (ASSUME hyps) rth else rth in
    let th3 = MP th2 (prove_exists (lhand(concl th2)) vs bth) in
    let th4 = GENL vs (if is_imp bod then DISCH hyps th3 else th3) in
    let is_sub th = let c = concl th in
                    is_eq c && (lhs c = l1 || lhs c = l2) in
    (MATCH_MP_TAC (DISCH ant th4) THEN X_GEN_TAC l1 THEN X_GEN_TAC l2 THEN
     DISCH_THEN(REPEAT_TCL CHOOSE_THEN
       (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
     REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o unfold o check is_sub))) (asl,w);;

let LLIST_COINDUCT_TAC = LLIST_COINDUCT_UNFOLD_TAC [];;

let LLIST_BISIM_REFL = prove
 (`!(R:A llist->A llist->bool) l.
        l = LNIL \/
        ?h t1 t2. l = LCONS h t1 /\ l = LCONS h t2 /\ (R t1 t2 \/ t1 = t2)`,
  REPEAT GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[NOT_LCONS_LNIL; LCONS_11] THEN MESON_TAC[]);;

let LLIST_BISIM_LCONS = prove
 (`!(a:A) x b y P.
        (?h t1 t2. LCONS a x = LCONS h t1 /\ LCONS b y = LCONS h t2 /\
                   P t1 t2) <=> a = b /\ P x y`,
  REWRITE_TAC[LCONS_11] THEN MESON_TAC[]);;

let LLIST_BISIM_TAC =
  REWRITE_TAC[LLIST_BISIM_LCONS; LLIST_BISIM_REFL; NOT_LCONS_LNIL;
              GSYM NOT_LCONS_LNIL];;

(* ------------------------------------------------------------------------- *)
(* Finite lists and infinite sequences.                                      *)
(* ------------------------------------------------------------------------- *)

let LNTH_LLIST_OF_LIST = prove
 (`!(l:A list) n.
        LNTH n (llist_of_list l) =
        if n < LENGTH l then SOME (EL n l) else NONE`,
  REWRITE_TAC[LNTH_DEF]);;

let LNTH_LLIST_OF_SEQ = prove
 (`!(f:num->A) n. LNTH n (llist_of_seq f) = SOME (f n)`,
  REWRITE_TAC[LNTH_DEF]);;

let list_of_llist = new_recursive_definition llist_RECURSION
 `!l. list_of_llist (llist_of_list l) = l:A list`;;

(* ------------------------------------------------------------------------- *)
(* Finiteness and length, by cases on the representation.                    *)
(* ------------------------------------------------------------------------- *)

let LFINITE_DEF = define
 `(LFINITE (llist_of_list (l:A list)) <=> T) /\
  (LFINITE (llist_of_seq (f:num->A)) <=> F)`;;

let LFINITE_LCONS = prove
 (`!h:A t. LFINITE (LCONS h t) <=> LFINITE t`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `t:A llist` THEN
  REWRITE_TAC[LCONS_DEF; LFINITE_DEF]);;

let LFINITE_RULES = prove
 (`LFINITE (LNIL:A llist) /\ (!h:A t. LFINITE t ==> LFINITE (LCONS h t))`,
  REWRITE_TAC[LNIL_DEF; LFINITE_DEF; LFINITE_LCONS]);;

let LFINITE_INDUCT = prove
 (`!LFINITE':A llist->bool.
        LFINITE' LNIL /\ (!h t. LFINITE' t ==> LFINITE' (LCONS h t))
        ==> (!a. LFINITE a ==> LFINITE' a)`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN LLIST_REP_CASES_TAC `a:A llist` THEN
  REWRITE_TAC[LFINITE_DEF] THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[GSYM LNIL_DEF] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 LCONS_DEF)] THEN ASM_MESON_TAC[]);;

let LFINITE_CASES = prove
 (`!a:A llist. LFINITE a <=> a = LNIL \/ (?h t. a = LCONS h t /\ LFINITE t)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:A llist` LLIST_CASES) THEN
  REWRITE_TAC[LFINITE_RULES; LFINITE_LCONS; NOT_LCONS_LNIL; LCONS_11] THEN
  MESON_TAC[]);;

let LFINITE_LTL = prove
 (`!l:A llist. LFINITE (LTL l) <=> LFINITE l`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:A llist` LLIST_CASES) THEN
  REWRITE_TAC[LTL; LFINITE_LCONS]);;

let LFINITE_LLIST_OF_LIST = prove
 (`!l:A llist. LFINITE l <=> ?xs. l = llist_of_list xs`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LFINITE_DEF; LLIST_REP_EQ] THEN MESON_TAC[]);;

let NOT_LFINITE_LLIST_OF_SEQ = prove
 (`!l:A llist. ~LFINITE l <=> ?f. l = llist_of_seq f`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LFINITE_DEF; LLIST_REP_EQ] THEN MESON_TAC[]);;

let LFINITE_LNTH = prove
 (`!l:A llist. LFINITE l <=> ?n. LNTH n l = NONE`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LFINITE_DEF; LNTH_DEF; option_DISTINCT] THEN
  EXISTS_TAC `LENGTH(xs:A list)` THEN REWRITE_TAC[LT_REFL]);;

let LLIST_OF_LIST_OF_LLIST = prove
 (`!l:A llist. LFINITE l ==> llist_of_list (list_of_llist l) = l`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LFINITE_DEF; list_of_llist]);;

let NOT_LFINITE_COINDUCT = prove
 (`!P:A llist->bool.
        (!l. P l ==> ?h t. l = LCONS h t /\ P t)
        ==> !l. P l ==> ~LFINITE l`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!l:A llist. LFINITE l ==> ~P l` (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC LFINITE_INDUCT THEN ASM_MESON_TAC[NOT_LCONS_LNIL; LCONS_11]);;

let LLENGTH_DEF = define
 `(LLENGTH (llist_of_list (l:A list)) = SOME (LENGTH l)) /\
  (LLENGTH (llist_of_seq (f:num->A)) = NONE)`;;

let LLENGTH = prove
 (`LLENGTH (LNIL:A llist) = SOME 0 /\
   !h:A t. LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t)`,
  REWRITE_TAC[LNIL_DEF; LLENGTH_DEF; LENGTH] THEN REPEAT GEN_TAC THEN
  LLIST_REP_CASES_TAC `t:A llist` THEN
  REWRITE_TAC[LCONS_DEF; LLENGTH_DEF; LENGTH; OPTION_MAP]);;

let LLENGTH_EQ_NONE = prove
 (`!l:A llist. LLENGTH l = NONE <=> ~LFINITE l`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LLENGTH_DEF; LFINITE_DEF; option_DISTINCT]);;

let LLENGTH_LLIST_OF_LIST = prove
 (`!l:A list. LLENGTH (llist_of_list l) = SOME (LENGTH l)`,
  REWRITE_TAC[LLENGTH_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Map, by cases on the representation.                                      *)
(* ------------------------------------------------------------------------- *)

let LMAP_DEF = define
 `(LMAP (f:A->B) (llist_of_list l) = llist_of_list (MAP f l)) /\
  (LMAP f (llist_of_seq s) = llist_of_seq (f o s))`;;

let LMAP = prove
 (`(!f:A->B. LMAP f LNIL = LNIL) /\
   (!(f:A->B) h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))`,
  REWRITE_TAC[LNIL_DEF; LMAP_DEF; MAP] THEN REPEAT GEN_TAC THEN
  LLIST_REP_CASES_TAC `t:A llist` THEN
  REWRITE_TAC[LCONS_DEF; LMAP_DEF; MAP; LLIST_OF_SEQ_11; FUN_EQ_THM;
              o_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let LMAP_LLIST_OF_LIST = prove
 (`!(f:A->B) l. LMAP f (llist_of_list l) = llist_of_list (MAP f l)`,
  REWRITE_TAC[LMAP_DEF]);;

let LMAP_LLIST_OF_SEQ = prove
 (`!(f:A->B) s. LMAP f (llist_of_seq s) = llist_of_seq (f o s)`,
  REWRITE_TAC[LMAP_DEF]);;

let LMAP_ID = prove
 (`!l:A llist. LMAP (\x. x) l = l`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP_DEF; MAP_ID; o_DEF; ETA_AX]);;

let LMAP_o = prove
 (`!(f:B->C) (g:A->B) l. LMAP f (LMAP g l) = LMAP (f o g) l`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP_DEF; MAP_o; o_ASSOC]);;

let LMAP_EQ_LNIL = prove
 (`!(f:A->B) l. LMAP f l = LNIL <=> l = LNIL`,
  GEN_TAC THEN GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP; NOT_LCONS_LNIL]);;

let LNTH_LMAP = prove
 (`!(f:A->B) n l. LNTH n (LMAP f l) = OPTION_MAP f (LNTH n l)`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP_DEF; LNTH_DEF; LENGTH_MAP; o_THM; OPTION_MAP] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL_MAP; OPTION_MAP]);;

let LFINITE_LMAP = prove
 (`!(f:A->B) l. LFINITE (LMAP f l) <=> LFINITE l`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP_DEF; LFINITE_DEF]);;

let LLENGTH_LMAP = prove
 (`!(f:A->B) l. LLENGTH (LMAP f l) = LLENGTH l`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP_DEF; LLENGTH_DEF; LENGTH_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Append, defined above. The algebraic laws are by coinduction.             *)
(* ------------------------------------------------------------------------- *)

let LAPPEND_LLIST_OF_LIST = prove
 (`!l1 l2:A list.
        LAPPEND (llist_of_list l1) (llist_of_list l2) =
        llist_of_list (APPEND l1 l2)`,
  REWRITE_TAC[LAPPEND_DEF]);;

let LAPPEND_LNIL = prove
 (`!l:A llist. LAPPEND l LNIL = l`,
  GEN_TAC THEN LLIST_REP_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LNIL_DEF; LAPPEND_DEF; APPEND_NIL]);;

let LAPPEND_ASSOC = prove
 (`!l1 l2 l3:A llist.
        LAPPEND l1 (LAPPEND l2 l3) = LAPPEND (LAPPEND l1 l2) l3`,
  LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC `l1:A llist` THEN
  REWRITE_TAC[LAPPEND] THEN LLIST_BISIM_TAC THEN MESON_TAC[]);;

let LAPPEND_INFINITE = prove
 (`!l1 l2:A llist. ~LFINITE l1 ==> LAPPEND l1 l2 = l1`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  REWRITE_TAC[LFINITE_DEF; LAPPEND_DEF]);;

let LFINITE_LAPPEND = prove
 (`!l1 l2:A llist. LFINITE (LAPPEND l1 l2) <=> LFINITE l1 /\ LFINITE l2`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  LLIST_REP_CASES_TAC `l2:A llist` THEN
  REWRITE_TAC[LFINITE_DEF; LAPPEND_DEF]);;

let LMAP_LAPPEND = prove
 (`!(f:A->B) l1 l2.
        LMAP f (LAPPEND l1 l2) = LAPPEND (LMAP f l1) (LMAP f l2)`,
  LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC `l1:A llist` THEN
  REWRITE_TAC[LAPPEND; LMAP] THEN LLIST_BISIM_TAC THEN MESON_TAC[]);;

let LNTH_LAPPEND = prove
 (`!(l1:A list) l2 n.
        LNTH n (LAPPEND (llist_of_list l1) l2) =
        if n < LENGTH l1 then SOME (EL n l1) else LNTH (n - LENGTH l1) l2`,
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l2:A llist` THEN
  REWRITE_TAC[LAPPEND_DEF; LNTH_DEF; LENGTH_APPEND; EL_APPEND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LAPPEND_EQ_LNIL = prove
 (`!l1 l2:A llist. LAPPEND l1 l2 = LNIL <=> l1 = LNIL /\ l2 = LNIL`,
  REPEAT GEN_TAC THEN LLIST_CASES_TAC `l1:A llist` THEN
  REWRITE_TAC[LAPPEND; NOT_LCONS_LNIL]);;

(* ------------------------------------------------------------------------- *)
(* Take and drop, by primitive recursion on the number.                      *)
(* ------------------------------------------------------------------------- *)

let LTAKE_DEF = define
 `(LTAKE 0 (l:A llist) = []) /\
  (LTAKE (SUC n) l =
   if l = LNIL then [] else CONS (LHD l) (LTAKE n (LTL l)))`;;

let LTAKE = prove
 (`(!l:A llist. LTAKE 0 l = []) /\
   (!n. LTAKE (SUC n) (LNIL:A llist) = []) /\
   (!n h:A t. LTAKE (SUC n) (LCONS h t) = CONS h (LTAKE n t))`,
  REWRITE_TAC[LTAKE_DEF; NOT_LCONS_LNIL; LHD; LTL]);;

let LDROP_DEF = define
 `(LDROP 0 (l:A llist) = l) /\ (LDROP (SUC n) l = LDROP n (LTL l))`;;

let LDROP_LNIL = prove
 (`!n. LDROP n (LNIL:A llist) = LNIL`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LDROP_DEF; LTL]);;

let LDROP = prove
 (`(!l:A llist. LDROP 0 l = l) /\
   (!n. LDROP (SUC n) (LNIL:A llist) = LNIL) /\
   (!n h:A t. LDROP (SUC n) (LCONS h t) = LDROP n t)`,
  REWRITE_TAC[LDROP_DEF; LDROP_LNIL; LTL]);;

let LTAKE_LDROP = prove
 (`!n (l:A llist). LAPPEND (llist_of_list (LTAKE n l)) (LDROP n l) = l`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  ASM_REWRITE_TAC[LTAKE; LDROP; LLIST_OF_LIST; LAPPEND]);;

let LNTH_LDROP = prove
 (`!m n (l:A llist). LNTH m (LDROP n l) = LNTH (m + n) l`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  ASM_REWRITE_TAC[LDROP; LNTH; ADD_CLAUSES]);;

let LDROP_ADD = prove
 (`!m n (l:A llist). LDROP (m + n) l = LDROP m (LDROP n l)`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  ASM_REWRITE_TAC[LDROP; LDROP_LNIL; ADD_CLAUSES]);;

let LNTH_LTAKE = prove
 (`!n (l:A llist). LNTH n (llist_of_list (LTAKE (SUC n) l)) = LNTH n l`,
  INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  ASM_REWRITE_TAC[LTAKE; LLIST_OF_LIST; LNTH]);;

let LLIST_EQ_LTAKE = prove
 (`!l1 l2:A llist. l1 = l2 <=> !n. LTAKE n l1 = LTAKE n l2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[LLIST_EQ] THEN ONCE_REWRITE_TAC[GSYM LNTH_LTAKE] THEN
  ASM_REWRITE_TAC[]);;

let LTAKE_LLIST_OF_SEQ = prove
 (`!n (f:num->A). LTAKE n (llist_of_seq f) = list_of_seq f n`,
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[LLIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[LTAKE; LIST_OF_SEQ; o_DEF]);;

let LDROP_LLIST_OF_SEQ = prove
 (`!n (f:num->A). LDROP n (llist_of_seq f) = llist_of_seq (\i. f(i + n))`,
  REWRITE_TAC[LLIST_EQ; LNTH_LDROP; LNTH_LLIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* The set of elements, and the quantifiers over elements.                   *)
(* ------------------------------------------------------------------------- *)

let set_of_llist = new_definition
 `set_of_llist (l:A llist) = {x | ?n. LNTH n l = SOME x}`;;

let IN_SET_OF_LLIST = prove
 (`!(x:A) l. x IN set_of_llist l <=> ?n. LNTH n l = SOME x`,
  REWRITE_TAC[set_of_llist; IN_ELIM_THM]);;

let LNTH_LCONS_EXISTS = prove
 (`!h:A t x. (?n. LNTH n (LCONS h t) = SOME x) <=>
             x = h \/ ?n. LNTH n t = SOME x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LNTH; option_INJ] THEN MESON_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LNTH];
      EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[LNTH]]]);;

let SET_OF_LLIST = prove
 (`set_of_llist (LNIL:A llist) = {} /\
   !h:A t. set_of_llist (LCONS h t) = h INSERT set_of_llist t`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LLIST; NOT_IN_EMPTY; IN_INSERT; LNTH;
              option_DISTINCT; GSYM option_DISTINCT; LNTH_LCONS_EXISTS]);;

let SET_OF_LLIST_LLIST_OF_LIST = prove
 (`!l:A list. set_of_llist (llist_of_list l) = set_of_list l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LLIST_OF_LIST; SET_OF_LLIST; set_of_list]);;

let SET_OF_LLIST_LLIST_OF_SEQ = prove
 (`!f:num->A. set_of_llist (llist_of_seq f) = IMAGE f (:num)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LLIST; LNTH_LLIST_OF_SEQ; option_INJ;
              IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[]);;

let SET_OF_LLIST_LMAP = prove
 (`!(f:A->B) l. set_of_llist (LMAP f l) = IMAGE f (set_of_llist l)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SET_OF_LLIST; LNTH_LMAP;
              OPTION_MAP_EQ_SOME] THEN
  MESON_TAC[]);;

let SET_OF_LLIST_LAPPEND = prove
 (`!l1 l2:A llist.
        set_of_llist (LAPPEND l1 l2) =
        if LFINITE l1 then set_of_llist l1 UNION set_of_llist l2
        else set_of_llist l1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LAPPEND_INFINITE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LFINITE_LLIST_OF_LIST]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LLIST_OF_LIST; LAPPEND; SET_OF_LLIST; UNION_EMPTY;
                  INSERT_UNION_EQ]);;

let LALL_DEF = new_definition
 `LALL P (l:A llist) <=> !x. x IN set_of_llist l ==> P x`;;

let LEXISTS_DEF = new_definition
 `LEXISTS P (l:A llist) <=> ?x. x IN set_of_llist l /\ P x`;;

let LALL_SET_OF_LLIST = prove
 (`!P (l:A llist). LALL P l <=> !x. x IN set_of_llist l ==> P x`,
  REWRITE_TAC[LALL_DEF]);;

let LEXISTS_SET_OF_LLIST = prove
 (`!P (l:A llist). LEXISTS P l <=> ?x. x IN set_of_llist l /\ P x`,
  REWRITE_TAC[LEXISTS_DEF]);;

let LALL = prove
 (`(!P:A->bool. LALL P LNIL) /\
   (!P h:A t. LALL P (LCONS h t) <=> P h /\ LALL P t)`,
  REWRITE_TAC[LALL_DEF; SET_OF_LLIST; FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let LEXISTS = prove
 (`(!P:A->bool. ~LEXISTS P LNIL) /\
   (!P h:A t. LEXISTS P (LCONS h t) <=> P h \/ LEXISTS P t)`,
  REWRITE_TAC[LEXISTS_DEF; SET_OF_LLIST; EXISTS_IN_INSERT; NOT_IN_EMPTY]);;

let LEXISTS_LALL = prove
 (`!P (l:A llist). LEXISTS P l <=> ~LALL (\x. ~P x) l`,
  REWRITE_TAC[LEXISTS_DEF; LALL_DEF] THEN MESON_TAC[]);;

let LALL_LMAP = prove
 (`!P (f:A->B) l. LALL P (LMAP f l) <=> LALL (P o f) l`,
  REWRITE_TAC[LALL_DEF; SET_OF_LLIST_LMAP; FORALL_IN_IMAGE; o_THM]);;

let LEXISTS_LMAP = prove
 (`!P (f:A->B) l. LEXISTS P (LMAP f l) <=> LEXISTS (P o f) l`,
  REWRITE_TAC[LEXISTS_DEF; SET_OF_LLIST_LMAP; EXISTS_IN_IMAGE; o_THM]);;

(* LALL satisfies the natural coinduction principle and LEXISTS induction.   *)

let LALL_COINDUCT = prove
 (`!P (Q:A llist->bool).
        (!l. Q l ==> l = LNIL \/ ?h t. l = LCONS h t /\ P h /\ Q t)
        ==> !l. Q l ==> LALL P l`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun coind ->
    REWRITE_TAC[LALL_DEF] THEN
    SUBGOAL_THEN `!n l (x:A). Q l /\ LNTH n l = SOME x ==> P x`
     (fun th -> MESON_TAC[th; IN_SET_OF_LLIST]) THEN
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP coind) MP_TAC) THEN
    ASM_REWRITE_TAC[LNTH; GSYM option_DISTINCT; option_INJ] THEN
    ASM_MESON_TAC[]));;

let LEXISTS_INDUCT = prove
 (`!P LEXISTS'.
        (!h:A t. P h ==> LEXISTS' (LCONS h t)) /\
        (!h t. LEXISTS' t ==> LEXISTS' (LCONS h t))
        ==> (!a. LEXISTS P a ==> LEXISTS' a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n (l:A llist) x. LNTH n l = SOME x /\ P x ==> LEXISTS' l`
   (fun th -> REWRITE_TAC[LEXISTS_DEF; IN_SET_OF_LLIST] THEN
              MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LNTH; option_DISTINCT; option_INJ] THEN ASM_MESON_TAC[]);;

let MONO_LALL = prove
 (`(!x:A. P x ==> Q x) ==> LALL P l ==> LALL Q l`,
  REWRITE_TAC[LALL_DEF] THEN MESON_TAC[]);;

let MONO_LEXISTS = prove
 (`(!x:A. P x ==> Q x) ==> LEXISTS P l ==> LEXISTS Q l`,
  REWRITE_TAC[LEXISTS_DEF] THEN MESON_TAC[]);;

monotonicity_theorems :=
  [MONO_LALL; MONO_LEXISTS] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* The suffix starting at the first element satisfying P, if there is one.   *)
(* ------------------------------------------------------------------------- *)

let LFIRST_RULES,LFIRST_INDUCT,LFIRST_CASES = new_inductive_definition
 `(!h:A t. P h ==> LFIRST P (LCONS h t) (LCONS h t)) /\
  (!h t l. ~P h /\ LFIRST P t l ==> LFIRST P (LCONS h t) l)`;;

let LFIRST_UNIQUE = prove
 (`!P (l:A llist) l1 l2. LFIRST P l l1 /\ LFIRST P l l2 ==> l1 = l2`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC LFIRST_INDUCT THEN REPEAT STRIP_TAC THEN
  POP_ASSUM(MP_TAC o ONCE_REWRITE_RULE[LFIRST_CASES]) THEN
  REWRITE_TAC[LCONS_11] THEN ASM_MESON_TAC[]);;

let LFIRST_EXISTS = prove
 (`!P (l:A llist). LEXISTS P l ==> ?l'. LFIRST P l l'`,
  GEN_TAC THEN MATCH_MP_TAC LEXISTS_INDUCT THEN MESON_TAC[LFIRST_RULES]);;

let LFIRST_LCONS = prove
 (`!P (l:A llist) l'. LFIRST P l l' ==> ?h t. l' = LCONS h t /\ P h`,
  GEN_TAC THEN MATCH_MP_TAC LFIRST_INDUCT THEN MESON_TAC[]);;

let LFIRST_SUBSET = prove
 (`!P (l:A llist) l'. LFIRST P l l' ==> set_of_llist l' SUBSET set_of_llist l`,
  GEN_TAC THEN MATCH_MP_TAC LFIRST_INDUCT THEN
  REWRITE_TAC[SET_OF_LLIST; SUBSET_REFL] THEN SET_TAC[]);;

let LFIRST_LEXISTS = prove
 (`!P (l:A llist) l'. LFIRST P l l' ==> LEXISTS P l`,
  GEN_TAC THEN MATCH_MP_TAC LFIRST_INDUCT THEN
  SIMP_TAC[LEXISTS]);;

let lfirst = new_definition
 `lfirst P (l:A llist) = @l'. LFIRST P l l'`;;

let LFIRST_LFIRST = prove
 (`!P (l:A llist). LEXISTS P l ==> LFIRST P l (lfirst P l)`,
  REWRITE_TAC[lfirst] THEN MESON_TAC[LFIRST_EXISTS]);;

let LFIRST_EQ = prove
 (`!P (l:A llist) l'. LFIRST P l l' ==> lfirst P l = l'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LFIRST_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`P:A->bool`; `l:A llist`] THEN
  ASM_MESON_TAC[LFIRST_LFIRST; LFIRST_LEXISTS]);;

let LFIRST_LCONS_P = prove
 (`!P (h:A) t. P h ==> lfirst P (LCONS h t) = LCONS h t`,
  MESON_TAC[LFIRST_EQ; LFIRST_RULES]);;

let LFIRST_LCONS_NOTP = prove
 (`!P (h:A) t. ~P h /\ LEXISTS P t ==> lfirst P (LCONS h t) = lfirst P t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LFIRST_EQ THEN
  MATCH_MP_TAC(CONJUNCT2(SPEC_ALL LFIRST_RULES)) THEN
  ASM_SIMP_TAC[LFIRST_LFIRST]);;

(* ------------------------------------------------------------------------- *)
(* Filter. This is not productive, so it is defined by unfolding from the    *)
(* first element that passes, ending when there is none.                     *)
(* ------------------------------------------------------------------------- *)

let LFILTER_DEF = new_definition
 `LFILTER P = LUNFOLD (\l:A llist. ~LEXISTS P l) (\l. LHD (lfirst P l))
                      (\l. LTL (lfirst P l))`;;

let LFILTER_UNFOLD = prove
 (`!P (l:A llist).
        LFILTER P l =
        if ~LEXISTS P l then LNIL
        else LCONS (LHD (lfirst P l)) (LFILTER P (LTL (lfirst P l)))`,
  REWRITE_TAC[LFILTER_DEF] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN REWRITE_TAC[]);;

let LFILTER = prove
 (`(!P:A->bool. LFILTER P LNIL = LNIL) /\
   (!P h:A t. LFILTER P (LCONS h t) =
              if P h then LCONS h (LFILTER P t) else LFILTER P t)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [LFILTER_UNFOLD] THEN
  REWRITE_TAC[LEXISTS] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN
  ASM_SIMP_TAC[LFIRST_LCONS_P; LHD; LTL] THEN
  ASM_CASES_TAC `LEXISTS (P:A->bool) t` THEN
  ASM_SIMP_TAC[LFIRST_LCONS_NOTP] THEN
  GEN_REWRITE_TAC RAND_CONV [LFILTER_UNFOLD] THEN ASM_REWRITE_TAC[]);;

let LFILTER_EQ_LNIL = prove
 (`!P (l:A llist). LFILTER P l = LNIL <=> LALL (\x. ~P x) l`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[LFILTER_UNFOLD] THEN
  REWRITE_TAC[LEXISTS_LALL] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NOT_LCONS_LNIL]);;

let LFILTER_LAPPEND = prove
 (`!P (l1:A llist) l2.
        LFINITE l1
        ==> LFILTER P (LAPPEND l1 l2) = LAPPEND (LFILTER P l1) (LFILTER P l2)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC LFINITE_INDUCT THEN REWRITE_TAC[LAPPEND; LFILTER] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LAPPEND]);;

let LFILTER_LLIST_OF_LIST = prove
 (`!P (l:A list). LFILTER P (llist_of_list l) = llist_of_list (FILTER P l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LLIST_OF_LIST; LFILTER; FILTER] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LLIST_OF_LIST]);;

let SET_OF_LLIST_LFILTER = prove
 (`!P (l:A llist).
        set_of_llist (LFILTER P l) = {x | x IN set_of_llist l /\ P x}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_SET_OF_LLIST; LEFT_IMP_EXISTS_THM] THEN
    SPEC_TAC(`l:A llist`,`l:A llist`) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[LFILTER_UNFOLD] THEN COND_CASES_TAC THEN
    REWRITE_TAC[LNTH; option_DISTINCT; option_INJ] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LFIRST_LFIRST o REWRITE_RULE[]) THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP LFIRST_SUBSET th) THEN
                         MP_TAC(MATCH_MP LFIRST_LCONS th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LHD; LTL; SUBSET; SET_OF_LLIST;
                                   IN_INSERT; GSYM IN_SET_OF_LLIST] THEN
    REWRITE_TAC[IN_SET_OF_LLIST] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_SET_OF_LLIST] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`l:A llist`,`l:A llist`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
    REWRITE_TAC[LNTH; LFILTER; option_DISTINCT; option_INJ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[LNTH_LCONS_EXISTS] THEN ASM_MESON_TAC[]]);;

let LALL_LFILTER = prove
 (`!P (l:A llist). LALL P (LFILTER P l)`,
  REWRITE_TAC[LALL_DEF; SET_OF_LLIST_LFILTER; IN_ELIM_THM] THEN MESON_TAC[]);;

let LFILTER_LFILTER = prove
 (`!P Q (l:A llist). LFILTER P (LFILTER Q l) = LFILTER (\x. P x /\ Q x) l`,
  LLIST_COINDUCT_TAC THEN ASM_CASES_TAC `LEXISTS (\x:A. P x /\ Q x) l` THENL
   [ALL_TAC;
    DISJ1_TAC THEN REWRITE_TAC[LFILTER_EQ_LNIL; LALL_DEF] THEN
    REWRITE_TAC[SET_OF_LLIST_LFILTER; IN_ELIM_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LEXISTS_DEF]) THEN ASM_MESON_TAC[]] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:A llist`,`l:A llist`) THEN
  MATCH_MP_TAC LEXISTS_INDUCT THEN REWRITE_TAC[] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN ASM_CASES_TAC `(Q:A->bool) h` THEN
  ASM_REWRITE_TAC[LFILTER] THEN LLIST_BISIM_TAC THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Flatten, also not productive, unfolding from the first nonempty llist.    *)
(* ------------------------------------------------------------------------- *)

let LFLATTEN_DEF = new_definition
 `LFLATTEN =
  LUNFOLD (\ls:(A llist) llist. ~LEXISTS (\l. ~(l = LNIL)) ls)
          (\ls. LHD (LHD (lfirst (\l. ~(l = LNIL)) ls)))
          (\ls. LCONS (LTL (LHD (lfirst (\l. ~(l = LNIL)) ls)))
                      (LTL (lfirst (\l. ~(l = LNIL)) ls)))`;;

let LFLATTEN_UNFOLD = prove
 (`!ls:(A llist) llist.
        LFLATTEN ls =
        if ~LEXISTS (\l. ~(l = LNIL)) ls then LNIL
        else LCONS (LHD (LHD (lfirst (\l. ~(l = LNIL)) ls)))
                   (LFLATTEN (LCONS (LTL (LHD (lfirst (\l. ~(l = LNIL)) ls)))
                                    (LTL (lfirst (\l. ~(l = LNIL)) ls))))`,
  REWRITE_TAC[LFLATTEN_DEF] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN REWRITE_TAC[]);;

let LFLATTEN = prove
 (`LFLATTEN (LNIL:(A llist) llist) = LNIL /\
   (!ls:(A llist) llist. LFLATTEN (LCONS LNIL ls) = LFLATTEN ls) /\
   (!(h:A) t ls. LFLATTEN (LCONS (LCONS h t) ls) =
                 LCONS h (LFLATTEN (LCONS t ls)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [LFLATTEN_UNFOLD] THEN
  REWRITE_TAC[LEXISTS; NOT_LCONS_LNIL] THEN
  SIMP_TAC[LFIRST_LCONS_P; NOT_LCONS_LNIL; LHD; LTL] THEN
  ASM_CASES_TAC `LEXISTS (\l:A llist. ~(l = LNIL)) ls` THEN
  ASM_SIMP_TAC[LFIRST_LCONS_NOTP] THEN
  GEN_REWRITE_TAC RAND_CONV [LFLATTEN_UNFOLD] THEN ASM_REWRITE_TAC[]);;

let LFLATTEN_EQ_LNIL = prove
 (`!ls:(A llist) llist. LFLATTEN ls = LNIL <=> LALL (\l. l = LNIL) ls`,
  GEN_TAC THEN ONCE_REWRITE_TAC[LFLATTEN_UNFOLD] THEN
  REWRITE_TAC[LEXISTS_LALL] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NOT_LCONS_LNIL] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]);;

let LFLATTEN_INFINITE = prove
 (`!(l:A llist) ls. ~LFINITE l ==> LFLATTEN (LCONS l ls) = l`,
  LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC `l:A llist` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LFINITE_RULES; LFINITE_LCONS]) THEN
  ASM_REWRITE_TAC[LFLATTEN] THEN LLIST_BISIM_TAC THEN ASM_MESON_TAC[]);;

let LFLATTEN_LCONS = prove
 (`!(l:A llist) ls. LFLATTEN (LCONS l ls) = LAPPEND l (LFLATTEN ls)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LFINITE (l:A llist)` THEN
  ASM_SIMP_TAC[LFLATTEN_INFINITE; LAPPEND_INFINITE] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:A llist`,`l:A llist`) THEN
  MATCH_MP_TAC LFINITE_INDUCT THEN ASM_SIMP_TAC[LFLATTEN; LAPPEND]);;

let LMAP_LFLATTEN = prove
 (`!(f:A->B) ls. LMAP f (LFLATTEN ls) = LFLATTEN (LMAP (LMAP f) ls)`,
  LLIST_COINDUCT_TAC THEN
  ASM_CASES_TAC `LEXISTS (\l:A llist. ~(l = LNIL)) ls` THENL
   [ALL_TAC;
    DISJ1_TAC THEN REWRITE_TAC[LMAP_EQ_LNIL; LFLATTEN_EQ_LNIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LEXISTS_LALL]) THEN
    ASM_REWRITE_TAC[LALL_LMAP; o_DEF; LMAP_EQ_LNIL]] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ls:(A llist) llist`,`ls:(A llist) llist`) THEN
  MATCH_MP_TAC LEXISTS_INDUCT THEN REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`l:A llist`; `ls:(A llist) llist`] THEN
  LLIST_CASES_TAC `l:A llist` THEN
  REWRITE_TAC[LMAP; LFLATTEN; NOT_LCONS_LNIL] THEN
  LLIST_BISIM_TAC THEN MESON_TAC[LMAP]);;

(* ------------------------------------------------------------------------- *)
(* Zip, by corecursion.                                                      *)
(* ------------------------------------------------------------------------- *)

let LZIP_DEF = new_definition
 `LZIP (l1:A llist) (l2:B llist) =
  LUNFOLD (\p:A llist#B llist. FST p = LNIL \/ SND p = LNIL)
          (\p. LHD (FST p),LHD (SND p)) (\p. LTL (FST p),LTL (SND p))
          (l1,l2)`;;

let LZIP = prove
 (`(!l:B llist. LZIP (LNIL:A llist) l = LNIL) /\
   (!(h:A) t. LZIP (LCONS h t) (LNIL:B llist) = LNIL) /\
   (!(h1:A) t1 (h2:B) t2.
        LZIP (LCONS h1 t1) (LCONS h2 t2) = LCONS (h1,h2) (LZIP t1 t2))`,
  REWRITE_TAC[LZIP_DEF] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN
  REWRITE_TAC[FST; SND; NOT_LCONS_LNIL; LHD; LTL]);;

let LNTH_LZIP = prove
 (`!(l1:A llist) (l2:B llist) n x y.
        LNTH n (LZIP l1 l2) = SOME (x,y) <=>
        LNTH n l1 = SOME x /\ LNTH n l2 = SOME y`,
  SUBGOAL_THEN
   `!n (l1:A llist) (l2:B llist) x y.
        LNTH n (LZIP l1 l2) = SOME (x,y) <=>
        LNTH n l1 = SOME x /\ LNTH n l2 = SOME y`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  LLIST_CASES_TAC `l1:A llist` THEN LLIST_CASES_TAC `l2:B llist` THEN
  ASM_REWRITE_TAC[LZIP; LNTH; option_DISTINCT; GSYM option_DISTINCT;
                  option_INJ; PAIR_EQ]);;

let LZIP_LMAP = prove
 (`!(f:A->C) (g:B->D) l1 l2.
        LZIP (LMAP f l1) (LMAP g l2) = LMAP (\(x,y). (f x,g y)) (LZIP l1 l2)`,
  LLIST_COINDUCT_TAC THEN
  LLIST_CASES_TAC `l1:A llist` THEN LLIST_CASES_TAC `l2:B llist` THEN
  REWRITE_TAC[LZIP; LMAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  LLIST_BISIM_TAC THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The relator, by cases on the representation, with its coinduction.        *)
(* ------------------------------------------------------------------------- *)

let LALL2_DEF = define
 `(LALL2 R (llist_of_list l1) (llist_of_list l2) <=>
   ALL2 R (l1:A list) (l2:B list)) /\
  (LALL2 R (llist_of_list l1) (llist_of_seq (g:num->B)) <=> F) /\
  (LALL2 R (llist_of_seq (f:num->A)) (llist_of_list l2) <=> F) /\
  (LALL2 R (llist_of_seq f) (llist_of_seq g) <=> !n. R (f n) (g n))`;;

let LALL2 = prove
 (`(!R:A->B->bool. LALL2 R LNIL LNIL) /\
   (!R:A->B->bool h1 t1. ~LALL2 R (LCONS h1 t1) LNIL) /\
   (!R:A->B->bool h2 t2. ~LALL2 R LNIL (LCONS h2 t2)) /\
   (!R:A->B->bool h1 t1 h2 t2.
        LALL2 R (LCONS h1 t1) (LCONS h2 t2) <=> R h1 h2 /\ LALL2 R t1 t2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[LNIL_DEF; LALL2_DEF; ALL2];
    LLIST_REP_CASES_TAC `t1:A llist` THEN
    REWRITE_TAC[LNIL_DEF; LCONS_DEF; LALL2_DEF; ALL2];
    LLIST_REP_CASES_TAC `t2:B llist` THEN
    REWRITE_TAC[LNIL_DEF; LCONS_DEF; LALL2_DEF; ALL2];
    LLIST_REP_CASES_TAC `t1:A llist` THEN LLIST_REP_CASES_TAC `t2:B llist` THEN
    REWRITE_TAC[LCONS_DEF; LALL2_DEF; ALL2] THEN
    GEN_REWRITE_TAC LAND_CONV [MESON[num_CASES]
     `(!n. P n) <=> P 0 /\ !n. P(SUC n)`] THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1]]);;

let LALL2_EQ = prove
 (`!l1 l2:A llist. LALL2 (=) l1 l2 <=> l1 = l2`,
  let lemma = prove
   (`!l1 l2:A list. ALL2 (=) l1 l2 <=> l1 = l2`,
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[ALL2; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL]) in
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  LLIST_REP_CASES_TAC `l2:A llist` THEN
  REWRITE_TAC[LALL2_DEF; LLIST_REP_EQ; lemma; FUN_EQ_THM]);;

let LALL2_LNTH = prove
 (`!R (l1:A llist) (l2:B llist).
        LALL2 R l1 l2 <=>
        LLENGTH l1 = LLENGTH l2 /\
        !n x y. LNTH n l1 = SOME x /\ LNTH n l2 = SOME y ==> R x y`,
  let lemma = prove
   (`!R (l1:A list) (l2:B list).
        ALL2 R l1 l2 <=>
        LENGTH l1 = LENGTH l2 /\
        !n. n < LENGTH l1 ==> R (EL n l1) (EL n l2)`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[ALL2; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ;
                    CONJUNCT1 LT; LT_0] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [MESON[num_CASES] `(!n. P n) <=> P 0 /\ !n. P(SUC n)`] THEN
    REWRITE_TAC[LT_0; LT_SUC; EL; HD; TL] THEN CONV_TAC TAUT)
  and lemma' = prove
   (`!b (a:A) c. (if b then SOME a else NONE) = SOME c <=> b /\ a = c`,
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_INJ; GSYM option_DISTINCT]) in
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  LLIST_REP_CASES_TAC `l2:B llist` THEN
  REWRITE_TAC[LALL2_DEF; LLENGTH_DEF; LNTH_DEF; lemma'; option_INJ;
              option_DISTINCT; GSYM option_DISTINCT; lemma] THEN
  MESON_TAC[]);;

let LLENGTH_EQ = prove
 (`!(l1:A llist) (l2:B llist).
        LLENGTH l1 = LLENGTH l2 <=> !n. LNTH n l1 = NONE <=> LNTH n l2 = NONE`,
  let lemma = prove
   (`!(l:A list) n. LNTH n (llist_of_list l) = NONE <=> LENGTH l <= n`,
    REWRITE_TAC[LNTH_DEF; GSYM NOT_LT] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]) in
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  LLIST_REP_CASES_TAC `l2:B llist` THEN
  REWRITE_TAC[LLENGTH_DEF; lemma; LNTH_DEF; option_INJ; option_DISTINCT;
              GSYM option_DISTINCT] THEN
  MESON_TAC[LE_REFL; LE_ANTISYM]);;

let LALL2_COINDUCT = prove
 (`!R (R':A llist->B llist->bool).
        (!l1 l2. R' l1 l2
                 ==> l1 = LNIL /\ l2 = LNIL \/
                     ?h1 t1 h2 t2. l1 = LCONS h1 t1 /\ l2 = LCONS h2 t2 /\
                                   R h1 h2 /\ R' t1 t2)
        ==> !l1 l2. R' l1 l2 ==> LALL2 R l1 l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun bisim ->
    REWRITE_TAC[LALL2_LNTH; LLENGTH_EQ] THEN
    SUBGOAL_THEN
     `!n (l1:A llist) (l2:B llist).
        R' l1 l2
        ==> (LNTH n l1 = NONE <=> LNTH n l2 = NONE) /\
            (!x y. LNTH n l1 = SOME x /\ LNTH n l2 = SOME y ==> R x y)`
     (fun th -> MESON_TAC[th]) THEN
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP bisim) THEN
    ASM_REWRITE_TAC[LNTH; option_DISTINCT; GSYM option_DISTINCT;
                    option_INJ] THEN
    ASM_MESON_TAC[]));;

let MONO_LALL2 = prove
 (`(!x y. (P:A->B->bool) x y ==> Q x y) ==> LALL2 P l l' ==> LALL2 Q l l'`,
  REWRITE_TAC[LALL2_LNTH] THEN MESON_TAC[]);;

monotonicity_theorems := MONO_LALL2 :: !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* The prefix order, defined as having a continuation, with its              *)
(* coinduction principle. Every chain has a least upper bound.               *)
(* ------------------------------------------------------------------------- *)

let LPREFIX_DEF = new_definition
 `LPREFIX (l1:A llist) l2 <=> ?l3. l2 = LAPPEND l1 l3`;;

let LPREFIX = prove
 (`(!l:A llist. LPREFIX LNIL l) /\
   (!(h:A) t l.
        LPREFIX (LCONS h t) l <=> ?t'. l = LCONS h t' /\ LPREFIX t t')`,
  REWRITE_TAC[LPREFIX_DEF; LAPPEND] THEN MESON_TAC[]);;

let LPREFIX_LAPPEND = prove
 (`!l1 l2:A llist. LPREFIX l1 l2 <=> ?l3. l2 = LAPPEND l1 l3`,
  REWRITE_TAC[LPREFIX_DEF]);;

let LPREFIX_REFL = prove
 (`!l:A llist. LPREFIX l l`,
  MESON_TAC[LPREFIX_DEF; LAPPEND_LNIL]);;

let LPREFIX_TRANS = prove
 (`!l1 l2 l3:A llist. LPREFIX l1 l2 /\ LPREFIX l2 l3 ==> LPREFIX l1 l3`,
  MESON_TAC[LPREFIX_DEF; LAPPEND_ASSOC]);;

let LPREFIX_LTAKE = prove
 (`!n (l:A llist). LPREFIX (llist_of_list (LTAKE n l)) l`,
  MESON_TAC[LPREFIX_DEF; LTAKE_LDROP]);;

let LPREFIX_LNTH = prove
 (`!l1 l2:A llist.
        LPREFIX l1 l2 <=> !n x. LNTH n l1 = SOME x ==> LNTH n l2 = SOME x`,
  let lemma = prove
   (`!b (a:A) c. (if b then SOME a else NONE) = SOME c <=> b /\ a = c`,
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_INJ; GSYM option_DISTINCT]) in
  REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC `l1:A llist` THEN
  REWRITE_TAC[LPREFIX_DEF; LAPPEND_DEF] THENL
   [EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[LNTH_LAPPEND] THEN
      REWRITE_TAC[LNTH_DEF; lemma] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `LDROP (LENGTH (xs:A list)) (l2:A llist)` THEN
      REWRITE_TAC[LLIST_EQ; LNTH_LAPPEND; LNTH_LDROP] THEN
      X_GEN_TAC `n:num` THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `EL n (xs:A list)`]) THEN
        ASM_REWRITE_TAC[LNTH_DEF];
        AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LNTH_DEF; option_INJ];
      REWRITE_TAC[LNTH_DEF; option_INJ] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[LLIST_EQ; LNTH_DEF] THEN ASM_MESON_TAC[]]]);;

let LPREFIX_ANTISYM = prove
 (`!l1 l2:A llist. LPREFIX l1 l2 /\ LPREFIX l2 l1 ==> l1 = l2`,
  REWRITE_TAC[LPREFIX_LNTH; LLIST_EQ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `LNTH n (l1:A llist)` option_CASES) THEN
  MP_TAC(ISPEC `LNTH n (l2:A llist)` option_CASES) THEN
  ASM_MESON_TAC[]);;

let LPREFIX_COINDUCT = prove
 (`!R:A llist->A llist->bool.
        (!l1 l2. R l1 l2
                 ==> l1 = LNIL \/
                     ?h t1 t2. l1 = LCONS h t1 /\ l2 = LCONS h t2 /\ R t1 t2)
        ==> !l1 l2. R l1 l2 ==> LPREFIX l1 l2`,
  GEN_TAC THEN DISCH_THEN(fun bisim ->
    REWRITE_TAC[LPREFIX_LNTH] THEN
    SUBGOAL_THEN
     `!n (l1:A llist) l2 x.
        R l1 l2 /\ LNTH n l1 = SOME x ==> LNTH n l2 = SOME x`
     (fun th -> MESON_TAC[th]) THEN
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP bisim) MP_TAC) THEN
    ASM_REWRITE_TAC[LNTH; option_DISTINCT] THEN ASM_MESON_TAC[]));;

let LLIST_OF_LNTH = prove
 (`!f:num->A option.
        (!m n. f m = NONE /\ m <= n ==> f n = NONE)
        ==> ?l. !n. LNTH n l = f n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `?n. (f:num->A option) n = NONE` THENL
   [EXISTS_TAC `llist_of_list (list_of_seq (\i. THE((f:num->A option) i))
                                ((minimal) (\n. f n = NONE)))` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
    SPEC_TAC(`(minimal) (\n. (f:num->A option) n = NONE)`,`k:num`) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[LNTH_DEF; LENGTH_LIST_OF_SEQ] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THENL
     [MP_TAC(ISPEC `(f:num->A option) n` option_CASES) THEN
      ASM_MESON_TAC[THE];
      ASM_MESON_TAC[NOT_LT]];
    EXISTS_TAC `llist_of_seq (\i. THE((f:num->A option) i))` THEN
    REWRITE_TAC[LNTH_DEF] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `(f:num->A option) n` option_CASES) THEN
    ASM_MESON_TAC[THE]]);;

let LPREFIX_CHAIN_LUB = prove
 (`!s:A llist->bool.
        (!l1 l2. l1 IN s /\ l2 IN s ==> LPREFIX l1 l2 \/ LPREFIX l2 l1)
        ==> ?u. (!l. l IN s ==> LPREFIX l u) /\
                (!u'. (!l. l IN s ==> LPREFIX l u') ==> LPREFIX u u')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n l1 l2 (x1:A) x2. l1 IN s /\ l2 IN s /\
                        LNTH n l1 = SOME x1 /\ LNTH n l2 = SOME x2 ==> x1 = x2`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[LPREFIX_LNTH; option_INJ]; ALL_TAC] THEN
  MP_TAC(ISPEC
   `\n. if ?l (x:A). l IN s /\ LNTH n l = SOME x
        then SOME (@x. ?l. l IN s /\ LNTH n l = SOME x) else NONE`
   LLIST_OF_LNTH) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[LNTH_NONE_MONO; option_CASES; option_DISTINCT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:A llist`) THEN EXISTS_TAC `u:A llist` THEN
  ASM_REWRITE_TAC[LPREFIX_LNTH] THEN CONJ_TAC THENL
   [X_GEN_TAC `l:A llist` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[option_INJ] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `u':A llist` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[GSYM option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `?l. l IN s /\ LNTH n l = SOME (@x:A. ?l. l IN s /\ LNTH n l = SOME x)`
     MP_TAC THENL [CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let LPREFIX_LTAKE_LUB = prove
 (`!(l:A llist) u.
        (!n. LPREFIX (llist_of_list (LTAKE n l)) u) ==> LPREFIX l u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LPREFIX_LNTH] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LPREFIX_LNTH] o SPEC `SUC n`) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LNTH_LTAKE]);;

(* ------------------------------------------------------------------------- *)
(* The infinite llist of iterates x, f x, f (f x), ...                       *)
(* ------------------------------------------------------------------------- *)

let LITERATE_DEF = new_definition
 `LITERATE (f:A->A) x = llist_of_seq (\n. ITER n f x)`;;

let LITERATE = prove
 (`!(f:A->A) x. LITERATE f x = LCONS x (LITERATE f (f x))`,
  REWRITE_TAC[LITERATE_DEF] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [LLIST_OF_SEQ] THEN REWRITE_TAC[ITER_ALT]);;

let LFINITE_LITERATE = prove
 (`!(f:A->A) x. ~LFINITE (LITERATE f x)`,
  REWRITE_TAC[LITERATE_DEF; LFINITE_DEF]);;

let LMAP_LITERATE = prove
 (`!(f:A->A) x. LMAP f (LITERATE f x) = LITERATE f (f x)`,
  REWRITE_TAC[LITERATE_DEF; LMAP_DEF; LLIST_REP_EQ; FUN_EQ_THM; o_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER); ITER_ALT]);;
