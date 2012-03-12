(* ========================================================================= *)
(* Basic notions of cardinal arithmetic.                                     *)
(* ========================================================================= *)

needs "Library/wo.ml";;

(* ------------------------------------------------------------------------- *)
(* We need these a few times, so give them names.                            *)
(* ------------------------------------------------------------------------- *)

let sum_DISTINCT = distinctness "sum";;

let sum_INJECTIVE = injectivity "sum";;

let sum_CASES = prove_cases_thm sum_INDUCT;;

let FORALL_SUM_THM = prove
 (`(!z. P z) <=> (!x. P(INL x)) /\ (!x. P(INR x))`,
  MESON_TAC[sum_CASES]);;

let EXISTS_SUM_THM = prove
 (`(?z. P z) <=> (?x. P(INL x)) \/ (?x. P(INR x))`,
  MESON_TAC[sum_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Special case of Zorn's Lemma for restriction of subset lattice.           *)
(* ------------------------------------------------------------------------- *)

let POSET_RESTRICTED_SUBSET = prove
 (`!P. poset(\(x,y). P(x) /\ P(y) /\ x SUBSET y)`,
  GEN_TAC THEN REWRITE_TAC[poset; fl] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SUBSET; EXTENSION] THEN MESON_TAC[]);;

let FL_RESTRICTED_SUBSET = prove
 (`!P. fl(\(x,y). P(x) /\ P(y) /\ x SUBSET y) = P`,
  REWRITE_TAC[fl; FORALL_PAIR_THM; FUN_EQ_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[SUBSET_REFL]);;

let ZL_SUBSETS = prove
 (`!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> ?z. P z /\ (!x. x IN c ==> x SUBSET z))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\(x,y). P(x:A->bool) /\ P(y) /\ x SUBSET y` ZL) THEN
  REWRITE_TAC[POSET_RESTRICTED_SUBSET; FL_RESTRICTED_SUBSET] THEN
  REWRITE_TAC[chain] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[IN] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL; ALL_TAC] THEN
  MESON_TAC[]);;

let ZL_SUBSETS_UNIONS = prove
 (`!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> P(UNIONS c))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `UNIONS(c:(A->bool)->bool)` THEN
  ASM_MESON_TAC[SUBSET; IN_UNIONS]);;

let ZL_SUBSETS_UNIONS_NONEMPTY = prove
 (`!P. (?x. P x) /\
       (!c. (?x. x IN c) /\
            (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> P(UNIONS c))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `?x:A->bool. x IN c` THENL
   [EXISTS_TAC `UNIONS(c:(A->bool)->bool)` THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[SUBSET; IN_UNIONS];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Useful lemma to reduce some higher order stuff to first order.            *)
(* ------------------------------------------------------------------------- *)

let FLATTEN_LEMMA = prove
 (`(!x. x IN s ==> (g(f(x)) = x)) <=> !y x. x IN s /\ (y = f x) ==> (g y = x)`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Knaster-Tarski fixpoint theorem (used in Schroeder-Bernstein below).      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_SET = prove
 (`!f. (!s t. s SUBSET t ==> f(s) SUBSET f(t)) ==> ?s:A->bool. f(s) = s`,
  REPEAT STRIP_TAC THEN MAP_EVERY ABBREV_TAC
   [`Y = {b:A->bool | f(b) SUBSET b}`; `a:A->bool = INTERS Y`] THEN
  SUBGOAL_THEN `!b:A->bool. b IN Y <=> f(b) SUBSET b` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:A->bool. b IN Y ==> f(a:A->bool) SUBSET b` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; IN_INTERS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `f(a:A->bool) SUBSET a`
   (fun th -> ASM_MESON_TAC[SUBSET_ANTISYM; IN_INTERS; th]) THEN
  ASM_MESON_TAC[IN_INTERS; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* We need a nonemptiness hypothesis for the nicest total function form.     *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_LEFT_INVERSE_NONEMPTY = prove
 (`(?x. x IN s)
   ==> ((!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) <=>
        ?g. (!y. y IN t ==> g(y) IN s) /\
            (!x. x IN s ==> (g(f(x)) = x)))`,
  REWRITE_TAC[FLATTEN_LEMMA; GSYM SKOLEM_THM; AND_FORALL_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Now bijectivity.                                                          *)
(* ------------------------------------------------------------------------- *)

let BIJECTIVE_INJECTIVE_SURJECTIVE = prove
 (`(!x. x IN s ==> f(x) IN t) /\
   (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) <=>
   (!x. x IN s ==> f(x) IN t) /\
   (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
   (!y. y IN t ==> ?x. x IN s /\ (f x = y))`,
  MESON_TAC[]);;

let BIJECTIVE_INVERSES = prove
 (`(!x. x IN s ==> f(x) IN t) /\
   (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) <=>
   (!x. x IN s ==> f(x) IN t) /\
   ?g. (!y. y IN t ==> g(y) IN s) /\
       (!y. y IN t ==> (f(g(y)) = y)) /\
       (!x. x IN s ==> (g(f(x)) = x))`,
  REWRITE_TAC[BIJECTIVE_INJECTIVE_SURJECTIVE;
              INJECTIVE_ON_LEFT_INVERSE;
              SURJECTIVE_ON_RIGHT_INVERSE] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Relational variant of =_c is sometimes useful.                            *)
(* ------------------------------------------------------------------------- *)

let EQ_C = prove
 (`s =_c t <=>
   ?R:A#B->bool. (!x y. R(x,y) ==> x IN s /\ y IN t) /\
                 (!x. x IN s ==> ?!y. y IN t /\ R(x,y)) /\
                 (!y. y IN t ==> ?!x. x IN s /\ R(x,y))`,
  REWRITE_TAC[eq_c] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\(x:A,y:B). x IN s /\ y IN t /\ (y = f x)` THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [EXISTS_UNIQUE_ALT; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The "easy" ordering properties.                                           *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_REFL = prove
 (`!s:A->bool. s <=_c s`,
  GEN_TAC THEN REWRITE_TAC[le_c] THEN EXISTS_TAC `\x:A. x` THEN SIMP_TAC[]);;

let CARD_LE_TRANS = prove
 (`!s:A->bool t:B->bool u:C->bool.
       s <=_c t /\ t <=_c u ==> s <=_c u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `f:A->B`) (X_CHOOSE_TAC `g:B->C`)) THEN
  EXISTS_TAC `(g:B->C) o (f:A->B)` THEN REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[]);;

let CARD_LT_REFL = prove
 (`!s:A->bool. ~(s <_c s)`,
  MESON_TAC[lt_c; CARD_LE_REFL]);;

let CARD_LET_TRANS = prove
 (`!s:A->bool t:B->bool u:C->bool.
       s <=_c t /\ t <_c u ==> s <_c u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lt_c] THEN
  MATCH_MP_TAC(TAUT `(a /\ b ==> c) /\ (c' /\ a ==> b')
                     ==> a /\ b /\ ~b' ==> c /\ ~c'`) THEN
  REWRITE_TAC[CARD_LE_TRANS]);;

let CARD_LTE_TRANS = prove
 (`!s:A->bool t:B->bool u:C->bool.
       s <_c t /\ t <=_c u ==> s <_c u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lt_c] THEN
  MATCH_MP_TAC(TAUT `(a /\ b ==> c) /\ (b /\ c' ==> a')
                     ==> (a /\ ~a') /\ b ==> c /\ ~c'`) THEN
  REWRITE_TAC[CARD_LE_TRANS]);;

let CARD_LT_TRANS = prove
 (`!s:A->bool t:B->bool u:C->bool.
       s <_c t /\ t <_c u ==> s <_c u`,
  MESON_TAC[lt_c; CARD_LTE_TRANS]);;

let CARD_EQ_REFL = prove
 (`!s:A->bool. s =_c s`,
  GEN_TAC THEN REWRITE_TAC[eq_c] THEN EXISTS_TAC `\x:A. x` THEN
  SIMP_TAC[] THEN MESON_TAC[]);;

let CARD_EQ_SYM = prove
 (`!s t. s =_c t <=> t =_c s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c; BIJECTIVE_INVERSES] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN REWRITE_TAC[CONJ_ACI]);;

let CARD_EQ_IMP_LE = prove
 (`!s t. s =_c t ==> s <=_c t`,
  REWRITE_TAC[le_c; eq_c] THEN MESON_TAC[]);;

let CARD_LT_IMP_LE = prove
 (`!s t. s <_c t ==> s <=_c t`,
  SIMP_TAC[lt_c]);;

(* ------------------------------------------------------------------------- *)
(* Two trivial lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_EMPTY = prove
 (`!s. (s <=_c EMPTY) <=> (s = EMPTY)`,
  REWRITE_TAC[le_c; EXTENSION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let CARD_EQ_EMPTY = prove
 (`!s. (s =_c EMPTY) <=> (s = EMPTY)`,
  REWRITE_TAC[eq_c; EXTENSION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Antisymmetry (the Schroeder-Bernstein theorem).                           *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_ANTISYM = prove
 (`!s:A->bool t:B->bool. s <=_c t /\ t <=_c s <=> (s =_c t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CARD_EQ_IMP_LE] THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    SIMP_TAC[CARD_EQ_IMP_LE]] THEN
  ASM_CASES_TAC `s:A->bool = EMPTY` THEN ASM_CASES_TAC `t:B->bool = EMPTY` THEN
  ASM_SIMP_TAC[CARD_LE_EMPTY; CARD_EQ_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM]) THEN
  ASM_SIMP_TAC[le_c; eq_c; INJECTIVE_LEFT_INVERSE_NONEMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `i:A->B`
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i':B->A` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `j:B->A`
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `j':A->B` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC
    `\a. s DIFF (IMAGE (j:B->A) (t DIFF (IMAGE (i:A->B) a)))`
    TARSKI_SET) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A->bool` ASSUME_TAC) THEN
  REWRITE_TAC[BIJECTIVE_INVERSES] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  EXISTS_TAC `\x. if x IN a then (i:A->B)(x) else j'(x)` THEN
  EXISTS_TAC `\y. if y IN (IMAGE (i:A->B) a) then i'(y) else (j:B->A)(y)` THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_DEF] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> (a /\ d) /\ (b /\ c)`] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x:A IN a`;
    X_GEN_TAC `y:B` THEN ASM_CASES_TAC `y IN IMAGE (i:A->B) a`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXTENSION; IN_UNIV; IN_DIFF; IN_IMAGE]) THEN
  TRY(FIRST_X_ASSUM(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
  TRY(FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:A` th) THEN
      ASM_REWRITE_TAC[] THEN ASSUME_TAC th)) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Totality (cardinal comparability).                                        *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_TOTAL = prove
 (`!s:A->bool t:B->bool. s <=_c t \/ t <=_c s`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
   `P = \R. (!x:A y:B. R(x,y) ==> x IN s /\ y IN t) /\
            (!x y y'. R(x,y) /\ R(x,y') ==> (y = y')) /\
            (!x x' y. R(x,y) /\ R(x',y) ==> (x = x'))` THEN
  MP_TAC(ISPEC `P:((A#B)->bool)->bool` ZL_SUBSETS_UNIONS) THEN ANTS_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:A#B->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(!x:A. x IN s ==> ?y:B. y IN t /\ R(x,y)) \/
                 (!y:B. y IN t ==> ?x:A. x IN s /\ R(x,y))`
  THENL
   [FIRST_X_ASSUM(K ALL_TAC o SPEC `\(x:A,y:B). T`) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; le_c] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (X_CHOOSE_TAC `b:B`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `\(x:A,y:B). (x = a) /\ (y = b) \/ R(x,y)`) THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN; EXTENSION] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MATCH_MP_TAC th THEN EXISTS_TAC tm for polymorphic transitivity theorem.  *)
(* ------------------------------------------------------------------------- *)

let TRANS_TAC th =
  let ctm = snd(strip_forall(concl th)) in
  let cl,cr = dest_conj(lhand ctm) in
  let x = lhand cl and y = rand cl and z = rand cr in
  fun tm (asl,w as gl) ->
    let lop,r = dest_comb w in
    let op,l = dest_comb lop in
    let ilist =
      itlist2 type_match (map type_of [x;y;z])(map type_of [l;tm;r]) [] in
    let th' = INST_TYPE ilist th in
    (MATCH_MP_TAC th' THEN EXISTS_TAC tm) gl;;

let TRANS_CHAIN_TAC th =
  MAP_EVERY (fun t -> TRANS_TAC th t THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Other variants like "trichotomy of cardinals" now follow easily.          *)
(* ------------------------------------------------------------------------- *)

let CARD_LET_TOTAL = prove
 (`!s:A->bool t:B->bool. s <=_c t \/ t <_c s`,
  REWRITE_TAC[lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);;

let CARD_LTE_TOTAL = prove
 (`!s:A->bool t:B->bool. s <_c t \/ t <=_c s`,
  REWRITE_TAC[lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);;

let CARD_LT_TOTAL = prove
 (`!s:A->bool t:B->bool. s =_c t \/ s <_c t \/ t <_c s`,
  REWRITE_TAC[lt_c; GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_TOTAL]);;

let CARD_NOT_LE = prove
 (`!s:A->bool t:B->bool. ~(s <=_c t) <=> t <_c s`,
  REWRITE_TAC[lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);;

let CARD_NOT_LT = prove
 (`!s:A->bool t:B->bool. ~(s <_c t) <=> t <=_c s`,
  REWRITE_TAC[lt_c] THEN MESON_TAC[CARD_LE_TOTAL]);;

let CARD_LT_LE = prove
 (`!s t. s <_c t <=> s <=_c t /\ ~(s =_c t)`,
  REWRITE_TAC[lt_c; GSYM CARD_LE_ANTISYM] THEN CONV_TAC TAUT);;

let CARD_LE_LT = prove
 (`!s t. s <=_c t <=> s <_c t \/ s =_c t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CARD_NOT_LT] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CARD_LT_LE] THEN
  REWRITE_TAC[DE_MORGAN_THM; CARD_NOT_LE; CARD_EQ_SYM]);;

let CARD_LE_CONG = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> (s <=_c t <=> s' <=_c t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN
  MATCH_MP_TAC(TAUT
   `!x y. (b /\ e ==> x) /\ (x /\ c ==> f) /\ (a /\ f ==> y) /\ (y /\ d ==> e)
          ==> (a /\ b) /\ (c /\ d) ==> (e <=> f)`) THEN
  MAP_EVERY EXISTS_TAC
   [`(s':B->bool) <=_c (t:C->bool)`;
    `(s:A->bool) <=_c (t':D->bool)`] THEN
  REWRITE_TAC[CARD_LE_TRANS]);;

let CARD_LT_CONG = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> (s <_c t <=> s' <_c t')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_NOT_LE] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CARD_LE_CONG THEN
  ASM_REWRITE_TAC[]);;

let CARD_EQ_TRANS = prove
 (`!s:A->bool t:B->bool u:C->bool.
       s =_c t /\ t =_c u ==> s =_c u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CARD_LE_TRANS]);;

let CARD_EQ_CONG = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> (s =_c t <=> s' =_c t')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [TRANS_CHAIN_TAC CARD_EQ_TRANS [`t:C->bool`; `s:A->bool`];
    TRANS_CHAIN_TAC CARD_EQ_TRANS [`s':B->bool`; `t':D->bool`]] THEN
  ASM_MESON_TAC[CARD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness and infiniteness in terms of cardinality of N.                 *)
(* ------------------------------------------------------------------------- *)

let INFINITE_CARD_LE = prove
 (`!s:A->bool. INFINITE s <=> (UNIV:num->bool) <=_c s`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[INFINITE; le_c; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INFINITE_IMAGE_INJ) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP num_INFINITE) THEN
    REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
    ASM_SIMP_TAC[SUBSET; IN_IMAGE; IN_UNIV; LEFT_IMP_EXISTS_THM]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?f:num->A. !n. f(n) = @x. x IN (s DIFF IMAGE f {m | m < n})`
  MP_TAC THENL
   [MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[le_c] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:num->A` THEN REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. (f:num->A)(n) IN (s DIFF IMAGE f {m | m < n})` MP_TAC THENL
   [GEN_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
    REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    MATCH_MP_TAC INFINITE_NONEMPTY THEN MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[LT_CASES]);;

let FINITE_CARD_LT = prove
 (`!s:A->bool. FINITE s <=> s <_c (UNIV:num->bool)`,
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[GSYM INFINITE; CARD_NOT_LT; INFINITE_CARD_LE]);;

let CARD_LE_SUBSET = prove
 (`!s:A->bool t. s SUBSET t ==> s <=_c t`,
  REWRITE_TAC[SUBSET; le_c] THEN MESON_TAC[I_THM]);;

let CARD_LE_UNIV = prove
 (`!s:A->bool. s <=_c (:A)`,
  GEN_TAC THEN MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let CARD_LE_EQ_SUBSET = prove
 (`!s:A->bool t:B->bool. s <=_c t <=> ?u. u SUBSET t /\ (s =_c u)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
    MATCH_MP_TAC CARD_LE_CONG THEN
    ASM_REWRITE_TAC[CARD_LE_CONG; CARD_EQ_REFL]] THEN
  REWRITE_TAC[le_c; eq_c] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN EXISTS_TAC `IMAGE (f:A->B) s` THEN
  EXISTS_TAC `f:A->B` THEN REWRITE_TAC[IN_IMAGE; SUBSET] THEN
  ASM_MESON_TAC[]);;

let CARD_INFINITE_CONG = prove
 (`!s:A->bool t:B->bool. s =_c t ==> (INFINITE s <=> INFINITE t)`,
  REWRITE_TAC[INFINITE_CARD_LE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CARD_LE_CONG THEN ASM_REWRITE_TAC[CARD_EQ_REFL]);;

let CARD_FINITE_CONG = prove
 (`!s:A->bool t:B->bool. s =_c t ==> (FINITE s <=> FINITE t)`,
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[GSYM INFINITE; CARD_INFINITE_CONG]);;

let CARD_LE_FINITE = prove
 (`!s:A->bool t:B->bool. FINITE t /\ s <=_c t ==> FINITE s`,
  ASM_MESON_TAC[CARD_LE_EQ_SUBSET; FINITE_SUBSET; CARD_FINITE_CONG]);;

let CARD_EQ_FINITE = prove
 (`!s t:A->bool. FINITE t /\ s =_c t ==> FINITE s`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_FINITE]);;

let CARD_LE_INFINITE = prove
 (`!s:A->bool t:B->bool. INFINITE s /\ s <=_c t ==> INFINITE t`,
  MESON_TAC[CARD_LE_FINITE; INFINITE]);;

let CARD_LE_CARD_IMP = prove
 (`!s:A->bool t:B->bool. FINITE t /\ s <=_c t ==> CARD s <= CARD t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_LE_FINITE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [le_c]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(IMAGE (f:A->B) s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `(m = n:num) ==> n <= m`) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; IN_IMAGE]]);;

let CARD_EQ_CARD_IMP = prove
 (`!s:A->bool t:B->bool. FINITE t /\ s =_c t ==> (CARD s = CARD t)`,
  MESON_TAC[CARD_FINITE_CONG; LE_ANTISYM; CARD_LE_ANTISYM; CARD_LE_CARD_IMP]);;

let CARD_LE_CARD = prove
 (`!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> (s <=_c t <=> CARD s <= CARD t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (~a ==> ~b) ==> (a <=> b)`) THEN
  ASM_SIMP_TAC[CARD_LE_CARD_IMP] THEN
  REWRITE_TAC[CARD_NOT_LE; NOT_LE] THEN REWRITE_TAC[lt_c; LT_LE] THEN
  ASM_SIMP_TAC[CARD_LE_CARD_IMP] THEN
  MATCH_MP_TAC(TAUT `(c ==> a ==> b) ==> a /\ ~b ==> ~c`) THEN
  DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [CARD_LE_EQ_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  SUBGOAL_THEN `u:A->bool = s` (fun th -> ASM_MESON_TAC[th; CARD_EQ_SYM]) THEN
  ASM_MESON_TAC[CARD_SUBSET_EQ; CARD_EQ_CARD_IMP; CARD_EQ_SYM]);;

let CARD_EQ_CARD = prove
 (`!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> (s =_c t <=> (CARD s = CARD t))`,
  MESON_TAC[CARD_FINITE_CONG; LE_ANTISYM; CARD_LE_ANTISYM; CARD_LE_CARD]);;

let CARD_LT_CARD = prove
 (`!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> (s <_c t <=> CARD s < CARD t)`,
  SIMP_TAC[CARD_LE_CARD; GSYM NOT_LE; GSYM CARD_NOT_LE]);;

let CARD_HAS_SIZE_CONG = prove
 (`!s:A->bool t:B->bool n. s HAS_SIZE n /\ s =_c t ==> t HAS_SIZE n`,
  REWRITE_TAC[HAS_SIZE] THEN
  MESON_TAC[CARD_EQ_CARD; CARD_FINITE_CONG]);;

let CARD_LE_IMAGE = prove
 (`!f s. IMAGE f s <=_c s`,
  REWRITE_TAC[LE_C; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let CARD_LE_IMAGE_GEN = prove
 (`!f:A->B s t. t SUBSET IMAGE f s ==> t <=_c s`,
  REPEAT STRIP_TAC THEN TRANS_TAC CARD_LE_TRANS `IMAGE (f:A->B) s` THEN
  ASM_SIMP_TAC[CARD_LE_IMAGE; CARD_LE_SUBSET]);;

let CARD_EQ_IMAGE = prove
 (`!f:A->B s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f s =_c s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[eq_c] THEN EXISTS_TAC `f:A->B` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinal arithmetic operations.                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("+_c",(16,"right"));;
parse_as_infix("*_c",(20,"right"));;

let add_c = new_definition
  `s +_c t = {INL x | x IN s} UNION {INR y | y IN t}`;;

let mul_c = new_definition
  `s *_c t = {(x,y) | x IN s /\ y IN t}`;;

(* ------------------------------------------------------------------------- *)
(* Congruence properties for the arithmetic operators.                       *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_ADD = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s <=_c s' /\ t <=_c t' ==> s +_c t <=_c s' +_c t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c; add_c] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g:C->D` STRIP_ASSUME_TAC)) THEN
  MP_TAC(prove_recursive_functions_exist sum_RECURSION
   `(!x. h(INL x) = INL((f:A->B) x)) /\ (!y. h(INR y) = INR((g:C->D) y))`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:(A+C)->(B+D)` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
         ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[sum_DISTINCT;
                  sum_INJECTIVE] THEN
  ASM_MESON_TAC[]);;

let CARD_LE_MUL = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s <=_c s' /\ t <=_c t' ==> s *_c t <=_c s' *_c t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c; mul_c] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g:C->D` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\(x,y). (f:A->B) x,(g:C->D) y` THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

let CARD_ADD_CONG = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> s +_c t =_c s' +_c t'`,
  SIMP_TAC[CARD_LE_ADD; GSYM CARD_LE_ANTISYM]);;

let CARD_MUL_CONG = prove
 (`!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> s *_c t =_c s' *_c t'`,
  SIMP_TAC[CARD_LE_MUL; GSYM CARD_LE_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let IN_CARD_ADD = prove
 (`(!x. INL(x) IN (s +_c t) <=> x IN s) /\
   (!y. INR(y) IN (s +_c t) <=> y IN t)`,
  REWRITE_TAC[add_c; IN_UNION; IN_ELIM_THM] THEN
  REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE] THEN MESON_TAC[]);;

let IN_CARD_MUL = prove
 (`!s t x y. (x,y) IN (s *_c t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[mul_c; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let CARD_LE_SQUARE = prove
 (`!s:A->bool. s <=_c s *_c s`,
  GEN_TAC THEN REWRITE_TAC[le_c] THEN EXISTS_TAC `\x:A. x,(@z:A. z IN s)` THEN
  SIMP_TAC[IN_CARD_MUL; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN MESON_TAC[]);;

let CARD_SQUARE_NUM = prove
 (`(UNIV:num->bool) *_c (UNIV:num->bool) =_c (UNIV:num->bool)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM; CARD_LE_SQUARE] THEN
  REWRITE_TAC[le_c; IN_UNIV; mul_c; IN_ELIM_THM] THEN
  EXISTS_TAC `\(x,y). NUMPAIR x y` THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[NUMPAIR_INJ]);;

let UNION_LE_ADD_C = prove
 (`!s t:A->bool. (s UNION t) <=_c s +_c t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CARD_LE_IMAGE_GEN THEN
  EXISTS_TAC `function INL x -> (x:A) | INR x -> x` THEN
  REWRITE_TAC[add_c; IMAGE_UNION] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Various "arithmetical" lemmas.                                            *)
(* ------------------------------------------------------------------------- *)

let CARD_ADD_SYM = prove
 (`!s:A->bool t:B->bool. s +_c t =_c t +_c s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  MP_TAC(prove_recursive_functions_exist sum_RECURSION
    `(!x. (h:A+B->B+A) (INL x) = INR x) /\ (!y. h(INR y) = INL y)`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[FORALL_SUM_THM; EXISTS_SUM_THM; EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE; IN_CARD_ADD] THEN MESON_TAC[]);;

let CARD_ADD_ASSOC = prove
 (`!s:A->bool t:B->bool u:C->bool. s +_c (t +_c u) =_c (s +_c t) +_c u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  CHOOSE_TAC(prove_recursive_functions_exist sum_RECURSION
    `(!u. (i:B+C->(A+B)+C) (INL u) = INL(INR u)) /\
     (!v. i(INR v) = INR v)`) THEN
  MP_TAC(prove_recursive_functions_exist sum_RECURSION
    `(!x. (h:A+B+C->(A+B)+C) (INL x) = INL(INL x)) /\
     (!z. h(INR z) = i(z))`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FORALL_SUM_THM; EXISTS_SUM_THM; EXISTS_UNIQUE_THM;
                  sum_DISTINCT; sum_INJECTIVE; IN_CARD_ADD] THEN
  MESON_TAC[]);;

let CARD_MUL_SYM = prove
 (`!s:A->bool t:B->bool. s *_c t =_c t *_c s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  MP_TAC(prove_recursive_functions_exist pair_RECURSION
    `(!x:A y:B. h(x,y) = (y,x))`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; IN_CARD_MUL; PAIR_EQ] THEN
  MESON_TAC[]);;

let CARD_MUL_ASSOC = prove
 (`!s:A->bool t:B->bool u:C->bool. s *_c (t *_c u) =_c (s *_c t) *_c u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  CHOOSE_TAC(prove_recursive_functions_exist pair_RECURSION
    `(!x y z. (i:A->B#C->(A#B)#C) x (y,z) = (x,y),z)`) THEN
  MP_TAC(prove_recursive_functions_exist pair_RECURSION
    `(!x p. (h:A#B#C->(A#B)#C) (x,p) = i x p)`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; IN_CARD_MUL; PAIR_EQ] THEN
  MESON_TAC[]);;

let CARD_LDISTRIB = prove
 (`!s:A->bool t:B->bool u:C->bool.
        s *_c (t +_c u) =_c (s *_c t) +_c (s *_c u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  CHOOSE_TAC(prove_recursive_functions_exist sum_RECURSION
    `(!x y. (i:A->(B+C)->A#B+A#C) x (INL y) = INL(x,y)) /\
     (!x z. (i:A->(B+C)->A#B+A#C) x (INR z) = INR(x,z))`) THEN
  MP_TAC(prove_recursive_functions_exist pair_RECURSION
    `(!x s. (h:A#(B+C)->(A#B)+(A#C)) (x,s) = i x s)`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM;
                  FORALL_SUM_THM; EXISTS_SUM_THM; PAIR_EQ; IN_CARD_MUL;
                  sum_DISTINCT; sum_INJECTIVE; IN_CARD_ADD] THEN
  MESON_TAC[]);;

let CARD_RDISTRIB = prove
 (`!s:A->bool t:B->bool u:C->bool.
        (s +_c t) *_c u =_c (s *_c u) +_c (t *_c u)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC CARD_EQ_TRANS
   `(u:C->bool) *_c ((s:A->bool) +_c (t:B->bool))` THEN
  REWRITE_TAC[CARD_MUL_SYM] THEN
  TRANS_TAC CARD_EQ_TRANS
   `(u:C->bool) *_c (s:A->bool) +_c (u:C->bool) *_c (t:B->bool)` THEN
  REWRITE_TAC[CARD_LDISTRIB] THEN
  MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC[CARD_MUL_SYM]);;

let CARD_LE_ADDR = prove
 (`!s:A->bool t:B->bool. s <=_c s +_c t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC `INL:A->A+B` THEN SIMP_TAC[IN_CARD_ADD; sum_INJECTIVE]);;

let CARD_LE_ADDL = prove
 (`!s:A->bool t:B->bool. t <=_c s +_c t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC `INR:B->A+B` THEN SIMP_TAC[IN_CARD_ADD; sum_INJECTIVE]);;

(* ------------------------------------------------------------------------- *)
(* A rather special lemma but temporarily useful.                            *)
(* ------------------------------------------------------------------------- *)

let CARD_ADD_LE_MUL_INFINITE = prove
 (`!s:A->bool. INFINITE s ==> s +_c s <=_c s *_c s`,
  GEN_TAC THEN REWRITE_TAC[INFINITE_CARD_LE; le_c; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(prove_recursive_functions_exist sum_RECURSION
    `(!x. h(INL x) = (f(0),x):A#A) /\ (!x. h(INR x) = (f(1),x))`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:A+A->A#A` THEN
  STRIP_TAC THEN
  REPEAT((MATCH_MP_TAC sum_INDUCT THEN
          ASM_REWRITE_TAC[IN_CARD_ADD; IN_CARD_MUL; PAIR_EQ])
         ORELSE STRIP_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NUM_REDUCE_CONV `1 = 0`]);;

(* ------------------------------------------------------------------------- *)
(* Relate cardinal addition to the simple union operation.                   *)
(* ------------------------------------------------------------------------- *)

let CARD_DISJOINT_UNION = prove
 (`!s:A->bool t. (s INTER t = EMPTY) ==> (s UNION t =_c s +_c t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[eq_c; IN_UNION] THEN
  EXISTS_TAC `\x:A. if x IN s then INL x else INR x` THEN
  REWRITE_TAC[FORALL_SUM_THM; IN_CARD_ADD] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR] THEN
  REWRITE_TAC[TAUT `(if b then x else y) <=> b /\ x \/ ~b /\ y`] THEN
  REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE; IN_CARD_ADD] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The key to arithmetic on infinite cardinals: k^2 = k.                     *)
(* ------------------------------------------------------------------------- *)

let CARD_SQUARE_INFINITE = prove
 (`!k:A->bool. INFINITE k ==> (k *_c k =_c k)`,
  let lemma = prove
   (`INFINITE(s:A->bool) /\ s SUBSET k /\
     (!x y. R(x,y) ==> x IN (s *_c s) /\ y IN s) /\
     (!x. x IN (s *_c s) ==> ?!y. y IN s /\ R(x,y)) /\
     (!y:A. y IN s ==> ?!x. x IN (s *_c s) /\ R(x,y))
     ==> (s = {z | ?p. R(p,z)})`,
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `P = \R. ?s. INFINITE(s:A->bool) /\ s SUBSET k /\
                 (!x y. R(x,y) ==> x IN (s *_c s) /\ y IN s) /\
                 (!x. x IN (s *_c s) ==> ?!y. y IN s /\ R(x,y)) /\
                 (!y. y IN s ==> ?!x. x IN (s *_c s) /\ R(x,y))` THEN
  MP_TAC(ISPEC `P:((A#A)#A->bool)->bool` ZL_SUBSETS_UNIONS_NONEMPTY) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM EQ_C] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INFINITE_CARD_LE]) THEN
      REWRITE_TAC[CARD_LE_EQ_SUBSET] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:A->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[num_INFINITE; CARD_INFINITE_CONG]; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
       MP_TAC(MATCH_MP CARD_MUL_CONG (CONJ th th))) THEN
      GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
      DISCH_THEN(MP_TAC o C CONJ CARD_SQUARE_NUM) THEN
      DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_TRANS) THEN
      FIRST_ASSUM(fun th ->
        DISCH_THEN(ACCEPT_TAC o MATCH_MP CARD_EQ_TRANS o C CONJ th));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `P = \R. INFINITE {z | ?x y. R((x,y),z)} /\
              (!x:A y z. R((x,y),z) ==> x IN k /\ y IN k /\ z IN k) /\
              (!x y. (?u v. R((u,v),x)) /\ (?u v. R((u,v),y))
                     ==> ?z. R((x,y),z)) /\
              (!x y. (?z. R((x,y),z))
                     ==> (?u v. R((u,v),x)) /\ (?u v. R((u,v),y))) /\
              (!x y z1 z2. R((x,y),z1) /\ R((x,y),z2) ==> (z1 = z2)) /\
              (!x1 y1 x2 y2 z. R((x1,y1),z) /\ R((x2,y2),z)
                               ==> (x1 = x2) /\ (y1 = y2))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[MATCH_MP(TAUT `(a ==> b) ==> (a <=> b /\ a)`) lemma] THEN
      REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[FUN_EQ_THM] THEN
      REWRITE_TAC[IN_CARD_MUL; EXISTS_PAIR_THM; SUBSET; FUN_EQ_THM;
                  IN_ELIM_THM; FORALL_PAIR_THM; EXISTS_UNIQUE_THM;
                  UNIONS; PAIR_EQ] THEN
      GEN_TAC THEN AP_TERM_TAC THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o SYM) THEN REWRITE_TAC[] THEN GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [FORALL_AND_THM] THEN
    MATCH_MP_TAC(TAUT
     `(c /\ d ==> f) /\ (a /\ b ==> e)
      ==> (a /\ (b /\ c) /\ d ==> e /\ f)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[UNIONS; IN_ELIM_THM] THEN
      REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:(A#A)#A->bool`) MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `s:(A#A)#A->bool`) THEN
    ASM_REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                      FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; UNIONS] THEN ASM_MESON_TAC[IN];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:(A#A)#A->bool`
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:A->bool`) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(s:A->bool) *_c s =_c s` ASSUME_TAC THENL
   [REWRITE_TAC[EQ_C] THEN EXISTS_TAC `R:(A#A)#A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s +_c s <=_c (s:A->bool)` ASSUME_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(s:A->bool) *_c s` THEN
    ASM_SIMP_TAC[CARD_EQ_IMP_LE; CARD_ADD_LE_MUL_INFINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) INTER (k DIFF s) = EMPTY` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(ISPECL [`k DIFF (s:A->bool)`; `s:A->bool`] CARD_LE_TOTAL)
  THENL
   [SUBGOAL_THEN `k = (s:A->bool) UNION (k DIFF s)` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                  IN_UNION; IN_DIFF] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM; CARD_LE_SQUARE] THEN
    TRANS_TAC CARD_LE_TRANS
     `((s:A->bool) +_c (k DIFF s:A->bool)) *_c (s +_c k DIFF s)` THEN
    ASM_SIMP_TAC[CARD_DISJOINT_UNION; CARD_EQ_IMP_LE; CARD_MUL_CONG] THEN
    TRANS_TAC CARD_LE_TRANS `((s:A->bool) +_c s) *_c (s +_c s)` THEN
    ASM_SIMP_TAC[CARD_LE_ADD; CARD_LE_MUL; CARD_LE_REFL] THEN
    TRANS_TAC CARD_LE_TRANS `(s:A->bool) *_c s` THEN
    ASM_SIMP_TAC[CARD_LE_MUL] THEN
    TRANS_TAC CARD_LE_TRANS `s:A->bool` THEN ASM_SIMP_TAC[CARD_EQ_IMP_LE] THEN
    REWRITE_TAC[CARD_LE_EQ_SUBSET] THEN EXISTS_TAC `s:A->bool` THEN
    SIMP_TAC[CARD_EQ_REFL; SUBSET; IN_UNION];
    ALL_TAC] THEN
  UNDISCH_TAC `s:A->bool <=_c k DIFF s` THEN
  REWRITE_TAC[CARD_LE_EQ_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:A->bool *_c d) UNION (d *_c s) UNION (d *_c d) =_c d`
  MP_TAC THENL
   [TRANS_TAC CARD_EQ_TRANS
       `((s:A->bool) *_c (d:A->bool)) +_c ((d *_c s) +_c (d *_c d))` THEN
    CONJ_TAC THENL
     [TRANS_TAC CARD_EQ_TRANS
       `((s:A->bool) *_c d) +_c ((d *_c s) UNION (d *_c d))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC[CARD_EQ_REFL]] THEN
      MATCH_MP_TAC CARD_DISJOINT_UNION THEN
      UNDISCH_TAC `s INTER (k DIFF s:A->bool) = {}` THEN
      UNDISCH_TAC `d SUBSET (k DIFF s:A->bool)` THEN
      REWRITE_TAC[EXTENSION; SUBSET; FORALL_PAIR_THM; NOT_IN_EMPTY;
                  IN_INTER; IN_UNION; IN_CARD_MUL; IN_DIFF] THEN MESON_TAC[];
      ALL_TAC] THEN
    TRANS_TAC CARD_EQ_TRANS `s:A->bool` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC CARD_EQ_TRANS
      `(s:A->bool *_c s) +_c (s *_c s) +_c (s *_c s)` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CARD_ADD_CONG THEN CONJ_TAC) THEN
      MATCH_MP_TAC CARD_MUL_CONG THEN ASM_REWRITE_TAC[CARD_EQ_REFL] THEN
      ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    TRANS_TAC CARD_EQ_TRANS `(s:A->bool) +_c s +_c s` THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CARD_ADD_CONG THEN ASM_REWRITE_TAC[]);
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM; CARD_LE_ADDR] THEN
    TRANS_TAC CARD_LE_TRANS `(s:A->bool) +_c s` THEN
    ASM_SIMP_TAC[CARD_LE_ADD; CARD_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[EQ_C; IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_TAC `S:(A#A)#A->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:(A#A)#A. R(x) \/ S(x)`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `(s:A->bool) UNION d`;
    SIMP_TAC[SUBSET; IN];
    SUBGOAL_THEN `~(d:A->bool = {})` MP_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `FINITE:(A->bool)->bool`) THEN
      REWRITE_TAC[FINITE_RULES; GSYM INFINITE] THEN
      ASM_MESON_TAC[CARD_INFINITE_CONG];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `a:A IN d`) o last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o EXISTENCE) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A#A` (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REWRITE_TAC[EXTENSION; NOT_FORALL_THM] THEN
    EXISTS_TAC `(b:A#A,a:A)` THEN ASM_REWRITE_TAC[IN] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM
     (MP_TAC o CONJUNCT2 o C MATCH_MP th o CONJUNCT1)) THEN
    MAP_EVERY UNDISCH_TAC
     [`a:A IN d`; `(d:A->bool) SUBSET (k DIFF s)`] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN MESON_TAC[]] THEN
  REWRITE_TAC[INFINITE; FINITE_UNION; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[GSYM INFINITE] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(d:A->bool) SUBSET (k DIFF s)`; `(s:A->bool) SUBSET k`] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_ASSUM(UNDISCH_TAC o check is_conj o concl)) THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_UNIQUE_THM; EXISTS_PAIR_THM;
              IN_CARD_MUL; IN_UNION; PAIR_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [`(s:A->bool) SUBSET k`;
    `(d:A->bool) SUBSET (k DIFF s)`] THEN
  REWRITE_TAC[SUBSET; EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_DIFF] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  DISCH_THEN(fun th ->
   FIRST_ASSUM(MP_TAC o C MATCH_MP th o last o CONJUNCTS)) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the "absorption laws" for arithmetic with an infinite cardinal.     *)
(* ------------------------------------------------------------------------- *)

let CARD_MUL_ABSORB_LE = prove
 (`!s:A->bool t:B->bool. INFINITE(t) /\ s <=_c t ==> s *_c t <=_c t`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `(t:B->bool) *_c t` THEN
  ASM_SIMP_TAC[CARD_LE_MUL; CARD_LE_REFL;
               CARD_SQUARE_INFINITE; CARD_EQ_IMP_LE]);;

let CARD_MUL2_ABSORB_LE = prove
 (`!s:A->bool t:B->bool u:C->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> s *_c t <=_c u`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `(s:A->bool) *_c (u:C->bool)` THEN
  ASM_SIMP_TAC[CARD_MUL_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_MUL THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);;

let CARD_ADD_ABSORB_LE = prove
 (`!s:A->bool t:B->bool. INFINITE(t) /\ s <=_c t ==> s +_c t <=_c t`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `(t:B->bool) *_c t` THEN
  ASM_SIMP_TAC[CARD_SQUARE_INFINITE; CARD_EQ_IMP_LE] THEN
  TRANS_TAC CARD_LE_TRANS `(t:B->bool) +_c t` THEN
  ASM_SIMP_TAC[CARD_ADD_LE_MUL_INFINITE; CARD_LE_ADD; CARD_LE_REFL]);;

let CARD_ADD2_ABSORB_LE = prove
 (`!s:A->bool t:B->bool u:C->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> s +_c t <=_c u`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `(s:A->bool) +_c (u:C->bool)` THEN
  ASM_SIMP_TAC[CARD_ADD_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_ADD THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);;

let CARD_MUL_ABSORB = prove
 (`!s:A->bool t:B->bool.
     INFINITE(t) /\ ~(s = {}) /\ s <=_c t ==> s *_c t =_c t`,
  SIMP_TAC[GSYM CARD_LE_ANTISYM; CARD_MUL_ABSORB_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
   GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `\x:B. (a:A,x)` THEN
  ASM_SIMP_TAC[IN_CARD_MUL; PAIR_EQ]);;

let CARD_ADD_ABSORB = prove
 (`!s:A->bool t:B->bool. INFINITE(t) /\ s <=_c t ==> s +_c t =_c t`,
  SIMP_TAC[GSYM CARD_LE_ANTISYM; CARD_LE_ADDL; CARD_ADD_ABSORB_LE]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of finiteness.                                               *)
(* ------------------------------------------------------------------------- *)

let CARD_ADD_FINITE = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE(s +_c t)`,
  SIMP_TAC[add_c; FINITE_UNION; SIMPLE_IMAGE; FINITE_IMAGE]);;

let CARD_MUL_FINITE = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE(s *_c t)`,
  SIMP_TAC[mul_c; FINITE_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Some more ad-hoc but useful theorems.                                     *)
(* ------------------------------------------------------------------------- *)

let CARD_MUL_LT_LEMMA = prove
 (`!s t:B->bool u. s <=_c t /\ t <_c u /\ INFINITE u ==> s *_c t <_c u`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `FINITE(t:B->bool)` THENL
   [REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[CARD_NOT_LT; INFINITE] THEN
    ASM_MESON_TAC[CARD_LE_FINITE; CARD_MUL_FINITE];
    ASM_MESON_TAC[INFINITE; CARD_MUL_ABSORB_LE; CARD_LET_TRANS]]);;

let CARD_MUL_LT_INFINITE = prove
 (`!s:A->bool t:B->bool u. s <_c u /\ t <_c u /\ INFINITE u ==> s *_c t <_c u`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(ISPECL [`s:A->bool`; `t:B->bool`] CARD_LE_TOTAL) THENL
   [ASM_MESON_TAC[CARD_MUL_SYM; CARD_MUL_LT_LEMMA];
    STRIP_TAC THEN TRANS_TAC CARD_LET_TRANS `t:B->bool *_c s:A->bool` THEN
    ASM_MESON_TAC[CARD_EQ_IMP_LE; CARD_MUL_SYM; CARD_MUL_LT_LEMMA]]);;

(* ------------------------------------------------------------------------- *)
(* Cantor's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let CANTOR_THM = prove
 (`!s:A->bool. s <_c {t | t SUBSET s}`,
  GEN_TAC THEN REWRITE_TAC[lt_c] THEN CONJ_TAC THENL
   [REWRITE_TAC[le_c] THEN EXISTS_TAC `(=):A->A->bool` THEN
    REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM; SUBSET; IN] THEN MESON_TAC[];
    REWRITE_TAC[LE_C; IN_ELIM_THM; SURJECTIVE_RIGHT_INVERSE] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `g:A->(A->bool)` THEN
    DISCH_THEN(MP_TAC o SPEC `\x:A. s(x) /\ ~(g x x)`) THEN
    REWRITE_TAC[SUBSET; IN; FUN_EQ_THM] THEN MESON_TAC[]]);;

let CANTOR_THM_UNIV = prove
 (`(UNIV:A->bool) <_c (UNIV:(A->bool)->bool)`,
  MP_TAC(ISPEC `UNIV:A->bool` CANTOR_THM) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_UNIV; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about countability.                                                *)
(* ------------------------------------------------------------------------- *)

let NUM_COUNTABLE = prove
 (`COUNTABLE(:num)`,
  REWRITE_TAC[COUNTABLE; ge_c; CARD_LE_REFL]);;

let COUNTABLE_ALT = prove
 (`!s. COUNTABLE s <=> s <=_c (:num)`,
  REWRITE_TAC[COUNTABLE; ge_c]);;

let COUNTABLE_CASES = prove
 (`!s. COUNTABLE s <=> FINITE s \/ s =_c (:num)`,
  REWRITE_TAC[COUNTABLE_ALT; FINITE_CARD_LT; CARD_LE_LT]);;

let CARD_LE_COUNTABLE = prove
 (`!s t:A->bool. COUNTABLE t /\ s <=_c t ==> COUNTABLE s`,
  REWRITE_TAC[COUNTABLE; ge_c] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `t:A->bool` THEN ASM_REWRITE_TAC[]);;

let CARD_EQ_COUNTABLE = prove
 (`!s t:A->bool. COUNTABLE t /\ s =_c t ==> COUNTABLE s`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_COUNTABLE]);;

let CARD_COUNTABLE_CONG = prove
 (`!s t. s =_c t ==> (COUNTABLE s <=> COUNTABLE t)`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_COUNTABLE]);;

let COUNTABLE_SUBSET = prove
 (`!s t:A->bool. COUNTABLE t /\ s SUBSET t ==> COUNTABLE s`,
  REWRITE_TAC[COUNTABLE; ge_c] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `t:A->bool` THEN
  ASM_SIMP_TAC[CARD_LE_SUBSET]);;

let COUNTABLE_RESTRICT = prove
 (`!s P. COUNTABLE s ==> COUNTABLE {x | x IN s /\ P x}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  SET_TAC[]);;

let FINITE_IMP_COUNTABLE = prove
 (`!s. FINITE s ==> COUNTABLE s`,
  SIMP_TAC[FINITE_CARD_LT; lt_c; COUNTABLE; ge_c]);;

let COUNTABLE_IMAGE = prove
 (`!f:A->B s. COUNTABLE s ==> COUNTABLE (IMAGE f s)`,
  REWRITE_TAC[COUNTABLE; ge_c] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `s:A->bool` THEN
  ASM_SIMP_TAC[CARD_LE_IMAGE]);;

let COUNTABLE_EMPTY = prove
 (`COUNTABLE {}`,
  SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_RULES]);;

let COUNTABLE_INTER = prove
 (`!s t. COUNTABLE s \/ COUNTABLE t ==> COUNTABLE (s INTER t)`,
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  SET_TAC[]);;

let COUNTABLE_UNION_IMP = prove
 (`!s t:A->bool. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s UNION t)`,
  REWRITE_TAC[COUNTABLE; ge_c] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `(s:A->bool) +_c (t:A->bool)` THEN
  ASM_SIMP_TAC[CARD_ADD2_ABSORB_LE; num_INFINITE; UNION_LE_ADD_C]);;

let COUNTABLE_UNION = prove
 (`!s t:A->bool. COUNTABLE(s UNION t) <=> COUNTABLE s /\ COUNTABLE t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[COUNTABLE_UNION_IMP] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
  SET_TAC[]);;

let COUNTABLE_SING = prove
 (`!x. COUNTABLE {x}`,
  SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_SING]);;

let COUNTABLE_INSERT = prove
 (`!x s. COUNTABLE(x INSERT s) <=> COUNTABLE s`,
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  REWRITE_TAC[COUNTABLE_UNION; COUNTABLE_SING]);;

let COUNTABLE_DELETE = prove
 (`!x:A s. COUNTABLE(s DELETE x) <=> COUNTABLE s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:A) IN s` THEN
  ASM_SIMP_TAC[SET_RULE `~(x IN s) ==> s DELETE x = s`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `COUNTABLE((x:A) INSERT (s DELETE x))` THEN CONJ_TAC THENL
   [REWRITE_TAC[COUNTABLE_INSERT]; AP_TERM_TAC THEN ASM SET_TAC[]]);;

let COUNTABLE_DIFF_FINITE = prove
 (`!s t. FINITE s ==> (COUNTABLE(t DIFF s) <=> COUNTABLE t)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[DIFF_EMPTY; SET_RULE `s DIFF (x INSERT t) = (s DIFF t) DELETE x`;
           COUNTABLE_DELETE]);;

let COUNTABLE_CROSS = prove
 (`!s t. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s CROSS t)`,
  REWRITE_TAC[COUNTABLE; ge_c; CROSS; GSYM mul_c] THEN
  SIMP_TAC[CARD_MUL2_ABSORB_LE; num_INFINITE]);;

let COUNTABLE_AS_IMAGE_SUBSET = prove
 (`!s. COUNTABLE s ==> ?f. s SUBSET (IMAGE f (:num))`,
  REWRITE_TAC[COUNTABLE; ge_c; LE_C; SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

let COUNTABLE_AS_IMAGE_SUBSET_EQ = prove
 (`!s:A->bool. COUNTABLE s <=> ?f. s SUBSET (IMAGE f (:num))`,
  REWRITE_TAC[COUNTABLE; ge_c; LE_C; SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

let COUNTABLE_AS_IMAGE = prove
 (`!s:A->bool. COUNTABLE s /\ ~(s = {}) ==> ?f. s = IMAGE f (:num)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP COUNTABLE_AS_IMAGE_SUBSET) THEN
  DISCH_THEN(X_CHOOSE_TAC `f:num->A`) THEN
  EXISTS_TAC `\n. if (f:num->A) n IN s then f n else a` THEN
  ASM SET_TAC[]);;

let FORALL_COUNTABLE_AS_IMAGE = prove
 (`(!d. COUNTABLE d ==> P d) <=> P {} /\ (!f. P(IMAGE f (:num)))`,
  MESON_TAC[COUNTABLE_AS_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE;
            COUNTABLE_EMPTY]);;

let COUNTABLE_AS_INJECTIVE_IMAGE = prove
 (`!s. COUNTABLE s /\ INFINITE s
       ==> ?f. s = IMAGE f (:num) /\ (!m n. f(m) = f(n) ==> m = n)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[INFINITE_CARD_LE; COUNTABLE; ge_c] THEN
  REWRITE_TAC[CARD_LE_ANTISYM; eq_c] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let COUNTABLE_UNIONS = prove
 (`!A:(A->bool)->bool.
        COUNTABLE A /\ (!s. s IN A ==> COUNTABLE s)
        ==> COUNTABLE (UNIONS A)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [COUNTABLE_AS_IMAGE_SUBSET_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `f:num->A->bool`) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:(A->bool)->num->A`) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(m,n). (g:(A->bool)->num->A) ((f:num->A->bool) m) n)
                    ((:num) CROSS (:num))` THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_CROSS; NUM_COUNTABLE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_UNIV] THEN
  ASM SET_TAC[]);;

let COUNTABLE_PRODUCT_DEPENDENT = prove
 (`!f:A->B->C s t.
        COUNTABLE s /\ (!x. x IN s ==> COUNTABLE(t x))
        ==> COUNTABLE {f x y | x IN s /\ y IN (t x)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{(f:A->B->C) x y | x IN s /\ y IN (t x)} =
                IMAGE (\(x,y). f x y) {(x,y) | x IN s /\ y IN (t x)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    SET_TAC[];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN POP_ASSUM MP_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [COUNTABLE_AS_IMAGE_SUBSET_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `f:num->A`) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->num->B`) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(m,n). (f:num->A) m,(g:A->num->B)(f m) n)
                    ((:num) CROSS (:num))` THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_CROSS; NUM_COUNTABLE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
  REWRITE_TAC[IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
              EXISTS_PAIR_THM; IN_CROSS; IN_UNIV] THEN
  ASM SET_TAC[]);;

let COUNTABLE_CART = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N) ==> COUNTABLE {x | P i x})
       ==> COUNTABLE {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N)
        ==> COUNTABLE {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                 ==> P i (v$i)) /\
                            (!i. 1 <= i /\ i <= dimindex(:N) /\ n < i
                                 ==> v$i = @x. F)}`
   (MP_TAC o SPEC `dimindex(:N)`) THEN REWRITE_TAC[LE_REFL; LET_ANTISYM] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= n /\ i <= 0 <=> F`] THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n /\ 0 < i <=> 1 <= i /\ i <= n`] THEN
    SUBGOAL_THEN
     `{v | !i. 1 <= i /\ i <= dimindex (:N) ==> v$i = (@x. F)} =
      {(lambda i. @x. F):A^N}`
     (fun th -> SIMP_TAC[COUNTABLE_SING;th]) THEN
    SIMP_TAC[EXTENSION; IN_SING; IN_ELIM_THM; CART_EQ; LAMBDA_BETA];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
   `IMAGE (\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)
          {x,v | x IN {x:A | P (SUC n) x} /\
                 v IN {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                ==> P i (v$i)) /\
                           (!i. 1 <= i /\ i <= dimindex (:N) /\ n < i
                                ==> v$i = (@x. F))}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE THEN
    ASM_SIMP_TAC[REWRITE_RULE[CROSS] COUNTABLE_CROSS; ARITH_RULE `1 <= SUC n`;
                 ARITH_RULE `SUC n <= m ==> n <= m`];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_PAIR_THM; EXISTS_PAIR_THM] THEN
  X_GEN_TAC `v:A^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `(v:A^N)$(SUC n)` THEN
  EXISTS_TAC `(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N` THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; ARITH_RULE `i <= n ==> ~(i = SUC n)`] THEN
  ASM_MESON_TAC[LE; ARITH_RULE `1 <= SUC n`;
                ARITH_RULE `n < i /\ ~(i = SUC n) ==> SUC n < i`]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of infinite list and cartesian product types.                 *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_LIST = prove
 (`INFINITE(:A) ==> (:A list) =_c (:A)`,
  DISCH_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[le_c; IN_UNIV] THEN
    EXISTS_TAC `\x:A. [x]` THEN REWRITE_TAC[CONS_11]] THEN
  TRANS_TAC CARD_LE_TRANS `(:num) *_c (:A)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CARD_MUL2_ABSORB_LE THEN
    ASM_REWRITE_TAC[GSYM INFINITE_CARD_LE; CARD_LE_REFL]] THEN
  SUBGOAL_THEN `(:A) *_c (:A) <=_c (:A)` MP_TAC THENL
   [MATCH_MP_TAC CARD_MUL2_ABSORB_LE THEN ASM_REWRITE_TAC[CARD_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[le_c; mul_c; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
  REWRITE_TAC[IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `pair:A#A->A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `\l. LENGTH l,ITLIST (\x:A a:A. pair(x,a)) l (@x. T)` THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; GSYM EXISTS_REFL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN SIMP_TAC[LENGTH_EQ_NIL; LENGTH] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
  REWRITE_TAC[ITLIST; SUC_INJ] THEN
  ABBREV_TAC `f:A->A->A = \x a. pair (x,a)` THEN
  ABBREV_TAC `z = @x:A. T` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN ASM_MESON_TAC[]);;

let CARD_EQ_CART = prove
 (`INFINITE(:A) ==> (:A^N) =_c (:A)`,
  DISCH_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[le_c; IN_UNIV] THEN
    EXISTS_TAC `(\x. lambda i. x):A->A^N` THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    MESON_TAC[LE_REFL; DIMINDEX_GE_1]] THEN
  TRANS_TAC CARD_LE_TRANS `(:A list)` THEN
  ASM_SIMP_TAC[CARD_EQ_LIST; CARD_EQ_IMP_LE] THEN REWRITE_TAC[LE_C] THEN
  EXISTS_TAC `(\l. lambda i. EL i l):(A)list->A^N` THEN
  ASM_SIMP_TAC[CART_EQ; IN_UNIV; LAMBDA_BETA] THEN X_GEN_TAC `x:A^N` THEN
  SUBGOAL_THEN `!n f. ?l. !i. i < n ==> EL i l:A = f i` MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN X_GEN_TAC `f:num->A` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (f:num->A)(SUC i)`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `l:A list` THEN
    DISCH_TAC THEN EXISTS_TAC `CONS ((f:num->A) 0) l` THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC];
    DISCH_THEN(MP_TAC o SPECL [`dimindex(:N)+1`; `\i. (x:A^N)$i`]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; ARITH_RULE `i < n + 1 <=> i <= n`] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of the reals. This is done in a rather laborious way to avoid *)
(* any dependence on the theories of analysis.                               *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_REAL = prove
 (`(:real) =_c (:num->bool)`,
  let lemma = prove
   (`!s m n. sum (s INTER (m..n)) (\i. inv(&3 pow i)) < &3 / &2 / &3 pow m`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum (m..n) (\i. inv(&3 pow i))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      SIMP_TAC[FINITE_NUMSEG; INTER_SUBSET; REAL_LE_INV_EQ;
               REAL_POW_LE; REAL_POS];
      WF_INDUCT_TAC `n - m:num` THEN
      ASM_CASES_TAC `m:num <= n` THENL
       [ASM_SIMP_TAC[SUM_CLAUSES_LEFT] THEN ASM_CASES_TAC `m + 1 <= n` THENL
         [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `SUC m`]) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ADD1; REAL_POW_ADD]] THEN
          MATCH_MP_TAC(REAL_ARITH
           `a + j:real <= k ==> x < j ==> a + x < k`) THEN
          REWRITE_TAC[real_div; REAL_INV_MUL; REAL_POW_1] THEN REAL_ARITH_TAC;
          ALL_TAC];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE; GSYM NUMSEG_EMPTY]) THEN
      ASM_REWRITE_TAC[SUM_CLAUSES; REAL_ADD_RID] THEN
      REWRITE_TAC[REAL_ARITH `inv x < &3 / &2 / x <=> &0 < inv x`] THEN
      SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT;
               ARITH]]) in
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:num) *_c (:num->bool)` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC CARD_MUL2_ABSORB_LE THEN REWRITE_TAC[INFINITE_CARD_LE] THEN
      SIMP_TAC[CANTOR_THM_UNIV; CARD_LT_IMP_LE; CARD_LE_REFL]] THEN
    TRANS_TAC CARD_LE_TRANS `(:num) *_c {x:real | &0 <= x}` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_C; mul_c; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM; IN_UNIV] THEN
      EXISTS_TAC `\(n,x:real). --(&1) pow n * x` THEN X_GEN_TAC `x:real` THEN
      MATCH_MP_TAC(MESON[] `P 0 \/ P 1 ==> ?n. P n`) THEN
      REWRITE_TAC[OR_EXISTS_THM] THEN EXISTS_TAC `abs x` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_LE_MUL THEN REWRITE_TAC[CARD_LE_REFL] THEN
    MP_TAC(ISPECL [`(:num)`; `(:num)`] CARD_MUL_ABSORB_LE) THEN
    REWRITE_TAC[CARD_LE_REFL; num_INFINITE] THEN
    REWRITE_TAC[le_c; mul_c; IN_UNIV; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[GSYM FORALL_PAIR_THM; INJECTIVE_LEFT_INVERSE] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`pair:num#num->num`; `unpair:num->num#num`] THEN
    DISCH_TAC THEN
    EXISTS_TAC `\x:real n:num. &(FST(unpair n)) * x <= &(SND(unpair n))` THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC[IN_ELIM_THM; FUN_EQ_THM] THEN
    CONJ_TAC THENL [REWRITE_TAC[EQ_SYM_EQ; CONJ_ACI]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GENL [`p:num`; `q:num`] o
      SPEC `(pair:num#num->num) (p,q)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MP_TAC(SPEC `y - x:real` REAL_ARCH) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; NOT_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&2`) THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `&p * x:real` REAL_ARCH_LT) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MATCH_MP_TAC num_INDUCTION THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS;
      REAL_ARITH `x:real < &0 <=> ~(&0 <= x)`] THEN
    X_GEN_TAC `q:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
    REWRITE_TAC[LT] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[le_c; IN_UNIV] THEN
    EXISTS_TAC `\s:num->bool. sup { sum (s INTER (0..n)) (\i. inv(&3 pow i)) |
                                    n IN (:num) }` THEN
    MAP_EVERY X_GEN_TAC [`x:num->bool`; `y:num->bool`] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[EXTENSION; NOT_FORALL_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MAP_EVERY (fun w -> SPEC_TAC(w,w)) [`y:num->bool`; `x:num->bool`] THEN
    MATCH_MP_TAC(MESON[IN]
     `((!P Q n. R P Q n <=> R Q P n) /\ (!P Q. S P Q <=> S Q P)) /\
      (!P Q. (?n. n IN P /\ ~(n IN Q) /\ R P Q n) ==> S P Q)
      ==> !P Q. (?n:num. ~(n IN P <=> n IN Q) /\ R P Q n) ==> S P Q`) THEN
    CONJ_TAC THENL [REWRITE_TAC[EQ_SYM_EQ]; REWRITE_TAC[]] THEN
    MAP_EVERY X_GEN_TAC [`x:num->bool`; `y:num->bool`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `!z:real. y < z /\ z <= x ==> ~(x = y)`) THEN
    EXISTS_TAC `sum (x INTER (0..n)) (\i. inv(&3 pow i))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
       `sum (y INTER (0..n)) (\i. inv(&3 pow i)) +
        &3 / &2 / &3 pow (SUC n)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_SUP_LE THEN
        CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV]] THEN
        X_GEN_TAC `p:num` THEN ASM_CASES_TAC `n:num <= p` THENL
         [MATCH_MP_TAC(REAL_ARITH
           `!d. s:real = t + d /\ d <= e ==> s <= t + e`) THEN
          EXISTS_TAC `sum(y INTER (n+1..p)) (\i. inv (&3 pow i))` THEN
          CONJ_TAC THENL
           [ONCE_REWRITE_TAC[INTER_COMM] THEN
            REWRITE_TAC[INTER; SUM_RESTRICT_SET] THEN
            ASM_SIMP_TAC[SUM_COMBINE_R; LE_0];
            SIMP_TAC[ADD1; lemma; REAL_LT_IMP_LE]];
          MATCH_MP_TAC(REAL_ARITH `y:real <= x /\ &0 <= d ==> y <= x + d`) THEN
          SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_POW_LE] THEN
          MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
          SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
          SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN MATCH_MP_TAC
           (SET_RULE `s SUBSET t ==> u INTER s SUBSET u INTER t`) THEN
          REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_ARITH_TAC];
        ONCE_REWRITE_TAC[INTER_COMM] THEN
        REWRITE_TAC[INTER; SUM_RESTRICT_SET] THEN ASM_CASES_TAC `n = 0` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          ASM_REWRITE_TAC[SUM_SING; NUMSEG_SING; real_pow] THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_1; LE_0; REAL_ADD_RID] THEN
          MATCH_MP_TAC(REAL_ARITH `s:real = t /\ d < e ==> s + d < t + e`) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
            ASM_SIMP_TAC[ARITH_RULE `~(n = 0) /\ m <= n - 1 ==> m < n`];
            REWRITE_TAC[real_pow; real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
            CONV_TAC REAL_RAT_REDUCE_CONV THEN
            REWRITE_TAC[REAL_ARITH `&1 / &2 * x < x <=> &0 < x`] THEN
            SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]]]];
      MP_TAC(ISPEC `{ sum (x INTER (0..n)) (\i. inv(&3 pow i)) | n IN (:num) }`
          SUP) THEN REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `&3 / &2 / &3 pow 0` THEN
      SIMP_TAC[lemma; REAL_LT_IMP_LE]]]);;

let UNCOUNTABLE_REAL = prove
 (`~COUNTABLE(:real)`,
  REWRITE_TAC[COUNTABLE; CARD_NOT_LE; ge_c] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN
  REWRITE_TAC[CANTOR_THM_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[CARD_EQ_REAL]);;

let CARD_EQ_REAL_IMP_UNCOUNTABLE = prove
 (`!s. s =_c (:real) ==> ~COUNTABLE s`,
  GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o ISPEC `(:real)` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] CARD_EQ_COUNTABLE)) THEN
  REWRITE_TAC[UNCOUNTABLE_REAL] THEN ASM_MESON_TAC[CARD_EQ_SYM]);;
