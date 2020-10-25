(* ========================================================================= *)
(* Some general material about ordered sets of various kinds including WQOs. *)
(* Proof of some useful AC equivalents like wellordering and Zorn's Lemma.   *)
(* ========================================================================= *)

let PBETA_TAC = CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV);;

let SUBSET_PRED = prove
 (`!P Q. P SUBSET Q <=> !x. P x ==> Q x`,
  REWRITE_TAC[SUBSET; IN]);;

let UNIONS_PRED = prove
 (`UNIONS P = \x. ?p. P p /\ p x`,
  REWRITE_TAC[UNIONS; FUN_EQ_THM; IN_ELIM_THM; IN]);;

(* ======================================================================== *)
(* (1) Definitions and general lemmas.                                      *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* Field of an uncurried binary relation                                    *)
(* ------------------------------------------------------------------------ *)

let fld = new_definition
 `fld R = {x:A | ?y. R x y \/ R y x}`;;

let IN_FLD = prove
 (`!l x:A. x IN fld l <=> ?y. l x y \/ l y x`,
  REWRITE_TAC[fld; IN_ELIM_THM]);;

let FLD_EQ_EMPTY = prove
 (`!R:A->A->bool. fld R = {} <=> R = (\x y. F)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[fld] THEN SET_TAC[]);;

let FLD_SUBSET = prove
 (`!l r. (!x y. l x y ==> r x y) ==> fld l SUBSET fld r`,
  REWRITE_TAC[fld] THEN SET_TAC[]);;

let FINITE_FLD = prove
 (`!l:A->A->bool. FINITE(fld l) <=> FINITE {(x,y) | l x y}`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP FINITE_CROSS o W CONJ);
    DISCH_THEN((fun th ->
     MP_TAC(ISPEC `FST:A#A->A` th) THEN MP_TAC(ISPEC `SND:A#A->A` th)) o
     MATCH_MP FINITE_IMAGE) THEN
    REWRITE_TAC[IMP_IMP; GSYM FINITE_UNION]] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[IN_CROSS; fld; IN_IMAGE; IN_ELIM_THM; IN_UNION] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Various kinds of order                                                    *)
(* ------------------------------------------------------------------------- *)

let qoset = new_definition
 `qoset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z)`;;

let poset = new_definition
 `poset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z) /\
       (!x y. l x y /\ l y x ==> x = y)`;;

let toset = new_definition
 `toset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z) /\
       (!x y. l x y /\ l y x ==> x = y) /\
       (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x)`;;

let woset = new_definition
  `woset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z) /\
       (!x y. l x y /\ l y x ==> x = y) /\
       (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x) /\
       (!s. s SUBSET fld l /\ ~(s = {})
            ==> ?x. x IN s /\ !y. y IN s ==> l x y)`;;

let wqoset = new_definition
 `wqoset (l:A->A->bool) <=>
        (!x. x IN fld l ==> l x x) /\
        (!x y z. l x y /\ l y z ==> l x z) /\
        (!s. s SUBSET fld l
             ==> ?t. FINITE t /\ t SUBSET s /\
                     !y. y IN s ==> ?x. x IN t /\ l x y)`;;

(* ------------------------------------------------------------------------- *)
(* Chains and antichains (subsets of the carrier, not the ordering)          *)
(* ------------------------------------------------------------------------- *)

let chain = new_definition
  `chain (l:A->A->bool) s <=>
        !x y. x IN s /\ y IN s ==> l x y \/ l y x`;;

let antichain = new_definition
  `antichain (l:A->A->bool) s <=>
        s SUBSET fld l /\ pairwise (\x y. ~(l x y)) s`;;

let CHAIN = prove
 (`!l s:A->bool.
        chain l s <=>
        s SUBSET fld l /\
        !x y. x IN s /\ y IN s ==> l x y \/ l y x`,
  REWRITE_TAC[chain; fld] THEN SET_TAC[]);;

let ANTICHAIN = prove
 (`!l s:A->bool.
        antichain l s <=>
        s SUBSET fld l /\
        !x y. x IN s /\ y IN s /\ ~(x = y) ==> ~(l x y)`,
  REWRITE_TAC[antichain; pairwise; fld] THEN SET_TAC[]);;

let CHAIN_SUBSET = prove
 (`!(l:A->A->bool) s t. chain l s /\ t SUBSET s ==> chain l t`,
  REWRITE_TAC[chain] THEN SET_TAC[]);;

let ANTICHAIN_SUBSET = prove
 (`!(l:A->A->bool) s t. antichain l s /\ t SUBSET s ==> antichain l t`,
  REWRITE_TAC[ANTICHAIN] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The trivial implications.                                                 *)
(* ------------------------------------------------------------------------- *)

let QOSET_REFL = prove
 (`!l (x:A). qoset l ==> (l x x <=> x IN fld l)`,
  REWRITE_TAC[qoset; fld; IN_ELIM_THM] THEN MESON_TAC[]);;

let QOSET_FLD = prove
 (`!l:A->A->bool. qoset l ==> fld l = {x | l x x}`,
  SIMP_TAC[QOSET_REFL] THEN SET_TAC[]);;

let WOSET_IMP_TOSET = prove
 (`!l:A->A->bool. woset l ==> toset l`,
  GEN_TAC THEN REWRITE_TAC[woset; toset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let WOSET_IMP_POSET = prove
 (`!l:A->A->bool. woset l ==> poset l`,
  GEN_TAC THEN REWRITE_TAC[woset; poset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let WOSET_IMP_QOSET = prove
 (`!l:A->A->bool. woset l ==> qoset l`,
  GEN_TAC THEN REWRITE_TAC[woset; qoset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let TOSET_IMP_POSET = prove
 (`!l:A->A->bool. toset l ==> poset l`,
  GEN_TAC THEN REWRITE_TAC[toset; poset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let TOSET_IMP_QOSET = prove
 (`!l:A->A->bool. toset l ==> qoset l`,
  GEN_TAC THEN REWRITE_TAC[toset; qoset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let POSET_IMP_QOSET = prove
 (`!l:A->A->bool. poset l ==> qoset l`,
  GEN_TAC THEN REWRITE_TAC[poset; qoset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let WQOSET_IMP_QOSET = prove
 (`!l:A->A->bool. wqoset l ==> qoset l`,
  GEN_TAC THEN REWRITE_TAC[wqoset; qoset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* In general, these need to be distinguished, but not for partial orders.   *)
(* ------------------------------------------------------------------------- *)

let strictly = new_definition
 `strictly R = \x y:A. R x y /\ ~(R y x)`;;

let properly = new_definition
 `properly R = \x y:A. R x y /\ ~(x = y)`;;

let PROPERLY_EQ_STRICTLY = prove
 (`!l:A->A->bool. poset l ==> properly l = strictly l`,
  REWRITE_TAC[poset; properly; strictly; FUN_EQ_THM] THEN MESON_TAC[]);;

let STRICTLY_EQ_PROPERLY = prove
 (`!l:A->A->bool. poset l ==> strictly l = properly l`,
  REWRITE_TAC[poset; properly; strictly; FUN_EQ_THM] THEN MESON_TAC[]);;

let STRICTLY_IMP_PROPERLY = prove
 (`!l x y:A. qoset l /\ strictly l x y ==> properly l x y`,
  REWRITE_TAC[qoset; properly; strictly; FUN_EQ_THM] THEN MESON_TAC[]);;

let STRICTLY_STRICTLY = prove
 (`!R:A->A->bool. strictly(strictly R) = strictly R`,
  REWRITE_TAC[FUN_EQ_THM; strictly] THEN MESON_TAC[]);;

let PROPERLY_PROPERLY = prove
 (`!R:A->A->bool. properly(properly R) = properly R`,
  REWRITE_TAC[FUN_EQ_THM; properly] THEN MESON_TAC[]);;

let STRICTLY_PROPERLY = prove
 (`!R:A->A->bool. strictly(properly R) = strictly R`,
  REWRITE_TAC[FUN_EQ_THM; strictly; properly] THEN MESON_TAC[]);;

let PROPERLY_STRICTLY = prove
 (`!R:A->A->bool. properly(strictly R) = strictly R`,
  REWRITE_TAC[FUN_EQ_THM; strictly; properly] THEN MESON_TAC[]);;

let PROPERLY_MONO = prove
 (`!R S. (!x y. R x y ==> S x y)
         ==> (!x y. properly R x y ==> properly S x y)`,
  REWRITE_TAC[properly] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Various interrelations and alternative forms of definitions.              *)
(* ------------------------------------------------------------------------- *)

let POSET_QOSET = prove
 (`!l:A->A->bool.
        poset l <=> qoset l /\ (!x y. l x y /\ l y x ==> x = y)`,
  REWRITE_TAC[poset; qoset; GSYM CONJ_ASSOC]);;

let TOSET = prove
 (`!l:A->A->bool.
        toset l <=>
        (!x y z. l x y /\ l y z ==> l x z) /\
        (!x y. l x y /\ l y x ==> x = y) /\
        (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x)`,
  REWRITE_TAC[toset] THEN MESON_TAC[]);;

let TOSET_POSET = prove
 (`!l:A->A->bool.
        toset l <=>
        poset l /\ (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x)`,
  REWRITE_TAC[toset; poset; GSYM CONJ_ASSOC]);;

let WOSET_TOSET = prove
 (`!l:A->A->bool.
       woset l <=>
       toset l /\
       !s. s SUBSET fld l /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> l x y`,
  REWRITE_TAC[woset; toset; GSYM CONJ_ASSOC]);;

let WQOSET = prove
 (`!l:A->A->bool.
        wqoset l <=>
        (!x y z. l x y /\ l y z ==> l x z) /\
        (!s. s SUBSET fld l
             ==> ?t. FINITE t /\
                     t SUBSET s /\
                     !y. y IN s ==> ?x. x IN t /\ l x y)`,
  GEN_TAC THEN REWRITE_TAC[wqoset] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN ASM SET_TAC[]);;

let WQOSET_QOSET = prove
 (`!l:A->A->bool.
       wqoset l <=>
       qoset l /\
       !s. s SUBSET fld l
           ==> ?t. FINITE t /\ t SUBSET s /\
                   !y. y IN s ==> ?x. x IN t /\ l x y`,
  REWRITE_TAC[wqoset; qoset; GSYM CONJ_ASSOC]);;

let WOSET_POSET = prove
 (`!l:A->A->bool.
       woset l <=>
       poset l /\
       !s. s SUBSET fld l /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> l x y`,
  GEN_TAC THEN REWRITE_TAC[woset; poset] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x:A,y}`) THEN ASM SET_TAC[]);;

let WOSET = prove
 (`!l:A->A->bool.
       woset l <=>
       (!x y. l x y /\ l y x ==> x = y) /\
       !s. s SUBSET fld l /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> l x y`,
  GEN_TAC THEN REWRITE_TAC[woset] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(r ==> p) /\ r /\ q ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{x:A,y}`) THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{x:A,y,z}`) THEN
    REWRITE_TAC[fld] THEN ASM SET_TAC[]]);;

let WOSET_WF = prove
 (`!l:A->A->bool.
        woset l <=>
        (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x) /\
        WF(properly l)`,
  GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (q ==> (p <=> r)) ==> (p <=> q /\ r)`) THEN
  CONJ_TAC THENL [SIMP_TAC[woset]; DISCH_TAC THEN REWRITE_TAC[WOSET]] THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (q ==> (p <=> r)) ==> (q /\ r <=> p)`) THEN
  REWRITE_TAC[properly] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP WF_ANTISYM) THEN MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[WF] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. x IN s`) THEN ASM SET_TAC[];
    X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{x:A | x IN fld l /\ P x}`) THEN
    REWRITE_TAC[fld] THEN RULE_ASSUM_TAC(REWRITE_RULE[fld]) THEN
    ASM SET_TAC[]]);;

let WOSET_IMP_WQOSET = prove
 (`!l:A->A->bool. woset l ==> wqoset l`,
  GEN_TAC THEN REWRITE_TAC[woset; wqoset] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [ASM_MESON_TAC[FINITE_EMPTY; SUBSET_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x:A}` THEN ASM_REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[]);;

let WQOSET_SUPERSET = prove
 (`!l m:A->A->bool.
        wqoset l /\
        qoset m /\
        fld m SUBSET fld l /\
        (!x y. l x y ==> m x y)
        ==> wqoset m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WQOSET_QOSET] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:A->bool` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM SET_TAC[]);;

let [WQOSET_NOBAD; WQOSET_NOBAD_SUBSEQ; WQOSET_ANTICHAIN] =
  (CONJUNCTS o prove)
 (`(!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        !x. (!n:num. x n IN fld l) ==> ?i j. i < j /\ l (x i) (x j)) /\
   (!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        !x. (!n. x n IN fld l)
            ==> ?r:num->num.
                    (!m n. m < n ==> r(m) < r(n)) /\
                    (!i j. i <= j ==> l (x(r i)) (x(r j)))) /\
   (!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        WF(strictly l) /\
        !s. antichain l s ==> FINITE s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `l:A->A->bool` THEN
  REWRITE_TAC[wqoset; qoset; antichain; FORALL_AND_THM] THEN
  ASM_CASES_TAC `!x:A. x IN fld l ==> l x x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `!x y z:A. l x y /\ l y z ==> l x z` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> s) /\ (s ==> p)
    ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `x:num->A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (x:num->A) (:num)`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE]] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; SUBSET_UNIV; IN_UNIV] THEN
    REWRITE_TAC[num_FINITE] THEN ASM_MESON_TAC[LT_SUC_LE];
    DISCH_TAC THEN X_GEN_TAC `x:num->A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~INFINITE {n | !p. n < p ==> ~l ((x:num->A) n) (x p)}`
    MP_TAC THENL
     [REWRITE_TAC[INFINITE_ENUMERATE_EQ; NOT_EXISTS_THM] THEN
      X_GEN_TAC `r:num->num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->A) o (r:num->num)`) THEN
      ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
      REWRITE_TAC[INFINITE; num_FINITE; IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN
    SUBGOAL_THEN
     `?t:num->num.
        (!n:num. T) /\
        (!n. t n < t (SUC n) /\
             (l:A->A->bool) (x(t n + p + 1)) (x(t(SUC n) + p + 1)))`
    MP_TAC THENL
    [MATCH_MP_TAC DEPENDENT_CHOICE THEN REWRITE_TAC[] THEN
     X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o
       GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] o SPEC `n + p + 1`) THEN
     REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; ARITH_RULE `~(n + p + 1 <= p)`] THEN
     MATCH_MP_TAC(MESON[]
      `!p. (!m. P m ==> Q(m - (p + 1))) ==> (?m. P m) ==> (?m. Q m)`) THEN
     EXISTS_TAC `p:num` THEN X_GEN_TAC `q:num` THEN MATCH_MP_TAC(TAUT
      `(p ==> q) /\ (p ==> (r <=> s)) ==> p /\ r ==> q /\ s`) THEN
     REPEAT STRIP_TAC THENL [ALL_TAC; AP_TERM_TAC THEN AP_TERM_TAC] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `t:num->num` THEN
     STRIP_TAC THEN EXISTS_TAC `\i. (t:num->num) i + p + 1` THEN
     REWRITE_TAC[] THEN CONJ_TAC THENL
      [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
       ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN ARITH_TAC;
       MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
       ASM_MESON_TAC[]]];
     DISCH_TAC THEN CONJ_TAC THENL
      [REWRITE_TAC[WF_DCHAIN; strictly; NOT_EXISTS_THM; FORALL_AND_THM] THEN
       X_GEN_TAC `x:num->A` THEN STRIP_TAC THEN
       SUBGOAL_THEN
        `!m n:num. m < n ==> (l:A->A->bool) (x n) (x m) /\ ~l (x m) (x n)`
       ASSUME_TAC THENL
        [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[];
         FIRST_X_ASSUM(MP_TAC o SPEC `x:num->A`) THEN
         REWRITE_TAC[fld; IN_ELIM_THM; NOT_IMP] THEN
         ASM_MESON_TAC[ARITH_RULE `n < SUC n`; LT_IMP_LE]];
       X_GEN_TAC `s:A->bool` THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
       REWRITE_TAC[REWRITE_RULE[INFINITE] INFINITE_ENUMERATE_SUBSET] THEN
       REWRITE_TAC[INJECTIVE_ALT; LEFT_IMP_EXISTS_THM] THEN
       X_GEN_TAC `x:num->A` THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `x:num->A`) THEN
       REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `r:num->num`
        (CONJUNCTS_THEN(MP_TAC o SPECL [`n:num`; `SUC n`]))) THEN
       REPEAT(ANTS_TAC THENL [ARITH_TAC; DISCH_TAC]) THEN
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
       DISCH_THEN(MP_TAC o SPECL
        [`(x:num->A)(r(n:num))`; `(x:num->A)(r(SUC n))`]) THEN
       ASM_SIMP_TAC[LT_IMP_NE]];
    STRIP_TAC THEN X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[MESON[]
     `(?x. P x /\ Q x /\ R x) <=> ~(!x. P x /\ Q x ==> ~R x)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
     [NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?x:num->A.
        !n. x n IN s DIFF UNIONS {{y | l (x m) y} | m < n} /\
            !z. z IN s DIFF UNIONS {{y | l (x m) y} | m < n}
                ==> ~(l z (x n) /\ ~(l (x n) z))`
    MP_TAC THENL
     [MATCH_MP_TAC(MATCH_MP WF_REC_EXISTS WF_num) THEN
      REWRITE_TAC[UNIONS_GSPEC] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`x:num->A`; `n:num`] THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN DISCH_THEN(LABEL_TAC "*") THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (x:num->A) {m | m < n}`) THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
       `\y. y IN s /\ !m:num. m < n ==> ~((l:A->A->bool) (x m) y)` o
       GEN_REWRITE_RULE I [WF]) THEN
      ASM_REWRITE_TAC[strictly] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_AND_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:num->A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `FINITE(IMAGE (x:num->A) (:num))` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[PAIRWISE_IMAGE] THEN REWRITE_TAC[pairwise; IN_UNIV];
        REWRITE_TAC[GSYM INFINITE] THEN MATCH_MP_TAC INFINITE_IMAGE THEN
        REWRITE_TAC[num_INFINITE; IN_UNIV]] THEN
      MATCH_MP_TAC WLOG_LT THEN ASM SET_TAC[]]]);;

let WQOSET_IMP_WF = prove
 (`!l:A->A->bool. wqoset l ==> WF(strictly l)`,
  SIMP_TAC[WQOSET_ANTICHAIN]);;

let WQOSET_WF_SUPERSET = prove
 (`!l m:A->A->bool.
        wqoset l /\ qoset m /\ fld m SUBSET fld l /\ (!x y. l x y ==> m x y)
        ==> WF(strictly m)`,
  MESON_TAC[WQOSET_SUPERSET; WQOSET_IMP_WF]);;

let WQOSET_WF_SUPERSET_EQ = prove
 (`!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        !m. qoset m /\ fld m = fld l /\ (!x y. l x y ==> m x y)
            ==> WF(strictly m)`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[WQOSET_WF_SUPERSET; WQOSET_IMP_QOSET; SUBSET_REFL];
    STRIP_TAC THEN ASM_REWRITE_TAC[WQOSET_NOBAD]] THEN
  X_GEN_TAC `a:num->A` THEN DISCH_TAC THEN MATCH_MP_TAC(MESON[]
   `~(!i j. P i j ==> ~Q i j) ==> ?i j. P i j /\ Q i j`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
   `\x y:A. l x y \/ ?i j:num. i < j /\ l x (a j) /\ l (a i) y`) THEN
  REWRITE_TAC[qoset; NOT_IMP; GSYM CONJ_ASSOC] THEN SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `r /\ (r ==> p /\ q /\ s) ==> p /\ q /\ r /\ s`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[fld] THEN RULE_ASSUM_TAC(REWRITE_RULE[fld]) THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [qoset]) THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LT_TRANS; LT_CASES]; ALL_TAC] THEN
  REWRITE_TAC[WF_DCHAIN; strictly] THEN EXISTS_TAC `a:num->A` THEN
  X_GEN_TAC `n:num` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `n < SUC n`]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < SUC n`; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `l:num`] THEN STRIP_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `~(n < l) /\ ~(k < SUC n) ==> ~(k < l)`]);;

let WOSET_WQOSET = prove
 (`!l:A->A->bool. woset l <=> toset l /\ wqoset l`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[WOSET_IMP_TOSET; WOSET_IMP_WQOSET] THEN
  SIMP_TAC[WOSET_WF; PROPERLY_EQ_STRICTLY; WQOSET_IMP_WF; TOSET_IMP_POSET] THEN
  REWRITE_TAC[toset] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Restrictions of ordered sets.                                             *)
(* ------------------------------------------------------------------------- *)

let FLD_RESTRICT_QOSET = prove
 (`!(l:A->A->bool) P.
        qoset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}`,
  REWRITE_TAC[qoset; fld] THEN SET_TAC[]);;

let FLD_RESTRICT_POSET = prove
 (`!(l:A->A->bool) P.
        poset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}`,
  SIMP_TAC[FLD_RESTRICT_QOSET; POSET_IMP_QOSET]);;

let FLD_RESTRICT_TOSET = prove
 (`!(l:A->A->bool) P.
        toset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}`,
  SIMP_TAC[FLD_RESTRICT_QOSET; TOSET_IMP_QOSET]);;

let FLD_RESTRICT_WOSET = prove
 (`!(l:A->A->bool) P.
        woset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}`,
  SIMP_TAC[FLD_RESTRICT_QOSET; WOSET_IMP_QOSET]);;

let FLD_RESTRICT_WQOSET = prove
 (`!(l:A->A->bool) P.
       wqoset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}`,
  SIMP_TAC[FLD_RESTRICT_QOSET; WQOSET_IMP_QOSET]);;

let QOSET_RESTRICT = prove
 (`!(l:A->A->bool) P. qoset l ==> qoset (\x y. P x /\ P y /\ l x y)`,
  REWRITE_TAC[qoset; fld] THEN SET_TAC[]);;

let POSET_RESTRICT = prove
 (`!(l:A->A->bool) P. poset l ==> poset (\x y. P x /\ P y /\ l x y)`,
  REWRITE_TAC[poset; fld] THEN SET_TAC[]);;

let TOSET_RESTRICT = prove
 (`!(l:A->A->bool) P. toset l ==> toset (\x y. P x /\ P y /\ l x y)`,
  REWRITE_TAC[toset; fld] THEN SET_TAC[]);;

let WOSET_RESTRICT = prove
 (`!(l:A->A->bool) P. woset l ==> woset (\x y. P x /\ P y /\ l x y)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[WOSET_POSET; FLD_RESTRICT_POSET; POSET_RESTRICT] THEN
  SET_TAC[]);;

let WQOSET_RESTRICT = prove
 (`!(l:A->A->bool) P. wqoset l ==> wqoset (\x y. P x /\ P y /\ l x y)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[WQOSET_NOBAD_SUBSEQ; FLD_RESTRICT_QOSET; QOSET_RESTRICT] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Finite sets have maximal/minimal/greatest/least in various senses.        *)
(* ------------------------------------------------------------------------- *)

let QOSET_MIN,QOSET_MAX = (CONJ_PAIR o prove)
 (`(!l s:A->bool.
        qoset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(strictly l x a)) /\
   (!l s:A->bool.
        qoset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(strictly l a x))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMP_IMP; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_INSERT; EXISTS_IN_INSERT; INSERT_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; strictly; TAUT `~(p /\ ~p)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[qoset; SUBSET; fld; IN_ELIM_THM]) THEN
  ASM METIS_TAC[]);;

let POSET_MIN,POSET_MAX = (CONJ_PAIR o prove)
 (`(!l s:A->bool.
        poset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(properly l x a)) /\
   (!l s:A->bool.
        poset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(properly l a x))`,
  SIMP_TAC[PROPERLY_EQ_STRICTLY; QOSET_MIN; QOSET_MAX; POSET_IMP_QOSET]);;

let TOSET_MIN,TOSET_MAX = (CONJ_PAIR o prove)
 (`(!l s:A->bool.
        toset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> l a x) /\
   (!l s:A->bool.
        toset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> l x a)`,
  CONJ_TAC THENL [MP_TAC POSET_MIN; MP_TAC POSET_MAX] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[TOSET_IMP_POSET] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[properly] THEN RULE_ASSUM_TAC(REWRITE_RULE[toset]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The trivial relation is every kind of ordered set.                        *)
(* ------------------------------------------------------------------------- *)

let FLD_TRIVIAL = prove
 (`fld(\x y:A. F) = {}`,
  REWRITE_TAC[FLD_EQ_EMPTY]);;

let WOSET_TRIVIAL = prove
 (`woset(\x y:A. F)`,
  REWRITE_TAC[woset; FLD_TRIVIAL; NOT_IN_EMPTY] THEN SET_TAC[]);;

let WQOSET_TRIVIAL = prove
 (`wqoset(\x y:A. F)`,
  SIMP_TAC[WOSET_IMP_WQOSET; WOSET_TRIVIAL]);;

let TOSET_TRIVIAL = prove
 (`toset(\x y:A. F)`,
  SIMP_TAC[WOSET_IMP_TOSET; WOSET_TRIVIAL]);;

let POSET_TRIVIAL = prove
 (`poset(\x y:A. F)`,
  SIMP_TAC[WOSET_IMP_POSET; WOSET_TRIVIAL]);;

let QOSET_TRIVIAL = prove
 (`qoset(\x y:A. F)`,
  SIMP_TAC[WOSET_IMP_QOSET; WOSET_TRIVIAL]);;

(* ------------------------------------------------------------------------- *)
(* The natural numbers with the usual <= are every kind of ordered set.      *)
(* ------------------------------------------------------------------------- *)

let FLD_num = prove
 (`fld(<=) = (:num)`,
  REWRITE_TAC[fld; IN_ELIM_THM; LE_CASES] THEN SET_TAC[]);;

let WOSET_num = prove
 (`woset((<=):num->num->bool)`,
  REWRITE_TAC[WOSET_WF; fld; IN_ELIM_THM; LE_CASES; properly] THEN
  REWRITE_TAC[GSYM LT_LE; ETA_AX; WF_num]);;

let WQOSET_num = prove
 (`wqoset((<=):num->num->bool)`,
  SIMP_TAC[WOSET_IMP_WQOSET; WOSET_num]);;

let TOSET_num = prove
 (`toset((<=):num->num->bool)`,
  SIMP_TAC[WOSET_IMP_TOSET; WOSET_num]);;

let POSET_num = prove
 (`poset((<=):num->num->bool)`,
  SIMP_TAC[WOSET_IMP_POSET; WOSET_num]);;

let QOSET_num = prove
 (`qoset((<=):num->num->bool)`,
  SIMP_TAC[WOSET_IMP_QOSET; WOSET_num]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise orders (no domain restriction, a quasi-order in general).       *)
(* Hence Dickson's lemma in the general WQO setting and common special case. *)
(* ------------------------------------------------------------------------- *)

let QOSET_POINTWISE = prove
 (`!l s. qoset(\x y:K->A. !i. i IN s ==> l (x i) (y i)) <=>
         s = {} \/ qoset l`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:K->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; qoset]; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[qoset; fld; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC(MESON[]
   `(!a. P (\i. a) ==> Q a) ==> (!a. P a) ==> !b. Q b`) THEN GEN_TAC)
  THENL [ALL_TAC; ASM SET_TAC[]] THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:A`) THEN EXISTS_TAC `(\i. y):K->A` THEN
  ASM SET_TAC[]);;

let FLD_POINTWISE = prove
 (`!l s. qoset l
         ==> fld(\x y:K->A. !i. i IN s ==> l (x i) (y i)) =
             {x | !i. i IN s ==> x i IN fld l}`,
  SIMP_TAC[QOSET_FLD; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) QOSET_FLD o lhand o snd) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[QOSET_POINTWISE]);;

let WQOSET_POINTWISE = prove
 (`!l s. wqoset l /\ FINITE s
         ==> wqoset(\x y:K->A. !i. i IN s ==> l (x i) (y i))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; WQOSET_NOBAD_SUBSEQ] THEN
  GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[QOSET_POINTWISE; FLD_POINTWISE; IN_UNIV; IN_ELIM_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`]] THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN DISCH_THEN(fun th ->
    X_GEN_TAC `x:num->K->A` THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:num->K->A` th)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l:num->num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i:num. (x:num->K->A) (l i) a`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(l:num->num) o (r:num->num)` THEN
  ASM_SIMP_TAC[o_THM] THEN ASM_MESON_TAC[LE_LT]);;

let DICKSON = prove
 (`!n x:num->num->num. ?i j. i < j /\ (!k. k < n ==> x i k <= x j k)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(<=):num->num->bool`; `{m:num | m < n}`]
        WQOSET_POINTWISE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WQOSET_NOBAD] THEN
  SIMP_TAC[FLD_POINTWISE; WQOSET_IMP_QOSET; QOSET_POINTWISE] THEN
  SIMP_TAC[WOSET_IMP_WQOSET; WOSET_num; FLD_num; IN_UNIV; IN_ELIM_THM] THEN
  SIMP_TAC[FINITE_NUMSEG_LT]);;

(* ------------------------------------------------------------------------ *)
(* General (reflexive) notion of initial segment.                           *)
(* ------------------------------------------------------------------------ *)

parse_as_infix("inseg",(12,"right"));;

let inseg = new_definition
  `(l:A->A->bool) inseg m <=> !x y. l x y <=> m x y /\ fld(l) y`;;

let INSEG_ANTISYM = prove
 (`!l m:A->A->bool. l inseg m /\ m inseg l ==> l = m`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[inseg] THEN MESON_TAC[]);;

let INSEG_REFL = prove
 (`!l:A->A->bool. l inseg l`,
  REWRITE_TAC[inseg; REWRITE_RULE[IN] IN_FLD] THEN MESON_TAC[]);;

let INSEG_TRANS = prove
 (`!l m n:A->A->bool. l inseg m /\ m inseg n ==> l inseg n`,
  REWRITE_TAC[inseg; REWRITE_RULE[IN] IN_FLD] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Specific form of initial segment: `all elements in fld(l) less than a`.  *)
(* ------------------------------------------------------------------------ *)

let linseg = new_definition
  `linseg (l:A->A->bool) a = \ x y. l x y /\ (properly l) y a`;;

(* ------------------------------------------------------------------------ *)
(* `Ordinals`, i.e. canonical wosets using choice operator.                 *)
(* ------------------------------------------------------------------------ *)

let ordinal = new_definition
  `ordinal(l:A->A->bool) <=>
    woset(l) /\ (!x. fld(l) x ==> (x = (@) (\y. ~(properly l) y x)))`;;

(* ------------------------------------------------------------------------ *)
(* Now useful things about the orderings                                    *)
(* ------------------------------------------------------------------------ *)

let [POSET_REFL; POSET_TRANS; POSET_ANTISYM] =
  map (GEN `l:A->A->bool` o DISCH_ALL)
      (CONJUNCTS(REWRITE_RULE[poset; IN] (ASSUME `poset (l:A->A->bool)`)));;

let POSET_FLDEQ = prove
 (`!l:A->A->bool. poset l ==> (!x. fld(l) x <=> l x x)`,
  MESON_TAC[POSET_REFL; REWRITE_RULE[IN] IN_FLD]);;

let [WOSET_REFL; WOSET_TRANS; WOSET_ANTISYM; WOSET_TOTAL; WOSET_WELL] =
  map (GEN `l:A->A->bool` o DISCH_ALL)
      (CONJUNCTS(REWRITE_RULE[woset; SUBSET; GSYM MEMBER_NOT_EMPTY; IN]
         (ASSUME `woset (l:A->A->bool)`)));;

let WOSET_FLDEQ = prove
 (`!l:A->A->bool. woset l ==> (!x. fld(l) x <=> l x x)`,
  MESON_TAC[WOSET_IMP_POSET; POSET_FLDEQ]);;

let WOSET_TRANS_LESS = prove
 (`!l:A->A->bool. woset l ==>
       !x y z. (properly l) x y /\ l y z ==> (properly l) x z`,
  REWRITE_TAC[woset; properly] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Misc lemmas.                                                             *)
(* ------------------------------------------------------------------------ *)

let PAIRED_EXT = prove
 (`!(l:A->B->C) m. (!x y. l x y = m x y) <=> (l = m)`,
  REWRITE_TAC[FUN_EQ_THM]);;

let WOSET_TRANS_LE = prove
 (`!l:A->A->bool. woset l ==>
       !x y z. l x y /\ (properly l) y z ==> (properly l) x z`,
  REWRITE_TAC[properly] THEN MESON_TAC[WOSET_TRANS; WOSET_ANTISYM]);;

let WOSET_WELL_CONTRAPOS = prove
 (`!l:A->A->bool. woset l ==>
                (!P. (!x. P x ==> fld(l) x) /\ (?x. P x) ==>
                     (?y. P y /\ (!z. (properly l) z y ==> ~P z)))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `P:A->bool` o MATCH_MP WOSET_WELL) THEN
  ASM_MESON_TAC[WOSET_TRANS_LE; properly]);;

let WOSET_TOTAL_LE = prove
 (`!l:A->A->bool. woset l
                 ==> !x y. fld(l) x /\ fld(l) y ==> l x y \/ (properly l) y x`,
  REWRITE_TAC[properly] THEN MESON_TAC[WOSET_REFL; WOSET_TOTAL]);;

let WOSET_TOTAL_LT = prove
 (`!l:A->A->bool. woset l ==>
     !x y. fld(l) x /\ fld(l) y
           ==> x = y \/ (properly l) x y \/ (properly l) y x`,
  REWRITE_TAC[properly] THEN MESON_TAC[WOSET_TOTAL]);;

let ORDINAL_IMP_WOSET = prove
 (`!l:A->A->bool. ordinal l ==> woset l`,
  SIMP_TAC[ordinal]);;

let WOSET_FINITE_TOSET = prove
 (`!l:A->A->bool. toset l /\ FINITE {(x,y) | l x y} ==> woset l`,
  ONCE_REWRITE_TAC[GSYM FINITE_FLD] THEN
  SIMP_TAC[TOSET_POSET; WOSET_WF; properly; poset; IN] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WF_FINITE THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; X_GEN_TAC `a:A`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    FINITE_SUBSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD; IN] THEN
  ASM_MESON_TAC[]);;

(* ======================================================================== *)
(* (2) AXIOM OF CHOICE ==> CANTOR-ZERMELO WELLORDERING THEOREM              *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* UNIONS of initial segments is an initial segment.                        *)
(* ------------------------------------------------------------------------ *)

let UNION_FLD = prove
 (`!P. fld(\x y:A. ?l. P l /\ l x y) x <=> ?l. P l /\ fld(l) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN MESON_TAC[]);;

let UNION_INSEG = prove
 (`!P (l:A->A->bool).
        (!m. P m ==> m inseg l)
        ==> (\x y. ?l. P l /\ l x y) inseg l`,
  REWRITE_TAC[inseg; UNION_FLD; UNIONS_PRED] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Initial segment of a woset is a woset.                                   *)
(* ------------------------------------------------------------------------ *)

let INSEG_SUBSET = prove
 (`!(l:A->A->bool) m. m inseg l ==> !x y. m x y ==> l x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inseg] THEN MESON_TAC[]);;

let INSEG_SUBSET_FLD = prove
 (`!(l:A->A->bool) m. m inseg l ==> !x. fld(m) x ==> fld(l) x`,
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN MESON_TAC[INSEG_SUBSET]);;

let INSEG_FLD_SUBSET = prove
 (`!l m:A->A->bool. l inseg m ==> fld l SUBSET fld m`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN
  SET_TAC[]);;

let INSEG_WOSET = prove
 (`!(l:A->A->bool) m. m inseg l /\ woset l ==> woset m`,
  REWRITE_TAC[inseg] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WOSET; SUBSET; GSYM MEMBER_NOT_EMPTY; IN] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WOSET_ANTISYM];
    X_GEN_TAC `P:A->bool` THEN
    FIRST_ASSUM(MP_TAC o SPEC `P:A->bool` o MATCH_MP WOSET_WELL) THEN
    REWRITE_TAC[fld; SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]]);;

let INSEG_ORDINAL = prove
 (`!l m:A->A->bool. m inseg l /\ ordinal l ==> ordinal m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INSEG_WOSET]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_REWRITE_TAC[properly]);;

(* ------------------------------------------------------------------------ *)
(* Properties of segments of the `linseg` form.                             *)
(* ------------------------------------------------------------------------ *)

let LINSEG_INSEG = prove
 (`!(l:A->A->bool) a. woset l ==> (linseg l a) inseg l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[inseg; linseg; REWRITE_RULE[IN] IN_FLD] THEN PBETA_TAC THEN
  ASM_MESON_TAC[WOSET_TRANS_LE]);;

let LINSEG_WOSET = prove
 (`!(l:A->A->bool) a. woset l ==> woset(linseg l a)`,
  MESON_TAC[INSEG_WOSET; LINSEG_INSEG]);;

let LINSEG_FLD = prove
 (`!(l:A->A->bool) a x. woset l ==> (fld (linseg l a) x <=> (properly l) x a)`,
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD; linseg; properly] THEN PBETA_TAC THEN
  MESON_TAC[WOSET_REFL; WOSET_TRANS; WOSET_ANTISYM; REWRITE_RULE[IN] IN_FLD]);;

(* ------------------------------------------------------------------------ *)
(* Key fact: a proper initial segment is of the special form.               *)
(* ------------------------------------------------------------------------ *)

let INSEG_PROPER_SUBSET = prove
 (`!(l:A->A->bool) m. m inseg l /\ ~(l = m) ==>
                   ?x y. l x y /\ ~m x y`,
  REWRITE_TAC[GSYM PAIRED_EXT] THEN MESON_TAC[INSEG_SUBSET]);;

let INSEG_PROPER_SUBSET_FLD = prove
 (`!(l:A->A->bool) m. m inseg l /\ ~(l = m) ==>
                   ?a. fld(l) a /\ ~fld(m) a`,
  MESON_TAC[INSEG_PROPER_SUBSET; REWRITE_RULE[IN] IN_FLD; inseg]);;

let INSEG_LINSEG = prove
 (`!(l:A->A->bool) m. woset l ==>
      (m inseg l <=> (m = l) \/ (?a. fld(l) a /\ (m = linseg l a)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:A->A->bool = l` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[inseg; REWRITE_RULE[IN] IN_FLD] THEN MESON_TAC[]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[LINSEG_INSEG]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL_CONTRAPOS) THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. fld(l) x /\ ~fld(m) x`) THEN
  REWRITE_TAC[] THEN REWRITE_TAC[linseg; GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [ASM_MESON_TAC[INSEG_PROPER_SUBSET_FLD]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[INSEG_SUBSET; INSEG_SUBSET_FLD; REWRITE_RULE[IN] IN_FLD;
    WOSET_TOTAL_LE; properly; inseg]);;

(* ------------------------------------------------------------------------ *)
(* A proper initial segment can be extended by its bounding element.        *)
(* ------------------------------------------------------------------------ *)

let EXTEND_FLD = prove
 (`!(l:A->A->bool) x. woset l ==> (fld (\ x y. l x y /\ l y a) x <=> l x a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN PBETA_TAC THEN
  ASM_MESON_TAC[WOSET_TRANS; WOSET_REFL; REWRITE_RULE[IN] IN_FLD]);;

let EXTEND_INSEG = prove
 (`!(l:A->A->bool) a. woset l /\ fld(l) a ==> (\ x y. l x y /\ l y a) inseg l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inseg] THEN PBETA_TAC THEN
  REPEAT GEN_TAC THEN IMP_RES_THEN (fun t ->REWRITE_TAC[t]) EXTEND_FLD);;

let EXTEND_LINSEG = prove
 (`!(l:A->A->bool) a. woset l /\ fld(l) a ==>
       (\ x y. linseg l a  x y \/ (y = a) /\ (fld(linseg l a) x \/ (x = a)))
                inseg l`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC (MATCH_MP EXTEND_INSEG th)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  REPEAT GEN_TAC THEN IMP_RES_THEN (fun th -> REWRITE_TAC[th]) LINSEG_FLD THEN
  REWRITE_TAC[linseg; properly] THEN ASM_MESON_TAC[WOSET_REFL]);;

(* ------------------------------------------------------------------------ *)
(* Key canonicality property of ordinals.                                   *)
(* ------------------------------------------------------------------------ *)

let ORDINAL_CHAINED_LEMMA = prove
 (`!(k:A->A->bool) l m.
        ordinal(l) /\ ordinal(m)
        ==> k inseg l /\ k inseg m
            ==> k = l \/ k = m \/ ?a. fld(l) a /\ fld(m) a /\
                                      k = linseg l a /\
                                      k = linseg m a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN STRIP_TAC THEN
  EVERY_ASSUM(fun th -> TRY
    (fun g -> REWRITE_TAC[MATCH_MP INSEG_LINSEG th] g)) THEN
  ASM_CASES_TAC `k:A->A->bool = l` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k:A->A->bool = m` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a:A = b` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP th (ASSUME `fld(l) (a:A)`))) THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP th (ASSUME `fld(m) (b:A)`))) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `k = linseg m (b:A)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linseg; GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  ASM_MESON_TAC[WOSET_REFL; properly; REWRITE_RULE[IN] IN_FLD]);;

let ORDINAL_CHAINED = prove
 (`!(l:A->A->bool) m. ordinal(l) /\ ordinal(m) ==> m inseg l \/ l inseg m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[ordinal] th) THEN
                       ASSUME_TAC (MATCH_MP ORDINAL_CHAINED_LEMMA th)) THEN
  MP_TAC(SPEC `\k:A->A->bool. k inseg l /\ k inseg m` UNION_INSEG) THEN
  DISCH_THEN(fun th ->
    MP_TAC(CONJ (SPEC `l:A->A->bool` th) (SPEC `m:A->A->bool` th))) THEN
  REWRITE_TAC[TAUT `(a /\ b ==> a) /\ (a /\ b ==> b)`] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
                       FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN MP_TAC o
                       C MATCH_MP th)) THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME
   `(\x y. ?k. (k inseg l /\ k inseg m) /\ k x y) = linseg l (a:A)`) THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPECL [`a:A`; `a:A`]) THEN
  REWRITE_TAC[linseg] THEN PBETA_TAC THEN REWRITE_TAC[properly] THEN
  EXISTS_TAC
  `\x y. linseg l a x y \/ (y = a) /\ (fld(linseg l a) x \/ (x = a:A))` THEN
  PBETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC
     `(\x y. ?k. (k inseg l /\ k inseg m) /\ k x y) = linseg l (a:A)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EXTEND_LINSEG THEN ASM_REWRITE_TAC[]);;

let ORDINAL_FLD_UNIQUE = prove
 (`!l m:A->A->bool.
        ordinal l /\ ordinal m /\ fld l = fld m ==> l = m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A->A->bool`; `m:A->A->bool`]
        ORDINAL_CHAINED) THEN
  REWRITE_TAC[inseg; FUN_EQ_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]);;

let ORDINAL_FLD_SUBSET = prove
 (`!l m:A->A->bool.
        ordinal l /\ ordinal m /\ fld l SUBSET fld m ==> l inseg m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A->A->bool`; `m:A->A->bool`]
        ORDINAL_CHAINED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[INSEG_REFL] `x = y ==> x inseg y`) THEN
  MATCH_MP_TAC ORDINAL_FLD_UNIQUE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN ASM SET_TAC[]);;

let ORDINAL_FLD_SUBSET_EQ = prove
 (`!l m:A->A->bool.
        ordinal l /\ ordinal m ==> (fld l SUBSET fld m <=> l inseg m)`,
  MESON_TAC[ORDINAL_FLD_SUBSET; INSEG_FLD_SUBSET]);;

(* ------------------------------------------------------------------------ *)
(* Proof that any non-universe ordinal can be extended to its "successor".  *)
(* ------------------------------------------------------------------------ *)

let FLD_SUC = prove
 (`!(l:A->A->bool) a.
     fld(\ x y. l x y \/ (y = a) /\ (fld(l) x \/ (x = a))) x <=>
     fld(l) x \/ (x = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY DISJ1_TAC THEN
  ASM_MESON_TAC[]);;

let ORDINAL_SUC = prove
 (`!l:A->A->bool. ordinal(l) /\ (?x. ~(fld(l) x)) ==>
                 ordinal(\x y. l x y \/ (y = @y. ~fld(l) y) /\
                                           (fld(l) x \/ (x = @y. ~fld(l) y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `a:A = @y. ~fld(l) y` THEN
  SUBGOAL_THEN `~fld(l:A->A->bool) a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN CONV_TAC SELECT_CONV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PBETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[WOSET; SUBSET; GSYM MEMBER_NOT_EMPTY; IN] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[WOSET_ANTISYM]; ALL_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~fld(l:A->A->bool) a` THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THENL
       [EXISTS_TAC `y:A`; EXISTS_TAC `x:A`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `P:A->bool` THEN REWRITE_TAC[FLD_SUC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `w:A`)) THEN
      IMP_RES_THEN (MP_TAC o SPEC `\x:A. P x /\ fld(l) x`) WOSET_WELL THEN
      BETA_TAC THEN REWRITE_TAC[TAUT `a /\ b ==> b`] THEN
      ASM_CASES_TAC `?x:A. P x /\ fld(l) x` THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[];
        FIRST_ASSUM(MP_TAC o SPEC `w:A` o
          GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        ASM_MESON_TAC[]]];
    X_GEN_TAC `z:A` THEN REWRITE_TAC[FLD_SUC; properly] THEN
    PBETA_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
     [UNDISCH_TAC `!x:A. fld l x ==> (x = (@y. ~properly l y x))` THEN
      DISCH_THEN(IMP_RES_THEN MP_TAC) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `y:A` THEN
      BETA_TAC THEN REWRITE_TAC[properly] THEN AP_TERM_TAC THEN
      ASM_CASES_TAC `y:A = z` THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `fld(l:A->A->bool) z` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `z:A = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [SYM(ASSUME `(@y:A. ~fld(l) y) = a`)] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `y:A` THEN
      BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `y:A = a` THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
      EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------ *)
(* The union of a set of ordinals is an ordinal.                            *)
(* ------------------------------------------------------------------------ *)

let ORDINAL_UNION = prove
 (`!P. (!l:A->A->bool. P l ==> ordinal(l))
       ==> ordinal(\x y. ?l. P l /\ l x y)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ordinal; WOSET; SUBSET; GSYM MEMBER_NOT_EMPTY; IN] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN REWRITE_TAC[UNIONS_PRED] THEN
    BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `l:A->A->bool` (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
        ASSUME_TAC))
     (X_CHOOSE_THEN `m:A->A->bool` (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
        ASSUME_TAC))) THEN
    MP_TAC(SPECL [`l:A->A->bool`; `m:A->A->bool`] ORDINAL_CHAINED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPEC `l:A->A->bool` WOSET_ANTISYM);
      MP_TAC(SPEC `m:A->A->bool` WOSET_ANTISYM)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ordinal]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `Q:A->bool` THEN REWRITE_TAC[UNION_FLD] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `a:A`)) THEN
    MP_TAC(ASSUME `!x:A. Q x ==> (?l. P l /\ fld l x)`) THEN
    DISCH_THEN(IMP_RES_THEN
      (X_CHOOSE_THEN `l:A->A->bool` STRIP_ASSUME_TAC)) THEN
    IMP_RES_THEN ASSUME_TAC (ASSUME `!l:A->A->bool. P l ==> ordinal l`) THEN
    ASSUME_TAC(CONJUNCT1
      (REWRITE_RULE[ordinal] (ASSUME `ordinal(l:A->A->bool)`))) THEN
    IMP_RES_THEN(MP_TAC o SPEC `\x:A. fld(l) x /\ Q x`) WOSET_WELL THEN
    BETA_TAC THEN REWRITE_TAC[TAUT `a /\ b ==> a`] THEN
    SUBGOAL_THEN `?x:A. fld(l) x /\ Q x` (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME `(Q:A->bool) x`) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A->A->bool` STRIP_ASSUME_TAC) THEN
    ANTE_RES_THEN ASSUME_TAC (ASSUME `(P:(A->A->bool)->bool) m`) THEN
    MP_TAC(SPECL [`l:A->A->bool`; `m:A->A->bool`] ORDINAL_CHAINED) THEN
    ASM_REWRITE_TAC[UNIONS_PRED] THEN BETA_TAC THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [EXISTS_TAC `l:A->A->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET_FLD THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `m:A->A->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `b:A`] o REWRITE_RULE[inseg]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      IMP_RES_THEN (MP_TAC o SPEC `b:A`) INSEG_SUBSET_FLD THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(CONJUNCT1(REWRITE_RULE[ordinal]
        (ASSUME `ordinal(m:A->A->bool)`))) THEN
      DISCH_THEN(MP_TAC o SPECL [`b:A`; `x:A`] o MATCH_MP WOSET_TOTAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
      EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[UNION_FLD] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:A->A->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ASSUME `!l:A->A->bool. P l ==> ordinal l`) THEN
    DISCH_THEN(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[ordinal] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    REPEAT AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `y:A` THEN BETA_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[properly; UNIONS_PRED] THEN
    BETA_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC `l:A->A->bool` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(X_CHOOSE_THEN `m:A->A->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ordinal(l:A->A->bool) /\ ordinal(m:A->A->bool)`
      MP_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(DISJ_CASES_TAC o MATCH_MP ORDINAL_CHAINED)] THENL
       [IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------ *)
(* Consequently, every type can be wellordered (and by an ordinal).         *)
(* ------------------------------------------------------------------------ *)

let ORDINAL_UNION_LEMMA = prove
 (`!(l:A->A->bool) x.
      ordinal l ==> fld(l) x ==> fld(\a b. ?l. ordinal l /\ l a b) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_FLD] THEN
  EXISTS_TAC `l:A->A->bool` THEN ASM_REWRITE_TAC[]);;

let ORDINAL_UP = prove
 (`!l:A->A->bool. ordinal(l) ==> (!x. fld(l) x) \/
                          (?m x. ordinal(m) /\ fld(m) x /\ ~fld(l) x)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  GEN_REWRITE_TAC LAND_CONV [NOT_FORALL_THM] THEN DISCH_TAC THEN
  MP_TAC(SPEC `l:A->A->bool` ORDINAL_SUC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`\x y. l x y \/ (y = @y:A. ~fld l y) /\ (fld(l) x \/ (x = @y. ~fld l y))`;
    `@y. ~fld(l:A->A->bool) y`] THEN
  ASM_REWRITE_TAC[FLD_SUC] THEN
  CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]);;

let WO_ORDINAL = prove
 (`?l:A->A->bool. ordinal(l) /\ !x. fld(l) x`,
  EXISTS_TAC `\a b:A. ?l. ordinal l /\ l a b` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORDINAL_UNION THEN REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP ORDINAL_UP) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(X_CHOOSE_THEN `m:A->A->bool`
     (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
    IMP_RES_THEN (IMP_RES_THEN MP_TAC) ORDINAL_UNION_LEMMA THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------ *)
(* At least -- every set can be wellordered.                                *)
(* ------------------------------------------------------------------------ *)

let FLD_RESTRICT = prove
 (`!l. woset l ==>
       !P. fld(\x y:A. P x /\ P y /\ l x y) x <=> P x /\ fld(l) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN EXISTS_TAC `y:A` THEN
  ASM_REWRITE_TAC[]);;

let WO = prove
 (`!P. ?l:A->A->bool. woset l /\ (fld(l) = P)`,
  GEN_TAC THEN X_CHOOSE_THEN `l:A->A->bool` STRIP_ASSUME_TAC
   (REWRITE_RULE[ordinal] WO_ORDINAL) THEN
  EXISTS_TAC `\x y:A. P x /\ P y /\ l x y` THEN
  REWRITE_TAC[WOSET; SUBSET; GSYM MEMBER_NOT_EMPTY; IN] THEN
  GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FLD_RESTRICT th]) THEN
  PBETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `Q:A->bool` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
    DISCH_THEN(MP_TAC o SPEC `Q:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Moreover, the ordinals themselves are wellordered by "inseg".             *)
(* ------------------------------------------------------------------------- *)

let WF_INSEG_WOSET = prove
 (`WF(\(x:A->A->bool) y. woset x /\ woset y /\ x inseg y /\ ~(x = y))`,
  REWRITE_TAC[WF] THEN X_GEN_TAC `P:(A->A->bool)->bool` THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NOT_FORALL_THM] THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:A->A->bool. P x ==> woset x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. ?(a:A) z. P y ==> P z /\ fld y a /\ linseg y a = z`
  MP_TAC THENL
   [X_GEN_TAC `y:A->A->bool` THEN
    ASM_CASES_TAC `(P:(A->A->bool)->bool) y` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:A->A->bool`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INSEG_LINSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`a:(A->A->bool)->A`; `l:(A->A->bool)->(A->A->bool)`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `z:A->A->bool`) THEN
  SUBGOAL_THEN `woset(z:A->A->bool)` MP_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[woset; SUBSET; GSYM MEMBER_NOT_EMPTY; IN]] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `{(a:(A->A->bool)->A) x | P x /\ x inseg z}`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[TAUT `P /\ x = y <=> x = y /\ P`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM; SWAP_FORALL_THM] THEN
  REWRITE_TAC[UNWIND_THM2; FORALL_UNWIND_THM2; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM; SWAP_FORALL_THM] THEN
  REWRITE_TAC[UNWIND_THM2; FORALL_UNWIND_THM2; IMP_CONJ;
              RIGHT_FORALL_IMP_THM; NOT_IMP] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INSEG_SUBSET_FLD]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INSEG_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->A->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `(l:(A->A->bool)->(A->A->bool)) w`) THEN
  ASM_SIMP_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LINSEG_INSEG; INSEG_TRANS]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `(l:(A->A->bool)->(A->A->bool)) w` th) THEN
   MP_TAC(SPEC `w:A->A->bool` th)) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `fld ((l:(A->A->bool)->(A->A->bool)) w) (a (l w))` THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
  ASM_SIMP_TAC[LINSEG_FLD; properly] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_MESON_TAC[]);;

let WOSET_INSEG_ORDINAL = prove
 (`woset (\(x:A->A->bool) y. ordinal x /\ ordinal y /\ x inseg y)`,
  REWRITE_TAC[WOSET_WF; IN; properly; REWRITE_RULE[IN] IN_FLD] THEN
  CONJ_TAC THENL [MESON_TAC[ORDINAL_CHAINED]; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] WF_SUBSET)
        WF_INSEG_WOSET) THEN
  SIMP_TAC[ordinal]);;

let SUBWOSET_ISO_INSEG = prove
 (`!l s. woset l /\ fld l = (:A)
         ==> ?f. (!x y. x IN s /\ y IN s ==> (l(f x) (f y) <=> l x y)) /\
                 (!x y. y IN IMAGE f s /\ l x y ==> x IN IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [woset]) THEN
  ASM_REWRITE_TAC[UNIV; MEMBER_NOT_EMPTY] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:(A->bool)->A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?f:A->A. !x. f(x) = m (UNIV DIFF IMAGE f {u | u IN s /\ properly l u x})`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[WOSET_WF; properly]) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP WF_REC) THEN
    REWRITE_TAC[properly] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `f:A->A` THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN `!x. x IN s ==> (l:A->A->bool)(f x) x` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[WOSET_WF; properly]) THEN
    REWRITE_TAC[WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `(:A) DIFF IMAGE (f:A->A) {u | u IN s /\ properly l u x}`) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[properly; woset] THEN SET_TAC[];
      REWRITE_TAC[IN_DIFF; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[properly; woset] THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MONO_FORALL o GEN `x:A` o SPEC
     `(:A) DIFF IMAGE (f:A->A) {u | u IN s /\ properly l u x}`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[properly; woset] THEN SET_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o CONV_RULE (BINDER_CONV SYM_CONV))] THEN
  REWRITE_TAC[IN_UNIV; IN_IMAGE; IN_DIFF; IN_ELIM_THM; FORALL_AND_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x z:A. x IN s /\ properly l z (f x)
            ==> ?u. u IN s /\ properly l u x /\ f u = z`
  ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[properly; woset] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z:A. x IN s /\ l z (f x) ==> ?u. u IN s /\ l u x /\ f u = z`
  ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[properly; woset] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!x y:A. x IN s /\ y IN s /\ properly l x y ==> properly l (f x) (f y)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `(f:A->A) y`])) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[properly; woset] THEN SET_TAC[];
      MATCH_MP_TAC(MESON[]
       `(!x y. P x y /\ P y x ==> Q x y)
        ==> (!x y. P x y) ==> (!x y. Q x y)`) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[properly; woset] THEN
      SET_TAC[]];
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[properly; woset] THEN
    SET_TAC[]]);;

(* ======================================================================== *)
(* (3) CANTOR-ZERMELO WELL-ORDERING THEOREM ==> HAUSDORFF MAXIMAL PRINCIPLE *)
(* ======================================================================== *)

let HP = prove
 (`!l:A->A->bool. poset l ==>
        ?P. chain(l) P /\ !Q. chain(l) Q  /\ P SUBSET Q ==> (Q = P)`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `w:A->A->bool` MP_TAC (SPEC `\x:A. T` WO) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN BETA_TAC THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  IMP_RES_THEN (MP_TAC o SPEC `\x:A. fld(l) x`) WOSET_WELL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?x:A. fld(l) x` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC);
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    EXISTS_TAC `\x:A. F` THEN REWRITE_TAC[chain; IN; SUBSET_PRED] THEN
    GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` MP_TAC o
      GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`u:A`; `u:A`]) THEN
    IMP_RES_THEN(ASSUME_TAC o GSYM) POSET_FLDEQ THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
    `?f. !x. f x = if fld(l) x /\
                      !y. properly w  y x ==> l x (f y) \/ l (f y) x
                   then (x:A) else b`
  (CHOOSE_TAC o GSYM) THENL
   [SUBGOAL_THEN `WF(\x:A y. (properly w) x y)` MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[WOSET_WF]) THEN ASM_REWRITE_TAC[ETA_AX];
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP WF_REC) THEN
      REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]]; ALL_TAC] THEN
  IMP_RES_THEN(IMP_RES_THEN ASSUME_TAC) POSET_REFL THEN
  SUBGOAL_THEN `(f:A->A) b = b` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `b:A`) THEN
    REWRITE_TAC[COND_ID] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. fld(l:A->A->bool) (f x)` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:A`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ANTE_RES_THEN (ASSUME_TAC o GEN_ALL) o SPEC_ALL) THEN
  SUBGOAL_THEN `!x:A. (l:A->A->bool) b (f x) \/ l (f x) b` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC`x:A` (ASSUME `!x:A. (w:A->A->bool) b (f x)`)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:A`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:A = b` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(properly w) (b:A) x` MP_TAC THENL
     [ASM_REWRITE_TAC[properly] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. l((f:A->A) x) (f y) \/ l(f y) (f x)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    IMP_RES_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) WOSET_TOTAL_LT THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN IMP_RES_THEN MATCH_MP_TAC POSET_REFL;
      ONCE_REWRITE_TAC[DISJ_SYM] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `y:A`);
      FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:A`)] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(IMP_RES_THEN ACCEPT_TAC o CONJUNCT2); ALL_TAC] THEN
  EXISTS_TAC `\y:A. ?x:A. y = f(x)` THEN
  SUBGOAL_THEN `chain(l:A->A->bool)(\y. ?x:A. y = f x)` ASSUME_TAC THENL
   [REWRITE_TAC[chain; IN] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN(CHOOSE_THEN SUBST1_TAC)); ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [DISCH_TAC THEN BETA_TAC THEN EXISTS_TAC `z:A` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `z:A`) THEN
    SUBGOAL_THEN `fld(l:A->A->bool) z /\
                  !y. (properly w) y z ==> l z (f y) \/ l (f y) z`
    (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [UNDISCH_TAC `chain(l:A->A->bool) Q` THEN REWRITE_TAC[chain; IN] THEN
      DISCH_THEN(MP_TAC o SPECL [`z:A`; `z:A`]) THEN
      ASM_REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
      DISCH_TAC THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      UNDISCH_TAC `chain(l:A->A->bool) Q` THEN REWRITE_TAC[chain; IN] THEN
      DISCH_THEN(MP_TAC o SPECL [`z:A`; `(f:A->A) y`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET_PRED]) THEN
      BETA_TAC THEN EXISTS_TAC `y:A` THEN REFL_TAC];
    SPEC_TAC(`z:A`,`z:A`) THEN ASM_REWRITE_TAC[GSYM SUBSET_PRED]]);;

(* ======================================================================== *)
(* (4) HAUSDORFF MAXIMAL PRINCIPLE ==> ZORN'S LEMMA                         *)
(* ======================================================================== *)

let ZL = prove
 (`!l:A->A->bool. poset l /\
           (!P. chain(l) P ==> (?y. fld(l) y /\ !x. P x ==> l x y)) ==>
        ?y. fld(l) y /\ !x. l y x ==> (y = x)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:A->bool` STRIP_ASSUME_TAC o MATCH_MP HP) THEN
  UNDISCH_TAC `!P. chain(l:A->A->bool) P
                   ==> (?y. fld(l) y /\ !x. P x ==> l x y)` THEN
  DISCH_THEN(MP_TAC o SPEC `M:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN
  DISCH_TAC THEN GEN_REWRITE_TAC I [TAUT `a <=> ~ ~a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `chain(l) (\x:A. M x \/ (x = z))` MP_TAC THENL
   [REWRITE_TAC[chain; IN] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
    ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `chain(l:A->A->bool) M` THEN REWRITE_TAC[chain; IN] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_REFL) THEN
      REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN EXISTS_TAC `m:A` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `M SUBSET (\x:A. M x \/ (x = z))` MP_TAC THENL
   [REWRITE_TAC[SUBSET_PRED] THEN GEN_TAC THEN BETA_TAC THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `(a ==> b ==> c) <=> (b /\ a ==> c)`] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `z:A`) THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:A`; `z:A`] o MATCH_MP POSET_ANTISYM) THEN
  ASM_REWRITE_TAC[]);;

(* ======================================================================== *)
(* (5) ZORN'S LEMMA ==> KURATOWSKI'S LEMMA                                  *)
(* ======================================================================== *)

let KL_POSET_LEMMA = prove
 (`poset (\ c1 c2. C SUBSET c1 /\ c1 SUBSET c2 /\ chain(l:A->A->bool) c2)`,
  REWRITE_TAC[poset; IN] THEN PBETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
    DISCH_THEN(X_CHOOSE_THEN `Q:A->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THENL
     [MATCH_MP_TAC CHAIN_SUBSET; MATCH_MP_TAC SUBSET_TRANS];
    GEN_TAC THEN X_GEN_TAC `Q:A->bool` THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM] THEN
  TRY(EXISTS_TAC `Q:A->bool`) THEN ASM_REWRITE_TAC[]);;

let KL = prove
 (`!l:A->A->bool. poset l ==>
        !C. chain(l) C ==>
            ?P. (chain(l) P /\ C SUBSET P) /\
                (!R. chain(l) R /\ P SUBSET R ==> (R = P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\c1 c2. C SUBSET c1 /\ c1 SUBSET c2 /\
                          chain(l:A->A->bool) c2` ZL) THEN PBETA_TAC THEN
  REWRITE_TAC[KL_POSET_LEMMA; MATCH_MP POSET_FLDEQ KL_POSET_LEMMA] THEN
  PBETA_TAC THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [X_GEN_TAC `P:(A->bool)->bool` THEN GEN_REWRITE_TAC LAND_CONV [chain] THEN
    REWRITE_TAC[IN] THEN
    PBETA_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `?D:A->bool. P D` THENL
     [EXISTS_TAC `UNIONS(P) :A->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
      FIRST_ASSUM(X_CHOOSE_TAC `D:A->bool`) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`D:A->bool`; `D:A->bool`]) THEN
      REWRITE_TAC[ASSUME `(P:(A->bool)->bool) D`; SUBSET_REFL] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> (a /\ b) /\ c`) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[UNIONS_PRED; SUBSET_PRED] THEN REPEAT STRIP_TAC THEN
        BETA_TAC THEN EXISTS_TAC `D:A->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET_PRED]) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[chain; IN; UNIONS_PRED] THEN
        MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
        BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
         (X_CHOOSE_TAC `A:A->bool`) (X_CHOOSE_TAC `B:A->bool`)) THEN
        FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
        DISCH_THEN(MP_TAC o SPECL [`A:A->bool`; `B:A->bool`]) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [UNDISCH_TAC `chain(l:A->A->bool) B`;
          UNDISCH_TAC `chain(l:A->A->bool) A`] THEN
        REWRITE_TAC[chain; IN] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET_PRED]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN X_GEN_TAC `X:A->bool` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPECL [`X:A->bool`; `X:A->bool`]) THEN
        REWRITE_TAC[] THEN DISCH_THEN(IMP_RES_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_PRED; SUBSET_PRED] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN EXISTS_TAC `X:A->bool` THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `C:A->bool` THEN
      FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    DISCH_THEN(X_CHOOSE_THEN `D:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:A->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Special case of Zorn's Lemma for restriction of subset lattice.           *)
(* ------------------------------------------------------------------------- *)

let POSET_RESTRICTED_SUBSET = prove
 (`!P. poset(\x y. P(x) /\ P(y) /\ x SUBSET y)`,
  GEN_TAC THEN REWRITE_TAC[poset; IN; REWRITE_RULE[IN] IN_FLD] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SUBSET; EXTENSION] THEN MESON_TAC[]);;

let FLD_RESTRICTED_SUBSET = prove
 (`!P. fld(\ x y. P(x) /\ P(y) /\ x SUBSET y) = P`,
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD; FORALL_PAIR_THM; FUN_EQ_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[SUBSET_REFL]);;

let ZL_SUBSETS = prove
 (`!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> ?z. P z /\ (!x. x IN c ==> x SUBSET z))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\x y. P(x:A->bool) /\ P(y) /\ x SUBSET y` ZL) THEN
  REWRITE_TAC[POSET_RESTRICTED_SUBSET; FLD_RESTRICTED_SUBSET] THEN
  REWRITE_TAC[chain; IN] THEN
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
(* A form of Tukey's lemma.                                                  *)
(* ------------------------------------------------------------------------- *)

let TUKEY = prove
 (`!s:(A->bool)->bool.
        ~(s = {}) /\
        (!t. (!c. FINITE c /\ c SUBSET t ==> c IN s) <=> t IN s)
        ==> ?u. u IN s /\ !v. v IN s /\ u SUBSET v ==> u = v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS_UNIONS_NONEMPTY THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)->bool` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  SUBGOAL_THEN
   `!d. FINITE d ==> d SUBSET UNIONS c ==> ?e:A->bool. e IN c /\ d SUBSET e`
  MP_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_FORALL THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INSERT_SUBSET] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Also the order extension theorem, using Abian's proof.                    *)
(* ------------------------------------------------------------------------- *)

let OEP = prove
 (`!p:A->A->bool.
     poset p ==> ?t. toset t /\ fld(t) = fld(p) /\ !x y. p x y ==> t x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `fld(p:A->A->bool)` WO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `t = \(x:A) (y:A). fld p x /\ fld p y /\
                    (x = y \/
                     ?i. fld p i /\
                         (!j. w j i /\ ~(j = i) ==> (p j x <=> p j y)) /\
                         ~p i x /\ p i y)` THEN
  EXISTS_TAC `t:A->A->bool` THEN
  SUBGOAL_THEN
   `!x:A y:A. fld p x /\ fld p y /\ ~(x = y)
              ==> ?i. fld p i /\
                      (!j:A. w j i /\ ~(j = i) ==> (p j x <=> p j y)) /\
                      ~(p i x <=> p i y)`
  (LABEL_TAC "*") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN ASM_SIMP_TAC[IN] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC `\i:A. fld p i /\ ~(p i x <=> p i y)`) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [poset]) THEN ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:A` THEN
       ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A y:A. p x y ==> t x y` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(CONJ_TAC THENL
     [ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]; ALL_TAC]) THEN
    ASM_CASES_TAC `x:A = y` THENL
     [ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]; MATCH_MP_TAC MONO_EXISTS] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [poset]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
    ASM_MESON_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[TOSET_POSET; poset; IN]] THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [poset]) THEN
  REWRITE_TAC[IN] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN
    ASM_CASES_TAC `x:A = z` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `y:A = z` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `fld p (x:A)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fld p (y:A)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fld p (z:A)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `n:A` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
    REWRITE_TAC[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:A`; `n:A`] o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[REWRITE_RULE[IN] IN_FLD]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `m:A`; EXISTS_TAC `n:A`] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fld p (x:A)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fld p (y:A)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `n:A` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
    REWRITE_TAC[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:A`; `n:A`] o CONJUNCT1) THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[IN] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Every toset contains a cofinal woset.                                     *)
(* ------------------------------------------------------------------------- *)

let TOSET_COFINAL_WOSET = prove
 (`!l. toset l
       ==> ?w. (!x y. w x y ==> l x y) /\ woset w /\
               !x:A. x IN fld l ==> ?y. y IN fld w /\ l x y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `fld l:A->bool = {}` THENL
   [EXISTS_TAC `(\x y. F):A->A->bool` THEN
    ASM_REWRITE_TAC[woset; FLD_TRIVIAL; NOT_IN_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. ordinal r /\ fld r = (:A->bool)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV] THEN REWRITE_TAC[IN; WO_ORDINAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?f. !w. f w = if ?x:A. x IN fld l /\
                           !v:A->bool. r v w /\ ~(v = w) ==> ~l x (f v)
                  then @x:A. x IN fld l /\
                             !v. r v w /\ ~(v = w) ==> ~l x (f v)
                  else @x:A. x IN fld l`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP ORDINAL_IMP_WOSET) THEN
    REWRITE_TAC[WOSET_WF; properly] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP WF_REC o CONJUNCT2) THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[]
     `(p <=> p') /\ x' = x
      ==> (if p then x else a) = (if p' then x' else a)`) THEN
    CONJ_TAC THENL [ALL_TAC; AP_TERM_TAC THEN ABS_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. (f:(A->bool)->A) w IN fld l`
  ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w:A->bool. (!x. x IN fld l ==> ?v. r v w /\ ~(v = w) /\ l (x:A) (f v)) /\
                !z. (!x. x IN fld l ==> ?v. r v z /\ ~(v = z) /\ l x (f v))
                    ==> r w z`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o
        REWRITE_RULE[REWRITE_RULE[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] woset] o
        MATCH_MP ORDINAL_IMP_WOSET) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MESON[] `(?w. P w) <=> ~(!w. ~P w)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NOT_FORALL_THM] THEN
    REWRITE_TAC[NOT_IMP; NOT_EXISTS_THM; TAUT
     `~(p /\ q /\ r) <=> (p /\ q ==> ~r)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!v w:A->bool. f v:A = f w ==> v = w` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS o
        REWRITE_RULE[REWRITE_RULE[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] woset] o
        MATCH_MP ORDINAL_IMP_WOSET) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[UNIV] THEN
      MATCH_MP_TAC(MESON[]
       `(!x y. P x y ==> P y x) /\ (!x y. R x y ==> P x y)
        ==> (!x y. R x y \/ R y x) ==> (!x y. P x y)`) THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun t -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [t]) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
       `(y = @x. P x) ==> (?x. P x) ==> P y`)) THEN
      ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[TOSET_POSET]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[INJECTIVE_LEFT_INVERSE; NOT_EXISTS_THM] THEN
      X_GEN_TAC `g:A->(A->bool)` THEN
      DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN
      REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. r x y /\ r y w /\ ~(y = w) ==> l((f:(A->bool)->A) x) (f y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[]
     `(l a b \/ l b a) /\ (~(b = a) ==> ~l b a) ==> l a b`) THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[TOSET_POSET]) THEN ASM SET_TAC[];
      DISCH_THEN(ASSUME_TAC o MATCH_MP (MESON[]
       `~(f x = f y) ==> ~(x = y)`))] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o SELECT_RULE) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o
        REWRITE_RULE[REWRITE_RULE[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] woset] o
        MATCH_MP ORDINAL_IMP_WOSET) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\x y. x IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
                    y IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
                    l x y` THEN
  SUBGOAL_THEN
   `fld(\ x y. x IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
               y IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
               l x y) =
    IMAGE f {v | r v w /\ ~(v = w)}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    REWRITE_TAC[IN; REWRITE_RULE[IN] IN_FLD] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOSET_POSET]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN];
    ASM_REWRITE_TAC[REWRITE_RULE[SET_RULE `fld l x <=> x IN fld l`]
      (REWRITE_RULE[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] woset)];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    ASM SET_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [TOSET_POSET]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [poset]) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]] THEN
  X_GEN_TAC `P:A->bool` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORDINAL_IMP_WOSET) THEN
  REWRITE_TAC[REWRITE_RULE[SUBSET; GSYM MEMBER_NOT_EMPTY; IN] woset] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\x:A->bool. (P:A->bool) (f x)` o last o CONJUNCTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:(A->bool)->A) z` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `(!z. P z ==> z IN IMAGE f s)
    ==> (!x. x IN s /\ P(f x) ==> Q(f x))
        ==> !y. P y ==> Q y`)) THEN
  X_GEN_TAC `y:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ASM SET_TAC[]]);;
