

(* ------------------------------------------------------------------ *)
(*
   Topological Spaces, Metric Spaces,
   Connectedness, Totally bounded spaces, compactness,
   Hausdorff property, completeness, properties of Euclidean space,

   Author: Thomas Hales 2004

*)

(* ------------------------------------------------------------------ *)


(* prioritize_real (or num) *)

(* ------------------------------------------------------------------ *)
(* Logical Preliminaries *)
(* ------------------------------------------------------------------ *)


let Q_ELIM_THM = prove_by_refinement(
  `!P Q R . (?(u:B). (?(x:A). (u = P x) /\ (Q x)) /\ (R u)) <=>
    (?x. (Q x) /\ R( P x))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MESON_TAC[];
  ]);;
  (* }}} *)

let Q_ELIM_THM' = prove_by_refinement(
  `!P Q R. (!(t:B). (?(x:A). P x /\ (t = Q x)) ==> R t) <=>
    (!x. P x ==> R (Q x))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MESON_TAC[];
  ]);;
  (* }}} *)

let Q_ELIM_THM'' = prove_by_refinement(
  `!P Q R. (!(t:B). (?(x:A).  (t = Q x) /\ P x ) ==> R t) <=>
    (!x. P x ==> R (Q x))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MESON_TAC[];
  ]);;
  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Set Preliminaries *)
(* ------------------------------------------------------------------ *)

let DIFF_SUBSET = prove_by_refinement(
  `!X A (B:A->bool). A SUBSET (X DIFF B) <=>
         (A SUBSET X) /\ (A INTER B = EMPTY)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[SUBSET;DIFF;INTER;IN];
  EQ_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  DISCH_TAC;
  CONJ_TAC;
  ASM_MESON_TAC[];
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM';EMPTY];
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  GEN_TAC;
  DISCH_ALL_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  CONJ_TAC;
  ASM_MESON_TAC[];
  USE 1 (fun t-> AP_THM t `x:A`);
  USE 1 (REWRITE_RULE[IN_ELIM_THM';EMPTY]);
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let SUBSET_INTERS = prove_by_refinement(
  `!X (A:A->bool). A SUBSET (INTERS X) <=> (!x. X x ==> (A SUBSET x))`,
  (* {{{ proof *)
  [
  REP_GEN_TAC;
  REWRITE_TAC[SUBSET;INTERS];
  REWRITE_TAC [IN_ELIM_THM'];
  MESON_TAC[IN];
  ]);;
  (* }}} *)

let EQ_EMPTY = prove_by_refinement(
  `!P. ({(x:A) | P x} = {}) <=> (!x. ~P x)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_TAC;
  (USE 0 (fun t-> AP_THM t `x:A`));
  USE 0 (REWRITE_RULE[IN_ELIM_THM';EMPTY]);
  USE 0 (GEN_ALL);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM';EMPTY];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let DIFF_INTER = prove_by_refinement(
  `!A B (C:A->bool). ((A DIFF B) INTER C = EMPTY) <=>
         ((A INTER C) SUBSET B)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[DIFF;INTER;SUBSET;IN_ELIM_THM'];
  REWRITE_TAC[IN;EQ_EMPTY];
  MESON_TAC[];
  ]);;
  (* }}} *)

let SUB_IMP_INTER = prove_by_refinement(
  `!A B (C:A->bool). ((A SUBSET B) ==> (A INTER C) SUBSET B) /\
        ((A SUBSET B) ==> (C INTER A) SUBSET B)`,
  (* {{{ proof *)
  [
    DISCH_ALL_TAC;
    SUBCONJ_TAC;
    REWRITE_TAC[INTER;SUBSET;IN;IN_ELIM_THM'];
    MESON_TAC[];
    MESON_TAC[INTER_COMM];
  ]);;
  (* }}} *)

let SUBSET_UNIONS_INSERT = prove_by_refinement(
  `!(A:A->bool) B C. A SUBSET (UNIONS (B INSERT C)) <=>
           (A DIFF B) SUBSET (UNIONS C)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  SET_TAC[UNIONS;SUBSET;INSERT];
  ]);;
  (* }}} *)

let UNIONS_DELETE2 = prove_by_refinement(
  `!(A:A->bool) B C. (A SUBSET (UNIONS B)) /\ (A INTER C = EMPTY) ==>
                (A SUBSET (UNIONS (B DELETE (C))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ASM SET_TAC[SUBSET;UNIONS;INTER;EMPTY;DELETE];
  ]);;
  (* }}} *)


(* this generalizes to arbitrary cardinalities *)
let finite_subset = prove_by_refinement(
  `!A (f:A->B) B. (B SUBSET (IMAGE f A)) /\ (FINITE B) ==>
     (?C. (C SUBSET A) /\ (FINITE C) /\ (B = IMAGE f C))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  USE 0 (REWRITE_RULE[SUBSET;IN_IMAGE]);
  USE 0 (CONV_RULE NAME_CONFLICT_CONV);
  USE 0 (CONV_RULE (quant_left_CONV "x'"));
  USE 0 (CONV_RULE (quant_left_CONV "x'"));
  CHO 0;
  TYPE_THEN `IMAGE x' B` EXISTS_TAC ;
  SUBCONJ_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE];
  NAME_CONFLICT_TAC;
  GEN_TAC;
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  CONJ_TAC;
  ASM_MESON_TAC[ FINITE_IMAGE];
  MATCH_MP_TAC  SUBSET_ANTISYM;
  CONJ_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE];
  GEN_TAC;
  TYPE_THEN `x` (USE 0 o SPEC);
  ASM_MESON_TAC[];
  REWRITE_TAC[SUBSET;IN_IMAGE];
  NAME_CONFLICT_TAC;
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  ASM_REWRITE_TAC[];
  AND 3;
  CHO 3;
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let inters_singleton = prove_by_refinement(
  `!(A:A->bool). INTERS {A} = A`,
  (* {{{ proof *)
  [
  REWRITE_TAC[INSERT;INTERS];
  REWRITE_TAC[IN_ELIM_THM';NOT_IN_EMPTY];
  GEN_TAC;
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[IN];
  ]);;
  (* }}} *)

let delete_empty = prove_by_refinement(
  `!(A:A->bool) x. (A DELETE x = EMPTY) <=> (~(A = EMPTY) ==> (A = {x}))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[DELETE];
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_ALL_TAC;
  USE 1 (fun t-> AP_THM t `u:A`);
  USE 1 (REWRITE_RULE[IN_ELIM_THM';EMPTY]);
  REWRITE_TAC[EMPTY;INSERT;IN];
  USE 0 (REWRITE_RULE[EMPTY_EXISTS]);
  USE 1 (GEN `u:A`);
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[IN];
  DISCH_ALL_TAC;
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM';EMPTY];
  USE 0 (REWRITE_RULE[EMPTY_EXISTS]);
  USE 0 (REWRITE_RULE[EMPTY;INSERT;IN]);
  REWRITE_TAC[IN];
  USE 0 (CONV_RULE (quant_left_CONV "u"));
  USE 0 (SPEC `x':A`);
  MATCH_MP_TAC  (TAUT `(a ==> b) ==> ~(a /\ ~b)`);
  DISCH_ALL_TAC;
  REWR 0;
  UND  1;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[IN_ELIM_THM'];
  ]);;

  (* }}} *)

let inters_subset = prove_by_refinement(
  `!A (B:(A->bool)->bool). A SUBSET B ==> INTERS B SUBSET INTERS A`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[INTERS;SUBSET;IN_ELIM_THM'];
  ASM_MESON_TAC[SUBSET;IN];
  ]);;
  (* }}} *)

let delete_inters = prove_by_refinement(
  `!V (u:A->bool). V u ==> (INTERS V = (INTERS (V DELETE u)) INTER u)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MATCH_MP_TAC SUBSET_ANTISYM;
  CONJ_TAC;
  REWRITE_TAC[SUBSET_INTER];
  CONJ_TAC;
  MATCH_MP_TAC  inters_subset;
  REWRITE_TAC [DELETE_SUBSET];
  USE 0 (ONCE_REWRITE_RULE[GSYM IN]);
  USE 0 (MATCH_MP INTERS_SUBSET);
  ASM_REWRITE_TAC[];
  TYPE_THEN `INTERS (V DELETE u) INTER u SUBSET u` SUBGOAL_TAC;
  REWRITE_TAC[INTER_SUBSET];
  REWRITE_TAC[SUBSET_INTERS];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `x = u` ASM_CASES_TAC;
  ASM_MESON_TAC[];
  TYPE_THEN `INTERS (V DELETE u) INTER u SUBSET INTERS (V DELETE u) ` SUBGOAL_TAC;
  REWRITE_TAC[INTER_SUBSET];
  TYPE_THEN `INTERS (V DELETE u) SUBSET x` SUBGOAL_TAC;
  MATCH_MP_TAC  INTERS_SUBSET;
  ASM_REWRITE_TAC [IN;DELETE;IN_ELIM_THM'];
  ASM_MESON_TAC[SUBSET_TRANS];
  ]);;
  (* }}} *)

let EQ_EMPTY = prove_by_refinement(
  `!(A:A->bool) . (A = EMPTY) <=> (!x. ~(A x))`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[EMPTY_EXISTS;IN];
  ]);;
  (* }}} *)

let UNIONS_EQ_EMPTY = prove_by_refinement(
  `!(U:(A->bool)->bool). (UNIONS U = {}) <=>
     ((U = EMPTY) \/ (U = {EMPTY}))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[EQ_EMPTY;UNIONS;IN_ELIM_THM';INSERT;EMPTY];
  REWRITE_TAC [IN];
  EQ_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `!x. ~U x` ASM_CASES_TAC ;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  USE 1 (CONV_RULE (quant_left_CONV "x"));
  CHO 1;
  USE 0 (CONV_RULE (quant_left_CONV "u"));
  USE 0 (CONV_RULE (quant_left_CONV "u"));
  EQ_TAC;
  DISCH_TAC;
  TYPE_THEN `x` (USE 0 o SPEC);
  ASM_MESON_TAC[];
  DISCH_TAC;
  COPY 0;
  TYPE_THEN `x` (USE 0 o SPEC);
  TYPE_THEN `x'` (USE 3 o SPEC);
  PROOF_BY_CONTR_TAC;
  TYPE_THEN `x' = {}` SUBGOAL_TAC;
  PROOF_BY_CONTR_TAC;
  USE 5 (REWRITE_RULE[EMPTY_EXISTS]);
  CHO 5;
  USE 5 (REWRITE_RULE[IN]);
  ASM_MESON_TAC[];
  USE 2 (CONV_RULE (quant_right_CONV "x'"));
  ASM_MESON_TAC[IN;EMPTY_EXISTS];
  DISCH_THEN DISJ_CASES_TAC;
  ASM_MESON_TAC[];
  ASM_REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let INTERS_EQ_EMPTY = prove_by_refinement(
  `!((A:(A->bool)->bool)). ((INTERS A) = EMPTY) <=>
    (!x . ?a.  (A a) /\ ~(a x))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[INTERS;EQ_EMPTY;IN_ELIM_THM'];
  REWRITE_TAC[IN];
  MESON_TAC[];
   ]);;
  (* }}} *)

let CARD_SING_CONV = prove_by_refinement(
  `!X:A->bool. (X HAS_SIZE 1) ==> (SING X)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[HAS_SIZE ;SING ];
  DISCH_ALL_TAC;
  TYPE_THEN `CHOICE X` EXISTS_TAC;
  TYPE_THEN `~(X = {})` SUBGOAL_TAC;
  ASM_MESON_TAC[CARD_CLAUSES;ARITH_RULE`~(0=1)`];
  DISCH_ALL_TAC;
  TYPE_THEN `SUC (CARD (X DELETE (CHOICE X)))=1` SUBGOAL_TAC ;
  ASM_SIMP_TAC[CARD_DELETE_CHOICE];
  REWRITE_TAC[ARITH_RULE`(SUC a = 1) <=> (a=0)`];
  ASSUME_TAC HAS_SIZE_0;
  USE 3 (REWRITE_RULE [HAS_SIZE ]);
  ASSUME_TAC FINITE_DELETE_IMP;
  ASM_MESON_TAC[delete_empty];
  ]);;

  (* }}} *)

let countable_prod = prove_by_refinement(
  `!(A:A->bool) (B:B->bool). (COUNTABLE A) /\ (COUNTABLE B) ==>
   (COUNTABLE {(a,b) | (A a) /\ (B b) })`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  (INST_TYPE [`:num#num`,`:A`] COUNTABLE_IMAGE);
  USE 0 (REWRITE_RULE [COUNTABLE;GE_C;IN_UNIV]);
  USE 1 (REWRITE_RULE [COUNTABLE;GE_C;IN_UNIV]);
  CHO 0;
  CHO 1;
  TYPE_THEN `{(m:num,n:num) | T}` EXISTS_TAC;
  REWRITE_TAC[NUM2_COUNTABLE;SUBSET;IN_IMAGE];
  REWRITE_TAC[IN_ELIM_THM];
  TYPE_THEN `(\ (u,v) . (f u,f' v))` EXISTS_TAC;
  DISCH_ALL_TAC;
  CHO 2;
  CHO 2;
  AND 2;
  TYPE_THEN `a` (USE 0 o SPEC);
  TYPE_THEN `b` (USE 1 o SPEC);
  IN_OUT_TAC;
  REWR 2;
  REWR 3;
  CHO 3;
  CHO 2;
  TYPE_THEN `(x',x'')` EXISTS_TAC;
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let IMAGE_I = prove_by_refinement(
  `!(A:A->bool). IMAGE I A = A`,
  (* {{{ proof *)
  [
  REWRITE_TAC[IMAGE;IN;I_DEF];
  GEN_TAC;
  MATCH_MP_TAC EQ_EXT THEN GEN_TAC ;
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let EMPTY_NOT_EXISTS = prove_by_refinement(
  `!X. (X = {}) <=> (~(?(u:A). X u))`,
  (* {{{ proof *)
  [
  MESON_TAC [IN;EMPTY_EXISTS];
  ]);;
  (* }}} *)

let DIFF_SURJ = prove_by_refinement(
  `!(f : A->B) X Y. (BIJ f X Y) ==>
  (! t. (t SUBSET X) ==> ((IMAGE f (X DIFF t)) = (Y DIFF (IMAGE f t))))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[BIJ;INJ;SURJ;IN  ];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  REWRITE_TAC[IMAGE;IN];
  IMATCH_MP_TAC  EQ_EXT ;
  REWRITE_TAC[IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  X_GEN_TAC `y:B`;
  REWRITE_TAC[REWRITE_RULE[IN] IN_DIFF];
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[SUBSET;IN ];
  ]);;

  (* }}} *)

let union_subset = prove_by_refinement(
  `!Z1 Z2 A. ((Z1 UNION Z2) SUBSET (A:A->bool)) <=>
     (Z1 SUBSET A) /\ (Z2 SUBSET A)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[UNION;SUBSET;IN;IN_ELIM_THM'];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let preimage_disjoint = prove_by_refinement(
  `!(f:A->B) A B X. (A INTER B = EMPTY) ==>
    (preimage X f A INTER (preimage X f B) = EMPTY )`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[preimage];
  REWRITE_TAC[EQ_EMPTY];
  DISCH_ALL_TAC;
  USE 1( REWRITE_RULE[INTER;IN;IN_ELIM_THM']);
  USE 0 (REWRITE_RULE[EQ_EMPTY;INTER;IN;IN_ELIM_THM']);
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let preimage_union = prove_by_refinement(
  `!(f:A->B) A B X Z.
       (Z SUBSET ((preimage X f A) UNION (preimage X f B))) <=>
     (Z SUBSET X) /\ (IMAGE f Z SUBSET (A UNION B))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[preimage;IMAGE;UNION;SUBSET;IN;IN_ELIM_THM' ];
  MESON_TAC[];
  ]);;
  (* }}} *)

let subset_preimage = prove_by_refinement(
  `!(f:A->B) A X Z. (Z SUBSET (preimage X f A)) <=> (Z SUBSET X) /\
        (IMAGE f Z SUBSET A)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[SUBSET;preimage;IMAGE;IN;IN_ELIM_THM'];
  MESON_TAC[];
  ]);;
  (* }}} *)

let preimage_unions = prove_by_refinement(
  `!dom (f:A->B) C. preimage dom f (UNIONS C) =
     (UNIONS (IMAGE (preimage dom f) C))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[preimage;IN_UNIONS ];
  REWRITE_TAC[UNIONS;IN_IMAGE ];
  REWRITE_TAC[preimage;IN];
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  EQ_EXT ;
  DISCH_ALL_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  REWRITE_TAC[Q_ELIM_THM;IN_ELIM_THM' ];
  MESON_TAC[];
  ]);;
  (* }}} *)

let preimage_subset = prove_by_refinement(
  `!(f:A->B) X  A B. (A SUBSET B) ==>
   (preimage X f A SUBSET (preimage X f B))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[SUBSET;in_preimage];
  REWRITE_TAC[IN];
  MESON_TAC[];
  ]);;
  (* }}} *)

(* to fix two varying descriptions of ((INTER) Y): *)
let INTER_THM = prove_by_refinement(
  `!(X:A->bool). ((\B. B INTER X) = ((INTER) X)) /\
    ((\B. X INTER B) = ((INTER) X))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[INTER_COMM];
  GEN_TAC;
  MATCH_MP_TAC EQ_EXT THEN BETA_TAC;
  REWRITE_TAC[INTER_COMM];
]);;
 (* }}} *)


(* ------------------------------------------------------------------ *)
(* Real Preliminaries *)
(* ------------------------------------------------------------------ *)

let REAL_SUM_SQUARE_POS = prove_by_refinement(
  `!m n x . &.0 <=. sum(m,n) (\i. (x i)*.(x i))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MATCH_MP_TAC SUM_POS_GEN;
  DISCH_ALL_TAC;
  BETA_TAC;
  REWRITE_TAC[REAL_LE_SQUARE];
  ]);;
  (* }}} *)

(* twopow , DUPLICATE OF TWOPOW_MK_POS *)
let twopow_pos = prove_by_refinement(
  `!n. (&.0 <. twopow(n))`,
  (* {{{ proof *)
  [
  GEN_TAC;
  DISJ_CASES_TAC (SPEC `n:int` INT_IMAGE);
  CHO 0;
  ASM_REWRITE_TAC[TWOPOW_POS];
  REDUCE_TAC;
  ARITH_TAC;
  CHO 0;
  ASM_REWRITE_TAC[TWOPOW_NEG];
  REDUCE_TAC;
  ARITH_TAC;
  ]);;
  (* }}} *)

let twopow_double = prove_by_refinement(
  `!n. &.2 * (twopow (--: (&: (n+1)))) = twopow (--: (&:n))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[TWOPOW_NEG;REAL_POW_ADD;POW_1;REAL_INV_MUL    ];
  REWRITE_TAC [REAL_ARITH `a*b*cc = (a*cc)*b`];
  REWRITE_TAC [REAL_RINV_2 ];
  REAL_ARITH_TAC ;
  ]);;
  (* }}} *)


let min_finite = prove_by_refinement(
  `!X.  (FINITE X) /\ (~(X = EMPTY )) ==>
     (?delta. (X delta) /\ (!x. (X x) ==> (delta <=. x)))`,
  (* {{{ proof *)

  [
  TYPE_THEN `(!X k. FINITE X /\ (~(X = EMPTY )) /\ (X HAS_SIZE k) ==> (?delta. X delta /\ (!x. X x ==> delta <= x))) ==>(!X. FINITE X /\ (~(X = EMPTY )) ==> (?delta. X delta /\ (!x. X x ==> delta <= x)))` SUBGOAL_TAC ;
  DISCH_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `X` (USE 0 o SPEC);
  TYPE_THEN `CARD X` (USE 0 o SPEC);
  UND 0;
  DISCH_THEN IMATCH_MP_TAC ;
  ASM_REWRITE_TAC[HAS_SIZE ];
  DISCH_THEN IMATCH_MP_TAC ;
  CONV_TAC (quant_left_CONV "k");
  INDUCT_TAC;
  REWRITE_TAC[HAS_SIZE_0];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[EMPTY];
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  USE 3(REWRITE_RULE[HAS_SIZE]);
  TYPE_THEN `X DELETE (CHOICE X)` (USE 0 o SPEC);
  ASM_CASES_TAC `k=0`;
  REWR 3;
  USE 3 (REWRITE_RULE [ARITH_RULE `SUC 0=1`]);
  TYPE_THEN `SING X` SUBGOAL_TAC ;
  IMATCH_MP_TAC  CARD_SING_CONV;
  ASM_MESON_TAC [HAS_SIZE];
  REWRITE_TAC[SING];
  DISCH_TAC ;
  CHO 5;
  TYPE_THEN `x` EXISTS_TAC ;
  ASM_REWRITE_TAC[REWRITE_RULE[IN] IN_SING ];
  REAL_ARITH_TAC;
  TYPE_THEN `FINITE (X DELETE CHOICE X) /\ ~(X DELETE CHOICE X = {}) /\ (X DELETE CHOICE X HAS_SIZE k ) ` SUBGOAL_TAC;
  REWRITE_TAC[FINITE_DELETE;HAS_SIZE ];
  ASM_REWRITE_TAC[];
  REWR 3;
  IMATCH_MP_TAC  (TAUT `(a /\ b) ==> (b /\ a)`);
  SUBCONJ_TAC;
  IMATCH_MP_TAC  (ARITH_RULE `(SUC x = SUC y) ==> (x = y)`);
  COPY 3;
  UND 3;
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  IMATCH_MP_TAC  CARD_DELETE_CHOICE;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC  (TAUT `(b ==> ~a ) ==> (a ==> ~b)`);
  DISCH_THEN (fun t-> ASM_REWRITE_TAC[t;CARD_CLAUSES]);
  DISCH_TAC;
  REWR 0;
  CHO 0;
  ALL_TAC; (* "ccx" *)
  TYPE_THEN `if (delta < (CHOICE X)) then delta else (CHOICE X)` EXISTS_TAC;
  (* REWRITE_TAC[min_real]; *)
  COND_CASES_TAC ;
  CONJ_TAC;
  UND 0;
  REWRITE_TAC[DELETE;IN ;IN_ELIM_THM' ];
  MESON_TAC[];
  GEN_TAC;
  UND 0;
  REWRITE_TAC[DELETE;IN ;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  TYPE_THEN  `x = CHOICE X` ASM_CASES_TAC ;
  ASM_REWRITE_TAC[];
  UND 6;
  REAL_ARITH_TAC;
  ASM_MESON_TAC[];
  SUBCONJ_TAC;
  IMATCH_MP_TAC  (REWRITE_RULE[IN ] CHOICE_DEF);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `x = CHOICE X` ASM_CASES_TAC ;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  UND 0;
    REWRITE_TAC[DELETE;IN ;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  TYPE_THEN `x` (USE 11 o SPEC);
  REWR 11;
  UND 11;
  UND 6;
  REAL_ARITH_TAC;
  ]);;

  (* }}} *)

let min_finite_delta = prove_by_refinement(
  `!c X.  (FINITE X) /\ ( !x. (X x) ==> (c <. x) ) ==>
     (?delta. (c <. delta) /\ (!x. (X x) ==> (delta <=. x)))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  TYPE_THEN `~(X = EMPTY)` ASM_CASES_TAC;
  JOIN 0 2;
  USE 0 (MATCH_MP min_finite);
  CHO 0;
  TYPE_THEN `delta` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  REWR 2;
  ASM_REWRITE_TAC[EMPTY];
  TYPE_THEN `c +. (&.1)` EXISTS_TAC;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let union_closed_interval = prove_by_refinement(
  `!a b c. (a <=. b) /\ (b <=. c) ==>
    ({x | a <= x /\ x < b} UNION {x | b <= x /\ x <= c} =
     { x | a <= x /\ x <= c})`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[UNION;IN;IN_ELIM_THM'];
  IMATCH_MP_TAC  EQ_EXT ;
  REWRITE_TAC[IN_ELIM_THM'];
  UND 0;
  UND 1;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let real_half_LT = prove_by_refinement(
  `!x y z. ((x < z/(&.2)) /\ (y < z/(&.2)) ==> (x + y < z))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  (GEN_REWRITE_TAC RAND_CONV) [GSYM REAL_HALF_DOUBLE];
  UND 0;
  UND 1;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let real_half_LE = prove_by_refinement(
  `!x y z. ((x < z/(&.2)) /\ (y <= z/(&.2)) ==> (x + y < z))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  (GEN_REWRITE_TAC RAND_CONV) [GSYM REAL_HALF_DOUBLE];
  UND 0;
  UND 1;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let real_half_EL = prove_by_refinement(
  `!x y z. ((x <= z/(&.2)) /\ (y < z/(&.2)) ==> (x + y < z))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  (GEN_REWRITE_TAC RAND_CONV) [GSYM REAL_HALF_DOUBLE];
  UND 0;
  UND 1;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let real_half_LLE = prove_by_refinement(
  `!x y z. ((x <= z/(&.2)) /\ (y <= z/(&.2)) ==> (x + y <= z))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  (GEN_REWRITE_TAC RAND_CONV) [GSYM REAL_HALF_DOUBLE];
  UND 0;
  UND 1;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let interval_finite = prove_by_refinement(
  `!N. FINITE {x | ?j. (abs x = &.j) /\ (j <=| N)}`,
  (* {{{ proof *)
  [
  GEN_TAC;
  ABBREV_TAC `inter = {n | n <=| N}`;
  SUBGOAL_TAC `FINITE {y | ?x. (x IN inter /\ (y = (&. x)))}`;
  MATCH_MP_TAC FINITE_IMAGE_EXPAND;
  EXPAND_TAC "inter";
  REWRITE_TAC[FINITE_NUMSEG_LE];
  SUBGOAL_TAC `FINITE {y | ?x. (x IN inter /\ (y = --.(&. x)))}`;
  MATCH_MP_TAC FINITE_IMAGE_EXPAND;
  EXPAND_TAC "inter";
  REWRITE_TAC[FINITE_NUMSEG_LE];
  DISCH_ALL_TAC;
  JOIN 1 2;
  USE 1 (REWRITE_RULE[GSYM FINITE_UNION]);
  UND 1;
  SUBGOAL_TAC `!a b. ((a:real->bool) = b) ==> (FINITE a ==> FINITE b)`;
  REP_GEN_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  DISCH_THEN (fun t-> MATCH_MP_TAC t);
  MATCH_MP_TAC EQ_EXT;
  X_GEN_TAC `c:real`;
  REWRITE_TAC[IN_ELIM_THM';UNION];
  EXPAND_TAC "inter";
  REWRITE_TAC[IN_ELIM_THM'];
  REWRITE_TAC[real_abs];
  EQ_TAC;
  MATCH_MP_TAC (TAUT `(a==>b) /\ (c==>b) ==> (a \/ c ==> b)`);
  CONJ_TAC;
  DISCH_THEN CHOOSE_TAC;
  AND 1;
  ASM_REWRITE_TAC[];
  EXISTS_TAC `x:num`;
  ASM_REWRITE_TAC [REAL_LE;LE_0];
  DISCH_THEN CHOOSE_TAC;
  AND 1;
  EXISTS_TAC `x:num`;
  ASM_REWRITE_TAC[REAL_NEG_NEG];
  COND_CASES_TAC;
  UND 3;
  REDUCE_TAC;
  ARITH_TAC;
  REDUCE_TAC;
  DISCH_THEN CHOOSE_TAC;
  AND 1;
  UND 2;
  COND_CASES_TAC;
  ASM_MESON_TAC[];
  DISCH_TAC;
  DISJ2_TAC;
  EXISTS_TAC `j:num`;
  ASM_REWRITE_TAC[];
  UND 3;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Euclidean Space *)
(* ------------------------------------------------------------------ *)

let euclid_add_closure = prove_by_refinement(
  `!f g n. (euclid n f) /\ (euclid n g) ==> (euclid n (f + g))`,
(* {{{ *)
  [
  REWRITE_TAC[euclid;euclid_plus];
  ASM_MESON_TAC[REAL_ARITH `&0 +. (&.0) = (&.0)`];
  ]);;
(* }}} *)

let euclid_scale_closure = prove_by_refinement(
  `!n t f. (euclid n f) ==> (euclid n ((t:real) *# f))`,
(* {{{ *)
  [
  REWRITE_TAC[euclid;euclid_scale];
  MESON_TAC[REAL_ARITH `t *.(&.0) = (&.0)`];
  ]);;
(* }}} *)

let euclid_neg_closure = prove_by_refinement(
  `!f n. (euclid n f) ==> (euclid n (-- f))`,
(* {{{ *)

  [
  REWRITE_TAC[euclid;euclid_neg];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[REAL_ARITH `(--x = &.0) <=> (x = &.0)`];
  ]);;

(* }}} *)

let euclid_sub_closure = prove_by_refinement(
  `!f g n. (euclid n f ) /\ (euclid n g) ==> (euclid n (f - g))`,
(* {{{ *)

  [
  REWRITE_TAC[euclid;euclid_minus];
  ASM_MESON_TAC[REAL_ARITH `&.0 -. (&.0) = (&.0)`];
  ]);;

(* }}} *)

let neg_dim = prove_by_refinement(
  `!f n. (euclid n f) = (euclid n (--f))`,
(* {{{ *)

  [
  REPEAT GEN_TAC;
  EQ_TAC;
  REWRITE_TAC[euclid_neg_closure];
  REWRITE_TAC[euclid;euclid_neg];
  DISCH_ALL_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `(x = &.0) <=> (--x = &.0)`];
  ASM_REWRITE_TAC[];
  ]);;

(* }}} *)

let euclid_updim = prove_by_refinement (
 `!f m n. (m <=| n) /\ (euclid m f) ==> (euclid n f)`,
(* {{{ *)
 [
 REWRITE_TAC[euclid];
 MESON_TAC[LE_TRANS];
 ]);;
(* }}} *)

let euclidean_add_closure = prove_by_refinement(
 `!f g. (euclidean f) /\ (euclidean g) ==> (euclidean (f+g))`,
(* {{{ *)

  [
  REWRITE_TAC[euclidean];
  DISCH_ALL_TAC;
  UNDISCH_FIND_THEN `euclid` CHOOSE_TAC;
  UNDISCH_FIND_THEN `(?)` CHOOSE_TAC;
  EXISTS_TAC `n+|n'`;
  ASSUME_TAC (ARITH_RULE `n <=| n+n'`);
  ASSUME_TAC (ARITH_RULE `n' <=| n+n'`);
  ASM_MESON_TAC[euclid_add_closure;euclid_updim];
  ]);;

(* }}} *)

let euclidean_sub_closure = prove_by_refinement(
  `!f g. (euclidean f) /\ (euclidean g) ==> (euclidean (f-g))`,
(* {{{ *)

  [
  REWRITE_TAC[euclidean];
  DISCH_ALL_TAC;
  UNDISCH_FIND_THEN `euclid` CHOOSE_TAC;
  UNDISCH_FIND_THEN `(?)` CHOOSE_TAC;
  EXISTS_TAC `n+|n'`;
  ASSUME_TAC (ARITH_RULE `n <=| n+n'`);
  ASSUME_TAC (ARITH_RULE `n' <=| n+n'`);
  ASM_MESON_TAC[euclid_sub_closure;euclid_updim];
  ]);;

(* }}} *)

let euclidean_scale_closure = prove_by_refinement(
  `!s f. (euclidean f) ==> (euclidean (s *# f))`,
(* {{{ *)
  [
  REWRITE_TAC[euclidean];
  REPEAT GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `n:num`;
  ASM_MESON_TAC[euclid_scale_closure];
  ]);;
(* }}} *)

let euclidean_neg_closure = prove_by_refinement(
  `!f. (euclidean f) ==> (euclidean (-- f))`,
(* {{{ *)
  [
  REWRITE_TAC[euclidean];
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `n:num`;
  ASM_MESON_TAC[euclid_neg_closure];
  ]);;
(* }}} *)

let euclid_add_comm = prove_by_refinement(
  `!(f:num->real) g. (f + g = g + f)`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_plus;REAL_ARITH `a+.b = b+.a`]
  ]);;
(* }}} *)

let euclid_add_assoc = prove_by_refinement(
  `!(f:num->real) g h. (f + g)+h = f + g + h`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_plus;REAL_ARITH `(a+.b)+.c = a+b+c`];
  ]);;
(* }}} *)

let euclid_lzero = prove_by_refinement(
  `!f. euclid0 + f = f`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_plus;euclid0;REAL_ARITH `&.0+a=a`];
  ACCEPT_TAC (INST_TYPE [(`:num`,`:A`);(`:real`,`:B`)] ETA_AX);
  ]);;
(* }}} *)

let euclid_rzero = prove_by_refinement(
  `!f. f + euclid0  = f`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_plus;euclid0;REAL_ARITH `a+(&.0)=a`];
  ACCEPT_TAC (INST_TYPE [(`:num`,`:A`);(`:real`,`:B`)] ETA_AX);
  ]);;
(* }}} *)

let euclid_ldistrib = prove_by_refinement(
  `!f g r. r *# (f + g) = (r *# f) + (r *# g)`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_plus;euclid_scale;REAL_ARITH `a*(b+.c)=a*b+a*c`];
  ]);;
(* }}} *)

let euclid_rdistrib = prove_by_refinement(
  `!f r s.  (r+s)*# f  = (r *# f) + (s *# f)`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_plus;euclid_scale;REAL_ARITH `(a+b)*c= a*c+b*c`];
  ]);;
(* }}} *)

let euclid_scale_act = prove_by_refinement(
  `!r s f. r *# (s *# f) = (r *s) *# f`,
(* {{{ *)
  [
  REWRITE_TAC[euclid_scale;REAL_ARITH `(a*b)*c = a*(b*c)`];
  ]);;
(* }}} *)

let euclid_scale_one = prove_by_refinement(
  `!f. (&.1) *# f = f`,
(* {{{ proof *)
  [
  REWRITE_TAC[euclid_scale];
  REDUCE_TAC;
  MESON_TAC[ETA_AX];
  ]);;
(* }}} *)

let euclid_neg_sum = prove_by_refinement(
  `!x y .  euclid_minus (--x) (--y) = -- (euclid_minus x y)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[euclid_neg;euclid_minus];
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  BETA_TAC;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let trivial_lin_combo = prove_by_refinement(
  `!x t.  ((t *# x) + (&.1 - t) *# x = x)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[euclid_plus;euclid_scale;];
  IMATCH_MP_TAC  EQ_EXT  THEN BETA_TAC;
  REAL_ARITH_TAC ;
  ]);;
  (* }}} *)


(* DOT PRODUCT  *)

let dot_euclid = prove_by_refinement(
 `!p f g. (euclid p f) /\ (euclid p g) ==>
   (dot f g = sum (0,p) (\i. (f i)* (g i)))`,
(* {{{ *)

  [
  REWRITE_TAC[dot];
    LET_TAC;
  REPEAT GEN_TAC;
  ABBREV_TAC `(P:num->bool) = \m. (euclid m f) /\ (euclid m g)`;
  DISCH_ALL_TAC;
  SUBGOAL_TAC `(P:num->bool) (p:num)`;
  EXPAND_TAC "P";
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  SUBGOAL_TAC `min_num P <=| p`;
  ASM_MESON_TAC[min_least];
  DISCH_TAC;
  SUBGOAL_TAC
    `euclid (min_num (P:num->bool)) f /\ (euclid (min_num (P:num->bool)) g)`;
  ASM_MESON_TAC[min_least];
  DISCH_ALL_TAC;
  ABBREV_TAC `q = min_num P`;
  MP_TAC (SPECL [`q:num`;`p:num`] LE_EXISTS);
  ASM_REWRITE_TAC[];
  DISCH_THEN CHOOSE_TAC;
  ASM_REWRITE_TAC[GSYM SUM_TWO];
  MATCH_MP_TAC (REAL_ARITH `(u = (&.0)) ==> (x = x + u)`);
  SUBGOAL_THEN `!n. n>=| q  ==> ((\i. f i *. g i) n = (&.0))` (fun th -> MATCH_MP_TAC (MATCH_MP SUM_ZERO th));
  GEN_TAC THEN BETA_TAC;
  DISCH_TAC;
  SUBGOAL_THEN `(f:num->real) n = (&.0)` (fun th -> REWRITE_TAC[th;REAL_ARITH `(&.0)*.a =(&.0)`]);
  UNDISCH_TAC `euclid q f`;
  UNDISCH_TAC `n >=| q`;
  MESON_TAC[euclid;ARITH_RULE `(a<=|b) <=> (b >=| a)`];
  ACCEPT_TAC (ARITH_RULE `q >=| q`);
  ]);;

(* }}} *)

let dot_updim = prove_by_refinement (
 `!f g m n. (m <=|n) /\ (euclid m f) /\ (euclid m g) ==>
   (dot f g = sum (0,n) (\i. (f i)* (g i)))`,
(* {{{ *)
 [
 REPEAT GEN_TAC;
 DISCH_ALL_TAC;
   SUBGOAL_TAC `(euclid n f) /\ (euclid n g)`;
 ASM_MESON_TAC[euclid_updim];
 MATCH_ACCEPT_TAC dot_euclid]
);;
(* }}} *)

let dot_nonneg = prove_by_refinement(
 `!f. (&.0 <= (dot f f))`,
(* {{{ *)
 [
 REWRITE_TAC[dot];
   LET_TAC;
 GEN_TAC;
 SUBGOAL_TAC `(!n. (&.0 <=. (\(i:num). f i *. f i) n))`;
 BETA_TAC;
 REWRITE_TAC[REAL_LE_SQUARE];
 ASSUME_TAC(SPEC `\i. (f:num->real) i *. f i` SUM_POS);
 ASM_MESON_TAC[]]);;
(* }}} *)

let dot_comm = prove_by_refinement(
  `!f g. (dot f g = dot g f)`,
(* {{{ *)
 [
 REWRITE_TAC[dot];
 REWRITE_TAC[REAL_ARITH `a*.b = b*.a`;TAUT `a/\b <=> b/\a`]
 ]);;
(* }}} *)

let dot_neg = prove_by_refinement(
  `!f g. (dot (--f) g) = --. (dot f g)`,
(* {{{ *)
 [
 REWRITE_TAC[dot];
   LET_TAC;
  REWRITE_TAC [GSYM neg_dim];
  ONCE_REWRITE_TAC[GSYM SUM_NEG];
  REWRITE_TAC[euclid_neg];
  REPEAT GEN_TAC;
  AP_TERM_TAC;
  MATCH_MP_TAC EQ_EXT;
  BETA_TAC;
  GEN_TAC;
  REWRITE_TAC[REAL_ARITH `(--x) * y = --. (x *y)`];
 ]);;
(* }}} *)

let dot_neg2 = prove_by_refinement(
  `!f g. (dot f (--g)) = --. (dot f g)`,
(* {{{ *)
  [
  ONCE_REWRITE_TAC[dot_comm];
  REWRITE_TAC[dot_neg];
  ]);;
(* }}} *)

let dot_scale = prove_by_refinement(
 `!n f g s. (euclid n f) /\ (euclid n g) ==>
  (dot (s *# f) g = s *. (dot f g))`,
(* {{{ *)
 [
 REWRITE_TAC[euclid_scale];
 REPEAT GEN_TAC;
   DISCH_THEN (fun th -> ASSUME_TAC th THEN ASSUME_TAC (MATCH_MP dot_euclid th));
   SUBGOAL_THEN (`euclid n (\ (i:num). (s *. f i) ) /\ (euclid n g)`) ASSUME_TAC;
 ASM_REWRITE_TAC[];
 ASSUME_TAC(REWRITE_RULE[euclid_scale](SPECL [`n:num`;`s:real`;`f:num->real`] euclid_scale_closure));
 ASM_MESON_TAC[];
 IMP_RES_THEN ASSUME_TAC dot_euclid;
 ASM_REWRITE_TAC[];
 REWRITE_TAC[GSYM SUM_CMUL];
 AP_TERM_TAC;
 MATCH_MP_TAC EQ_EXT;
 GEN_TAC;
 BETA_TAC;
 REWRITE_TAC[REAL_ARITH `a*.(b*.c) = (a*b)*c`];
 ]);;
(* }}} *)

let dot_scale_euclidean = prove_by_refinement(
  `!f g s. (euclidean f) /\ (euclidean g) ==>
  (dot (s *# f) g = s *. (dot f g))`,
(* {{{ *)

 [
 REWRITE_TAC[euclidean];
 DISCH_ALL_TAC;
 REPEAT (UNDISCH_FIND_THEN  `euclid` (CHOOSE_THEN MP_TAC));
 DISCH_ALL_TAC;
 ASSUME_TAC (ARITH_RULE `(n' <=| n+n')`);
 ASSUME_TAC (ARITH_RULE `(n <=| n+n')`);
 SUBGOAL_TAC `euclid (n+|n') f /\ euclid (n+n') g`;
 ASM_MESON_TAC[euclid_updim];
 MESON_TAC[dot_scale];
 ]);;

(* }}} *)

let dot_scale2 = prove_by_refinement(
 `!n f g s. (euclid n f) /\ (euclid n g) ==>
  (dot f (s *# g) = s *. (dot f g))`,
(* {{{ *)
 [
 ONCE_REWRITE_TAC[dot_comm];
 MESON_TAC[dot_scale]
 ]);;
(* }}} *)

let dot_scale2_euclidean = prove_by_refinement(
  `!f g s. (euclidean f) /\ (euclidean g) ==>
  (dot f (s *# g) = s *. (dot f g))`,
(* {{{ *)
 [
 ONCE_REWRITE_TAC[dot_comm];
 MESON_TAC[dot_scale_euclidean];
 ]);;
(* }}} *)

let dot_linear = prove_by_refinement(
 `!n f g h. (euclid n f) /\ (euclid n g) /\ (euclid n h) ==>
    ((dot (f + g) h ) = (dot f h) +. (dot g h))`,
(* {{{ *)
  [
  DISCH_ALL_TAC;
  SUBGOAL_TAC `euclid n (f+g)`;
  ASM_MESON_TAC[euclid_add_closure];
  DISCH_TAC;
  MP_TAC (SPECL [`n:num`;`f:num->real`;`h:num->real`] dot_euclid);
  MP_TAC (SPECL [`n:num`;`g:num->real`;`h:num->real`] dot_euclid);
  MP_TAC (SPECL [`n:num`;`(f+g):num->real`;`h:num->real`] dot_euclid);  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[GSYM SUM_ADD];
  AP_TERM_TAC;
  MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN BETA_TAC;
  REWRITE_TAC[euclid_plus];
  REWRITE_TAC[REAL_ARITH `(a+.b)*.c = a*c + b*c`];
  ]);;
(* }}} *)

let dot_minus_linear = prove_by_refinement(
 `!n f g h. (euclid n f) /\ (euclid n g) /\ (euclid n h) ==>
    ((dot (f - g) h ) = (dot f h) -. (dot g h))`,
(* {{{ *)

  [
  DISCH_ALL_TAC;
  SUBGOAL_TAC `euclid n (f-g)`;
  ASM_MESON_TAC[euclid_sub_closure];
  DISCH_TAC;
  MP_TAC (SPECL [`n:num`;`f:num->real`;`h:num->real`] dot_euclid);
  MP_TAC (SPECL [`n:num`;`g:num->real`;`h:num->real`] dot_euclid);
  MP_TAC (SPECL [`n:num`;`(f-g):num->real`;`h:num->real`] dot_euclid);
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[GSYM SUM_SUB];
  AP_TERM_TAC;
  MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN BETA_TAC;
  REWRITE_TAC[euclid_minus];
  REWRITE_TAC[REAL_ARITH `(a-.b)*.c = a*c - b*c`];
  ]);;

(* }}} *)

let dot_linear_euclidean = prove_by_refinement(
 `!f g h. (euclidean f) /\ (euclidean g) /\ (euclidean h) ==>
    ((dot (f + g) h ) = (dot f h) +. (dot g h))`,
(* {{{ *)
  [
  REWRITE_TAC[euclidean];
  DISCH_ALL_TAC;
  REPEAT (UNDISCH_FIND_THEN `euclid` (CHOOSE_THEN MP_TAC));
  DISCH_ALL_TAC;
  SUBGOAL_TAC `(euclid (n+n'+n'') f)`;
  ASM_MESON_TAC[ARITH_RULE `n <=| n+n'+n''`;euclid_updim];
  SUBGOAL_TAC `(euclid (n+n'+n'') g)`;
  ASM_MESON_TAC[ARITH_RULE `n' <=| n+n'+n''`;euclid_updim];
  SUBGOAL_TAC `(euclid (n+n'+n'') h)`;
  ASM_MESON_TAC[ARITH_RULE `n'' <=| n+n'+n''`;euclid_updim];
  MESON_TAC[dot_linear]]);;
(* }}} *)

let dot_minus_linear_euclidean = prove_by_refinement(
 `!f g h. (euclidean f) /\ (euclidean g) /\ (euclidean h) ==>
    ((dot (f - g) h ) = (dot f h) -. (dot g h))`,
(* {{{ *)

  [
  REWRITE_TAC[euclidean];
  DISCH_ALL_TAC;
  REPEAT (UNDISCH_FIND_THEN `euclid` (CHOOSE_THEN MP_TAC));
  DISCH_ALL_TAC;
  SUBGOAL_TAC `(euclid (n+n'+n'') f)`;
  ASM_MESON_TAC[ARITH_RULE `n <=| n+n'+n''`;euclid_updim];
  SUBGOAL_TAC `(euclid (n+n'+n'') g)`;
  ASM_MESON_TAC[ARITH_RULE `n' <=| n+n'+n''`;euclid_updim];
  SUBGOAL_TAC `(euclid (n+n'+n'') h)`;
  ASM_MESON_TAC[ARITH_RULE `n'' <=| n+n'+n''`;euclid_updim];
  MESON_TAC[dot_minus_linear];
]);;

(* }}} *)

let dot_linear2 = prove_by_refinement(
  `!n f g h. (euclid n f) /\ (euclid n g) /\ (euclid n h) ==>
    ((dot h (f + g)) = (dot h f) +. (dot h g))`,
(* {{{ *)

  [
  REPEAT GEN_TAC;
  ONCE_REWRITE_TAC[dot_comm];
  MESON_TAC[dot_linear]
  ]);;

(* }}} *)

let dot_linear2_euclidean = prove_by_refinement(
  `!f g h. (euclidean f) /\ (euclidean g) /\ (euclidean h) ==>
    ((dot h (f + g)) = (dot h f) +. (dot h g))`,
(* {{{ *)
  [
  REPEAT GEN_TAC;
  ONCE_REWRITE_TAC[dot_comm];
  MESON_TAC[dot_linear_euclidean]
  ]);;
(* }}} *)

let dot_minus_linear2 = prove_by_refinement(
  `!n f g h. (euclid n f) /\ (euclid n g) /\ (euclid n h) ==>
    ((dot h (f - g)) = (dot h f) -. (dot h g))`,
(* {{{ *)

  [
  REPEAT GEN_TAC;
  ONCE_REWRITE_TAC[dot_comm];
  MESON_TAC[dot_minus_linear]
  ]);;

(* }}} *)

let dot_minus_linear2_euclidean = prove_by_refinement(
  `!f g h. (euclidean f) /\ (euclidean g) /\ (euclidean h) ==>
    ((dot h (f - g)) = (dot h f) -. (dot h g))`,
(* {{{ *)

  [
  REPEAT GEN_TAC;
  ONCE_REWRITE_TAC[dot_comm];
  MESON_TAC[dot_minus_linear_euclidean]
  ]);;

(* }}} *)

let dot_rzero = prove_by_refinement(
  `!f. (dot f euclid0) = &.0`,
(* {{{ *)
   [
     REWRITE_TAC[dot;euclid0];
     LET_TAC;
     GEN_TAC;
     SUBGOAL_THEN `(\ (i:num). (f i *. (&.0))) = (\ (r:num). (&.0))` (fun t -> REWRITE_TAC[t]);
   REWRITE_TAC[REAL_ARITH `a*.(&.0) = (&.0)`];
   MESON_TAC[SUM_0];
   ]);;
(* }}} *)

let dot_lzero = prove_by_refinement(
   `!f. (dot euclid0 f ) = &.0`,
(* {{{ *)
   [
   ONCE_REWRITE_TAC[dot_comm];
   REWRITE_TAC[dot_rzero];
   ]);;
(* }}} *)

let dot_zero = prove_by_refinement(
  `!f n. (euclid n f) /\ (dot f f = (&.0)) ==> (f = euclid0)`,
(* {{{ *)
   [
   DISCH_ALL_TAC;
   UNDISCH_TAC `dot f f = (&.0)`;
   MP_TAC (SPECL [`n:num`;`f:num->real`;`f:num->real`] dot_euclid);
   ASM_REWRITE_TAC[];
   DISCH_THEN (fun th -> REWRITE_TAC[th]);
   REWRITE_TAC[euclid0];
   DISCH_TAC;
   MATCH_MP_TAC EQ_EXT;
   GEN_TAC THEN BETA_TAC;
   DISJ_CASES_TAC (ARITH_RULE `x <| n \/ (n <=| x)`);
   CLEAN_ASSUME_TAC (ARITH_RULE `(x <|n) ==> (SUC x <=| n)`);
   CLEAN_THEN (SPECL [`SUC x`;`n:num`] LE_EXISTS) CHOOSE_TAC;
   UNDISCH_TAC `sum(0,n) (\ (i:num). f i *. f i) = (&.0)`;
   ASM_REWRITE_TAC[];
   REWRITE_TAC[GSYM SUM_TWO;sum;ARITH_RULE `0+| x = x`];
   SUBGOAL_TAC `!a b. (&.0 <=. sum(a,b) (\ (i:num). f i *. f i))`;
   REPEAT GEN_TAC;
   MP_TAC (SPEC `\ (i:num). f i *. f i` SUM_POS);
   BETA_TAC;
   REWRITE_TAC[REAL_LE_SQUARE];
   MESON_TAC[];
   DISCH_ALL_TAC;
   IMP_RES_THEN MP_TAC (REAL_ARITH `(a+.b = &.0) ==> ((&.0 <=. b) ==> (a <=. (&.0)))`);
   ASM_REWRITE_TAC[];
   DISCH_TAC;
   IMP_RES_THEN MP_TAC (REAL_ARITH `(a+b <=. &.0) ==> ((&.0 <=. a) ==> (b <=. (&.0)))`);
   ASM_REWRITE_TAC[];
   ABBREV_TAC `a = (f:num->real) x`;
   MESON_TAC[REAL_LE_SQUARE;REAL_ARITH `a <=. (&.0) /\ (&.0 <=. a) ==> (a = (&.0))`;REAL_ENTIRE];
   UNDISCH_TAC `euclid n f`;
   REWRITE_TAC[euclid];
   ASM_MESON_TAC[];
   ]);;
(* }}} *)

let dot_zero_euclidean = prove_by_refinement(
  `!f. (euclidean f) /\ (dot f f = (&.0)) ==> (f = euclid0)`,
(* {{{ *)
   [
   REWRITE_TAC[euclidean];
   DISCH_ALL_TAC;
   UNDISCH_FIND_THEN `euclid` CHOOSE_TAC;
   ASM_MESON_TAC[dot_zero];
   ]);;
(* }}} *)

(* norm *)

let norm_nonneg = prove_by_refinement(
   `!f. (&.0 <=. norm f)`,
(* {{{ *)
   [
   REWRITE_TAC[norm];
   ONCE_REWRITE_TAC[GSYM SQRT_0];
   GEN_TAC;
   MATCH_MP_TAC SQRT_MONO_LE;
   REWRITE_TAC[dot_nonneg];
   ]);;
(* }}} *)

let norm_neg = prove_by_refinement(
  `!f. norm (--f) = norm f`,
(* {{{ *)

  [
  REWRITE_TAC[norm;dot_neg;dot_neg2];
  REWRITE_TAC[REAL_ARITH `--(--. x) = x`];
  ]);;

(* }}} *)

let cauchy_schwartz = prove_by_refinement(
  `!f g. (euclidean f) /\ (euclidean g) ==>
   ((abs(dot f g)) <=. (norm f)*. (norm g))`,
(* {{{ *)
  [
  DISCH_ALL_TAC;
  DISJ_CASES_TAC (TAUT `(f = euclid0 ) \/ ~(f = euclid0)`);
  ASM_REWRITE_TAC[dot_lzero;norm;SQRT_0;REAL_ARITH`&.0 *. x = (&.0)`];
  REWRITE_TAC[ABS_0;REAL_ARITH `x <=. x`];
  SUBGOAL_THEN `!a b. (dot (a *# f + b *# g) (a *# f + b *# g)) = a*a*(dot f f) + (&.2)*a*b*(dot f g) + b*b*(dot g g)` ASSUME_TAC;
  REPEAT GEN_TAC;
  ASM_SIMP_TAC[euclidean_scale_closure;euclidean_add_closure;dot_linear_euclidean;dot_linear2_euclidean;dot_scale_euclidean;dot_scale2_euclidean];
  REWRITE_TAC[REAL_MUL_AC;REAL_ADD_AC;REAL_ADD_LDISTRIB];
  MATCH_MP_TAC (REAL_ARITH`(b+. c=e) ==> (a+b+c+d = a+ e+d)`);
  REWRITE_TAC[GSYM REAL_LDISTRIB];
  REPEAT AP_TERM_TAC;
  MATCH_MP_TAC (REAL_ARITH `(a=b)==> (a+.b = a*(&.2))`);
  REWRITE_TAC[dot_comm];
  FIRST_ASSUM (fun th -> ASSUME_TAC (SPECL[` --. (dot f g)`;`dot f f`] th));
  CLEAN_THEN (SPEC `(--.(dot f g)) *# f + (dot f f)*# g` dot_nonneg) ASSUME_TAC;
  REWRITE_TAC[norm];
  ASSUME_TAC(SPEC `f:num->real` dot_nonneg);
  ASSUME_TAC(SPEC `g:num->real` dot_nonneg);
  ASM_SIMP_TAC[GSYM SQRT_MUL];
  REWRITE_TAC[GSYM POW_2_SQRT_ABS;POW_2];
  MATCH_MP_TAC SQRT_MONO_LE;
  REWRITE_TAC[REAL_LE_SQUARE];
  SUBGOAL_TAC `&.0 <. dot f f`;
  MATCH_MP_TAC (REAL_ARITH `~(x = &.0) /\ (&.0 <=. x) ==> (&.0 <. x)`);
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[dot_zero_euclidean];
  REPEAT (UNDISCH_FIND_TAC `(<=.)` );
  ABBREV_TAC `a = dot f f`;
  ABBREV_TAC `b = dot f g`;
  ABBREV_TAC `c = dot g g`;
  POP_ASSUM_LIST (fun t -> ALL_TAC);
  REWRITE_TAC[REAL_ARITH `(&.2 *. x = x + x)`;REAL_ADD_AC];
  REWRITE_TAC[REAL_ARITH `(a *. ((--. b)*.c) = --. (a *. (b*.c)))/\ (--. ((--. a) *. b) = a *.b )`];
  REWRITE_TAC[REAL_ARITH `(--. b) *. a*. b + b*.b*.a = (&.0)`];
  REWRITE_TAC[REAL_ARITH `x +. (&.0) = x`];
  REWRITE_TAC[REAL_ARITH `(&.0 <=. (a*.a*.c +. (--.b)*.a*.b)) <=> (a*b*b <=. a*a*c)`];
  DISCH_ALL_TAC;
  MATCH_MP_TAC (SPEC `a:real` REAL_LE_LCANCEL_IMP);
  ASM_REWRITE_TAC[];
  ]);;
(* }}} *)

let norm_dot = prove_by_refinement(
  `!h. norm(h) * norm(h) = (dot h h)`,
(* {{{ *)
  [
  REWRITE_TAC[norm];
  ONCE_REWRITE_TAC[GSYM POW_2];
  REWRITE_TAC[SQRT_POW2;dot_nonneg];
  ]);;
(* }}} *)

let norm_triangle = prove_by_refinement(
  `!f g. (euclidean f) /\ (euclidean g) ==>
    (norm (f+g) <=. norm(f) + norm(g))`,
(* {{{ *)
  [
  DISCH_ALL_TAC;
  MATCH_MP_TAC square_le;
  REWRITE_TAC[norm_nonneg];
  CONJ_TAC;
  MATCH_MP_TAC (REAL_ARITH `(&.0 <=. x) /\ (&.0 <=. y) ==> (&.0 <= x+y)`);
  REWRITE_TAC[norm_nonneg];
  REWRITE_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_ADD_AC];
  REWRITE_TAC[norm_dot];
ASM_SIMP_TAC[euclidean_add_closure;dot_linear_euclidean;dot_linear2_euclidean];
  REWRITE_TAC[REAL_MUL_AC];
  REWRITE_TAC[REAL_ADD_AC];
  MATCH_MP_TAC (REAL_ARITH `(b<=.c)==>((a+.b) <=. (a+c))`);
  MATCH_MP_TAC (REAL_ARITH `(a=b)/\ (a<=. e) ==>((a+b+c) <= (c+e+e))`);
  CONJ_TAC;
  REWRITE_TAC[dot_comm];
  ASM_MESON_TAC[cauchy_schwartz;REAL_LE_TRANS;REAL_ARITH `x <=. ||. x`];
  ]);;
(* }}} *)



(* ------------------------------------------------------------------ *)
(* Metric Space *)
(* ------------------------------------------------------------------ *)

let metric_space_zero = prove_by_refinement(
 `!(X:A->bool) d a. (metric_space(X,d) /\ (X a) ==> (d a a = (&.0)))`,
(* {{{ *)
  [MESON_TAC[metric_space]
  ]);;
(* }}} *)

let metric_space_symm = prove_by_refinement(
 `!(X:A->bool) d a b. (metric_space(X,d) /\ (X a) /\ (X b) ==>
   (d a b = d b a))`,
(* {{{ *)
  [
  MESON_TAC[metric_space];
  ]);;
(* }}} *)

let metric_space_triangle = prove_by_refinement(
 `!(X:A->bool) d a b c. (metric_space(X,d) /\ (X a) /\ (X b) /\ (X c)
   ==> (d a c <=. d a b +. d b c))`,
(* {{{ *)
  [
  MESON_TAC[metric_space];
  ]);;
(* }}} *)

let metric_subspace = prove_by_refinement(
  `!X Y d. (Y SUBSET (X:A->bool)) /\ (metric_space (X,d)) ==>
    (metric_space (Y,d))`,
(* {{{ *)
  [
  REWRITE_TAC[SUBSET;metric_space;IN];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  UNDISCH_FIND_THEN `( /\ )` (fun t -> MP_TAC (SPECL[`x:A`;`y:A`;`z:A`] t));
  ASM_SIMP_TAC[];
  ]);;
(* }}} *)

let metric_euclidean = prove_by_refinement(
  `metric_space (euclidean,d_euclid)`,
(* {{{ *)
  [
  REWRITE_TAC[metric_space;d_euclid];
  DISCH_ALL_TAC;
  CONJ_TAC;
  REWRITE_TAC[norm_nonneg];
  CONJ_TAC;
  EQ_TAC;
  REWRITE_TAC[norm];
  ONCE_REWRITE_TAC[REAL_ARITH `(&.0 = x) <=> (x = (&.0))`];
  ASM_SIMP_TAC[dot_nonneg;SQRT_EQ_0];
  DISCH_TAC;
  SUBGOAL_TAC `x - y = euclid0`;
  ASM_MESON_TAC[dot_zero_euclidean;euclidean_sub_closure];
  REWRITE_TAC[euclid_minus;euclid0];
  DISCH_TAC THEN (MATCH_MP_TAC EQ_EXT);
  X_GEN_TAC `n:num`;
  FIRST_ASSUM  (fun t -> ASSUME_TAC (BETA_RULE (AP_THM t `n:num`)));
  ASM_MESON_TAC [REAL_ARITH `(a = b) <=> (a-.b = (&.0))`];
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  SUBGOAL_THEN `(y:num->real) - y = euclid0` (fun t-> REWRITE_TAC[t]);
  REWRITE_TAC[euclid0;euclid_minus];
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC THEN BETA_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[norm;dot_lzero;SQRT_0];
  CONJ_TAC;
  SUBGOAL_THEN `x - y = (euclid_neg (y-x))` ASSUME_TAC;
  REWRITE_TAC[euclid_neg;euclid_minus];
  MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN BETA_TAC;
  REAL_ARITH_TAC;
  ASM_MESON_TAC[norm_neg];
  SUBGOAL_THEN `(x-z) = euclid_plus(x - y)  (y-z)` (fun t -> REWRITE_TAC[t]);
  REWRITE_TAC[euclid_plus;euclid_minus];
  MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
  ASM_SIMP_TAC[norm_triangle;euclidean_sub_closure;euclidean_sub_closure];
  ]);;
(* }}} *)

let metric_euclid = prove_by_refinement(
  `!n. metric_space (euclid n,d_euclid)`,
(* {{{ *)
  [
  GEN_TAC;
  MATCH_MP_TAC (ISPEC `euclidean` metric_subspace);
  REWRITE_TAC[metric_euclidean;SUBSET;IN];
  MESON_TAC[euclidean];
  ]);;
(* }}} *)

let euclid1_abs = prove_by_refinement(
  `!x y. (euclid 1 x) /\ (euclid 1 y) ==>
     ((d_euclid x y) = (abs ((x 0) -. (y 0))))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[d_euclid;norm];
  DISCH_ALL_TAC;
  SUBGOAL_TAC `euclid 1 (x - y)`;
  ASM_MESON_TAC[euclid_sub_closure];
  DISCH_TAC;
  ASSUME_TAC (prove(`1 <= 1`,ARITH_TAC));
  MP_TAC (SPECL[`(x-y):num->real`;`(x-y):num->real`;`1`;`1`] dot_updim);
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  REWRITE_TAC[prove(`1 = SUC 0`,ARITH_TAC)];
  REWRITE_TAC[sum];
  REWRITE_TAC[REAL_ARITH `&.0 + x = x`];
  REWRITE_TAC[ARITH_RULE `0 +| 0 = 0`];
  REWRITE_TAC[euclid_minus];
  ASM_MESON_TAC[REAL_POW_2;POW_2_SQRT_ABS];
  ]);;
  (* }}} *)

let coord_dirac = prove_by_refinement(
  `!i t. coord i (t *# dirac_delta i ) = t`,
  (* {{{ proof *)

  [
  REWRITE_TAC[coord;dirac_delta;euclid_scale];
  ARITH_TAC;
  ]);;

  (* }}} *)

let dirac_0 = prove_by_refinement(
  `!x. (x *# dirac_delta 0) 0 = x`,
  (* {{{ proof *)
  [
  GEN_TAC;
  REWRITE_TAC[dirac_delta;euclid_scale;];
  REDUCE_TAC;
  ]);;
  (* }}} *)

let euclid1_dirac = prove_by_refinement(
  `!x. euclid 1 x <=> (x = (x 0) *# (dirac_delta 0))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[euclid; euclid_scale;dirac_delta ];
  EQ_TAC;
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  X_GEN_TAC `n:num`;
  BETA_TAC;
  COND_CASES_TAC;
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  REDUCE_TAC;
  ASM_SIMP_TAC[ARITH_RULE  `(~(0=m))==>(1<=| m)`];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  USE 1 (MATCH_MP (ARITH_RULE `1<= m ==> (~(0=m))`));
  ASM ONCE_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  REDUCE_TAC ;
  ]);;
  (* }}} *)

(* projection onto the ith coordinate, as a euclidean vector *)
let proj = euclid_def
  `proj i x = (\j. (if (j=0) then (x (i:num)) else (&.0)))`;;

let proj_euclid1 = prove_by_refinement(
  `!i x. euclid 1 (proj i x)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[proj;euclid];
  REPEAT GEN_TAC;
  COND_CASES_TAC;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  ARITH_TAC;
  ]);;
  (* }}} *)

let d_euclid_n = prove_by_refinement(
  `!n x y. ((euclid n x) /\ (euclid n y)) ==> ((d_euclid x y) =
     sqrt(sum (0,n) (\i. (x i - y i) * (x i - y i))))`,
  (* {{{ proof *)

  [
  REPEAT GEN_TAC;
  REWRITE_TAC[d_euclid;norm];
  DISCH_ALL_TAC;
  ASSUME_TAC (ARITH_RULE `n <=| n`);
  SUBGOAL_TAC `euclid n (x - y)`;
  ASM_SIMP_TAC[euclid_sub_closure];
  DISCH_TAC;
  CLEAN_ASSUME_TAC (SPECL[`(x-y):num->real`;`(x-y):num->real`;`n:num`;`n:num`]dot_updim);
  ASM_REWRITE_TAC[euclid_minus];
  ]);;

  (* }}} *)

let norm_n = prove_by_refinement(
  `!n x. ((euclid n x) ) ==> ((norm x) =
     sqrt(sum (0,n) (\i. (x i ) * (x i ))))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  TYPEL_THEN [`x`;`x`;`n`;`n`] (fun t-> SIMP_TAC  [norm;ISPECL t dot_updim;ARITH_RULE `n <=| n`;]);
  ]);;
  (* }}} *)

let proj_d_euclid = prove_by_refinement(
  `!i x y. d_euclid (proj i x) (proj i y) = abs (x i -. y i)`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  SIMP_TAC[SPEC `1` d_euclid_n;proj_euclid1];
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`;sum];
  NUM_REDUCE_TAC;
  REWRITE_TAC[proj];
  REWRITE_TAC[REAL_ARITH `&.0 + x = x`];
  MESON_TAC[POW_2_SQRT_ABS;REAL_POW_2];
  ]);;
  (* }}} *)

let d_euclid_pos = prove_by_refinement(
  `!x y n. (euclid n x) /\ (euclid n y) ==> (&.0 <=. d_euclid x y)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MP_TAC metric_euclid;
  REWRITE_TAC[metric_space;euclidean];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let proj_contraction = prove_by_refinement(
  `!n x y i. (euclid n x) /\ (euclid n y) ==>
     abs (x i - (y i)) <=. d_euclid x y`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MATCH_MP_TAC REAL_POW_2_LE;
  REWRITE_TAC[REAL_ABS_POS];
  CONJ_TAC;
  ASM_MESON_TAC[d_euclid_pos];
  ASM_SIMP_TAC[SPEC `n:num` d_euclid_n];
  REWRITE_TAC[REAL_POW2_ABS];
  SUBGOAL_TAC `euclid n (x - y)`; (* why does MESON fail here??? *)
  MATCH_MP_TAC euclid_sub_closure;
  ASM_MESON_TAC[];
  DISCH_TAC;
  SUBGOAL_TAC `&.0 <=. sum (0,n) (\i. (x i - y i)*. (x i - y i))`;
  MATCH_MP_TAC SUM_POS_GEN;
  DISCH_ALL_TAC THEN BETA_TAC;
  REWRITE_TAC[REAL_LE_SQUARE];
  SIMP_TAC[SQRT_POW_2];
  DISCH_TAC;
  ASM_CASES_TAC `n <=| i`;
  MATCH_MP_TAC (REAL_ARITH `(x = (&.0)) /\ (&.0 <=. y) ==> (x <=. y)`);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_PROP_ZERO_POW];
  NUM_REDUCE_TAC;
  ASM_MESON_TAC[euclid;euclid_minus];
  MP_TAC (ARITH_RULE `~(n <=| i) ==> (i < n) /\ (n = (SUC i) + (n-i-1))`);
  ASM_REWRITE_TAC[] THEN DISCH_ALL_TAC;
  ASM ONCE_REWRITE_TAC[];
  REWRITE_TAC[GSYM SUM_TWO];
  MATCH_MP_TAC (REAL_ARITH `(a <=. b) /\ (&.0 <=. c)   ==> (a <=. (b +c))`);
  CONJ_TAC;
  REWRITE_TAC[sum_DEF];
  REWRITE_TAC[ARITH_RULE `0 +| i = i`];
  MATCH_MP_TAC (REAL_ARITH `(a = c) /\ (&.0 <=. b) ==> (a <=. b+c)`);
  REWRITE_TAC[REAL_POW_2];
  MP_TAC (SPECL [`0:num`;`i:num`;`(x:num->real)- y`] REAL_SUM_SQUARE_POS);
  BETA_TAC;
  REWRITE_TAC[euclid_minus];
  MP_TAC (SPECL [`SUC i`;`(n:num)-i-1`;`(x:num->real)- y`] REAL_SUM_SQUARE_POS);
  BETA_TAC;
  REWRITE_TAC[euclid_minus];
  ]);;
  (* }}} *)

let euclid_dirac = prove_by_refinement(
  `!x. (euclid 1 (x *# (dirac_delta 0)))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[euclid;dirac_delta ;euclid_scale];
  DISCH_ALL_TAC;
  USE 0 (MATCH_MP (ARITH_RULE  `1 <=| m ==> (~(0=m))`));
  ASM_REWRITE_TAC[];
  REDUCE_TAC;
  ]);;
  (* }}} *)

let d_euclid_pow2 = prove_by_refinement(
  `!n x y. (euclid n x) /\ (euclid n y) ==>
     ((d_euclid x y) pow 2 = sum (0,n) (\i. (x i - y i) * (x i - y i)))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[d_euclid_n];
  REWRITE_TAC[SQRT_POW2];
  MATCH_MP_TAC SUM_POS_GEN;
  BETA_TAC;
  REDUCE_TAC;
  ]);;
  (* }}} *)

let D_EUCLID_BOUND = prove_by_refinement(
  `!n x y eps. ((euclid n x) /\ (euclid n y) /\
     (!i. (abs (x i -. y i) <=. eps))) ==>
    ( d_euclid x y <=. sqrt(&.n)*. eps )`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  SQUARE_TAC;
  SUBCONJ_TAC;
  JOIN 0 1;
  USE 0 (MATCH_MP d_euclid_pos);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  WITH 2 (SPEC `0`);
  USE 4 (MATCH_MP (REAL_ARITH `abs (x) <=. eps ==> &.0 <=. eps`));
  SUBCONJ_TAC;
  ALL_TAC;
  REWRITE_TAC[REAL_MUL_NN];
  DISJ1_TAC;
  CONJ_TAC;
  MATCH_MP_TAC SQRT_POS_LE ;
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ASM_SIMP_TAC[d_euclid_pow2];
  SUBGOAL_TAC `!i. ((x:num->real) i -. y i) *. (x i -. y i) <=. eps* eps`;
  GEN_TAC;
  ALL_TAC;
  USE 2 (SPEC `i:num`);
  ABBREV_TAC `t = x i - (y:num->real) i`;
  UND 2;
  REWRITE_TAC[ABS_SQUARE_LE];
  REWRITE_TAC[REAL_POW_MUL];
  ASSUME_TAC (REWRITE_RULE[] ((REDUCE_CONV `&.0 <= &.n`)));
  USE 6 (REWRITE_RULE[GSYM SQRT_POW2]);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ALL_TAC;
  MATCH_MP_TAC SUM_BOUND;
  GEN_TAC;
  DISCH_TAC;
  BETA_TAC;
  REWRITE_TAC[POW_2];
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let metric_translate = prove_by_refinement(
  `!n x y z . (euclid n x) /\ (euclid n y) /\ (euclid n z) ==>
   (d_euclid (x + z) (y + z) = d_euclid x y)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[d_euclid;norm];
  DISCH_ALL_TAC;
  TYPE_THEN `euclid n (euclid_minus x y)` SUBGOAL_TAC;
  ASM_SIMP_TAC[euclid_sub_closure];
  DISCH_TAC;
  TYPE_THEN `euclid n (euclid_minus (euclid_plus x z) (euclid_plus y z))` SUBGOAL_TAC;
  ASM_SIMP_TAC[euclid_sub_closure; euclid_add_closure];
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[SPEC `n:num` dot_euclid];
  TYPE_THEN `(x + z) - (y + z) = ((x:num->real) - y)` SUBGOAL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  X_GEN_TAC `i:num`;
  REWRITE_TAC[euclid_minus;euclid_plus];
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  ]);;

  (* }}} *)

let metric_translate_LEFT = prove_by_refinement(
  `!n x y z . (euclid n x) /\ (euclid n y) /\ (euclid n z) ==>
   (d_euclid (z + x ) (z + y) = d_euclid x y)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[d_euclid;norm];
  DISCH_ALL_TAC;
  TYPE_THEN `euclid n (euclid_minus x y)` SUBGOAL_TAC;
  ASM_SIMP_TAC[euclid_sub_closure];
  DISCH_TAC;
  TYPE_THEN `euclid n (euclid_minus (euclid_plus z x) (euclid_plus z y))` SUBGOAL_TAC;
  ASM_SIMP_TAC[euclid_sub_closure; euclid_add_closure];
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[SPEC `n:num` dot_euclid];
  TYPE_THEN `(z + x) - (z + y) = ((x:num->real) - y)` SUBGOAL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  X_GEN_TAC `i:num`;
  REWRITE_TAC[euclid_minus;euclid_plus];
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  ]);;

  (* }}} *)

let norm_scale = prove_by_refinement(
  `!t t' x . (euclidean x) ==>
   (d_euclid (t *# x) (t' *# x) =
        ||. (t - t') * norm(x))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[euclidean];
  LEFT_TAC "n";
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[d_euclid_n;norm_n;euclid_scale_closure;euclid_scale;GSYM REAL_SUB_RDISTRIB;REAL_MUL_AC;];
  REWRITE_TAC[GSYM REAL_POW_2   ];
  REWRITE_TAC[REAL_ARITH `a * a * b = b * (a * a)`;SUM_CMUL;];
  ASM_SIMP_TAC[SQRT_MUL;REAL_SUM_SQUARE_POS;REAL_LE_SQUARE_POW;POW_2_SQRT_ABS  ];
  REWRITE_TAC[REAL_POW_2];
  ]);;

  (* }}} *)

let norm_scale_vec = prove_by_refinement(
  `!n t x x' . (euclid n x) /\ (euclid n x') ==>
   (d_euclid (t *# x) (t *# x') = ||. t * d_euclid x x')`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[d_euclid_n;norm_n;euclid_scale_closure;euclid_scale;GSYM REAL_SUB_LDISTRIB;REAL_MUL_AC;];
  REWRITE_TAC[REAL_ARITH `t*t*b = (t*t)*b`];
  REWRITE_TAC[GSYM REAL_POW_2 ;SUM_CMUL   ];
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_2];
  ASM_SIMP_TAC[SQRT_MUL;REAL_SUM_SQUARE_POS;REAL_LE_SQUARE_POW;POW_2_SQRT_ABS  ];
  REWRITE_TAC[REAL_POW_2];
    ]);;

  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Topological Spaces *)
(* ------------------------------------------------------------------ *)


(* Definitions *)
(* underscore is necessary to avoid Harrison's global "topology" *)
(* carrier of topology is UNIONS U *)

let topology = euclid_def `topology_ (U:(A->bool)->bool) <=>
  (!A B V.  (U EMPTY) /\
      ((U A) /\ (U B) ==> (U (A INTER B))) /\
      ((V SUBSET U) ==> (U (UNIONS V))))`;;

let open_DEF = euclid_def `open_ (U:(A->bool)->bool) A = (U A)`;;

let closed = euclid_def `closed_ (U:(A->bool)->bool) B <=>
    (B SUBSET (UNIONS U)) /\
    (open_ U ((UNIONS U) DIFF B))`;;

let closure = euclid_def `closure (U:(A->bool)->bool) A =
    INTERS { B | (closed_ U B) /\ (A SUBSET B) }`;;

let induced_top  = euclid_def `induced_top U (A:A->bool) =
  IMAGE ( \B. (B INTER A)) U`;;

let open_ball = euclid_def
  `open_ball(X,d) (x:A) r = { y | (X x) /\ (X y) /\ (d x y <. r) }`;;

let closed_ball =euclid_def
  `closed_ball (X,d) (x:A) r = { y | (X x) /\ (X y) /\ (d x y <=. r) }`;;

let open_balls = euclid_def
  `open_balls (X,d) = { B | ?(x:A) r. B = open_ball (X,d) x r}`;;

let top_of_metric = euclid_def
  `top_of_metric ((X:A->bool),d) =
      { A | ?F. (F SUBSET (open_balls (X,d)))/\
     (A = UNIONS F) }`;;

(* basic properties *)

let open_EMPTY = prove_by_refinement(
  `!(U:(A->bool)->bool). (topology_ U ==> open_ U EMPTY)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[topology;open_DEF];
  MESON_TAC[];
  ]);;
  (* }}} *)

let open_closed = prove_by_refinement(
  `!U A. (topology_ (U:(A->bool)->bool)) /\ (open_ U A) ==>
     (closed_ U ((UNIONS U) DIFF A))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[closed;open_DEF];
  DISCH_ALL_TAC;
  SUBGOAL_THEN `(A:A->bool) SUBSET (UNIONS U)` ASSUME_TAC;
  ASM_MESON_TAC[sub_union];
  ASM_SIMP_TAC[DIFF_DIFF2];
  REWRITE_TAC[SUBSET_DIFF];
  ]);;
(* }}} *)

let closed_UNIV = prove_by_refinement(
  `!(U:(A->bool)->bool). (topology_ U ==> closed_ U (UNIONS U))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[open_closed];
  REWRITE_TAC[closed;open_DEF];
  TYPE_THEN `a = UNIONS U` ABBREV_TAC;
  USE 0 (REWRITE_RULE[topology]);
  CONJ_TAC;
  MESON_TAC[SUBSET];
  USE 0 (CONV_RULE (quant_right_CONV "V"));
  USE 0 (CONV_RULE (quant_right_CONV "B"));
  USE 0 (CONV_RULE (quant_right_CONV "A"));
  AND 0;
  UND 2;
  MESON_TAC[DIFF_EQ_EMPTY];
  ]);;

  (* }}} *)

let top_univ = prove_by_refinement(
  `!(U:(A->bool)->bool). (topology_ U) ==> (U (UNIONS U))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[topology];
  DISCH_ALL_TAC;
  ASM_MESON_TAC[SUBSET_REFL];
  ]);;
  (* }}} *)

let empty_closed = prove_by_refinement(
  `!(U:(A->bool)->bool).
     (topology_ U) ==> closed_ U EMPTY`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[closed;EMPTY_SUBSET;DIFF_EMPTY;open_DEF];
  ASM_MESON_TAC[top_univ];
  ]);;
  (* }}} *)

let closed_open = prove_by_refinement(
  `!(U:(A->bool)->bool) A.  (closed_ U A) ==>
    (open_ U ((UNIONS U) DIFF A))`,
  (* {{{ proof *)
  [
  MESON_TAC[closed];
  ]);;
(* }}} *)

let closed_inter = prove_by_refinement (
  `!U V. (topology_ (U:(A->bool)->bool)) /\ (!a. (V a) ==> (closed_ U a))
    /\ ~(V = EMPTY)
     ==> (closed_ U (INTERS V))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[closed];
  DISCH_ALL_TAC;
  CONJ_TAC;
  MATCH_MP_TAC  INTERS_SUBSET2;
  USE 2 (REWRITE_RULE[ EMPTY_EXISTS]);
  USE 2 (REWRITE_RULE[IN]);
  CHO 2;
  EXISTS_TAC `u:A->bool`;
  ASM_MESON_TAC[ ];
  ABBREV_TAC `VCOMP = IMAGE ((DIFF) (UNIONS (U:(A->bool)->bool))) V`;
  UNDISCH_FIND_THEN `VCOMP` (fun t -> ASSUME_TAC (GSYM t));
  SUBGOAL_THEN `(VCOMP:(A->bool)->bool) SUBSET U` ASSUME_TAC;
  ASM_REWRITE_TAC[SUBSET;IN_ELIM_THM;IMAGE];
  REWRITE_TAC[IN];
  GEN_TAC;
  ASM_MESON_TAC[open_DEF];
  SUBGOAL_THEN `open_ U (UNIONS (VCOMP:(A->bool)->bool))` ASSUME_TAC;
  ASM_MESON_TAC[topology;open_DEF];
  SUBGOAL_THEN ` (UNIONS U DIFF INTERS V)= (UNIONS (VCOMP:(A->bool)->bool))` (fun t-> (REWRITE_TAC[t]));
  ASM_REWRITE_TAC[UNIONS_INTERS];
  UNDISCH_FIND_TAC `(open_)`;
  REWRITE_TAC[];
  ]);;
(* }}} *)

let open_nbd = prove_by_refinement(
  `!U (A:A->bool). (topology_ U) ==>
    ((U A) = (!x. ?B. (A x ) ==> ((B SUBSET A) /\ (B x) /\ (U B))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  EXISTS_TAC `A:A->bool`;
  ASM_MESON_TAC[SUBSET];
  CONV_TAC (quant_left_CONV "B");
  DISCH_THEN CHOOSE_TAC;
  USE 1 (CONV_RULE NAME_CONFLICT_CONV);
  TYPE_THEN `UNIONS (IMAGE B A)  = A` SUBGOAL_TAC;
  MATCH_MP_TAC  SUBSET_ANTISYM;
  CONJ_TAC;
  MATCH_MP_TAC  UNIONS_SUBSET;
  REWRITE_TAC[IN_IMAGE];
  ASM_MESON_TAC[IN];
  REWRITE_TAC[SUBSET;IN_UNIONS;IN_IMAGE];
  DISCH_ALL_TAC;
  NAME_CONFLICT_TAC;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x'");
  EXISTS_TAC `x:A`;
  TYPE_THEN `B x` EXISTS_TAC ;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[IN];
  (* on 1*)
  TYPE_THEN `(IMAGE B A) SUBSET U` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE;];
  REWRITE_TAC[IN];
  NAME_CONFLICT_TAC;
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  TYPE_THEN `W = IMAGE B A` ABBREV_TAC;
  KILL 2;
  ASM_MESON_TAC[topology];
  ]);;
  (* }}} *)

let open_inters = prove_by_refinement(
  `!U (V:(A->bool)->bool). (topology_ U) /\ (V SUBSET U) /\
    (FINITE V) /\ ~(V = EMPTY)  ==>
                        (U (INTERS V))`,
  (* {{{ proof *)
  [
  REP_GEN_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `(?n. V HAS_SIZE n)` SUBGOAL_TAC;
  REWRITE_TAC[HAS_SIZE];
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  UND 0;
  UND 1;
  UND 2;
  UND 3;
  UND 4;
  CONV_TAC (quant_left_CONV "n");
  TYPE_THEN `V` SPEC2_TAC ;
  TYPE_THEN `U` SPEC2_TAC ;
  CONV_TAC (quant_left_CONV "n");
  CONV_TAC (quant_left_CONV "n");
  INDUCT_TAC;
  DISCH_ALL_TAC;
  ASM_MESON_TAC[HAS_SIZE_0];
  DISCH_ALL_TAC;
  TYPE_THEN `U` (USE 0 o SPEC);
  USE 5 (REWRITE_RULE[HAS_SIZE_SUC;EMPTY_EXISTS]);
  AND 5;
  CHO 6;
  TYPE_THEN `u` (USE 5 o SPEC);
  REWR 5;
  TYPE_THEN `V DELETE u` (USE  0 o SPEC);
  REWR 0;
  TYPE_THEN `V={u}` ASM_CASES_TAC;
  ASM_REWRITE_TAC[inters_singleton];
  UND 6;
  UND 2;
  REWRITE_TAC [SUBSET;IN];
  MESON_TAC[];
  ALL_TAC; (* oi1 *)
  USE 0 (REWRITE_RULE[delete_empty]);
  REWR 0;
  USE 0 (REWRITE_RULE[FINITE_DELETE]);
  REWR 0;
  TYPE_THEN `V DELETE u SUBSET U ` SUBGOAL_TAC;
  ASM_MESON_TAC[DELETE_SUBSET;SUBSET_TRANS];
  DISCH_ALL_TAC;
  REWR 0;
  ALL_TAC; (* oi2 *)
  COPY 6;
  USE 9 (REWRITE_RULE[IN]);
  USE 9 (MATCH_MP delete_inters);
  ASM_REWRITE_TAC[];
  USE 1 (REWRITE_RULE[topology]);
  TYPEL_THEN [`(INTERS (V DELETE u))`;`u`;`U`] (USE 1 o ISPECL);
  AND 1;
  AND 1;
  UND 11;
  DISCH_THEN MATCH_MP_TAC ;
  ASM_REWRITE_TAC[];
  UND 6;
  UND 2;
  REWRITE_TAC [SUBSET;IN];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let top_unions = prove_by_refinement(
  `!(U:(A->bool)->bool) V. topology_ U /\ (V SUBSET U) ==> U (UNIONS V)`,
  (* {{{ proof *)
  [
  MESON_TAC[topology];
  ]);;
  (* }}} *)

let top_inter = prove_by_refinement(
  `!(U:(A->bool)-> bool) A B. topology_ U /\ (U A) /\ (U B) ==> (U (A INTER B))`,
  (* {{{ proof *)
  [
  MESON_TAC[topology];
  ]);;
  (* }}} *)


(* open and closed balls in  metric spaces *)

let open_ball_nonempty = prove_by_refinement(
 `!(X:A->bool) d a r. (metric_space (X,d)) /\ (&.0 <. r) /\ (X a) ==>
    (a IN (open_ball(X,d) a r))`,
 (* {{{ proof *)
 [
 REWRITE_TAC[metric_space;IN_ELIM_THM;open_ball];
 DISCH_ALL_TAC;
 UNDISCH_FIND_THEN `( /\ )` (ASSUME_TAC o (SPECL [`a:A`;`a:A`;`a:A`]));
 ASM_MESON_TAC[];
 ]);;
 (* }}} *)

let open_ball_subset = prove_by_refinement(
 `!(X:A->bool) d a r. (open_ball (X,d) a r SUBSET X)`,
(* {{{ proof *)
 [
 REWRITE_TAC[SUBSET;open_ball;IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)

let open_ball_subspace = prove_by_refinement(
  `!(X:A->bool) Y d a r. (Y SUBSET X) ==>
    (open_ball(Y,d) a r SUBSET open_ball(X,d) a r)`,
(* {{{ proof *)
 [
 REWRITE_TAC[SUBSET;open_ball;IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)

let open_ball_empty = prove_by_refinement(
  `!(X:A->bool) d a r. ~(a IN X) ==> (EMPTY = open_ball (X,d) a r)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[open_ball];
  MATCH_MP_TAC EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM;EMPTY];
  ASM_MESON_TAC[IN];
  ]);;
  (* }}} *)

(*** Old proof modified by JRH to avoid GSPEC

let open_ball_intersect = prove_by_refinement(
  `!(X:A->bool) Y d a r. (Y SUBSET X) /\ (a IN Y) ==>
   (open_ball(Y,d) a r = (open_ball(X,d) a r INTER Y))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[SUBSET;IN;INTER;open_ball];
  REWRITE_TAC[GSPEC_THM];
  REWRITE_TAC[IN_ELIM_THM];
  REWRITE_TAC[GSPEC];
  DISCH_ALL_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  BETA_TAC;
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

***)

let open_ball_intersect = prove_by_refinement(
  `!(X:A->bool) Y d a r. (Y SUBSET X) /\ (a IN Y) ==>
   (open_ball(Y,d) a r = (open_ball(X,d) a r INTER Y))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[SUBSET;IN;INTER;open_ball];
  REWRITE_TAC[EXTENSION; IN_ELIM_THM];
  MESON_TAC[]
  ]);;
  (* }}} *)

let open_ball_center = prove_by_refinement(
 `!(X:A->bool) d a b r. (metric_space (X,d)) /\
      (a IN (open_ball (X,d) b r)) ==>
     (?r'. (&.0 <. r') /\
         ((open_ball(X,d) a r') SUBSET (open_ball(X,d) b r)))`,
(* {{{ proof *)
 [
 REWRITE_TAC[metric_space;open_ball];
 DISCH_ALL_TAC;
 EXISTS_TAC `r -. (d (a:A) (b:A))`;
 REWRITE_TAC[SUBSET;IN_ELIM_THM];
 UNDISCH_FIND_TAC `(IN)`;
 REWRITE_TAC[IN_ELIM_THM];
 DISCH_ALL_TAC;
 CONJ_TAC;
 REWRITE_TAC[REAL_ARITH `(&.0 < r -. s)= (s <. r)`];
 ASM_MESON_TAC[];
 GEN_TAC;
 ASM_REWRITE_TAC[];
 REWRITE_TAC[REAL_ARITH `(u <. v-.w) <=> (w +. u <. v)`];
 DISCH_ALL_TAC;
 ASM_REWRITE_TAC[];
 UNDISCH_FIND_TAC `(!)`;
 DISCH_THEN (fun t-> (MP_TAC (SPECL [`b:A`;`a:A`;`x:A`] t)));
 ASM_REWRITE_TAC[];
 ASM_MESON_TAC[REAL_LET_TRANS;REAL_LTE_TRANS];
 ]);;
(* }}} *)

let open_ball_nonempty_center = prove_by_refinement(
 `!(X:A->bool) d a r. (metric_space(X,d)) ==>
    ((a IN (open_ball(X,d) a r)) =
    ~(open_ball(X,d) a r = EMPTY))`,
(* {{{ proof *)
 [
 REWRITE_TAC[metric_space];
 DISCH_ALL_TAC;
 REWRITE_TAC[open_ball];
 REWRITE_TAC[REWRITE_CONV[IN_ELIM_THM] `(a:A) IN { y | X a /\ X y /\ (d a y <. r)}`];
 REWRITE_TAC[EXTENSION];
 REWRITE_TAC[IN_ELIM_THM;NOT_IN_EMPTY;NOT_FORALL_THM];
 EQ_TAC;
 MESON_TAC[];
 DISCH_THEN CHOOSE_TAC;
 ASM_REWRITE_TAC[];
 FIRST_ASSUM  (fun t -> MP_TAC (SPECL [`a:A`;`x:A`;`a:A`] t));
 UNDISCH_FIND_THEN `(+.)`  (fun t -> MP_TAC (SPECL [`a:A`;`a:A`;`a:A`] t));
 ASM_MESON_TAC[REAL_LET_TRANS;REAL_LTE_TRANS];
 ]);;
(* }}} *)

(*** Old proof modified by JRH to remove apparent misnamed quantifier

let open_ball_neg_radius = prove_by_refinement(
  `!(X:A->bool) d a r. metric_space(X,d) /\ (r <. (&.0)) ==>
    (EMPTY = open_ball(X,d) a r)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[open_ball;metric_space];
  DISCH_ALL_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[EMPTY;IN_ELIM_THM];
  FIRST_ASSUM  (fun t -> MP_TAC (SPECL [`a:A`;`x:A`;`a:A`] t));
  ASSUME_TAC (REAL_ARITH `!u r. ~((dd <. r) /\ (r <. (&.0)) /\ (&.0 <=. dd))`);
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

***)

let open_ball_neg_radius = prove_by_refinement(
  `!(X:A->bool) d a r. metric_space(X,d) /\ (r <. (&.0)) ==>
    (EMPTY = open_ball(X,d) a r)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[open_ball;metric_space];
  DISCH_ALL_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[EMPTY;IN_ELIM_THM];
  FIRST_ASSUM  (fun t -> MP_TAC (SPECL [`a:A`;`x:A`;`a:A`] t));
  ASSUME_TAC (REAL_ARITH `!d r. ~((d <. r) /\ (r <. (&.0)) /\ (&.0 <=. d))`);
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)


let open_ball_nest = prove_by_refinement(
 `!(X:A->bool) d a r r'. (r <. r') ==>
   ((open_ball (X,d) a r) SUBSET (open_ball(X,d) a r'))`,
(* {{{ proof *)
  [
  REWRITE_TAC[SUBSET;open_ball;IN_ELIM_THM];
  MESON_TAC[REAL_ARITH `(r<. r') /\ (a <. r) ==> (a <. r')`];
  ]);;
(* }}} *)

(* intersection of open balls contains an open ball *)
let open_ball_inter = prove_by_refinement(
 `!(X:A->bool) d a b c r r'. (metric_space (X,d)) /\ (X a) /\ (X b) /\
  (c IN (open_ball(X,d) a r INTER (open_ball(X,d) b r'))) ==>
  (?r''. (&.0 <. r'') /\ (open_ball(X,d) c r'') SUBSET
    (open_ball(X,d) a r INTER (open_ball(X,d) b r')))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
    UNDISCH_FIND_THEN `(INTER)` (fun t-> MP_TAC (REWRITE_RULE[IN_INTER] t) THEN DISCH_ALL_TAC);
  SUBGOAL_TAC `(X:A->bool) (c:A)`;
  ASM_MESON_TAC[SUBSET;open_ball_subset;IN];
  DISCH_TAC;
  MP_TAC (SPECL[`X:A->bool`;`d:A->A->real`;`c:A`;`b:A`;`r':real`] open_ball_center) THEN (ASM_REWRITE_TAC[]) THEN (DISCH_THEN CHOOSE_TAC);
  MP_TAC (SPECL[`X:A->bool`;`d:A->A->real`;`c:A`;`a:A`;`r:real`] open_ball_center) THEN (ASM_REWRITE_TAC[]) THEN (DISCH_THEN CHOOSE_TAC);
  REWRITE_TAC[SUBSET_INTER];
  EXISTS_TAC `(if (r'' <. r''') then (r'') else (r'''))`;
  COND_CASES_TAC;
  ASM_MESON_TAC[open_ball_nest;SUBSET_TRANS];
  IMP_RES_THEN DISJ_CASES_TAC (REAL_ARITH `(~(r'' <. r''')) ==> ((r''' <. r'') \/ (r'''=r''))`);
  ASM_MESON_TAC[open_ball_nest;SUBSET_TRANS];
  ASM_MESON_TAC[];
  ]);;
(* }}} *)

let BALL_DIST = prove_by_refinement(
  `!X d x y (z:A) r. metric_space(X,d) /\ open_ball(X,d) z r x /\
  open_ball(X,d) z r y ==> d x y <. (&.2 * r)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[metric_space;open_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  USE 0 (SPECL [`x:A`;`z:A`;`y:A`]);
  REWR 0;
  UND 0 THEN DISCH_ALL_TAC;
  UND 9;
  UND 6;
  ASM_REWRITE_TAC[];
  UND 3;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let BALL_DIST_CLOSED = prove_by_refinement(
  `!X d x y (z:A) r. metric_space(X,d) /\ closed_ball(X,d) z r x /\
  closed_ball(X,d) z r y ==> d x y <=. (&.2 * r)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[metric_space;closed_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  USE 0 (SPECL [`x:A`;`z:A`;`y:A`]);
  REWR 0;
  UND 0 THEN DISCH_ALL_TAC;
  UND 9;
  UND 6;
  ASM_REWRITE_TAC[];
  UND 3;
  REAL_ARITH_TAC;
  ]);;

  (* }}} *)


let open_ball_sub_closed = prove_by_refinement(
  `!X d (x:A) r.
     (open_ball(X,d) x r SUBSET (closed_ball(X,d) x r))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  REWRITE_TAC[SUBSET;IN;open_ball;closed_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 2;
  REAL_ARITH_TAC;
  ]);;

  (* }}} *)

let ball_symm = prove_by_refinement(
  `!X d (x:A) y r. metric_space(X,d) /\ (X x) /\ (X y) ==>
       (open_ball(X,d) x r y = open_ball(X,d) y r x)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC [open_ball;IN_ELIM_THM'];
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC [metric_space_symm];
  ]);;
  (* }}} *)

let ball_subset_ball = prove_by_refinement(
  `!X d (x:A) z r. metric_space(X,d) /\
       (open_ball(X,d) x r z ) ==>
    (open_ball(X,d) z r SUBSET (open_ball(X,d) x (&.2 * r)))`,
  (* {{{ proof *)
  [
    DISCH_ALL_TAC;
    REWRITE_TAC[SUBSET;IN];
    DISCH_ALL_TAC;
    REWRITE_TAC[open_ball;IN_ELIM_THM'];
    TYPE_THEN `X z /\ X x' /\ X x` SUBGOAL_TAC ;
    UND 2;
    UND 1;
    REWRITE_TAC[open_ball;IN_ELIM_THM'];
    MESON_TAC[];
    DISCH_ALL_TAC;
    TYPE_THEN `open_ball(X,d) z r x` SUBGOAL_TAC;
    ASM_MESON_TAC[ball_symm];
    ASM_MESON_TAC[BALL_DIST];
  ]);;
  (* }}} *)


(* top_of_metric *)

let top_of_metric_unions = prove_by_refinement(
 `!(X:A->bool) d. (metric_space (X,d)) ==>
    (X = UNIONS (top_of_metric (X,d)))`,
  (* {{{ proof *)
 [
 REPEAT GEN_TAC;
 DISCH_TAC;
 MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC;
 REWRITE_TAC[SUBSET];
 REWRITE_TAC[IN_UNIONS;top_of_metric];
 DISCH_ALL_TAC;
 EXISTS_TAC `open_ball(X,d) (x:A) (&.1)`;
 UNDISCH_TAC `(x:A) IN X` THEN (REWRITE_TAC[IN_ELIM_THM]);
 DISCH_ALL_TAC;
 CONJ_TAC;
 EXISTS_TAC `{(open_ball(X,d) (x:A) (&.1))}`;
 REWRITE_TAC[GSYM UNIONS_1;INSERT_SUBSET;EMPTY_SUBSET];
 REWRITE_TAC[open_balls;IN_ELIM_THM];
 MESON_TAC[];
 REWRITE_TAC[IN_ELIM_THM;open_ball];
 UNDISCH_FIND_TAC `(IN)`;
 ASM_REWRITE_TAC[IN];
 DISCH_TAC;
 ASM_REWRITE_TAC[];
 UNDISCH_FIND_TAC `metric_space`;
 REWRITE_TAC[metric_space];
 DISCH_THEN (fun t -> MP_TAC (ISPECL [`x:A`;`x:A`;`x:A`] t));
 ASM_MESON_TAC[REAL_ARITH `(&.0) <. (&.1)`];
 MATCH_MP_TAC UNIONS_SUBSET;
 GEN_TAC;
 REWRITE_TAC[top_of_metric;IN_ELIM_THM];
 DISCH_THEN CHOOSE_TAC;
 ASM_REWRITE_TAC[];
 MATCH_MP_TAC UNIONS_SUBSET;
 X_GEN_TAC `B:A->bool`;
 DISCH_TAC;
 SUBGOAL_TAC `(B:A->bool) IN open_balls (X,d)`;
 ASM SET_TAC[];
 REWRITE_TAC[open_balls;IN_ELIM_THM];
 DISCH_THEN (CHOOSE_THEN MP_TAC);
 DISCH_THEN (CHOOSE_THEN ASSUME_TAC);
 ASM_REWRITE_TAC[];
 REWRITE_TAC[open_ball;SUBSET;IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)

let top_of_metric_empty = prove_by_refinement(
 `!(X:A->bool) d.
   ( (top_of_metric (X,d)) EMPTY)`,
  (* {{{ proof  *)
 [
 REWRITE_TAC[top_of_metric];
 REPEAT GEN_TAC;
 REWRITE_TAC[IN_ELIM_THM];
 EXISTS_TAC `EMPTY:(A->bool)->bool`;
 REWRITE_TAC[UNIONS_0;EMPTY_SUBSET];
 ]);;
(* }}} *)

let top_of_metric_open = prove_by_refinement(
 `!(X:A->bool) d F.
    (F SUBSET (open_balls (X,d))) ==>
    ((UNIONS F) IN (top_of_metric(X,d)))`,
 (* {{{ proof *)
 [
 REWRITE_TAC[top_of_metric;IN_ELIM_THM];
 MESON_TAC[];
 ]);;
 (* }}} *)

let top_of_metric_open_balls = prove_by_refinement(
 `!(X:A->bool) d.
    (open_balls (X,d)) SUBSET (top_of_metric(X,d))`,
 (* {{{ proof *)
 [
 REWRITE_TAC[SUBSET];
 REWRITE_TAC[top_of_metric;IN_ELIM_THM];
 DISCH_ALL_TAC;
 EXISTS_TAC `{(x:A->bool)}`;
 ASM SET_TAC[];
 ]);;
  (* }}} *)

let open_ball_open = prove_by_refinement(
  `! (X:A->bool) d x r. (metric_space(X,d)) ==>
   (top_of_metric (X,d) (open_ball (X,d) x r)) `,
  (* {{{ proof *)
  [
    DISCH_ALL_TAC;
  TYPEL_THEN [`X`;`d`] (fun t-> ASSUME_TAC ( ISPECL t top_of_metric_open_balls));
  USE 1 (REWRITE_RULE[open_balls;SUBSET;IN_ELIM_THM']);
  ASM_MESON_TAC[IN];
  ]);;
  (* }}} *)

(* a set is open then every point contains a ball *)
let top_of_metric_nbd = prove_by_refinement(
 `!(X:A->bool) d A. (metric_space (X,d)) ==>
     ((top_of_metric (X,d) A) <=> ((A SUBSET X) /\
    (!a. (a IN A) ==>
    (?r. (&.0 <. r) /\ (open_ball(X,d) a r SUBSET A)))))`,
(* {{{ proof *)

 [
 (DISCH_ALL_TAC);
 EQ_TAC;
 REWRITE_TAC[top_of_metric;IN_ELIM_THM];
 DISCH_THEN (CHOOSE_THEN MP_TAC);
 DISCH_ALL_TAC;
 CONJ_TAC;
 IMP_RES_THEN ASSUME_TAC top_of_metric_unions;
 ASM_REWRITE_TAC[];
 IMP_RES_THEN ASSUME_TAC top_of_metric_open;
 ASM ONCE_REWRITE_TAC[];
 MATCH_MP_TAC UNIONS_UNIONS;
 ASM_MESON_TAC[SUBSET_TRANS;top_of_metric_open_balls];
 DISCH_ALL_TAC THEN (ASM_REWRITE_TAC[]);
 REWRITE_TAC[IN_UNIONS;UNIONS_SUBSET];
 UNDISCH_FIND_TAC `(IN)`;
 ASM_REWRITE_TAC[];
 REWRITE_TAC[IN_UNIONS];
 DISCH_THEN (CHOOSE_THEN ASSUME_TAC);
 SUBGOAL_TAC `(t IN open_balls (X:A->bool,d))`;
 ASM_MESON_TAC[SUBSET];
 REWRITE_TAC[open_balls;IN_ELIM_THM];
 REPEAT (DISCH_THEN (CHOOSE_THEN MP_TAC));
 DISCH_TAC;
 MP_TAC (SPECL[`(X:A->bool)`; `d:A->A->real`;`a:A`;`x:A`;`r:real`] open_ball_center);
 ASM_REWRITE_TAC[];
 SUBGOAL_TAC `(a:A) IN open_ball(X,d) x r`;
 ASM_MESON_TAC[];
 DISCH_TAC THEN (ASM_REWRITE_TAC[]);
 DISCH_THEN CHOOSE_TAC;
 EXISTS_TAC `r':real`;
 ASM_REWRITE_TAC[];
 (* to here *)
 SUBGOAL_TAC `!s. ((s:A->bool) IN F') ==> (s SUBSET (UNIONS F'))`;
 SET_TAC[];
 ASM_MESON_TAC[SUBSET_TRANS] ; (*second direction: *)
 DISCH_THEN (fun t -> ASSUME_TAC (CONJUNCT1 t) THEN MP_TAC (CONJUNCT2 t));
 DISCH_THEN (fun t -> MP_TAC (REWRITE_RULE[RIGHT_IMP_EXISTS_THM] t));
 REWRITE_TAC[SKOLEM_THM];
 DISCH_THEN CHOOSE_TAC;
 REWRITE_TAC[top_of_metric;IN_ELIM_THM];
 EXISTS_TAC `IMAGE (\b. (open_ball(X,d) b (r b))) (A:A->bool)`;
 CONJ_TAC;
 REWRITE_TAC[IMAGE;SUBSET];
 REWRITE_TAC[IN_ELIM_THM;open_balls];
 MESON_TAC[IN];
 REWRITE_TAC[IMAGE];
 GEN_REWRITE_TAC I [EXTENSION];
 X_GEN_TAC `a:A`;
 REWRITE_TAC[IN_UNIONS];
 REWRITE_TAC[IN_ELIM_THM];
 EQ_TAC;
 DISCH_TAC;
 EXISTS_TAC `open_ball (X,d) (a:A) (r a)`;
 CONJ_TAC;
 EXISTS_TAC `a:A`;
 ASM_REWRITE_TAC[];
 REWRITE_TAC[IN;open_ball];
 REWRITE_TAC[IN_ELIM_THM];
 ASM_MESON_TAC[metric_space_zero;IN;SUBSET];  (* last: *)
 DISCH_THEN (CHOOSE_THEN MP_TAC);
 DISCH_ALL_TAC;
 UNDISCH_FIND_TAC `(?)` ;
 DISCH_THEN (CHOOSE_THEN MP_TAC);
 DISCH_ALL_TAC;
 UNDISCH_FIND_TAC `(!)`;
 DISCH_THEN (fun t -> MP_TAC(SPEC `x:A` t));
 ASM_REWRITE_TAC[];
 DISCH_ALL_TAC;
 ASM_MESON_TAC[SUBSET;IN];
 ]);;

(* }}} *)

let top_of_metric_inter = prove_by_refinement(
 `!(X:A->bool) d. (metric_space (X,d)) ==>
   (!A B. (top_of_metric (X,d) A) /\ (top_of_metric (X,d) B) ==>
      (top_of_metric (X,d) (A INTER B)))`,
(* {{{ proof *)
 [
 DISCH_ALL_TAC;
 DISCH_ALL_TAC;
 IMP_RES_THEN ASSUME_TAC (SPECL [`X:A->bool`;`d:A->A->real`] top_of_metric_nbd);
 UNDISCH_TAC `(top_of_metric (X,d) (B:A->bool))`;
 UNDISCH_TAC `(top_of_metric (X,d) (A:A->bool))`;
 ASM_REWRITE_TAC[];
 DISCH_ALL_TAC;
 DISCH_ALL_TAC;
 CONJ_TAC;
 ASM SET_TAC[];
 DISCH_ALL_TAC;
 UNDISCH_FIND_THEN `(INTER)` (fun t-> (MP_TAC (REWRITE_RULE[IN_INTER]t)) THEN DISCH_ALL_TAC );
 UNDISCH_FIND_THEN `(IN)` (fun t-> ANTE_RES_THEN MP_TAC t);
 UNDISCH_FIND_THEN `(IN)` (fun t-> ANTE_RES_THEN MP_TAC t);
 DISCH_THEN CHOOSE_TAC;
 DISCH_THEN CHOOSE_TAC;
 EXISTS_TAC `if (r<. r') then r else r'`;
 COND_CASES_TAC;
 ASM_REWRITE_TAC[SUBSET_INTER];
 ASM_MESON_TAC[open_ball_nest;SUBSET_TRANS];
 MP_TAC (ARITH_RULE `~(r<.r') ==> ((r'<. r) \/ (r'=r))`) THEN (ASM_REWRITE_TAC[]);
 DISCH_THEN DISJ_CASES_TAC;
 ASM_REWRITE_TAC[SUBSET_INTER];
 ASM_MESON_TAC[open_ball_nest;SUBSET_TRANS];
 ASM_MESON_TAC[SUBSET_INTER];
 ]);;
(* }}} *)

let top_of_metric_union = prove_by_refinement(
  `!(X:A->bool) d. (metric_space(X,d)) ==>
   (!V. (V SUBSET top_of_metric(X,d)) ==>
      (top_of_metric(X,d) (UNIONS V)))`,
(* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MP_TAC (SPECL[`X:A->bool`;`d:A->A->real`] top_of_metric_nbd);
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  DISCH_ALL_TAC;
  CONJ_TAC;
  ASM_MESON_TAC[UNIONS_UNIONS;top_of_metric_unions];
  GEN_TAC;
  REWRITE_TAC[IN_UNIONS];
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  DISCH_ALL_TAC;
  SUBGOAL_TAC `(top_of_metric (X,d)) (t:A->bool)`;
  ASM_MESON_TAC[IN;SUBSET];
  MP_TAC (SPECL[`X:A->bool`;`d:A->A->real`] top_of_metric_nbd);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  UNDISCH_FIND_THEN `(!)` (fun t -> MP_TAC (SPEC `a:A` t));
  ASM_REWRITE_TAC[];
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `r:real`;
  ASM_REWRITE_TAC[];
  ASM SET_TAC[UNIONS];
  ]);;
(* }}} *)

let top_of_metric_top = prove_by_refinement(
 `!(X:A->bool) d. ( (metric_space (X,d))) ==>
    (topology_ (top_of_metric (X,d)))`,
(* {{{ proof *)
 [
 DISCH_ALL_TAC;
 REWRITE_TAC[topology];
 REPEAT GEN_TAC;
 ASM_SIMP_TAC[top_of_metric_empty;top_of_metric_inter;top_of_metric_union];
 ]);;
(* }}} *)

let closed_ball_closed = prove_by_refinement(
  `!X d (x:A) r. (metric_space (X,d)) ==>
     (closed_ (top_of_metric(X,d)) (closed_ball(X,d) x r))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  TYPE_THEN `X x`  ASM_CASES_TAC ;
  REWRITE_TAC[closed];
  ASM_SIMP_TAC [GSYM top_of_metric_unions];
  SUBCONJ_TAC;
  REWRITE_TAC[closed_ball;SUBSET;IN;IN_ELIM_THM'];
  MESON_TAC[];
  DISCH_ALL_TAC;
  REWRITE_TAC[open_DEF];
  COPY 0;
  USE 0 (MATCH_MP top_of_metric_top);
  ONCE_ASM_SIMP_TAC[open_nbd];
  GEN_TAC;
  TYPE_THEN `open_ball(X,d) x' (d x x' -. r)` EXISTS_TAC;
  TYPE_THEN `R = (d x x' -. r)` ABBREV_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `X x'` SUBGOAL_TAC;
  USE 5 (REWRITE_RULE[INR IN_DIFF]);
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  SUBCONJ_TAC;
  REWRITE_TAC[DIFF_SUBSET;open_ball_subset;INTER;EQ_EMPTY;IN_ELIM_THM'];
  X_GEN_TAC `y:A`;
  REWRITE_TAC[IN];
  ASM_REWRITE_TAC[open_ball;closed_ball];
  REWRITE_TAC[IN_ELIM_THM';GSYM CONJ_ASSOC];
  PROOF_BY_CONTR_TAC;
  USE 7 (REWRITE_RULE[]);
  AND 7;
  REWR 7;
  COPY 3;
  USE 3 (REWRITE_RULE[metric_space]);
  TYPEL_THEN [`x`;`y`;`x'`] (USE 3 o SPECL);
  REWR 3;
  ALL_TAC; (* "bb"; *)
  TYPE_THEN `d x' y = d y x'` SUBGOAL_TAC;
  TYPEL_THEN [`X`;`d`] (fun t-> MATCH_MP_TAC  (SPECL t metric_space_symm));
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  UND 7;
  UND 10;
  AND 3;
  AND 3;
  AND 3;
  UND 3;
  EXPAND_TAC "R";
  ALL_TAC; (* "cb" *)
  REAL_ARITH_TAC;
  ALL_TAC; (* "cbc" *)
  DISCH_TAC;
  ASM_SIMP_TAC [open_ball_open];
  MATCH_MP_TAC  (INR open_ball_nonempty);
  ASM_REWRITE_TAC[];
  EXPAND_TAC "R";
  PROOF_BY_CONTR_TAC;
  USE 8 (MATCH_MP (REAL_ARITH `~(&.0 < d x x' - r) ==> (d x x' <=. r)`));
  USE 5 (REWRITE_RULE[INR IN_DIFF;closed_ball;IN_ELIM_THM']);
  ASM_MESON_TAC[];
  TYPE_THEN `(closed_ball (X,d) x r) = EMPTY` SUBGOAL_TAC;
(**** Old step changed by JRH for modified set comprehensions
  ASM_REWRITE_TAC[closed_ball;EMPTY;GSPEC];
 ***)
  ASM_REWRITE_TAC[closed_ball;IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY];
  DISCH_THEN (REWRT_TAC);
  ALL_TAC; (* "cbc1" *)
  ASM_MESON_TAC[empty_closed;top_of_metric_top];
  ]);;
  (* }}} *)

let open_ball_nbd = prove_by_refinement(
  `!X d C x. ?e. (metric_space((X:A->bool),d)) /\ (C x) /\
    (top_of_metric (X,d) C) ==>
   ((&.0 < e) /\ (open_ball (X,d) x e SUBSET C))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  RIGHT_TAC "e";
  DISCH_ALL_TAC;
  USE 2 (REWRITE_RULE[top_of_metric;open_balls;IN_ELIM_THM';SUBSET;IN  ]);
  CHO 2;
  AND 2;
  ASM_REWRITE_TAC[];
  REWR 1;
  USE 1 (REWRITE_RULE[UNIONS;IN;IN_ELIM_THM'  ]);
  CHO 1;
  TYPE_THEN `u` (USE 3 o SPEC);
  REWR 3;
  CHO 3;
  CHO 3;
  REWR 1;
  TYPEL_THEN [`X`;`d`;`x`;`x'`;`r`] (fun t-> (ASSUME_TAC (ISPECL t open_ball_center)));
  USE 4 (REWRITE_RULE[IN ]);
  REWR 4;
  CHO 4;
  TYPE_THEN `r'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;UNIONS;IN;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  AND 4;
  USE 4 (REWRITE_RULE[SUBSET;IN;IN_ELIM_THM']);
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)


(* closure *)

let closure_closed = prove_by_refinement(
  `!U (A:A->bool). (topology_ U) /\ (A SUBSET (UNIONS U))  ==>
    (closed_ U (closure U A))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[closure];
  MATCH_MP_TAC closed_inter;
  REWRITE_TAC[IN_ELIM_THM];
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  MESON_TAC[];
  REWRITE_TAC[EMPTY_EXISTS];
  TYPE_THEN `UNIONS U` EXISTS_TAC;
  ASM_REWRITE_TAC[IN_ELIM_THM'];
  ASM_SIMP_TAC[closed_UNIV];
  ]);;
(* }}} *)

let subset_closure = prove_by_refinement(
  `!U (A:A->bool). (topology_ U) ==> (A SUBSET (closure U A))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[closure;SUBSET;IN_INTERS;IN_ELIM_THM];
  X_GEN_TAC `a:A`;
  MESON_TAC[IN];
  ]);;
  (* }}} *)

let closure_subset = prove_by_refinement(
  `!U (A:A->bool) B. (topology_ U) /\ (closed_ U B) /\ (A SUBSET B)
    ==> (closure U A SUBSET B)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[closure];
  DISCH_ALL_TAC;
  MATCH_MP_TAC INTERS_SUBSET;
  ASM_REWRITE_TAC[IN_ELIM_THM];
  ]);;
  (* }}} *)

let closure_self = prove_by_refinement(
  `!U (A:A->bool). (topology_ U) /\ (closed_ U A) ==>
     (closure U A = A)`,
  (* {{{ proof *)
 [
 DISCH_ALL_TAC;
 MATCH_MP_TAC SUBSET_ANTISYM;
 ASM_SIMP_TAC[subset_closure];
 ASM_SIMP_TAC[closure_subset;SUBSET_REFL];
 ]);;
 (* }}} *)

let closure_close = prove_by_refinement(
  `!U Z (A:A->bool). (topology_ U) /\ (Z SUBSET (UNIONS U)) ==>
     ((A = closure U Z) = ((Z SUBSET A) /\ (closed_ U A) /\
         (!B. (closed_ U B) /\ ((Z SUBSET B)) ==>
             (A SUBSET B))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_THEN (REWRT_TAC);
  ASM_SIMP_TAC[subset_closure;closure_closed;closure_subset];
  DISCH_ALL_TAC;
  REWRITE_TAC [closure];
  MATCH_MP_TAC (SUBSET_ANTISYM);
  CONJ_TAC;
  REWRITE_TAC[SUBSET_INTERS];
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[];
  MATCH_MP_TAC  INTERS_SUBSET;
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let closure_open = prove_by_refinement(
  `!U Z (A:A->bool). (topology_ U) /\ (Z SUBSET (UNIONS U)) ==>
     ((A = closure U Z) = ((Z SUBSET A) /\ (closed_ U A) /\
            (!B. (open_ U B) /\ ((B INTER Z) = EMPTY) ==>
             ((B INTER A) = EMPTY))))`,
  (* {{{ proof *)

  [
  REP_GEN_TAC;
  DISCH_TAC;
  ASM_SIMP_TAC[closure_close];
  MATCH_MP_TAC (TAUT `( A ==> (B <=> C)) ==>   (A /\ B <=> A /\ C)`);
  DISCH_TAC;
  MATCH_MP_TAC (TAUT `( A ==> (B <=> C)) ==>   (A /\ B <=> A /\ C)`);
  DISCH_TAC;
  EQ_TAC;
  DISCH_TAC;
  USE 2 (REWRITE_RULE[closed]);
  ASM_REWRITE_TAC[];
  GEN_TAC;
  USE 3 (SPEC `(UNIONS U) DIFF (B:A->bool)`);
  DISCH_ALL_TAC;
  UND 3;
  ASM_SIMP_TAC[open_closed];
  ASM_REWRITE_TAC[DIFF_SUBSET];
  DISCH_TAC;
  UND 5;
  UND 3;
  REWRITE_TAC[INTER_COMM];
  ALL_TAC; (* co1 *)
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  USE 3 (SPEC `(UNIONS U) DIFF (B:A->bool)`);
  UND 3;
  ASM_SIMP_TAC[closed_open];
  REWRITE_TAC[DIFF_INTER];
  ASM_SIMP_TAC[SUB_IMP_INTER];
  TYPE_THEN `A SUBSET (UNIONS U INTER A)` SUBGOAL_TAC;
  USE 2 (REWRITE_RULE[closed]);
  AND 2;
  UND 3;
  ALL_TAC; (* co2 *)
  SET_TAC[SUBSET;INTER];
  MESON_TAC [SUBSET_TRANS];
  ]);;

  (* }}} *)


(* induced topology *)

let image_top = prove_by_refinement(
 `!(U:(A->bool)->bool) (f:(A->bool)->(B->bool)).
    ((topology_ U) /\ (EMPTY = f EMPTY) /\
    (!a b. (a IN U) /\ (b IN U) ==>
      (((f a) INTER (f b)) = f (a INTER b))) /\
    (!V. (V SUBSET U) ==> (UNIONS (IMAGE f V) =f (UNIONS V) )))
    ==> (topology_ (IMAGE f U))`,
  (* {{{ proof *)

 [
 REWRITE_TAC[topology];
 DISCH_ALL_TAC;
 DISCH_ALL_TAC;
 CONJ_TAC;
 REWRITE_TAC[IMAGE;IN];
 REWRITE_TAC[IN_ELIM_THM];
 ASM_MESON_TAC[];
 CONJ_TAC;
 REWRITE_TAC[IMAGE;IN];
 REWRITE_TAC[IN_ELIM_THM];
 DISCH_ALL_TAC;
 REPEAT (UNDISCH_FIND_THEN `(?)` CHOOSE_TAC);
 ASM_REWRITE_TAC[];
 EXISTS_TAC `(x:A->bool) INTER x'`;
 ASM_SIMP_TAC[IN];
 DISCH_THEN (fun t-> MP_TAC (MATCH_MP SUBSET_PREIMAGE t));
 DISCH_THEN CHOOSE_TAC;
 ASM_REWRITE_TAC[];
 ASM_SIMP_TAC[];
 REWRITE_TAC[IMAGE;IN_ELIM_THM];
 EXISTS_TAC `UNIONS (Z:(A->bool)->bool)`;
 ASM_SIMP_TAC[IN];
 ]);;

(* }}} *)

let induced_top_support = prove_by_refinement(
 `!U (C:A->bool). (UNIONS (induced_top U C) = ((UNIONS U) INTER C))`,
  (* {{{ proof *)
 [
 REWRITE_TAC[UNIONS_INTER];
 DISCH_ALL_TAC;
 AP_TERM_TAC;
 REWRITE_TAC[induced_top];
 AP_THM_TAC;
 AP_TERM_TAC;
 MATCH_MP_TAC EQ_EXT THEN BETA_TAC;
 SET_TAC[];
 ]);;
(* }}} *)

let induced_top_top = prove_by_refinement(
  `!U (C:A->bool). (topology_ U) ==> (topology_ (induced_top U C))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_TAC;
  REWRITE_TAC[induced_top];
  MATCH_MP_TAC image_top;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  SET_TAC[];
  CONJ_TAC;
  SET_TAC[];
  REWRITE_TAC[UNIONS_INTER];
  DISCH_ALL_TAC;
  AP_TERM_TAC;
  AP_THM_TAC;
  AP_TERM_TAC;
  MATCH_MP_TAC EQ_EXT THEN BETA_TAC;
  SET_TAC[];
  ]);;
(* }}} *)

let induced_top_open = prove_by_refinement(
 `!U (C:A->bool) A. (topology_ U) ==> (induced_top U C A =
     (?B. (U B) /\ ((B INTER C) = A)))`,
  (* {{{ proof *)
 [
 DISCH_ALL_TAC;
 REWRITE_TAC[induced_top;IMAGE];
 REWRITE_TAC[IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)

let induced_trans = prove_by_refinement(
  `! U (A:A->bool) B. (topology_ U) /\ U A /\ (induced_top U A B) ==>
    (U B)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[induced_top;IMAGE;IN ;IN_ELIM_THM'  ];
  DISCH_ALL_TAC;
  CHO 2;
  ASM_MESON_TAC[top_inter];
  ]);;
  (* }}} *)

let induced_top_unions = prove_by_refinement(
  `!(U:(A->bool)->bool). (topology_ U) ==>
        ((induced_top U (UNIONS U)) = U)`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  ASM_SIMP_TAC[induced_top_open];
  EQ_TAC;
  DISCH_ALL_TAC;
  CHO 1;
  USE 0 (REWRITE_RULE[topology]);
  TYPE_THEN `B SUBSET (UNIONS U)` SUBGOAL_TAC;
  ASM_MESON_TAC[sub_union ];
  REWRITE_TAC[SUBSET_INTER_ABSORPTION];
  DISCH_TAC ;
  ASM_MESON_TAC[];
  DISCH_TAC ;
  TYPE_THEN `x` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `x SUBSET (UNIONS U)` SUBGOAL_TAC;
  ASM_MESON_TAC[sub_union ];
  REWRITE_TAC[SUBSET_INTER_ABSORPTION];
  ]);;

  (* }}} *)

(* induced metric *)

let gen = euclid_def `gen (X:(A->bool)->bool)
  = {A | ?Y. (Y SUBSET X) /\ (A = UNIONS Y)}`;;

let top_of_metric_gen = prove_by_refinement(
  `!(X:(A)->bool) d. gen (open_balls(X,d))= (top_of_metric(X,d))`,
(* {{{ proof *)
  [
  REWRITE_TAC[gen;top_of_metric];
  ]);;
(* }}} *)

let gen_subset = prove_by_refinement(
  `!U (V:(A->bool)->bool).  (U SUBSET V) /\
     (!A. (A IN V) ==> (?Y. (Y SUBSET U) /\ (A = UNIONS Y)))
    ==> (gen U = (gen V))`,
(* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[EXTENSION];
  GEN_TAC THEN EQ_TAC;
  REWRITE_TAC[IN_ELIM_THM;gen];
  DISCH_THEN CHOOSE_TAC;
  ASM_MESON_TAC[SUBSET_TRANS];
  REWRITE_TAC[IN_ELIM_THM;gen];
  DISCH_THEN CHOOSE_TAC;
  UNDISCH_FIND_THEN `(?)` (fun t-> MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM;SKOLEM_THM]t));
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `UNIONS (IMAGE (Y':(A->bool)->((A->bool)->bool)) (Y:(A->bool)->bool))`;
  CONJ_TAC;
  MATCH_MP_TAC UNIONS_SUBSET;
  REWRITE_TAC[IN_IMAGE];
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  ASM_MESON_TAC[IN;SUBSET];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[UNIONS_IMAGE_UNIONS];
  AP_TERM_TAC;
  REWRITE_TAC[GSYM IMAGE_o];
  REWRITE_TAC[EXTENSION];
  X_GEN_TAC `A:(A->bool)`;
  REWRITE_TAC[IN_IMAGE;o_THM];
  ASM_MESON_TAC[SUBSET;IN];
  ]);;
(* }}} *)

let gen_subspace = prove_by_refinement(
  `!(X:A->bool) Y d. (Y SUBSET X) /\ (metric_space(X,d)) ==>
     (induced_top (top_of_metric(X,d)) Y =
         gen (induced_top (open_balls(X,d)) Y))`,
(* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[induced_top];
  REWRITE_TAC[EXTENSION];
  X_GEN_TAC `B:A->bool`;
  REWRITE_TAC[IN_IMAGE];
  EQ_TAC;
  DISCH_THEN (X_CHOOSE_TAC `C:A->bool`);
  FIRST_ASSUM MP_TAC;
  REWRITE_TAC[top_of_metric];
  REWRITE_TAC[IN_ELIM_THM];
  DISCH_ALL_TAC;
  UNDISCH_FIND_TAC `(?)`;
  DISCH_THEN (CHOOSE_TAC);
  UNDISCH_FIND_TAC `(INTER)`;
  ASM_REWRITE_TAC[UNIONS_INTER];
  REWRITE_TAC[gen;IN_ELIM_THM];
  EXISTS_TAC `IMAGE ((INTER) Y) (F':(A->bool)->bool)`;
  CONJ_TAC;
  REWRITE_TAC[INTER_THM];
  MATCH_MP_TAC IMAGE_SUBSET;
  ASM_REWRITE_TAC[];
  REFL_TAC;
  REWRITE_TAC[gen;IN_ELIM_THM];
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  DISCH_ALL_TAC;
  IMP_RES_THEN MP_TAC SUBSET_PREIMAGE;
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `UNIONS (Z:(A->bool)->bool)`;
  CONJ_TAC;
  REWRITE_TAC[UNIONS_INTER];
  UNDISCH_FIND_THEN `(UNIONS)` (fun t -> REWRITE_TAC[t]);
  AP_TERM_TAC;
  UNDISCH_FIND_TAC `(SUBSET)`;
  REWRITE_TAC[INTER_THM];
  ASM_MESON_TAC[];
  REWRITE_TAC[top_of_metric;IN_ELIM_THM];
  ASM_MESON_TAC[];
  ]);;
(* }}} *)

let gen_induced = prove_by_refinement(
 `!(X:A->bool) Y d. (Y SUBSET X) /\ (metric_space (X,d)) ==>
    (gen (open_balls(Y,d)) = gen (induced_top (open_balls(X,d)) Y))`,
(* {{{ proof *)
 [
 DISCH_ALL_TAC;
 MATCH_MP_TAC gen_subset;
 CONJ_TAC;
 REWRITE_TAC[induced_top;SUBSET;open_balls];
 REWRITE_TAC [IN_IMAGE];
 X_GEN_TAC `A:(A->bool)`;
 REWRITE_TAC[IN_ELIM_THM];
 REPEAT (DISCH_THEN (CHOOSE_THEN MP_TAC));
 DISCH_TAC;
 ASM_REWRITE_TAC[];
 ASM_CASES_TAC `(Y:A->bool) (x:A)`;
 CONV_TAC (relabel_bound_conv);
 EXISTS_TAC `open_ball (X,d) (x:A) r`;
 CONJ_TAC;
 MATCH_MP_TAC open_ball_intersect;
 ASM_MESON_TAC[IN];
 MESON_TAC[];
 EXISTS_TAC `open_ball (X,d) (x:A) (--. (&.1))`;
 CONJ_TAC;
 ASM_MESON_TAC[IN;INTER_EMPTY;open_ball_empty;open_ball_neg_radius;REAL_ARITH `(--.(&.1) <. (&.0))`];
 MESON_TAC[];  (* end of first half *)
 REWRITE_TAC[induced_top;IN_IMAGE];
 GEN_TAC;
 DISCH_THEN (CHOOSE_THEN MP_TAC);
 NAME_CONFLICT_TAC;
 REWRITE_TAC[IN;open_balls];
 REWRITE_TAC[IN_ELIM_THM'];
 NAME_CONFLICT_TAC;
 DISCH_ALL_TAC;
 ASM_REWRITE_TAC[];
 FIRST_ASSUM (CHOOSE_THEN ASSUME_TAC);
 FIRST_ASSUM (CHOOSE_THEN ASSUME_TAC);
 SUBGOAL_TAC `!(a:A). (a IN x INTER Y) ==> (?s. ((&.0) <. s) /\ open_ball(Y,d) a s SUBSET (x INTER Y))`;
 DISCH_ALL_TAC;
 TYPEL_THEN [`X`;`d`;`a`;`x'`;`r`] (fun t -> (CLEAN_ASSUME_TAC (ISPECL t open_ball_center)));
 SUBGOAL_TAC `(a:A) IN open_ball(X,d) x' r`;
 ASM_MESON_TAC[IN_INTER];
 DISCH_THEN (fun t -> ANTE_RES_THEN (MP_TAC) t);
 DISCH_THEN (CHOOSE_TAC);
 EXISTS_TAC `r':real`;
 ASM_REWRITE_TAC[SUBSET_INTER;open_ball_subset];
 ASM_MESON_TAC[open_ball_subspace;SUBSET_TRANS];
 DISCH_THEN (fun t -> MP_TAC (REWRITE_RULE[RIGHT_IMP_EXISTS_THM;SKOLEM_THM] t));
 DISCH_THEN CHOOSE_TAC;
 EXISTS_TAC `IMAGE (\t. open_ball(Y,d) t (s t) ) ((x:A->bool) INTER Y)`;
 REWRITE_TAC[SUBSET_INTER];
 CONJ_TAC;
 REWRITE_TAC[SUBSET;IN_ELIM_THM'];
 REWRITE_TAC[IN_IMAGE];
 GEN_TAC;
 MESON_TAC[];
 MATCH_MP_TAC SUBSET_ANTISYM;
 CONJ_TAC;
 REWRITE_TAC[SUBSET];
 GEN_TAC;
 REWRITE_TAC[IN_UNIONS];
 DISCH_TAC;
 EXISTS_TAC `open_ball (Y,d) (x'':A) (s x'')`;
 REWRITE_TAC[IN_IMAGE];
 CONJ_TAC;
 NAME_CONFLICT_TAC;
 EXISTS_TAC `x'':A`;
 ASM_REWRITE_TAC[];
 MATCH_MP_TAC open_ball_nonempty;
 ASM_SIMP_TAC[metric_subspace];
 ASM_MESON_TAC[IN_INTER;IN;metric_subspace];
 MATCH_MP_TAC UNIONS_SUBSET;
 GEN_TAC;
 REWRITE_TAC[IN_IMAGE];
 DISCH_THEN CHOOSE_TAC;
 ASM_MESON_TAC[];
 ]);;
(* }}} *)

let top_of_metric_induced = prove_by_refinement(
  `!(X:A->bool) Y d. (Y SUBSET X) /\ (metric_space(X,d)) ==>
    (induced_top (top_of_metric(X,d)) Y = (top_of_metric(Y,d)))`,
(* {{{ proof *)
  [
  SIMP_TAC[gen_subspace];
  REPEAT GEN_TAC;
  REWRITE_TAC[GSYM top_of_metric_gen];
  MESON_TAC[gen_induced];
  ]);;
(* }}} *)

(* ------------------------------------------------------------------ *)
(* Continuity *)
(* ------------------------------------------------------------------ *)


let continuous = euclid_def `continuous (f:A->B) U V <=> !v.
  (v IN V) ==> (preimage (UNIONS U) f v) IN U`;;

let metric_continuous_pt = euclid_def
  `metric_continuous_pt (f:A->B) (X,dX) ((Y:B->bool),dY) x =
  !epsilon. ?delta. (((&.0) < epsilon) ==> ((&.0) <. delta) /\
    (!y. ((x IN X) /\ (y IN X) /\ (dX x y) <. delta) ==>
     (dY (f x) (f y) <. epsilon)))`;;

let metric_continuous = euclid_def
  `metric_continuous (f:A->B) (X,dX) (Y,dY) <=> !x.
    metric_continuous_pt f (X,dX) (Y,dY) x`;;

let metric_continuous_pt_domain = prove_by_refinement(`!f X dX Y dY x .
   ~(x IN X) ==> (metric_continuous_pt (f:A->B) (X,dX) (Y,dY) x)`,
  (* {{{ proof *)

 [
 REWRITE_TAC[metric_continuous_pt];
 MESON_TAC[];
 ]);;

 (* }}} *)

let metric_continuous_continuous = prove_by_refinement(
  `!f X Y dX dY. (IMAGE f X SUBSET Y) /\ (metric_space(X,dX)) /\ (metric_space(Y,dY))
    ==>
   (continuous (f:A->B) (top_of_metric(X,dX)) (top_of_metric(Y,dY))
   <=> (metric_continuous f (X,dX) (Y,dY)))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  EQ_TAC;
  REWRITE_TAC[continuous;metric_continuous];
  DISCH_TAC;
  GEN_TAC;
  ASM_CASES_TAC `(x:A) IN X` THENL[ALL_TAC;ASM_SIMP_TAC[metric_continuous_pt_domain]];
  REWRITE_TAC[metric_continuous_pt];
  GEN_TAC;
  SUBGOAL_TAC `(open_ball (Y,dY) ((f:A->B) x) epsilon) IN (top_of_metric(Y,dY))`;
  MATCH_MP_TAC (prove_by_refinement(`!(x:A) B. (?A. (x IN A /\ A SUBSET B)) ==> (x IN B)`,[SET_TAC[]]));
  EXISTS_TAC `open_balls((Y:B->bool),dY)`;
  REWRITE_TAC[top_of_metric_open_balls];
  REWRITE_TAC[open_balls;IN_ELIM_THM'];
  MESON_TAC[];
  DISCH_THEN (ANTE_RES_THEN ASSUME_TAC);
  REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM];
  DISCH_TAC;
  SUBGOAL_TAC `(x:A) IN preimage (UNIONS (top_of_metric (X,dX))) f (open_ball (Y,dY) ((f:A->B) x) epsilon)`;
  REWRITE_TAC[in_preimage];
  SUBGOAL_TAC `(Y:B->bool) ((f:A->B) x )`;
  UNDISCH_FIND_TAC `IMAGE`;
  UNDISCH_TAC `(x:A) IN X`;
  REWRITE_TAC[SUBSET;IMAGE];
  REWRITE_TAC[IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[IN];
  MESON_TAC[];
  ASM_MESON_TAC[top_of_metric_unions;open_ball_nonempty];
  ABBREV_TAC `B = preimage (UNIONS (top_of_metric (X,dX))) (f:A->B) (open_ball (Y,dY) (f x) epsilon)`;
  DISCH_TAC;
  SUBGOAL_TAC `?r. (&.0 <. r) /\ (open_ball(X,dX) (x:A) r SUBSET B)`;
  ASSUME_TAC top_of_metric_nbd;
  ASM_MESON_TAC[IN];
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `r:real`;
  ASM_REWRITE_TAC[];
  GEN_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_TAC `y:A IN B`;
  MATCH_MP_TAC (prove_by_refinement(`!(x:A) B. (?A. (x IN A /\ A SUBSET B)) ==> (x IN B)`,[SET_TAC[]]));
  EXISTS_TAC `open_ball(X,dX) (x:A) r`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  ASM_MESON_TAC[IN];
  UNDISCH_FIND_TAC `preimage`;
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  REWRITE_TAC[in_preimage];
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  MESON_TAC[]; (* first half done *)
  REWRITE_TAC[metric_continuous];
  DISCH_TAC;
  REWRITE_TAC[continuous];
  GEN_TAC;
  DISCH_TAC;
  REWRITE_TAC[IN];
  ASM_SIMP_TAC[top_of_metric_nbd];
  ASM_SIMP_TAC[GSYM top_of_metric_unions];
  CONJ_TAC;
  REWRITE_TAC[SUBSET;in_preimage];
  MESON_TAC[];
  GEN_TAC;
  DISCH_THEN (fun t -> ASSUME_TAC t THEN (MP_TAC (REWRITE_RULE[in_preimage] t)));
  DISCH_ALL_TAC;
  SUBGOAL_TAC `?eps. (&.0 <. eps) /\ (open_ball(Y,dY) ((f:A->B) a) eps SUBSET v)`;
  UNDISCH_FIND_TAC `v IN top_of_metric (Y,dY)`;
  REWRITE_TAC[IN];
  ASM_SIMP_TAC[top_of_metric_nbd];
  DISCH_THEN CHOOSE_TAC;
  FIRST_ASSUM (fun t -> MP_TAC (SPEC `a:A` t));
  REWRITE_TAC[metric_continuous_pt];
  DISCH_THEN (fun t-> MP_TAC (SPEC `eps:real` t));
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  EXISTS_TAC `delta:real`;
  ASM_REWRITE_TAC[SUBSET];
  REWRITE_TAC[in_preimage;open_ball];
  REWRITE_TAC[IN_ELIM_THM'];
  X_GEN_TAC `y:A`;
  DISCH_ALL_TAC;
  CONJ_TAC THENL [(ASM_REWRITE_TAC[IN]);ALL_TAC];
  FIRST_ASSUM (fun t -> (MP_TAC (SPEC `y:A` t)));
  ASM_REWRITE_TAC[IN];
  UNDISCH_FIND_TAC `open_ball`;
  REWRITE_TAC[open_ball];
  DISCH_THEN (fun t  -> (MP_TAC (CONJUNCT2 t)));
  REWRITE_TAC[SUBSET];
  DISCH_THEN (fun t-> (MP_TAC (SPEC `(f:A->B) y` t)));
  ASM_REWRITE_TAC[IN_ELIM_THM'];
  SUBGOAL_TAC `!x. (X x) ==> (Y ((f:A->B) x))`;
  UNDISCH_FIND_TAC `IMAGE`;
  REWRITE_TAC[SUBSET;IN_IMAGE];
  NAME_CONFLICT_TAC;
  ASM_MESON_TAC[IN];
  ASM_MESON_TAC[IN];
  ]);;
  (* }}} *)

let continuous_induced = prove_by_refinement(
  `!(f:A->B) U V A. (topology_ V) /\ (continuous f U V) /\ (V A) ==>
       (continuous f U (induced_top V A)) `,
  (* {{{ proof *)
  [
  REWRITE_TAC[continuous;induced_top;IN_IMAGE;Q_ELIM_THM''  ];
  ASM_MESON_TAC[top_inter;IN ];
  ]);;
  (* }}} *)

let metric_cont = prove_by_refinement(
  `!U X d f. (metric_space(X,d)) /\ (topology_ U) ==>
    ((continuous (f:A->B) U (top_of_metric(X,d))) =
      (!(x:B) r. U (preimage (UNIONS U) f (open_ball (X,d) x r))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  USE 2 (REWRITE_RULE[continuous;IN]);
  UND 2 THEN (DISCH_THEN MATCH_MP_TAC );
  ASM_MESON_TAC [open_ball_open];
  REWRITE_TAC[continuous;IN];
  DISCH_ALL_TAC;
  REWRITE_TAC[top_of_metric;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  CHO 3;
  AND 3;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[preimage_unions];
  IMATCH_MP_TAC  top_unions ;
  ASM_REWRITE_TAC[IMAGE;SUBSET;IN;IN_ELIM_THM' ];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[Q_ELIM_THM'];
  USE 4 (REWRITE_RULE[SUBSET;IN]);
  DISCH_ALL_TAC;
  TYPE_THEN `x'` (USE 4 o SPEC);
  REWR 4;
  USE 4 (REWRITE_RULE[open_balls;IN_ELIM_THM' ]);
  CHO 4;
  CHO 4;
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let continuous_sum = prove_by_refinement(
  `!U (f:A->(num->real)) g n. (topology_ U) /\
   (continuous f U (top_of_metric(euclid n,d_euclid))) /\
   (continuous g U (top_of_metric(euclid n,d_euclid))) /\
   (IMAGE f (UNIONS U) SUBSET (euclid n)) /\
   (IMAGE g (UNIONS U) SUBSET (euclid n)) ==>
   (continuous (\t. (f t + g t))  U (top_of_metric(euclid n,d_euclid)))`,
  (* {{{ proof *)
  [
  ASSUME_TAC metric_euclid;
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[metric_cont];
  DISCH_ALL_TAC;
  ONCE_ASM_SIMP_TAC[open_nbd];
  X_GEN_TAC `t:A`;
  RIGHT_TAC "B";
  DISCH_ALL_TAC;
  USE 6 (REWRITE_RULE[REWRITE_RULE[IN] in_preimage]);
  USE 2 (REWRITE_RULE[continuous]);
  USE 3 (REWRITE_RULE[continuous]);
  AND 6;
  TYPE_THEN `n` (USE 0 o SPEC);
  COPY 0;
  JOIN 8 6;
  USE 6 (MATCH_MP (REWRITE_RULE[IN] open_ball_center));
  CHO 6;
  AND 6;
  TYPE_THEN `open_ball(euclid n,d_euclid) (f t) (r'/(&.2))` (USE 2 o SPEC);
  TYPE_THEN `open_ball(euclid n,d_euclid) (g t) (r'/(&.2))` (USE 3 o SPEC);
  UND 3;
  UND 2;
  REWRITE_TAC[IN];
  ASM_SIMP_TAC[open_ball_open];
  DISCH_ALL_TAC;
  TYPE_THEN `B = (preimage (UNIONS U) f (open_ball (euclid n,d_euclid) (f t) (r' / &2))) INTER (preimage (UNIONS U) g (open_ball (euclid n,d_euclid) (g t) (r' / &2)))` ABBREV_TAC ;
  TYPE_THEN `B` EXISTS_TAC;
  CONJ_TAC;
  (* cs1 *)
  USE 6 (MATCH_MP preimage_subset );
  TYPEL_THEN [`(\t. euclid_plus (f t) (g t))`;`UNIONS U`] (USE 6 o ISPECL);
  UND 6;
  IMATCH_MP_TAC  (prove_by_refinement(`!D B C. ((B:A->bool) SUBSET D) ==> ((D SUBSET C) ==> (B SUBSET C))`,[MESON_TAC [SUBSET_TRANS]]));
  REWRITE_TAC[subset_preimage];
  CONJ_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM'];
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;in_preimage;IN ;IN_ELIM_THM'  ];
  ASM_MESON_TAC[];
  REWRITE_TAC[IMAGE;SUBSET;IN;IN_ELIM_THM'];
  REWRITE_TAC[Q_ELIM_THM'];
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;in_preimage;IN ;IN_ELIM_THM'  ];
  REWRITE_TAC[open_ball;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[euclid_add_closure];
  TYPE_THEN `d_euclid (f t + (g t)) (f x' + g x') <=. (d_euclid (f t + (g t)) (f x' + g t)) + (d_euclid (f x' + g t) (f x' + g x'))` SUBGOAL_TAC;
  TYPEL_THEN [`euclid n`;`d_euclid`] (fun t-> ASSUME_TAC (ISPECL t metric_space_triangle));
  REWR 17;
  UND 17 THEN DISCH_THEN IMATCH_MP_TAC  ;
  ASM_SIMP_TAC[euclid_add_closure];
  IMATCH_MP_TAC  (REAL_ARITH `b + C < d ==> (a <= b + C ==> (a < d))`);
  (* cs2 *)
  IMATCH_MP_TAC real_half_LT;
  CONJ_TAC;
  ASM_MESON_TAC  [euclid_add_closure;SPEC `n:num` metric_translate];
  ASM_MESON_TAC[euclid_add_closure;metric_translate_LEFT];
  CONJ_TAC;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;in_preimage ;IN_ELIM_THM];
  ASM_REWRITE_TAC[IN];
  UND 4;
  UND 5;
  REWRITE_TAC[SUBSET;IN;IN_IMAGE ;IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[Q_ELIM_THM''];
  USE 8 (ONCE_REWRITE_RULE [GSYM REAL_LT_HALF1]);
  ASM_MESON_TAC[REWRITE_RULE[IN] open_ball_nonempty];
  EXPAND_TAC "B";
  IMATCH_MP_TAC  top_inter;
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Cauchy sequences and completeness *)
(* ------------------------------------------------------------------ *)


let sequence = euclid_def
  `sequence X (f:num->A) <=> (IMAGE f UNIV) SUBSET X`;;

let converge = euclid_def
  `converge (X,d) (f:num -> A) <=> (?x. (x IN (X:A->bool)) /\
   (!eps. ?n. (&.0 <. eps) ==>
        (!i. (n <=| i) ==> (d x (f i) <. eps))))`;;

let cauchy_seq = euclid_def
  `cauchy_seq (X,d) (f:num->A) <=> (sequence X f) /\
    (!eps. ?n. !i j. (&.0 <. eps) /\
        (n <= i) /\ (n <= j) ==> (d (f i) (f j) <. eps))`;;

let complete = euclid_def
  `complete (X,d) <=> !(f:num->A). cauchy_seq (X,d) f ==>
    converge (X,d) f`;;

let converge_cauchy = prove_by_refinement(
  `!X d f. metric_space(X,d) /\ (sequence X f) /\ (converge((X:A->bool),d) f)
    ==> cauchy_seq(X,d) f`,
  (* {{{ proof *)

  [
  REWRITE_TAC[converge;metric_space];
  DISCH_ALL_TAC;
  REWRITE_TAC[cauchy_seq];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM CHOOSE_TAC;
  GEN_TAC;
  UNDISCH_FIND_TAC `(IN)`;
  DISCH_ALL_TAC;
  FIRST_ASSUM (fun t-> MP_TAC (SPEC `eps/(&.2)` t));
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `n:num`;
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_TAC ` (&.0 <. (eps/(&.2)))`;
  MATCH_MP_TAC REAL_LT_DIV;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_THEN (ANTE_RES_THEN ASSUME_TAC);
  UNDISCH_TAC `n <=| i`;
  DISCH_THEN (ANTE_RES_THEN ASSUME_TAC);
  UNDISCH_TAC `n <=| j`;
  DISCH_THEN (ANTE_RES_THEN ASSUME_TAC);
  FIRST_ASSUM (fun t-> MP_TAC (SPECL [`(f:num->A) i`;`x:A`;`(f:num->A) j`] t));
  UNDISCH_FIND_TAC `sequence`;
  REWRITE_TAC[sequence;SUBSET;IN_IMAGE;IN_UNIV];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[IN];
  DISCH_TAC;
  SUBGOAL_TAC `X ((f:num->A) i) /\ X x /\ X (f j)`;
  ASM_MESON_TAC[IN];
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  DISCH_ALL_TAC;
  ASM_MESON_TAC[REAL_LET_TRANS;REAL_LT_ADD2;REAL_HALF_DOUBLE];
  ]);;

  (* }}} *)


(* relate the metric space version to the real numbers version *)
let cauchy_seq_cauchy = prove_by_refinement(
  `!f. (cauchy_seq(euclid 1,d_euclid) f) ==> (cauchy (\x. (f x 0)))`,
  (* {{{ proof *)
  [
  GEN_TAC;
  REWRITE_TAC[cauchy_seq;cauchy;sequence;SUBSET;IN_IMAGE;IN_UNIV];
  REWRITE_TAC[IN];
  NAME_CONFLICT_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  DISCH_TAC;
  FIRST_ASSUM (fun t -> MP_TAC (SPEC `e:real` t));
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `n:num`;
  REPEAT GEN_TAC;
  REWRITE_TAC[ARITH_RULE `a >=| b <=> b <=| a`];
  SUBGOAL_TAC `euclid 1 (f (m:num)) /\ euclid 1 (f (n':num))`;
  ASM_MESON_TAC[];
  ASM_MESON_TAC[euclid1_abs];
  ]);;
  (* }}} *)

(* a variant of SEQ_CAUCHY *)
let complete_real = prove_by_refinement(
  `complete (euclid 1,d_euclid)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[complete;converge];
  GEN_TAC;
  DISCH_THEN (fun t-> ASSUME_TAC t THEN MP_TAC t);
  DISCH_THEN (fun t -> MP_TAC (MATCH_MP cauchy_seq_cauchy t));
  REWRITE_TAC[SEQ_CAUCHY;SEQ_LIM;tends_num_real;SEQ_TENDS];
  ABBREV_TAC `z = lim (\x. f x 0)`;
  REWRITE_TAC[MR1_DEF];
  DISCH_TAC;
  ABBREV_TAC `c = \j. (if (j=0) then (z:real) else (&.0))`;
  EXISTS_TAC `(c:num->real)`;
  SUBGOAL_TAC `c IN (euclid 1)`;
  REWRITE_TAC[IN;euclid];
  EXPAND_TAC "c";
  GEN_TAC;
  COND_CASES_TAC;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  ARITH_TAC;
  DISCH_TAC;
  ASM_REWRITE_TAC[];
  GEN_TAC;
  REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM];
  DISCH_TAC;
  FIRST_ASSUM (fun t-> (MP_TAC (SPEC `eps:real` t)));
  FIRST_ASSUM (fun t-> REWRITE_TAC[t]);
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `N:num`;
  GEN_TAC;
  SUBGOAL_TAC `euclid 1 (f (i:num))`;
  UNDISCH_FIND_TAC `cauchy_seq`;
  REWRITE_TAC[cauchy_seq;sequence;SUBSET;IN_IMAGE;IN_UNIV];
  DISCH_THEN (fun t-> MP_TAC (CONJUNCT1 t));
  REWRITE_TAC[IN];
  MESON_TAC[];
  UNDISCH_FIND_TAC `(IN)`;
  REWRITE_TAC[IN];
  SIMP_TAC[euclid1_abs];
  DISCH_ALL_TAC;
  EXPAND_TAC "c";
  COND_CASES_TAC;
  ASM_MESON_TAC[ARITH_RULE `n >=| N <=> N <= n`];
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let sequence_in = prove_by_refinement(
  `!X (f:num->A) i. sequence X f ==> X (f i)`,
  (* {{{ proof *)

  [
  REPEAT GEN_TAC;
  REWRITE_TAC[sequence;SUBSET;IN_IMAGE;IN_UNIV];
  REWRITE_TAC[IN];
  MESON_TAC[];
  ]);;

  (* }}} *)

let proj_cauchy = prove_by_refinement(
  `!i f n. cauchy_seq (euclid n,d_euclid) f ==>
     (cauchy_seq (euclid 1,d_euclid) ((proj i) o f))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[cauchy_seq];
  DISCH_ALL_TAC;
  SUBGOAL_TAC `sequence (euclid 1) (proj (i:num) o f)`;
  REWRITE_TAC[sequence;SUBSET;IN_IMAGE;o_DEF;IN_UNIV];
  NAME_CONFLICT_TAC;
  MESON_TAC[IN;proj_euclid1];
  DISCH_TAC;
  ASM_REWRITE_TAC[];
  GEN_TAC;
  FIRST_ASSUM (fun t -> CHOOSE_TAC (SPEC `eps:real` t));
  EXISTS_TAC `n':num`;
  DISCH_ALL_TAC;
  FIRST_ASSUM (fun t-> MP_TAC(SPECL [`i':num`;`j:num`] t));
  UNDISCH_FIND_THEN `d_euclid` (fun t-> ALL_TAC);
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC (REAL_ARITH `a <=. b ==> (b <. eps ==> a <. eps)`);
  REWRITE_TAC[o_DEF;proj_d_euclid];
  MATCH_MP_TAC proj_contraction;
  EXISTS_TAC `n:num`;
  ASM_MESON_TAC[sequence_in];
  ]);;

  (* }}} *)

let complete_euclid = prove_by_refinement(
  `!n. complete (euclid n,d_euclid)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[complete;IN];
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  IMP_RES_THEN MP_TAC proj_cauchy;
  DISCH_TAC;
  SUBGOAL_TAC `!i. converge (euclid 1,d_euclid) (proj i o f)`;
  GEN_TAC;
  ASM_MESON_TAC[complete;complete_real];
  REWRITE_TAC[converge;IN];
  DISCH_THEN (fun t-> MP_TAC (ONCE_REWRITE_RULE[SKOLEM_THM] t));
  DISCH_THEN (X_CHOOSE_TAC `L:num->(num->real)`);
  EXISTS_TAC `(\j. ((L:num->num->real) j 0))`;
  SUBCONJ_TAC;
  REWRITE_TAC[euclid];
  GEN_TAC;
  FIRST_ASSUM (fun t->(MP_TAC (SPEC `m:num` t)));
  DISCH_ALL_TAC;
  FIRST_ASSUM (fun t-> (MP_TAC (SPEC `abs((L:num->num->real) m 0)` t)));
  DISCH_THEN CHOOSE_TAC;
  PROOF_BY_CONTR_TAC;
  ASSUME_TAC (REAL_ARITH `!x. ~(x=(&.0)) ==> (&.0 <. abs(x))`);
  UNDISCH_FIND_TAC `d_euclid`;
  ASM_SIMP_TAC[];
  REWRITE_TAC[GSYM EXISTS_NOT_THM];
  EXISTS_TAC `(n:num)+n'`;
  REWRITE_TAC[o_DEF];
  REWRITE_TAC[ARITH_RULE `n' <=| n+| n'`];
  MATCH_MP_TAC(REAL_ARITH `(x = y) ==> ~(x<y)`);
  ALL_TAC; (* #buffer "CE1"; *)
  SUBGOAL_TAC `euclid 1 (proj m (f (n +| n')))`;
  REWRITE_TAC[proj_euclid1];
  ASM_SIMP_TAC[euclid1_abs];
  DISCH_TAC;
  MATCH_MP_TAC (REAL_ARITH `(&.0 = x) ==> (abs(u - x) = abs(u))`);
  REWRITE_TAC[proj];
  SUBGOAL_TAC `euclid n (f (n+| n'))`;
  ASM_MESON_TAC[cauchy_seq;sequence_in];
  REWRITE_TAC[euclid];
  DISCH_THEN (fun t->  ASM_SIMP_TAC[t]);
  ALL_TAC; (* #buffer "CE2"; *)
  DISCH_TAC;
  GEN_TAC;
  CONV_TAC (quant_right_CONV "n");
  DISCH_TAC;
  USE 2 (CONV_RULE (quant_left_CONV "eps"));
  USE 2 (CONV_RULE (quant_left_CONV "eps"));
  USE 2 (SPEC `eps/(&.1 +. &. n)`);
  USE 2 (CONV_RULE (quant_left_CONV "n'"));
  USE 2 (CONV_RULE (quant_left_CONV "n'"));
  CHO 2;
  SUBGOAL_TAC `&.0 <. eps/ (&.1 +. &.n)`;
  MATCH_MP_TAC REAL_LT_DIV;
  ASM_REWRITE_TAC[REAL_OF_NUM_ADD;REAL_OF_NUM_LT];
  ARITH_TAC;
  DISCH_THEN (fun t-> (USE 2 (REWRITE_RULE[t])));
  SUBGOAL_TAC `!i j. euclid 1 ((proj i o f) (j:num))`;
  ASM_MESON_TAC[cauchy_seq;sequence_in];
  DISCH_TAC;
  SUBGOAL_TAC `!i. euclid n (f (i:num))`;
  GEN_TAC;
  ASM_MESON_TAC[cauchy_seq;sequence_in];
  DISCH_TAC;
  ASM_SIMP_TAC[d_euclid_n];
  SUBGOAL_TAC `!(j:num). ?c. !i. (c <=| i) ==> ||. (L j 0 -. f i j) <. eps/(&.1 + &. n)`;
  CONV_TAC (quant_left_CONV "c");
  EXISTS_TAC `n':num->num`;
  REPEAT GEN_TAC;
  USE 2 ((SPEC `j:num`));
  UND 2;
  DISCH_ALL_TAC;
  USE 8 (SPEC `i:num`);
  UND 8;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[euclid1_abs];
  REWRITE_TAC[proj;o_DEF];
  CONV_TAC (quant_left_CONV "c");
  DISCH_THEN CHOOSE_TAC;
  ABBREV_TAC `t = (\u. (if (u <| n) then (c u) else (0)))`;
  SUBGOAL_TAC `?M. (!j. (t:num->num) j <=| M)`;
  MATCH_MP_TAC max_num_sequence;
  EXISTS_TAC `n:num`;
  GEN_TAC;
  EXPAND_TAC "t";
  COND_CASES_TAC;
  ASM_MESON_TAC[ARITH_RULE `m <| n ==> ~(n <= m)`];
  REWRITE_TAC[];
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `M:num`;
  GEN_TAC;
  ALL_TAC; (* #set "CE3"; *)
  DISCH_TAC;
  MATCH_MP_TAC REAL_POW_2_LT;
  CONJ_TAC;
  MATCH_MP_TAC SQRT_POS_LE;
  REWRITE_TAC[REAL_SUM_SQUARE_POS];
  CONJ_TAC;
  UND 4;
  REAL_ARITH_TAC;
  SIMP_TAC[REAL_SUM_SQUARE_POS;SQRT_POW_2];
  SUBGOAL_TAC `sum (0,n) (\i'. (L i' 0 - f (i:num) i') * (L i' 0 - f i i')) <=. sum (0,n) (\i'. (eps/(&.1 + &.n)) * (eps/(&.1 + &.n)))`;
  MATCH_MP_TAC SUM_LE;
  BETA_TAC;
  GEN_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_TAC `c (r:num) = (t:num->num) r`;
  EXPAND_TAC "t";
  COND_CASES_TAC;
  REFL_TAC;
  ASM_MESON_TAC[ARITH_RULE `n +| 0 = n`];
  DISCH_TAC;
  SUBGOAL_TAC `(abs (L r 0 - f (i:num) (r:num)) < eps/(&.1 + &.n))`;
  USE 7 (SPECL [`r:num`;`i:num`]);
  UND 7;
  DISCH_THEN MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  USE 9 (SPEC `r:num`);
  JOIN 7 10;
  UND 7;
  REWRITE_TAC[LE_TRANS];
  ALL_TAC; (* "CE4" *)
  ABBREV_TAC `b = eps/(&1 + &n)`;
  ABBREV_TAC `a = (L r 0 - (f:num->num->real) i r)`;
  REWRITE_TAC[GSYM REAL_POW_2];
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS];
  REAL_ARITH_TAC;
  MATCH_MP_TAC (REAL_ARITH `(b <. c)   ==> ((a <=. b) ==> (a <. c))`);
  REWRITE_TAC[SUM_CONST];
  REWRITE_TAC[REAL_MUL_AC;real_div];
  SUBGOAL_TAC `eps pow 2 = eps*eps*(&. 1)`;
  REWRITE_TAC[REAL_POW_2];
  REAL_ARITH_TAC;
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  MATCH_MP_TAC REAL_PROP_LT_LMUL;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_PROP_LT_LMUL;
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC `&.0 <. &.1 + &.n `;
  REWRITE_TAC[REAL_OF_NUM_ADD;REAL_OF_NUM_LT];
  ARITH_TAC;
  ALL_TAC; (*  "CE5" *)
  SIMP_TAC[REAL_INV_LT];
  DISCH_TAC;
  REWRITE_TAC[REAL_OF_NUM_ADD;REAL_OF_NUM_LT;REAL_OF_NUM_MUL];
  REWRITE_TAC[ARITH_RULE `(1+n)*(1+n)*1 = 1+n+n+n*n`];
  MATCH_MP_TAC (ARITH_RULE `(0<=a)/\(0<=b) /\(0<1)  ==> (a <| 1 + a + a + b)`);
  CONJ_TAC;
  ARITH_TAC;
  CONJ_TAC;
  ONCE_REWRITE_TAC [ARITH_RULE `0 = n *| 0`];
  REWRITE_TAC[LE_MULT_LCANCEL];
  ARITH_TAC;
  ARITH_TAC;
  ]);;
  (* }}} *)

let subset_sequence = prove_by_refinement(
  `!(X:A->bool) S f. S SUBSET X /\ sequence S f ==>
         sequence X f`,
  (* {{{ proof *)
  [
  REWRITE_TAC[sequence];
  SET_TAC[];
  ]);;
  (* }}} *)

let subset_cauchy = prove_by_refinement(
  `!(X:A->bool) S d f. S SUBSET X /\ cauchy_seq(S,d) f ==>
         cauchy_seq(X,d) f`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  REWRITE_TAC[cauchy_seq];
  DISCH_ALL_TAC;
  ASM_MESON_TAC[subset_sequence];
  ]);;
  (* }}} *)

let complete_closed = prove_by_refinement(
  `!n S. (closed_ (top_of_metric (euclid n,d_euclid)) S) /\
    (S SUBSET (euclid n)) ==>
     (complete (S,d_euclid))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[complete];
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  DISCH_TAC;
  USE 0 (MATCH_MP closed_open);
  UND 0;
  SIMP_TAC[GSYM top_of_metric_unions;metric_euclid];
  DISCH_TAC;
  SUBGOAL_TAC `cauchy_seq(euclid n,d_euclid) f`;
  ASM_MESON_TAC[subset_cauchy];
  DISCH_TAC;
  SUBGOAL_TAC `converge(euclid n,d_euclid) f`;
  ASM_MESON_TAC[complete_euclid;complete];
  REWRITE_TAC[converge];
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `(x:num->real)`;
  ASM_REWRITE_TAC[];
  PROOF_BY_CONTR_TAC;
  SUBGOAL_TAC `~(x IN S) ==> (x IN (euclid n DIFF S))`;
  ASM SET_TAC[];
  DISCH_TAC;
  H_MATCH_MP (HYP "6") (HYP "5");
  USE 0 (REWRITE_RULE[open_DEF]);
  USE 0 (REWRITE_RULE[(MATCH_MP (CONV_RULE (quant_right_CONV "A") top_of_metric_nbd) (SPEC `n:num` metric_euclid))]);
  USE 0 (CONV_RULE (quant_left_CONV "a"));
  USE 0 (SPEC `x:num->real`);
  UND 0;
  ASM_REWRITE_TAC[SUBSET_DIFF];
  ALL_TAC; (* #CC1; *)
  PROOF_BY_CONTR_TAC;
  USE 0 (REWRITE_RULE[]);
  CHO 0;
  USE 0 (REWRITE_RULE[SUBSET;IN_ELIM_THM';open_ball]);
  AND 0;
  AND 4;
  USE 4 (SPEC `r:real`);
  CHO 4;
  H_MATCH_MP (HYP "4") (HYP "8");
  USE 10 (SPEC `n':num`);
  USE 10 (REWRITE_RULE[ARITH_RULE `n <=| n`]);
  USE 0 (SPEC `(f:num->num->real) n'`);
  UND 0;
  USE 9 (REWRITE_RULE[IN]);
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC `(S:(num->real)->bool) ((f:num->num->real) n')`;
  ASM_MESON_TAC[cauchy_seq;sequence_in];
  UND 1;
  ABBREV_TAC `X = euclid n`;
  ABBREV_TAC `a = (f:num->num->real) n'`;
  REWRITE_TAC[IN_DIFF];
  REWRITE_TAC[IN;SUBSET];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Totally bounded metric spaces *)
(* ------------------------------------------------------------------ *)


let totally_bounded = euclid_def `totally_bounded ((X:A->bool),d) =
  (!eps. ?B.  (&.0 <. eps) ==>
    (FINITE B) /\
    (!b. (B b) ==> ?x. b = open_ball(X,d) x eps) /\
    (X = UNIONS B))`;;

let totally_bounded_subset = prove_by_refinement(
  `!(X:A->bool) d S. (metric_space (X,d)) /\ (totally_bounded(X,d))
      /\ (S SUBSET X)  ==>
     (totally_bounded (S,d)) `,
  (* {{{ proof *)

  [
  REPEAT GEN_TAC;
  REWRITE_TAC[totally_bounded];
  DISCH_ALL_TAC;
  GEN_TAC;
  USE 1 (SPEC `eps/(&.2)`);
  CHO 1;
  CONV_TAC (quant_right_CONV "B");
  DISCH_TAC;
  SUBGOAL_TAC `&.0 <. eps ==> &.0 <. eps/(&.2)`;
  DISCH_THEN (fun t-> MP_TAC (ONCE_REWRITE_RULE[GSYM REAL_HALF_DOUBLE] t));
  REWRITE_TAC[REAL_DIV_LZERO];
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  (UND 1) THEN (ASM_REWRITE_TAC[]) THEN DISCH_ALL_TAC;
  SUBGOAL_TAC `!b. ?s. (?t. (t IN (b:A->bool) INTER S)) ==> (s IN b INTER S)`;
  GEN_TAC;
  CONV_TAC (quant_left_CONV "t");
  MESON_TAC[IN];
  CONV_TAC (quant_left_CONV "s");
  DISCH_THEN CHOOSE_TAC;
  ALL_TAC; (* #set "TB1"; *)
  EXISTS_TAC `IMAGE (\c. (open_ball ((S:A->bool),d) ((s) c) eps)) (B:(A->bool)->bool)`;
  CONJ_TAC;
  MATCH_MP_TAC FINITE_IMAGE;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  GEN_TAC;
  REWRITE_TAC[IMAGE;IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  DISCH_THEN (X_CHOOSE_TAC `c:A->bool`);
  ASM_MESON_TAC[];
  MATCH_MP_TAC EQ_EXT;
  X_GEN_TAC `u:A`;
  EQ_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `(X:A->bool) (u:A)`;
  ASM_MESON_TAC[SUBSET;IN];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REWRITE_RULE[IN] IN_UNIONS];
  DISCH_THEN (X_CHOOSE_TAC `b:A->bool`);
  USE 7 (SPEC `b:A->bool`);
  REWRITE_TAC[IMAGE];
  REWRITE_TAC[IN_ELIM_THM'];
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x");
  EXISTS_TAC `b:A->bool`;
  EXISTS_TAC `open_ball((S:A->bool),d) (s (b:A->bool)) eps`;
  ASM_REWRITE_TAC[IN];
  REWRITE_TAC[open_ball];
  REWRITE_TAC[IN_ELIM_THM'];
  ALL_TAC; (* #set "TB2"; *)
  SUBGOAL_TAC `(u:A) IN (b INTER S)`;
  REWRITE_TAC[IN_INTER];
  ASM_MESON_TAC[IN];
  UND 7;
  CONV_TAC (quant_left_CONV "t");
  CONV_TAC (quant_left_CONV "t");
  EXISTS_TAC `u:A`;
  DISCH_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `(S:A->bool) ((s:(A->bool)->A) b)`;
  UND 7;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[IN_INTER];
  MESON_TAC[IN];
  DISCH_TAC;
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC `(b:A->bool) ((s:(A->bool)->A) b)`;
  UND 11;
  UND 7;
  REWRITE_TAC[IN_INTER];
  ASM_MESON_TAC[IN];
  ALL_TAC; (* #set "TB3"; *)
  DISCH_TAC;
  AND 9;
  USE 5 (SPEC `b:A->bool`);
  H_MATCH_MP (HYP "5") (HYP "13");
  CHO 14;
  ABBREV_TAC `v = (s:(A->bool)->A) b`;
  COPY 9;
  UND 9;
  UND 12;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  SUBGOAL_TAC `(X x) /\ ((X:A->bool) u) /\ (X v)`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[SUBSET;IN];
  DISCH_ALL_TAC;
  USE 0 (REWRITE_RULE[metric_space]);
  COPY 16;
  KILL 1;
  KILL 7;
  KILL 11;
  UND 21;
  KILL 6;
  UND 14;
  DISCH_THEN (fun t-> ASSUME_TAC t THEN (REWRITE_TAC[t]));
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  USE 0 (SPECL [`v:A`;`x:A`;`u:A`]);
  UND 0;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  USE 22 (MATCH_MP (REAL_ARITH `(a <=. b + c) ==> !e. (b + c <. e ==> (a <. e))`));
  USE 22 (SPEC `eps:real`);
  UND 22 THEN (DISCH_THEN (MATCH_MP_TAC));
  ASM_REWRITE_TAC[];
  UND 11;
  UND 17;
  MP_TAC (SPEC `eps:real` REAL_HALF_DOUBLE);
  REAL_ARITH_TAC;
  REWRITE_TAC[IMAGE;IN_ELIM_THM'];
  REWRITE_TAC[UNIONS;IN_ELIM_THM'];
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x");
  NAME_CONFLICT_TAC;
  CONV_TAC (quant_left_CONV "x");
  X_GEN_TAC `c:A->bool`;
  CONV_TAC (quant_left_CONV "u'");
  GEN_TAC;
  DISCH_ALL_TAC;
  UND 10;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  MESON_TAC[];
  ]);;

  (* }}} *)

let integer_cube_finite = prove_by_refinement(
  `!n N. FINITE { f | (euclid n f) /\
       (!i. (?j. (abs(f i) = &.j) /\ (j <=| N)))}`,
  (* {{{ proof *)

  [
  REP_GEN_TAC;
  ABBREV_TAC `fs = FUN {m | m <| n} {x |  ?j. (abs x = &.j) /\ (j <=| N)}`;
  ABBREV_TAC `gs = { f | (euclid n f) /\ (!i. (?j. (abs(f i) = &.j) /\ (j <=| N)))}`;
  SUBGOAL_TAC `FINITE (fs:(num->real)->bool)`;
  EXPAND_TAC "fs";
  MP_TAC(prove(`!(a:num->bool) (b:real->bool). FINITE a /\ FINITE b ==> (FINITE (FUN a b))`,MESON_TAC[HAS_SIZE;FUN_SIZE]));
  DISCH_THEN MATCH_MP_TAC;
  REWRITE_TAC[interval_finite;FINITE_NUMSEG_LT];
  DISCH_TAC;
  ABBREV_TAC `G = (\ u. (\ j. if (n <=| j) then (&.0) else (u j)))`;
  SUBGOAL_TAC `FINITE { y | ?x. x IN fs /\ (y:(num->real) = G (x:num->real))}`;
  MATCH_MP_TAC FINITE_IMAGE_EXPAND;
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC `!a b. ((a:(num->real)->bool) = b) ==> (FINITE a ==> FINITE b)`;
  REP_GEN_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  DISCH_THEN (fun t-> MATCH_MP_TAC t);
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  EXPAND_TAC "gs";
  REWRITE_TAC[IN_ELIM_THM'];
  EXPAND_TAC "fs";
  REWRITE_TAC[FUN;IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  EQ_TAC;
  DISCH_THEN (CHOOSE_TAC );
  SUBGOAL_TAC `euclid n x`;
  REWRITE_TAC[euclid];
  GEN_TAC;
  AND 4;
  UND 4;
  EXPAND_TAC "G";
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  DISCH_TAC THEN (ASM_REWRITE_TAC[]);
  GEN_TAC;
  AND 4;
  EXPAND_TAC "G";
  COND_CASES_TAC;
  REDUCE_TAC;
  EXISTS_TAC `0`;
  REDUCE_TAC;
  AND 6;
  USE 8 (SPEC `i:num`);
  ASM_MESON_TAC[ARITH_RULE `~(n <=| i) ==> (i <| n)`];
  DISCH_ALL_TAC;
  EXISTS_TAC `\p. (if (p <| n) then ((x:num->real) p) else (CHOICE UNIV))`;
  CONJ_TAC;
  REWRITE_TAC[SUPP;SUBSET;IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  CONJ_TAC;
  GEN_TAC;
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  UND 5;
  MESON_TAC[];
  GEN_TAC;
  COND_CASES_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[];
  MATCH_MP_TAC EQ_EXT;
  X_GEN_TAC `q:num`;
  EXPAND_TAC "G";
  COND_CASES_TAC;
  ASM_MESON_TAC[euclid];
  USE 6 (MATCH_MP (ARITH_RULE `~(n <=| q) ==> (q <| n)`));
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let FINITE_scaled_lattice = prove_by_refinement(
  `!n N s. (&.0 <. s) ==> FINITE {x | euclid n x /\ (!i. (?j. abs(x i) = s*(&.j)) /\ (abs(x i) <=. (&.N) ) ) }`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  ABBREV_TAC `map  = ( *# ) s`;
  ASSUME_TAC REAL_ARCH_SIMPLE;
  USE 2 (SPEC `inv(s)*(&.N)`);
  UND 2 THEN (DISCH_THEN (X_CHOOSE_TAC `M:num`));
  ASSUME_TAC integer_cube_finite;
  USE 3 (SPECL [`n:num`;`M:num`]);
  USE 3 (MATCH_MP (ISPEC `map:(num->real)->(num->real)` FINITE_IMAGE_EXPAND));
  UND 3;
  MATCH_MP_TAC (prove_by_refinement (`!a b. ((b:A->bool) SUBSET a) ==> (FINITE a ==> FINITE b)`,[MESON_TAC[FINITE_SUBSET]]));
  REWRITE_TAC[SUBSET];
  X_GEN_TAC `c:num->real`;
  REWRITE_TAC[IN_ELIM_THM'];
  EXPAND_TAC "map";
  DISCH_ALL_TAC;
  EXISTS_TAC `inv(s) *# c`;
  REWRITE_TAC[euclid_scale_act];
  ASM_SIMP_TAC[euclid_scale_closure];
  WITH 0 (MATCH_MP (REAL_ARITH `&.0 < s ==> ~(s = &.0)`));
  ASM_SIMP_TAC[REAL_MUL_RINV];
  CONJ_TAC;
  GEN_TAC;
  USE 4 (SPEC `i:num`);
  AND 4;
  CHO 6;
  REWRITE_TAC[euclid_scale;REAL_ABS_MUL;REAL_ABS_INV];
  SUBGOAL_TAC `abs s = s`;
  UND 0;
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  EXISTS_TAC `j:num`;
  ALL_TAC; (* save_goal "C" *)
  SUBCONJ_TAC;
  ASM_REWRITE_TAC[];
  UND 5;
  REWRITE_TAC[GSYM (CONJUNCT1 (CONJUNCT2 (REAL_MUL_AC)))];
  SIMP_TAC[REAL_MUL_LINV];
  REAL_ARITH_TAC;
  DISCH_TAC;
  REWRITE_TAC[GSYM REAL_OF_NUM_LE];
  USE 7 (GSYM);
  UND 7 THEN DISCH_THEN (fun t-> REWRITE_TAC[t]);
  USE 0 (MATCH_MP REAL_LT_INV);
  ABBREV_TAC `s' = inv(s)`;
  USE 0 (MATCH_MP (REAL_ARITH `&.0 < s' ==> &.0 <=. s'`));
  JOIN 0 4;
  USE 0 (MATCH_MP REAL_LE_LMUL);
  JOIN 0 2;
  UND 0;
  REAL_ARITH_TAC;
  REWRITE_TAC[euclid_scale_one];
  ]);;

  (* }}} *)

let totally_bounded_cube = prove_by_refinement(
  `!n N. totally_bounded
        ({x | euclid n x /\ (!i. abs(x i) <=. (&.N))},d_euclid)`,
  (* {{{ proof *)
  [
  REP_GEN_TAC;
  REWRITE_TAC[totally_bounded];
  GEN_TAC;
  CONV_TAC (quant_right_CONV "B");
  DISCH_TAC;
  ABBREV_TAC `cent = {x | euclid n x /\ (!i. (?j. abs(x i) = (eps/(&.n+. &.1))*(&.j)) /\ (abs(x i) <=. (&.N) ) ) }`;
  SUBGOAL_TAC `&.0 <. (&.n +. &.1)`;
  REDUCE_TAC;
  ARITH_TAC;
  DISCH_TAC;
  ABBREV_TAC `s = eps/(&.n +. &.1)`;
  SUBGOAL_TAC `&.0 < s`;
  EXPAND_TAC "s";
  ASM_SIMP_TAC[REAL_LT_DIV];
  DISCH_TAC;
  SUBGOAL_TAC `FINITE (cent:(num->real)->bool)`;
  EXPAND_TAC "cent";
  ASM_SIMP_TAC[FINITE_scaled_lattice];
  DISCH_TAC;
  ABBREV_TAC `cube = {x | euclid n x /\ (!i. abs(x i) <=. (&.N))}`;
  EXISTS_TAC `IMAGE (\c. open_ball(cube,d_euclid) c eps) cent`;
  SUBCONJ_TAC;
  ASM_MESON_TAC[FINITE_IMAGE];
  DISCH_TAC;
  SUBCONJ_TAC;
  GEN_TAC;
  REWRITE_TAC[IMAGE;IN_ELIM_THM'];
  ASM_MESON_TAC[];
  DISCH_TAC;
  ALL_TAC; (* # TB1; *)
  SUBGOAL_TAC `cent SUBSET (cube:(num->real)->bool)`;
  REWRITE_TAC[SUBSET];
  EXPAND_TAC "cent";
  EXPAND_TAC "cube";
  REWRITE_TAC[IN_ELIM_THM'];
  MESON_TAC[];
  DISCH_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  EQ_TAC;
  DISCH_TAC;
  REWRITE_TAC[UNIONS;IN_IMAGE;IN_ELIM_THM'];
  ASSUME_TAC REAL_ARCH_LEAST;
  USE 11 (SPEC `s:real`);
  UND 11 THEN (ASM_REWRITE_TAC[]) THEN DISCH_TAC;
  USE 11 (CONV_RULE (quant_left_CONV "n"));
  USE 11 (CONV_RULE (quant_left_CONV "n"));
  UND 11 THEN (DISCH_THEN (X_CHOOSE_TAC `cs:real->num`));
  NAME_CONFLICT_TAC;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x'");
  ABBREV_TAC `cx = \ (i:num) . if (&.0 <=. (x i)) then &(cs (x i))* s else --. (&.(cs (--. (x i))) * s )`;
  EXISTS_TAC `cx:num->real`;
  EXISTS_TAC `open_ball(cube,d_euclid) cx eps`;
  ASM_REWRITE_TAC[];
  ALL_TAC; (* # TB2; *)
  SUBGOAL_TAC `euclid n x`;
  UND 10;
  EXPAND_TAC "cube";
  REWRITE_TAC[IN_ELIM_THM'];
  MESON_TAC[];
  DISCH_TAC;
  SUBGOAL_TAC `cx IN (euclid n)`;
  REWRITE_TAC[IN;euclid;];
  DISCH_ALL_TAC;
  EXPAND_TAC "cx";
  UND 13;
  REWRITE_TAC[euclid];
  DISCH_THEN (fun t-> MP_TAC(SPEC `m:num` t));
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  REDUCE_TAC;
  USE 11 (SPEC `&.0`);
  UND 11;
  REDUCE_TAC;
  ABBREV_TAC `(a:num) = (cs (&.0))`;
  SUBGOAL_TAC `&.0 <=. &.a *s`;
  REWRITE_TAC[REAL_MUL_NN];
  DISJ1_TAC;
  REDUCE_TAC;
  UND 4;
  REAL_ARITH_TAC;
  ABBREV_TAC `q = (&.a)*. s`;
  REAL_ARITH_TAC;
  DISCH_TAC;
  ALL_TAC; (* # TB3; *)
  SUBCONJ_TAC;
  EXPAND_TAC "cent";
  REWRITE_TAC[IN_ELIM_THM'];
  USE 14 (REWRITE_RULE[IN]);
  ASM_REWRITE_TAC[];
  GEN_TAC;
  EXPAND_TAC "cx";
  BETA_TAC;
  COND_CASES_TAC;
  SUBCONJ_TAC;
  EXISTS_TAC `((cs:real->num) (x (i:num)))`;
  REWRITE_TAC[REAL_ABS_MUL];
  REDUCE_TAC;
  REWRITE_TAC[REAL_MUL_AC];
  AP_THM_TAC;
  AP_TERM_TAC;
  UND 4;
  REAL_ARITH_TAC;
  DISCH_TAC;
  ALL_TAC; (* # TB4; *)
  SUBGOAL_TAC `(&.0 <=. &.(cs ((x:num->real) i)) * s)`;
  REWRITE_TAC[REAL_MUL_NN];
  DISJ1_TAC;
  REDUCE_TAC;
  UND 4 THEN REAL_ARITH_TAC;
  DISCH_THEN (fun t-> MP_TAC (REWRITE_RULE[GSYM REAL_ABS_REFL] t));
  DISCH_THEN (fun t-> REWRITE_TAC [t]);
  USE 11 (SPEC `(x:num->real) i`);
  UND 11;
  ASM_REWRITE_TAC [];
  UND 10;
  EXPAND_TAC "cube";
  REWRITE_TAC [IN_ELIM_THM'];
  DISCH_THEN (fun t -> ASSUME_TAC (CONJUNCT2 t));
  USE 10 (SPEC `i:num`);
  UND 10;
  ASSUME_TAC(prove(`&.0 <= x ==> (abs x = x)`,MESON_TAC[REAL_ABS_REFL]));
  ASM_SIMP_TAC[];
  MESON_TAC[REAL_LE_TRANS];
  ALL_TAC ; (* #TB5; *)
  REWRITE_TAC[REAL_ABS_NEG];
  SUBCONJ_TAC;
  EXISTS_TAC `((cs:real->num) (--. (x (i:num))))`;
  REWRITE_TAC [REAL_ABS_MUL];
  REDUCE_TAC;
  ASSUME_TAC(prove(`&.0 <= x ==> (abs x = x)`,MESON_TAC[REAL_ABS_REFL]));
  ASSUME_TAC(REAL_ARITH `&.0 < x ==> &. 0 <=. x`);
  ASM_SIMP_TAC[];
  REWRITE_TAC [REAL_MUL_AC];
  DISCH_TAC;
  USE 11 (SPEC `--. (x (i:num))`);
  UND 11;
  ASSUME_TAC (REAL_ARITH `!x. ~(&.0 <= x) ==> (&.0 <= --. x)`);
  ASM_SIMP_TAC[];
  UND 10;
  EXPAND_TAC "cube";
  REWRITE_TAC[IN_ELIM_THM'];
  DISCH_THEN (fun t -> ASSUME_TAC (CONJUNCT2 t));
  USE 10 (SPEC `i:num`);
  UND 10;
  MP_TAC(prove(`!v. (-- v <=. abs(v))`,REAL_ARITH_TAC));
  REWRITE_TAC [REAL_ABS_MUL];
  REDUCE_TAC;
  ASSUME_TAC(prove(`&.0 <= x ==> (abs x = x)`,MESON_TAC[REAL_ABS_REFL]));
  ASSUME_TAC(REAL_ARITH `&.0 < x ==> &. 0 <=. x`);
  ASM_SIMP_TAC[];
  MESON_TAC[REAL_LE_TRANS];
  ALL_TAC;  (* #TB6; *)
  DISCH_TAC;
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  UND 15;
  UND 9;
  REWRITE_TAC[SUBSET;IN];
  MESON_TAC[];
  SUBGOAL_TAC `d_euclid cx x <= sqrt(&.n)*s`;
  MATCH_MP_TAC D_EUCLID_BOUND;
  USE 14 (REWRITE_RULE[IN]);
  ASM_REWRITE_TAC[];
  GEN_TAC;
  EXPAND_TAC "cx";
  BETA_TAC;
  ASSUME_TAC (REAL_ARITH `!x a b. a <=. x /\ x <. b ==> abs(a - x) <= b -a`);
  SUBGOAL_TAC `!x. &.0 <=. x ==> abs(&.(cs x)*.s -. x) <=. s`;
  DISCH_ALL_TAC;
  USE 11 (SPEC `x':real`);
  H_MATCH_MP (HYP "11") (HYP "17");
  H_MATCH_MP (HYP "16") (HYP "18");
  USE 19 (REWRITE_RULE [GSYM REAL_SUB_RDISTRIB]);
  ALL_TAC; (* # TB7; *)
  USE 19 (CONV_RULE REDUCE_CONV);
  ASM_REWRITE_TAC [];
  DISCH_TAC;
  COND_CASES_TAC;
  ASM_MESON_TAC[];
  REWRITE_TAC[REAL_ARITH `--x - y = --(x+.y)`;REAL_ABS_NEG];
  REWRITE_TAC[REAL_ARITH `x+. y = (x -. (--. y))`];
  ASM_MESON_TAC[REAL_ARITH `!u. ~(&.0 <=. u) ==> (&.0 <=. (--. u))`];
  ALL_TAC; (* # TB8; *)
  MATCH_MP_TAC(REAL_ARITH `b < c ==> ((a<=b) ==> (a < c))`);
  EXPAND_TAC "s";
  REWRITE_TAC[real_div;REAL_MUL_AC];
  MATCH_MP_TAC(REAL_ARITH`(t < e *(&.1)) ==> (t <. e)`);
  MATCH_MP_TAC (REAL_LT_LMUL);
  ASM_REWRITE_TAC[];
  ASSUME_TAC REAL_PROP_LT_LCANCEL ;
  USE 16 (SPEC `&.n +. &.1`);
  UND 16;
  DISCH_THEN (MATCH_MP_TAC);
  REDUCE_TAC;
  SUBGOAL_TAC `~(&.(n+1) = &.0)`;
  REDUCE_TAC;
  ARITH_TAC;
  REWRITE_TAC[REAL_ARITH`a*b*c = (a*b)*c`];
  ALL_TAC; (* # TB8; *)
  SIMP_TAC[REAL_MUL_RINV];
  REDUCE_TAC;
  DISCH_TAC;
  CONJ_TAC;
  ARITH_TAC;
  SQUARE_TAC;
  SUBCONJ_TAC;
  MATCH_MP_TAC SQRT_POS_LE;
  REDUCE_TAC;
  DISCH_TAC;
  SUBCONJ_TAC;
  REDUCE_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `&.0 <=. &.n`;
  REDUCE_TAC;
  SIMP_TAC[prove(`!x. (&.0 <=. x) ==> (sqrt(x) pow 2 = x)`,MESON_TAC[SQRT_POW2])];
  DISCH_TAC;
  REWRITE_TAC[REAL_POW_2];
  REDUCE_TAC;
  REWRITE_TAC[LEFT_ADD_DISTRIB;RIGHT_ADD_DISTRIB];
  REDUCE_TAC;
  ABBREV_TAC `m = n*|n +| n`;
  ARITH_TAC;
  ALL_TAC; (* # TB9;  *)
  REWRITE_TAC[UNIONS;IN_IMAGE;IN_ELIM_THM'];
  DISCH_THEN CHOOSE_TAC;
  AND 10;
  CHO 11;
  AND 11;
  UND 10;
  ASM_REWRITE_TAC[];
  MP_TAC (ISPEC `cube:(num->real)->bool` open_ball_subset);
  REWRITE_TAC[SUBSET];
  REWRITE_TAC[IN];
  MESON_TAC[];
  ]);;
  (* }}} *)

let center_FINITE = prove_by_refinement(
  `!X d  . metric_space ((X:A->bool),d) /\ (totally_bounded (X,d))
   ==> (!eps. (&.0 < eps) ==> (?C. (C SUBSET X) /\ (FINITE C) /\ (X = UNIONS (IMAGE (\x. open_ball(X,d) x eps) C))))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[totally_bounded];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  USE 1 (SPEC `eps:real`);
  CHO 1;
  REWR 1;
  AND 1;
  AND 1;
  USE 4 (CONV_RULE ((quant_left_CONV "x")));
  USE 4 (CONV_RULE ((quant_left_CONV "x")));
  CHO 4;
  ABBREV_TAC `C'={z | (X (z:A)) /\ (?b. (B (b:A->bool)) /\ (z = x b))}`;
  EXISTS_TAC `C':A->bool`;
  SUBCONJ_TAC;
  EXPAND_TAC"C'";
  REWRITE_TAC[SUBSET;IN_ELIM_THM'];
  REWRITE_TAC[IN];
  MESON_TAC[];
  DISCH_TAC;
  CONJ_TAC;
  SUBGOAL_TAC `C' SUBSET (IMAGE (x:(A->bool)->A) B)`;
  EXPAND_TAC"C'";
  REWRITE_TAC[SUBSET;IN_IMAGE;IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  MESON_TAC[IN];
  DISCH_TAC;
  SUBGOAL_TAC `FINITE (IMAGE (x:(A->bool)->A) B)`;
  ASM_MESON_TAC[FINITE_IMAGE];
  ASM_MESON_TAC[FINITE_SUBSET];
  ALL_TAC; (* #g1; *)
  (ASM (GEN_REWRITE_TAC LAND_CONV)) [];
  ( (GEN_REWRITE_TAC LAND_CONV)) [UNIONS_DELETE];
  AP_TERM_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[DELETE;IN_ELIM_THM';IMAGE];
  EXPAND_TAC "C'";
  REWRITE_TAC[IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  EQ_TAC;
  DISCH_ALL_TAC;
  USE 4 (SPEC `x':A->bool`);
  CONV_TAC (quant_left_CONV "b");
  CONV_TAC (quant_left_CONV "b");
  CONV_TAC (quant_left_CONV "b");
  EXISTS_TAC `x':(A->bool)`;
  EXISTS_TAC `(x:(A->bool)->A) x'`;
  REWRITE_TAC[];
  USE 7 (REWRITE_RULE[IN]);
  H_MATCH_MP (HYP "4") (HYP"7");
  ALL_TAC; (* #g2 *)
  ABBREV_TAC `a = (x:(A->bool)->A) x'`;
  KILL 1;
  ASM_REWRITE_TAC[];
  UND 8;
  ASM_REWRITE_TAC[];
  MESON_TAC[open_ball_empty;IN];
  ALL_TAC; (* #g3 *)
  DISCH_THEN CHOOSE_TAC;
  UND 7;
  DISCH_ALL_TAC;
  CHO 8;
  AND 8;
  CONJ_TAC;
  KILL 1;
  ASM_REWRITE_TAC[];
  KILL 9;
  USE 4 (SPEC `b:A->bool`);
  REWR 1;
  ASM_MESON_TAC[IN];
  KILL 1;
  ASM_REWRITE_TAC[];
  UND 7;
  ASM_REWRITE_TAC[];
  ABBREV_TAC `a = (x:(A->bool)->A) b`;
  DISCH_TAC;
  JOIN 2 7;
  JOIN 0 2;
  USE 0 (MATCH_MP open_ball_nonempty);
  UND 0;
  ABBREV_TAC `E= open_ball(X,d) (a:A) eps `;
  MESON_TAC[IN;EMPTY];
  ]);;
  (* }}} *)

let open_ball_dist = prove_by_refinement(
  `!X d x y r. (open_ball(X,d) x r y) ==> (d (x:A) y <. r)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let totally_bounded_bounded = prove_by_refinement(
  `!(X:A->bool) d. metric_space(X,d) /\ totally_bounded (X,d) ==>
    (?a r. X SUBSET (open_ball(X,d) a r))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  COPY 0;
  JOIN 0 1;
  USE 0 (MATCH_MP center_FINITE);
  USE 0 (SPEC `&.1`);
  USE 0 (CONV_RULE REDUCE_CONV);
  CHO 0;
  EXISTS_TAC `CHOICE (X:A->bool)`;
  ASM_CASES_TAC `(X:A->bool) = EMPTY`;
  ASM_REWRITE_TAC[EMPTY_SUBSET];
  USE 1 (MATCH_MP CHOICE_DEF);
  UND 0 THEN DISCH_ALL_TAC;
  ABBREV_TAC `(dset:real->bool) = IMAGE (\c. (d (CHOICE (X:A->bool)) (c:A))) C`;
  SUBGOAL_TAC `FINITE (dset:real->bool)`;
  EXPAND_TAC"dset";
  MATCH_MP_TAC FINITE_IMAGE;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  USE 6 (MATCH_MP real_FINITE);
  CHO 6;
  EXISTS_TAC `a +. &.1`;
  REWRITE_TAC[SUBSET];
  GEN_TAC;
  REWRITE_TAC[open_ball;IN_ELIM_THM'];
  UND 1;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  UND 4;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  (* ASM (GEN_REWRITE_TAC LAND_CONV) []; *)
  USE 4(REWRITE_RULE[UNIONS;IN_IMAGE;IN_ELIM_THM']);
  USE 4(fun t -> AP_THM t `x:A`);
  UND 1;
  DISCH_THEN (fun t-> ((MP_TAC t) THEN (ASM_REWRITE_TAC[])) THEN ASSUME_TAC t);
  DISCH_TAC;
  USE 8 (REWRITE_RULE[IN_ELIM_THM']);
  CHO 8;
  AND 8;
  USE 9 (CONV_RULE NAME_CONFLICT_CONV);
  CHO 9;
  ALL_TAC; (* # "tbb"; *)
  REWR 8;
  USE 8(REWRITE_RULE[IN]);
  USE 8 (MATCH_MP open_ball_dist);
  AND 9;
  SUBGOAL_TAC `d (CHOICE (X:A->bool)) (x':A) IN (dset:real->bool)`;
  EXPAND_TAC"dset";
  REWRITE_TAC[IN_IMAGE];
  ASM_MESON_TAC[];
  DISCH_TAC;
  H_MATCH_MP (HYP"6") (HYP"11");
  USE 2 (REWRITE_RULE[metric_space]);
  USE 2 (SPECL[`(CHOICE (X:A->bool))`;`(x':A)`;`x:A`]);
  KILL 4;
  REWR 2;
  SUBGOAL_TAC `(X:A->bool) x'`;
  UND 9;
  UND 0;
  SET_TAC[IN;SUBSET];
  DISCH_TAC;
  REWR 2;
  UND 2 THEN DISCH_ALL_TAC;
  UND 8;
  UND 12;
  UND 15;
  ARITH_TAC;
  ]);;
  (* }}} *)

let subsequence_rec = prove_by_refinement(
  `!(X:A->bool) d f C s n r.
   metric_space(X,d) /\ (totally_bounded(X,d)) /\ (sequence X f) /\
   (C SUBSET X) /\ (&.0 < r) /\
   (~FINITE{j| C (f j)} /\ C(f s) /\ (!x y. (C x /\ C y) ==>
       d x y <. r*twopow(--: (&:n)))) ==>
   (? C' s'. ((C' SUBSET C) /\ (s < s') /\
   (~FINITE{j| C' (f j)} /\ C'(f s') /\ (!x y. (C' x /\ C' y) ==>
        d x y <. r*twopow(--: (&:(SUC n)))))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  USE 1 (REWRITE_RULE[totally_bounded]);
  USE 1 (SPEC `r*twopow(--: (&:(n+| 2)))`);
  CHO 1;
  ASSUME_TAC twopow_pos;
  USE 8 (SPEC `--: (&: (n+| 2))`);
  ALL_TAC; (* ## need a few lines here to match Z8 with Z1. *)
  COPY 4;
  JOIN 9 8;
  USE 8 (MATCH_MP REAL_LT_MUL);
  REWR 1;
  UND 1 THEN DISCH_ALL_TAC;
  ALL_TAC ; (* "sr1"  OK TO HERE *)
  ASSUME_TAC (ISPECL [`UNIV:num->bool`;`f:num->A`;`B:(A->bool)->bool`;`C:A->bool`] INFINITE_PIGEONHOLE);
  UND 11;
  ASM_SIMP_TAC[UNIV];
  H_REWRITE_RULE[HYP "10"] (HYP "3");
  ASM_REWRITE_TAC [];
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `C INTER (b:A->bool)`;
  CONV_TAC (quant_right_CONV "s'");
  SUBCONJ_TAC;
  REWRITE_TAC[INTER_SUBSET];
  DISCH_TAC;
  AND 12;
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC `~(FINITE ({i | (C INTER b) ((f:num->A) i)} INTER {i | s <| i}))`;
  PROOF_BY_CONTR_TAC;
  (USE 15) (REWRITE_RULE[]);
  USE 15 (MATCH_MP num_above_finite);
  UND 12;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ABBREV_TAC `J = ({i | (C INTER b) ((f:num->A) i)} INTER {i | s <| i})`;
  EXISTS_TAC `CHOICE (J:num->bool)`; (* ok to here *)
  SUBGOAL_TAC `J (CHOICE (J:num->bool))`;
  MATCH_MP_TAC (REWRITE_RULE [IN] CHOICE_DEF);
  PROOF_BY_CONTR_TAC;
  USE 17 (REWRITE_RULE[]);
  H_REWRITE_RULE[(HYP "17")] (HYP "15");
  UND 18;
  REWRITE_TAC[FINITE_RULES];
  ALL_TAC; (* "sr2" *)
  ABBREV_TAC `s' = (CHOICE (J:num->bool))`;
  EXPAND_TAC "J";
  REWRITE_TAC[INTER;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  KILL 5 THEN (KILL 2) THEN (KILL 1) THEN (KILL 13) THEN (KILL 12);
  SUBGOAL_TAC `(X x) /\ (X (y:A))`;
  UND 21 THEN UND 23 THEN UND 3;
  MESON_TAC[SUBSET;IN];
  USE 9 (SPEC `b:A->bool`);
  H_REWRITE_RULE[HYP "14"] (HYP "1");
  CHO 2;
  ALL_TAC; (* #"gg1" *)
  JOIN 22 24;
  JOIN 0 5;
  H_REWRITE_RULE[(HYP "2")] (HYP "0");
  USE 5 (REWRITE_RULE[IN]);
  USE 5 (MATCH_MP BALL_DIST);
  DISCH_ALL_TAC;
  UND 5;
  MATCH_MP_TAC (REAL_ARITH `(b = c) ==> ((a<. b) ==> (a<c))`);
  ALL_TAC;  (* insert here *)
  REWRITE_TAC[REAL_MUL_ASSOC];
  REWRITE_TAC[REAL_ARITH `&.2 *.r = r*. (&.2)`];
  REWRITE_TAC[GSYM REAL_MUL_ASSOC];
  REWRITE_TAC[REAL_EQ_LMUL];
  USE 4 (MATCH_MP (REAL_ARITH `&.0 <. r ==> ~(r = &.0)`));
  ASM_REWRITE_TAC[];
  REWRITE_TAC[TWOPOW_NEG];
  REWRITE_TAC[ARITH_RULE `(n+|2) = 1 + (SUC n)`];
  REWRITE_TAC[REAL_POW_ADD;REAL_INV_MUL];
  REWRITE_TAC [REAL_MUL_ASSOC];
  REWRITE_TAC[REAL_INV2;REAL_POW_1];
  REDUCE_TAC;
  ]);;
  (* }}} *)

let sequence_subseq = prove_by_refinement(
  `!(X:A->bool) f (ss:num->num). (sequence X f) ==>
    (sequence X (f o ss))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[sequence;IMAGE;IN_UNIV;SUBSET;IN_ELIM_THM';o_DEF];
  REWRITE_TAC[IN];
  MESON_TAC[];
  ]);;
  (* }}} *)

let cauchy_subseq = prove_by_refinement(
  `!(X:A->bool) d f. ((metric_space(X,d))/\(totally_bounded(X,d)) /\
        (sequence X f)) ==>
     (?ss. (subseq ss) /\ (cauchy_seq(X,d) (f o ss)))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  COPY 0 THEN COPY 1;
  JOIN 4 3;
  USE 3 (MATCH_MP totally_bounded_bounded);
  CHO 3;
  CHO 3;
  ALL_TAC; (* {{{ xxx *)
  ALL_TAC; (* make r pos *)
  ASSUME_TAC (REAL_ARITH `r <. (&.1 + abs(r))`);
  ASSUME_TAC (REAL_ARITH `&.0 <. (&.1 + abs(r))`);
  ABBREV_TAC (`r' = &.1 +. abs(r)`);
  SUBGOAL_TAC `open_ball(X,d) a r SUBSET open_ball(X,d) (a:A) r'`;
  ASM_SIMP_TAC[open_ball_nest];
  DISCH_TAC;
  JOIN 3 7;
  USE 3 (MATCH_MP SUBSET_TRANS);
  KILL 6;
  KILL 4;
  ALL_TAC; (* "cs1" *)
  SUBGOAL_TAC `( !(x:A) y.  (X x) /\ (X y) ==> (d x y <. &.2 *. r'))`;
  DISCH_ALL_TAC;
  USE 3 (REWRITE_RULE[SUBSET;IN]);
  COPY 3;
  USE 7 (SPEC `x:A`);
  USE 3 (SPEC `y:A`);
  H_MATCH_MP (HYP "3") (HYP "6");
  H_MATCH_MP (HYP "7") (HYP "4");
  JOIN 9 8;
  JOIN 0 8;
  USE 0 (MATCH_MP BALL_DIST);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ABBREV_TAC `cond = (\ ((C:A->bool),(s:num)) n. ~FINITE{j| C (f j)} /\ (C(f s)) /\ (!x y. (C x /\ C y) ==> d x y <. (&.2*.r')*. twopow(--: (&:n))))`;
  ABBREV_TAC `R = (&.2)*r'`;
  ALL_TAC ; (* 0 case of recursio *)
  ALL_TAC; (* cs2 *)
  SUBGOAL_TAC ` (X SUBSET X) /\ (cond ((X:A->bool),0) 0)`;
  REWRITE_TAC[SUBSET_REFL];
  EXPAND_TAC "cond";
  CONV_TAC (TOP_DEPTH_CONV  GEN_BETA_CONV);
  USE 2 (REWRITE_RULE[sequence;SUBSET;IN_IMAGE;IN_UNIV]);
  USE 2 (REWRITE_RULE[IN]);
  USE 2 (CONV_RULE (NAME_CONFLICT_CONV));
  SUBGOAL_TAC `!x. X((f:num->A) x)`;
  ASM_MESON_TAC[];
  REDUCE_TAC;
  REWRITE_TAC[TWOPOW_0] THEN REDUCE_TAC;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  SUBGOAL_TAC `{ j | (X:A->bool) (f j) } = (UNIV:num->bool)`;
  MATCH_MP_TAC EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM;UNIV];
  ASM_REWRITE_TAC[];
  DISCH_THEN REWRT_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[num_infinite];
  ALL_TAC; (* #save_goal "cs3" *)
  SUBGOAL_TAC `&.0 <. R`;
  EXPAND_TAC "R";
  UND 5;
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_TAC `!cs n. ?cs' . (FST cs SUBSET X) /\ (cond cs n)==>( (FST cs' SUBSET (FST cs)) /\(SND cs <| ((SND:((A->bool)#num)->num) cs') /\ (cond cs' (SUC n))) )`;
  DISCH_ALL_TAC;
  CONV_TAC (quant_right_CONV "cs'");
  DISCH_TAC;
  AND 11;
  H_REWRITE_RULE[GSYM o (HYP "6")] (HYP "11");
  USE 13 (CONV_RULE (SUBS_CONV[GSYM(ISPEC `cs:(A->bool)#num` PAIR)]));
  USE 13 (CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV));
  JOIN 10 13;
  JOIN 12 10;
  JOIN 2 10;
  JOIN 1 2;
  JOIN 0 1;
  USE 0 (MATCH_MP subsequence_rec);
  CHO 0;
  CHO 0;
  EXISTS_TAC `(C':A->bool,s':num)`;
  ASM_REWRITE_TAC[FST;SND];
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ALL_TAC; (* "cs4" *)
  USE 11 (REWRITE_RULE[SKOLEM_THM]);
  CHO 11;
  ASSUME_TAC (ISPECL[`((X:A->bool),0)`;`cs':(((A->bool)#num)->(num->(A->bool)#num))`] num_RECURSION);
  CHO 12;
  EXISTS_TAC `\i. (SND ((fn : num->(A->bool)#num) i))`;
  USE 11 (CONV_RULE (quant_left_CONV "n"));
  USE 11 (SPEC `n:num`);
  USE 11 (SPEC `(fn:num->(A->bool)#num) n`);
  AND 12;
  H_REWRITE_RULE[GSYM o (HYP "12")] (HYP "11");
  USE 14 (GEN_ALL);
  ABBREV_TAC `sn = (\i. SND ((fn:num->(A->bool)#num) i))`;
  ABBREV_TAC `Cn = (\i. FST ((fn:num->(A->bool)#num) i))`;
  SUBGOAL_TAC `((sn:num->num) 0 = 0) /\ (Cn 0 = (X:A->bool))`;
  EXPAND_TAC "sn";
  EXPAND_TAC "Cn";
  UND 13;
  MESON_TAC[FST;SND];
  DISCH_TAC;
  KILL 13;
  KILL 11;
  SUBGOAL_TAC `!(n:num). ((fn n):(A->bool)#num) = (Cn n,sn n)`;
  EXPAND_TAC "sn";
  EXPAND_TAC "Cn";
  REWRITE_TAC[PAIR];
  DISCH_TAC;
  H_REWRITE_RULE[(HYP "11")] (HYP"14");
  KILL 12;
  KILL 14;
  KILL 11;
  KILL 16;
  KILL 15;
  ALL_TAC; (* }}} *)
  ALL_TAC; (* KILL 10; cs4m *)
  KILL 8;
  KILL 7;
  KILL 3;
  KILL 5;
  ALL_TAC; (* cs5 *)
  TYPE_THEN `!n. (Cn n SUBSET X) /\ (cond (Cn n,sn n) n)` SUBGOAL_TAC;
  INDUCT_TAC;
  ASM_REWRITE_TAC[];
  SET_TAC[SUBSET];
  USE 13 (SPEC `n:num`);
  REWR 5;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[SUBSET_TRANS];
  DISCH_TAC;
  REWR 13;
  SUBCONJ_TAC;
  ASM_REWRITE_TAC[SUBSEQ_SUC];
  DISCH_TAC;
  ASM_REWRITE_TAC[cauchy_seq];
  ASM_SIMP_TAC[sequence_subseq];
  GEN_TAC;
  TYPE_THEN `!i j. (i <=| j) ==> (Cn j SUBSET (Cn i))` SUBGOAL_TAC;
  MATCH_MP_TAC SUBSET_SUC2;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ALL_TAC; (* cs6 *)
  SUBGOAL_TAC `!R e. ?n. (&.0 <. R)/\ (&.0 <. e) ==> R*(twopow(--: (&:n))) <. e`;
  DISCH_ALL_TAC;
  REWRITE_TAC[TWOPOW_NEG]; (* cs6b *)
  ASSUME_TAC (prove(`!n. &.0 < &.2 pow n`,REDUCE_TAC THEN ARITH_TAC));
  ONCE_REWRITE_TAC[REAL_MUL_AC];
  ASM_SIMP_TAC[REAL_INV_LT];
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ];
  CONV_TAC (quant_right_CONV "n");
  DISCH_ALL_TAC;
  ASSUME_TAC (SPEC `R'/e` REAL_ARCH_SIMPLE);
  CHO 14;
  EXISTS_TAC `n:num`;
  UND 14;
  MESON_TAC[POW_2_LT;REAL_LET_TRANS];
  DISCH_TAC;
  USE 11 (SPECL [`R:real`;`eps:real`]);
  CHO 11;
  EXISTS_TAC `n:num`;
  DISCH_ALL_TAC;
  REWR 11;
  ALL_TAC; (* cs7 *)
  COPY 3;
  USE 3 (SPEC `n:num`);
  AND 3;
  UND 3;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  DISCH_ALL_TAC;
  COPY 15;
  USE 15 (SPEC `i:num`);
  AND 15;
  UND 15;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  DISCH_ALL_TAC;
  COPY 20;
  USE 20 (SPEC `j:num`);
  AND 20;
  UND 20;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  DISCH_ALL_TAC;
  ABBREV_TAC `e2 = R * twopow (--: (&:n))`;
  REWRITE_TAC[o_DEF];
  TYPEL_THEN [`f (sn i)`;`f (sn j)`] (fun t-> (USE 19 (SPECL t)));
  KILL 27;
  KILL 23;
  KILL 25;
  KILL 21;
  KILL 16;
  KILL 9;
  KILL 6;
  KILL 28;
  COPY 8;
  USE 8 (SPECL [`n:num`;`i:num`]);
  USE 6 (SPECL [`n:num`;`j:num`]);
  UND 11;
  MATCH_MP_TAC (REAL_ARITH `(c < a) ==> ((a < b) ==> (c < b))`);
  UND 19;
  DISCH_THEN (MATCH_MP_TAC);
  UND 6;
  UND 8;
  ASM_REWRITE_TAC[];
  UND 22;
  UND 26;
  MESON_TAC[IN;SUBSET];
  ]);;

  (* }}} *)

let convergent_subseq = prove_by_refinement(
  `!(X:A->bool) d f. metric_space(X,d) /\ (totally_bounded(X,d)) /\
     (complete (X,d)) /\ (sequence X f)  ==>
     ((?(ss:num->num). (subseq ss) /\ (converge (X,d) (f o ss))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
    TYPE_THEN `?ss. (subseq ss) /\ (cauchy_seq(X,d) (f o ss))` SUBGOAL_TAC;
  ASM_MESON_TAC[cauchy_subseq];
  DISCH_ALL_TAC;
  CHO 4;
  EXISTS_TAC `ss:num->num`;
  USE 2 (REWRITE_RULE[complete]);
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let dense = euclid_def `!U Z. dense U Z <=>
  (closure U (Z:A->bool) = UNIONS U)`;;

let hausdorff = euclid_def `hausdorff U  <=> (!x y.
   (UNIONS U (x:A) /\ UNIONS U y /\ ~(x = y)) ==>
   (?A B. (U A) /\ (U B) /\ (A x) /\ (B y) /\ (A INTER B = EMPTY)))`;;

let dense_subset = prove_by_refinement(
  `!U Z. (topology_ U) /\ (dense U (Z:A->bool)) ==>
      (Z SUBSET (UNIONS U))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[dense];
  MESON_TAC[subset_closure];
  ]);;
  (* }}} *)

let dense_open = prove_by_refinement(
  `!U Z. (topology_ U) /\ (Z SUBSET (UNIONS U)) ==>
   (dense U (Z:A->bool) <=>
    (!A. (open_ U A) /\ ( (A INTER Z) = EMPTY) ==> (A = EMPTY)))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_TAC;
  DISCH_ALL_TAC;
  COPY 3;
  COPY 0;
  JOIN 0 3;
  USE 0 (MATCH_MP (open_closed));
  TYPE_THEN `Z SUBSET (UNIONS U DIFF A)` SUBGOAL_TAC;
  ALL_TAC ; (* do1 *)
  REWRITE_TAC[DIFF_SUBSET];
  ONCE_REWRITE_TAC[INTER_COMM];
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  JOIN 0 3;
  JOIN 6 0;
  USE 0 (MATCH_MP closure_subset);
  USE 0 (REWRITE_RULE[DIFF_SUBSET]);
  AND 0;
  USE 2 (REWRITE_RULE[dense]);
  H_REWRITE_RULE [(HYP "2")] (HYP "0");
  (USE 5 (REWRITE_RULE[open_DEF]));
  USE 5 (MATCH_MP sub_union);
  USE 5 (REWRITE_RULE[ SUBSET_INTER_ABSORPTION]);
  USE 5 (ONCE_REWRITE_RULE[INTER_COMM]);
  ASM_MESON_TAC[];
  REWRITE_TAC[dense];
  DISCH_TAC ;
  MATCH_MP_TAC  EQ_SYM;
  UND 0;
  UND 1;
  SIMP_TAC [closure_open];
  DISCH_TAC ;
  SIMP_TAC[closed_UNIV];
  DISCH_TAC ;
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  USE 2 (SPEC `B:A->bool`);
  REWR 2;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[INTER_EMPTY];
   ]);;
  (* }}} *)

let countable_dense = prove_by_refinement(
  `!(X:A->bool) d. (metric_space(X,d)) /\ (totally_bounded(X,d)) ==>
     ?Z. (COUNTABLE Z) /\ (dense (top_of_metric(X,d)) Z)`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  TYPE_THEN `!r. ?z. (COUNTABLE z) /\ (z SUBSET X) /\ (X = UNIONS (IMAGE (\x. open_ball(X,d) x (twopow(--: (&:r)))) z))` SUBGOAL_TAC;
  GEN_TAC;
  COPY 0;
  COPY 1;
  JOIN 2 3;
  USE 2 (MATCH_MP center_FINITE);
  USE 2 (SPEC `twopow (--: (&:r))`);
  H_MATCH_MP (HYP "2") (THM (SPEC `(--: (&:r))` twopow_pos));
  X_CHO 3 `z:A->bool`;
  EXISTS_TAC `z:A->bool`;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[FINITE_COUNTABLE];
  ASM_MESON_TAC[];
  CONV_TAC (quant_left_CONV "z");
  DISCH_THEN CHOOSE_TAC;
  TYPE_THEN  `UNIONS (IMAGE z (UNIV:num->bool))` EXISTS_TAC;
  CONJ_TAC;
  MATCH_MP_TAC  COUNTABLE_UNIONS;
  CONJ_TAC;
  MATCH_MP_TAC  (ISPEC `UNIV:num->bool` COUNTABLE_IMAGE);
  REWRITE_TAC[NUM_COUNTABLE];
  TYPE_THEN `z` EXISTS_TAC ;
  SET_TAC[];
  GEN_TAC;
  REWRITE_TAC[IN_IMAGE;IN_UNIV];
  ASM_MESON_TAC[ ];
  TYPE_THEN `U = top_of_metric (X,d)` ABBREV_TAC;
  TYPE_THEN `Z = UNIONS (IMAGE z UNIV)` ABBREV_TAC;
  TYPE_THEN `topology_ U /\ (Z SUBSET (UNIONS U))` SUBGOAL_TAC;
  EXPAND_TAC "U";
  KILL 3;
  ASM_SIMP_TAC[top_of_metric_top;GSYM top_of_metric_unions];
  EXPAND_TAC "Z";
  MATCH_MP_TAC  UNIONS_SUBSET;
  REWRITE_TAC[IN_IMAGE;IN_UNIV];
  ASM_MESON_TAC[];
  SIMP_TAC[dense_open];
  DISCH_ALL_TAC;
  GEN_TAC;
  REWRITE_TAC[open_DEF];
  MATCH_MP_TAC  (TAUT `( a /\ ~b ==> ~c) ==> (a /\ c ==> b)`);
  EXPAND_TAC "U";
  ASM_SIMP_TAC [top_of_metric_nbd];
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY];
  DISCH_ALL_TAC;
  CHO 9;
  TYPE_THEN `x` (fun t-> (USE 8 (SPEC t)));
  REWR 8;
  X_CHO 8 `eps:real`;
  ALL_TAC; (*"cd5"*)
  SUBGOAL_TAC `?r. twopow(--: (&:r)) < eps`;
  ASSUME_TAC (SPECL [`&.1`;`eps:real`] twopow_eps);
  USE 10 (CONV_RULE REDUCE_CONV);
  ASM_MESON_TAC[];
  DISCH_THEN CHOOSE_TAC;
  USE 2 (SPEC `r:num`);
  AND 2;
  AND 2;
  TYPE_THEN `x IN X` SUBGOAL_TAC;
  ASM SET_TAC[IN;SUBSET];
  ASM ONCE_REWRITE_TAC[];
  REWRITE_TAC[UNIONS;IN_ELIM_THM';IN_IMAGE];
  DISCH_THEN CHOOSE_TAC;
  AND 13;
  X_CHO 14 `z0:A`;
  REWR 13;
  AND 14;
  EXISTS_TAC `z0:A`;
  REWRITE_TAC[IN_INTER];
  USE 13  (REWRITE_RULE[IN]);
  USE 13 (MATCH_MP open_ball_dist);
  CONJ_TAC;
  USE 8 (REWRITE_RULE [open_ball;SUBSET]);
  AND 8;
  USE 8 (SPEC `z0:A`);
  USE 8 (REWRITE_RULE [IN_ELIM_THM']);
  UND 8;
  DISCH_THEN (MATCH_MP_TAC  );
  ALL_TAC; (* "cd6" *)
  SUBCONJ_TAC;
  ASM SET_TAC[IN;SUBSET];
  DISCH_TAC;
  SUBCONJ_TAC;
  ASM SET_TAC[IN;SUBSET];
  DISCH_TAC;
  UND 13;
  UND 10;
  USE 0 (REWRITE_RULE[metric_space]);
  TYPEL_THEN [`z0`;`x`;`z0`] (fun t-> USE 0 (SPECL t));
  REWR 0;
  UND 0;
  REAL_ARITH_TAC;
  EXPAND_TAC "Z";
  REWRITE_TAC[IN_UNIONS;IN_IMAGE;IN_UNIV];
  UND 14;
  MESON_TAC[];
  ]);;

  (* }}} *)

let metric_hausdorff = prove_by_refinement(
  `! (X:A->bool) d. (metric_space(X,d))==>
    (hausdorff (top_of_metric(X,d)))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  REWRITE_TAC[hausdorff;];
  ASM_SIMP_TAC [GSYM top_of_metric_unions];
  DISCH_ALL_TAC;
  COPY 0;
  USE 4 (REWRITE_RULE[metric_space]);
  TYPEL_THEN [`x`;`y`;`x`] (USE 4 o SPECL);
  REWR 4;
  TYPE_THEN  `r = d x y` ABBREV_TAC;
  SUBGOAL_TAC `&.0 <. r`;
  UND 4;
  ARITH_TAC;
  DISCH_TAC;
  TYPE_THEN  `open_ball(X,d) x (r/(&.2))`   EXISTS_TAC;
  TYPE_THEN  `open_ball(X,d) y (r/(&.2))`   EXISTS_TAC;
  ALL_TAC; (* mh1 *)
  KILL 4;
  ASM_SIMP_TAC[open_ball_open];
  COPY 6;
  USE 4 (ONCE_REWRITE_RULE[GSYM REAL_LT_HALF1]);
  ASM_SIMP_TAC[REWRITE_RULE[IN] open_ball_nonempty];
  PROOF_BY_CONTR_TAC;
  USE 7 (REWRITE_RULE[EMPTY_EXISTS]);
  CHO 7;
  USE 7 (REWRITE_RULE[IN_INTER]);
  USE 7 (REWRITE_RULE[IN]);
  ALL_TAC; (* mh2 *)
  AND 7;
  COPY 7;
  COPY 8;
  USE 7 (MATCH_MP open_ball_dist);
  USE 8 (MATCH_MP open_ball_dist);
  USE 0 (REWRITE_RULE[metric_space]);
  COPY 0;
  TYPEL_THEN [`x`;`u`;`y`] (fun t-> (USE 0 (ISPECL t)));
  TYPEL_THEN [`y`;`u`;`y`] (fun t-> (USE 11 (ISPECL t)));
  UND 11;
  UND 0;
  ASM_REWRITE_TAC[];
  TYPE_THEN `X u` SUBGOAL_TAC;
  ASM_MESON_TAC[ open_ball_subset;IN;SUBSET];
  DISCH_THEN (REWRT_TAC);
  DISCH_ALL_TAC;
  UND 14;
  UND 0;
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  JOIN 7 8;
  USE 0 (MATCH_MP (REAL_ARITH `(a <. c) /\ (b < c) ==> b+a < c + c`));
  USE 0 (CONV_RULE REDUCE_CONV);
  ASM_MESON_TAC[real_lt];
  ]);;

  (* }}} *)

(* compactness *)

let compact = euclid_def `compact U (K:A->bool) <=>
     (K SUBSET UNIONS U) /\ (!V. (K SUBSET UNIONS V ) /\ (V SUBSET U) ==>
        (?W. (W SUBSET V) /\ (FINITE W) /\ (K SUBSET UNIONS W )))`;;

let closed_compact = prove_by_refinement(
  `!U K (S:A->bool). ((topology_ U) /\ (compact U K) /\
     (closed_ U S) /\ (S SUBSET K)) ==> (compact U S)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[compact];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  SUBCONJ_TAC;
  ASM_MESON_TAC[ SUBSET_TRANS];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `A = UNIONS U DIFF S` ABBREV_TAC;
  TYPE_THEN `open_ U A` SUBGOAL_TAC ;
  ASM_MESON_TAC[ closed_open];
  TYPE_THEN `V' = (A INSERT V)` ABBREV_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `V'` (USE 2 o SPEC);
  ALL_TAC; (* cc1 *)
  TYPE_THEN `K SUBSET UNIONS V'` SUBGOAL_TAC;
  EXPAND_TAC "V'";
  EXPAND_TAC "A";
  UND 6;
  UND 4;
  UND  1;
  TYPE_THEN `X = UNIONS U ` ABBREV_TAC;
  ALL_TAC; (* cc2 *)
  REWRITE_TAC[SUBSET_UNIONS_INSERT];
  SET_TAC[SUBSET;UNIONS;DIFF];
  DISCH_ALL_TAC;
  TYPE_THEN `V' SUBSET U` SUBGOAL_TAC;
  EXPAND_TAC "V'";
  EXPAND_TAC "A";
  REWRITE_TAC[INSERT_SUBSET];
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[IN;open_DEF];
  DISCH_ALL_TAC;
  REWR 2;
  CHO 2;
  TYPE_THEN `W DELETE A` EXISTS_TAC;
  CONJ_TAC;
  AND 2;
  UND 13;
  EXPAND_TAC "V'";
  SET_TAC[SUBSET;INSERT;DELETE];
  ASM_REWRITE_TAC[FINITE_DELETE];
  AND 2;
  AND 2;
  UND 2;
  UND 4;
  UND 1;
  EXPAND_TAC "A";
  TYPE_THEN `X = UNIONS U ` ABBREV_TAC;
  ALL_TAC; (* cc3 *)
  DISCH_ALL_TAC;
  MATCH_MP_TAC  UNIONS_DELETE2;
  CONJ_TAC;
  ASM_MESON_TAC[SUBSET_TRANS];
  SET_TAC[INTER;DIFF];
  ]);;
  (* }}} *)


let compact_closed = prove_by_refinement(
  `!U (K:A->bool). (topology_ U) /\ (hausdorff U) /\ (compact U K) ==>
     (closed_ U K)`,
  (* {{{ proof *)

  [
   REWRITE_TAC[hausdorff;compact;closed];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[open_DEF];
  ONCE_ASM_SIMP_TAC[open_nbd];
  TYPE_THEN `C = UNIONS U DIFF K` ABBREV_TAC;
  GEN_TAC;
  CONV_TAC (quant_right_CONV "B");
  DISCH_ALL_TAC;
  (* cc1 *)
  TYPE_THEN `!y. (K y) ==> (?A B. (U A /\ U B /\ A x /\ B y /\ (A INTER B = {})))` SUBGOAL_TAC;
  DISCH_ALL_TAC;
  UND 1;
  DISCH_THEN MATCH_MP_TAC;
  CONJ_TAC;
  UND 5;
  EXPAND_TAC "C";
  REWRITE_TAC[DIFF;IN_ELIM_THM'];
  REWRITE_TAC [IN];
  MESON_TAC[];
  CONJ_TAC;
  UND 6;
  UND 2;
  REWRITE_TAC[SUBSET;IN];
  MESON_TAC[];
  PROOF_BY_CONTR_TAC;
  REWR 1;
  REWR 5;
  UND 5;
  UND 6;
  EXPAND_TAC "C";
  REWRITE_TAC[DIFF;IN_ELIM_THM'];
  MESON_TAC[IN];
  (* cc2 *)
  DISCH_ALL_TAC;
  USE 6 (CONV_RULE (quant_left_CONV "B"));
  USE 6 (CONV_RULE (quant_left_CONV "B"));
  USE 6 (CONV_RULE (quant_left_CONV "B"));
  CHO 6;
  TYPE_THEN `IMAGE B K` (USE 3 o SPEC);
  TYPE_THEN `K SUBSET UNIONS (IMAGE B K) /\ IMAGE B K SUBSET U` SUBGOAL_TAC;
  CONJ_TAC;
  REWRITE_TAC[SUBSET;UNIONS;IN_IMAGE;IN_ELIM_THM'];
  X_GEN_TAC `y:A`;
  REWRITE_TAC[IN];
  ASM_MESON_TAC[];
  REWRITE_TAC[SUBSET;IN_IMAGE];
  NAME_CONFLICT_TAC;
  CONV_TAC (quant_left_CONV "x'");
  CONV_TAC (quant_left_CONV "x'");
  ASM_MESON_TAC[IN];
  DISCH_TAC;
  REWR 3;
  CHO 3;
  (* cc3 *)
  AND 3;
  AND 3;
  JOIN 8 9;
  USE 8 (MATCH_MP finite_subset);
  X_CHO 8 `kc:A->bool`;
  USE 6 (CONV_RULE (quant_left_CONV "A"));
  USE 6 (CONV_RULE (quant_left_CONV "A"));
  CHO 6;
  (* cc4 *)
  TYPE_THEN  `K = EMPTY` ASM_CASES_TAC;
  REWR 4;
  USE 4 (REWRITE_RULE[DIFF_EMPTY]);
  EXISTS_TAC `C:A->bool`;
  ASM_REWRITE_TAC[SUBSET_REFL];
  EXPAND_TAC "C";
  USE 0 (REWRITE_RULE[topology]);
  UND 0;
  MESON_TAC[topology;IN;SUBSET_REFL];
  TYPE_THEN `~(kc = EMPTY)` SUBGOAL_TAC;
  PROOF_BY_CONTR_TAC;
  USE 10 (REWRITE_RULE[]);
  REWR 8;
  USE 8 (REWRITE_RULE[IMAGE_CLAUSES]);
  REWR 3;
  USE 3 (REWRITE_RULE[UNIONS_0;SUBSET_EMPTY]);
  ASM_MESON_TAC[ ];
  REWRITE_TAC[EMPTY_EXISTS];
  DISCH_THEN CHOOSE_TAC;
  ALL_TAC; (* cc5 *)
  TYPE_THEN `INTERS (IMAGE A kc)` EXISTS_TAC;
  TYPE_THEN `INTERS (IMAGE A kc) INTER (UNIONS (IMAGE B kc)) = EMPTY` SUBGOAL_TAC;
  REWRITE_TAC[INTER;UNIONS];
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM';EMPTY];
  MATCH_MP_TAC  (TAUT `(a ==> ~b )==> ~(a /\ b)`);
  REWRITE_TAC[IN_INTERS;IN_IMAGE];
  DISCH_ALL_TAC;
  CHO 11;
  AND 11;
  CHO 13;
  IN_ELIM 13;
  REWR 11;
  USE  12 (CONV_RULE (quant_left_CONV "x"));
  USE  12 (CONV_RULE (quant_left_CONV "x"));
  TYPE_THEN `x''` (USE 12 o SPEC);
  TYPE_THEN `A x''` (USE 12 o SPEC);
  IN_ELIM 12;
  REWR 12;
  TYPE_THEN `x''` (USE 6 o SPEC);
  TYPE_THEN `K x''` SUBGOAL_TAC;
  UND 13;
  AND 8;
  UND 13;
  MESON_TAC[SUBSET;IN];
  DISCH_TAC;
  REWR 6;
  USE 6 (REWRITE_RULE [INTER]);
  (AND 6);
  (AND 6);
  (AND 6);
  (AND 6);
  USE 6 (fun t-> AP_THM t `x':A`);
  USE 6 (REWRITE_RULE[IN_ELIM_THM';EMPTY]);
  ASM_MESON_TAC[IN];
  DISCH_TAC;
  ALL_TAC; (* cc6 *)
  SUBCONJ_TAC;
  EXPAND_TAC "C";
  REWRITE_TAC[DIFF_SUBSET];
  CONJ_TAC;
  MATCH_MP_TAC  INTERS_SUBSET2;
  TYPE_THEN `A u` EXISTS_TAC ;
  REWRITE_TAC[IMAGE;IN_ELIM_THM'];
  CONJ_TAC;
  TYPE_THEN `u` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC  sub_union;
  TYPE_THEN `u` (USE 6 o SPEC);
  AND 8;
  USE 12 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[IN];
  UND 3;
  ASM_REWRITE_TAC[];
  UND 11;
  TYPE_THEN `a' = INTERS (IMAGE A kc)` ABBREV_TAC;
  TYPE_THEN `b' = UNIONS (IMAGE B kc)` ABBREV_TAC;
  SET_TAC[INTER;SUBSET;EMPTY];
  DISCH_TAC;
  ALL_TAC; (* cc7 *)
  CONJ_TAC;
  REWRITE_TAC[INTERS;IN_IMAGE;IN_ELIM_THM'];
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  TYPE_THEN `x'` (USE 6 o SPEC);
  ASM_REWRITE_TAC[];
  USE 8 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[IN];
  MATCH_MP_TAC  open_inters;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE;];
  NAME_CONFLICT_TAC;
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  USE 6 (SPEC `x'':A`);
  USE 8 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[IN];
  CONJ_TAC;
  ASM_MESON_TAC[FINITE_IMAGE];
  REWRITE_TAC[EMPTY_EXISTS];
  TYPE_THEN `A u` EXISTS_TAC;
  REWRITE_TAC[IN_IMAGE];
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let compact_totally_bounded = prove_by_refinement(
  `!(X:A->bool) d.( metric_space(X,d)) /\ (compact (top_of_metric(X,d)) X)
    ==> (totally_bounded (X,d))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[totally_bounded;compact];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  CONV_TAC (quant_right_CONV "B");
  DISCH_TAC;
  TYPE_THEN `IMAGE (\x. open_ball(X,d) x eps) X` (USE 2 o SPEC);
  TYPE_THEN `X SUBSET UNIONS (IMAGE (\x. open_ball (X,d) x eps) X)` SUBGOAL_TAC;
  (REWRITE_TAC[SUBSET;IN_UNIONS;IN_IMAGE]);
  GEN_TAC;
  NAME_CONFLICT_TAC;
  REWRITE_TAC[IN];
  DISCH_TAC;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x'");
  TYPE_THEN `x` EXISTS_TAC;
  TYPE_THEN `open_ball (X,d) x eps` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[open_ball_nonempty;IN];
  DISCH_TAC;
  REWR 2;
  ALL_TAC; (* ctb1 *)
  TYPE_THEN `IMAGE (\x. open_ball (X,d) x eps) X SUBSET top_of_metric (X,d)` SUBGOAL_TAC;
  TYPE_THEN `IMAGE (\x. open_ball (X,d) x eps) X SUBSET open_balls(X,d)` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE;open_balls;IN_ELIM_THM'];
  MESON_TAC[IN];
  MESON_TAC[SUBSET_TRANS;top_of_metric_open_balls];
  DISCH_TAC;
  REWR 2;
  CHO 2;
  TYPE_THEN `W` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  DISCH_ALL_TAC;
  AND 2;
  USE  7 (REWRITE_RULE [SUBSET;IN_IMAGE]);
  ASM_MESON_TAC[IN];
  MATCH_MP_TAC  SUBSET_ANTISYM;
  ASM_REWRITE_TAC[];
  TYPE_THEN `W SUBSET top_of_metric (X,d)` SUBGOAL_TAC;
  ASM_MESON_TAC[SUBSET_TRANS];
  DISCH_ALL_TAC;
  USE 6 (MATCH_MP UNIONS_UNIONS);
  ASM_MESON_TAC[top_of_metric_unions];
  ]);;
  (* }}} *)

(*
   If W is empty then INTERS W = UNIV, rather than EMPTY.
   Thus, extra arguments must be provided for this case. *)

let finite_inters = prove_by_refinement(
  `!U V . (topology_ U) /\ (compact U (UNIONS U)) /\ (INTERS V = EMPTY) /\
        (!(u:A->bool). (V u) ==> (closed_ U u))
    ==> (?W. (W SUBSET V) /\ (FINITE W) /\ (INTERS W = EMPTY))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[compact;SUBSET_REFL];
  DISCH_ALL_TAC;
  (* {{{ proof *)

  TYPE_THEN `IMAGE (\r. ((UNIONS U) DIFF r)) V` (USE 1 o SPEC);
  TYPE_THEN `IMAGE (\r. UNIONS U DIFF r) V SUBSET U` SUBGOAL_TAC;
  REWRITE_TAC[IMAGE;SUBSET;IN_ELIM_THM'];
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[top_univ;IN;SUBSET_DIFF];
  IN_ELIM 4;
  TYPE_THEN `x'` (USE 3 o SPEC);
  REWR 3;
  USE 3 (REWRITE_RULE[closed;open_DEF]);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  REWR 1;
  ALL_TAC; (* fi1 *)
  TYPE_THEN `UNIONS U SUBSET UNIONS (IMAGE (\r. UNIONS U DIFF r) V)` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN_UNIONS;IN_IMAGE];
  GEN_TAC;
  DISCH_THEN CHOOSE_TAC;
  NAME_CONFLICT_TAC;
  USE 2 (REWRITE_RULE[INTERS_EQ_EMPTY]);
  TYPE_THEN `x` (USE 2 o SPEC);
  CHO 2;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x");
  TYPE_THEN `a` EXISTS_TAC;
  TYPE_THEN `UNIONS U DIFF a` EXISTS_TAC ;
  ASM_REWRITE_TAC[IN];
  REWRITE_TAC[DIFF;IN_ELIM_THM';IN_UNIONS];
  ASM_MESON_TAC[IN];
  DISCH_TAC;
  REWR 1;
  CHO 1;
  AND 1;
  AND 1;
  JOIN 7 6;
(*** Modified by JRH for changed theorem name
  USE 6 (MATCH_MP FINITE_SUBSET_IMAGE);
 ****)
  USE 6 (MATCH_MP FINITE_SUBSET_IMAGE_IMP);
  CHO 6;
  ALL_TAC; (* fi2*)
  TYPE_THEN `s'={}` ASM_CASES_TAC ;
  REWR 6;
  USE  6 (REWRITE_RULE[IMAGE_CLAUSES;SUBSET_EMPTY]);
  REWR 1;
  USE 1 (REWRITE_RULE[UNIONS_0;SUBSET_EMPTY]);
  USE 1 (REWRITE_RULE [UNIONS_EQ_EMPTY]);
  UND 1;
  DISCH_THEN DISJ_CASES_TAC;
  REWR 4;
  USE 4 (REWRITE_RULE[SUBSET_EMPTY;IMAGE;EQ_EMPTY;IN_ELIM_THM']);
  TYPE_THEN `V = {}` SUBGOAL_TAC;
  PROOF_BY_CONTR_TAC;
  USE 8 (REWRITE_RULE[EMPTY_EXISTS]);
  CHO 8;
  USE 4 (CONV_RULE (quant_left_CONV "x'"));
  USE 4 (CONV_RULE (quant_left_CONV "x'"));
  TYPE_THEN `u` (USE 4 o SPEC);
  TYPE_THEN `UNIONS {} DIFF u` (USE 4 o SPEC);
  ASM_MESON_TAC[];
  USE 2 (REWRITE_RULE[INTERS_EQ_EMPTY]);
  REWRITE_TAC[EQ_EMPTY];
  ASM_MESON_TAC[];
  ALL_TAC; (* fi3*)
  TYPE_THEN `V` EXISTS_TAC;
  ASM_REWRITE_TAC[SUBSET_REFL];
  USE 3 (REWRITE_RULE[closed;open_DEF]);
  REWR 3;
  USE 3 (REWRITE_RULE[REWRITE_RULE[IN] IN_SING]);
  TYPE_THEN `!u. V u ==> (u = EMPTY)` SUBGOAL_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `u` (USE 3 o SPEC);
  REWR 3;
  AND 3;
  ASM_MESON_TAC[ SUBSET_EMPTY;UNIONS_EQ_EMPTY];
  DISCH_TAC;
  TYPE_THEN `V SUBSET {EMPTY}` SUBGOAL_TAC;
  REWRITE_TAC[INSERT_DEF];
  REWRITE_TAC[IN_ELIM_THM'];
  REWRITE_TAC[IN;EMPTY;SUBSET];
  ASM_MESON_TAC[IN;EMPTY];

  (* }}} *)
  MESON_TAC[FINITE_SING;FINITE_SUBSET];
  ALL_TAC; (* fi4*)
  TYPE_THEN `s'` EXISTS_TAC;
  ASM_REWRITE_TAC[INTERS_EQ_EMPTY];
  GEN_TAC;
  USE 7 (REWRITE_RULE[EMPTY_EXISTS]);
  CHO 7;
  TYPE_THEN `UNIONS U x` ASM_CASES_TAC ;
  TYPE_THEN `UNIONS W x` SUBGOAL_TAC;
  USE 1 (REWRITE_RULE[SUBSET;IN]);
  UND 8;
  UND 1;
  MESON_TAC[];
  DISCH_ALL_TAC;
  TYPE_THEN `UNIONS (IMAGE (\r. UNIONS U DIFF r) s') x` SUBGOAL_TAC;
  AND 6;
  AND 6;
  USE 6 (MATCH_MP UNIONS_UNIONS);
  USE 6 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[];
  REWRITE_TAC[UNIONS;IN_IMAGE;IN_ELIM_THM'];
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  LEFT 10 "x";
  LEFT 10 "x";
  TYPE_THEN `S:A->bool` (X_CHO 10) ;
  CHO 10;
  AND 10;
  REWR 10;
  TYPE_THEN `S` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  USE 10(REWRITE_RULE[REWRITE_RULE[IN] IN_DIFF]);
  ASM_REWRITE_TAC[];
  TYPE_THEN `u` EXISTS_TAC;
  IN_ELIM 7;
  ASM_REWRITE_TAC[];
  PROOF_BY_CONTR_TAC;
  USE 9 (REWRITE_RULE[]);
  TYPE_THEN `V u` SUBGOAL_TAC;
  AND 6;
  AND 6;
  USE 11 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[];
  DISCH_TAC;
  H_MATCH_MP (HYP "3") (HYP "10");
  USE 11(REWRITE_RULE[closed;open_DEF]);
  USE 11 (REWRITE_RULE [SUBSET;IN]);
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)


(* first part of the proof of cauchy_subseq *)
let cauchy_subseq_sublemma = prove_by_refinement(
  `!(X:A->bool) d f. ((metric_space(X,d))/\(totally_bounded(X,d)) /\
        (sequence X f)) ==>
    (?R Cn sn cond.
       (&0 < R) /\
       (!x y. X x /\ X y ==> d x y < R) /\
       (cond (X,0) 0) /\
       (sn 0 = 0) /\ (Cn 0 = X) /\
       (!n. Cn n SUBSET X /\ cond (Cn n,sn n) n) /\
       (!n. Cn (SUC n) SUBSET Cn n /\ sn n <| sn (SUC n)) /\
       (((\ (C,s). \n.
            (~FINITE {j | C (f j)}) /\
            (C (f s)) /\
           (!x y. (C x /\ C y) ==> d x y < R * (twopow (--: (&:n))))) =
       cond)
    ))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  COPY 0 THEN COPY 1;
  JOIN 4 3;
  USE 3 (MATCH_MP totally_bounded_bounded);
  CHO 3;
  CHO 3;
  ALL_TAC; (* {{{ xxx *)
  ALL_TAC; (* make r pos *)
  ASSUME_TAC (REAL_ARITH `r <. (&.1 + abs(r))`);
  ASSUME_TAC (REAL_ARITH `&.0 <. (&.1 + abs(r))`);
  ABBREV_TAC (`r' = &.1 +. abs(r)`);
  SUBGOAL_TAC `open_ball(X,d) a r SUBSET open_ball(X,d) (a:A) r'`;
  ASM_SIMP_TAC[open_ball_nest];
  DISCH_TAC;
  JOIN 3 7;
  USE 3 (MATCH_MP SUBSET_TRANS);
  KILL 6;
  KILL 4;
  ALL_TAC; (* "cs1" *)
  SUBGOAL_TAC `( !(x:A) y.  (X x) /\ (X y) ==> (d x y <. &.2 *. r'))`;
  DISCH_ALL_TAC;
  USE 3 (REWRITE_RULE[SUBSET;IN]);
  COPY 3;
  USE 7 (SPEC `x:A`);
  USE 3 (SPEC `y:A`);
  H_MATCH_MP (HYP "3") (HYP "6");
  H_MATCH_MP (HYP "7") (HYP "4");
  JOIN 9 8;
  JOIN 0 8;
  USE 0 (MATCH_MP BALL_DIST);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ABBREV_TAC `cond = (\ ((C:A->bool),(s:num)) n. ~FINITE{j| C (f j)} /\ (C(f s)) /\ (!x y. (C x /\ C y) ==> d x y <. (&.2*.r')*. twopow(--: (&:n))))`;
  ABBREV_TAC `R = (&.2)*r'`;
  ALL_TAC ; (* 0 case of recursio *)
  ALL_TAC; (* cs2 *)
  SUBGOAL_TAC ` (X SUBSET X) /\ (cond ((X:A->bool),0) 0)`;
  REWRITE_TAC[SUBSET_REFL];
  EXPAND_TAC "cond";
  CONV_TAC (TOP_DEPTH_CONV  GEN_BETA_CONV);
  USE 2 (REWRITE_RULE[sequence;SUBSET;IN_IMAGE;IN_UNIV]);
  USE 2 (REWRITE_RULE[IN]);
  USE 2 (CONV_RULE (NAME_CONFLICT_CONV));
  SUBGOAL_TAC `!x. X((f:num->A) x)`;
  ASM_MESON_TAC[];
  REDUCE_TAC;
  REWRITE_TAC[TWOPOW_0] THEN REDUCE_TAC;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  SUBGOAL_TAC `{ j | (X:A->bool) (f j) } = (UNIV:num->bool)`;
  MATCH_MP_TAC EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM;UNIV];
  ASM_REWRITE_TAC[];
  DISCH_THEN REWRT_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[num_infinite];
  ALL_TAC; (* #save_goal "cs3" *)
  SUBGOAL_TAC `&.0 <. R`;
  EXPAND_TAC "R";
  UND 5;
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_TAC `!cs n. ?cs' . (FST cs SUBSET X) /\ (cond cs n)==>( (FST cs' SUBSET (FST cs)) /\(SND cs <| ((SND:((A->bool)#num)->num) cs') /\ (cond cs' (SUC n))) )`;
  DISCH_ALL_TAC;
  CONV_TAC (quant_right_CONV "cs'");
  DISCH_TAC;
  AND 11;
  H_REWRITE_RULE[GSYM o (HYP "6")] (HYP "11");
  USE 13 (CONV_RULE (SUBS_CONV[GSYM(ISPEC `cs:(A->bool)#num` PAIR)]));
  USE 13 (CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV));
  JOIN 10 13;
  JOIN 12 10;
  JOIN 2 10;
  JOIN 1 2;
  JOIN 0 1;
  USE 0 (MATCH_MP subsequence_rec);
  CHO 0;
  CHO 0;
  EXISTS_TAC `(C':A->bool,s':num)`;
  ASM_REWRITE_TAC[FST;SND];
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ALL_TAC; (* "cs4" *)
  USE 11 (REWRITE_RULE[SKOLEM_THM]);
  CHO 11;
  ASSUME_TAC (ISPECL[`((X:A->bool),0)`;`cs':(((A->bool)#num)->(num->(A->bool)#num))`] num_RECURSION);
  CHO 12;
  ALL_TAC;(* EXISTS_TAC `\i. (SND ((fn : num->(A->bool)#num) i))`; *)
  USE 11 (CONV_RULE (quant_left_CONV "n"));
  USE 11 (SPEC `n:num`);
  USE 11 (SPEC `(fn:num->(A->bool)#num) n`);
  AND 12;
  H_REWRITE_RULE[GSYM o (HYP "12")] (HYP "11");
  USE 14 (GEN_ALL);
  ABBREV_TAC `sn = (\i. SND ((fn:num->(A->bool)#num) i))`;
  ABBREV_TAC `Cn = (\i. FST ((fn:num->(A->bool)#num) i))`;
  SUBGOAL_TAC `((sn:num->num) 0 = 0) /\ (Cn 0 = (X:A->bool))`;
  EXPAND_TAC "sn";
  EXPAND_TAC "Cn";
  UND 13;
  MESON_TAC[FST;SND];
  DISCH_TAC;
  KILL 13;
  KILL 11;
  SUBGOAL_TAC `!(n:num). ((fn n):(A->bool)#num) = (Cn n,sn n)`;
  EXPAND_TAC "sn";
  EXPAND_TAC "Cn";
  REWRITE_TAC[PAIR];
  DISCH_TAC;
  H_REWRITE_RULE[(HYP "11")] (HYP"14");
  KILL 12;
  KILL 14;
  KILL 11;
  KILL 16;
  KILL 15;
  ALL_TAC; (* }}} *)
  ALL_TAC; (* KILL 10; cs4m *)
  KILL 8;
  KILL 7;
  KILL 3;
  KILL 5;
  ALL_TAC; (* cs5 *)
  TYPE_THEN `!n. (Cn n SUBSET X) /\ (cond (Cn n,sn n) n)` SUBGOAL_TAC;
  INDUCT_TAC;
  ASM_REWRITE_TAC[];
  SET_TAC[SUBSET];
  USE 13 (SPEC `n:num`);
  REWR 5;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[SUBSET_TRANS];
  DISCH_TAC;
  REWR 13;
  ALL_TAC; (* TO HERE EVERYTHING WORKS GENERALLY *)
  TYPE_THEN `R` EXISTS_TAC;
  TYPE_THEN `Cn` EXISTS_TAC;
  TYPE_THEN `sn` EXISTS_TAC;
  TYPE_THEN `cond` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

(* more on metric spaces and topology *)

let subseq_cauchy = prove_by_refinement(
  `!(X:A->bool) d f s. (metric_space(X,d)) /\
    (cauchy_seq (X,d) f) /\ (subseq s) /\
    (converge(X,d) (f o s)) ==> (converge(X,d) f)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[cauchy_seq;converge;sequence_in];
  DISCH_ALL_TAC;
  CHO 4;
  TYPE_THEN `x` EXISTS_TAC ;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  AND 4;
  TYPE_THEN `eps/(&.2)` (USE 2 o SPEC);
  TYPE_THEN `eps/(&.2)` (USE 4 o SPEC);
  CHO 4;
  CHO 2;
  CONV_TAC (quant_right_CONV "n");
  DISCH_ALL_TAC;
  USE 2 (REWRITE_RULE[REAL_LT_HALF1]);
  USE 4 (REWRITE_RULE[REAL_LT_HALF1]);
  REWR 2;
  REWR 4;
  TYPE_THEN `n'` EXISTS_TAC ;
  DISCH_ALL_TAC;
  TYPE_THEN `n +| n'` (USE 4 o SPEC);
  USE 4 (REWRITE_RULE[ARITH_RULE `n  <=| n +| n'`]);
  TYPE_THEN `s(n +| n')` (USE 2 o SPEC);
  TYPE_THEN `i` (USE 2 o SPEC);
  TYPE_THEN `n' <=| s (n +| n')` SUBGOAL_TAC;
  USE 3 (MATCH_MP SEQ_SUBLE);
  TYPE_THEN `n +| n'` (USE 3 o SPEC);
  ASM_MESON_TAC[ LE_TRANS; ARITH_RULE `n' <=| n +| n'`];
  DISCH_TAC;
  REWR 2;
  USE 4 (REWRITE_RULE[o_DEF]);
  (* save_goal"sc1"; *)
  TYPEL_THEN [`X`;`d`;`x`;`f (s(n +| n'))`;`f i`] (fun t-> ASSUME_TAC (ISPECL t metric_space_triangle));
  USE 5 (REWRITE_RULE[IN]);
  REWR 9;
  USE 1 (MATCH_MP sequence_in);
  REWR 9;
  UND 9;
  UND 4;
  UND 2;
  MP_TAC (SPEC `eps:real` REAL_HALF_DOUBLE);
  TYPE_THEN `a = d (f (s (n +| n'))) (f i)` ABBREV_TAC ;
  TYPE_THEN `b = d x (f (s (n +| n')))` ABBREV_TAC ;
  TYPE_THEN `c = d x (f i)` ABBREV_TAC ;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let compact_complete = prove_by_refinement(
  `!(X:A->bool) d. metric_space(X,d) /\
     (compact (top_of_metric(X,d)) X) ==>
     (complete(X,d))`,
  (* {{{ proof *)

  [
  REWRITE_TAC [complete];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  COPY 0;
  COPY 1;
  JOIN 3 4;
  USE 3 (MATCH_MP compact_totally_bounded);
  COPY 2;
  USE 4 (REWRITE_RULE[cauchy_seq]);
  AND 4;
  COPY 0;
  COPY 3;
  COPY 5;
  JOIN 7 8;
  JOIN 6 7;
  USE 6 (MATCH_MP cauchy_subseq_sublemma);
  CHO 6;
  CHO 6;
  CHO 6;
  CHO 6;
  (AND 6);
  (AND 6);
  (AND 6);
  (AND 6);
  (AND 6);
  (AND 6);
  (AND 6);
  ALL_TAC ; (* cc1 *)
  MATCH_MP_TAC subseq_cauchy;
  TYPE_THEN `sn` EXISTS_TAC;
  ASM_REWRITE_TAC [converge];
  SUBCONJ_TAC;
  REWRITE_TAC[SUBSEQ_SUC];
  ASM_MESON_TAC[ ];
  DISCH_ALL_TAC;
  TYPE_THEN `~(INTERS {z | ?n. z = closed_ball(X,d) (f (sn n)) (R* twopow(--: (&:n)))} =EMPTY)` SUBGOAL_TAC;
  PROOF_BY_CONTR_TAC ;
  REWR 15;
  TYPEL_THEN [`top_of_metric(X,d)`;`{z | ?n. z = closed_ball (X,d) (f(sn n)) (R * twopow (--: (&:n)))}`] (fun t-> ASSUME_TAC (ISPECL t finite_inters));
  REWR 16;
  TYPE_THEN `topology_ (top_of_metric (X,d)) /\ compact (top_of_metric (X,d)) (UNIONS (top_of_metric (X,d))) /\ (!u. {z | ?n. z = closed_ball (X,d) (f(sn n)) (R * twopow (--: (&:n)))} u ==> closed_ (top_of_metric (X,d)) u)` SUBGOAL_TAC ;
  ASM_SIMP_TAC[GSYM top_of_metric_unions;];
  ASM_SIMP_TAC[top_of_metric_top];
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[closed_ball_closed];
  DISCH_TAC;
  REWR 16;
  CHO 16;
  ALL_TAC ; (* cc2 *)
  TYPE_THEN `{z | ?n. z = closed_ball (X,d) (f (sn n)) (R * twopow (--: (&:n)))} = IMAGE (\n. closed_ball (X,d) (f (sn n)) (R * twopow (--: (&:n)))) (UNIV)` SUBGOAL_TAC ;
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC ;
  REWRITE_TAC[IN_ELIM_THM';INR IN_IMAGE;UNIV];
  DISCH_TAC;
  REWR 16;
  AND 16;
  AND 16;
  JOIN 20 19;
(*** Modified by JRH for new theorem name
  USE 19 (MATCH_MP FINITE_SUBSET_IMAGE);
 ***)
  USE 19 (MATCH_MP FINITE_SUBSET_IMAGE_IMP);
  CHO 19;
  AND 19;
  AND 19;
(*** JRH --- originally for implicational num_FINITE:
  USE 20 (MATCH_MP num_FINITE);
 ***)
  USE 20 (CONV_RULE (REWR_CONV num_FINITE));
  CHO 20;
  TYPE_THEN `f (sn a) IN (INTERS W)` SUBGOAL_TAC ;
  REWRITE_TAC[IN_INTERS];
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  USE 19 (REWRITE_RULE [SUBSET;IN_IMAGE]);
  TYPE_THEN `t` (USE 19 o SPEC);
  USE 19 (REWRITE_RULE [IN]);
  REWR 19;
  X_CHO 19 `m:num`;
  USE 20 (SPEC `m:num`);
  USE 20 (REWRITE_RULE[IN]);
  REWR 20;
  TYPE_THEN `Cn m SUBSET closed_ball (X,d) (f (sn m)) (R * twopow (--: (&:m)))` SUBGOAL_TAC ;
  REWRITE_TAC[SUBSET;closed_ball;IN_ELIM_THM'];
  USE 12 (SPEC `m:num`);
  UND 12;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  REWRITE_TAC[SUBSET];
  MESON_TAC[IN;REAL_ARITH `x <. y ==> x <=. y`];
  REWRITE_TAC[SUBSET;IN];
  DISCH_THEN (MATCH_MP_TAC  );
  ALL_TAC ; (* cc3 *)
  TYPE_THEN `Cn a SUBSET Cn m` SUBGOAL_TAC ;
  UND 13;
  UND 20;
  MESON_TAC [SUBSET_SUC2];
  REWRITE_TAC[SUBSET;IN];
  DISCH_THEN (MATCH_MP_TAC  );
  USE 12 (SPEC `a:num`);
  AND 12;
  UND 12;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  MESON_TAC[];
  ASM_REWRITE_TAC [NOT_IN_EMPTY];
  DISCH_TAC;
  ALL_TAC ; (* cc4 *)
  USE 15 (REWRITE_RULE[EMPTY_EXISTS]);
  CHO 15;
  TYPE_THEN `u` EXISTS_TAC ;
  REWRITE_TAC[IN];
  SUBCONJ_TAC;
  USE 15 (REWRITE_RULE [IN_INTERS]);
  TYPE_THEN `closed_ball (X,d) (f (sn 0)) (R * twopow (--: (&:0)))` (USE 15 o SPEC);
  USE 15 (REWRITE_RULE[IN_ELIM_THM']);
  LEFT 15 "n";
  TYPE_THEN `0` (USE 15 o SPEC);
  USE 15 (REWRITE_RULE[IN;closed_ball]);
  USE 15 (REWRITE_RULE [IN_ELIM_THM']);
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  CONV_TAC (quant_right_CONV "n");
  DISCH_ALL_TAC;
  TYPEL_THEN [`(&.2)*R`;`eps`] (fun t-> ASSUME_TAC (ISPECL t twopow_eps));
  CHO 18;
  REWR 18;
  TYPE_THEN `n` EXISTS_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `&0 < &2 * R ` SUBGOAL_TAC;
  MATCH_MP_TAC  REAL_PROP_POS_MUL2;
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  DISCH_ALL_TAC;
  REWR 18;
  UND 18;
  MATCH_MP_TAC  (REAL_ARITH `x <= a ==> ((a < b) ==> (x < b))`);
  USE 15 (REWRITE_RULE[IN_INTERS]);
  TYPE_THEN `closed_ball (X,d) (f (sn n)) (R * twopow (--: (&:n)))` (USE 15 o SPEC);
  USE 15 (REWRITE_RULE[IN_ELIM_THM']);
  LEFT 15 "n'";
  USE 15 (SPEC `n:num`);
  REWR 15;
  TYPE_THEN `Cn n SUBSET closed_ball (X,d) (f (sn n)) (R * twopow (--: (&:n)))`  SUBGOAL_TAC ;
  REWRITE_TAC[SUBSET;closed_ball;IN_ELIM_THM'];
  USE 12 (SPEC `n:num`);
  UND 12;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  REWRITE_TAC[SUBSET];
  MESON_TAC[IN;REAL_ARITH `x <. y ==> x <=. y`];
  DISCH_TAC;
  TYPE_THEN `Cn i SUBSET Cn n` SUBGOAL_TAC ;
  UND 13;
  UND 19;
  MESON_TAC [SUBSET_SUC2];
  ALL_TAC ; (* REWRITE_TAC[SUBSET;IN];*)
  DISCH_ALL_TAC;
  USE 12 (SPEC `i:num`);
  AND 12;
  UND 12;
  EXPAND_TAC "cond";
  (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));
  DISCH_ALL_TAC;
  TYPE_THEN `((f o sn) i)  IN closed_ball (X,d) (f (sn n)) (R * twopow (--: (&:n)))` SUBGOAL_TAC;
  KILL 1;
  KILL 0;
  KILL 2;
  KILL 3;
  KILL 5;
  KILL 4;
  JOIN  21 18;
  USE 0 (MATCH_MP SUBSET_TRANS);
  ALL_TAC; (* "CC5"; *)
  ASM_MESON_TAC[IN;o_DEF;SUBSET];
  REWRITE_TAC[GSYM REAL_MUL_ASSOC];
  UND 15;
  TYPE_THEN  `r = R * twopow (--: (&:n))` ABBREV_TAC;
  UND 0;
  REWRITE_TAC[IN];
  MESON_TAC[BALL_DIST_CLOSED];
  ]);;

  (* }}} *)

let countable_cover = prove_by_refinement(
  `!(X:A->bool) d U. (metric_space(X,d)) /\ (totally_bounded(X,d)) /\
       (X SUBSET (UNIONS U)) /\ (U SUBSET (top_of_metric(X,d))) ==>
     (?V. (V SUBSET U) /\ (X SUBSET (UNIONS V)) /\ (COUNTABLE V))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  TYPE_THEN `(?Z. COUNTABLE Z /\ dense (top_of_metric (X,d)) Z)` SUBGOAL_TAC;
  ASM_MESON_TAC[countable_dense];
  DISCH_ALL_TAC;
  CHO 4;
  TYPE_THEN  `S = {(z,n) | ?A. (Z z) /\ (open_ball(X,d) z (twopow(--: (&:n))) SUBSET A) /\ U A}` ABBREV_TAC ;
  TYPE_THEN `COUNTABLE S` SUBGOAL_TAC;
  IMATCH_MP_TAC  (INST_TYPE [`:A#num`,`:A`] COUNTABLE_IMAGE);
  TYPE_THEN `{(z,(n:num)) | (Z z) /\ (UNIV n)}` EXISTS_TAC ;
  CONJ_TAC ;
  IMATCH_MP_TAC  countable_prod;
  ASM_REWRITE_TAC [NUM_COUNTABLE];
  TYPE_THEN `I:(A#num) -> (A#num)` EXISTS_TAC;
  REWRITE_TAC[IMAGE_I;UNIV;SUBSET];
  IN_OUT_TAC;
  EXPAND_TAC "S";
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  ASM_MESON_TAC[GSPEC];
  DISCH_TAC;
  TYPE_THEN `!z n. (S (z,n) ==> ?A. Z z /\ open_ball (X,d) z (twopow (--: (&:n))) SUBSET A /\ U A)` SUBGOAL_TAC;
  EXPAND_TAC "S";
  REWRITE_TAC[IN_ELIM_THM'];
  DISCH_ALL_TAC;
  CHO 7;
  CHO 7;
  AND 7;
  CHO 8;
  TYPE_THEN `A` EXISTS_TAC;
  ASM_MESON_TAC[PAIR_EQ];
  DISCH_TAC ;
  LEFT 7 "A";
  LEFT 7 "A";
  LEFT 7 "A";
  CHO 7;
  ALL_TAC ; (* "cc1"; *)
  TYPE_THEN `IMAGE (\ (z,n). A z n) S` EXISTS_TAC;
  SUBCONJ_TAC ;
  REWRITE_TAC[SUBSET;IN_IMAGE];
  NAME_CONFLICT_TAC;
  TYPE_THEN `Azn:A->bool`  X_GEN_TAC;
  DISCH_THEN (X_CHOOSE_TAC `zn:A#num`);
  USE 8 (SUBS [(ISPEC `zn:A#num` (GSYM PAIR))]);
  USE 8 (GBETA_RULE);
  TYPE_THEN `z = FST zn`  ABBREV_TAC ;
  TYPE_THEN `n = SND zn`  ABBREV_TAC ;
  IN_OUT_TAC;
  ASM_MESON_TAC[];
  DISCH_TAC;
  CONJ_TAC ;
  REWRITE_TAC[SUBSET];
  USE 2 (REWRITE_RULE[SUBSET;IN_UNIONS]);
  IN_OUT_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `x` (  USE 6 o SPEC);
  REWR 6;
  CHO 6;
  TYPE_THEN `top_of_metric (X,d) t` SUBGOAL_TAC;
  AND 6;
  UND 10;
  UND 5;
  REWRITE_TAC[SUBSET;IN];
  MESON_TAC[];
  ASM_SIMP_TAC[top_of_metric_nbd];
  DISCH_ALL_TAC;
  TYPE_THEN `x` (USE 11 o SPEC);
  IN_OUT_TAC;
  REWR 0;
  CHO 0;
  AND 0;
  ASSUME_TAC (SPECL[`&.1`;`r:real`] twopow_eps);
  CHO 13;
  USE 13 (CONV_RULE REDUCE_CONV);
  REWR 13;
  TYPEL_THEN [`X`;`d`;`x`] (fun t-> USE 13 (MATCH_MP (SPECL t open_ball_nest)));
  JOIN 13 0;
  USE 0 (MATCH_MP SUBSET_TRANS);
  ASSUME_TAC (SPEC `(--: (&:n))` twopow_pos);
  WITH 3 (MATCH_MP top_of_metric_top);
  AND 7;
  COPY 7;
  COPY 14;
  JOIN  14 7;
  USE 7 (MATCH_MP dense_subset);
  UND 16;
  ASM_SIMP_TAC [dense_open];
  DISCH_TAC ;
  TYPE_THEN `(open_ball(X,d) x (twopow (--: (&:(n+1)))))` (USE 14 o SPEC);
  ALL_TAC ; (* "cc2"; *)
  TYPE_THEN `open_ball (X,d) x (twopow (--: (&:(n +| 1)))) x` SUBGOAL_TAC;
  IMATCH_MP_TAC  open_ball_nonempty;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  TYPE_THEN `?z. (Z z) /\ (open_ball(X,d) x (twopow (--: (&:(n+1)))) z)` SUBGOAL_TAC;
  UND 14;
  REWRITE_TAC[open_DEF];
  ASM_SIMP_TAC[open_ball_open];
  UND 16;
  TYPE_THEN `B = open_ball (X,d) x (twopow (--: (&:(n +| 1))))` ABBREV_TAC ;
  REWRITE_TAC[INTER;IN];
  POP_ASSUM_LIST (fun t->ALL_TAC);
  REWRITE_TAC[EMPTY_NOT_EXISTS];
  REWRITE_TAC[IN_ELIM_THM'];
  MESON_TAC[];
  DISCH_TAC;
  CHO 18;
  AND 18;
  WITH 3 (MATCH_MP top_of_metric_unions);
  USE 20 (SYM);
  REWR 7;
  TYPE_THEN `X z` SUBGOAL_TAC;
  UND 7;
  UND 19;
  MESON_TAC[SUBSET;IN];
  DISCH_TAC;
  TYPE_THEN `open_ball (X,d) z (twopow (--: (&:(n +| 1)))) x` SUBGOAL_TAC;
  ASM_MESON_TAC[ball_symm];
  DISCH_TAC;
  ALL_TAC ; (* "cc3"; *)
  REWRITE_TAC[UNIONS;IN_IMAGE;IN_ELIM_THM'];
  REWRITE_TAC[IN];
  LEFT_TAC "x";
  LEFT_TAC "x";
  TYPE_THEN `(z,n+1)` EXISTS_TAC;
  TYPE_THEN `A z (n+1)` EXISTS_TAC;
  GBETA_TAC;
  EXPAND_TAC "S";
  REWRITE_TAC[IN_ELIM_THM'];
  LEFT_TAC "z'";
  TYPE_THEN `z` EXISTS_TAC;
  LEFT_TAC "n'";
  TYPE_THEN `n + 1` EXISTS_TAC;
  REWRITE_TAC[];
  LEFT_TAC "A";
  TYPE_THEN `t` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ALL_TAC ; (* "cc4"; *)
  SUBCONJ_TAC ;
  TYPE_THEN `open_ball (X,d) z (twopow (--: (&:(n +| 1)))) SUBSET (open_ball (X,d) x (twopow (--: (&:n))))`  SUBGOAL_TAC ;
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [(GSYM twopow_double)]));
  IMATCH_MP_TAC  ball_subset_ball;
  ASM_REWRITE_TAC[];
  UND 0;
  MESON_TAC[SUBSET_TRANS];
  DISCH_TAC ;
  TYPEL_THEN [`z`;`n+1`] (fun t -> USE 10 (SPECL t));
  USE 10 (REWRITE_RULE [SUBSET ]);
  IN_OUT_TAC ;
  ALL_TAC ; (* "cc5" *)
  TYPE_THEN `S (z,n +| 1)` SUBGOAL_TAC ;
  EXPAND_TAC "S";
  REWRITE_TAC[IN_ELIM_THM' ];
  TYPE_THEN `z` EXISTS_TAC ;
  TYPE_THEN `n + 1` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `t` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_TAC ;
  REWR 13;
  AND  13;
  TYPE_THEN `x` (USE 25 o SPEC );
  UND 25;
  ASM_REWRITE_TAC[];
  TYPE_THEN `S` ( fun t-> IMATCH_MP_TAC  ( ISPEC t COUNTABLE_IMAGE)) ;
  ASM_REWRITE_TAC[];
  TYPE_THEN `\ (z,n). A z n` EXISTS_TAC;
  REWRITE_TAC[SUBSET_REFL ];
  ]);;

  (* }}} *)

let complete_compact = prove_by_refinement(
  `!(X:A->bool) d . (metric_space(X,d)) /\ (totally_bounded(X,d)) /\
  (complete (X,d)) ==> (compact (top_of_metric(X,d)) X)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[compact];
  CONJ_TAC ;
  UND 0;
  SIMP_TAC[GSYM   top_of_metric_unions ];
  REWRITE_TAC[SUBSET_REFL];
  GEN_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `(?V'. (V' SUBSET V) /\ (X SUBSET (UNIONS V')) /\ (COUNTABLE V'))` SUBGOAL_TAC ;
  IMATCH_MP_TAC  countable_cover;
  TYPE_THEN `d` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  DISCH_ALL_TAC;
  ALL_TAC; (* ASM_MESON_TAC[]; *)
  ALL_TAC; (* DISCH_THEN (CHOOSE_THEN MP_TAC); *)
  ALL_TAC; (* DISCH_ALL_TAC;  *)
  USE 7 (REWRITE_RULE[COUNTABLE;GE_C;UNIV]);
  IN_OUT_TAC;
  CHO 0;
  TYPE_THEN `B = \i. (IMAGE f { u | (u <=| i )  /\ V' (f u)}) ` ABBREV_TAC ;
  TYPE_THEN `?i . UNIONS (B i ) = X ` ASM_CASES_TAC;
  CHO 9;
  TYPE_THEN `B i ` EXISTS_TAC;
  EXPAND_TAC "B";
  CONJ_TAC;
  REWRITE_TAC[IMAGE;SUBSET ;IN  ];
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  UND 2;
  REWRITE_TAC[SUBSET;IN ];
  MESON_TAC[];
  CONJ_TAC ;
  IMATCH_MP_TAC  FINITE_IMAGE;
  IMATCH_MP_TAC  FINITE_SUBSET;
  TYPE_THEN `{u | u <=| i }` EXISTS_TAC;
  REWRITE_TAC[FINITE_NUMSEG_LE;SUBSET;IN ;IN_ELIM_THM' ];
  MESON_TAC[];
  UND 9;
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  EXPAND_TAC "B";
  REWRITE_TAC[SUBSET_REFL ];
  ALL_TAC ; (* "sv1" *)
  LEFT 9 "i";
  TYPE_THEN `UNIONS V' SUBSET X` SUBGOAL_TAC;
  JOIN 2 3;
  USE 2 (MATCH_MP SUBSET_TRANS );
  USE 2 (MATCH_MP UNIONS_UNIONS );
  UND 2;
  ASM_MESON_TAC[top_of_metric_unions ];
  DISCH_TAC ;
  TYPE_THEN `!i. UNIONS (B i) SUBSET X` SUBGOAL_TAC;
  GEN_TAC;
  UND 10;
  EXPAND_TAC "B";
  REWRITE_TAC[SUBSET;IN_UNIONS;IN_IMAGE  ];
  REWRITE_TAC[IN;IN_ELIM_THM'  ];
  MESON_TAC[];
  DISCH_TAC ;
  COPY 11;
  COPY 9;
  JOIN 12 13;
  LEFT 12 "i";
  USE 12 (REWRITE_RULE [GSYM PSUBSET ;PSUBSET_ALT;IN  ]);
  LEFT 12 "a";
  LEFT 12 "a";
  CHO 12;
  ALL_TAC ; (* "sv2" *)
  TYPE_THEN `(?ss. subseq ss /\ converge (X,d) (a o ss))` SUBGOAL_TAC;
  IMATCH_MP_TAC  convergent_subseq ;
  ASM_REWRITE_TAC[sequence];
  REWRITE_TAC[SUBSET;UNIV;IN_IMAGE  ];
  REWRITE_TAC[IN];
  ASM_MESON_TAC[];
  DISCH_TAC;
  CHO 13;
  AND 13;
  COPY 13;
  USE 13 (REWRITE_RULE[converge;IN ]);
  CHO 13;
  AND 13;
  USE 1 (REWRITE_RULE[SUBSET;UNIONS;IN;IN_ELIM_THM' ]);
  TYPE_THEN `x` (USE 1 o SPEC);
  REWR 1;
  CHO 1;
  TYPE_THEN `u` (USE 0 o SPEC);
  REWR 0;
  X_CHO 0 `j:num`;
  TYPE_THEN `(UNIONS (B j)) x` SUBGOAL_TAC;
  EXPAND_TAC "B";
  REWRITE_TAC[UNIONS;IN_IMAGE ];
  REWRITE_TAC[IN;IN_ELIM_THM'  ];
  TYPE_THEN `u` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `j` EXISTS_TAC;
  ASM_MESON_TAC[ARITH_RULE `j <=| j`];
  DISCH_TAC;
  TYPE_THEN `u SUBSET (UNIONS (B j))` SUBGOAL_TAC;
  IMATCH_MP_TAC  sub_union;
  EXPAND_TAC "B";
  REWRITE_TAC[IMAGE;IN;IN_ELIM_THM'  ];
  TYPE_THEN `j` EXISTS_TAC;
  ASM_MESON_TAC[ARITH_RULE `j <=| j`];
  DISCH_TAC;
  JOIN 2 3;
  USE 2 (MATCH_MP SUBSET_TRANS);
  ALL_TAC ; (* "sv3" *)
  TYPE_THEN `top_of_metric(X,d) u` SUBGOAL_TAC;
  USE 2 (REWRITE_RULE[SUBSET;IN ]);
  ASM_MESON_TAC[];
  ASM_SIMP_TAC[top_of_metric_nbd];
  REWRITE_TAC[IN ];
  DISCH_ALL_TAC;
  TYPE_THEN `x` (USE 19 o SPEC);
  REWR 1;
  REWR 19;
  CHO 19;
  TYPE_THEN `r` (USE 13 o SPEC);
  CHO 13;
  REWR 13;
  REWR 0;
  TYPE_THEN `n +| (j)` (USE 13 o SPEC);
  USE 13 (REWRITE_RULE[ARITH_RULE `n<=| (n+| a)`]);
  AND 19;
  TYPE_THEN `u ((a o ss) (n +| j) )` SUBGOAL_TAC;
  USE 19 (REWRITE_RULE[SUBSET;open_ball;IN ;IN_ELIM_THM' ]);
  TYPE_THEN `((a o ss) (n +| j))` (USE 19 o SPEC);
  ASM_REWRITE_TAC[];
  UND 19;
  DISCH_THEN IMATCH_MP_TAC  ;
  ASM_REWRITE_TAC[];
  TYPE_THEN `(ss (n +| j))` (USE 12 o SPEC);
  ASM_REWRITE_TAC[o_DEF ];
  DISCH_TAC;
  TYPE_THEN `z = ((a o ss) (n +| j))` ABBREV_TAC;
  TYPE_THEN `UNIONS (B (ss (n+| j))) ((a o ss) (n +| j))` SUBGOAL_TAC;
  EXPAND_TAC "B";
  ASM_REWRITE_TAC[];
  REWRITE_TAC[UNIONS;IN_IMAGE];
  REWRITE_TAC[IN; IN_ELIM_THM'];
  TYPE_THEN `u` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `j` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC  (ARITH_RULE `j <= a /\ a <= ss(a) ==> (j <=| (ss (a)))`);
  ASM_SIMP_TAC[SEQ_SUBLE];
  ARITH_TAC;
  REWRITE_TAC[o_DEF];
  TYPE_THEN `ss(n +| j)` (USE 12 o SPEC);
  UND 12;
  MESON_TAC[];
  ]);;
  (* }}} *)

let uniformly_continuous = euclid_def
  `uniformly_continuous (f:A->B) ((X:A->bool),dX) ((Y:B->bool),dY) <=>
  (!epsilon. ?delta. (&.0 < epsilon) ==> (&.0 <. delta) /\
    (!x y. (X x) /\ (X y) /\
         (dX x y < delta) ==> (dY (f x) (f y) < epsilon)))`;;

(* NB. It is not part of the hypothesis on metric_continuous
   that the IMAGE of f on X is contained in Y.  Hence the
   extra hypothesis.  *)

let compact_uniformly_continuous = prove_by_refinement(
  `!f X dX Y dY. metric_continuous f (X,dX) (Y,dY) /\ (metric_space(X,dX))
    /\ (metric_space(Y,dY)) /\ (compact(top_of_metric(X,dX)) X) /\
    (IMAGE f X SUBSET Y) ==>
    uniformly_continuous (f:A->B) ((X:A->bool),dX) ((Y:B->bool),dY)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[uniformly_continuous;metric_continuous;metric_continuous_pt];
  DISCH_ALL_TAC;
  GEN_TAC;
  LEFT 0 "epsilon";
  TYPE_THEN `epsilon/(&.2)` (USE 0 o SPEC);
  LEFT 0 "delta";
  CHO 0;
  TYPE_THEN `cov = IMAGE (\x. open_ball (X,dX) x ((delta x)/(&.2))) X` ABBREV_TAC;
  USE 3 (REWRITE_RULE[compact]);
  UND 3;
  ASM_SIMP_TAC[GSYM top_of_metric_unions;SUBSET_REFL ];
  DISCH_TAC;
  TYPE_THEN `cov` (USE 3 o SPEC);
  CONV_TAC (quant_right_CONV  "delta");
  DISCH_TAC;
  WITH 6 (ONCE_REWRITE_RULE [GSYM REAL_LT_HALF1]);
  REWR 0;
  TYPE_THEN `!x. (&.0 < (delta x)/(&.2))` SUBGOAL_TAC;
  ASM_MESON_TAC[REAL_LT_HALF1];
  DISCH_TAC;
  TYPE_THEN `X SUBSET UNIONS cov /\ cov SUBSET top_of_metric (X,dX)` SUBGOAL_TAC;
  SUBCONJ_TAC;
  REWRITE_TAC[SUBSET;UNIONS;IN;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  TYPE_THEN `open_ball (X,dX) x ((delta x)/(&.2))` EXISTS_TAC;
  CONJ_TAC;
  EXPAND_TAC "cov";
  REWRITE_TAC[IMAGE;IN ;IN_ELIM_THM'  ];
  ASM_MESON_TAC[];
  IMATCH_MP_TAC  (REWRITE_RULE[IN] open_ball_nonempty);
  ASM_REWRITE_TAC[];
  DISCH_TAC ;
  REWRITE_TAC[SUBSET;IN ];
  EXPAND_TAC "cov";
  REWRITE_TAC[IMAGE;IN;IN_ELIM_THM' ];
  NAME_CONFLICT_TAC;
  DISCH_ALL_TAC;
  CHO 10;
  AND 10;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[open_ball_open];
  DISCH_TAC;
  REWR 3;
  CHO 3;
  ALL_TAC; (* "cc1"; *)
  AND 3;
  AND 3;
  JOIN 11 10;
  UND 10;
  EXPAND_TAC "cov";
  DISCH_TAC;
(*** Modified by JRH for changed theorem name
  USE 10 (MATCH_MP FINITE_SUBSET_IMAGE);
 ***)
  USE 10 (MATCH_MP FINITE_SUBSET_IMAGE_IMP);
  X_CHO 10 `S:A->bool`;
  TYPE_THEN `ds = IMAGE delta S` ABBREV_TAC ;
  TYPE_THEN `(FINITE ds) /\ ( !x. (ds x) ==> (&.0 <. x) )` SUBGOAL_TAC;
  EXPAND_TAC "ds";
  CONJ_TAC;
  IMATCH_MP_TAC  FINITE_IMAGE ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[IMAGE;IN;IN_ELIM_THM' ];
  NAME_CONFLICT_TAC ;
  DISCH_ALL_TAC;
  CHO 12;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  USE 12 (MATCH_MP min_finite_delta);
  CHO 12;
  TYPE_THEN `delta'/(&.2)` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ALL_TAC ; (* "cc2" *)
  ASM_REWRITE_TAC[REAL_LT_HALF1];
  DISCH_ALL_TAC;
  AND 10;
  AND 10;
  USE 10(  MATCH_MP UNIONS_UNIONS );
  JOIN 3 10;
  USE 3 (MATCH_MP SUBSET_TRANS);
  USE 3 (REWRITE_RULE [SUBSET;IN;UNIONS;IN_ELIM_THM'  ]);
  USE 3 (REWRITE_RULE[IMAGE;IN ;IN_ELIM_THM' ]);
  TYPE_THEN `x` (WITH 3 o SPEC);
  TYPE_THEN `y` (WITH 3 o SPEC);
  KILL 3; (* start of yest *)
  H_MATCH_MP (HYP "18")(HYP "14");
  H_MATCH_MP (HYP "10") (HYP "13");
  CHO 19;
  CHO 3;
  AND 19;
  CHO 20;
  AND 20;
  USE 20 (REWRITE_RULE [open_ball]);
  REWR 19;
  USE 19 (REWRITE_RULE [IN_ELIM_THM']);
  AND 19;
  AND 19;
  TYPE_THEN `dX x' x < delta x'` SUBGOAL_TAC;
  UND 19;
  IMATCH_MP_TAC  (REAL_ARITH `((u <. v) ==> (a< u)==>(a <v))`);
  TYPE_THEN `x'` (USE 8 o SPEC);
  UND 8;
  REWRITE_TAC[REAL_LT_HALF2;REAL_LT_HALF1 ];
  DISCH_TAC;
  ALL_TAC ; (* cc3 *)
  TYPE_THEN `dX x' y < delta x'` SUBGOAL_TAC;
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM REAL_HALF_DOUBLE]));
  IMATCH_MP_TAC  (REAL_ARITH `(dX x' x <. u) /\ (dX x y <. u) /\ (dX x' y <= dX x' x +. dX x y) ==> (dX x' y <. u + u)`);
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  UND 15;
  IMATCH_MP_TAC  (REAL_ARITH `((u <=. v) ==> (a< u)==>(a <v))`);
  IMATCH_MP_TAC  (REAL_ARITH `(u + u) <= (v +. v) ==> (u <= v)`);
  REWRITE_TAC[REAL_HALF_DOUBLE];
  AND 12;
  UND 12;
  DISCH_THEN (MATCH_MP_TAC);
  EXPAND_TAC "ds";
  REWRITE_TAC[IMAGE;IN; IN_ELIM_THM' ];
  UND 21;
  MESON_TAC[];
  IMATCH_MP_TAC  metric_space_triangle;
  TYPE_THEN `X` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM REAL_HALF_DOUBLE]));
  TYPE_THEN `(dY (f x) (f x') <. u0) /\ (dY (f x') (f y) <. u0) /\ (dY (f x) (f y) <= (dY (f x) (f x')) + (dY (f x') (f y))) ==> ((dY (f x) (f y)) < u0 + u0)` (fun t-> (IMATCH_MP_TAC    (REAL_ARITH t)));
  TYPE_THEN `x'` (USE 0 o SPEC);
  AND 0;
  USE 0 (REWRITE_RULE[IN ]);
  TYPE_THEN `y` (WITH  0  o SPEC);
  TYPE_THEN `x` (USE 0 o  SPEC);
  ALL_TAC; (* cc4 *)
  TYPE_THEN `Y (f x) /\ Y (f y) /\ Y (f x')` SUBGOAL_TAC;
  UND 4;
  REWRITE_TAC[SUBSET;IN_IMAGE;  ];
  REWRITE_TAC[IN ];
  UND 13;
  UND 14;
  UND 22;
  MESON_TAC[];
  DISCH_ALL_TAC;
  CONJ_TAC;
  TYPE_THEN `dY (f x) (f x') = dY (f x') (f x)` SUBGOAL_TAC;
  UND 2;
  UND 28;
  UND 30;
  TYPEL_THEN [`Y`;`dY`;`f x`;`f x'`] (fun t-> MP_TAC(ISPECL t metric_space_symm));
  MESON_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  UND 0;
  DISCH_THEN IMATCH_MP_TAC ;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  UND 27;
  DISCH_THEN IMATCH_MP_TAC ;
  ASM_REWRITE_TAC[];
  TYPEL_THEN [`Y`;`dY`;`f x`;`f x'`;`f y`] (fun t-> MP_TAC(ISPECL t metric_space_triangle));
  DISCH_THEN IMATCH_MP_TAC ;
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

(* I'm rather surprised that this lemma did not need the
   hypothesis that U and- V are topologies. *)

let image_compact = prove_by_refinement(
  `!U V (f:A->B) K. (continuous f U V ) /\
      (compact U K) /\ (IMAGE f K SUBSET (UNIONS V))
  ==> (compact V (IMAGE f K))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[compact];
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  TYPE_THEN `cov = IMAGE (\v. preimage (UNIONS U) f v ) V'`  ABBREV_TAC ;
  TYPE_THEN `cov SUBSET U` SUBGOAL_TAC ;
  EXPAND_TAC "cov";
  REWRITE_TAC[SUBSET;IN_IMAGE ];
  NAME_CONFLICT_TAC;
  GEN_TAC;
  DISCH_ALL_TAC;
  CHO 6;
  AND 6;
  ASM_REWRITE_TAC[];
  USE 4 (REWRITE_RULE[SUBSET]);
  TYPE_THEN `x'` (USE 4 o SPEC);
  REWR 4;
  UND 4;
  UND 0;
  REWRITE_TAC[continuous];
  MESON_TAC[];
  TYPE_THEN `K SUBSET UNIONS cov` SUBGOAL_TAC;
  ALL_TAC; (* ic1 *)
  UND 3;
  REWRITE_TAC[SUBSET;IN_IMAGE ];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  LEFT 3 "x'";
  DISCH_ALL_TAC;
  LEFT 3 "x'";
  TYPE_THEN `x` (USE 3 o SPEC);
  TYPE_THEN `f x` (USE 3 o SPEC);
  REWR 3;
  UND 3;
  REWRITE_TAC[UNIONS;IN;IN_ELIM_THM'  ];
  USE 5 (REWRITE_RULE[IMAGE]);
  EXPAND_TAC "cov";
  REWRITE_TAC[IN_ELIM_THM';IN ];
  DISCH_ALL_TAC;
  TYPE_THEN `exists u. V' u /\ u(f x)` SUBGOAL_TAC;
  ASM_MESON_TAC[];
  DISCH_TAC;
  CHO 7;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x");
  TYPE_THEN `u` EXISTS_TAC;
  NAME_CONFLICT_TAC;
  TYPE_THEN `preimage (UNIONS U) f u` EXISTS_TAC;
  ASM_REWRITE_TAC[preimage;IN_ELIM_THM' ;IN ];
  USE 1 (REWRITE_RULE[compact;SUBSET;IN  ]);
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  USE 1 (REWRITE_RULE[compact]);
  AND 1;
  TYPE_THEN `cov` (USE 1 o SPEC);
  REWR 1;
  CHO 1;
  ALL_TAC ; (* ic2 *)
  TYPE_THEN `(?V''. V'' SUBSET V' /\ FINITE V'' /\ (W = IMAGE (\v. preimage (UNIONS U) f v) V''))` SUBGOAL_TAC;
  IMATCH_MP_TAC  finite_subset ;
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  CHO 9;
  TYPE_THEN `V''` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN_IMAGE];
  REWRITE_TAC[IN;UNIONS;IN_ELIM_THM' ];
  NAME_CONFLICT_TAC;
  CONV_TAC (quant_left_CONV "x'");
  CONV_TAC (quant_left_CONV "x'");
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  AND 1;
  AND 1;
  USE 1 (REWRITE_RULE[SUBSET;UNIONS;IN;IN_ELIM_THM'  ]);
  TYPE_THEN `x'` (USE 1 o SPEC);
  REWR 1;
  CHO 1;
  AND 1;
  USE 14 (REWRITE_RULE[IMAGE;IN ;IN_ELIM_THM' ]);
  TYPE_THEN `u':B->bool` (X_CHO 14);
  TYPE_THEN `u'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  UND 1;
  ASM_REWRITE_TAC[preimage;IN;IN_ELIM_THM' ];
  MESON_TAC [];
  ]);;
  (* }}} *)

let metric_bounded = euclid_def
  `metric_bounded (X,d) <=>
     ?(x:A) r. X SUBSET (open_ball(X,d) x r)`;;

let euclid_ball_cube = prove_by_refinement(
  `!n x r. ?N. (open_ball(euclid n,d_euclid) x r) SUBSET
      {x | euclid n x /\ (!i. abs (x i) <= &N)}`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM';open_ball; ];
  ASSUME_TAC  REAL_ARCH_SIMPLE;
  TYPE_THEN ` (d_euclid x (\i. &.0) +. r)` (USE 0 o SPEC);
  X_CHO 0 `N:num`;
  TYPE_THEN `N` EXISTS_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  GEN_TAC ;
  ASSUME_TAC proj_contraction;
  TYPEL_THEN [`n`;`x'`;`(\(i :num). &.0)`;`i`] (USE 4 o SPECL);
  USE 4 BETA_RULE ;
  USE 4 (CONV_RULE REDUCE_CONV );
  TYPE_THEN `euclid n (\i. &.0)` SUBGOAL_TAC ;
  REWRITE_TAC[euclid];
  DISCH_TAC;
  REWR 4;
  ASSUME_TAC metric_euclid;
  TYPE_THEN `n` (USE 6 o SPEC);
  TYPE_THEN `d_euclid x' (\i. &.0) <=. d_euclid x' x + d_euclid x (\i. &0)` SUBGOAL_TAC;
  IMATCH_MP_TAC  metric_space_triangle;
  TYPE_THEN `euclid n` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `d_euclid x' x = d_euclid x x'` SUBGOAL_TAC;
  IMATCH_MP_TAC  metric_space_symm;
  TYPE_THEN `euclid n` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  UND 0;
  UND 3;
  UND 4;
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let totally_bounded_euclid = prove_by_refinement(
  `!X n. (metric_bounded (X,d_euclid) /\
    (X SUBSET (euclid n))) ==>
   (totally_bounded (X,d_euclid))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[metric_bounded];
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  totally_bounded_subset;
  CHO 0;
  CHO 0;
  ASSUME_TAC euclid_ball_cube;
  TYPEL_THEN [`n`;`x`;`r`] (USE 2 o SPECL);
  CHO 2;
  ASSUME_TAC open_ball_subspace;
  TYPEL_THEN [`euclid n`;`X`;`d_euclid`;`x`;`r`] (USE 3 o ISPECL);
  REWR 3;
  JOIN 0 3;
  USE 0 (MATCH_MP SUBSET_TRANS);
  JOIN 0 2;
  USE 0 (MATCH_MP SUBSET_TRANS);
  TYPE_THEN `{x | euclid n x /\ (!i. abs (x i) <= &N)}` EXISTS_TAC;
  ASM_REWRITE_TAC[totally_bounded_cube ];
  IMATCH_MP_TAC  metric_subspace;
  TYPE_THEN `euclid n` EXISTS_TAC;
  REWRITE_TAC[metric_euclid];
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM' ];
  MESON_TAC[];
  ]);;
  (* }}} *)

(* topology  is not needed as an assumption here!  *)
let induced_compact = prove_by_refinement(
  `!U (K:A->bool). (K SUBSET (UNIONS U)) ==>
     (compact U K <=> (compact (induced_top U K) K))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[compact];
  EQ_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[induced_top_support;SUBSET_INTER;SUBSET_REFL  ];
  DISCH_ALL_TAC;
  USE 3 (REWRITE_RULE[induced_top;SUBSET;IN_IMAGE  ]);
  LEFT 3 "x'";
  LEFT 3 "x'";
  X_CHO 3 `u:(A->bool)->(A->bool)`;
  TYPE_THEN `IMAGE u V` (USE 1 o SPEC);
  TYPE_THEN `K SUBSET UNIONS (IMAGE u V) /\ IMAGE u V SUBSET U` SUBGOAL_TAC;
  REWRITE_TAC[IMAGE;SUBSET;IN_UNIONS;IN_ELIM_THM'  ];
  CONJ_TAC;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  USE 2 (REWRITE_RULE[SUBSET;IN_UNIONS ]);
  USE 2 (REWRITE_RULE[IN ]);
  TYPE_THEN `x` (USE 2 o SPEC);
  REWR 2;
  X_CHO 2 `v:A->bool`;
  NAME_CONFLICT_TAC;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x");
  TYPE_THEN `v` EXISTS_TAC;
  TYPE_THEN `u v` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `v` (USE 3 o SPEC);
  USE 3 (REWRITE_RULE[IN]);
  REWR 3;
  ASSUME_TAC INTER_SUBSET;
  USE 5 (CONJUNCT1);
  TYPEL_THEN [`u v`;`K`] (USE 5 o ISPECL);
  ASM_MESON_TAC[SUBSET;IN];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[IN ];
  ASM_MESON_TAC[IN];
  DISCH_TAC;
  REWR 1;
  CHO 1;
  AND 1;
  AND 1;
  JOIN 6 5;
(*** Modified by JRH for changed theorem name
  USE 5 (MATCH_MP FINITE_SUBSET_IMAGE);
 ***)
  USE 5 (MATCH_MP FINITE_SUBSET_IMAGE_IMP);
  X_CHO 5 `W':(A->bool)->bool`;
  TYPE_THEN `W'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `K SUBSET UNIONS (IMAGE u W')` SUBGOAL_TAC;
  ASM_MESON_TAC[UNIONS_UNIONS ;SUBSET_TRANS];
  REWRITE_TAC[SUBSET;IN_UNIONS;IN_IMAGE; ];
  NAME_CONFLICT_TAC;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `x` (USE 6 o SPEC);
  REWR 6;
  CHO 6;
  AND 6;
  CHO 8;
  AND 5;
  AND 5;
  USE 10 (REWRITE_RULE[SUBSET;IN ]);
  TYPE_THEN `x'` (USE 10 o SPEC);
  REWR 10;
  USE 3 (REWRITE_RULE[IN]);
  TYPE_THEN `x'` (USE 3 o SPEC);
  REWR 3;
  TYPE_THEN `x'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ASM ONCE_REWRITE_TAC[];
  REWRITE_TAC[INTER;IN;IN_ELIM_THM' ];
  ASM_MESON_TAC[];
  ALL_TAC ; (* dd1*)
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN  `VK = IMAGE (\b. (b INTER K)) V` ABBREV_TAC ;
  TYPE_THEN `VK` (USE 2 o SPEC);
  TYPE_THEN `K SUBSET UNIONS VK /\ VK SUBSET induced_top U K` SUBGOAL_TAC;
  CONJ_TAC;
  EXPAND_TAC "VK";
  REWRITE_TAC[INTER_THM;GSYM UNIONS_INTER ];
  ASM_REWRITE_TAC[SUBSET_INTER;SUBSET_REFL  ]; (* end of branch *)
  REWRITE_TAC[induced_top];
  EXPAND_TAC "VK";
  REWRITE_TAC[INTER_THM ];
  IMATCH_MP_TAC  IMAGE_SUBSET;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  REWR 2;
  X_CHO 2 `WK:(A->bool)->bool`;
  TYPEL_THEN [`V`;`(INTER) K`;`WK`] (fun t-> MP_TAC (ISPECL t finite_subset ));
  ASM_REWRITE_TAC[];
  AND 2;
  UND 8;
  EXPAND_TAC "VK";
  REWRITE_TAC[INTER_THM];
  DISCH_ALL_TAC;
  REWR 8;
  CHO 8;
  TYPE_THEN `C` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  REWR 2;
  AND 2;
  USE 2 (REWRITE_RULE[GSYM UNIONS_INTER]);
  UND 2;
  TYPE_THEN `R = UNIONS C` ABBREV_TAC;
  SET_TAC[];
  ]);;

  (* }}} *)

let compact_euclid = prove_by_refinement(
  `!X n. (X SUBSET euclid n) ==>
        (compact (top_of_metric(euclid n,d_euclid)) X <=>
        (closed_ (top_of_metric(euclid n,d_euclid)) X /\
        (metric_bounded(X,d_euclid))))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  TYPE_THEN `top_of_metric (X,d_euclid) = induced_top (top_of_metric(euclid n,d_euclid)) X` SUBGOAL_TAC;
  IMATCH_MP_TAC  (GSYM top_of_metric_induced);
  ASM_REWRITE_TAC[metric_euclid];
  DISCH_TAC;
  TYPE_THEN `metric_space (X,d_euclid)` SUBGOAL_TAC ;
  ASM_MESON_TAC [metric_euclid;metric_subspace];
  DISCH_TAC ;
  EQ_TAC;
  DISCH_ALL_TAC;
  CONJ_TAC;
  IMATCH_MP_TAC  compact_closed;
  SIMP_TAC [metric_euclid;metric_hausdorff;top_of_metric_top ];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[metric_bounded];
  IMATCH_MP_TAC  totally_bounded_bounded;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC  compact_totally_bounded ;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[induced_compact;top_of_metric_unions;metric_euclid ];
  DISCH_ALL_TAC;
  TYPE_THEN `X SUBSET (UNIONS (top_of_metric (euclid n,d_euclid)))` SUBGOAL_TAC;
  ASM_MESON_TAC[top_of_metric_unions ; metric_euclid];
  ASM_SIMP_TAC [induced_compact ];
  ASSUME_TAC metric_euclid;
  DISCH_TAC;
  TYPE_THEN `induced_top (top_of_metric(euclid n,d_euclid)) X = top_of_metric(X,d_euclid)` SUBGOAL_TAC;
  IMATCH_MP_TAC  top_of_metric_induced;
  ASM_REWRITE_TAC[];
  DISCH_THEN REWRT_TAC;
  IMATCH_MP_TAC  complete_compact;
  ASM_REWRITE_TAC[];
  CONJ_TAC ;
  ASM_MESON_TAC[totally_bounded_euclid];
  IMATCH_MP_TAC  complete_closed;
  TYPE_THEN `n` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)


let neg_continuous = prove_by_refinement(
  `!n. metric_continuous (euclid_neg) (euclid n,d_euclid) (euclid n,d_euclid)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[metric_continuous;metric_continuous_pt];
  DISCH_ALL_TAC;
  RIGHT_TAC "delta";
  DISCH_TAC;
  TYPE_THEN `epsilon` EXISTS_TAC;
  ASM_REWRITE_TAC[IN ];
  DISCH_ALL_TAC;
  REWRITE_TAC[d_euclid];
  REWRITE_TAC[euclid_neg_sum];
  REWRITE_TAC[norm_neg];
  REWRITE_TAC[GSYM d_euclid];
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let continuous_comp = prove_by_refinement(
  `!(f:A->B) (g:B->C) U V W.
      continuous f U V /\ continuous g V W /\
      (IMAGE f (UNIONS U) SUBSET (UNIONS V)) ==>
     continuous (g o f) U W`,
  (* {{{ proof *)

  [
  REWRITE_TAC[continuous;IN;preimage];
  DISCH_ALL_TAC;
  X_GEN_TAC `w :C->bool`;
  DISCH_TAC;
  TYPE_THEN `w ` (USE  1 o SPEC);
  REWR 1;
  TYPE_THEN `{x | UNIONS V x /\ w (g x)}` (USE 0 o SPEC);
  REWR 0;
  USE 0 (REWRITE_RULE[IN_ELIM_THM' ]);
  REWRITE_TAC[o_DEF ];
  TYPE_THEN `U {x | UNIONS U x /\ UNIONS V (f x) /\ w (g (f x))} = U {x | UNIONS U x /\ w (g (f x))}` SUBGOAL_TAC;
  AP_TERM_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  DISCH_ALL_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  IMATCH_MP_TAC  (TAUT `(a ==> b) ==> ((a /\ b /\ c) <=> (a /\ c ))`);
  TYPE_THEN  `UU = UNIONS U ` ABBREV_TAC;
  TYPE_THEN `VV = UNIONS V` ABBREV_TAC ;
  USE 2 (REWRITE_RULE[SUBSET;IN_IMAGE ]);
  ASM_MESON_TAC[IN];
  DISCH_THEN (fun  t-> (USE 0 ( REWRITE_RULE[t])));
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)


let compact_max = prove_by_refinement(
  `!(f:A->(num->real)) U K.
       (continuous f U (top_of_metric(euclid 1,d_euclid))) /\
       (IMAGE f K SUBSET (euclid 1)) /\
        (compact U K) /\ ~(K=EMPTY)==>
     (?x. K x /\ (!y. (K y) ==> (f y 0 <= f x 0)))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  COPY 2;
  COPY 1;
  TYPE_THEN `euclid 1 = UNIONS (top_of_metric (euclid 1,d_euclid))` SUBGOAL_TAC;
  MESON_TAC[top_of_metric_unions;metric_euclid];
  DISCH_THEN (fun t-> USE 5 (ONCE_REWRITE_RULE[t]));
  JOIN 4 5;
  COPY 0;
  JOIN 0 4;
  WITH  0 (MATCH_MP image_compact);
  UND 4;
  ASM_SIMP_TAC[compact_euclid];
  DISCH_ALL_TAC;
  TYPE_THEN `P = (IMAGE (coord 0) (IMAGE f K))` ABBREV_TAC ;
  TYPE_THEN `(?s. !y. (?x. P x /\ y <. x) <=> y <. s)` SUBGOAL_TAC;
  IMATCH_MP_TAC  REAL_SUP_EXISTS;
  CONJ_TAC;
  USE 3 (REWRITE_RULE[EMPTY_EXISTS;IN ]);
  CHO 3;
  TYPE_THEN `f u 0` EXISTS_TAC;
  EXPAND_TAC "P";
  REWRITE_TAC[IMAGE;IN;IN_ELIM_THM';coord ];
  NAME_CONFLICT_TAC;
  LEFT_TAC "x'";
  LEFT_TAC "x'";
  TYPE_THEN `u` EXISTS_TAC;
  ASM_MESON_TAC[];
  USE 6 (REWRITE_RULE[metric_bounded;open_ball;SUBSET;IN_IMAGE  ]);
  X_CHO 6 `x0:num->real`;
  X_CHO 6 `r:real`;
  USE 6 (REWRITE_RULE[IN;IN_ELIM_THM' ]);
  EXPAND_TAC "P";
  REWRITE_TAC[IMAGE;IN;IN_ELIM_THM';coord];
  NAME_CONFLICT_TAC;
  TYPE_THEN `x0 0 +. r` EXISTS_TAC;
  DISCH_ALL_TAC;
  X_CHO 8 `fx:num->real`;
  AND 8;
  ASM_REWRITE_TAC[];
  KILL 8;
  X_CHO 9 `x:A`;
  LEFT 6 "x";
  LEFT 6 "x";
  TYPE_THEN `x` (USE 6 o SPEC);
  TYPE_THEN `fx` (USE 6 o SPEC);
  REWR 6;
  TYPE_THEN `(d_euclid x0 (f x) = abs (x0 0 - (f x 0)))` SUBGOAL_TAC;
  IMATCH_MP_TAC  euclid1_abs;
  USE 1 (REWRITE_RULE[SUBSET;IN ]);
  ASM_MESON_TAC[];
  AND 6;
  AND 6;
  DISCH_TAC;
  REWR 6;
  UND 6;
  REAL_ARITH_TAC;
  DISCH_TAC;
  ALL_TAC ; (* cc1 *)
  TYPE_THEN `(!u. (P u) ==> (u <=. sup P)) /\ (P (sup P))` SUBGOAL_TAC;
  REWRITE_TAC[sup];
  SELECT_TAC;
  CHO 8;
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  TYPE_THEN `s = t` SUBGOAL_TAC;
  PROOF_BY_CONTR_TAC;
  USE 10 (MATCH_MP  (REAL_ARITH `~(s=t) ==> (s<. t) \/ (t <. s)`));
  TYPE_THEN `s ` (WITH 9 o SPEC);
  TYPE_THEN `t` (WITH 9 o SPEC);
  ASM_MESON_TAC[REAL_ARITH `~(x <. x)`];
  DISCH_TAC;
  REWR 8;
  SUBCONJ_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `t` (USE 8 o SPEC);
  UND 8;
  REWRITE_TAC[REAL_ARITH `~(x <. x)`];
  LEFT_TAC "x";
  LEFT_TAC "x";
  TYPE_THEN `u` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  PROOF_BY_CONTR_TAC;
  TYPE_THEN `~ (IMAGE f K) (t *# (dirac_delta 0))` SUBGOAL_TAC;
  PROOF_BY_CONTR_TAC;
  REWR 13;
  UND 12;
  EXPAND_TAC "P";
  ONCE_REWRITE_TAC[IMAGE];
  ONCE_REWRITE_TAC[IMAGE];
  ONCE_REWRITE_TAC[IMAGE];
  REWRITE_TAC[IN_ELIM_THM';IN];
  TYPE_THEN `t *# (dirac_delta 0)` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ALL_TAC ; (* cc2 *)
  REWRITE_TAC[coord_dirac];
  DISCH_TAC;
  USE 4 (MATCH_MP closed_open);
  ASSUME_TAC (SPEC `1` metric_euclid);
  WITH 14 (MATCH_MP top_of_metric_unions);
  WITH 15 (GSYM);
  REWR 4;
  TYPE_THEN `z = t *# dirac_delta 0`  ABBREV_TAC ;
  TYPE_THEN `(euclid 1 DIFF (IMAGE f K)) z` SUBGOAL_TAC ;
  REWRITE_TAC[REWRITE_RULE[IN] IN_DIFF];
  ASM_REWRITE_TAC[];
  EXPAND_TAC "z";
  REWRITE_TAC[euclid;euclid_scale;dirac_delta];
  DISCH_ALL_TAC;
  ASSUME_TAC (ARITH_RULE `1 <=| m ==> (~(0=m))`);
  REWR 19;
  ASM_REWRITE_TAC[];
  REDUCE_TAC;
  REWRITE_TAC[];
  UND 16;
  DISCH_THEN (fun t-> ONCE_REWRITE_TAC [GSYM t]);
  UND 4;
  REWRITE_TAC[open_DEF];
    ASM_SIMP_TAC[top_of_metric_nbd];
  DISCH_ALL_TAC;
  IN_OUT_TAC ;
  TYPE_THEN `z` (USE  0 o SPEC);
  KILL 12;
  KILL 13;
  KILL 9;
  UND 14;
  UND 3;
  REWRITE_TAC[];
  DISCH_THEN (fun t-> ONCE_REWRITE_TAC[GSYM t]);
  DISCH_ALL_TAC;
  REWR 0;
  CHO 0;
  AND 0;
  USE 0 (REWRITE_RULE[SUBSET;IN; open_ball;IN_ELIM_THM' ]);
  COPY 0;
  TYPE_THEN `(t- (r/(&.2)))*# (dirac_delta 0)` (USE 0 o SPEC);
  TYPE_THEN `euclid 1 z /\ euclid 1 ((t - r / &2) *# dirac_delta 0) /\ d_euclid z ((t - r / &2) *# dirac_delta 0) < r` SUBGOAL_TAC;
  EXPAND_TAC "z";
  SUBCONJ_TAC;
  REWRITE_TAC[euclid;dirac_delta;euclid_scale];
  GEN_TAC;
  SIMP_TAC [ (ARITH_RULE `1 <=| m ==> (~(0=m))`)];
  REWRITE_TAC[REAL_ARITH `t*(&.0) = (&.0)`];
  DISCH_ALL_TAC;
  SUBCONJ_TAC;
  REWRITE_TAC[euclid;dirac_delta;euclid_scale];
  GEN_TAC;
  SIMP_TAC [ (ARITH_RULE `1 <=| m ==> (~(0=m))`)];
  REWRITE_TAC[REAL_ARITH `t*(&.0) = (&.0)`];
  ALL_TAC ; (* cc3 *)
  UND 13 ;
  SIMP_TAC[euclid1_abs];
  DISCH_ALL_TAC;
  REWRITE_TAC[euclid_minus ; euclid_scale;dirac_delta ];
  REDUCE_TAC ;
  REWRITE_TAC[REAL_ARITH `t - (t - (r/(&.2))) = r/(&.2)`];
  WITH  9 (ONCE_REWRITE_RULE[GSYM REAL_LT_HALF1]);
  WITH 19 (MATCH_MP (REAL_ARITH `&.0 < x ==> (&.0 <= x)`));
  WITH 20 (REWRITE_RULE[GSYM REAL_ABS_REFL]);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_LT_HALF2];
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> (USE 0 (REWRITE_RULE[t])));
  ALL_TAC ; (* cc4 *)
  TYPE_THEN `t - (r/(&.2)) ` (USE 10 o SPEC);
  TYPE_THEN `t - r / &2 < t` SUBGOAL_TAC;
  IMATCH_MP_TAC  (REAL_ARITH `&.0 < x ==> (t - x < t)`);
  WITH  9 (ONCE_REWRITE_RULE[GSYM REAL_LT_HALF1]);
  ASM_REWRITE_TAC[];
  DISCH_TAC ;
  REWR 10;
  X_CHO 10 `u:real`;
  TYPE_THEN `u` (USE 7 o SPEC);
  REWR 7;
  TYPE_THEN `(euclid 1 DIFF IMAGE f K) (u *# (dirac_delta 0))` SUBGOAL_TAC ;
  UND 12;
  DISCH_THEN (IMATCH_MP_TAC  );
  EXPAND_TAC "z";
  SUBCONJ_TAC;
  REWRITE_TAC[euclid;euclid_scale;dirac_delta];
  REWRITE_TAC[ (ARITH_RULE `1 <=| m <=> (~(0=m))`)];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  SUBCONJ_TAC;
  REWRITE_TAC[euclid;euclid_scale;dirac_delta];
  REWRITE_TAC[ (ARITH_RULE `1 <=| m <=> (~(0=m))`)];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[euclid1_abs];
  EXPAND_TAC "z";
  REWRITE_TAC[dirac_delta;euclid_scale;euclid_minus];
  REDUCE_TAC;
  AND 10;
  REWRITE_TAC[GSYM ABS_BETWEEN];
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  UND 7;
  UND 9;
  REAL_ARITH_TAC;
  UND 10;
  IMATCH_MP_TAC  (REAL_ARITH `y <. x ==> ((t - y <. u) ==> (t <. u + x))`);
  REWRITE_TAC[REAL_LT_HALF2];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REWRITE_RULE[IN] IN_DIFF];
  IMATCH_MP_TAC  (TAUT `B ==> (~(A /\ ~B))`);
  AND 10;
  UND 14;
  EXPAND_TAC "P";
  TYPE_THEN  `B = IMAGE f K` ABBREV_TAC ;
  ALL_TAC ; (* cc5 *)
  REWRITE_TAC[IMAGE;coord;IN;IN_ELIM_THM' ];
  DISCH_TAC;
  CHO 19;
  AND 19;
  ASM_REWRITE_TAC[];
  USE 17 (REWRITE_RULE[SUBSET;IN]);
  TYPE_THEN `x` (USE 17 o SPEC);
  REWR 17;
  USE 17 (REWRITE_RULE[euclid1_dirac]);
  ASM_MESON_TAC[];
  ASM_MESON_TAC[];
  TYPE_THEN `t = sup P` ABBREV_TAC;
  DISCH_ALL_TAC;
  UND 11;
  EXPAND_TAC "P";
  REWRITE_TAC[];
  ONCE_REWRITE_TAC[IMAGE];
  REWRITE_TAC[IN_IMAGE;IN_ELIM_THM';IN ];
  NAME_CONFLICT_TAC;
  DISCH_ALL_TAC;
  CHO 11;
  AND 11;
  CHO 12;
  REWR 11;
  TYPE_THEN `x'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  UND 10;
  EXPAND_TAC "P";
  REWRITE_TAC[];
  ONCE_REWRITE_TAC[IMAGE];
  REWRITE_TAC[IN_IMAGE;IN_ELIM_THM' ];
  REWRITE_TAC[IN];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[coord];
  NAME_CONFLICT_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `f y 0` (USE 10 o SPEC);
  UND 10;
  DISCH_THEN IMATCH_MP_TAC  ;
  LEFT_TAC "x'";
  LEFT_TAC "x'";
  ASM_MESON_TAC[];
  (* finish *)
  ]);;

  (* }}} *)

(* ------------------------------------------------------------------ *)
(* homeomorphisms *)
(* ------------------------------------------------------------------ *)

let homeomorphism = euclid_def `homeomorphism (f:A->B) U V <=>
  (BIJ f (UNIONS U) (UNIONS V) ) /\ (continuous f U V) /\
  (!A. (U A) ==> (V (IMAGE f A)))`;;

let INV_homeomorphism  = prove_by_refinement(
  `!f U V. homeomorphism (f:A-> B) U V ==>
    (continuous (INV f (UNIONS U) (UNIONS V)) V U)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[continuous;IN;preimage];
  REWRITE_TAC[homeomorphism];
  DISCH_ALL_TAC;
  X_GEN_TAC `u:A->bool`;
  DISCH_ALL_TAC;
  TYPE_THEN `{ x | UNIONS V x /\ u (INV f (UNIONS U) (UNIONS V) x)} = IMAGE f u` SUBGOAL_TAC;
  IMATCH_MP_TAC  EQ_EXT ;
  X_GEN_TAC `t:B`;
  REWRITE_TAC[IN_ELIM_THM';IMAGE ;IN ];
  EQ_TAC ;
  DISCH_ALL_TAC;
  TYPE_THEN `(INV f (UNIONS U) (UNIONS V) t)` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[INVERSE_DEF;IN;BIJ ];
  DISCH_ALL_TAC;
  CHO 4;
  SUBCONJ_TAC;
  USE 0 (REWRITE_RULE[BIJ;INJ]);
  IN_OUT_TAC ;
  ASM_REWRITE_TAC[];
  AND 4;
  AND 5;
  TYPE_THEN `x` (USE 6 o SPEC);
  UND 6;
  DISCH_THEN (IMATCH_MP_TAC );
  REWRITE_TAC[UNIONS;IN;IN_ELIM_THM' ];
  ASM_MESON_TAC[];
  DISCH_TAC ;
  TYPE_THEN `INV f (UNIONS U) (UNIONS V) t = x` SUBGOAL_TAC;
  (* stop here this is an example that ASM_MESON_TAC should catch *)
  (* ASM_MESON_TAC[INVERSE_XY;IN ;UNIONS ]; *)
  TYPE_THEN `(UNIONS U x)` SUBGOAL_TAC;
  REWRITE_TAC[UNIONS;IN_ELIM_THM';IN   ];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[INVERSE_XY;IN ];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  UND 2;
  DISCH_THEN IMATCH_MP_TAC ;
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let bicont_homeomorphism = prove_by_refinement(
  `!f U V. (BIJ (f:A->B) (UNIONS U) (UNIONS V)) /\ (continuous f U V) /\
    (continuous (INV  f (UNIONS U) (UNIONS V)) V U) ==>
     (homeomorphism f U V)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[homeomorphism];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  UND 2;
  REWRITE_TAC[continuous;IN;preimage ];
  DISCH_ALL_TAC;
  TYPE_THEN `A` (USE 2 o SPEC);
  REWR 2;
  TYPE_THEN `{x | UNIONS V x /\ A (INV f (UNIONS U) (UNIONS V) x)}= (IMAGE f A) ` SUBGOAL_TAC;
  IMATCH_MP_TAC  EQ_EXT ;
  X_GEN_TAC `t:B`;
  REWRITE_TAC[IN_ELIM_THM';IMAGE ;IN ];
  EQ_TAC ;
  DISCH_ALL_TAC;
  TYPE_THEN `(INV f (UNIONS U) (UNIONS V) t)` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[INVERSE_DEF;IN;BIJ ];
  DISCH_ALL_TAC;
  CHO 4;
  SUBCONJ_TAC;
  USE 0 (REWRITE_RULE[BIJ;INJ]);
  IN_OUT_TAC ;
  ASM_REWRITE_TAC[];
  AND 4;
  AND 5;
  TYPE_THEN `x` (USE 6 o SPEC);
  UND 6;
  DISCH_THEN (IMATCH_MP_TAC );
  REWRITE_TAC[UNIONS;IN;IN_ELIM_THM' ];
  ASM_MESON_TAC[];
  DISCH_TAC ;
  TYPE_THEN `INV f (UNIONS U) (UNIONS V) t = x` SUBGOAL_TAC;
  TYPE_THEN `(UNIONS U x)` SUBGOAL_TAC;
  REWRITE_TAC[UNIONS;IN_ELIM_THM';IN   ];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[INVERSE_XY;IN ];
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let open_and_closed = prove_by_refinement(
  `!(f:A->B) U V. (topology_ U) /\ (topology_ V) /\
     (BIJ f (UNIONS U) (UNIONS V)) ==>
     ((!A. (U A ==> V (IMAGE f A))) <=>
    (!B. (closed_ U B) ==> (closed_ V (IMAGE f B))))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  REWRITE_TAC[closed];
  EQ_TAC;
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  SUBCONJ_TAC;
  UND 4;
  UND 2;
  (* should have worked:
    ASM_MESON_TAC[SUBSET;IN;BIJ;INJ;IMAGE;IN_ELIM_THM'  ];
    bug found?  *)
  REWRITE_TAC[BIJ;IN;INJ;SUBSET;IMAGE;IN_ELIM_THM'  ];
  DISCH_ALL_TAC;
  NAME_CONFLICT_TAC;
  TYPE_THEN `y:B`  X_GEN_TAC;
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  REWRITE_TAC[open_DEF];
  USE 5 (REWRITE_RULE[open_DEF]);
  TYPE_THEN `UNIONS U DIFF B` (USE 3 o SPEC);
  REWR 3;
  TYPE_THEN `IMAGE f (UNIONS U DIFF B) = (UNIONS V DIFF IMAGE f B)` SUBGOAL_TAC;
  ASM_MESON_TAC[DIFF_SURJ];
  ASM_MESON_TAC[];
  REWRITE_TAC[open_DEF];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `UNIONS U DIFF A` (USE 3 o SPEC);
  TYPE_THEN `UNIONS U DIFF A SUBSET UNIONS U /\ U (UNIONS U DIFF (UNIONS U DIFF A))` SUBGOAL_TAC;
  ASM_SIMP_TAC[sub_union ; DIFF_DIFF2 ];
  ASM_REWRITE_TAC[SUBSET_DIFF];
  DISCH_TAC ;
  REWR 3;
  TYPE_THEN `UNIONS V DIFF IMAGE f (UNIONS U DIFF A) = IMAGE f A` SUBGOAL_TAC;
  ASM_MESON_TAC[DIFF_SURJ; sub_union; DIFF_DIFF2];
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let hausdorff_homeomorphsim = prove_by_refinement(
  `!f U V. (BIJ (f:A->B) (UNIONS U) (UNIONS V)) /\ (continuous f U V) /\
    (compact U (UNIONS U)) /\ (hausdorff V) /\ (topology_ U) /\
    (topology_ V) ==> (homeomorphism f U V)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[homeomorphism];
  ASM_SIMP_TAC[open_and_closed];
  DISCH_ALL_TAC;
  TYPEL_THEN [`U`;`UNIONS U`;`B`] (fun t-> ASSUME_TAC (SPECL t closed_compact));
  REWR 7;
  WITH 6 (REWRITE_RULE[closed]);
  REWR 7;
  IMATCH_MP_TAC  compact_closed ;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC image_compact;
  TYPE_THEN `U` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  AND 8;
  USE 0 (REWRITE_RULE[BIJ;INJ;IN ]);
  AND 0;
  AND 10;
  REWRITE_TAC[SUBSET;IN_IMAGE];
  REWRITE_TAC[IN];
  USE 9 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)


(* ------------------------------------------------------------------ *)
(* the metric and topology on the real numbers *)
(* ------------------------------------------------------------------ *)

let d_real = euclid_def `d_real x y = ||. (x -. y)`;;

(*
let real_topology = euclid_def
     `real_topology = top_of_metric (UNIV,d_real)`;;
*)

let metric_real = prove_by_refinement(
  `metric_space (UNIV,d_real)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[metric_space;UNIV;d_real ];
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let continuous_euclid1 = prove_by_refinement(
  `!i  n. continuous (coord i)
    (top_of_metric (euclid n,d_euclid))
    (top_of_metric (UNIV,d_real))`,
  (* {{{ proof *)

  [
  TYPE_THEN `!i  n . IMAGE (coord i) (euclid n) SUBSET (UNIV) /\ metric_space (euclid n,d_euclid) /\ metric_space (UNIV,d_real)` SUBGOAL_TAC;
  REP_GEN_TAC;
  REWRITE_TAC[UNIV ;SUBSET;IN];
  REWRITE_TAC[metric_euclid;metric_real;GSYM UNIV];
  DISCH_TAC;
  DISCH_ALL_TAC;
  TYPEL_THEN [`i`;`n`] (USE 0 o SPECL);
  USE 0 (IMATCH_MP metric_continuous_continuous);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[metric_continuous;metric_continuous_pt];
  DISCH_ALL_TAC;
  RIGHT_TAC "delta";
  DISCH_ALL_TAC;
  REWRITE_TAC[d_real;IN;coord];
  TYPE_THEN `epsilon` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  GEN_TAC;
  DISCH_ALL_TAC;
  UND 4;
  IMATCH_MP_TAC  (REAL_ARITH  `(a <=. b) ==> ((b <. e) ==> (a <. e))`);
  ASM_MESON_TAC[proj_contraction];
  ]);;

  (* }}} *)


let interval_closed_ball = prove_by_refinement(
   `!a b . ? x r. (a <=. b) ==>
   ({x | euclid 1 x /\ a <= x 0 /\ x 0 <= b} =
    (closed_ball(euclid 1,d_euclid)) x r)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  TYPE_THEN `((a +b)/(&.2)) *# (dirac_delta 0)` EXISTS_TAC;
  TYPE_THEN `((b -a)/(&.2))` EXISTS_TAC;
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  REWRITE_TAC[closed_ball;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  (TAUT `(a ==> (b <=> d /\ c))  ==> (a /\ b <=> d /\ a /\ c)`);
  DISCH_ALL_TAC;
  TYPE_THEN `z = ((a + b) / &2 *# dirac_delta 0)` ABBREV_TAC;
  TYPE_THEN `euclid 1 z` SUBGOAL_TAC;
  EXPAND_TAC "z";
  MESON_TAC[euclid_dirac];
  DISCH_TAC;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[euclid1_abs];
  EXPAND_TAC "z";
  TYPE_THEN `t = x 0` ABBREV_TAC ;
  REWRITE_TAC[dirac_delta;euclid_scale];
  REDUCE_TAC ;
  REWRITE_TAC[GSYM INTERVAL_ABS ];
  IMATCH_MP_TAC  (TAUT `((a = d) /\ (b = C))    ==> ((a /\ b) <=> (C /\ d))`);
  ONCE_REWRITE_TAC[REAL_ARITH `((x <=. u + v) <=> (x - v <=. u)) /\ ((x - u <= v) <=> (x <=. v + u))`];
  CONJ_TAC;
  TYPE_THEN `(a + b) / &2 - (b - a) / &2 = a` SUBGOAL_TAC ;
  REWRITE_TAC[real_div];
  REWRITE_TAC[REAL_ARITH `(a+b)*C - (b-a)*C  = a*(&.2*C) `];
  REDUCE_TAC ;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  TYPE_THEN `(a+ b) /(&.2) + (b - a)/(&.2) = b` SUBGOAL_TAC;
  REWRITE_TAC[real_div];
  REWRITE_TAC[REAL_ARITH `(a+b) * C + (b - a) * C = b *(&.2*C)`];
  REDUCE_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
   ]);;
  (* }}} *)

let interval_euclid1_closed = prove_by_refinement(
  `!a b. closed_ (top_of_metric (euclid 1,d_euclid))
 {x | euclid 1 x /\ a <= x 0 /\ x 0 <= b}`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ASM_CASES_TAC `a <=. b`;
  ASSUME_TAC interval_closed_ball;
  TYPEL_THEN [`a`;`b`] (USE 1 o SPECL);
  (CHO 1);
  CHO 1;
  REWR 1;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC closed_ball_closed;
  REWRITE_TAC[metric_euclid];
  TYPE_THEN `{x | euclid 1 x /\ a <= x 0 /\ x 0 <= b}= EMPTY ` SUBGOAL_TAC ;
  REWRITE_TAC[EQ_EMPTY;IN_ELIM_THM' ];
  GEN_TAC;
  TYPE_THEN `t = x 0 ` ABBREV_TAC;
  KILL 1;
  IMATCH_MP_TAC  (TAUT `~(b /\ C) ==> ~( a /\ b/\ C)`);
  UND 0;
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  IMATCH_MP_TAC  empty_closed;
  IMATCH_MP_TAC  top_of_metric_top  ;
  REWRITE_TAC[metric_euclid];
  ]);;
  (* }}} *)

let interval_euclid1_bounded = prove_by_refinement(
  `!a b. metric_bounded
    ({x | euclid 1 x /\ a <= x 0 /\ x 0 <= b},d_euclid)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[metric_bounded];
  ASSUME_TAC interval_closed_ball;
  TYPEL_THEN [`a`;`b`] (USE 0 o SPECL);
  CHO 0;
  CHO 0;
  ASM_CASES_TAC `a <=. b`;
  REWR 0;
  ASM_REWRITE_TAC[];
  TYPE_THEN `x` EXISTS_TAC;
  TYPE_THEN `r + (&.1) ` EXISTS_TAC;
  REWRITE_TAC[open_ball;SUBSET;IN ;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 2;
  REWRITE_TAC[closed_ball;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 4;
  ASM_SIMP_TAC[euclid1_abs ];
  TYPE_THEN  `t = x 0` ABBREV_TAC;
  TYPE_THEN `s = x' 0` ABBREV_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `&.0 <=. r` SUBGOAL_TAC;
  UND 6;
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  UND 6;
  UND 7;
  REAL_ARITH_TAC ;
  TYPE_THEN `{x | euclid 1 x /\ a <= x 0 /\ x 0 <= b} = EMPTY` SUBGOAL_TAC;
  REWRITE_TAC[EQ_EMPTY;IN_ELIM_THM' ];
  GEN_TAC;
  TYPE_THEN `t = x 0 ` ABBREV_TAC;
  KILL 2;
  IMATCH_MP_TAC  (TAUT `~(b /\ C) ==> ~( a /\ b/\ C)`);
  UND 1;
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  REWRITE_TAC[EMPTY_SUBSET];
  ]);;
  (* }}} *)

let interval_euclid1_compact = prove_by_refinement(
  `!a b. compact (top_of_metric(euclid 1,d_euclid))
    {x | (euclid 1 x) /\ (a <=. (x 0)) /\ (x 0 <= b)}`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  TYPE_THEN `{x | euclid 1 x /\ a <= x 0 /\ x 0 <= b} SUBSET (euclid 1)` SUBGOAL_TAC;
  REWRITE_TAC [SUBSET;IN;IN_ELIM_THM' ];
  MESON_TAC[];
  DISCH_TAC;
  ASM_SIMP_TAC[compact_euclid];
  CONJ_TAC;
  MATCH_ACCEPT_TAC interval_euclid1_closed;
  MATCH_ACCEPT_TAC interval_euclid1_bounded;
  ]);;
  (* }}} *)

let interval_image = prove_by_refinement(
  `!a b. {x | a <=. x /\ (x <= b)} =
    IMAGE (coord 0) {x | euclid 1 x /\ a <= x 0 /\ x 0 <= b}`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM';IMAGE];
  GEN_TAC;
  EQ_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `x *# (dirac_delta 0)` EXISTS_TAC;
  REWRITE_TAC[coord_dirac;euclid_dirac;dirac_0];
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  CHO 0;
  USE 0 (REWRITE_RULE[coord]);
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let interval_compact = prove_by_refinement(
  `!a b. compact (top_of_metric (UNIV,d_real))
        {x | a <=. x /\ (x <=. b)} `,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[interval_image];
  IMATCH_MP_TAC  image_compact;
  TYPE_THEN `(top_of_metric (euclid 1,d_euclid))` EXISTS_TAC;
  REWRITE_TAC[continuous_euclid1;interval_euclid1_compact];
  SIMP_TAC[GSYM top_of_metric_unions;metric_real];
  REWRITE_TAC[UNIV;SUBSET;IN];
  ]);;
  (* }}} *)

let half_open = prove_by_refinement(
  `!a. top_of_metric(UNIV,d_real ) { x | x <. a}`,
  (* {{{ proof *)
  [
  GEN_TAC;
  ASSUME_TAC open_nbd ;
  TYPEL_THEN [`top_of_metric (UNIV,d_real)`;` {x | x < a}`] (USE 0 o ISPECL);
  USE 0 (SIMP_RULE[top_of_metric_top;metric_real ]);
  ASM_REWRITE_TAC[];
  GEN_TAC;
  TYPE_THEN `open_ball (UNIV,d_real) x (a - x)` EXISTS_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  DISCH_ALL_TAC;
  CONJ_TAC;
  REWRITE_TAC[open_ball;d_real ;IN;IN_ELIM_THM';UNIV ;SUBSET ];
  GEN_TAC ;
  UND 1;
  REAL_ARITH_TAC;
  CONJ_TAC;
  IMATCH_MP_TAC  (REWRITE_RULE[IN] open_ball_nonempty);
  REWRITE_TAC[metric_real; UNIV ];
  UND 1;
  REAL_ARITH_TAC;
  IMATCH_MP_TAC  open_ball_open;
  REWRITE_TAC[metric_real];
  ]);;
  (* }}} *)

let half_open_above = prove_by_refinement(
  `!a. top_of_metric(UNIV,d_real ) { x | a <. x}`,
  (* {{{ proof *)
  [
  GEN_TAC;
  ASSUME_TAC open_nbd ;
  TYPEL_THEN [`top_of_metric (UNIV,d_real)`;` {x | a <. x}`] (USE 0 o ISPECL);
  USE 0 (SIMP_RULE[top_of_metric_top;metric_real ]);
  ASM_REWRITE_TAC[];
  GEN_TAC;
  TYPE_THEN `open_ball (UNIV,d_real) x (x -. a)` EXISTS_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  DISCH_ALL_TAC;
  CONJ_TAC;
  REWRITE_TAC[open_ball;d_real ;IN;IN_ELIM_THM';UNIV ;SUBSET ];
  GEN_TAC ;
  UND 1;
  REAL_ARITH_TAC;
  CONJ_TAC;
  IMATCH_MP_TAC  (REWRITE_RULE[IN] open_ball_nonempty);
  REWRITE_TAC[metric_real; UNIV ];
  UND 1;
  REAL_ARITH_TAC;
  IMATCH_MP_TAC  open_ball_open;
  REWRITE_TAC[metric_real];
  ]);;
  (* }}} *)

let joinf = euclid_def `joinf (f:real -> A)  g a =
  (\ x . (if (x <. a) then (f x) else (g x)))`;;

let joinf_cont = prove_by_refinement(
  `!U a  (f:real -> A) g.
   (continuous f (top_of_metric(UNIV,d_real)) U) /\
   (continuous g (top_of_metric(UNIV,d_real)) U) /\
   (f a = (g a)) ==>
   ( (continuous (joinf f g a) (top_of_metric(UNIV,d_real)) U))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[continuous];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  REWRITE_TAC[IN ];
  ASSUME_TAC open_nbd;
  TYPEL_THEN [`top_of_metric (UNIV,d_real)`;`(preimage (UNIONS (top_of_metric (UNIV,d_real))) (joinf f g a) v)`] (USE 4 o ISPECL);
  USE 4 (SIMP_RULE [top_of_metric_top;metric_real  ]);
  ASM_REWRITE_TAC[];
  GEN_TAC;
  REWRITE_TAC[subset_preimage];
  RIGHT_TAC "B";
  DISCH_TAC;
  SIMP_TAC[GSYM top_of_metric_unions; metric_real];
  REWRITE_TAC[SUBSET_UNIV];
  MP_TAC (REAL_ARITH `(x = a) \/ (x <. a) \/ (a <. x)`);
  REP_CASES_TAC;
  TYPE_THEN `B = (preimage (UNIONS (top_of_metric (UNIV,d_real))) f  v) INTER (preimage (UNIONS (top_of_metric (UNIV,d_real)))  g v)` ABBREV_TAC ;
  TYPE_THEN `B` EXISTS_TAC;
  CONJ_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE;IN  ];
  GEN_TAC;
  LEFT_TAC "x";
  GEN_TAC ;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 9;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;IN_ELIM_THM';IN  ];
  REWRITE_TAC[REWRITE_RULE[IN] in_preimage;joinf ];
  COND_CASES_TAC;
  MESON_TAC[];
  MESON_TAC[];
  CONJ_TAC ;
  ASM_REWRITE_TAC[];
  UND 5;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;IN;IN_ELIM_THM'];
  REWRITE_TAC[REWRITE_RULE[IN] in_preimage];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[joinf];
  REWRITE_TAC[REAL_ARITH `~(a<. a)`];
  ASSUME_TAC top_of_metric_top;
  TYPEL_THEN [`UNIV:real -> bool`;`d_real `] (USE 8 o ISPECL);
  USE 8 (REWRITE_RULE[metric_real ]);
  USE 8 (REWRITE_RULE[topology]);
  EXPAND_TAC "B";
  KILL 7;
  TYPE_THEN `v` (USE 0 o SPEC);
  TYPE_THEN `v` (USE 1 o SPEC);
  ASM_MESON_TAC[IN ];
  (* 2nd case x < a *)
  TYPE_THEN `B = { x | x <. a } INTER (preimage (UNIONS (top_of_metric (UNIV,d_real))) f v)` ABBREV_TAC ;
  TYPE_THEN `B` EXISTS_TAC;
  CONJ_TAC;
  ASM_REWRITE_TAC[SUBSET;IN_IMAGE ; IN;joinf ];
  GEN_TAC ;
  LEFT_TAC "x";
  GEN_TAC ;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 9;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER ;IN ;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  USE 10 (REWRITE_RULE[REWRITE_RULE[IN] in_preimage]);
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  UND 5;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;IN;IN_ELIM_THM'];
  REWRITE_TAC[REWRITE_RULE[IN] in_preimage];
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 8;
  REWRITE_TAC[joinf];
  ASM_REWRITE_TAC[];
  ASSUME_TAC top_of_metric_top;
  TYPEL_THEN [`UNIV:real -> bool`;`d_real `] (USE 8 o ISPECL);
  USE 8 (REWRITE_RULE[metric_real ]);
  USE 8 (REWRITE_RULE[topology]);
  TYPE_THEN `v` (USE 0 o SPEC);
  TYPE_THEN `v` (USE 1 o SPEC);
  EXPAND_TAC "B";
  KILL 7;
  KILL 5;
  KILL 4;
  KILL 1;
  KILL 6;
  TYPEL_THEN [`{x | x < a}`;`preimage (UNIONS (top_of_metric (UNIV,d_real))) f v`] (USE 8 o ISPECL);
  RIGHT 1 "V";
  RIGHT 1 "V";
  AND 1;
  AND 1;
  REWR 0;
  USE 0 (REWRITE_RULE[IN]);
  REWR 5;
  USE 5 (REWRITE_RULE[half_open]);
  ASM_REWRITE_TAC[];
  (* case 3 a < x *)
  TYPE_THEN `B = { x | a <. x } INTER (preimage (UNIONS (top_of_metric (UNIV,d_real))) g v)` ABBREV_TAC ;
  TYPE_THEN `B` EXISTS_TAC;
  CONJ_TAC;
  ASM_REWRITE_TAC[SUBSET;IN_IMAGE ; IN;joinf ];
  GEN_TAC ;
  LEFT_TAC "x";
  GEN_TAC ;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 9;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER ;IN ;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  USE 10 (REWRITE_RULE[REWRITE_RULE[IN] in_preimage]);
  ASM_REWRITE_TAC[];
  USE 9 (MATCH_MP (REAL_ARITH `a < x'' ==> (~(x'' <. a))`));
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  UND 5;
  EXPAND_TAC "B";
  REWRITE_TAC[INTER;IN;IN_ELIM_THM'];
  REWRITE_TAC[REWRITE_RULE[IN] in_preimage];
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  UND 8;
  REWRITE_TAC[joinf];
  USE 6 (MATCH_MP (REAL_ARITH `a < x'' ==> (~(x'' <. a))`));
  ASM_REWRITE_TAC[];
  ASSUME_TAC top_of_metric_top;
  TYPEL_THEN [`UNIV:real -> bool`;`d_real `] (USE 8 o ISPECL);
  USE 8 (REWRITE_RULE[metric_real ]);
  USE 8 (REWRITE_RULE[topology]);
  TYPE_THEN `v` (USE 0 o SPEC);
  TYPE_THEN `v` (USE 1 o SPEC);
  EXPAND_TAC "B";
  KILL 7;
  KILL 5;
  KILL 4;
  KILL 0;
  KILL 6;
  TYPEL_THEN [`{x | a < x}`;`preimage (UNIONS (top_of_metric (UNIV,d_real))) g v`] (USE 8 o ISPECL);
  RIGHT 0 "V";
  RIGHT 0 "V";
  AND 0;
  AND 0;
  REWR 1;
  USE 1 (REWRITE_RULE[IN]);
  REWR 5;
  USE 5 (REWRITE_RULE[half_open_above]);
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let neg_cont = prove_by_refinement(
  `continuous ( --.)
     (top_of_metric(UNIV,d_real)) (top_of_metric(UNIV,d_real))  `,
  (* {{{ proof *)
  [
  TYPE_THEN `IMAGE ( --. ) (UNIV) SUBSET (UNIV)` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN;UNION;UNIV ];
  DISCH_TAC;
  ASM_SIMP_TAC[metric_continuous_continuous;metric_real ];
  REWRITE_TAC[metric_continuous;metric_continuous_pt];
  DISCH_ALL_TAC;
  TYPE_THEN `epsilon` EXISTS_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[UNIV;IN;d_real  ];
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let add_cont = prove_by_refinement(
  `!u. (continuous ( (+.) u))
      (top_of_metric(UNIV,d_real)) (top_of_metric(UNIV,d_real))  `,
  (* {{{ proof *)

  [
  GEN_TAC;
  TYPE_THEN `IMAGE ( (+.) u ) (UNIV) SUBSET (UNIV)` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN;UNION;UNIV ];
  DISCH_TAC;
  ASM_SIMP_TAC[metric_continuous_continuous;metric_real ];
  REWRITE_TAC[metric_continuous;metric_continuous_pt];
  DISCH_ALL_TAC;
  TYPE_THEN `epsilon` EXISTS_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[UNIV;IN;d_real  ];
  REAL_ARITH_TAC;
  ]);;

  (* }}} *)

let continuous_scale = prove_by_refinement(
  `!x n. (euclid n x) ==>
     (continuous (\t. (t *# x)) (top_of_metric(UNIV,d_real))
     (top_of_metric(euclid n,d_euclid)))`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  ASSUME_TAC metric_euclid;
  ASSUME_TAC metric_real ;
  TYPE_THEN `IMAGE (\t. (t *# x)) (UNIV) SUBSET (euclid n)` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE;IN_ELIM_THM'];
  REWRITE_TAC[Q_ELIM_THM'';IN ; UNIV ];
  ASM_MESON_TAC[euclid_scale_closure];
  ASM_SIMP_TAC[metric_continuous_continuous];
  DISCH_TAC;
  REWRITE_TAC[metric_continuous;metric_continuous_pt];
  DISCH_ALL_TAC;
  REWRITE_TAC[IN;UNIV];
  TYPE_THEN `euclidean x` SUBGOAL_TAC;
  ASM_MESON_TAC[euclidean];
  ASM_SIMP_TAC[norm_scale;d_real];
  DISCH_TAC;
  TYPE_THEN `norm x <=. &.1`  ASM_CASES_TAC ;
  TYPE_THEN `epsilon` EXISTS_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  MP_TAC (SPEC `x' -. y` REAL_ABS_POS);
  DISCH_TAC ;
  USE 5 (MATCH_MP (SPEC `x' -. y` REAL_PROP_LE_LABS));
  USE 5 (CONV_RULE REDUCE_CONV);
  UND 5;
  UND 7;
  REAL_ARITH_TAC ;
  TYPE_THEN `epsilon / norm x` EXISTS_TAC;
  DISCH_ALL_TAC;
  CONJ_TAC;
  IMATCH_MP_TAC  REAL_LT_DIV;
  ASM_REWRITE_TAC[];
  UND 5;
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x <= &.1) ==> (&.0 <. x)`;REAL_LT_RDIV_EQ];
  ]);;

  (* }}} *)

let continuous_lin_combo = prove_by_refinement(
  `! x y n. (euclid n x) /\ (euclid n y) ==>
    (continuous (\t. (t *# x + (&.1 - t) *# y))
     (top_of_metric(UNIV,d_real))
     (top_of_metric(euclid n,d_euclid)))`,
  (* {{{ proof *)

  let comp_elim_tac = (  IMATCH_MP_TAC  continuous_comp THEN
  TYPE_THEN `(top_of_metric (UNIV,d_real))` EXISTS_TAC THEN
  ASM_SIMP_TAC[add_cont;neg_cont;continuous_scale] THEN
  REWRITE_TAC[SUBSET;IN_IMAGE;Q_ELIM_THM''] THEN
  SIMP_TAC[GSYM top_of_metric_unions ;metric_real;IN_UNIV ] ) in
  [
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  continuous_sum;
  ASM_SIMP_TAC[metric_real;metric_euclid;top_of_metric_top;continuous_scale;SUBSET ;IN_IMAGE;Q_ELIM_THM'' ];
  ASM_SIMP_TAC[IN;euclid_scale_closure;continuous_scale];
  TYPE_THEN `(\t . (&. 1 - t) *# y) = (\t. t *# y) o ((--.) o ((+.) (--. (&.1))))` SUBGOAL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  REWRITE_TAC[o_DEF;REAL_ARITH `--.(--. u +. v) = (u -. v)`];
  DISCH_THEN (fun t-> REWRITE_TAC [t]);
  REPEAT comp_elim_tac;
  ]);;

  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Connected Sets  *)
(* ------------------------------------------------------------------ *)

let connected = euclid_def `connected U (Z:A->bool) <=>
   (Z SUBSET (UNIONS U)) /\
   (!A B. (U A) /\ (U B) /\ (A INTER B = EMPTY ) /\
    (Z SUBSET (A UNION B)) ==> ((Z SUBSET A) \/ (Z SUBSET B)))`;;

let connected_unions = prove_by_refinement(
  `!U (Z1:A->bool) Z2. (connected U Z1) /\ (connected U Z2) /\
    ~(Z1 INTER Z2 = EMPTY) ==> (connected U (Z1 UNION Z2))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[connected];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  SUBCONJ_TAC;
  REWRITE_TAC[UNION;SUBSET;IN;IN_ELIM_THM'   ];
  ASM_MESON_TAC[SUBSET ;IN];
  DISCH_TAC ;
  DISCH_ALL_TAC;
  TYPEL_THEN [`A`;`B`] (USE 1 o SPECL);
  REWR 1;
  TYPEL_THEN [`A`;`B`] (USE 3 o SPECL);
  REWR 3;
  WITH 9 (REWRITE_RULE[union_subset]);
  REWR 1;
  REWR 3;
  IMATCH_MP_TAC (TAUT  `(~b ==> a)   ==> (a \/ b)`);
  DISCH_ALL_TAC;
  USE 11 (REWRITE_RULE[union_subset]);
  (* start a case *)
  USE 4 (REWRITE_RULE[EMPTY_EXISTS]);
  CHO 4;
  USE 4 (REWRITE_RULE[IN;INTER;IN_ELIM_THM'  ]);
  REWRITE_TAC[union_subset];
  TYPE_THEN `~((Z1 SUBSET A) /\ (Z2 SUBSET B))` SUBGOAL_TAC;
  DISCH_ALL_TAC;
  USE 8 (REWRITE_RULE[EQ_EMPTY]);
  USE 8 (REWRITE_RULE[INTER;IN;IN_ELIM_THM' ]);
  ASM_MESON_TAC[SUBSET;IN];
  TYPE_THEN `~((Z2 SUBSET A) /\ (Z1 SUBSET B))` SUBGOAL_TAC;
  DISCH_ALL_TAC;
  USE 8 (REWRITE_RULE[EQ_EMPTY]);
  USE 8 (REWRITE_RULE[INTER;IN;IN_ELIM_THM' ]);
  ASM_MESON_TAC[SUBSET;IN];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let component_DEF = euclid_def `component U (x:A) y <=>
  (?Z. (connected U Z) /\ (Z x) /\ (Z y))`;;

let connected_sing = prove_by_refinement(
  `!U (x:A). (UNIONS U x) ==> (connected U {x})`,
  (* {{{ proof *)
  [
  REWRITE_TAC[connected];
  DISCH_ALL_TAC;
  CONJ_TAC;
  REWRITE_TAC[SUBSET;IN_SING ];
  ASM_MESON_TAC[IN];
  DISCH_ALL_TAC;
  UND 4;
  SET_TAC[];
  ]);;
  (* }}} *)

let component_refl = prove_by_refinement(
  `!U x. (UNIONS U x) ==> (component U x (x:A))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[component_DEF];
  ASM_MESON_TAC[IN_SING;IN;connected_sing];
  ]);;
  (* }}} *)

let component_symm = prove_by_refinement(
  `!U x y.  (component U x y) ==>
   (component U (y:A) x)`,
  (* {{{ proof *)
  [
  MESON_TAC[component_DEF];
  ]);;
  (* }}} *)

let component_trans = prove_by_refinement(
  `!U (x:A) y z. (component U x y) /\ (component U y z) ==>
   (component U x z)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[component_DEF];
  DISCH_ALL_TAC;
  CHO 0;
  CHO 1;
  TYPE_THEN `connected U (Z UNION Z')` SUBGOAL_TAC;
  IMATCH_MP_TAC connected_unions;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[EMPTY_EXISTS ];
  REWRITE_TAC[IN;INTER;IN_ELIM_THM' ];
  TYPE_THEN `y` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  TYPE_THEN `Z UNION Z'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[UNION;IN;IN_ELIM_THM' ];
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

(* based on the Bolzano lemma *)

let connect_real = prove_by_refinement(
  `!a b. connected (top_of_metric (UNIV,d_real))
    {x | a <=. x /\ x <=. b }`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[connected];
  ASSUME_TAC metric_real;
  ASM_SIMP_TAC[GSYM top_of_metric_unions];
  SUBCONJ_TAC;
  REWRITE_TAC[UNIV;SUBSET;IN ];
  DISCH_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `\ (u ,v ). ( u <. a) \/ (b <. v) \/ ({x | u <=. x /\ x <=. v } SUBSET A) \/ ({x | u <=. x /\ x <=. v } SUBSET B)` (fun t-> ASSUME_TAC (SPEC t BOLZANO_LEMMA ));
  UND 6;
  GBETA_TAC ;
  IMATCH_MP_TAC  (TAUT `((b ==> c ) /\ a ) ==> ((a ==> b) ==> c  )`);
  CONJ_TAC;
  DISCH_ALL_TAC;
  TYPEL_THEN [`a`;`b`] ((USE 6 o SPECL));
  USE 6 (REWRITE_RULE[ARITH_RULE `~(a <. a)`]);
  ASM_CASES_TAC `a <=. b`;
  REWR 6;
  TYPE_THEN `{x | a <=. x /\ x <=. b} = EMPTY ` SUBGOAL_TAC;
  IMATCH_MP_TAC  EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM';EMPTY];
  GEN_TAC;
  UND 7;
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  REWRITE_TAC[EMPTY_SUBSET];
  CONJ_TAC;
  DISCH_ALL_TAC;
  UND 8;
  UND 9;
  (* c1 *)
  USE 4 (REWRITE_RULE[EQ_EMPTY;INTER;IN;IN_ELIM_THM' ]);
  TYPE_THEN `b'` (USE 4 o SPEC);
  TYPE_THEN `{x | a' <=. x /\ x <=. b' } b'` SUBGOAL_TAC;
  ASM_REWRITE_TAC[IN_ELIM_THM'];
  REAL_ARITH_TAC;
  DISCH_TAC;
  TYPE_THEN `{x | b' <=. x /\ x <=. c  } b'` SUBGOAL_TAC;
  ASM_REWRITE_TAC[IN_ELIM_THM'];
  REAL_ARITH_TAC;
  DISCH_TAC;
  TYPE_THEN `{x | a' <=. x /\ x <=. b' } UNION {x | b' <=. x /\ x <= c  } = { x | a' <=. x /\ x <=. c }` SUBGOAL_TAC;
  REWRITE_TAC[UNION;IN;IN_ELIM_THM'];
  IMATCH_MP_TAC  EQ_EXT ;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  UND 6;
  UND 7;
  REAL_ARITH_TAC;
  DISCH_TAC;
  (* cr 1*)
  REPEAT (DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN (TRY (GEN_MESON_TAC 0 7 1[REAL_ARITH `(b < b' /\ b' <=. c ==> b <. c ) /\ (a' <=. b' /\ b' <. a ==> a' <. a)`]));
  IMATCH_MP_TAC  (TAUT `c  ==> (a \/ b \/ c \/ d)`);
  UND 10;
  DISCH_THEN (fun t-> REWRITE_TAC [GSYM t]);
  ASM_REWRITE_TAC[union_subset];
  (* ASM_MESON_TAC[SUBSET;IN]; should have worked *)
  PROOF_BY_CONTR_TAC;
  UND 11;
  UND 12;
  UND 9;
  UND 8;
  UND 4;
  REWRITE_TAC[SUBSET;IN];
  TYPE_THEN `R ={x | a' <=. x /\ x <=. b'}` ABBREV_TAC;
  TYPE_THEN `S = {x | b' <=. x /\ x <=. c}` ABBREV_TAC;
  MESON_TAC[]; (* ok now it works *)
  PROOF_BY_CONTR_TAC;
  UND 11;
  UND 12;
  UND 9;
  UND 8;
  UND 4;
  REWRITE_TAC[SUBSET;IN];
  TYPE_THEN `R ={x | a' <=. x /\ x <=. b'}` ABBREV_TAC;
  TYPE_THEN `S = {x | b' <=. x /\ x <=. c}` ABBREV_TAC;
  MESON_TAC[]; (* ok now it works *)
  IMATCH_MP_TAC  (TAUT `d  ==> (a \/ b \/ c \/ d)`);
  UND 10;
  DISCH_THEN (fun t-> REWRITE_TAC [GSYM t]);
  ASM_REWRITE_TAC[union_subset];
  (* cr 2*)
  DISCH_ALL_TAC;
  ASM_CASES_TAC `x <. a`;
  TYPE_THEN `&.1` EXISTS_TAC;
  REDUCE_TAC;
  DISCH_ALL_TAC;
  DISJ1_TAC ;
  UND 7;
  UND 6;
  REAL_ARITH_TAC;
  ASM_CASES_TAC `b <. x`;
  TYPE_THEN `&.1` EXISTS_TAC;
  REDUCE_TAC;
  DISCH_ALL_TAC;
  DISJ2_TAC;
  DISJ1_TAC;
  UND 9;
  UND 7;
  REAL_ARITH_TAC;
  TYPE_THEN ` (A UNION B) x` SUBGOAL_TAC;
  USE 5 (REWRITE_RULE[SUBSET;IN]);
  UND 5;
  DISCH_THEN (IMATCH_MP_TAC );
   REWRITE_TAC[IN_ELIM_THM'];
  UND 7;
  UND 6;
  REAL_ARITH_TAC;
  DISCH_TAC;
  (* cr3 *)
  TYPEL_THEN [`UNIV:real -> bool`;`d_real`] (fun t-> (ASSUME_TAC (ISPECL t open_ball_nbd)));  (* --//-- *)
  USE 8 (REWRITE_RULE[REWRITE_RULE[IN] IN_UNION]);
  TYPE_THEN `A x` ASM_CASES_TAC; (*   *)
  TYPE_THEN `A` (USE 9 o SPEC);
  TYPE_THEN `x` (USE 9 o SPEC);  (* --//-- *)
  CHO 9;
  REWR 9;
  USE 9 (REWRITE_RULE[open_ball;d_real;UNIV ]);
  TYPE_THEN `e` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  (TAUT `C ==> (a \/ b \/ C\/ d)`);
  AND 9;
  UND 9;
  TYPE_THEN `{x | a' <=. x /\ x <=. b'} SUBSET {y | abs (x - y) <. e}` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM'];
  GEN_TAC;
  UND 11;
  UND 12;
  UND 13;
  REAL_ARITH_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM' ];
  MESON_TAC[];
  REWR 8;
  TYPE_THEN `B` (USE 9 o SPEC);
  TYPE_THEN `x` (USE 9 o SPEC);  (* --//-- *)
  CHO 9;
  REWR 9;
  USE 9 (REWRITE_RULE[open_ball;d_real;UNIV ]);
  TYPE_THEN `e` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  IMATCH_MP_TAC  (TAUT `d ==> (a \/ b \/ C\/ d)`);
  AND 9;
  UND 9;
  TYPE_THEN `{x | a' <=. x /\ x <=. b'} SUBSET {y | abs (x - y) <. e}` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM'];
  GEN_TAC;
  UND 11;
  UND 12;
  UND 13;
  REAL_ARITH_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM' ];
  MESON_TAC[];
  ]);;
  (* }}} *)

let connect_image = prove_by_refinement(
  `!f U V Z. (continuous (f:A->B) U V) /\
    (IMAGE f Z SUBSET (UNIONS V)) /\ (connected U Z) ==>
    (connected V (IMAGE f Z))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[connected];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  USE 0 (REWRITE_RULE[continuous;IN ]);
  TYPE_THEN `A` (WITH 0 o SPEC);
  TYPE_THEN `B` (USE  0 o SPEC);
  TYPE_THEN `(preimage (UNIONS U) f A)` (USE 3 o SPEC);
  TYPE_THEN `(preimage (UNIONS U) f B)` (USE 3 o SPEC);
  USE 6 (MATCH_MP preimage_disjoint  );
  TYPE_THEN `Z SUBSET preimage (UNIONS U) f A UNION preimage (UNIONS U) f B` SUBGOAL_TAC;
  REWRITE_TAC[preimage_union];
  ASM_REWRITE_TAC[];
  USE 3 (REWRITE_RULE[subset_preimage ]);
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let path = euclid_def `path U x y <=>
  (?f a b. (continuous f (top_of_metric(UNIV,d_real )) U ) /\
    (f a = (x:A)) /\ (f b = y))`;;

(**** Old proof modified by JRH to avoid use of GSPEC

let const_continuous = prove_by_refinement(
  `!U V y. (topology_ U)  ==>
    (continuous (\ (x:A). (y:B)) U V)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[continuous];
  DISCH_ALL_TAC;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  REWRITE_TAC[preimage;IN ];
  TYPE_THEN `v y` ASM_CASES_TAC ;
  ASM_REWRITE_TAC[IN_ELIM_THM;GSPEC  ];
  USE 0 (MATCH_MP top_univ);
  TYPE_THEN`t = UNIONS U`  ABBREV_TAC;
  UND 0;
  REWRITE_TAC[ETA_AX];
  ASM_REWRITE_TAC[GSPEC ];
  USE 0 (MATCH_MP open_EMPTY);
  USE 0 (REWRITE_RULE[open_DEF ;EMPTY]);
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

****)

let const_continuous = prove_by_refinement(
  `!U V y. (topology_ U)  ==>
    (continuous (\ (x:A). (y:B)) U V)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[continuous];
  DISCH_ALL_TAC;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  REWRITE_TAC[preimage;IN ];
  TYPE_THEN `v y` ASM_CASES_TAC ;
  ASM_REWRITE_TAC[IN_ELIM_THM];
  USE 0 (MATCH_MP top_univ);
  TYPE_THEN`t = UNIONS U`  ABBREV_TAC;
  UND 0;
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`);
  AP_TERM_TAC;
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN];
  USE 0 (MATCH_MP open_EMPTY);
  USE 0 (REWRITE_RULE[open_DEF ;EMPTY]);
  ASM_REWRITE_TAC[];
  SUBGOAL_THEN `{x:A | F} = \x. F` SUBST1_TAC;
  REWRITE_TAC[EXTENSION; IN; IN_ELIM_THM];
  ASM_REWRITE_TAC[]
  ]);;
  (* }}} *)

let path_component = euclid_def `path_component U x y <=>
  (?f a b. (continuous f (top_of_metric(UNIV,d_real )) U ) /\ (a <. b) /\
    (f a = (x:A)) /\ (f b = y) /\
    (IMAGE f { t | a <=. t /\ t <=. b } SUBSET (UNIONS U)))`;;

let path_refl = prove_by_refinement(
  `!U x.  (UNIONS U x) ==> (path_component U x (x:A))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ASSUME_TAC (top_of_metric_top );
  TYPEL_THEN [`UNIV:real ->bool`;`d_real`] (USE 1 o ISPECL);
  USE 1 (REWRITE_RULE[metric_real ]);
  USE 1 (MATCH_MP const_continuous);
  REWRITE_TAC[path_component];
  TYPE_THEN `(\ (t:real). x)` EXISTS_TAC;
  ASM_REWRITE_TAC[IMAGE;IN;];
  TYPE_THEN `&.0` EXISTS_TAC;
  TYPE_THEN `&.1` EXISTS_TAC;
  CONJ_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[SUBSET;IN;IN_ELIM_THM'];
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)


let path_symm = prove_by_refinement(
`!U x y . (path_component U x (y:A)) ==> (path_component U y (x:A))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[path_component];
  DISCH_ALL_TAC;
  (CHO 0);
  (CHO 0);
  (CHO 0);
  TYPE_THEN `f o (--.)` EXISTS_TAC;
  TYPE_THEN `--. b` EXISTS_TAC;
  TYPE_THEN `--. a` EXISTS_TAC;
  CONJ_TAC;
  IMATCH_MP_TAC  continuous_comp;
  TYPE_THEN `(top_of_metric (UNIV,d_real))` EXISTS_TAC;
  REWRITE_TAC[neg_cont];
  SIMP_TAC[top_of_metric_top;  metric_real;  metric_euclidean;  metric_euclid;  metric_hausdorff;  GSYM top_of_metric_unions;  open_ball_open;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[UNIV;IN;SUBSET  ];
  CONJ_TAC ;
  AND 0;
  AND 0;
  UND 2;
  REAL_ARITH_TAC ;
  REWRITE_TAC[o_DEF ;];
  REDUCE_TAC ;
  ASM_REWRITE_TAC[];
  UND 0;
  REWRITE_TAC[IMAGE;IN;SUBSET;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  DISCH_ALL_TAC;
  CHO 5;
  USE 4 (CONV_RULE NAME_CONFLICT_CONV );
  TYPE_THEN `x'` (USE 4 o SPEC);
  UND 4;
  DISCH_THEN IMATCH_MP_TAC ;
  NAME_CONFLICT_TAC;
  TYPE_THEN `--. x''` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  UND 5;
  REAL_ARITH_TAC ;
  ]);;

  (* }}} *)

let path_symm_eq = prove_by_refinement(
`!U x y . (path_component U x (y:A)) <=> (path_component U y (x:A))`,
  (* {{{ proof *)
  [
  MESON_TAC[path_symm];
  ]);;
  (* }}} *)


let path_trans = prove_by_refinement(
  `!U x y (z:A). (path_component U x y) /\ (path_component U y z) ==>
  (path_component U x z)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[path_component];
  DISCH_ALL_TAC;
  CHO 0;
  CHO 0;
  CHO 0;
  CHO 1;
  CHO 1;
  CHO 1;
  TYPE_THEN `joinf f (f' o ((+.) (a' -. b))) b` EXISTS_TAC;
  TYPE_THEN `a` EXISTS_TAC;
  TYPE_THEN `b' +. (b - a')` EXISTS_TAC;
  CONJ_TAC; (* start of continuity *)
  IMATCH_MP_TAC  joinf_cont;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  IMATCH_MP_TAC  continuous_comp;
  TYPE_THEN `(top_of_metric (UNIV,d_real))` EXISTS_TAC;
  ASM_REWRITE_TAC [top_of_metric_top;  metric_real;  metric_euclidean;  metric_euclid;  metric_hausdorff;  GSYM top_of_metric_unions;  open_ball_open;];
  REWRITE_TAC[add_cont];
  ASM_SIMP_TAC [top_of_metric_top;  metric_real;  metric_euclidean;  metric_euclid;  metric_hausdorff;  GSYM top_of_metric_unions;  open_ball_open;];
  REWRITE_TAC[SUBSET;UNIV;IN;IN_ELIM_THM'];
  REWRITE_TAC[o_DEF];
  REDUCE_TAC;
  ASM_REWRITE_TAC[]; (* end of continuity *)
  CONJ_TAC; (* start real ineq *)
  AND 1;
  AND 1;
  AND 0;
  AND 0;
  UND 5;
  UND 3;
  REAL_ARITH_TAC; (* end of real ineq *)
  CONJ_TAC;
  REWRITE_TAC[joinf;o_DEF];
  ASM_REWRITE_TAC[]; (* end of JOIN statement *)
  CONJ_TAC; (* next JOIN statement *)
  REWRITE_TAC[joinf;o_DEF];
  TYPE_THEN `~(b' +. b -. a' <. b)` SUBGOAL_TAC;
  TYPE_THEN `(a' <. b') /\ (a <. b)` SUBGOAL_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  TYPE_THEN ` a' -. b +. b' +. b -. a' = b'` SUBGOAL_TAC;
  REAL_ARITH_TAC ;
    DISCH_THEN (fun t-> REWRITE_TAC[t]);
  ASM_REWRITE_TAC[]; (* end of next joinf *)
  TYPE_THEN `(a <=. b) /\ (b <=. (b' + b - a'))` SUBGOAL_TAC; (* subreal *)
  TYPE_THEN `(a' <. b') /\ (a <. b)` SUBGOAL_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_TAC; (* end of subreal *)
  USE 2 (MATCH_MP union_closed_interval);
  UND 2;
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  REWRITE_TAC[IMAGE_UNION;union_subset];
  CONJ_TAC; (* start of FIRST interval *)
  TYPE_THEN `IMAGE (joinf f (f' o (+.) (a' -. b)) b) {t | a <=. t /\ t <. b} = IMAGE f {t | a <=. t /\ t <. b}` SUBGOAL_TAC;
  REWRITE_TAC[joinf;IMAGE;IN_IMAGE ];
  IMATCH_MP_TAC  EQ_EXT;
  X_GEN_TAC `t:A`;
  REWRITE_TAC[IN_ELIM_THM'];
  EQ_TAC;
  DISCH_ALL_TAC;
  CHO 2;
  UND 2;
  DISCH_ALL_TAC;
  REWR 4;
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  CHO 2;
  UND 2;
  DISCH_ALL_TAC;
 TYPE_THEN `x'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun t-> REWRITE_TAC[t]); (* FIRST interval still *)
  TYPE_THEN `IMAGE f {t | a <=. t /\ t <. b} SUBSET IMAGE f {t | a <=. t /\ t <=. b} ` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE ;IN_ELIM_THM'];
  GEN_TAC;
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  MESON_TAC[REAL_ARITH `a <. b ==> a<=. b`];
  KILL 1;
  UND 0;
  DISCH_ALL_TAC;
  JOIN 0 5;
  USE 0 (MATCH_MP SUBSET_TRANS );
  ASM_REWRITE_TAC[]; (* end of FIRST interval *)
  (* lc 1*)
  TYPE_THEN `IMAGE (joinf f (f' o (+.) (a' -. b)) b) {t | b <=. t /\ t <=. b' + b -. a'}  = IMAGE f' {t | a' <=. t /\ t <=. b'}` SUBGOAL_TAC;
  REWRITE_TAC[joinf;IMAGE;IN_IMAGE ];
  IMATCH_MP_TAC  EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM'];
  NAME_CONFLICT_TAC ;
  X_GEN_TAC `t:A`;
  EQ_TAC;
  DISCH_ALL_TAC;
  CHO 2;
  UND 2;
  DISCH_ALL_TAC;
  TYPE_THEN `~(x' <. b)` SUBGOAL_TAC;
  UND 2;
  REAL_ARITH_TAC ;
  DISCH_TAC ;
  REWR 4;
  USE 4 (REWRITE_RULE[o_DEF]);
  TYPE_THEN `a' -. b +. x'` EXISTS_TAC; (* * *)
  ASM_REWRITE_TAC[];
  TYPE_THEN `(a' <. b') /\ (a <. b) /\ (b <=. x') /\ (x' <=. b' +. b -. a')` SUBGOAL_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  CHO 2;
  UND 2;
  DISCH_ALL_TAC;
  TYPE_THEN `x' +. b -. a'` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  SUBCONJ_TAC;
  UND 2;
  UND 3;
  REAL_ARITH_TAC;
  DISCH_ALL_TAC;
  TYPE_THEN `~(x' +. b -. a' <. b)` SUBGOAL_TAC;
  UND 5;
  REAL_ARITH_TAC ;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  REWRITE_TAC[o_DEF];
  AP_TERM_TAC;
  REAL_ARITH_TAC ;
  DISCH_THEN (fun t -> REWRITE_TAC [t]);
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let loc_path_conn = euclid_def `loc_path_conn U <=>
  !A x. (U A) /\ (A (x:A)) ==>
       (U (path_component (induced_top U A) x))`;;


let path_eq_conn = prove_by_refinement(
  `!U (x:A). (loc_path_conn U) /\ (topology_ U) ==>
    (path_component U x = component U x)`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  MATCH_MP_TAC EQ_EXT;
  X_GEN_TAC `y:A`;
  EQ_TAC ;
  REWRITE_TAC[path_component];
  DISCH_ALL_TAC;
  CHO 2;
  CHO 2;
  CHO 2;
  UND 2 THEN DISCH_ALL_TAC;
  REWRITE_TAC[component_DEF];
  TYPE_THEN `IMAGE f {t | a <= t /\ t <= b}` EXISTS_TAC;
  CONJ_TAC;
  IMATCH_MP_TAC  connect_image ;
  NAME_CONFLICT_TAC;
  TYPE_THEN `(top_of_metric (UNIV,d_real))` EXISTS_TAC ;
  ASM_REWRITE_TAC[connect_real ];
  REWRITE_TAC[IMAGE;IN;IN_ELIM_THM' ];
  CONJ_TAC;
  TYPE_THEN `a` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  UND 3;
  REAL_ARITH_TAC ;
  TYPE_THEN `b` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  UND 3;
  REAL_ARITH_TAC;
  REWRITE_TAC[component_DEF];
  DISCH_ALL_TAC;
  CHO 2;
  UND 2 THEN DISCH_ALL_TAC;
  USE 2 (REWRITE_RULE[connected]);
  UND 2 THEN DISCH_ALL_TAC;
  TYPE_THEN `path_component U x` (USE 5 o SPEC);
  TYPE_THEN `A = path_component U x` ABBREV_TAC;
  TYPE_THEN `B = UNIONS (IMAGE (\z. (path_component U z)) (Z DIFF A))` ABBREV_TAC ;
  TYPE_THEN `B` (USE 5 o SPEC);
  TYPE_THEN `U A /\ U B /\ (A INTER B = {}) /\ Z SUBSET A UNION B` SUBGOAL_TAC;
  WITH  0 (REWRITE_RULE[loc_path_conn]);
  TYPE_THEN `(UNIONS U)` (USE 8 o SPEC);
  TYPE_THEN `x` (USE   8 o SPEC);
  UND 8;
  ASM_SIMP_TAC[induced_top_unions];
  ASM_SIMP_TAC[top_univ];
  TYPE_THEN `UNIONS U x` SUBGOAL_TAC;
  USE 2 (REWRITE_RULE[SUBSET;IN;]);
  ASM_MESON_TAC[];
  DISCH_ALL_TAC;
  REWR 8;
  ASM_REWRITE_TAC[];
  (* dd *)
  CONJ_TAC;
  EXPAND_TAC "B";
  WITH  1 (REWRITE_RULE[topology]);
  TYPEL_THEN [`EMPTY:A->bool`;`EMPTY:A->bool`;`(IMAGE (\z. path_component U z) (Z DIFF A))`] (USE 10 o ISPECL);
  UND 10 THEN DISCH_ALL_TAC;
  UND 12 THEN (DISCH_THEN IMATCH_MP_TAC );
  REWRITE_TAC[SUBSET;IN_IMAGE];
  REWRITE_TAC[IN];
  NAME_CONFLICT_TAC;
  DISCH_ALL_TAC;
  CHO 12;
  ASM_REWRITE_TAC[];
  USE 0 (REWRITE_RULE[loc_path_conn]);
  TYPE_THEN `(UNIONS U)` (USE 0 o SPEC);
  USE 0 (  CONV_RULE NAME_CONFLICT_CONV);
  TYPE_THEN `x''` (USE   0 o SPEC);
  UND 0;
  ASM_SIMP_TAC[induced_top_unions];
  DISCH_THEN MATCH_MP_TAC;
  ASM_SIMP_TAC[top_univ];
  AND 12;
  USE 2 (REWRITE_RULE[SUBSET;IN]);
  USE 0 (REWRITE_RULE[DIFF;IN;IN_ELIM_THM' ]);
  ASM_MESON_TAC[];
  CONJ_TAC;
  REWRITE_TAC[EQ_EMPTY];
  DISCH_ALL_TAC;
  USE 10 (REWRITE_RULE[INTER;IN;IN_ELIM_THM' ]);
  AND 10;
  UND 10;
  EXPAND_TAC "B";
  REWRITE_TAC[UNIONS;IN_IMAGE ;IN_ELIM_THM' ];
  REWRITE_TAC[IN];
  LEFT_TAC "u";
  DISCH_ALL_TAC;
  AND 10;
  CHO 12;
  AND 12;
  REWR 10;
  UND 11;
  EXPAND_TAC "A";
  USE 10 (ONCE_REWRITE_RULE [path_symm_eq]);
  DISCH_TAC;
  JOIN 11 10;
  USE 10 (MATCH_MP path_trans);
  REWR 10;
  UND 10;
  UND 12;
  REWRITE_TAC[DIFF;IN;IN_ELIM_THM'];
  MESON_TAC[];
  REWRITE_TAC[SUBSET;IN;UNION;IN_ELIM_THM'];
  DISCH_ALL_TAC;
  TYPE_THEN `A x'` ASM_CASES_TAC;
  ASM_REWRITE_TAC[];
  DISJ2_TAC ;
  EXPAND_TAC "B";
  REWRITE_TAC[UNIONS;IN_IMAGE;IN_ELIM_THM' ];
  REWRITE_TAC[IN];
  LEFT_TAC "x";
  LEFT_TAC "x";
  TYPE_THEN `x'` EXISTS_TAC;
  TYPE_THEN `path_component U x'` EXISTS_TAC;
  ASM_REWRITE_TAC[DIFF;IN;IN_ELIM_THM' ];
  IMATCH_MP_TAC  path_refl;
  USE 2 (REWRITE_RULE[SUBSET;IN]);
  ASM_MESON_TAC[];
  DISCH_TAC ;
  REWR 5;
  UND 5;
  DISCH_THEN DISJ_CASES_TAC ;
  USE 5 (REWRITE_RULE[SUBSET;IN ;]);
  ASM_MESON_TAC[];
  UND 8 THEN DISCH_ALL_TAC;
  USE 10 (REWRITE_RULE[EQ_EMPTY]);
  TYPE_THEN `x` (USE 10 o SPEC);
  USE 10 (REWRITE_RULE[INTER;IN;IN_ELIM_THM']);
  USE 5 (REWRITE_RULE[SUBSET;IN;IN_ELIM_THM']);
  TYPE_THEN `A x` SUBGOAL_TAC;
  EXPAND_TAC "A";
  IMATCH_MP_TAC  path_refl ;
  USE 2 (REWRITE_RULE[SUBSET;IN;IN_ELIM_THM']);
  ASM_MESON_TAC[];
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)


let open_ball_star = prove_by_refinement(
  `!x r y t n. (open_ball(euclid n,d_euclid) x r y) /\
    (&.0 <=. t) /\ (t <=. &.1) ==>
   (open_ball(euclid n,d_euclid) x r ((t *# x + (&.1-t)*#y)))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[open_ball;IN_ELIM_THM' ];
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[euclid_scale_closure;euclid_add_closure];
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM trivial_lin_combo];
  ASSUME_TAC (SPEC `n:num` metric_translate_LEFT);
  TYPEL_THEN [`(&.1 - t) *# x`;`(&.1 - t)*# y`;`t *# x`] (USE 5 o ISPECL);
  UND 5;
  ASM_SIMP_TAC [euclid_scale_closure];
  ASM_MESON_TAC[norm_scale_vec;REAL_ARITH  `(&.0 <=. t) /\ (t <=. (&.1)) ==> (||. (&.1 - t) <=. &.1)`;REAL_ARITH `(b <= a) ==> ((a < C) ==> (b < C))`;GSYM REAL_MUL_LID;REAL_LE_RMUL;d_euclid_pos];
  ]);;

  (* }}} *)

let open_ball_path = prove_by_refinement(
  `!x r y n. (open_ball(euclid n,d_euclid) x r y) ==>
    (path_component
      (top_of_metric(open_ball(euclid n,d_euclid) x r,d_euclid)) y x)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[path_component ;];
  DISCH_ALL_TAC;
  TYPE_THEN `(\t. (t *# x + (&.1 - t) *# y))` EXISTS_TAC;
  EXISTS_TAC `&.0`;
  EXISTS_TAC `&.1`;
  REDUCE_TAC;
  TYPE_THEN `top_of_metric (open_ball (euclid n,d_euclid) x r,d_euclid) = (induced_top(top_of_metric(euclid n,d_euclid)) (open_ball (euclid n,d_euclid) x r))` SUBGOAL_TAC;
  ASM_MESON_TAC[open_ball_subset;metric_euclid;top_of_metric_induced ];
  DISCH_TAC ;
  TYPE_THEN `euclid n x /\ euclid n y` SUBGOAL_TAC;
  USE 0 (REWRITE_RULE[open_ball;IN_ELIM_THM' ]);
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  CONJ_TAC;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC continuous_induced;
  ASM_SIMP_TAC [top_of_metric_top;metric_euclid;open_ball_open];
  IMATCH_MP_TAC  continuous_lin_combo ;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  REWRITE_TAC[euclid_plus;euclid_scale];
  IMATCH_MP_TAC  EQ_EXT THEN BETA_TAC ;
  REDUCE_TAC;
  CONJ_TAC;
  REWRITE_TAC[euclid_plus;euclid_scale];
  IMATCH_MP_TAC  EQ_EXT THEN BETA_TAC ;
  REDUCE_TAC;
  REWRITE_TAC[SUBSET;IN_IMAGE;Q_ELIM_THM'' ];
  REWRITE_TAC[IN;IN_ELIM_THM'];
  TYPE_THEN `(UNIONS (top_of_metric (open_ball (euclid n,d_euclid) x r,d_euclid))) = (open_ball(euclid n,d_euclid) x r)` SUBGOAL_TAC;
  IMATCH_MP_TAC  (GSYM top_of_metric_unions);
  IMATCH_MP_TAC  metric_subspace;
  ASM_MESON_TAC[metric_euclid;open_ball_subset];
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  ASM_MESON_TAC [open_ball_star];
  ]);;

  (* }}} *)

let path_domain = prove_by_refinement(
  `!U x (y:A). path_component U x y <=>
  (?f a b. (continuous f (top_of_metric(UNIV,d_real )) U ) /\ (a <. b) /\
    (f a = (x:A)) /\ (f b = y) /\
    (IMAGE f UNIV SUBSET (UNIONS U)))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[path_component];
  DISCH_ALL_TAC;
  EQ_TAC;
  DISCH_TAC ;
  CHO 0;
  CHO 0;
  CHO 0;
  TYPE_THEN `joinf (\t. (f a)) (joinf f (\t. (f b)) b) a` EXISTS_TAC;
  TYPE_THEN `a` EXISTS_TAC;
  TYPE_THEN `b` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  IMATCH_MP_TAC  joinf_cont;
  ASM_SIMP_TAC[const_continuous;top_of_metric_top;metric_real];
  CONJ_TAC;
  IMATCH_MP_TAC  joinf_cont;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[const_continuous;top_of_metric_top;metric_real];
  REWRITE_TAC[joinf];
  ASM_REWRITE_TAC[];
  CONJ_TAC;
  ASM_REWRITE_TAC[joinf;REAL_ARITH `~(a<a)`];
  CONJ_TAC;
  UND 0;
  DISCH_ALL_TAC;
  USE 1 (MATCH_MP (REAL_ARITH `(a < b) ==> (~(b < a))`));
  ASM_REWRITE_TAC  [joinf;REAL_ARITH `~(b < b)`];
  REWRITE_TAC[SUBSET;IN_IMAGE;Q_ELIM_THM'';joinf   ];
  REWRITE_TAC[IN_UNIV];
  GEN_TAC;
  UND 0;
  DISCH_ALL_TAC;
  USE 4 (REWRITE_RULE[SUBSET;IN_IMAGE;Q_ELIM_THM'';]);
  USE 4 (REWRITE_RULE[IN;IN_ELIM_THM' ]);
  (* cc1 *)
  TYPE_THEN `a` (WITH 4 o SPEC);
  TYPE_THEN `b` (WITH  4 o SPEC);
  TYPE_THEN `x'` (USE 4 o SPEC);
  DISJ_CASES_TAC (REAL_ARITH `x' < a \/ (a <= x')`);
  ASM_REWRITE_TAC[IN];
  ASM_MESON_TAC[REAL_ARITH `(a <=a) /\ ((a < b) ==> (a <= b))`];
  DISJ_CASES_TAC (REAL_ARITH `x' < b \/ (b <= x')`);
  REWR 4;
  USE 7 (MATCH_MP (REAL_ARITH `a <= x' ==> (~(x' < a))`));
  ASM_REWRITE_TAC[IN ];
  ASM_MESON_TAC[REAL_ARITH `x' < b ==> x' <= b`];
  USE 7 (MATCH_MP (REAL_ARITH `a <= x' ==> (~(x' < a))`));
  ASM_REWRITE_TAC[];
  USE 8 (MATCH_MP (REAL_ARITH `b <= x' ==> ~(x' < b)`));
  ASM_REWRITE_TAC[IN];
  ASM_MESON_TAC[REAL_ARITH `b <=b /\ ((a < b) ==> (a <= b))`];
  DISCH_TAC ;
  CHO 0;
  CHO 0;
  CHO 0;
  TYPE_THEN `f` EXISTS_TAC;
  TYPE_THEN `a ` EXISTS_TAC;
  TYPE_THEN `b` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  UND 0;
  REWRITE_TAC[SUBSET;IN_IMAGE ;Q_ELIM_THM''];
  REWRITE_TAC[IN_UNIV];
  REWRITE_TAC[IN;IN_ELIM_THM'];
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let path_component_subspace = prove_by_refinement(
  `!X Y d (y:A). ((Y SUBSET X) /\ (metric_space(X,d) /\ (Y y))) ==>
    ((path_component(top_of_metric(Y,d)) y) SUBSET
      (path_component(top_of_metric(X,d)) y))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[SUBSET;IN;path_domain];
  DISCH_ALL_TAC;
  CHO 3;
  CHO 3;
  CHO 3;
  TYPE_THEN `f` EXISTS_TAC;
  TYPE_THEN `a` EXISTS_TAC;
  TYPE_THEN `b` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `metric_space(Y,d)` SUBGOAL_TAC;
  ASM_MESON_TAC[metric_subspace];
  DISCH_TAC;
  UND 3;
  ASM_SIMP_TAC[GSYM top_of_metric_unions];
  DISCH_ALL_TAC;
  CONJ_TAC;
  UND 3;
  TYPE_THEN `IMAGE f UNIV SUBSET X /\ IMAGE f UNIV SUBSET Y` SUBGOAL_TAC;
  ASM_MESON_TAC[SUBSET;IN];
  DISCH_TAC;
  ASM_SIMP_TAC[metric_continuous_continuous;metric_real];
  REWRITE_TAC[metric_continuous;metric_continuous_pt];
  ASM_MESON_TAC[SUBSET;IN];
  ]);;
  (* }}} *)

let path_component_in  = prove_by_refinement(
  `!x (y:A) U. (path_component U x y) ==> (UNIONS U y)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[path_component];
  DISCH_ALL_TAC;
  CHO 0;
  CHO 0;
  CHO 0;
  UND 0;
  DISCH_ALL_TAC;
  USE 4 (REWRITE_RULE[SUBSET;IN_IMAGE;Q_ELIM_THM'']);
  USE 4 (REWRITE_RULE[IN_ELIM_THM';IN]);
  TYPE_THEN `b` (USE 4 o SPEC);
  ASM_MESON_TAC[REAL_ARITH `(a < b) ==> ((a<=. b) /\ (b <= b))`];
  ]);;
  (* }}} *)

let loc_path_conn_euclid = prove_by_refinement(
  `!n A. (top_of_metric(euclid n,d_euclid)) A ==>
   (loc_path_conn (top_of_metric(A,d_euclid)))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  REWRITE_TAC[loc_path_conn];
  DISCH_ALL_TAC;
  TYPE_THEN `metric_space (A,d_euclid)` SUBGOAL_TAC;
  IMATCH_MP_TAC  metric_subspace;
  TYPE_THEN `euclid n` EXISTS_TAC;
  REWRITE_TAC[metric_euclid];
  USE 0 (MATCH_MP sub_union);
  ASM_MESON_TAC[top_of_metric_unions;metric_euclid];
  DISCH_ALL_TAC;
  WITH  3 (MATCH_MP top_of_metric_nbd);
  UND 4;
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  TYPE_THEN `A' SUBSET A` SUBGOAL_TAC;
  USE 1 (MATCH_MP sub_union);
  ASM_MESON_TAC[top_of_metric_unions];
  DISCH_TAC;
  ASM_SIMP_TAC[top_of_metric_induced];
  TYPE_THEN `metric_space(A',d_euclid)` SUBGOAL_TAC;
  ASM_MESON_TAC[metric_subspace];
  DISCH_TAC ;
  SUBCONJ_TAC;
  REWRITE_TAC[SUBSET;IN];
  REWRITE_TAC[path_component];
  DISCH_ALL_TAC;
  CHO 6;
  CHO 6;
  CHO 6;
  USE 6 (REWRITE_RULE[SUBSET;IN_IMAGE ;IN_ELIM_THM';Q_ELIM_THM'']);
  UND 6;
  DISCH_ALL_TAC;
  TYPE_THEN `b` (USE 10 o SPEC);
  USE 4 (REWRITE_RULE[SUBSET;IN]);
  UND 4;
  DISCH_THEN IMATCH_MP_TAC ;
  USE 5 (MATCH_MP top_of_metric_unions);
  UND 10;
  UND 4;
  DISCH_THEN (fun t -> ONCE_REWRITE_TAC[GSYM t]);
  ASM_REWRITE_TAC[IN];
  ASM_MESON_TAC[REAL_ARITH `b <=. b /\ ((a < b)==> (a <=. b))`];
  DISCH_TAC;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  (* c2 *)
  WITH 7 (MATCH_MP path_component_in);
  TYPE_THEN `A' a` SUBGOAL_TAC;
  UND 8;
  ASM_SIMP_TAC[GSYM top_of_metric_unions;];
  DISCH_TAC;
  TYPE_THEN `A SUBSET (euclid n)` SUBGOAL_TAC;
  USE 0 (MATCH_MP sub_union);
  UND 0;
  ASM_SIMP_TAC[GSYM top_of_metric_unions;metric_euclid];
  DISCH_TAC;
  TYPE_THEN `top_of_metric(euclid n,d_euclid) A'` SUBGOAL_TAC;
  IMATCH_MP_TAC  induced_trans;
  TYPE_THEN `A` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[top_of_metric_top;metric_euclid;top_of_metric_induced ];
  DISCH_TAC;
  COPY 11;
  UND 12;
  SIMP_TAC[top_of_metric_nbd;metric_euclid];
  DISCH_ALL_TAC;
  TYPE_THEN `a` (USE 13 o SPEC);
  USE 13 (REWRITE_RULE[IN]);
  REWR 13;
  CHO 13;
  TYPE_THEN `r` EXISTS_TAC;
  ASM_REWRITE_TAC[];
  TYPE_THEN `open_ball (A,d_euclid) a r SUBSET path_component (top_of_metric (A',d_euclid)) a` SUBGOAL_TAC ;
  TYPE_THEN `open_ball (euclid n,d_euclid) a r SUBSET path_component (top_of_metric (A',d_euclid)) a` SUBGOAL_TAC ;
  TYPE_THEN `open_ball (euclid n,d_euclid) a r SUBSET  path_component (top_of_metric ((open_ball(euclid n,d_euclid) a r),d_euclid)) a` SUBGOAL_TAC;
  REWRITE_TAC[SUBSET;IN];
  MESON_TAC[open_ball_path;SUBSET;IN;path_symm];
  IMATCH_MP_TAC  (prove_by_refinement(`!A B C. (B:A->bool) SUBSET C ==> (A SUBSET B ==> A SUBSET C)`,[MESON_TAC[SUBSET_TRANS]]));
  IMATCH_MP_TAC  path_component_subspace;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC  (REWRITE_RULE[IN] open_ball_nonempty);
  ASM_SIMP_TAC[metric_euclid];
  ASM_MESON_TAC[SUBSET;IN];
  IMATCH_MP_TAC  (prove_by_refinement (`!A B C. (A:A->bool) SUBSET B ==> (B SUBSET C ==> A SUBSET C)`,[MESON_TAC[SUBSET_TRANS]]));
  ASM_SIMP_TAC[open_ball_subspace];
  IMATCH_MP_TAC  (prove_by_refinement(`!A B C. (B:A->bool) SUBSET C ==> (A SUBSET B ==> A SUBSET C)`,[MESON_TAC[SUBSET_TRANS]]));
  REWRITE_TAC[SUBSET;IN];
  GEN_TAC;
  UND 7;
  MESON_TAC[path_trans];
  ]);;
  (* }}} *)

let loc_path_euclid_cor = prove_by_refinement(
  `!n A . (top_of_metric(euclid n,d_euclid)) A ==>
     (path_component (top_of_metric(A,d_euclid)) =
      component (top_of_metric(A,d_euclid)))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  WITH 0 (MATCH_MP loc_path_conn_euclid);
  IMATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  IMATCH_MP_TAC path_eq_conn;
  ASM_REWRITE_TAC[];
  IMATCH_MP_TAC  top_of_metric_top;
  USE 0 (MATCH_MP sub_union);
  UND 0;
  ASM_SIMP_TAC[GSYM top_of_metric_unions ;metric_euclid];
  ASM_MESON_TAC[metric_subspace;metric_euclid];
  ]);;
  (* }}} *)
