(* ========================================================================= *)
(* #55: Theorem on product of segments of chords.                            *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Geometric concepts.                                                       *)
(* ------------------------------------------------------------------------- *)

let BETWEEN_THM = prove
 (`between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b`,
  REWRITE_TAC[BETWEEN_IN_CONVEX_HULL] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_2_ALT; IN_ELIM_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

let length = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;

(* ------------------------------------------------------------------------- *)
(* One more special reduction theorem to avoid square roots.                 *)
(* ------------------------------------------------------------------------- *)

let lemma = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (x pow 2 = y pow 2 <=> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[REAL_POW_2] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN
  ASM_MESON_TAC[REAL_LT_MUL2; REAL_LT_REFL]);;

let NORM_CROSS = prove
 (`norm(a) * norm(b) = norm(c) * norm(d) <=>
   (a dot a) * (b dot b) = (c dot c) * (d dot d)`,
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC(GSYM lemma) THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Now the main theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_CHORDS = prove
 (`!centre radius q r s t b.
        between b (q,r) /\ between b (s,t) /\
        length(q,centre) = radius /\ length(r,centre) = radius /\
        length(s,centre) = radius /\ length(t,centre) = radius
        ==> length(q,b) * length(b,r) = length(s,b) * length(b,t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[length; NORM_CROSS; BETWEEN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
   (MP_TAC o AP_TERM `\x. x pow 2`)) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[NORM_POW_2] THEN
  ABBREV_TAC `rad = radius pow 2` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
           CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
