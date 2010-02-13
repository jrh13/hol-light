(* ========================================================================= *)
(* Thales's theorem.                                                         *)
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

let length_def = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;

let is_midpoint = new_definition
 `is_midpoint (m:real^2) (a,b) <=> m = (&1 / &2) % (a + b)`;;

(* ------------------------------------------------------------------------- *)
(* This formulation works.                                                   *)
(* ------------------------------------------------------------------------- *)

let THALES = prove
 (`!centre radius a b c.
        length(a,centre) = radius /\
        length(b,centre) = radius /\
        length(c,centre) = radius /\
        is_midpoint centre (a,b)
        ==> orthogonal (c - a) (c - b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[length_def; BETWEEN_THM; is_midpoint] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x pow 2`)) THEN
  REWRITE_TAC[NORM_POW_2] THEN FIRST_ASSUM(MP_TAC o SYM) THEN
  ABBREV_TAC `rad = radius pow 2` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
   orthogonal; CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* But for another natural version, we need to use the reals.                *)
(* ------------------------------------------------------------------------- *)

needs "Examples/sos.ml";;

(* ------------------------------------------------------------------------- *)
(* The following, which we need as a lemma, needs the reals specifically.    *)
(* ------------------------------------------------------------------------- *)

let MIDPOINT = prove
 (`!m a b. between m (a,b) /\ length(a,m) = length(b,m)
           ==> is_midpoint m (a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[length_def; BETWEEN_THM; is_midpoint; NORM_EQ] THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
   orthogonal; CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_SOS);;

(* ------------------------------------------------------------------------- *)
(* Now we get a more natural formulation of Thales's theorem.                *)
(* ------------------------------------------------------------------------- *)

let THALES = prove
 (`!centre radius a b c:real^2.
        length(a,centre) = radius /\
        length(b,centre) = radius /\
        length(c,centre) = radius /\
        between centre (a,b)
        ==> orthogonal (c - a) (c - b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `is_midpoint centre (a,b)` MP_TAC THENL
   [MATCH_MP_TAC MIDPOINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN `between (centre:real^2) (a,b)` (K ALL_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x pow 2`)) THEN
  REWRITE_TAC[length_def; is_midpoint; orthogonal; NORM_POW_2] THEN
  ABBREV_TAC `rad = radius pow 2` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
   orthogonal; CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
