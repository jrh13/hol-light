(* ========================================================================= *)
(* Specific formulas for evaluating (X,Z)-only projective point operations.  *)
(* ========================================================================= *)

needs "EC/xzprojective.ml";;

(* ------------------------------------------------------------------------- *)
(* Montgomery ladder step, XZ-coordinate differential addition and doubling. *)
(*                                                                           *)
(* Source: Montgomery [1987] "Speeding the Pollard and elliptic curve..."    *)
(* ------------------------------------------------------------------------- *)

(***
 ***
http://hyperelliptic.org/EFD/g1p/auto-code/montgom/xz/ladder/mladd-1987-m.op3
 ***)

let mladd_1987_m = new_definition
 `mladd_1987_m (f:A ring,a:A,b:A) a24 X1 (X2,Z2) (X3,Z3) =
        let A = ring_add f X2 Z2 in
        let AA = ring_pow f A 2 in
        let B = ring_sub f X2 Z2 in
        let BB = ring_pow f B 2 in
        let E = ring_sub f AA BB in
        let C = ring_add f X3 Z3 in
        let D = ring_sub f X3 Z3 in
        let DA = ring_mul f D A in
        let CB = ring_mul f C B in
        let t0 = ring_add f DA CB in
        let X5 = ring_pow f t0 2 in
        let t1 = ring_sub f DA CB in
        let t2 = ring_pow f t1 2 in
        let Z5 = ring_mul f X1 t2 in
        let X4 = ring_mul f AA BB in
        let t3 = ring_mul f a24 E in
        let t4 = ring_add f BB t3 in
        let Z4 = ring_mul f E t4 in
        (X4,Z4),(X5,Z5)`;;

let MLADD_1987_M = prove
 (`!f (a:A) b a24 X1 X2 Z2 X3 Z3.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        a24 IN ring_carrier f /\ X1 IN ring_carrier f /\
        X2 IN ring_carrier f /\ Z2 IN ring_carrier f /\
        X3 IN ring_carrier f /\ Z3 IN ring_carrier f /\
        ring_mul f (ring_of_num f 4) a24 = ring_add f a (ring_of_num f 2)
        ==> mladd_1987_m (f,a,b) a24 X1 (X2,Z2) (X3,Z3) =
                (montgomery_xzdouble (f,a,b) (X2,Z2),
                 montgomery_xzdiffadd (f,a,b) (X1,ring_1 f) (X2,Z2) (X3,Z3))`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[mladd_1987_m; montgomery_xzdouble; montgomery_xzdiffadd] THEN
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN FIELD_TAC THEN
  NOT_RING_CHAR_DIVIDES_TAC);;

(* ------------------------------------------------------------------------- *)
(* Recovering y coordinate within the projective representation.             *)
(*                                                                           *)
(* Source: Okeya and Sakurai [2001] "Efficient Elliptic Curve...", Alg. 1.   *)
(* ------------------------------------------------------------------------- *)

let okeya_sakurai_1 = new_definition
 `okeya_sakurai_1 (f:A ring,a:A,b:A) (x,y) (X1,Z1) (X2,Z2) =
        let a2 = ring_add f a a
        and b2 = ring_add f b b in
        let t1 = ring_mul f x Z1 in
        let t2 = ring_add f X1 t1 in
        let t3 = ring_sub f X1 t1 in
        let t3 = ring_mul f t3 t3 in
        let t3 = ring_mul f t3 X2 in
        let t1 = ring_mul f a2 Z1 in
        let t2 = ring_add f t2 t1 in
        let t4 = ring_mul f x X1 in
        let t4 = ring_add f t4 Z1 in
        let t2 = ring_mul f t2 t4 in
        let t1 = ring_mul f t1 Z1 in
        let t2 = ring_sub f t2 t1 in
        let t2 = ring_mul f t2 Z2 in
        let y' = ring_sub f t2 t3 in
        let t1 = ring_mul f b2 y in
        let t1 = ring_mul f t1 Z1 in
        let t1 = ring_mul f t1 Z2 in
        let x' = ring_mul f t1 X1 in
        let z' = ring_mul f t1 Z1 in
        (x',y',z')`;;

(*** Note the overarching assumption that the initial point is non-trivial
 *** and has nonzero y coordinate, although we do handle degeneracy in the
 *** result point.
 ***)

let OKEYA_SAKURAI_1 = prove
 (`!f (a:A) b x y p X1 Z1 X2 Z2.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        montgomery_curve (f,a,b) (SOME(x,y)) /\ ~(y = ring_0 f) /\
        montgomery_curve (f,a,b) p /\
        montgomery_xz f p (X1,Z1) /\
        montgomery_xz f (montgomery_add(f,a,b) (SOME(x,y)) p) (X2,Z2)
        ==> let x',y',z' = okeya_sakurai_1 (f,a,b) (x,y) (X1,Z1) (X2,Z2) in
            p = if z' = ring_0 f then
                 (if Z1 = ring_0 f then NONE else SOME(x,ring_neg f y))
                else SOME(ring_div f x' z',ring_div f y' z')`,
  MAP_EVERY X_GEN_TAC [`f:A ring`; `a:A`; `b:A`; `x:A`; `y:A`] THEN
  REWRITE_TAC[FIELD_CHAR_NOT2; FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; montgomery_xz; okeya_sakurai_1] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SPEC_TAC(`montgomery_add (f,a:A,b) (SOME(x,y)) NONE`,`q:(A#A)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; montgomery_xz] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; RING_0; RING_ADD; RING_MUL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `X1:A`; `Z1:A`; `X2:A`; `Z2:A`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[FIELD_MUL_EQ_0; RING_ADD; RING_MUL] THEN
  ASM_CASES_TAC `(X2:A) IN ring_carrier f /\ Z2 IN ring_carrier f` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [FIELD_MUL_EQ_0; RING_ADD; RING_MUL; RING_OF_NUM; RING_OF_NUM_EQ_0;
      RING_RULE `ring_add f b b:A = ring_mul f (ring_of_num f 2) b`];
   ASM_REWRITE_TAC[montgomery_add; LET_DEF; LET_END_DEF] THEN
   REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_xz]) THEN
   ASM_REWRITE_TAC[CONJ_ASSOC]] THEN
  REWRITE_TAC[montgomery_add; LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[montgomery_xz; option_DISTINCT; option_INJ; PAIR_EQ])
  THENL [FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC; FIELD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_of_num f 2:A = ring_0 f)` ASSUME_TAC THENL
   [FIELD_TAC; RING_PULL_DIV_TAC THEN DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL [FIELD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_sub f x1 x:A = ring_0 f)` ASSUME_TAC THENL
   [FIELD_TAC; RING_PULL_DIV_TAC THEN FIELD_TAC]);;
