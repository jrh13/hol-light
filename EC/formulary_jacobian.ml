(* ========================================================================= *)
(* Specific formulas for evaluating Jacobian coordinate point operations.    *)
(* ========================================================================= *)

needs "EC/jacobian.ml";;

(* ------------------------------------------------------------------------- *)
(* Point doubling in Jacobian coordinates.                                   *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian/doubling/dbl-2007-bl.op3
 ***)

let ja_dbl_2007_bl = new_definition
 `ja_dbl_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) =
      let xx = ring_pow f x1 2 in
      let yy = ring_pow f y1 2 in
      let yyyy = ring_pow f yy 2 in
      let zz = ring_pow f z1 2 in
      let t0 = ring_add f x1 yy in
      let t1 = ring_pow f t0 2 in
      let t2 = ring_sub f t1 xx in
      let t3 = ring_sub f t2 yyyy in
      let s = ring_mul f (ring_of_num f 2) t3 in
      let t4 = ring_pow f zz 2 in
      let t5 = ring_mul f a t4 in
      let t6 = ring_mul f (ring_of_num f 3) xx in
      let m = ring_add f t6 t5 in
      let t7 = ring_pow f m 2 in
      let t8 = ring_mul f (ring_of_num f 2) s in
      let t = ring_sub f t7 t8 in
      let x3 = t in
      let t9 = ring_sub f s t in
      let t10 = ring_mul f (ring_of_num f 8) yyyy in
      let t11 = ring_mul f m t9 in
      let y3 = ring_sub f t11 t10 in
      let t12 = ring_add f y1 z1 in
      let t13 = ring_pow f t12 2 in
      let t14 = ring_sub f t13 yy in
      let z3 = ring_sub f t14 zz in
      (x3,y3,z3)`;;

let JA_DBL_2007_BL = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1)
        ==> jacobian_eq f (ja_dbl_2007_bl (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN STRIP_TAC THEN
  REWRITE_TAC[ja_dbl_2007_bl; jacobian_add; jacobian_eq;
              jacobian_neg; jacobian_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  FIELD_TAC THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let JA_DBL_2007_BL' = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> ja_dbl_2007_bl (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq; jacobian_0; PAIR_EQ;
                  jacobian_neg; jacobian_0; ja_dbl_2007_bl] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  FIELD_TAC THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Point doubling in Jacobian coordinates assuming a = -3.                   *)
(*                                                                           *)
(* Source: Bernstein [2001] "A software implementation of NIST P-224".       *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-3/doubling/dbl-2001-b.op3
 ***)

let j3_dbl_2001_b = new_definition
 `j3_dbl_2001_b (f:A ring,a:A,b:A) (x1,y1,z1) =
      let delta = ring_pow f z1 2 in
      let gamma = ring_pow f y1 2 in
      let beta = ring_mul f x1 gamma in
      let t0 = ring_sub f x1 delta in
      let t1 = ring_add f x1 delta in
      let t2 = ring_mul f t0 t1 in
      let alpha = ring_mul f (ring_of_num f 3) t2 in
      let t3 = ring_pow f alpha 2 in
      let t4 = ring_mul f (ring_of_num f 8) beta in
      let x3 = ring_sub f t3 t4 in
      let t5 = ring_add f y1 z1 in
      let t6 = ring_pow f t5 2 in
      let t7 = ring_sub f t6 gamma in
      let z3 = ring_sub f t7 delta in
      let t8 = ring_mul f (ring_of_num f 4) beta in
      let t9 = ring_sub f t8 x3 in
      let t10 = ring_pow f gamma 2 in
      let t11 = ring_mul f (ring_of_num f 8) t10 in
      let t12 = ring_mul f alpha t9 in
      let y3 = ring_sub f t12 t11 in
      (x3,y3,z3)`;;

let J3_DBL_2001_B = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1)
        ==> jacobian_eq f (j3_dbl_2001_b (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[j3_dbl_2001_b; jacobian_add; jacobian_eq;
              jacobian_neg; jacobian_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  FIELD_TAC THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let J3_DBL_2001_B' = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> j3_dbl_2001_b (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq; jacobian_0; PAIR_EQ;
                  jacobian_neg; jacobian_0; j3_dbl_2001_b] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  FIELD_TAC THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Point doubling in Jacobian coordinates assuming a = 0.                    *)
(*                                                                           *)
(* Source: Lange [2009].                                                     *)
(* ------------------------------------------------------------------------- *)

(***
 *** https://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/doubling/dbl-2009-l.op3
 ***)

let j0_dbl_2009_l = new_definition
 `j0_dbl_2009_l (f:A ring,a:A,b:A) (x1,y1,z1) =
      let a = ring_pow f x1 2 in
      let b = ring_pow f y1 2 in
      let c = ring_pow f b 2 in
      let t0 = ring_add f x1 b in
      let t1 = ring_pow f t0 2 in
      let t2 = ring_sub f t1 a in
      let t3 = ring_sub f t2 c in
      let d = ring_mul f (ring_of_num f 2) t3 in
      let e = ring_mul f (ring_of_num f 3) a in
      let g = ring_pow f e 2 in
      let t4 = ring_mul f (ring_of_num f 2) d in
      let x3 = ring_sub f g t4 in
      let t5 = ring_sub f d x3 in
      let t6 = ring_mul f (ring_of_num f 8) c in
      let t7 = ring_mul f e t5 in
      let y3 = ring_sub f t7 t6 in
      let t8 = ring_mul f y1 z1 in
      let z3 = ring_mul f (ring_of_num f 2) t8 in
      (x3,y3,z3)`;;

let J0_DBL_2009_L = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_0 f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1)
        ==> jacobian_eq f (j0_dbl_2009_l (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[j0_dbl_2009_l; jacobian_add; jacobian_eq;
              jacobian_neg; jacobian_0] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  FIELD_TAC THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

let J0_DBL_2009_L' = prove
 (`!f a b x1 y1 z1:A.
        field f /\
        a = ring_0 f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> j0_dbl_2009_l (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN
  ASM_CASES_TAC `z1:A = ring_0 f` THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq; jacobian_0; PAIR_EQ;
                  jacobian_neg; jacobian_0; j0_dbl_2009_l] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                  jacobian_neg; jacobian_0] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ; jacobian_eq] THEN
  FIELD_TAC THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Pure point addition in Jacobian coordinates. This sequence never uses     *)
(* the value of "a" so there's no special optimized version for special "a". *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(*                                                                           *)
(* Note the correctness is not proved in cases where the points are equal    *)
(* (or projectively equivalent), or either input is 0 (point at infinity).   *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian/addition/add-2007-bl.op3
 ***)

let ja_add_2007_bl = new_definition
 `ja_add_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let z1z1 = ring_pow f z1 2 in
      let z2z2 = ring_pow f z2 2 in
      let u1 = ring_mul f x1 z2z2 in
      let u2 = ring_mul f x2 z1z1 in
      let t0 = ring_mul f z2 z2z2 in
      let s1 = ring_mul f y1 t0 in
      let t1 = ring_mul f z1 z1z1 in
      let s2 = ring_mul f y2 t1 in
      let h = ring_sub f u2 u1 in
      let t2 = ring_mul f (ring_of_num f 2) h in
      let i = ring_pow f t2 2 in
      let j = ring_mul f h i in
      let t3 = ring_sub f s2 s1 in
      let r = ring_mul f (ring_of_num f 2) t3 in
      let v = ring_mul f u1 i in
      let t4 = ring_pow f r 2 in
      let t5 = ring_mul f (ring_of_num f 2) v in
      let t6 = ring_sub f t4 j in
      let x3 = ring_sub f t6 t5 in
      let t7 = ring_sub f v x3 in
      let t8 = ring_mul f s1 j in
      let t9 = ring_mul f (ring_of_num f 2) t8 in
      let t10 = ring_mul f r t7 in
      let y3 = ring_sub f t10 t9 in
      let t11 = ring_add f z1 z2 in
      let t12 = ring_pow f t11 2 in
      let t13 = ring_sub f t12 z1z1 in
      let t14 = ring_sub f t13 z2z2 in
      let z3 = ring_mul f t14 h in
      (x3,y3,z3)`;;

let JA_ADD_2007_BL = prove
 (`!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\ jacobian_point f (x2,y2,z2) /\
        ~(z1 = ring_0 f) /\ ~(z2 = ring_0 f) /\
        ~(jacobian_eq f (x1,y1,z1) (x2,y2,z2))
        ==> jacobian_eq f (ja_add_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_eq; ja_add_2007_bl; jacobian_add] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                   jacobian_neg; jacobian_0; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (free_in `(=):A->A->bool` o concl))) THEN
  FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mixed point addition in Jacobian coordinates. Here "mixed" means          *)
(* assuming z2 = 1, which holds if the second point was directly injected    *)
(* from the Weierstrass coordinates via (x,y) |-> (x,y,1). This never uses   *)
(* the value of "a" so there's no special optimized version for special "a". *)
(*                                                                           *)
(* Source: Bernstein-Lange [2007] "Faster addition and doubling..."          *)
(*                                                                           *)
(* Note the correctness is not proved in the case where the points are equal *)
(* or projectively equivalent, nor where the first is the group identity     *)
(* (i.e. the point at infinity, anything with z1 = 0 in projective coords).  *)
(* ------------------------------------------------------------------------- *)

(***
 *** http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-3/addition/add-2007-bl.op3
 ***)

let ja_madd_2007_bl = new_definition
 `ja_madd_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let z1z1 = ring_pow f z1 2 in
      let u2 = ring_mul f x2 z1z1 in
      let t0 = ring_mul f z1 z1z1 in
      let s2 = ring_mul f y2 t0 in
      let h = ring_sub f u2 x1 in
      let hh = ring_pow f h 2 in
      let i = ring_mul f (ring_of_num f 4) hh in
      let j = ring_mul f h i in
      let t1 = ring_sub f s2 y1 in
      let r = ring_mul f (ring_of_num f 2) t1 in
      let v = ring_mul f x1 i in
      let t2 = ring_pow f r 2 in
      let t3 = ring_mul f (ring_of_num f 2) v in
      let t4 = ring_sub f t2 j in
      let x3 = ring_sub f t4 t3 in
      let t5 = ring_sub f v x3 in
      let t6 = ring_mul f y1 j in
      let t7 = ring_mul f (ring_of_num f 2) t6 in
      let t8 = ring_mul f r t5 in
      let y3 = ring_sub f t8 t7 in
      let t9 = ring_add f z1 h in
      let t10 = ring_pow f t9 2 in
      let t11 = ring_sub f t10 z1z1 in
      let z3 = ring_sub f t11 hh in
      (x3,y3,z3)`;;

let JA_MADD_2007_BL = prove
 (`!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\ jacobian_point f (x2,y2,z2) /\
        z2 = ring_1 f /\
        ~(z1 = ring_0 f) /\ ~(jacobian_eq f (x1,y1,z1) (x2,y2,z2))
        ==> jacobian_eq f (ja_madd_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian_point] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[jacobian_eq; ja_madd_2007_bl; jacobian_add] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[jacobian_add; jacobian_eq;
                   jacobian_neg; jacobian_0; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (free_in `(=):A->A->bool` o concl))) THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;
