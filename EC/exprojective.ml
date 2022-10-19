(* ========================================================================= *)
(* Extended projective coordinates for Edwards curves.                       *)
(* ========================================================================= *)

needs "EC/edwards.ml";;

(* ------------------------------------------------------------------------- *)
(* An affine (x,y) is represented by a triple (X,Y,Z,T) where                *)
(*                                                                           *)
(* x = X / Z, y = Y / Z and x * y = T / Z (so X * Y = T * Z)                 *)
(*                                                                           *)
(* We often use W in place of T to avoid inconvenience over "true" in HOL.   *)
(* ------------------------------------------------------------------------- *)

let exprojective = define
 `exprojective (f:A ring) (x,y) (X,Y,Z,W) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        X IN ring_carrier f /\ Y IN ring_carrier f /\
        W IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(Z = ring_0 f) /\
        ring_div f X Z = x /\
        ring_div f Y Z = y /\
        ring_div f W Z = ring_mul f x y`;;

let EXPROJECTIVE_ALT = prove
 (`!f x y X Y Z W:A.
        field f
        ==> (exprojective f (x,y) (X,Y,Z,W) <=>
             x IN ring_carrier f /\ y IN ring_carrier f /\
             X IN ring_carrier f /\ Y IN ring_carrier f /\
             W IN ring_carrier f /\ Z IN ring_carrier f /\
             ~(Z = ring_0 f) /\
             ring_mul f x Z = X /\
             ring_mul f y Z = Y /\
             ring_mul f W Z = ring_mul f X Y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exprojective] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Characterizing when an extended projective point is on a curve            *)
(* ------------------------------------------------------------------------- *)

let edwards_excurve = define
 `edwards_excurve (f,a,d) (X,Y,Z,W) <=>
     X IN ring_carrier f /\
     Y IN ring_carrier f /\
     Z IN ring_carrier f /\
     W IN ring_carrier f /\
     ~(Z = ring_0 f) /\
     ring_add f (ring_mul f a (ring_pow f X 2)) (ring_pow f Y 2) =
     ring_add f (ring_pow f Z 2) (ring_mul f d (ring_pow f W 2))`;;

let EDWARDS_EXCURVE = prove
 (`!f (a:A) d p Q.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        exprojective f p Q
        ==> (edwards_curve (f,a,d) p <=> edwards_excurve (f,a,d) Q)`,
  REWRITE_TAC[FORALL_PAIR_THM; exprojective;
              edwards_curve; edwards_excurve] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unified addition formula from Hisal-Wong-Carter-Dawson.                   *)
(*                                                                           *)
(* (X1,Y1,Z1,T1) + (X2,Y2,Z2,T2) =                                           *)
(*   ((X1 * Y2 + Y1 * X2) * (Z1 * Z2 - d * T1 * T2),                         *)
(*    (Y1 * Y2 - a * X1 * X2) * (Z1 * Z2 + d * T1 * T2),                     *)
(*    (Z1 * Z2 - d * T1 * T2) * (Z1 * Z2 + d * T1 * T2),                     *)
(*    (Y1 * Y2 - a * X1 * X2) * (X1 * Y2 + Y1 * X2))                         *)
(* ------------------------------------------------------------------------- *)

let edwards_exprojadd = define
 `edwards_exprojadd (f,a,d) (X1:A,Y1,Z1,T1) (X2,Y2,Z2,T2) =
  ring_mul f (ring_add f (ring_mul f X1 Y2) (ring_mul f Y1 X2))
   (ring_sub f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),
   ring_mul f
   (ring_sub f (ring_mul f Y1 Y2) (ring_mul f a (ring_mul f X1 X2)))
   (ring_add f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),
   ring_mul f
   (ring_sub f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2)))
   (ring_add f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),
   ring_mul f
   (ring_sub f (ring_mul f Y1 Y2) (ring_mul f a (ring_mul f X1 X2)))
   (ring_add f (ring_mul f X1 Y2) (ring_mul f Y1 X2))`;;

let EDWARDS_EXPROJADD = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1 T1 x2 y2 X2 Y2 Z2 T2.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1) /\
        exprojective f (x2,y2) (X2,Y2,Z2,T2)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x2,y2))
                           (edwards_exprojadd (f,a,d)
                             (X1,Y1,Z1,T1) (X2,Y2,Z2,T2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EXPROJECTIVE_ALT; edwards_add; edwards_exprojadd] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[exprojective; edwards_curve] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`]
        EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN
  REPEAT(CONJ_TAC THENL [RING_CARRIER_TAC; ALL_TAC]) THEN
  RING_PULL_DIV_TAC THEN REPEAT(FIRST_X_ASSUM
   (SUBST_ALL_TAC o SYM o check (is_var o rand o concl))) THEN
  RING_PULL_DIV_TAC THEN FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* A variant with everything scaled by 4, which can be faster to compute.    *)
(* ------------------------------------------------------------------------- *)

let edwards_exprojadd4 = define
 `edwards_exprojadd4 (f,a,d) (X1:A,Y1,Z1,T1) (X2,Y2,Z2,T2) =
    let X3,Y3,Z3,T3 = edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) in
    (ring_mul f (ring_of_num f 4) X3,
     ring_mul f (ring_of_num f 4) Y3,
     ring_mul f (ring_of_num f 4) Z3,
     ring_mul f (ring_of_num f 4) T3)`;;

let EDWARDS_EXPROJADD4 = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1 T1 x2 y2 X2 Y2 Z2 T2.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1) /\
        exprojective f (x2,y2) (X2,Y2,Z2,T2)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x2,y2))
                           (edwards_exprojadd4 (f,a,d)
                             (X1,Y1,Z1,T1) (X2,Y2,Z2,T2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT2] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EXPROJECTIVE_ALT; edwards_add; edwards_exprojadd4;
               edwards_exprojadd; LET_DEF; LET_END_DEF] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[exprojective; edwards_curve] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`]
        EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN
  REPEAT(CONJ_TAC THENL [RING_CARRIER_TAC; ALL_TAC]) THEN
  RING_PULL_DIV_TAC THEN REPEAT(FIRST_X_ASSUM
   (SUBST_ALL_TAC o SYM o check (is_var o rand o concl))) THEN
  RING_PULL_DIV_TAC THEN FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

(* ------------------------------------------------------------------------- *)
(* Similarly, a variant with everything negated.                             *)
(* ------------------------------------------------------------------------- *)

let edwards_exprojaddn = define
 `edwards_exprojaddn (f,a,d) (X1:A,Y1,Z1,T1) (X2,Y2,Z2,T2) =
    let X3,Y3,Z3,T3 = edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) in
    (ring_neg f X3,
     ring_neg f Y3,
     ring_neg f Z3,
     ring_neg f T3)`;;

let EDWARDS_EXPROJADDN = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1 T1 x2 y2 X2 Y2 Z2 T2.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1) /\
        exprojective f (x2,y2) (X2,Y2,Z2,T2)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x2,y2))
                           (edwards_exprojaddn (f,a,d)
                             (X1,Y1,Z1,T1) (X2,Y2,Z2,T2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EXPROJECTIVE_ALT; edwards_add; edwards_exprojaddn;
               edwards_exprojadd; LET_DEF; LET_END_DEF] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[exprojective; edwards_curve] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`]
        EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN
  REPEAT(CONJ_TAC THENL [RING_CARRIER_TAC; ALL_TAC]) THEN
  RING_PULL_DIV_TAC THEN REPEAT(FIRST_X_ASSUM
   (SUBST_ALL_TAC o SYM o check (is_var o rand o concl))) THEN
  RING_PULL_DIV_TAC THEN FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

(* ------------------------------------------------------------------------- *)
(* d-free doubling formula from Hisal-Wong-Carter-Dawson.                    *)
(*                                                                           *)
(* 2 * (X1,Y1,Z1,T1) =                                                       *)
(*     (2 * X1 * Y1 * (2 * Z1^2 - Y1^2 - a * X1^2),                          *)
(*      (Y1^2 + a * X1^2) * (Y1^2 - a * X1^2),                               *)
(*      (Y1^2 + a * X1^2) * (2 * Z1^2 - Y1^2 - a * X1^2),                    *)
(*      2 * X1 * Y1 * (Y1^2 - a * X1^2))                                     *)
(* ------------------------------------------------------------------------- *)

let EDWARDS_EXPROJADD_DOUBLE = prove
 (`!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1) =
         (ring_mul f (ring_of_num f 2)
             (ring_mul f X1
             (ring_mul f Y1
             (ring_sub f
              (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f Z1 2))
              (ring_pow f Y1 2))
             (ring_mul f a (ring_pow f X1 2))))),
          ring_mul f
             (ring_add f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))
             (ring_sub f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2))),
          ring_mul f
             (ring_add f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))
             (ring_sub f
              (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f Z1 2))
              (ring_pow f Y1 2))
             (ring_mul f a (ring_pow f X1 2))),
          ring_mul f (ring_of_num f 2)
             (ring_mul f X1
             (ring_mul f Y1
             (ring_sub f (ring_pow f Y1 2)
                         (ring_mul f a (ring_pow f X1 2))))))`,
  REWRITE_TAC[FORALL_PAIR_THM; exprojective; LET_DEF; LET_END_DEF;
              edwards_excurve; edwards_exprojadd; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  FIELD_TAC);;
