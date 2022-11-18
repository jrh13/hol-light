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
(* There is also a pure projective analog without the T field.               *)
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

let projective = define
 `projective (f:A ring) (x,y) (X,Y,Z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        X IN ring_carrier f /\ Y IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(Z = ring_0 f) /\
        ring_div f X Z = x /\
        ring_div f Y Z = y`;;

let PROJECTIVE_ALT = prove
 (`!f x y X Y Z:A.
        field f
        ==> (projective f (x,y) (X,Y,Z) <=>
             x IN ring_carrier f /\ y IN ring_carrier f /\
             X IN ring_carrier f /\ Y IN ring_carrier f /\
             Z IN ring_carrier f /\
             ~(Z = ring_0 f) /\
             ring_mul f x Z = X /\
             ring_mul f y Z = Y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[projective] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIELD_TAC);;

let PROJECTIVE_EXPROJECTIVE = prove
 (`!f x y X Y Z:A.
        field f
        ==> (projective f (x,y) (X,Y,Z) <=>
             exprojective f (x,y)
              (X,Y,Z,ring_div f (ring_mul f X Y) Z))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[projective; exprojective] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC);;

let EXPROJECTIVE_PROJECTIVE = prove
 (`!f x y X Y Z W:A.
        field f
        ==> (exprojective f (x,y) (X,Y,Z,W) <=>
             projective f (x,y) (X,Y,Z) /\
             ring_div f (ring_mul f X Y) Z = W)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[projective; exprojective] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC);;

let EXPROJECTIVE_PROJECTIVE_ALT = prove
 (`!f x y X Y Z W:A.
        field f
        ==> (exprojective f (x,y) (X,Y,Z,W) <=>
             projective f (x,y) (X,Y,Z) /\
             W IN ring_carrier f /\
             ring_mul f X Y = ring_mul f W Z)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[projective; exprojective] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Characterizing when an (extended) projective point is on a curve          *)
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

let edwards_pcurve = define
 `edwards_pcurve (f,a,d) (X,Y,Z) <=>
     X IN ring_carrier f /\
     Y IN ring_carrier f /\
     Z IN ring_carrier f /\
     ~(Z = ring_0 f) /\
     ring_mul f (ring_pow f Z 2)
                (ring_add f (ring_mul f a (ring_pow f X 2)) (ring_pow f Y 2)) =
     ring_add f (ring_pow f Z 4)
     (ring_mul f d (ring_mul f (ring_pow f X 2) (ring_pow f Y 2)))`;;

let EDWARDS_PCURVE = prove
 (`!f (a:A) d p Q.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        projective f p Q
        ==> (edwards_curve (f,a,d) p <=> edwards_pcurve (f,a,d) Q)`,
  REWRITE_TAC[FORALL_PAIR_THM; projective;
              edwards_curve; edwards_pcurve] THEN
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
(*                                                                           *)
(* Since this doesn't use the T1 field, we have some mixed variants as well. *)
(* ------------------------------------------------------------------------- *)

let edwards_prexprojdouble = define
 `edwards_prexprojdouble (f,a:A,d:A) (X1,Y1,Z1) =
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
                     (ring_mul f a (ring_pow f X1 2))))))`;;

let EDWARDS_PREXPROJDOUBLE_EXPROJADD = prove
 (`!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) =
         edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1)`,
   REWRITE_TAC[FORALL_PAIR_THM; exprojective; LET_DEF; LET_END_DEF;
     edwards_excurve; edwards_exprojadd; edwards_prexprojdouble; PAIR_EQ] THEN
   REPEAT STRIP_TAC THEN FIELD_TAC);;

let EDWARDS_PREXPROJDOUBLE = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        projective f (x1,y1) (X1,Y1,Z1)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                           (edwards_prexprojdouble (f,a,d) (X1,Y1,Z1))`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[PROJECTIVE_EXPROJECTIVE] THEN
  ABBREV_TAC `T1:A = ring_div f (ring_mul f X1 Y1) Z1` THEN
  MP_TAC(ISPECL
   [`f:A ring`; `a:A`; `d:A`; `X1:A`; `Y1:A`; `Z1:A`; `T1:A`]
   EDWARDS_PREXPROJDOUBLE_EXPROJADD) THEN
  MP_TAC(ISPECL
   [`f:A ring`; `a:A`; `d:A`; `(x1:A,y1:A)`; `(X1:A,Y1:A,Z1:A,T1:A)`]
   EDWARDS_EXCURVE) THEN
  ASM_SIMP_TAC[EDWARDS_EXPROJADD]);;

let edwards_exprojdouble = define
 `edwards_exprojdouble (f,a:A,d) (X1,Y1,Z1,T1:A) =
    edwards_prexprojdouble (f,a,d) (X1,Y1,Z1)`;;

let EDWARDS_EXPROJDOUBLE_EXPROJADD = prove
 (`!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_exprojdouble (f,a,d) (X1,Y1,Z1,T1) =
         edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1)`,
   REWRITE_TAC[FORALL_PAIR_THM; exprojective; LET_DEF; LET_END_DEF;
     edwards_excurve; edwards_exprojadd;
     edwards_exprojdouble; edwards_prexprojdouble; PAIR_EQ] THEN
   REPEAT STRIP_TAC THEN FIELD_TAC);;

let EDWARDS_EXPROJDOUBLE = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1 T1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                           (edwards_exprojdouble (f,a,d) (X1,Y1,Z1,T1))`,
  SIMP_TAC[IMP_CONJ; EXPROJECTIVE_PROJECTIVE;
           edwards_exprojdouble; EDWARDS_PREXPROJDOUBLE]);;

let edwards_projdouble = define
 `edwards_projdouble (f,a:A,d) (X1,Y1,Z1) =
    let X2,Y2,Z2,T2 = edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) in
    (X2,Y2,Z2)`;;

let EDWARDS_PROJDOUBLE = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        projective f (x1,y1) (X1,Y1,Z1)
        ==> projective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                         (edwards_projdouble (f,a,d) (X1,Y1,Z1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EDWARDS_PREXPROJDOUBLE) THEN
  REWRITE_TAC[edwards_projdouble; edwards_prexprojdouble;
              LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[EXPROJECTIVE_PROJECTIVE; edwards_add]);;

(* ------------------------------------------------------------------------- *)
(* A negated doubling variant.                                               *)
(* ------------------------------------------------------------------------- *)

let edwards_prexprojdoublen = define
 `edwards_prexprojdoublen (f,a:A,d:A) (X1,Y1,Z1) =
    let X3,Y3,Z3,T3 = edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) in
    (ring_neg f X3,
     ring_neg f Y3,
     ring_neg f Z3,
     ring_neg f T3)`;;

let EDWARDS_PREXPROJDOUBLEN_EXPROJADDN = prove
 (`!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_prexprojdoublen (f,a,d) (X1,Y1,Z1) =
         edwards_exprojaddn (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1)`,
  REWRITE_TAC[edwards_prexprojdoublen; edwards_exprojaddn] THEN
  ASM_SIMP_TAC[GSYM EDWARDS_PREXPROJDOUBLE_EXPROJADD]);;

let EDWARDS_PREXPROJDOUBLEN = prove
 (`!(f:A ring) a d x1 y1 X1 Y1 Z1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        projective f (x1,y1) (X1,Y1,Z1)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                           (edwards_prexprojdoublen (f,a,d) (X1,Y1,Z1))`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[PROJECTIVE_EXPROJECTIVE] THEN
  ABBREV_TAC `T1:A = ring_div f (ring_mul f X1 Y1) Z1` THEN
  MP_TAC(ISPECL
   [`f:A ring`; `a:A`; `d:A`; `X1:A`; `Y1:A`; `Z1:A`; `T1:A`]
   EDWARDS_PREXPROJDOUBLEN_EXPROJADDN) THEN
  MP_TAC(ISPECL
   [`f:A ring`; `a:A`; `d:A`; `(x1:A,y1:A)`; `(X1:A,Y1:A,Z1:A,T1:A)`]
   EDWARDS_EXCURVE) THEN
  ASM_SIMP_TAC[EDWARDS_EXPROJADDN]);;
