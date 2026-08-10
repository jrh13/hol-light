(* ========================================================================= *)
(* Legendre's three-square theorem and Gauss's triangular number theorem.    *)
(*                                                                           *)
(* Main results: LEGENDRE_THREE_SQUARES characterizes the natural numbers    *)
(* that are sums of three squares; GAUSS_TRIANGULAR and                      *)
(* GAUSS_TRIANGULAR_SUM state that every natural number is a sum of three    *)
(* triangular numbers.                                                       *)
(*                                                                           *)
(* The development follows the self-contained elementary proof of Nathanson, *)
(* "Additive Number Theory: The Classical Bases", section 1.5:               *)
(*   (A) reduction theory of integral quadratic forms -- a positive-definite *)
(*       ternary form of discriminant 1 represents only sums of three        *)
(*       squares (Nathanson Thm 1.3, here TSQ_DISC1);                        *)
(*   (B) Lemma 1.7 (LEMMA_1_7 / LEMMA_1_7_CONG) -- if -d' is a quadratic     *)
(*       residue mod d'n - 1 then n is a sum of three squares (an explicit   *)
(*       discriminant-1 form representing n);                                *)
(*   (C) Lemmas 1.8/1.9 -- Dirichlet's theorem on primes in arithmetic       *)
(*       progressions together with quadratic reciprocity supply the needed  *)
(*       residue for each class n = 1,2,3,5,6 (mod 8);                       *)
(*   (D) the 4^a descent and parity assemble the full iff and Gauss's        *)
(*       theorem.                                                            *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/dirichlet.ml";;

prioritize_int();;

(* ------------------------------------------------------------------------- *)
(* Nearest-integer approximation and the resulting square bound.             *)
(* ------------------------------------------------------------------------- *)

let INT_BALANCED_REM = prove
 (`!x q:int. &0 < q ==> ?b. abs(x - q * b) * &2 <= q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:int`; `q:int`] INT_DIVISION) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = x rem q` THEN ABBREV_TAC `d = x div q` THEN STRIP_TAC THEN
  ASM_CASES_TAC `r * &2 <= q` THENL
   [EXISTS_TAC `d:int`; EXISTS_TAC `d + &1`] THEN ASM_INT_ARITH_TAC);;

let SQ_BOUND = prove
 (`!a q:int. abs a * &2 <= q ==> &4 * a pow 2 <= q pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(abs a * &2) pow 2 <= q pow 2` MP_TAC THENL
   [MATCH_MP_TAC INT_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_ABS_POS] THEN INT_ARITH_TAC;
    REWRITE_TAC[INT_POW_MUL; INT_POW2_ABS] THEN INT_ARITH_TAC]);;

(* ========================================================================= *)
(* QUADRATIC FORM REDUCTION THEORY (Nathanson sec 1.4-1.5). Forms are        *)
(* encoded by their integer matrix entries; a binary form is (A11,A12,A22)   *)
(* |-> A11 x^2 + 2 A12 x y + A22 y^2 with discriminant A11 A22 - A12^2, and  *)
(* similarly for ternary forms.                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Binary forms: positive-definiteness criterion (Nathanson Lemma 1.1, hard  *)
(* direction) and the discriminant-1 reduction theorem (Nathanson Thm 1.2):  *)
(* a positive-definite binary form of discriminant 1 represents only sums of *)
(* two squares. Proved by the classical reduce-and-swap descent on A11.      *)
(* ------------------------------------------------------------------------- *)

let POSDEF_BINARY_CRITERION = prove
 (`!A11 A12 A22:int.
     &0 < A11 /\ &0 < A11 * A22 - A12 pow 2
     ==> !x y. ~(x = &0 /\ y = &0)
               ==> &0 < A11 * x pow 2 + &2 * A12 * x * y + A22 * y pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `y = &0` THENL
   [SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(x = &0 /\ y = &0)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `A11*x pow 2 + &2*A12*x*y + A22*y pow 2 = A11 * x pow 2` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING; ALL_TAC] THEN
    MATCH_MP_TAC INT_LT_MUL THEN ASM_SIMP_TAC[INT_LT_POW_2];
    SUBGOAL_THEN
     `&0 < A11 *
       (A11*x pow 2 + &2*A12*x*y + A22*y pow 2)` MP_TAC THENL
     [SUBGOAL_THEN
     `A11 * (A11*x pow 2 + &2*A12*x*y + A22*y pow 2) =
      (A11*x + A12*y) pow 2 + (A11*A22 - A12 pow 2) * y pow 2`
     SUBST1_TAC THENL [CONV_TAC INT_RING; ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    REWRITE_TAC[INT_LE_POW_2] THEN
    MATCH_MP_TAC INT_LT_MUL THEN ASM_SIMP_TAC[INT_LT_POW_2];
    ASM_SIMP_TAC[INT_LT_MUL_EQ]]]);;

let BINARY_DISC1 = prove
 (`!A11. &0 < A11
   ==> !A12 A22. A11 * A22 - A12 pow 2 = &1
       ==> !n. (?x y. A11 * x pow 2 + &2 * A12 * x * y + A22 * y pow 2 = n)
               ==> ?u v:int. u pow 2 + v pow 2 = n`,
  MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC `abs:int->int` THEN
  REWRITE_TAC[INT_ABS_POS] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `x:int` (X_CHOOSE_TAC `y:int`)) THEN
  ASM_CASES_TAC `A11 = &1` THENL
   [MAP_EVERY EXISTS_TAC [`x + A12 * y:int`; `y:int`] THEN
    UNDISCH_TAC `A11 * x pow 2 + &2*A12*x*y + A22*y pow 2 = n` THEN
    SUBGOAL_THEN `A22 = &1 + A12 pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `A11 * A22 - A12 pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
     INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`A12:int`;`A11:int`] INT_BALANCED_REM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:int`) THEN ABBREV_TAC `r = --b:int` THEN
  ABBREV_TAC `A12' = A12 + A11 * r` THEN
  ABBREV_TAC `A22' = A11*r pow 2 + &2*A12*r + A22` THEN
  SUBGOAL_THEN `abs A12' * &2 <= A11` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A12'";"r"] THEN
    UNDISCH_TAC `abs (A12 - A11 * b) * &2 <= A11` THEN
    REWRITE_TAC[INT_ARITH `A12 + A11 * --b = A12 - A11 * b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `A11 * A22' - A12' pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A12'";"A22'"] THEN
    UNDISCH_TAC `A11 * A22 - A12 pow 2 = &1` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A22'` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < A11 * A22'` MP_TAC THENL
     [SUBGOAL_THEN `A11 * A22' = &1 + A12' pow 2` SUBST1_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `A12':int` INT_LE_POW_2) THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_LT_MUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `A22' < A11` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 * (A11 * A22') <= &4 + A11 pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `A11 * A22' = &1 + A12' pow 2`
       (fun th -> REWRITE_TAC[th]) THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(MATCH_MP SQ_BOUND (ASSUME `abs A12' * &2 <= A11`)) THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 <= A11` ASSUME_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 <= A11 * A11` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&2 * A11` THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_LE_RMUL THEN ASM_INT_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `A11 * (&4 * A22') < A11 * (&4 * A11)` MP_TAC THENL
     [MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC `&4 + A11 pow 2` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `&4 * (A11*A22') <= &4 + A11 pow 2` THEN INT_ARITH_TAC;
        REWRITE_TAC[INT_POW_2] THEN
        UNDISCH_TAC `&4 <= A11 * A11` THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_LT_LMUL_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A22':int`) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`A12':int`; `A11:int`]) THEN
  ANTS_TAC THENL [UNDISCH_TAC `A11 * A22' - A12' pow 2 = &1` THEN
  INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`y:int`; `x - r * y:int`] THEN
  MAP_EVERY EXPAND_TAC ["A12'";"A22'"] THEN
  UNDISCH_TAC `A11 * x pow 2 + &2*A12*x*y + A22*y pow 2 = n` THEN
  CONV_TAC INT_RING);;

(* ------------------------------------------------------------------------- *)
(* Ternary forms: completion of the square (Nathanson Lemma 1.3) and the     *)
(* discriminant-1 representation theorem. TERNARY_COMPLETE expresses a11*F = *)
(* (a11 x1 + a12 x2 + a13 x3)^2 + G(x2,x3) with G the "lower" binary form.   *)
(* TSQ_DISC1_A11_1 handles the reduced case a11 = 1 by completing the square *)
(* and applying the binary theorem BINARY_DISC1 to G.                        *)
(* ------------------------------------------------------------------------- *)

let TERNARY_COMPLETE = INT_RING
 `!a11 a12 a13 a22 a23 a33 x1 x2 x3:int.
    a11 * (a11 * x1 pow 2 + a22 * x2 pow 2 + a33 * x3 pow 2 +
           &2 * a12 * x1 * x2 + &2 * a13 * x1 * x3 + &2 * a23 * x2 * x3) =
    (a11 * x1 + a12 * x2 + a13 * x3) pow 2 +
    ((a11 * a22 - a12 pow 2) * x2 pow 2 +
     &2 * (a11 * a23 - a12 * a13) * x2 * x3 +
     (a11 * a33 - a13 pow 2) * x3 pow 2)`;;

let TSQ_DISC1_A11_1 = prove
 (`!a12 a13 a22 a23 a33 n:int.
     &0 < &1 * a22 - a12 pow 2 /\
     &1 * (a22 * a33 - a23 pow 2) - a12 * (a12 * a33 - a23 * a13) +
       a13 * (a12 * a23 - a22 * a13) = &1 /\
     (?x1 x2 x3. &1 * x1 pow 2 + a22 * x2 pow 2 + a33 * x3 pow 2 +
                 &2 * a12 * x1 * x2 + &2 * a13 * x1 * x3 +
                 &2 * a23 * x2 * x3 = n)
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G11 = a22 - a12 pow 2` THEN
  ABBREV_TAC `G12 = a23 - a12 * a13` THEN
  ABBREV_TAC `G22 = a33 - a13 pow 2` THEN
  SUBGOAL_THEN `G11 * G22 - G12 pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G11";"G12";"G22"] THEN
    UNDISCH_TAC
     `&1*(a22*a33 - a23 pow 2) - a12*(a12*a33 - a23*a13) +
      a13*(a12*a23 - a22*a13) = &1` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < G11` ASSUME_TAC THENL
   [EXPAND_TAC "G11" THEN UNDISCH_TAC `&0 < &1*a22 - a12 pow 2` THEN
   INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = x1 + a12*x2 + a13*x3` THEN
  MP_TAC(ISPECL [`G11:int`] BINARY_DISC1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`G12:int`; `G22:int`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `n - L pow 2`) THEN
  ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x2:int`; `x3:int`] THEN
    MP_TAC(SPECL [`&1:int`;`a12:int`;`a13:int`;`a22:int`;`a23:int`;`a33:int`;
                  `x1:int`;`x2:int`;`x3:int`] TERNARY_COMPLETE) THEN
    ASM_REWRITE_TAC[INT_MUL_LID] THEN
    MAP_EVERY EXPAND_TAC ["G11";"G12";"G22";"L"] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:int` (X_CHOOSE_TAC `v:int`)) THEN
  MAP_EVERY EXISTS_TAC [`L:int`; `u:int`; `v:int`] THEN
  UNDISCH_TAC `u pow 2 + v pow 2 = n - L pow 2` THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* SL3 extension (Nathanson Lemma 1.5): a primitive integer vector           *)
(* (u1,u2,u3) [i.e. exists x y z. u1 x + u2 y + u3 z = 1] occurs as the      *)
(* first column of a 3x3 integer matrix of determinant 1. We expose only the *)
(* cofactor identity needed downstream (the determinant expanded along the   *)
(* first column equals 1, with the first column = (u1,u2,u3)). Built from    *)
(* two Bezout steps; the explicit second/third columns are c2 = (-y', x',    *)
(* 0), c3 = (-u1' z, -u2' z, u1' x + u2' y) where a = gcd(u1,u2) = u1 x' +   *)
(* u2 y', u1 = a u1', u2 = a u2'.                                            *)
(* ------------------------------------------------------------------------- *)

let SL3_EXTEND = prove
 (`!u1 u2 u3:int. (?x y z. u1 * x + u2 * y + u3 * z = &1)
     ==> ?c12 c13 c22 c23 c32 c33.
            u1 * (c22 * c33 - c23 * c32) -
            c12 * (u2 * c33 - c23 * u3) +
            c13 * (u2 * c32 - c22 * u3) = &1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `u1 = &0 /\ u2 = &0` THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:int`;`&0:int`;`&0:int`;`&1:int`;`&0:int`;
      `&0:int`] THEN
    UNDISCH_TAC `u1*x+u2*y+u3*z = &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`u1:int`;`u2:int`] int_gcd) THEN
  ABBREV_TAC `a = gcd(u1,u2)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [REWRITE_TAC[INT_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(u1 = &0 /\ u2 = &0)` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[INT_GCD_EQ_0];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `u1':int` o REWRITE_RULE[int_divides] o
     check (fun th -> rand(concl th) = `u1:int`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `u2':int` o REWRITE_RULE[int_divides] o
     check (fun th -> rand(concl th) = `u2:int`)) THEN
  SUBGOAL_THEN `u1' * x' + u2' * y' = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `a * (u1'*x' + u2'*y') = a * &1` MP_TAC THENL
     [MP_TAC(ASSUME `a = u1 * x' + u2 * y'`) THEN
      MP_TAC(ASSUME `u1 = a * u1'`) THEN
      MP_TAC(ASSUME `u2 = a * u2'`) THEN CONV_TAC INT_RING;
      REWRITE_TAC[INT_EQ_MUL_LCANCEL] THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * (u1'*x + u2'*y) + u3 * z = &1` ASSUME_TAC THENL
   [MP_TAC(ASSUME `u1 * x + u2 * y + u3 * z = &1`) THEN
    MP_TAC(ASSUME `u1 = a * u1'`) THEN MP_TAC(ASSUME `u2 = a * u2'`) THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`--y':int`; `--(u1' * z):int`; `x':int`; `--(u2' * z):int`; `&0:int`;
    `u1'*x + u2'*y:int`] THEN
  MP_TAC(ASSUME `u1 = a * u1'`) THEN MP_TAC(ASSUME `u2 = a * u2'`) THEN
  MP_TAC(ASSUME `u1' * x' + u2' * y' = &1`) THEN
  MP_TAC(ASSUME `a * (u1' * x + u2' * y) + u3 * z = &1`) THEN
  CONV_TAC INT_RING);;

(* ------------------------------------------------------------------------- *)
(* Binary Hermite bound (the short-vector half of Nathanson Lemma 1.6 in the *)
(* binary case): a positive-definite binary form of discriminant D > 0       *)
(* represents, at some nonzero integer vector, a value m with 3 m^2 <= 4 D.  *)
(* Proved by the same reduce-and-swap descent as BINARY_DISC1, terminating   *)
(* once 3 A11^2 <= 4 D (the reduced regime), where the witness is (1,0).     *)
(* ------------------------------------------------------------------------- *)

let BINARY_HERMITE = prove
 (`!D. &0 < D ==>
     !A11. &0 < A11
       ==> !A12 A22. A11 * A22 - A12 pow 2 = D
           ==> ?x y. ~(x = &0 /\ y = &0) /\
                     &3 * (A11 * x pow 2 + &2 * A12 * x * y +
                           A22 * y pow 2) pow 2
                       <= &4 * D`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC `abs:int->int` THEN
  REWRITE_TAC[INT_ABS_POS] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`A12:int`;`A11:int`] INT_BALANCED_REM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:int`) THEN ABBREV_TAC `r = --b:int` THEN
  ABBREV_TAC `A12' = A12 + A11 * r` THEN
  ABBREV_TAC `A22' = A11*r pow 2 + &2*A12*r + A22` THEN
  SUBGOAL_THEN `abs A12' * &2 <= A11` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A12'";"r"] THEN
    UNDISCH_TAC `abs (A12 - A11 * b) * &2 <= A11` THEN
    REWRITE_TAC[INT_ARITH `A12 + A11 * --b = A12 - A11 * b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `A11 * A22' - A12' pow 2 = D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A12'";"A22'"] THEN
    UNDISCH_TAC `A11 * A22 - A12 pow 2 = D` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A22'` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < A11 * A22'` MP_TAC THENL
     [SUBGOAL_THEN `A11 * A22' = D + A12' pow 2` SUBST1_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `A12':int` INT_LE_POW_2) THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_LT_MUL_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `&3 * A11 pow 2 <= &4 * D` THENL
   [MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`] THEN CONJ_TAC THENL
     [INT_ARITH_TAC;
      SUBGOAL_THEN
       `A11 * (&1:int) pow 2 + &2*A12*(&1)*(&0) + A22*(&0) pow 2 = A11`
       SUBST1_TAC THENL [CONV_TAC INT_RING; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A22' < A11` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 * (A11 * A22') <= &4 * D + A11 pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `A11 * A22' = D + A12' pow 2`
       (fun th -> REWRITE_TAC[th]) THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(MATCH_MP SQ_BOUND (ASSUME `abs A12' * &2 <= A11`)) THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * D < &3 * A11 pow 2` ASSUME_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `A11 * (&4 * A22') < A11 * (&4 * A11)` MP_TAC THENL
     [MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC `&4 * D + A11 pow 2` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `&4 * (A11*A22') <= &4 * D + A11 pow 2` THEN INT_ARITH_TAC;
        REWRITE_TAC[INT_POW_2] THEN
        UNDISCH_TAC `&4 * D < &3 * A11 pow 2` THEN REWRITE_TAC[INT_POW_2] THEN
        INT_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_LT_LMUL_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A22':int`) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`A12':int`; `A11:int`]) THEN
  ANTS_TAC THENL [UNDISCH_TAC `A11 * A22' - A12' pow 2 = D` THEN
  INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':int`
    (X_CHOOSE_THEN `y':int` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `y' + r * x':int` THEN EXISTS_TAC `x':int` THEN CONJ_TAC THENL
   [ASM_CASES_TAC `x' = &0` THENL
     [UNDISCH_TAC `~(x' = &0 /\ y' = &0)` THEN
     ASM_REWRITE_TAC[INT_MUL_RZERO; INT_ADD_RID] THEN
      MESON_TAC[];
      ASM_MESON_TAC[]];
    SUBGOAL_THEN
     `A11*(y'+r*x') pow 2 + &2*A12*(y'+r*x')*x' + A22*x' pow 2 =
      A22' * x' pow 2 + &2 * A12' * x' * y' + A11 * y' pow 2`
     ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A22'";"A12'"] THEN
     CONV_TAC INT_RING; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The minimal represented value of a positive-definite ternary form, and    *)
(* its primitivity (Nathanson, start of Lemma 1.6). TERNARY_MIN: the form    *)
(* attains a least value over nonzero integer vectors (well-ordering of the  *)
(* nonnegative integers, INT_WOP). MIN_PRIMITIVE: that minimizing vector is  *)
(* primitive -- if a common divisor g divided all coordinates then F scales  *)
(* by g^2, giving a strictly smaller value, so g is a unit. A determinant-1  *)
(* integer matrix is injective, which transfers nonzeroness through          *)
(* conjugation.                                                              *)
(* ------------------------------------------------------------------------- *)

let INT_GCD3_EXISTS = prove
 (`!a b c:int. ?d. d divides a /\ d divides b /\ d divides c /\
                   (?x y z. d = a * x + b * y + c * z)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:int`;`b:int`] INT_GCD_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`e:int`;`c:int`] INT_GCD_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:int` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INT_DIVIDES_TRANS];
    ASM_MESON_TAC[INT_DIVIDES_TRANS];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `e = a * x + b * y` THEN
  UNDISCH_TAC `d = e * x' + c * y'` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x * x':int`; `y * x':int`; `y':int`] THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let TERNARY_MIN = prove
 (`!a11 a12 a13 a22 a23 a33:int.
     (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> &0 < a11 * x pow 2 + a22 * y pow 2 + a33 * z pow 2 +
                       &2 * a12 * x * y + &2 * a13 * x * z + &2 * a23 * y * z)
     ==> ?v1 v2 v3.
            ~(v1 = &0 /\ v2 = &0 /\ v3 = &0) /\
            (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
                     ==> a11 * v1 pow 2 + a22 * v2 pow 2 + a33 * v3 pow 2 +
                         &2 * a12 * v1 * v2 + &2 * a13 * v1 * v3 +
                         &2 * a23 * v2 * v3
                         <= a11 * x pow 2 + a22 * y pow 2 + a33 * z pow 2 +
                            &2 * a12 * x * y + &2 * a13 * x * z +
                            &2 * a23 * y * z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\v:int. ?x y z. ~(x = &0 /\ y = &0 /\ z = &0) /\
                v = a11*x pow 2 + a22*y pow 2 + a33*z pow 2 +
                    &2*a12*x*y + &2*a13*x*z + &2*a23*y*z`
   (GEN `P:int->bool` INT_WOP)) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?v. &0 <= v /\
        (?x y z. ~(x = &0 /\ y = &0 /\ z = &0) /\
                 v = a11*x pow 2 + a22*y pow 2 + a33*z pow 2 +
                     &2*a12*x*y + &2*a13*x*z + &2*a23*y*z)`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXISTS_TAC `a11*(&1) pow 2 + a22*(&0) pow 2 + a33*(&0) pow 2 +
               &2*a12*(&1)*(&0) + &2*a13*(&1)*(&0) + &2*a23*(&0)*(&0)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`&1:int`;`&0:int`;`&0:int`]) THEN
      ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`&1:int`;`&0:int`;`&0:int`] THEN
      REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mn:int` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x':int`;`y:int`;`z:int`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:int`;`q:int`;`s:int`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `a11*p pow 2 + a22*q pow 2 + a33*s pow 2 +
    &2*a12*p*q + &2*a13*p*s + &2*a23*q*s`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INT_LT_IMP_LE THEN ASM_SIMP_TAC[];
      MAP_EVERY EXISTS_TAC [`p:int`;`q:int`;`s:int`] THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `mn = a11*x' pow 2 + a22*y pow 2 + a33*z pow 2 +
                      &2*a12*x'*y + &2*a13*x'*z + &2*a23*y*z` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th])]);;

let MIN_PRIMITIVE = prove
 (`!a11 a12 a13 a22 a23 a33 v1 v2 v3:int.
     (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> &0 < a11 * x pow 2 + a22 * y pow 2 + a33 * z pow 2 +
                       &2 * a12 * x * y + &2 * a13 * x * z +
                       &2 * a23 * y * z) /\
     ~(v1 = &0 /\ v2 = &0 /\ v3 = &0) /\
     (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> a11 * v1 pow 2 + a22 * v2 pow 2 + a33 * v3 pow 2 +
                  &2 * a12 * v1 * v2 + &2 * a13 * v1 * v3 +
                  &2 * a23 * v2 * v3
                  <= a11 * x pow 2 + a22 * y pow 2 + a33 * z pow 2 +
                     &2 * a12 * x * y + &2 * a13 * x * z + &2 * a23 * y * z)
     ==> ?x y z. v1 * x + v2 * y + v3 * z = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(SPECL [`v1:int`;`v2:int`;`v3:int`] INT_GCD3_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w1:int` o REWRITE_RULE[int_divides] o
     check (fun th -> rand(concl th) = `v1:int`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w2:int` o REWRITE_RULE[int_divides] o
     check (fun th -> rand(concl th) = `v2:int`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w3:int` o REWRITE_RULE[int_divides] o
     check (fun th -> rand(concl th) = `v3:int`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o
     check (fun th -> is_eq(concl th) &&
            (let l = lhand(concl th) in l = `v1:int` || l = `v2:int`
              || l = `v3:int`)))) THEN
  SUBGOAL_THEN `~(g = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
   UNDISCH_TAC `~(g * w1 = &0 /\ g * w2 = &0 /\ g * w3 = &0)` THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `w1 * x + w2 * y + w3 * z = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `g * (w1*x+w2*y+w3*z) = g * &1` MP_TAC THENL
     [REWRITE_TAC[INT_MUL_RID] THEN
      MP_TAC(ASSUME `g = (g*w1)*x + (g*w2)*y + (g*w3)*z`) THEN
      CONV_TAC INT_RING;
      ASM_SIMP_TAC[INT_EQ_MUL_LCANCEL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w1 = &0 /\ w2 = &0 /\ w3 = &0)` ASSUME_TAC THENL
   [STRIP_TAC THEN UNDISCH_TAC `w1 * x + w2 * y + w3 * z = &1` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `g pow 2 = &1` ASSUME_TAC THENL
   [ABBREV_TAC `Fw = a11*w1 pow 2 + a22*w2 pow 2 + a33*w3 pow 2 +
                     &2*a12*w1*w2 + &2*a13*w1*w3 + &2*a23*w2*w3` THEN
    SUBGOAL_THEN `&0 < Fw` ASSUME_TAC THENL
     [EXPAND_TAC "Fw" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> a11*(g*w1) pow 2 + a22*(g*w2) pow 2 +
                  a33*(g*w3) pow 2 + &2*a12*(g*w1)*(g*w2) +
                  &2*a13*(g*w1)*(g*w3) + &2*a23*(g*w2)*(g*w3)
                  <= a11*x pow 2 + a22*y pow 2 + a33*z pow 2 +
                     &2*a12*x*y + &2*a13*x*z + &2*a23*y*z` THEN
    DISCH_THEN(MP_TAC o SPECL [`w1:int`;`w2:int`;`w3:int`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `a11*(g*w1) pow 2 + a22*(g*w2) pow 2 + a33*(g*w3) pow 2 +
      &2*a12*(g*w1)*(g*w2) + &2*a13*(g*w1)*(g*w3) +
      &2*a23*(g*w2)*(g*w3) = g pow 2 * Fw`
     SUBST1_TAC THENL
     [EXPAND_TAC "Fw" THEN CONV_TAC INT_RING; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV
      o RAND_CONV) [GSYM(INT_ARITH `&1 * Fw = Fw`)] THEN
    ASM_SIMP_TAC[INT_LE_RMUL_EQ] THEN
    SUBGOAL_THEN `&1 <= g pow 2` MP_TAC THENL
     [REWRITE_TAC[INT_ARITH `&1 <= x <=> &0 < x`] THEN
      ASM_SIMP_TAC[INT_LT_POW_2]; ALL_TAC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`g*x:int`;`g*y:int`;`g*z:int`] THEN
  MP_TAC(ASSUME `g = (g*w1)*x + (g*w2)*y + (g*w3)*z`) THEN
  MP_TAC(ASSUME `g pow 2 = &1`) THEN REWRITE_TAC[INT_POW_2] THEN
  CONV_TAC INT_RING);;

(* ------------------------------------------------------------------------- *)
(* Hermite reduction arithmetic (Nathanson Lemma 1.6, ternary case). With    *)
(* a11 the minimal value of a positive-definite form of discriminant 1, the  *)
(* completed binary form G has discriminant a11 (DISC_G with det = 1), so    *)
(* BINARY_HERMITE gives a nonzero vector with 3 G^2 <= 4 a11; minimality and *)
(* a balanced first coordinate give 3 a11^2 <= 4 G (HERMITE_LOWER); together *)
(* these force 27 a11^3 <= 64 (HERMITE_CUBE), hence a11 = 1 (CUBE_GE_8).     *)
(* ------------------------------------------------------------------------- *)

let DISC_G = INT_RING
 `!a11 a12 a13 a22 a23 a33:int.
    (a11 * a22 - a12 pow 2) * (a11 * a33 - a13 pow 2) -
    (a11 * a23 - a12 * a13) pow 2 =
    a11 * (a11 * (a22 * a33 - a23 pow 2) -
           a12 * (a12 * a33 - a23 * a13) +
           a13 * (a12 * a23 - a22 * a13))`;;

let CUBE_GE_8 = prove
 (`!a:int. &2 <= a ==> &8 <= a pow 3`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&2 pow 3` THEN
  CONJ_TAC THENL [INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE2 THEN
  ASM_INT_ARITH_TAC]);;

let HERMITE_LOWER = prove
 (`!a11 a12 a13 a22 a23 a33 x1 s t Gst:int.
     &0 < a11 /\
     a11 <= a11 * x1 pow 2 + a22 * s pow 2 + a33 * t pow 2 +
             &2 * a12 * x1 * s + &2 * a13 * x1 * t + &2 * a23 * s * t /\
     &4 * (a11 * x1 + a12 * s + a13 * t) pow 2 <= a11 pow 2 /\
     a11 * (a11 * x1 pow 2 + a22 * s pow 2 + a33 * t pow 2 +
            &2 * a12 * x1 * s + &2 * a13 * x1 * t + &2 * a23 * s * t) =
       (a11 * x1 + a12 * s + a13 * t) pow 2 + Gst
     ==> &3 * a11 pow 2 <= &4 * Gst`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a11 * a11 <= a11 * (a11*x1 pow 2 + a22*s pow 2 + a33*t pow 2 +
            &2*a12*x1*s + &2*a13*x1*t + &2*a23*s*t)` MP_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN ASM_SIMP_TAC[INT_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `&4 * (a11*x1 + a12*s + a13*t) pow 2 <= a11 pow 2`) THEN
  REWRITE_TAC[INT_POW_2] THEN INT_ARITH_TAC);;

let HERMITE_CUBE = prove
 (`!a G:int.
     &0 < a /\ &0 < G /\
     &3 * a pow 2 <= &4 * G /\ &3 * G pow 2 <= &4 * a
     ==> &27 * a pow 3 <= &64`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&3 * a pow 2) pow 2 <= (&4 * G) pow 2` MP_TAC THENL
   [MATCH_MP_TAC INT_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_LE_POW_2] THEN
     INT_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[INT_POW_MUL] THEN DISCH_TAC THEN
  MATCH_MP_TAC INT_LE_RCANCEL_IMP THEN EXISTS_TAC `a:int` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&16 * (&3 * G pow 2)` THEN
  CONJ_TAC THENL
   [MP_TAC(ASSUME `&3 pow 2 * a pow 2 pow 2 <= &4 pow 2 * G pow 2`) THEN
    REWRITE_TAC[INT_ARITH `a pow 2 pow 2 = a pow 3 * a`; INT_POW_2] THEN
    INT_ARITH_TAC;
    MP_TAC(ASSUME `&3 * G pow 2 <= &4 * a`) THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Positive-definiteness of a ternary form from its principal minors         *)
(* (Nathanson Lemma 1.3, the "if" direction), and surjectivity over Z of a   *)
(* determinant-1 integer matrix (ADJ_PREIMAGE: every target has an integer   *)
(* preimage, via the adjugate -- used to transfer "represents n" through a   *)
(* change of variables).                                                     *)
(* ------------------------------------------------------------------------- *)

let TERNARY_POSDEF = prove
 (`!a11 a12 a13 a22 a23 a33:int.
     &0 < a11 /\ &0 < a11 * a22 - a12 pow 2 /\
     &0 < a11 * (a22 * a33 - a23 pow 2) -
          a12 * (a12 * a33 - a23 * a13) +
          a13 * (a12 * a23 - a22 * a13)
     ==> !x y z. ~(x = &0 /\ y = &0 /\ z = &0)
                 ==> &0 < a11 * x pow 2 + a22 * y pow 2 + a33 * z pow 2 +
                          &2 * a12 * x * y + &2 * a13 * x * z +
                          &2 * a23 * y * z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `G11 = a11*a22 - a12 pow 2` THEN
  ABBREV_TAC `G12 = a11*a23 - a12*a13` THEN
  ABBREV_TAC `G22 = a11*a33 - a13 pow 2` THEN
  SUBGOAL_THEN `&0 < G11 * G22 - G12 pow 2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G11";"G12";"G22"] THEN
    SUBGOAL_THEN
     `(a11*a22 - a12 pow 2)*(a11*a33 - a13 pow 2) - (a11*a23 - a12*a13) pow 2 =
      a11 * (a11*(a22*a33 - a23 pow 2) - a12*(a12*a33 - a23*a13) +
             a13*(a12*a23 - a22*a13))`
     SUBST1_TAC THENL [REWRITE_TAC[DISC_G]; ALL_TAC] THEN
    MATCH_MP_TAC INT_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < a11 *
     (a11*x pow 2 + a22*y pow 2 + a33*z pow 2 +
      &2*a12*x*y + &2*a13*x*z + &2*a23*y*z)` MP_TAC THENL
   [SUBGOAL_THEN
   `a11 * (a11*x pow 2 + a22*y pow 2 + a33*z pow 2 +
           &2*a12*x*y + &2*a13*x*z + &2*a23*y*z) =
    (a11*x + a12*y + a13*z) pow 2 + (G11*y pow 2 + &2*G12*y*z + G22*z pow 2)`
   SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G11";"G12";"G22"] THEN
    MP_TAC(SPECL [`a11:int`;`a12:int`;`a13:int`;`a22:int`;`a23:int`;`a33:int`;
                  `x:int`;`y:int`;`z:int`] TERNARY_COMPLETE) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `y = &0 /\ z = &0` THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(x = &0 /\ y = &0 /\ z = &0)` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[INT_MUL_RZERO; INT_ADD_RID; INT_MUL_LZERO;
                    INT_POW_ZERO; ARITH_EQ] THEN
    REWRITE_TAC[INT_ADD_RID] THEN
    REWRITE_TAC[INT_LT_POW_2] THEN
    REWRITE_TAC[INT_ENTIRE; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC(INT_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    REWRITE_TAC[INT_LE_POW_2] THEN
    MP_TAC(SPECL [`G11:int`;`G12:int`;`G22:int`] POSDEF_BINARY_CRITERION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    ALL_TAC;
    ASM_SIMP_TAC[INT_LT_MUL_EQ]]);;

let ADJ_PREIMAGE = prove
 (`!u1 u2 u3 c12 c22 c32 c13 c23 c33 X1 X2 X3:int.
     u1 * (c22 * c33 - c23 * c32) -
     c12 * (u2 * c33 - c23 * u3) +
     c13 * (u2 * c32 - c22 * u3) = &1
     ==> ?y1 y2 y3.
            u1 * y1 + c12 * y2 + c13 * y3 = X1 /\
            u2 * y1 + c22 * y2 + c23 * y3 = X2 /\
            u3 * y1 + c32 * y2 + c33 * y3 = X3`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(c22*c33 - c23*c32)*X1 + (c13*c32 - c12*c33)*X2 + (c12*c23 - c13*c22)*X3`;
    `(c23*u3 - u2*c33)*X1 + (u1*c33 - c13*u3)*X2 + (c13*u2 - u1*c23)*X3`;
    `(u2*c32 - u3*c22)*X1 + (u3*c12 - u1*c32)*X2 + (u1*c22 - u2*c12)*X3`] THEN
  MP_TAC(ASSUME
   `u1*(c22*c33 - c23*c32) - c12*(u2*c33 - c23*u3) +
    c13*(u2*c32 - c22*u3) = &1`) THEN
  CONV_TAC INT_RING);;

(* ------------------------------------------------------------------------- *)
(* The Hermite reduction packaged: a positive-definite ternary form of       *)
(* discriminant 1 whose leading coefficient b11 is the MINIMAL value it      *)
(* represents must have b11 = 1 (Nathanson Lemma 1.6 + Theorem 1.3, the a11  *)
(* = 1 conclusion). Completing the square gives a binary form G of           *)
(* discriminant b11; the short vector from BINARY_HERMITE plus minimality    *)
(* (with a balanced first coordinate, HERMITE_LOWER) bound 27 b11^3 <= 64,   *)
(* so b11 = 1.                                                               *)
(* ------------------------------------------------------------------------- *)

let HERMITE_A1 = prove
  (`!b11 b12 b13 b22 b23 b33:int.
     &0 < b11 /\
     b11 * (b22 * b33 - b23 pow 2) - b12 * (b12 * b33 - b13 * b23) +
       b13 * (b12 * b23 - b13 * b22) = &1 /\
     &0 < b11 * b22 - b12 pow 2 /\
     (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> b11 <= b11 * x pow 2 + b22 * y pow 2 + b33 * z pow 2 +
                         &2 * b12 * x * y + &2 * b13 * x * z +
                         &2 * b23 * y * z)
     ==> b11 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G11 = b11*b22 - b12 pow 2` THEN
  ABBREV_TAC `G12 = b11*b23 - b12*b13` THEN
  ABBREV_TAC `G22 = b11*b33 - b13 pow 2` THEN
  SUBGOAL_THEN `G11 * G22 - G12 pow 2 = b11` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G11";"G12";"G22"] THEN
    REWRITE_TAC[DISC_G] THEN
    MP_TAC(ASSUME `b11*(b22*b33 - b23 pow 2) - b12*(b12*b33 - b13*b23) +
                   b13*(b12*b23 - b13*b22) = &1`) THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(SPEC `b11:int` BINARY_HERMITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `G11:int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`G12:int`;`G22:int`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:int`
    (X_CHOOSE_THEN `t:int` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `Gst = G11 * s pow 2 + &2 * G12 * s * t + G22 * t pow 2` THEN
  MP_TAC(SPECL [`b12*s + b13*t`;`b11:int`] INT_BALANCED_REM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `bb:int`) THEN
  ABBREV_TAC `x1 = --bb:int` THEN
  SUBGOAL_THEN
   `&4 * (b11*x1 + b12*s + b13*t) pow 2 <= b11 pow 2`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP SQ_BOUND
     (ASSUME `abs ((b12*s + b13*t) - b11 * bb) * &2 <= b11`)) THEN
    EXPAND_TAC "x1" THEN
    REWRITE_TAC
     [INT_ARITH
       `b11 * --bb + b12*s + b13*t = (b12*s + b13*t) - b11*bb`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * b11 pow 2 <= &4 * Gst` ASSUME_TAC THENL
   [MATCH_MP_TAC HERMITE_LOWER THEN
    MAP_EVERY EXISTS_TAC [`b12:int`;`b13:int`;`b22:int`;`b23:int`;
      `b33:int`] THEN
    MAP_EVERY EXISTS_TAC [`x1:int`;`s:int`;`t:int`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`x1:int`;`s:int`;`t:int`] th) THEN
         ANTS_TAC THENL [UNDISCH_TAC `~(s = &0 /\ t = &0)` THEN
         MESON_TAC[]; ALL_TAC] THEN
         DISCH_THEN(fun th2 -> ACCEPT_TAC th2 ORELSE MP_TAC th2));
      EXPAND_TAC "Gst" THEN
      MP_TAC(SPECL [`b11:int`;`b12:int`;`b13:int`;`b22:int`;`b23:int`;
        `b33:int`;
                    `x1:int`;`s:int`;`t:int`] TERNARY_COMPLETE) THEN
      MAP_EVERY (fun e -> UNDISCH_TAC e)
        [`b11 * b22 - b12 pow 2 = G11`; `b11 * b23 - b12 * b13 = G12`;
         `b11 * b33 - b13 pow 2 = G22`] THEN
      CONV_TAC INT_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Gst` ASSUME_TAC THENL
   [EXPAND_TAC "Gst" THEN
    MP_TAC(SPECL [`G11:int`;`G12:int`;`G22:int`] POSDEF_BINARY_CRITERION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:int`;`t:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`b11:int`;`Gst:int`] HERMITE_CUBE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&2 <= b11)` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(SPEC `b11:int` CUBE_GE_8) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&27 * b11 pow 3 <= &64` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Minimality transfers through the conjugation: if A's minimal value is     *)
(* attained at the primitive vector v, and the matrix U (columns v, c2, c3)  *)
(* has determinant 1, then the conjugated form B, with entries the b_ij      *)
(* below and satisfying B(p) = A(U p), attains the same minimal value.       *)
(* Injectivity of U ensures that a nonzero p maps to a nonzero point where   *)
(* A's minimality applies.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONJ_MIN = prove
 (`!a11 a12 a13 a22 a23 a33 v1 v2 v3 c12 c13 c22 c23 c32 c33
     b11 b12 b13 b22 b23 b33:int.
     (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> a11 * v1 pow 2 + a22 * v2 pow 2 + a33 * v3 pow 2 +
                  &2 * a12 * v1 * v2 + &2 * a13 * v1 * v3 +
                  &2 * a23 * v2 * v3
                  <= a11 * x pow 2 + a22 * y pow 2 + a33 * z pow 2 +
                     &2 * a12 * x * y + &2 * a13 * x * z + &2 * a23 * y * z) /\
     v1 * (c22 * c33 - c23 * c32) -
     c12 * (v2 * c33 - c23 * v3) +
     c13 * (v2 * c32 - c22 * v3) = &1 /\
     b11 = a11 * v1 pow 2 + &2 * a12 * v1 * v2 + &2 * a13 * v1 * v3 +
            a22 * v2 pow 2 + &2 * a23 * v2 * v3 + a33 * v3 pow 2 /\
     b22 = a11 * c12 pow 2 + &2 * a12 * c12 * c22 + &2 * a13 * c12 * c32 +
            a22 * c22 pow 2 + &2 * a23 * c22 * c32 + a33 * c32 pow 2 /\
     b33 = a11 * c13 pow 2 + &2 * a12 * c13 * c23 + &2 * a13 * c13 * c33 +
            a22 * c23 pow 2 + &2 * a23 * c23 * c33 + a33 * c33 pow 2 /\
     b12 = a11 * v1 * c12 + a12 * (v1 * c22 + v2 * c12) +
            a13 * (v1 * c32 + v3 * c12) +
            a22 * v2 * c22 + a23 * (v2 * c32 + v3 * c22) + a33 * v3 * c32 /\
     b13 = a11 * v1 * c13 + a12 * (v1 * c23 + v2 * c13) +
            a13 * (v1 * c33 + v3 * c13) +
            a22 * v2 * c23 + a23 * (v2 * c33 + v3 * c23) + a33 * v3 * c33 /\
     b23 = a11 * c12 * c13 + a12 * (c12 * c23 + c22 * c13) +
            a13 * (c12 * c33 + c32 * c13) +
            a22 * c22 * c23 + a23 * (c22 * c33 + c32 * c23) + a33 * c32 * c33
     ==> !x y z. ~(x = &0 /\ y = &0 /\ z = &0)
                 ==> b11 <= b11 * x pow 2 + b22 * y pow 2 + b33 * z pow 2 +
                            &2 * b12 * x * y + &2 * b13 * x * z +
                            &2 * b23 * y * z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`x*v1 + y*c12 + z*c13`; `x*v2 + y*c22 + z*c23`;
    `x*v3 + y*c32 + z*c33`]) THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(x = &0 /\ y = &0 /\ z = &0)` THEN
    REWRITE_TAC[] THEN
    POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `lhs1 = lhs2 /\ rhs1 = rhs2 ==> lhs2 <= rhs2
    ==> lhs1 <= rhs1`) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING;
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING]);;

(* A positive-definite ternary form has positive leading 2x2 minor b11 b22 - *)
(* b12^2 (evaluate the form at (-b12, b11, 0) and divide by b11).            *)

let POSDEF_MINOR2 = prove
 (`!b11 b12 b13 b22 b23 b33:int.
     &0 < b11 /\
     (!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
              ==> &0 < b11 * x pow 2 + b22 * y pow 2 + b33 * z pow 2 +
                       &2 * b12 * x * y + &2 * b13 * x * z + &2 * b23 * y * z)
     ==> &0 < b11 * b22 - b12 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b11 * (b11*b22 - b12 pow 2)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`--b12:int`;`b11:int`;`&0:int`]) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `~(b11 = &0)` MP_TAC THENL
       [ASM_INT_ARITH_TAC; MESON_TAC[]];
      MATCH_MP_TAC(INT_ARITH `a = b ==> &0 < a ==> &0 < b`) THEN
      CONV_TAC INT_RING] THEN
    ALL_TAC;
    ASM_SIMP_TAC[INT_LT_MUL_EQ]]);;

(* Representation transfers through the conjugation: the conjugated form B   *)
(* represents every integer A represents. Given U has determinant 1, the     *)
(* adjugate (ADJ_PREIMAGE) supplies an integer preimage y of the             *)
(* representing vector X; expanding the b_ij definitions gives              *)
(* B(y) = A(U y) = A(X).                                                     *)

let CONJ_REPS = prove
 (`!a11 a12 a13 a22 a23 a33 v1 v2 v3 c12 c13 c22 c23 c32 c33
     b11 b12 b13 b22 b23 b33 n:int.
     v1 * (c22 * c33 - c23 * c32) -
     c12 * (v2 * c33 - c23 * v3) +
     c13 * (v2 * c32 - c22 * v3) = &1 /\
     b11 = a11 * v1 pow 2 + &2 * a12 * v1 * v2 + &2 * a13 * v1 * v3 +
            a22 * v2 pow 2 + &2 * a23 * v2 * v3 + a33 * v3 pow 2 /\
     b22 = a11 * c12 pow 2 + &2 * a12 * c12 * c22 + &2 * a13 * c12 * c32 +
            a22 * c22 pow 2 + &2 * a23 * c22 * c32 + a33 * c32 pow 2 /\
     b33 = a11 * c13 pow 2 + &2 * a12 * c13 * c23 + &2 * a13 * c13 * c33 +
            a22 * c23 pow 2 + &2 * a23 * c23 * c33 + a33 * c33 pow 2 /\
     b12 = a11 * v1 * c12 + a12 * (v1 * c22 + v2 * c12) +
            a13 * (v1 * c32 + v3 * c12) +
            a22 * v2 * c22 + a23 * (v2 * c32 + v3 * c22) + a33 * v3 * c32 /\
     b13 = a11 * v1 * c13 + a12 * (v1 * c23 + v2 * c13) +
            a13 * (v1 * c33 + v3 * c13) +
            a22 * v2 * c23 + a23 * (v2 * c33 + v3 * c23) + a33 * v3 * c33 /\
     b23 = a11 * c12 * c13 + a12 * (c12 * c23 + c22 * c13) +
            a13 * (c12 * c33 + c32 * c13) +
            a22 * c22 * c23 + a23 * (c22 * c33 + c32 * c23) +
            a33 * c32 * c33 /\
     (?x1 x2 x3. a11 * x1 pow 2 + a22 * x2 pow 2 + a33 * x3 pow 2 +
                 &2 * a12 * x1 * x2 + &2 * a13 * x1 * x3 +
                 &2 * a23 * x2 * x3 = n)
     ==> ?y1 y2 y3. b11 * y1 pow 2 + b22 * y2 pow 2 + b33 * y3 pow 2 +
                    &2 * b12 * y1 * y2 + &2 * b13 * y1 * y3 +
                    &2 * b23 * y2 * y3 = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`v1:int`;`v2:int`;`v3:int`;`c12:int`;`c22:int`;`c32:int`;
                `c13:int`;`c23:int`;`c33:int`;`x1:int`;`x2:int`;
                  `x3:int`] ADJ_PREIMAGE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:int` (X_CHOOSE_THEN `y2:int`
    (X_CHOOSE_THEN `y3:int` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`y1:int`;`y2:int`;`y3:int`] THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN CONV_TAC INT_RING);;

(* ========================================================================= *)
(* THE TERNARY DISCRIMINANT-1 REPRESENTATION THEOREM (Nathanson Theorem      *)
(* 1.3): every positive-definite ternary quadratic form of discriminant 1    *)
(* represents only sums of three integer squares. This is the crux of the    *)
(* elementary three-squares proof. Assembly:                                 *)
(*   - TERNARY_POSDEF: the form is positive-definite (from the principal     *)
(*     minors a11 > 0, d' > 0, det = 1 > 0);                                 *)
(*   - TERNARY_MIN + MIN_PRIMITIVE: it attains a least value at a PRIMITIVE  *)
(*     vector v;                                                             *)
(*   - SL3_EXTEND: v is the first column of a determinant-1 matrix U;        *)
(*   - the conjugated form B = U^T A U has b11 equal to the minimal value,   *)
(*     discriminant 1, is positive-definite, and represents the same n;      *)
(*   - HERMITE_A1 forces b11 = 1, so by TSQ_DISC1_A11_1 (the a11 = 1 case,   *)
(*     which completes the square and invokes the binary theorem) n is a sum *)
(*     of three squares.                                                     *)
(* ========================================================================= *)

let TSQ_DISC1 = prove
 (`!a11 a12 a13 a22 a23 a33 n:int.
     &0 < a11 /\
     &0 < a11 * a22 - a12 pow 2 /\
     a11 * (a22 * a33 - a23 pow 2) - a12 * (a12 * a33 - a23 * a13) +
       a13 * (a12 * a23 - a22 * a13) = &1 /\
     (?x1 x2 x3. a11 * x1 pow 2 + a22 * x2 pow 2 + a33 * x3 pow 2 +
                 &2 * a12 * x1 * x2 + &2 * a13 * x1 * x3 +
                 &2 * a23 * x2 * x3 = n)
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
            ==> &0 < a11*x pow 2 + a22*y pow 2 + a33*z pow 2 +
                     &2*a12*x*y + &2*a13*x*z + &2*a23*y*z`
   ASSUME_TAC THENL
   [MATCH_MP_TAC TERNARY_POSDEF THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `a11*(a22*a33 - a23 pow 2) - a12*(a12*a33 - a23*a13) +
       a13*(a12*a23 - a22*a13) = &1` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a11:int`;`a12:int`;`a13:int`;`a22:int`;`a23:int`;
    `a33:int`] TERNARY_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:int` (X_CHOOSE_THEN `v2:int`
    (X_CHOOSE_THEN `v3:int` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?p q s. v1*p + v2*q + v3*s = &1` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MIN_PRIMITIVE THEN
    MAP_EVERY EXISTS_TAC [`a11:int`;`a12:int`;`a13:int`;`a22:int`;`a23:int`;
      `a33:int`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`v1:int`;`v2:int`;`v3:int`] SL3_EXTEND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c12:int` (X_CHOOSE_THEN `c13:int`
    (X_CHOOSE_THEN `c22:int` (X_CHOOSE_THEN `c23:int`
     (X_CHOOSE_THEN `c32:int` (X_CHOOSE_THEN `c33:int` ASSUME_TAC)))))) THEN
  ABBREV_TAC `b11 = a11*v1 pow 2 + &2*a12*v1*v2 + &2*a13*v1*v3 +
                a22*v2 pow 2 + &2*a23*v2*v3 + a33*v3 pow 2` THEN
  ABBREV_TAC `b22 = a11*c12 pow 2 + &2*a12*c12*c22 + &2*a13*c12*c32 +
                a22*c22 pow 2 + &2*a23*c22*c32 + a33*c32 pow 2` THEN
  ABBREV_TAC `b33 = a11*c13 pow 2 + &2*a12*c13*c23 + &2*a13*c13*c33 +
                a22*c23 pow 2 + &2*a23*c23*c33 + a33*c33 pow 2` THEN
  ABBREV_TAC `b12 = a11*v1*c12 + a12*(v1*c22+v2*c12) + a13*(v1*c32+v3*c12) +
                a22*v2*c22 + a23*(v2*c32+v3*c22) + a33*v3*c32` THEN
  ABBREV_TAC `b13 = a11*v1*c13 + a12*(v1*c23+v2*c13) + a13*(v1*c33+v3*c13) +
                a22*v2*c23 + a23*(v2*c33+v3*c23) + a33*v3*c33` THEN
  ABBREV_TAC
   `b23 = a11*c12*c13 + a12*(c12*c23+c22*c13) +
          a13*(c12*c33+c32*c13) + a22*c22*c23 +
          a23*(c22*c33+c32*c23) + a33*c32*c33` THEN
  SUBGOAL_THEN
   `!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
            ==> b11 <= b11*x pow 2 + b22*y pow 2 + b33*z pow 2 +
                       &2*b12*x*y + &2*b13*x*z + &2*b23*y*z`
   ASSUME_TAC THENL
   [MATCH_MP_TAC CONJ_MIN THEN
    MAP_EVERY EXISTS_TAC
     [`a11:int`;`a12:int`;`a13:int`;`a22:int`;`a23:int`;`a33:int`;
      `v1:int`;`v2:int`;`v3:int`;`c12:int`;`c13:int`;`c22:int`;`c23:int`;
        `c32:int`;`c33:int`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b11` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`v1:int`;`v2:int`;`v3:int`] th) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun t -> if rand(rator(concl t)) = `&0` then MP_TAC t
        else NO_TAC)) THEN
    MP_TAC(ASSUME
     `a11 * v1 pow 2 + &2 * a12 * v1 * v2 + &2 * a13 * v1 * v3 +
      a22 * v2 pow 2 + &2 * a23 * v2 * v3 + a33 * v3 pow 2 = b11`) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `b11*(b22*b33 - b23 pow 2) - b12*(b12*b33 - b13*b23) +
    b13*(b12*b23 - b13*b22) = &1`
   ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["b11";"b12";"b13";"b22";"b23";"b33"] THEN
    MP_TAC(ASSUME `v1 * (c22 * c33 - c23 * c32) - c12 * (v2 * c33 - c23 * v3) +
                   c13 * (v2 * c32 - c22 * v3) = &1`) THEN
    MP_TAC(ASSUME
     `a11 * (a22 * a33 - a23 pow 2) -
      a12 * (a12 * a33 - a23 * a13) +
      a13 * (a12 * a23 - a22 * a13) = &1`) THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y z. ~(x = &0 /\ y = &0 /\ z = &0)
            ==> &0 < b11*x pow 2 + b22*y pow 2 + b33*z pow 2 +
                     &2*b12*x*y + &2*b13*x*z + &2*b23*y*z`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INT_LTE_TRANS THEN EXISTS_TAC `b11:int` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b11*b22 - b12 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC POSDEF_MINOR2 THEN
    MAP_EVERY EXISTS_TAC [`b13:int`;`b23:int`;`b33:int`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b11 = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC HERMITE_A1 THEN
    MAP_EVERY EXISTS_TAC [`b12:int`;`b13:int`;`b22:int`;`b23:int`;
      `b33:int`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?y1 y2 y3. b11*y1 pow 2 + b22*y2 pow 2 + b33*y3 pow 2 +
               &2*b12*y1*y2 + &2*b13*y1*y3 + &2*b23*y2*y3 = n`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CONJ_REPS THEN
    MAP_EVERY EXISTS_TAC
     [`a11:int`;`a12:int`;`a13:int`;`a22:int`;`a23:int`;`a33:int`;
      `v1:int`;`v2:int`;`v3:int`;`c12:int`;`c13:int`;`c22:int`;`c23:int`;
        `c32:int`;`c33:int`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC TSQ_DISC1_A11_1 THEN
  MAP_EVERY EXISTS_TAC [`b12:int`;`b13:int`;`b22:int`;`b23:int`;`b33:int`] THEN
  SUBST1_TAC(ASSUME `b11 = &1`) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < b11*b22 - b12 pow 2` THEN
    SUBST1_TAC(ASSUME `b11 = &1`) THEN REWRITE_TAC[INT_MUL_LID];
    UNDISCH_TAC
     `b11 * (b22 * b33 - b23 pow 2) -
      b12 * (b12 * b33 - b13 * b23) +
      b13 * (b12 * b23 - b13 * b22) = &1` THEN
    SUBST1_TAC(ASSUME `b11 = &1`) THEN REWRITE_TAC[INT_MUL_LID] THEN
    CONV_TAC INT_RING;
    MAP_EVERY EXISTS_TAC [`y1:int`;`y2:int`;`y3:int`] THEN
    UNDISCH_TAC
     `b11 * y1 pow 2 + b22 * y2 pow 2 + b33 * y3 pow 2 +
      &2 * b12 * y1 * y2 + &2 * b13 * y1 * y3 +
      &2 * b23 * y2 * y3 = n` THEN
    SUBST1_TAC(ASSUME `b11 = &1`) THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Nathanson Lemma 1.7: if 1 < n, 0 < d', and (d'n - 1) divides (t^2 + d')   *)
(* (i.e. -d' is a quadratic residue mod d'n - 1, witnessed by t), then n is  *)
(* a sum of three squares. Build the explicit discriminant-1 matrix A =      *)
(* [[a11, t, 1], [t, a22, 0], [1, 0, n]] with a22 = d'n - 1, a11 = (t^2 +    *)
(* d')/a22 (so a11 a22 - t^2 = d'); then det A = 1 and FA is                 *)
(* positive-definite and represents n at (0, 0, 1). TSQ_DISC1 finishes.      *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1_7 = prove
 (`!n d' t:int.
     &1 < n /\ &0 < d' /\ (d' * n - &1) divides (t pow 2 + d')
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = n`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a22 = d'*n - &1` THEN
  UNDISCH_TAC `a22 divides (t pow 2 + d')` THEN
  REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `a11:int`) THEN
  SUBGOAL_THEN `&0 < a22` ASSUME_TAC THENL
   [EXPAND_TAC "a22" THEN
    SUBGOAL_THEN `&1 * &2 <= d' * n` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL2 THEN ASM_INT_ARITH_TAC; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a11 * a22 - t pow 2 = d'` ASSUME_TAC THENL
   [MP_TAC(ASSUME `t pow 2 + d' = a22 * a11`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a11` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < a11 * a22` MP_TAC THENL
     [SUBGOAL_THEN `a11 * a22 = t pow 2 + d'` SUBST1_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `t:int` INT_LE_POW_2) THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INT_LT_MUL_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC TSQ_DISC1 THEN
  MAP_EVERY EXISTS_TAC [`a11:int`;`t:int`;`&1:int`;`a22:int`;`&0:int`;
    `n:int`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ASSUME `a11 * a22 - t pow 2 = d'`) THEN ASM_INT_ARITH_TAC;
    MP_TAC(ASSUME `a11 * a22 - t pow 2 = d'`) THEN
    MP_TAC(ASSUME `d' * n - &1 = a22`) THEN CONV_TAC INT_RING;
    MAP_EVERY EXISTS_TAC [`&0:int`;`&0:int`;`&1:int`] THEN
    CONV_TAC INT_RING]);;

(* ------------------------------------------------------------------------- *)
(* Congruence-form interface to Lemma 1.7: it suffices that -d' is a         *)
(* quadratic residue modulo d'n - 1 (the form in which Dirichlet's theorem + *)
(* quadratic reciprocity will supply the hypothesis).                        *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1_7_CONG = prove
 (`!n d':int.
     &1 < n /\ &0 < d' /\ (?x:int. (x pow 2 + d' == &0) (mod (d' * n - &1)))
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LEMMA_1_7 THEN
  MAP_EVERY EXISTS_TAC [`d':int`;`x:int`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x pow 2 + d' == &0) (mod (d'*n - &1))` THEN
  REWRITE_TAC[int_congruent] THEN
  REWRITE_TAC[int_divides] THEN STRIP_TAC THEN EXISTS_TAC `d:int` THEN
  POP_ASSUM MP_TAC THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Quadratic-residue endgame (Nathanson Lemmas 1.8/1.9): Dirichlet's theorem *)
(* and quadratic reciprocity supply an integer d' with -d' a quadratic       *)
(* residue modulo d'n - 1. This part is natural-number number theory; its    *)
(* terms carry explicit :num annotations and num-only operators (EXP, DIV,   *)
(* MOD, jacobi, coprime, ...), so it runs under the file-wide                *)
(* prioritize_int() with no priority switch.                                 *)
(* ------------------------------------------------------------------------- *)

let CONG_1_MOD_8 = prove
 (`!d:num. (d == 1) (mod 8) ==> ?q. d = 8 * q + 1`,
  MESON_TAC[CONG_CASE; MULT_SYM; ARITH_RULE `1 < 8`]);;

let CONG_MOD_8_IMP_MOD_4 = prove
 (`!x a:num. (x == a) (mod 8) ==> (x == a) (mod 4)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SPECL [`x:num`;`a:num`;`8`;`4`] CONG_DIVIDES_MODULUS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC DIVIDES_CONV);;

let JACOBI_2_1MOD8 = prove
 (`!d:num. (d == 1) (mod 8) ==> jacobi(2, d) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q:num` o MATCH_MP CONG_1_MOD_8) THEN
  ASM_SIMP_TAC[JACOBI_OF_2] THEN
  ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN
  ASM_REWRITE_TAC
   [ARITH_RULE `((8 * q + 1) EXP 2 - 1) DIV 8 = 8*q*q + 2*q`] THEN
  REWRITE_TAC[INT_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH; INT_POW_ONE]);;

let CONG_1_MOD_4 = prove
 (`!d:num. (d == 1) (mod 4) ==> ?q. d = 4 * q + 1`,
  MESON_TAC[CONG_CASE; MULT_SYM; ARITH_RULE `1 < 4`]);;

let ODD_OF_1MOD4 = prove
 (`!p:num. (p == 1) (mod 4) ==> ODD p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `q:num` SUBST1_TAC o
    MATCH_MP CONG_1_MOD_4) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]);;

let JACOBI_M1_1MOD4 = prove
 (`!p:num. (p == 1) (mod 4) ==> jacobi(p - 1, p) = &1`,
  SIMP_TAC[JACOBI_MINUS1_CASES; ODD_OF_1MOD4]);;

let CONG_3_MOD_8 = prove
 (`!d:num. (d == 3) (mod 8) ==> ?q. d = 8 * q + 3`,
  MESON_TAC[CONG_CASE; MULT_SYM; ARITH_RULE `3 < 8`]);;

let CONG_3_MOD_4 = prove
 (`!d:num. (d == 3) (mod 4) ==> ?q. d = 4 * q + 3`,
  MESON_TAC[CONG_CASE; MULT_SYM; ARITH_RULE `3 < 4`]);;

let ODD_OF_3MOD4 = prove
 (`!p:num. (p == 3) (mod 4) ==> ODD p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q:num` o MATCH_MP CONG_3_MOD_4) THEN
  ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]);;

let JACOBI_M1_3MOD4 = prove
 (`!p:num. (p == 3) (mod 4) ==> jacobi(p - 1, p) = -- &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q:num` o MATCH_MP CONG_3_MOD_4) THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [MATCH_MP_TAC ODD_OF_3MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[JACOBI_MINUS1] THEN
  ASM_REWRITE_TAC[ARITH_RULE `((4 * q + 3) - 1) DIV 2 = 2 * q + 1`] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; EVEN_ADD; EVEN_MULT; ARITH]);;

let JACOBI_2_3MOD8 = prove
 (`!d:num. (d == 3) (mod 8) ==> jacobi(2, d) = -- &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q:num` o MATCH_MP CONG_3_MOD_8) THEN
  ASM_SIMP_TAC[JACOBI_OF_2] THEN
  ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN
  ASM_REWRITE_TAC
   [ARITH_RULE `((8 * q + 3) EXP 2 - 1) DIV 8 = 8*q*q + 6*q + 1`] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; EVEN_ADD; EVEN_MULT; ARITH]);;

let JACOBI_P_DPRIME = prove
 (`!p d':num.
     ((d' == 1) (mod 8) \/ (d' == 3) (mod 8)) /\
     (2 * p == d' - 1) (mod d')
     ==> jacobi(p, d') = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CONG_MOD_8_IMP_MOD_4 o
    check (fun th -> can (find_term (fun t -> t = `8`)) (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP(SPECL [`2*p`;`d' - 1`;`d':num`] JACOBI_CONG) o
    check (fun th -> concl th = `(2*p == d' - 1) (mod d')`)) THEN
  MP_TAC(SPECL [`2`;`p:num`;`d':num`] JACOBI_LMUL) THEN
  ASM_SIMP_TAC[JACOBI_M1_1MOD4; JACOBI_M1_3MOD4;
    JACOBI_2_1MOD8; JACOBI_2_3MOD8] THEN
  INT_ARITH_TAC);;

let JACOBI_FLIP_1MOD4 = prove
 (`!p d':num.
     ODD p /\ ODD d' /\ coprime(p,d') /\ (p == 1) (mod 4)
     ==> jacobi(d', p) = jacobi(p, d')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`;`d':num`] JACOBI_RECIPROCITY) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `qp:num` o MATCH_MP CONG_1_MOD_4) THEN
  SUBGOAL_THEN `(p - 1) DIV 2 = 2 * qp` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `((4 * qp + 1) - 1) DIV 2 = 2 * qp`];
     ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(2 * qp) * m = 2 * (qp * m)`] THEN
  REWRITE_TAC[INT_POW_NEG; EVEN_MULT; ARITH; INT_POW_ONE; INT_MUL_LID]);;

let JACOBI_NEG_1MOD4 = prove
 (`!p d:num.
     ODD p /\ ODD d /\ coprime(p,d) /\
     (p == 1) (mod 4) /\ jacobi(p,d) = &1
     ==> jacobi(d * (p - 1),p) = &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[JACOBI_LMUL] THEN
  ASM_SIMP_TAC[JACOBI_M1_1MOD4] THEN
  REWRITE_TAC[INT_MUL_RID] THEN
  SUBGOAL_THEN `jacobi(d,p) = jacobi(p,d)` SUBST1_TAC THENL
   [MATCH_MP_TAC JACOBI_FLIP_1MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let JACOBI_NEGATIVE_SQUARE = prove
 (`!p d:num.
     prime p /\ jacobi(d * (p - 1),p) = &1
     ==> ?x. (x EXP 2 + d == 0) (mod p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:num. (x EXP 2 == d * (p - 1)) (mod p)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d * (p - 1)`; `p:num`] JACOBI_PRIME) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p divides d * (p - 1)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `?x:num. (x EXP 2 == d * (p - 1)) (mod p)` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `x:num` THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `d * (p - 1) + d:num` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_ADD THEN ASM_REWRITE_TAC[CONG_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `d * (p - 1) + d = d * p:num` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [ARITH_RULE `d = d * 1`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUB_ADD THEN
    MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[CONG_0_DIVIDES] THEN
    MATCH_MP_TAC DIVIDES_LMUL THEN REWRITE_TAC[DIVIDES_REFL]]);;

let QR_MOD_P_1MOD4 = prove
 (`!p d:num.
     prime p /\ ODD d /\ coprime(p,d) /\
     (p == 1) (mod 4) /\ jacobi(p,d) = &1
     ==> ?x. (x EXP 2 + d == 0) (mod p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [MATCH_MP_TAC ODD_OF_1MOD4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC JACOBI_NEGATIVE_SQUARE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC JACOBI_NEG_1MOD4 THEN ASM_REWRITE_TAC[]);;

let QR_MOD_P = prove
 (`!p d':num.
     prime p /\ ODD d' /\ coprime(p,d') /\
     (p == 1) (mod 4) /\
     ((d' == 1) (mod 8) \/ (d' == 3) (mod 8)) /\
     (2 * p == d' - 1) (mod d')
     ==> ?x. (x EXP 2 + d' == 0) (mod p)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC QR_MOD_P_1MOD4 THEN
  ASM_SIMP_TAC[JACOBI_P_DPRIME]);;

let QR_LIFT_2P = prove
 (`!p d' x:num.
     ODD p /\ ODD d' /\ (x EXP 2 + d' == 0) (mod p)
     ==> ?z. (z EXP 2 + d' == 0) (mod (2 * p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z. ODD z /\ (z == x) (mod p)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `ODD x` THENL
     [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[CONG_REFL];
      EXISTS_TAC `x + p:num` THEN
      ASM_REWRITE_TAC[ODD_ADD; NUMBER_RULE `!x p:num. (x + p == x) (mod p)`]];
    ALL_TAC] THEN
  EXISTS_TAC `z:num` THEN
  REWRITE_TAC[CONG_0_DIVIDES] THEN
  MATCH_MP_TAC DIVIDES_MUL THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIVIDES_2; EVEN_ADD; EVEN_EXP; ARITH] THEN
    REWRITE_TAC[GSYM NOT_ODD] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(z EXP 2 + d' == 0) (mod p)` MP_TAC THENL
     [MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `x EXP 2 + d'` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL] THEN
      ASM_SIMP_TAC[CONG_EXP];
      REWRITE_TAC[CONG_0_DIVIDES]];
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_REWRITE_TAC[COPRIME_2; GSYM NOT_EVEN; NOT_ODD]]);;

let LEGENDRE_TAIL = prove
 (`!q d m x:num.
     (x EXP 2 + d == 0) (mod q) /\
     q + 1 = d * m /\
     1 < m /\ 1 <= d
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = &m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&m:int`; `&d:int`] LEMMA_1_7_CONG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
      EXISTS_TAC `&x:int` THEN
      SUBGOAL_THEN `&d * &m - &1:int = &q` SUBST1_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_MUL;
          GSYM(ASSUME `q + 1 = d * m`); GSYM INT_OF_NUM_ADD] THEN
        INT_ARITH_TAC;
        UNDISCH_TAC `(x EXP 2 + d == 0) (mod q)` THEN
        REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW;
          GSYM INT_OF_NUM_ADD]]];
    MESON_TAC[]]);;

let LEGENDRE_TAIL_2P = prove
 (`!p d m:num.
     ODD p /\ ODD d /\
     (?x. (x EXP 2 + d == 0) (mod p)) /\
     2 * p + 1 = d * m /\
     1 < m
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = &m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`;`d:num`;`x:num`] QR_LIFT_2P) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  MATCH_MP_TAC(SPECL [`2 * p`;`d:num`;`m:num`;`z:num`] LEGENDRE_TAIL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ODD_EXISTS] o
    check (fun th -> concl th = `ODD d`)) THEN
  ARITH_TAC);;

(* The remaining number theory (Dirichlet, the residue computation, the      *)
(* assembly of Lemma 1.9) is natural-number; only the explicitly &-coerced   *)
(* subterms touch the integers.                                              *)

(* ------------------------------------------------------------------------- *)
(* Dirichlet's theorem supplies the prime. For m = 8k+3 (the case needed for *)
(* Gauss's triangular theorem), choose a prime p = 4mj + (m-1)/2 = 4mj+4k+1  *)
(* (Dirichlet: the residue 4k+1 is coprime to the modulus 4m), and set d' =  *)
(* 8j+1. Then d'm - 1 = 2p, d' = 1 (mod 8), p = 1 (mod 4), and the           *)
(* reciprocity computation above makes -d' a quadratic residue mod 2p, so    *)
(* Lemma 1.7 represents m as a sum of three squares.                         *)
(* ------------------------------------------------------------------------- *)

let COPRIME_DIRICHLET = prove
 (`!a b c:num. ODD a /\ c * b = 2 * a + 1 ==> coprime(a,4 * b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COPRIME_RMUL] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; COPRIME_RMUL; COPRIME_2] THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN];
    REWRITE_TAC[COPRIME_BEZOUT] THEN
    MAP_EVERY EXISTS_TAC [`c:num`;`2`] THEN DISJ2_TAC THEN ASM_ARITH_TAC]);;

let DIRICHLET_PRIME_CONG = prove
 (`!m a:num. 1 < m /\ coprime(a,m)
            ==> ?p. prime p /\ (p == a) (mod m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`;`a:num`] DIRICHLET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[]);;

let DIRICHLET_PRIME = prove
 (`!k:num. ?p. prime p /\ (p == 4 * k + 1) (mod (4 * (8 * k + 3)))`,
  GEN_TAC THEN MATCH_MP_TAC DIRICHLET_PRIME_CONG THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SPECL [`4*k+1`;`8*k+3`;`1`] COPRIME_DIRICHLET) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ARITH_TAC);;

let COPRIME_FROM_MULTP1 = NUMBER_RULE
 `!p c d m:num. prime p /\ c * p + 1 = d * m ==> coprime(p,d)`;;

(* ========================================================================= *)
(* Legendre/Gauss three squares for n = 3 (mod 8): every 8k+3 is a sum of    *)
(* three squares (Nathanson Lemma 1.9, c = 1 case), assembled from           *)
(* Dirichlet, quadratic reciprocity, the residue lift to mod 2p, and Lemma   *)
(* 1.7.                                                                      *)
(* ========================================================================= *)

let THREE_SQ_3MOD8 = prove
 (`!k:num. ?u v w:int. u pow 2 + v pow 2 + w pow 2 = &(8 * k + 3)`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` DIRICHLET_PRIME) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j. p = 4*(8*k+3)*j + (4*k+1)`
  (X_CHOOSE_TAC `j:num`) THENL
   [MP_TAC(SPECL [`4*(8*k+3)`; `4*k+1`; `p:num`] CONG_CASE) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d' = 8*j+1` THEN
  ABBREV_TAC `m = 8*k+3` THEN
  SUBGOAL_THEN `2 * p = d' * m - 1 /\ 2 * p + 1 = d' * m`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p = 4 * m * j + 4 * k + 1` THEN
    MAP_EVERY EXPAND_TAC ["d'";"m"] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d' == 1) (mod 8)` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[CONG; ARITH_RULE `8*j+1 = j*8+1`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD d'` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(p == 1) (mod 4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONG; ARITH_RULE `4*m*j+4*k+1 = (m*j+k)*4+1`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `4*m*j+4*k+1 = 2*(2*m*j+2*k)+1`; ODD_ADD;
     ODD_MULT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * p == d' - 1) (mod d')` ASSUME_TAC THENL
   [REWRITE_TAC[CONG_MINUS1] THEN DISJ2_TAC THEN
    REWRITE_TAC[ASSUME `2 * p + 1 = d' * m`] THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p:num,d')` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`p:num`;`2`;`d':num`;`m:num`] COPRIME_FROM_MULTP1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SPECL [`p:num`;`d':num`;`m:num`] LEGENDRE_TAIL_2P) THEN
  ASM_SIMP_TAC[QR_MOD_P] THEN
  MAP_EVERY EXPAND_TAC ["d'";"m"] THEN ARITH_TAC);;

(* ========================================================================= *)
(* Supporting results for the full Legendre three-square theorem.            *)
(* (1) THREE_SQ_3MOD8_NUM: the natural-number form of THREE_SQ_3MOD8.        *)
(* (2) The easy "impossibility" direction: 4^a(8m+7) is never a sum of three *)
(*     squares (squares are 0,1,4 mod 8, so a sum of three is never 7 mod 8; *)
(*     and 4 | a sum of three squares forces all three even, giving          *)
(*     descent).                                                             *)
(* (3) THREE_SQ_DOUBLE: if n is a sum of three squares then so is 4n. These  *)
(* feed the strict iff (?u v w. u^2+v^2+w^2 = n) <=> ~(?a m. n=4^a(8m+7)).   *)
(* ========================================================================= *)

let THREE_SQ_INT_TO_NUM = prove
 (`!n:num.
     (?u v w:int. u pow 2 + v pow 2 + w pow 2 = &n)
     ==> (?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = n)`,
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:int` (X_CHOOSE_THEN `v:int`
    (X_CHOOSE_TAC `w:int`))) THEN
  MAP_EVERY EXISTS_TAC [`num_of_int(abs u)`; `num_of_int(abs v)`;
    `num_of_int(abs w)`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
    GSYM INT_OF_NUM_POW] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  REWRITE_TAC[INT_POW2_ABS] THEN ASM_REWRITE_TAC[]);;

let THREE_SQ_3MOD8_NUM = prove
 (`!k:num. ?u v w:num. u EXP 2 + v EXP 2 + w EXP 2 = 8 * k + 3`,
  GEN_TAC THEN MATCH_MP_TAC THREE_SQ_INT_TO_NUM THEN
  REWRITE_TAC[THREE_SQ_3MOD8]);;

let SQUARE_MOD_8 = prove
 (`!n. (n EXP 2 == 0) (mod 8) \/
       (n EXP 2 == 1) (mod 8) \/
       (n EXP 2 == 4) (mod 8)`,
  GEN_TAC THEN SIMP_TAC[CONG; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[GSYM MOD_EXP_MOD] THEN
  MP_TAC(SPECL [`n:num`; `8`] DIVISION) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN SIMP_TAC[LT; ARITH; ARITH_RULE
   `~(m = 0) ==> (n < m <=> n = m - 1 \/ n < m - 1)`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let THREE_SQUARES_MOD_8 = prove
 (`!x y z. ~((x EXP 2 + y EXP 2 + z EXP 2 == 7) (mod 8))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (MP_TAC o C SPEC SQUARE_MOD_8) [`z:num`; `y:num`; `x:num`] THEN
  REWRITE_TAC[IMP_IMP; TAUT `a ==> ~b <=> ~(a /\ b)`;
              LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB; GSYM DISJ_ASSOC;
              GSYM CONJ_ASSOC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (MP_TAC o MATCH_MP (NUMBER_RULE
   `(x:num == a) (mod n) /\ (y == b) (mod n) /\ (z == c) (mod n) /\
    (x + y + z == d) (mod n)
    ==> (a + b + c == d) (mod n)`))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(RAND_CONV CONG_CONV) THEN
  REWRITE_TAC[]);;

let THREE_SQUARES_4_LEMMA = prove
 (`!x y z.
     4 divides (x EXP 2 + y EXP 2 + z EXP 2)
     ==> EVEN x /\ EVEN y /\ EVEN z`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (MP_TAC o C SPEC EVEN_OR_ODD) [`x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN
  REPEAT(DISCH_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * n) EXP 2 = 4 * (n EXP 2 + n) + 1`;
              ARITH_RULE `(2 * n) EXP 2 = 4 * n EXP 2`] THEN
  REWRITE_TAC[NUMBER_RULE `p:num divides (p * x + y) <=> p divides y`;
              NUMBER_RULE `p divides (1 + p * q) <=> p divides 1`;
              NUMBER_RULE `p divides (1 + p * q + r) <=> p divides (r + 1)`;
              GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
  REWRITE_TAC[]);;

let NOT_THREE_SQUARES = prove
 (`!a m x y z. ~(4 EXP a * (8 * m + 7) = x EXP 2 + y EXP 2 + z EXP 2)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `8` o MATCH_MP EQ_IMP_CONG) THEN
    MP_TAC(SPECL [`x:num`; `y:num`; `z:num`] THREE_SQUARES_MOD_8) THEN
    REWRITE_TAC[CONTRAPOS_THM; ARITH; MULT_CLAUSES] THEN
    SPEC_TAC(`8`,`e:num`) THEN NUMBER_TAC;
    REWRITE_TAC[EXP; GSYM MULT_ASSOC] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `EVEN x /\ EVEN y /\ EVEN z` MP_TAC THENL
     [MATCH_MP_TAC THREE_SQUARES_4_LEMMA THEN ASM_MESON_TAC[divides];
      ALL_TAC] THEN
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
    UNDISCH_TAC `4 * 4 EXP a * (8 * m + 7) = x EXP 2 + y EXP 2 + z EXP 2` THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * x) EXP 2 = 4 * x EXP 2`] THEN
    ASM_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL; ARITH]]);;

let THREE_SQ_DOUBLE = prove
 (`!n.
     (?x y z. x EXP 2 + y EXP 2 + z EXP 2 = n)
     ==> (?x y z. x EXP 2 + y EXP 2 + z EXP 2 = 4 * n)`,
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num`
    (X_CHOOSE_TAC `z:num`))) THEN
  MAP_EVERY EXISTS_TAC [`2 * x`; `2 * y`; `2 * z`] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m) EXP 2 = 4 * m EXP 2`] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The n = 2 (mod 4) case (Nathanson Lemma 1.8). Here d' = 4j+1 and the      *)
(* Dirichlet prime p = d'n - 1 directly (NO 2p lift), with p = 1 (mod 4); -d' *)
(* is a QR mod p by reciprocity (d' = 1 mod 4).                              *)
(* ========================================================================= *)

let ODD_PRED_EVEN = prove
 (`!n:num. 1 <= n /\ EVEN n ==> ODD(n - 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ODD_SUB; ARITH] THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
  ASM_CASES_TAC `n = 1` THENL
   [UNDISCH_TAC `EVEN n` THEN ASM_REWRITE_TAC[ARITH];
    ASM_ARITH_TAC]);;

let CONG_2_MOD_4 = prove
 (`!n:num. (n == 2) (mod 4) ==> ?t. n = 4 * t + 2`,
  MESON_TAC[CONG_CASE; MULT_SYM; ARITH_RULE `2 < 4`]);;

let QR_MOD_P_18 = prove
 (`!p d':num.
     prime p /\ ODD d' /\ coprime(p,d') /\
     (p == 1) (mod 4) /\ (d' == 1) (mod 4) /\
     (p == d' - 1) (mod d')
     ==> ?x. (x EXP 2 + d' == 0) (mod p)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC QR_MOD_P_1MOD4 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `jacobi(d' - 1,d')` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC JACOBI_CONG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC JACOBI_M1_1MOD4 THEN ASM_REWRITE_TAC[]]);;

let COPRIME_DIRICHLET_18 = prove
 (`!n:num. 1 <= n /\ EVEN n ==> coprime(n - 1, 4 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COPRIME_RMUL] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; COPRIME_RMUL] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_2] THEN
    ASM_SIMP_TAC[ODD_PRED_EVEN];
    MATCH_MP_TAC COPRIME_MINUS1 THEN
    UNDISCH_TAC `1 <= n` THEN ARITH_TAC]);;

let DIRICHLET_PRIME_18 = prove
 (`!n:num. 1 <= n /\ EVEN n ==> ?p. prime p /\ (p == n - 1) (mod (4 * n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIRICHLET_PRIME_CONG THEN
  ASM_SIMP_TAC[COPRIME_DIRICHLET_18] THEN ASM_ARITH_TAC);;

let THREE_SQ_2MOD4 = prove
 (`!n:num.
     1 < n /\ (n == 2) (mod 4)
     ==> ?u v w:int. u pow 2 + v pow 2 + w pow 2 = &n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC o MATCH_MP CONG_2_MOD_4) THEN
  SUBGOAL_THEN `1 <= 4 * t + 2 /\ EVEN(4 * t + 2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `4 * t + 2` DIRICHLET_PRIME_18) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j. p = 4 * (4 * t + 2) * j + ((4 * t + 2) - 1)`
  (X_CHOOSE_TAC `j:num`) THENL
   [MP_TAC(SPECL [`4*(4*t+2)`; `(4*t+2)-1`; `p:num`] CONG_CASE) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d' = 4 * j + 1` THEN
  SUBGOAL_THEN `p = d' * (4 * t + 2) - 1` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN
   UNDISCH_TAC `p = 4 * (4 * t + 2) * j + (4 * t + 2) - 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD d'` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(d' == 1)(mod 4)` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[CONG; ARITH_RULE `4*j+1 = j*4+1`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(p == 1)(mod 4)` ASSUME_TAC THENL
   [UNDISCH_TAC `p = 4 * (4 * t + 2) * j + (4 * t + 2) - 1` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC
     [CONG;
      ARITH_RULE
       `4 * (4 * t + 2) * j + (4 * t + 2) - 1 =
        (((4*t+2)*j + t) * 4) + 1`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `p + 1 = d' * (4 * t + 2)` ASSUME_TAC THENL
   [UNDISCH_TAC `p = d' * (4 * t + 2) - 1` THEN
    SUBGOAL_THEN `1 <= d' * (4 * t + 2)` MP_TAC THENL
     [EXPAND_TAC "d'" THEN ARITH_TAC; ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(p == d' - 1)(mod d')` ASSUME_TAC THENL
   [REWRITE_TAC[CONG_MINUS1] THEN DISJ2_TAC THEN
    REWRITE_TAC[ASSUME `p + 1 = d' * (4 * t + 2)`] THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p:num,d')` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`p:num`;`1`;`d':num`;`4*t+2`] COPRIME_FROM_MULTP1) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x. (x EXP 2 + d' == 0) (mod p)`
  (X_CHOOSE_TAC `x:num`) THENL
   [MATCH_MP_TAC QR_MOD_P_18 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC
   (SPECL [`p:num`;`d':num`;`4 * t + 2`;`x:num`] LEGENDRE_TAIL) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "d'" THEN ARITH_TAC);;

(* ========================================================================= *)
(* Legendre three squares for n = 1 (mod 8): every 8k+1 is a sum of three    *)
(* squares (Nathanson Lemma 1.9, c = 3 case). Mirrors the n = 3 (mod 8)      *)
(* assembly but with d' = 8j+3 (so d' = 3 (mod 8)) and the prime in the      *)
(* residue class 12k+1 (mod 4(8k+1)); the Jacobi computation flips sign      *)
(* twice (jacobi(-1,d') = jacobi(2,d') = -1 for d' = 3 (mod 8)), so          *)
(* jacobi(p,d') = 1 again and -d' is a quadratic residue mod p, lifted to    *)
(* mod 2p = d'(8k+1)-1.                                                      *)
(* ========================================================================= *)

let DIRICHLET_PRIME_1MOD8 = prove
 (`!k:num. ?p. prime p /\ (p == 12 * k + 1) (mod (4 * (8 * k + 1)))`,
  GEN_TAC THEN MATCH_MP_TAC DIRICHLET_PRIME_CONG THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SPECL [`12*k+1`;`8*k+1`;`3`] COPRIME_DIRICHLET) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ARITH_TAC);;

let THREE_SQ_1MOD8 = prove
 (`!k:num. ?u v w:int. u pow 2 + v pow 2 + w pow 2 = &(8 * k + 1)`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`&1:int`;`&0:int`;`&0:int`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` DIRICHLET_PRIME_1MOD8) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j. p = 4*(8*k+1)*j + (12*k+1)`
  (X_CHOOSE_TAC `j:num`) THENL
   [MP_TAC(SPECL [`4*(8*k+1)`; `12*k+1`; `p:num`] CONG_CASE) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d' = 8*j+3` THEN
  ABBREV_TAC `m = 8*k+1` THEN
  SUBGOAL_THEN `2 * p = d' * m - 1 /\ 2 * p + 1 = d' * m`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p = 4 * m * j + 12 * k + 1` THEN
    MAP_EVERY EXPAND_TAC ["d'";"m"] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d' == 3) (mod 8)` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[CONG; ARITH_RULE `8*j+3 = j*8+3`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD d'` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(p == 1) (mod 4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONG; ARITH_RULE `4*m*j+12*k+1 = (m*j+3*k)*4+1`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODD_OF_1MOD4]; ALL_TAC] THEN
  SUBGOAL_THEN `(2 * p == d' - 1) (mod d')` ASSUME_TAC THENL
   [REWRITE_TAC[CONG_MINUS1] THEN DISJ2_TAC THEN
    REWRITE_TAC[ASSUME `2 * p + 1 = d' * m`] THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p:num,d')` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`p:num`;`2`;`d':num`;`m:num`] COPRIME_FROM_MULTP1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SPECL [`p:num`;`d':num`;`m:num`] LEGENDRE_TAIL_2P) THEN
  ASM_SIMP_TAC[QR_MOD_P] THEN
  MAP_EVERY EXPAND_TAC ["d'";"m"] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* Legendre three squares for n = 5 (mod 8): every 8k+5 is a sum of three    *)
(* squares (Nathanson Lemma 1.9, c = 3 case, p = 3 (mod 4) branch). Same d'  *)
(* = 8j+3 as the n = 1 (mod 8) case, but the prime sits in class 12k+7 (mod  *)
(* 4(8k+5)), so p = 3 (mod 4). Then jacobi(-1,p) = -1 and the reciprocity    *)
(* flip also contributes -1 (both (p-1)/2 and (d'-1)/2 odd), and the two     *)
(* signs cancel: jacobi(d'(p-1),p) = 1 again, so -d' is a quadratic residue  *)
(* mod p.                                                                    *)
(* ========================================================================= *)

let JACOBI_FLIP_3MOD4 = prove
 (`!p d':num.
     ODD p /\ ODD d' /\ coprime(p,d') /\
     (p == 3) (mod 4) /\ (d' == 3) (mod 8)
     ==> jacobi(d', p) = -- jacobi(p, d')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`;`d':num`] JACOBI_RECIPROCITY) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `qp:num` o MATCH_MP CONG_3_MOD_4) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `qd:num` o MATCH_MP CONG_3_MOD_8) THEN
  SUBGOAL_THEN `(p - 1) DIV 2 = 2 * qp + 1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `((4 * qp + 3) - 1) DIV 2 = 2 * qp + 1`];
     ALL_TAC] THEN
  SUBGOAL_THEN `(d' - 1) DIV 2 = 4 * qd + 1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `((8 * qd + 3) - 1) DIV 2 = 4 * qd + 1`];
     ALL_TAC] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; EVEN_MULT; EVEN_ADD; ARITH] THEN
  INT_ARITH_TAC);;

let JACOBI_NEG_3MOD4 = prove
 (`!p d:num.
     ODD p /\ ODD d /\ coprime(p,d) /\
     (p == 3) (mod 4) /\ (d == 3) (mod 8) /\
     jacobi(p,d) = &1
     ==> jacobi(d * (p - 1),p) = &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[JACOBI_LMUL] THEN
  ASM_SIMP_TAC[JACOBI_M1_3MOD4] THEN
  SUBGOAL_THEN `jacobi(d,p) = -- jacobi(p,d)` SUBST1_TAC THENL
   [MATCH_MP_TAC JACOBI_FLIP_3MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let QR_MOD_P_5MOD8 = prove
 (`!p d':num.
     prime p /\ ODD d' /\ coprime(p,d') /\
     (p == 3) (mod 4) /\ (d' == 3) (mod 8) /\
     (2 * p == d' - 1) (mod d')
     ==> ?x. (x EXP 2 + d' == 0) (mod p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [MATCH_MP_TAC ODD_OF_3MOD4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC JACOBI_NEGATIVE_SQUARE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC JACOBI_NEG_3MOD4 THEN
  ASM_SIMP_TAC[JACOBI_P_DPRIME]);;

let DIRICHLET_PRIME_5MOD8 = prove
 (`!k:num. ?p. prime p /\ (p == 12 * k + 7) (mod (4 * (8 * k + 5)))`,
  GEN_TAC THEN MATCH_MP_TAC DIRICHLET_PRIME_CONG THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SPECL [`12*k+7`;`8*k+5`;`3`] COPRIME_DIRICHLET) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ARITH_TAC);;

let THREE_SQ_5MOD8 = prove
 (`!k:num. ?u v w:int. u pow 2 + v pow 2 + w pow 2 = &(8 * k + 5)`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` DIRICHLET_PRIME_5MOD8) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j. p = 4*(8*k+5)*j + (12*k+7)`
  (X_CHOOSE_TAC `j:num`) THENL
   [MP_TAC(SPECL [`4*(8*k+5)`; `12*k+7`; `p:num`] CONG_CASE) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d' = 8*j+3` THEN
  ABBREV_TAC `m = 8*k+5` THEN
  SUBGOAL_THEN `2 * p = d' * m - 1 /\ 2 * p + 1 = d' * m`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p = 4 * m * j + 12 * k + 7` THEN
    MAP_EVERY EXPAND_TAC ["d'";"m"] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d' == 3) (mod 8)` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[CONG; ARITH_RULE `8*j+3 = j*8+3`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD d'` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(p == 3) (mod 4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONG; ARITH_RULE `4*m*j+12*k+7 = (m*j+3*k+1)*4+3`] THEN
    SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODD_OF_3MOD4]; ALL_TAC] THEN
  SUBGOAL_THEN `(2 * p == d' - 1) (mod d')` ASSUME_TAC THENL
   [REWRITE_TAC[CONG_MINUS1] THEN DISJ2_TAC THEN
    REWRITE_TAC[ASSUME `2 * p + 1 = d' * m`] THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p:num,d')` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`p:num`;`2`;`d':num`;`m:num`] COPRIME_FROM_MULTP1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SPECL [`p:num`;`d':num`;`m:num`] LEGENDRE_TAIL_2P) THEN
  ASM_SIMP_TAC[QR_MOD_P_5MOD8] THEN
  MAP_EVERY EXPAND_TAC ["d'";"m"] THEN ARITH_TAC);;

(* ========================================================================= *)
(* FINAL ASSEMBLY: the full Legendre three-square theorem (?x y z. x^2 + y^2 *)
(*   + z^2 = n) <=> ~(?a m. n = 4^a (8m+7)). Backward direction by complete  *)
(*   induction on n: if n is not of the excluded form then n MOD 8 in        *)
(*   {1,2,3,5,6} (handled by the residue cases above), or n MOD 8 in {0,4}   *)
(*   (so 4 | n; descend to n DIV 4, which is also not of the excluded form,  *)
(*   and lift by THREE_SQ_DOUBLE), the case n MOD 8 = 7 being excluded by    *)
(*   hypothesis. Forward direction is NOT_THREE_SQUARES.                     *)
(* ========================================================================= *)

let THREE_SQ_1MOD8_NUM = prove
 (`!k:num. ?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = 8 * k + 1`,
  GEN_TAC THEN MATCH_MP_TAC THREE_SQ_INT_TO_NUM THEN
  REWRITE_TAC[THREE_SQ_1MOD8]);;

let THREE_SQ_5MOD8_NUM = prove
 (`!k:num. ?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = 8 * k + 5`,
  GEN_TAC THEN MATCH_MP_TAC THREE_SQ_INT_TO_NUM THEN
  REWRITE_TAC[THREE_SQ_5MOD8]);;

let THREE_SQ_2MOD4_NUM = prove
 (`!n:num.
     1 < n /\ (n == 2) (mod 4)
     ==> ?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SQ_INT_TO_NUM THEN
  MATCH_MP_TAC THREE_SQ_2MOD4 THEN ASM_REWRITE_TAC[]);;

let THREE_SQ_RESIDUE_NUM = prove
 (`!n:num.
     (n MOD 8 = 1 \/ n MOD 8 = 2 \/ n MOD 8 = 3 \/
      n MOD 8 = 5 \/ n MOD 8 = 6)
     ==> ?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = n`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`;`8`] (CONJUNCT1 DIVISION_SIMP)) THEN
  ABBREV_TAC `k = n DIV 8` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV
    o ONCE_DEPTH_CONV) [SYM th]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `k * 8 + r = 8 * k + r`] THEN
  REWRITE_TAC[THREE_SQ_1MOD8_NUM; THREE_SQ_3MOD8_NUM; THREE_SQ_5MOD8_NUM] THEN
  MATCH_MP_TAC THREE_SQ_2MOD4_NUM THEN
  (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THENL
   [REWRITE_TAC[CONG; ARITH_RULE `8*k+2 = (2*k)*4+2`];
    REWRITE_TAC[CONG; ARITH_RULE `8*k+6 = (2*k+1)*4+2`]] THEN
  SIMP_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOD8_04_DIV4 = prove
 (`!n:num. (n MOD 8 = 0 \/ n MOD 8 = 4) ==> 4 divides n`,
  GEN_TAC THEN REWRITE_TAC[DIVIDES_MOD] THEN
  SUBGOAL_THEN `n MOD 4 = n MOD 8 MOD 4` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 = 4 * 2`; MOD_MOD];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let DESCENT_NOT_FORM = prove
 (`!n:num.
     4 divides n /\ ~(?a m. n = 4 EXP a * (8 * m + 7))
     ==> ~(?a m. n DIV 4 = 4 EXP a * (8 * m + 7))`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`a:num`;`m:num`] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~(?a m. n = 4 EXP a * (8 * m + 7))` THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`SUC a`; `m:num`] THEN
  REWRITE_TAC[EXP; GSYM MULT_ASSOC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[divides]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `4 * c = c * 4`; DIV_MULT; ARITH] THEN
  SUBGOAL_THEN `(c * 4) DIV 4 = c` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `c * 4 = 4 * c`] THEN SIMP_TAC[DIV_MULT; ARITH];
    REFL_TAC]);;

let DIV4_LESS = prove
 (`!n:num. ~(n = 0) /\ 4 divides n ==> n DIV 4 < n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[divides]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `(4 * c) DIV 4 = c` SUBST1_TAC THENL
   [SIMP_TAC[DIV_MULT; ARITH]; ASM_ARITH_TAC]);;

let MOD8_7_FORM = prove
 (`!n:num. n MOD 8 = 7 ==> ?a m. n = 4 EXP a * (8 * m + 7)`,
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`0:num`; `n DIV 8`] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES] THEN
  MP_TAC(SPECL [`n:num`;`8`] (CONJUNCT1 DIVISION_SIMP)) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let THREE_SQ_NOT_FORM = prove
 (`!n:num.
     ~(?a m. n = 4 EXP a * (8 * m + 7))
     ==> ?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [MAP_EVERY EXISTS_TAC [`0:num`;`0`;`0`] THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE
   `(n MOD 8 = 1 \/ n MOD 8 = 2 \/ n MOD 8 = 3 \/ n MOD 8 = 5
     \/ n MOD 8 = 6) \/
    (n MOD 8 = 0 \/ n MOD 8 = 4) \/ n MOD 8 = 7`)
  THENL
   [MATCH_MP_TAC THREE_SQ_RESIDUE_NUM THEN FIRST_X_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ALL_TAC;
    MP_TAC(SPEC `n:num` MOD8_7_FORM) THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `4 divides n` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD8_04_DIV4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = n DIV 4` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 4`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC DIV4_LESS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC DESCENT_NOT_FORM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP THREE_SQ_DOUBLE) THEN
  SUBGOAL_THEN `4 * (n DIV 4) = n` SUBST1_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `c:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    SIMP_TAC[DIV_MULT; ARITH];
    REWRITE_TAC[]]);;

let LEGENDRE_THREE_SQUARES = prove
 (`!n:num.
     (?x y z:num. x EXP 2 + y EXP 2 + z EXP 2 = n) <=>
     ~(?a m. n = 4 EXP a * (8 * m + 7))`,
  MESON_TAC[NOT_THREE_SQUARES; THREE_SQ_NOT_FORM]);;

(* ========================================================================= *)
(* Gauss's triangular number theorem: every natural number is a sum of three *)
(* triangular numbers. This is the corollary that 8n + 3 is a sum of three   *)
(* squares iff n = T_a + T_b + T_c. A number congruent to 3 mod 8 that is a  *)
(* sum of three squares has all three summands odd (squares are 0, 1, 4 mod  *)
(* 8, and only 1 + 1 + 1 = 3 mod 8), and 8 T_k + 1 = (2k+1)^2. Here we       *)
(* package the reduction (the corollary), which together with                *)
(* three-squares-for-(8n+3) yields the theorem.                              *)
(* ========================================================================= *)

let REM_8_CASES = prove
 (`!x:int. x rem &8 = &0 \/ x rem &8 = &1 \/ x rem &8 = &2 \/ x rem &8 = &3 \/
           x rem &8 = &4 \/ x rem &8 = &5 \/ x rem &8 = &6 \/ x rem &8 = &7`,
  GEN_TAC THEN MP_TAC(SPECL [`x:int`;`&8:int`] INT_DIVISION) THEN
  INT_ARITH_TAC);;

let SQ_MOD_8 = prove
 (`!x:int.
     (x pow 2) rem &8 = &0 \/
     (x pow 2) rem &8 = &1 \/
     (x pow 2) rem &8 = &4`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
  MP_TAC(SPEC `x:int` REM_8_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let ODD_SQ_MOD_8 = prove
 (`!x:int. (x pow 2 rem &8 = &1) <=> ~(&2 divides x)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
  SUBGOAL_THEN `x rem &2 = (x rem &8) rem &2` SUBST1_TAC THENL
   [MESON_TAC[INT_REM_REM_MUL; INT_ARITH `&8 = &2 * &4`]; ALL_TAC] THEN
  MP_TAC(SPEC `x:int` REM_8_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let SUM3_MOD8_CORE = prove
 (`!pu pv pw:int.
     (pu = &0 \/ pu = &1 \/ pu = &4) /\
     (pv = &0 \/ pv = &1 \/ pv = &4) /\
     (pw = &0 \/ pw = &1 \/ pw = &4) /\
     (pu + pv + pw) rem &8 = &3
     ==> pu = &1 /\ pv = &1 /\ pw = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV);;

let THREE_SQ_ALL_ODD = prove
 (`!u v w n:int.
     u pow 2 + v pow 2 + w pow 2 = &8 * n + &3
     ==> ~(&2 divides u) /\ ~(&2 divides v) /\ ~(&2 divides w)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM ODD_SQ_MOD_8] THEN
  MATCH_MP_TAC SUM3_MOD8_CORE THEN
  REWRITE_TAC[SQ_MOD_8] THEN
  SUBGOAL_THEN
   `(u pow 2 rem &8 + v pow 2 rem &8 + w pow 2 rem &8) rem &8 =
    (u pow 2 + v pow 2 + w pow 2) rem &8` SUBST1_TAC THENL
   [CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC;
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_REM_MUL_ADD] THEN
    CONV_TAC INT_REDUCE_CONV]);;

(* An odd integer has the form 2a + 1; an integer triangular term a(a+1) is  *)
(* a natural triangular term k(k+1) (k = a or -a-1, whichever is             *)
(* nonnegative).                                                             *)

let INT_ODD_FORM = prove
 (`!u:int. ~(&2 divides u) ==> ?a. u = &2 * a + &1`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `u div &2` THEN
  MP_TAC(SPECL [`u:int`;`&2:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_ARITH `~(&2 = &0)`] THEN
  SUBGOAL_THEN `u rem &2 = &1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_2_DIVIDES]; INT_ARITH_TAC]);;

let INT_TRI_NAT = prove
 (`!a:int. ?k:num. a * (a + &1) = &(k * (k + 1))`,
  GEN_TAC THEN DISJ_CASES_TAC(INT_ARITH `&0 <= a \/ a < &0`) THENL
   [EXISTS_TAC `num_of_int a` THEN
    SUBGOAL_THEN `&(num_of_int a) = a` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    EXISTS_TAC `num_of_int(--a - &1)` THEN
    SUBGOAL_THEN `&(num_of_int(--a - &1)) = --a - &1` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let GAUSS_TRI_FROM_3SQ = prove
 (`!n.
     (?u v w:int. u pow 2 + v pow 2 + w pow 2 = &8 * &n + &3)
     ==> ?a b c:num. 2 * n = a * (a + 1) + b * (b + 1) + c * (c + 1)`,
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:int` (X_CHOOSE_THEN `v:int`
    (X_CHOOSE_TAC `w:int`))) THEN
  MP_TAC(SPECL [`u:int`; `v:int`; `w:int`; `&n:int`] THREE_SQ_ALL_ODD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:int` INT_ODD_FORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r:int`) THEN
  MP_TAC(SPEC `v:int` INT_ODD_FORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:int`) THEN
  MP_TAC(SPEC `w:int` INT_ODD_FORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:int`) THEN
  SUBGOAL_THEN
   `&2 * &n = r * (r + &1) + s * (s + &1) + t * (t + &1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `u pow 2 + v pow 2 + w pow 2 = &8 * &n + &3` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `r:int` INT_TRI_NAT) THEN DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  MP_TAC(SPEC `s:int` INT_TRI_NAT) THEN DISCH_THEN(X_CHOOSE_TAC `b:num`) THEN
  MP_TAC(SPEC `t:int` INT_TRI_NAT) THEN DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b:num`; `c:num`] THEN
  UNDISCH_TAC
   `&2 * &n = r * (r + &1) + s * (s + &1) + t * (t + &1)` THEN
  ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES]);;

let GAUSS_TRIANGULAR = prove
 (`!n:num. ?a b c. 2 * n = a * (a + 1) + b * (b + 1) + c * (c + 1)`,
  GEN_TAC THEN MATCH_MP_TAC GAUSS_TRI_FROM_3SQ THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; THREE_SQ_3MOD8]);;

let triangular = new_definition
 `triangular t <=> ?k. t = (k * (k + 1)) DIV 2`;;

let GAUSS_TRIANGULAR_SUM = prove
 (`!n:num.
     ?a b c. triangular a /\ triangular b /\ triangular c /\
             n = a + b + c`,
  GEN_TAC THEN
  MP_TAC(SPEC `n:num` GAUSS_TRIANGULAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num`
    (X_CHOOSE_TAC `c:num`))) THEN
  SUBGOAL_THEN
   `EVEN(a * (a + 1)) /\ EVEN(b * (b + 1)) /\ EVEN(c * (c + 1))`
  MP_TAC THENL
   [REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH; GSYM NOT_EVEN] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `ka:num`)
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `kb:num`) (X_CHOOSE_TAC `kc:num`))) THEN
  MAP_EVERY EXISTS_TAC [`ka:num`;`kb:num`;`kc:num`] THEN
  REWRITE_TAC[triangular] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[ARITH_RULE `(2 * x) DIV 2 = x`];
    EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[ARITH_RULE `(2 * x) DIV 2 = x`];
    EXISTS_TAC `c:num` THEN ASM_REWRITE_TAC[ARITH_RULE `(2 * x) DIV 2 = x`];
    UNDISCH_TAC `2 * n = a * (a + 1) + b * (b + 1) + c * (c + 1)` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* Restore the real overload priority established by 100/dirichlet.ml.       *)

prioritize_real();;
