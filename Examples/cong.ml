(* ========================================================================= *)
(* Integer congruences.                                                      *)
(* ========================================================================= *)

prioritize_int();;

(* ------------------------------------------------------------------------- *)
(* Combined rewrite, for later proofs.                                       *)
(* ------------------------------------------------------------------------- *)

let CONG = prove
 (`(x == y) (mod n) <=> ?q. x - y = q * n`,
  REWRITE_TAC[int_congruent; int_divides] THEN MESON_TAC[INT_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Trivial consequences.                                                     *)
(* ------------------------------------------------------------------------- *)

let CONG_MOD_0 = prove
 (`(x == y) (mod (&0)) <=> (x = y)`,
  INTEGER_TAC);;

let CONG_MOD_1 = prove
 (`(x == y) (mod (&1))`,
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Congruence is an equivalence relation.                                    *)
(* ------------------------------------------------------------------------- *)

let CONG_REFL = prove
 (`!n x. (x == x) (mod n)`,
  INTEGER_TAC);;

let CONG_SYM = prove
 (`!n x y. (x == y) (mod n) ==> (y == x) (mod n)`,
  INTEGER_TAC);;

let CONG_TRANS = prove
 (`!n x y z. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`,
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Congruences are indeed congruences.                                       *)
(* ------------------------------------------------------------------------- *)

let CONG_ADD = prove
 (`!n x1 x2 y1 y2.
    (x1 == x2) (mod n) /\ (y1 == y2) (mod n) ==> (x1 + y1 == x2 + y2) (mod n)`,
  INTEGER_TAC);;

let CONG_NEG = prove
 (`!n x1 x2. (x1 == x2) (mod n) ==> (--x1 == --x2) (mod n)`,
  INTEGER_TAC);;

let CONG_SUB = prove
 (`!n x1 x2 y1 y2.
    (x1 == x2) (mod n) /\ (y1 == y2) (mod n) ==> (x1 - y1 == x2 - y2) (mod n)`,
  INTEGER_TAC);;

let CONG_MUL = prove
 (`!n x1 x2 y1 y2.
    (x1 == x2) (mod n) /\ (y1 == y2) (mod n) ==> (x1 * y1 == x2 * y2) (mod n)`,
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Various other trivial properties of congruences.                          *)
(* ------------------------------------------------------------------------- *)

let CONG_MOD_NEG = prove
 (`!x y n. (x == y) (mod (--n)) <=> (x == y) (mod n)`,
  INTEGER_TAC);;

let CONG_MOD_ABS = prove
 (`!x y n. (x == y) (mod (abs n)) <=> (x == y) (mod n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_ABS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONG_MOD_NEG]);;

let CONG_MULTIPLE = prove
 (`!m n. (m * n == &0) (mod n)`,
  INTEGER_TAC);;

let CONG_SELF = prove
 (`!n. (n == &0) (mod n)`,
  INTEGER_TAC);;

let CONG_SELF_ABS = prove
 (`!n. (abs(n) == &0) (mod n)`,
  ONCE_REWRITE_TAC[GSYM CONG_MOD_ABS] THEN REWRITE_TAC[CONG_SELF]);;

let CONG_MOD_1 = prove
 (`(x == y) (mod &1)`,
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Can choose a representative, either positive or with minimal magnitude.   *)
(* ------------------------------------------------------------------------- *)

let CONG_REP_POS_POS = prove
 (`!n x. &0 <= x /\ ~(n = &0)
         ==> ?y. &0 <= y /\ y < abs(n) /\ (x == y) (mod n)`,
  REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS] THEN
  MAP_EVERY X_GEN_TAC [`n:int`; `k:num`] THEN
  ONCE_REWRITE_TAC[GSYM CONG_MOD_ABS] THEN
  MP_TAC(SPEC `n:int` INT_ABS_POS) THEN
  ONCE_REWRITE_TAC[INT_ARITH `(n = &0) <=> (abs n = &0)`] THEN
  SPEC_TAC(`abs n`,`n:int`) THEN REWRITE_TAC[GSYM INT_FORALL_POS] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[INT_OF_NUM_EQ] THEN DISCH_TAC THEN
  EXISTS_TAC `&(k MOD n)` THEN
  REWRITE_TAC[CONG; INT_OF_NUM_LE; INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[DIVISION; LE_0] THEN EXISTS_TAC `&(k DIV n)` THEN
  REWRITE_TAC[INT_ARITH `(x - y = z) <=> (x = z + y)`] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[DIVISION]);;

let CONG_REP_POS = prove
 (`!n x. ~(n = &0) ==> ?y. &0 <= y /\ y < abs(n) /\ (x == y) (mod n)`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(INT_ARITH `&0 <= x \/ &0 <= --x`) THEN
  ASM_SIMP_TAC[CONG_REP_POS_POS] THEN
  MP_TAC(SPECL [`n:int`; `--x`] CONG_REP_POS_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:int` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `y = &0` THENL
   [EXISTS_TAC `y:int` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONG_NEG) THEN
    ASM_REWRITE_TAC[INT_NEG_0; INT_NEG_NEG];
    ALL_TAC] THEN
  EXISTS_TAC `abs(n) - y` THEN
  ASM_SIMP_TAC[INT_ARITH `y < abs(n) ==> &0 <= abs(n) - y`;
               INT_ARITH `&0 <= y /\ ~(y = &0) ==> abs(n) - y < abs(n)`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONG_NEG) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_SYM) THEN
  DISCH_THEN(MP_TAC o CONJ (SPEC `abs n` CONG_SELF)) THEN
  REWRITE_TAC[CONG_MOD_ABS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_ADD) THEN
  REWRITE_TAC[INT_NEG_NEG; INT_ADD_LID] THEN
  MESON_TAC[INT_ARITH `x + --y = x - y`; CONG_SYM]);;

let CONG_REP_MIN = prove
 (`!n x. ~(n = &0)
         ==> ?y. --(abs n) <= &2 * y /\ &2 * y < abs n /\ (x == y) (mod n)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CONG_REP_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:int` STRIP_ASSUME_TAC o SPEC `x:int`) THEN
  MP_TAC(INT_ARITH
   `&0 <= y /\ y < abs n
    ==> --(abs n) <= &2 * y /\ &2 * y < abs(n) \/
        --(abs n) <= &2 * (y - abs(n)) /\ &2 * (y - abs(n)) < abs(n)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[CONG_REP_POS; INT_LT_IMP_LE]; ALL_TAC] THEN
  EXISTS_TAC `y - abs(n)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `n:int` CONG_SELF_ABS) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_SYM) THEN
  UNDISCH_TAC `(x == y) (mod n)` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_SUB) THEN
  REWRITE_TAC[INT_ARITH `x - &0 = x`]);;

let CONG_REP_MIN_ABS = prove
 (`!n x. ~(n = &0) ==> ?y. &2 * abs(y) <= abs(n) /\ (x == y) (mod n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONG_REP_MIN) THEN
  DISCH_THEN(MP_TAC o SPEC `x:int`) THEN MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[] THEN INT_ARITH_TAC);;
