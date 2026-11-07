(* ========================================================================= *)
(* Gaussian integers and the theorem of Lebesgue (1850).                     *)
(*                                                                           *)
(* Purpose: x^m = y^2 + 1 has no solution in natural numbers with m >= 2 and *)
(* y >= 1. Route: Gaussian integers as complex numbers with integer          *)
(* coordinates; they are the ring imag_quadratic_integers 1 of Q(i)          *)
(* (IMAG_QUADRATIC_INTEGERS_GAUSSIAN), Euclidean for the norm, hence a PID   *)
(* and a UFD (Baker/quadint_ring.ml); so Euclidean division, Bezout,         *)
(* irreducible elements are prime, and coprime factors of a p-th power are   *)
(* p-th powers (p odd; UFD_COPRIME_MUL_POW, the units are p-th powers); then *)
(* the classical argument: y + ii = a^p, Im a = +-1, and a 2-adic            *)
(* contradiction in the binomial expansion of Re((1 + ii c)^p).              *)
(*                                                                           *)
(* Main results: LEBESGUE, GAUSSIAN_INTEGER_CLOSED, GAUSSIAN_EUCLIDEAN,      *)
(* GAUSSIAN_BEZOUT, GAUSSIAN_IRREDUCIBLE_IMP_PRIME, GAUSSIAN_COPRIME_POW,    *)
(* IMAG_QUADRATIC_INTEGERS_GAUSSIAN.                                         *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (COMPLEX_BINOMIAL_THEOREM); Baker/quadint_defs.ml   *)
(* (imag_quadratic_integers, quad_omega), Baker/quadint_ring.ml              *)
(* (IMAG_QUADRATIC_INTEGERS_CARRIER, _NORM_EUCLIDEAN, _PID, _UFD, _UNIT,     *)
(* _DIVIDES, _CLOSED, _CX), Baker/quadint_ant.ml                             *)
(* (IMAG_QUADRATIC_INTEGERS_CLAUSES, _SUB_POW); ANT/ufd.ml                   *)
(* (UFD_COPRIME_MUL_POW); Library/ringtheory.ml (BEZOUT_RING_IMP_BEZOUT,     *)
(* BEZOUT_RING_COPRIME, PID_IMP_BEZOUT_RING, UFD_IRREDUCIBLE_EQ_PRIME).      *)
(* ========================================================================= *)

needs "ANT/ufd.ml";;
needs "Baker/quadint_ring.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The Gaussian integers and their closure properties.                       *)
(* ------------------------------------------------------------------------- *)

let gaussian_integer = new_definition
 `gaussian_integer (z:complex) <=> integer(Re z) /\ integer(Im z)`;;

let GAUSSIAN_INTEGER_CX = prove
 (`!x. gaussian_integer(Cx x) <=> integer x`,
  REWRITE_TAC[gaussian_integer; RE_CX; IM_CX; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_II = prove
 (`gaussian_integer ii`,
  REWRITE_TAC[gaussian_integer; RE_II; IM_II; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_ADD = prove
 (`!z w. gaussian_integer z /\ gaussian_integer w
         ==> gaussian_integer(z + w)`,
  SIMP_TAC[gaussian_integer; RE_ADD; IM_ADD; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_SUB = prove
 (`!z w. gaussian_integer z /\ gaussian_integer w
         ==> gaussian_integer(z - w)`,
  SIMP_TAC[gaussian_integer; RE_SUB; IM_SUB; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_MUL = prove
 (`!z w. gaussian_integer z /\ gaussian_integer w
         ==> gaussian_integer(z * w)`,
  SIMP_TAC[gaussian_integer; complex_mul; RE; IM; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_NEG = prove
 (`!z. gaussian_integer z ==> gaussian_integer(--z)`,
  SIMP_TAC[gaussian_integer; RE_NEG; IM_NEG; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_CNJ = prove
 (`!z. gaussian_integer z ==> gaussian_integer(cnj z)`,
  SIMP_TAC[gaussian_integer; RE_CNJ; IM_CNJ; INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_POW = prove
 (`!z n. gaussian_integer z ==> gaussian_integer(z pow n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[complex_pow; GAUSSIAN_INTEGER_MUL; GAUSSIAN_INTEGER_CX;
               INTEGER_CLOSED]);;

let GAUSSIAN_INTEGER_CLOSED = prove
 (`(!x. integer x ==> gaussian_integer(Cx x)) /\ gaussian_integer ii /\
   (!z w. gaussian_integer z /\ gaussian_integer w
          ==> gaussian_integer(z + w) /\ gaussian_integer(z - w) /\
              gaussian_integer(z * w)) /\
   (!z. gaussian_integer z ==> gaussian_integer(--z) /\
                               gaussian_integer(cnj z)) /\
   (!z n. gaussian_integer z ==> gaussian_integer(z pow n))`,
  SIMP_TAC[GAUSSIAN_INTEGER_CX; GAUSSIAN_INTEGER_II; GAUSSIAN_INTEGER_ADD;
           GAUSSIAN_INTEGER_SUB; GAUSSIAN_INTEGER_MUL; GAUSSIAN_INTEGER_NEG;
           GAUSSIAN_INTEGER_CNJ; GAUSSIAN_INTEGER_POW]);;

let GAUSSIAN_INTEGER_NUM = prove
 (`!n. gaussian_integer(Cx(&n))`,
  REWRITE_TAC[GAUSSIAN_INTEGER_CX; INTEGER_CLOSED]);;

(* A closure tactic: proves gaussian_integer t (or integer t) for terms t    *)
(* built by ring operations from atoms that are gaussian_integer (integer)   *)
(* by assumption, by structural decomposition (MATCH_MP_TAC with the         *)
(* closure rules); equations among the assumptions are never used.           *)

let GAUSSIAN_INTEGER_TAC : tactic =
  let ics = CONJUNCTS INTEGER_CLOSED in
  let axs = [GAUSSIAN_INTEGER_II; GAUSSIAN_INTEGER_NUM; hd ics]
  and imps = [GAUSSIAN_INTEGER_ADD; GAUSSIAN_INTEGER_SUB; GAUSSIAN_INTEGER_MUL;
              GAUSSIAN_INTEGER_NEG; GAUSSIAN_INTEGER_CNJ; GAUSSIAN_INTEGER_POW;
              GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL GAUSSIAN_INTEGER_CX)))] @
             tl ics in
  REPEAT(CONJ_TAC ORELSE FIRST_ASSUM ACCEPT_TAC ORELSE
         FIRST(map MATCH_ACCEPT_TAC axs) ORELSE FIRST(map MATCH_MP_TAC imps));;

(* ------------------------------------------------------------------------- *)
(* The norm: its square is a natural number, nonzero ones have norm >= 1.    *)
(* ------------------------------------------------------------------------- *)

let GAUSSIAN_INTEGER_NORM_POW_2 = prove
 (`!z. gaussian_integer z ==> ?n. norm z pow 2 = &n`,
  REWRITE_TAC[gaussian_integer] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_SQNORM] THEN
  MATCH_MP_TAC(MESON[INTEGER_POS] `&0 <= x /\ integer x ==> ?n. x = &n`) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_LE_ADD; REAL_LE_POW_2]);;

let GAUSSIAN_INTEGER_NORM_GE_1 = prove
 (`!z. gaussian_integer z /\ ~(z = Cx(&0)) ==> &1 <= norm z`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o
    MATCH_MP GAUSSIAN_INTEGER_NORM_POW_2) THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[NORM_POS_LE; ARITH_EQ; REAL_POW_ONE] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `norm(z:complex) pow 2 = &0` THEN
  ASM_REWRITE_TAC[REAL_POW_EQ_0; COMPLEX_NORM_ZERO] THEN ARITH_TAC);;

let GAUSSIAN_INTEGER_NORM_LT_1 = prove
 (`!z. gaussian_integer z /\ norm z < &1 ==> z = Cx(&0)`,
  MESON_TAC[GAUSSIAN_INTEGER_NORM_GE_1; REAL_NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* The Gaussian integers are the ring of integers of Q(i), the ring          *)
(* imag_quadratic_integers 1 of Baker/quadint_defs.ml; Euclidean division,   *)
(* Bezout and irreducible elements are prime from the Euclidean ring of      *)
(* Baker/quadint_ring.ml and the library (a PID, hence a Bezout ring and a   *)
(* UFD).                                                                     *)
(* ------------------------------------------------------------------------- *)

let IMAG_QUADRATIC_INTEGERS_GAUSSIAN = prove
 (`!z. z IN ring_carrier(imag_quadratic_integers 1) <=> gaussian_integer z`,
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CARRIER; SQUAREFREE_1] THEN
  REWRITE_TAC[quad_omega; gaussian_integer; IN_ELIM_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SQRT_1; COMPLEX_MUL_RID] THEN
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX; IM_MUL_CX;
                    RE_II; IM_II; REAL_MUL_RZERO; REAL_ADD_RID;
                    REAL_ADD_LID; REAL_MUL_RID];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Re z`; `Im z`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_CX;
                IM_MUL_CX; RE_II; IM_II] THEN REAL_ARITH_TAC]);;

let GAUSSIAN_EUCLIDEAN = prove
 (`!a b. gaussian_integer a /\ gaussian_integer b /\ ~(b = Cx(&0))
         ==> ?q. gaussian_integer q /\ norm(a - q * b) < norm b`,
  REWRITE_TAC[GSYM IMAG_QUADRATIC_INTEGERS_GAUSSIAN] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_NORM_EUCLIDEAN THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let GAUSSIAN_BEZOUT = prove
 (`!a b. gaussian_integer a /\ gaussian_integer b
         ==> ?g s t. gaussian_integer g /\ gaussian_integer s /\
                     gaussian_integer t /\ g = s * a + t * b /\
                     (?k1. gaussian_integer k1 /\ a = g * k1) /\
                     (?k2. gaussian_integer k2 /\ b = g * k2)`,
  REWRITE_TAC[GSYM IMAG_QUADRATIC_INTEGERS_GAUSSIAN] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`imag_quadratic_integers 1`; `a:complex`; `b:complex`]
    BEZOUT_RING_IMP_BEZOUT) THEN
  ASM_SIMP_TAC[PID_IMP_BEZOUT_RING; IMAG_QUADRATIC_INTEGERS_PID; IN_INSERT;
               IMAG_QUADRATIC_INTEGERS_DIVIDES;
               IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:complex`
     (X_CHOOSE_THEN `y:complex` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`x:complex`; `y:complex`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a * x + b * y = g:complex` THEN CONV_TAC COMPLEX_RING);;

let GAUSSIAN_IRREDUCIBLE_IMP_PRIME = prove
 (`!q. gaussian_integer q /\
       (!d k. gaussian_integer d /\ gaussian_integer k /\ q = d * k
              ==> norm d = &1 \/ norm k = &1)
       ==> !x y. gaussian_integer x /\ gaussian_integer y /\
                 (?m. gaussian_integer m /\ x * y = q * m)
                 ==> (?m. gaussian_integer m /\ x = q * m) \/
                     (?m. gaussian_integer m /\ y = q * m)`,
  REWRITE_TAC[GSYM IMAG_QUADRATIC_INTEGERS_GAUSSIAN] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `norm(q:complex) = &1` THENL
   [REPEAT STRIP_TAC THEN DISJ1_TAC THEN EXISTS_TAC `cnj q * x` THEN
    ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CLOSED] THEN
    MP_TAC(SPEC `q:complex` COMPLEX_MUL_CNJ) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_prime (imag_quadratic_integers 1) q` MP_TAC THENL
   [SIMP_TAC[GSYM UFD_IRREDUCIBLE_EQ_PRIME; IMAG_QUADRATIC_INTEGERS_UFD;
             IN_INSERT] THEN
    ASM_REWRITE_TAC[ring_irreducible; IMAG_QUADRATIC_INTEGERS_CLAUSES;
                    IMAG_QUADRATIC_INTEGERS_UNIT] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`Cx(&0)`; `Cx(&0)`]) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_NORM_0; INTEGER_CLOSED;
                    IMAG_QUADRATIC_INTEGERS_CX] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[ring_prime; IMAG_QUADRATIC_INTEGERS_CLAUSES;
                IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:complex`; `y:complex`]) THEN
    ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CLOSED] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Units are p-th powers for odd p; coprime factors of a p-th power are      *)
(* p-th powers (UFD_COPRIME_MUL_POW in the UFD imag_quadratic_integers 1).   *)
(* ------------------------------------------------------------------------- *)

let GAUSSIAN_UNIT_RING = prove
 (`!x y. x * y = &0 /\ x pow 2 + y pow 2 = &1
         ==> (Cx x + ii * Cx y) pow 4 = Cx(&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CX_INJ; CX_MUL; CX_ADD; CX_POW] THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING);;

let GAUSSIAN_UNIT_POW_4 = prove
 (`!u. gaussian_integer u /\ norm u = &1 ==> u pow 4 = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[gaussian_integer] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Re u pow 2 + Im u pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM COMPLEX_SQNORM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Re u * Im u = &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE] THEN
    MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    MP_TAC(SPEC `Re u` REAL_ABS_INTEGER_LEMMA) THEN
    MP_TAC(SPEC `Im u` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `&1`; `abs(Re u)`] REAL_POW_LE2) THEN
    MP_TAC(SPECL [`2`; `&1`; `abs(Im u)`] REAL_POW_LE2) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_POW2_ABS; REAL_POW_ONE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(SPEC `u:complex` COMPLEX_EXPAND) THEN
  MATCH_MP_TAC GAUSSIAN_UNIT_RING THEN ASM_REWRITE_TAC[]);;

let GAUSSIAN_UNIT_POW = prove
 (`!p u. ODD p /\ gaussian_integer u /\ norm u = &1
         ==> ?a. gaussian_integer a /\ u = a pow p`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `(u:complex) pow p` THEN
  ASM_SIMP_TAC[GAUSSIAN_INTEGER_POW; COMPLEX_POW_POW] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST1_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  SUBGOAL_THEN `SUC(2 * k) * SUC(2 * k) = 4 * (k * k + k) + 1` SUBST1_TAC
  THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_POW_ADD; GSYM COMPLEX_POW_POW; GAUSSIAN_UNIT_POW_4;
               COMPLEX_POW_ONE; COMPLEX_POW_1; COMPLEX_MUL_LID]);;

let GAUSSIAN_COPRIME_POW = prove
 (`!p u v w. ODD p /\ gaussian_integer u /\ gaussian_integer v /\
             gaussian_integer w /\
             (?s t. gaussian_integer s /\ gaussian_integer t /\
                    s * u + t * v = Cx(&1)) /\
             u * v = w pow p
             ==> ?a. gaussian_integer a /\ u = a pow p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`imag_quadratic_integers 1`; `u:complex`; `v:complex`;
                 `w:complex`; `p:num`] UFD_COPRIME_MUL_POW) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM IMAG_QUADRATIC_INTEGERS_GAUSSIAN]) THEN
  ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_UFD; IN_INSERT; BEZOUT_RING_COPRIME;
               PID_IMP_BEZOUT_RING; IMAG_QUADRATIC_INTEGERS_PID;
               IMAG_QUADRATIC_INTEGERS_CLAUSES;
               IMAG_QUADRATIC_INTEGERS_SUB_POW] THEN
  ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`s:complex`; `t:complex`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s * u + t * v = Cx(&1)` THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMAG_QUADRATIC_INTEGERS_UNIT]] THEN
  MAP_EVERY X_GEN_TAC [`e:complex`; `c:complex`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `e:complex`] GAUSSIAN_UNIT_POW) THEN
  ASM_REWRITE_TAC[GSYM IMAG_QUADRATIC_INTEGERS_GAUSSIAN] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a * c:complex` THEN
  ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CLOSED; COMPLEX_POW_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Lebesgue: the elementary reductions.                                      *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_SQUARE = prove
 (`!X y. 1 <= y ==> ~(X EXP 2 = y EXP 2 + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y EXP 2 < X EXP 2 /\ X EXP 2 < (y + 1) EXP 2` MP_TAC THENL
   [UNDISCH_TAC `X EXP 2 = y EXP 2 + 1` THEN UNDISCH_TAC `1 <= y` THEN
    REWRITE_TAC[EXP_2] THEN ARITH_TAC;
    REWRITE_TAC[EXP_MONO_LT] THEN ARITH_TAC]);;

let LEBESGUE_Y_EVEN = prove
 (`!p x y. 2 <= p /\ x EXP p = y EXP 2 + 1 ==> EVEN y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_ODD; ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `EVEN x` MP_TAC THENL
   [SUBGOAL_THEN `EVEN(x EXP p)` MP_TAC THENL
     [UNDISCH_TAC `x EXP p = SUC(2 * k) EXP 2 + 1` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[EVEN_ADD; EVEN_EXP; EVEN; EVEN_MULT; ARITH];
      REWRITE_TAC[EVEN_EXP] THEN MESON_TAC[]];
    REWRITE_TAC[EVEN_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)] THEN
  SUBGOAL_THEN `4 divides (2 * j) EXP p` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `(2 * j) EXP 2` THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE_IMP] THEN
    REWRITE_TAC[EXP_2] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `SUC(2 * k) EXP 2 + 1 = 4 * (k * k + k) + 2`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `4 divides 2` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `4 * (k * k + k)` THEN
    CONJ_TAC THENL [CONV_TAC NUMBER_RULE; FIRST_ASSUM ACCEPT_TAC];
    CONV_TAC(LAND_CONV DIVIDES_CONV) THEN REWRITE_TAC[]]);;

let LEBESGUE_GAUSSIAN_DESCENT = prove
 (`!p x y. ODD p /\ EVEN y /\ x EXP p = y EXP 2 + 1
           ==> ?a. gaussian_integer a /\ Cx(&y) + ii = a pow p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    REWRITE_RULE[EVEN_EXISTS]) THEN
  MATCH_MP_TAC GAUSSIAN_COPRIME_POW THEN
  MAP_EVERY EXISTS_TAC [`Cx(&(2 * j)) - ii`; `Cx(&x)`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[GAUSSIAN_INTEGER_ADD; GAUSSIAN_INTEGER_NUM; GAUSSIAN_INTEGER_II];
    SIMP_TAC[GAUSSIAN_INTEGER_SUB; GAUSSIAN_INTEGER_NUM; GAUSSIAN_INTEGER_II];
    REWRITE_TAC[GAUSSIAN_INTEGER_NUM];
    MAP_EVERY EXISTS_TAC
     [`Cx(&(2 * j)) - ii + ii * Cx(&2 * &j pow 2)`;
      `--(ii * Cx(&2 * &j pow 2))`] THEN
    REPEAT CONJ_TAC THENL
     [GAUSSIAN_INTEGER_TAC; GAUSSIAN_INTEGER_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL; CX_POW] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[GSYM CX_POW; REAL_OF_NUM_POW] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_ADD; CX_ADD; CX_POW] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING]);;

let GAUSSIAN_POW_SUB_FACTOR = prove
 (`!a b n. gaussian_integer a /\ gaussian_integer b
           ==> ?g. gaussian_integer g /\ a pow n - b pow n = (a - b) * g`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `Cx(&0)` THEN REWRITE_TAC[GAUSSIAN_INTEGER_NUM; complex_pow] THEN
    CONV_TAC COMPLEX_RING;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a * g + (b:complex) pow n` THEN CONJ_TAC THENL
     [GAUSSIAN_INTEGER_TAC;
      REWRITE_TAC[complex_pow] THEN
      UNDISCH_TAC `a pow n - b pow n = (a - b) * g:complex` THEN
      CONV_TAC COMPLEX_RING]]);;

let LEBESGUE_IM_UNIT = prove
 (`!a p y. gaussian_integer a /\ a pow p = Cx(&y) + ii ==> abs(Im a) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:complex`; `Cx(Re a)`; `p:num`] GAUSSIAN_POW_SUB_FACTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GAUSSIAN_INTEGER_CX] THEN
    ASM_MESON_TAC[gaussian_integer];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `a - Cx(Re a) = ii * Cx(Im a)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_CX; IM_CX; RE_MUL_II;
                IM_MUL_II] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Im a * Re g = &1` MP_TAC THENL
   [UNDISCH_TAC `a pow p - Cx(Re a) pow p = (a - Cx(Re a)) * g` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[GSYM CX_POW; IM_SUB; IM_ADD; IM_CX; IM_II;
                GSYM COMPLEX_MUL_ASSOC; IM_MUL_II; RE_MUL_CX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`Im a`; `Re g`] INTEGER_ABS_MUL_EQ_1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[gaussian_integer]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM] THEN MESON_TAC[]);;

let LEBESGUE_NORM = prove
 (`!a p x y. ~(p = 0) /\ a pow p = Cx(&y) + ii /\ x EXP p = y EXP 2 + 1
             ==> norm a pow 2 = &x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `p:num` THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN
  SUBGOAL_THEN `(norm(a:complex) pow 2) pow p = norm(a pow p) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_POW; REAL_POW_POW] THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_II;
                  IM_II; REAL_OF_NUM_POW] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
  REAL_ARITH_TAC);;

let LEBESGUE_POW_ODD_UNIT = prove
 (`!b h. b pow 2 = &1
         ==> (ii * Cx b) pow (2 * h + 1) = Cx((-- &1) pow h * b) * ii`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(ii * Cx b) pow 2 = Cx(-- &1)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_II_2; GSYM CX_POW] THEN
    ASM_REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_POW_ADD; GSYM COMPLEX_POW_POW; COMPLEX_POW_1;
                  CX_MUL; CX_POW] THEN
  CONV_TAC COMPLEX_RING);;

let LEBESGUE_REDUCE = prove
 (`!A B h. B pow 2 = &1 /\ Im((Cx A + ii * Cx B) pow (2 * h + 1)) = &1
           ==> Re((Cx(&1) + ii * Cx(--B * A)) pow (2 * h + 1)) = &1 \/
               Re((Cx(&1) + ii * Cx(--B * A)) pow (2 * h + 1)) = -- &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `Cx A + ii * Cx B = (ii * Cx B) * (Cx(&1) + ii * Cx(--B * A))`
  MP_TAC THENL
   [MP_TAC COMPLEX_POW_II_2 THEN UNDISCH_TAC `(B:real) pow 2 = &1` THEN
    REWRITE_TAC[GSYM CX_INJ; CX_POW; CX_MUL; CX_NEG] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `Im((Cx A + ii * Cx B) pow (2 * h + 1)) = &1` THEN
    SUBST1_TAC th) THEN
  ONCE_REWRITE_TAC[COMPLEX_POW_MUL] THEN
  ASM_SIMP_TAC[LEBESGUE_POW_ODD_UNIT] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; IM_MUL_CX; IM_MUL_II] THEN
  SPEC_TAC(`Re((Cx(&1) + ii * Cx(--B * A)) pow (2 * h + 1))`,`r:real`) THEN
  GEN_TAC THEN
  SUBGOAL_THEN `((-- &1) pow h) pow 2 = &1` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ONE];
    ALL_TAC] THEN
  UNDISCH_TAC `(B:real) pow 2 = &1` THEN
  SPEC_TAC(`(-- &1) pow h`,`e1:real`) THEN GEN_TAC THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The real part of (1 + ii c)^(2h+1) by the binomial theorem.               *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_II_POW = prove
 (`!c l. (ii * Cx c) pow (2 * l) = Cx((-- &1) pow l * c pow (2 * l)) /\
         (ii * Cx c) pow (2 * l + 1) =
         ii * Cx((-- &1) pow l * c pow (2 * l + 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_POW_1; COMPLEX_POW_MUL;
              GSYM COMPLEX_POW_POW; COMPLEX_POW_II_2; CX_MUL; CX_POW;
              CX_NEG] THEN
  CONV_TAC COMPLEX_RING);;

let LEBESGUE_RE_BINOMIAL = prove
 (`!h c. Re((Cx(&1) + ii * Cx c) pow (2 * h + 1)) =
         sum(0..h) (\l. (-- &1) pow l * &(binom(2 * h + 1,2 * l)) *
                        c pow (2 * l))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  REWRITE_TAC[COMPLEX_BINOMIAL_THEOREM; COMPLEX_POW_ONE; COMPLEX_MUL_RID] THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL [`\k. Re(Cx(&(binom(2 * h + 1,k))) * (ii * Cx c) pow k)`;
                 `0`; `h:num`] SUM_PAIR) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REWRITE_TAC[LEBESGUE_II_POW; RE_MUL_CX; RE_CX; RE_MUL_II; IM_CX] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 2-adic argument: for c even and non-zero the alternating sum          *)
(* sum_l (-1)^l C(2h+1,2l) c^(2l) is not +-1 (h >= 1).                       *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_SUM_SPLIT = prove
 (`!h n r. sum(0..h) (\l. (-- &1) pow l * &(binom(2 * h + 1,2 * l)) *
                          &n pow (2 * l)) = r
           ==> &(nsum(1..h) (\l. if EVEN l then 0
                                 else binom(2 * h + 1,2 * l) * n EXP (2 * l))) +
               r =
               &(nsum(1..h) (\l. if EVEN l
                                 then binom(2 * h + 1,2 * l) * n EXP (2 * l)
                                 else 0)) + &1`,
  REPEAT GEN_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; binom; real_pow; REAL_MUL_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `s = b - a ==> a + &1 + s = b + &1:real`) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  REAL_ARITH_TAC);;

let LEBESGUE_BINOM_2 = prove
 (`!l. binom(2 * l,2) = l * (2 * l - 1)`,
  GEN_TAC THEN MP_TAC(SPECL [`2 * l`; `1`] BINOM_BOTTOM_STEP) THEN
  REWRITE_TAC[BINOM_1; ARITH_RULE `1 + 1 = 2`] THEN ARITH_TAC);;

let LEBESGUE_INDEX2_MUL = prove
 (`!m n. ~(m = 0) /\ ~(n = 0) ==> index 2 (m * n) = index 2 m + index 2 n`,
  SIMP_TAC[INDEX_MUL; PRIME_2]);;

let LEBESGUE_2ADIC_TERM = prove
 (`!h n l. EVEN n /\ ~(n = 0) /\ 2 <= l /\ l <= h
           ==> 2 EXP (index 2 (binom(2 * h + 1,2) * n EXP 2) + 1) divides
               binom(2 * h + 1,2 * l) * n EXP (2 * l)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `p = 2 * h + 1` THEN
  SUBGOAL_THEN
   `~(binom(p,2 * l) = 0) /\ ~(binom(p,2) = 0) /\
    ~(binom(p - 2,2 * l - 2) = 0) /\ ~(l = 0) /\ ~(2 * l - 1 = 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BINOM_EQ_0] THEN EXPAND_TAC "p" THEN
    MAP_EVERY UNDISCH_TAC [`2 <= l`; `l <= h`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `index 2 (2 * l - 1) = 0` ASSUME_TAC THENL
   [MATCH_MP_TAC INDEX_ZERO THEN
    REWRITE_TAC[DIVIDES_2; EVEN_SUB; EVEN_MULT; ARITH] THEN
    UNDISCH_TAC `2 <= l` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `index 2 l < l` ASSUME_TAC THENL
   [MATCH_MP_TAC INDEX_LT THEN ASM_REWRITE_TAC[LT_POW2_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= index 2 n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `2`; `1`] PRIMEPOW_DIVIDES_INDEX) THEN
    ASM_REWRITE_TAC[EXP_1; DIVIDES_2; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(2 * l - 2) * index 2 n + 2 * index 2 n = (2 * l) * index 2 n /\
    2 * l - 2 <= (2 * l - 2) * index 2 n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `2 <= l` THEN ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(binom(p,2 * l) * n EXP (2 * l)) * (l * (2 * l - 1)) =
    (binom(p,2) * n EXP 2) * (binom(p - 2,2 * l - 2) * n EXP (2 * l - 2))`
  MP_TAC THENL
   [MP_TAC(SPECL [`2 * l`; `p:num`; `2`] BINOM_MUL_SHIFT) THEN
    ANTS_TAC THENL [UNDISCH_TAC `2 <= l` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEBESGUE_BINOM_2] THEN DISCH_TAC THEN
    SUBGOAL_THEN `n EXP (2 * l) = n EXP 2 * n EXP (2 * l - 2)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `2 <= l` THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(binom(p,2 * l) * (l * (2 * l - 1))) *
                (n EXP 2 * n EXP (2 * l - 2))` THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_AC]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[MULT_AC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `index 2`) THEN
  REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; ARITH_EQ] THEN
  ASM_SIMP_TAC[LEBESGUE_INDEX2_MUL; INDEX_EXP; PRIME_2; MULT_EQ_0;
               EXP_EQ_0] THEN
  MAP_EVERY UNDISCH_TAC
   [`index 2 l < l`; `2 <= l`;
    `(2 * l - 2) * index 2 n + 2 * index 2 n = (2 * l) * index 2 n`;
    `2 * l - 2 <= (2 * l - 2) * index 2 n`] THEN
  ARITH_TAC);;

let LEBESGUE_DIVIDES_LEMMA = prove
 (`!a r b d k. 2 <= k /\ 2 EXP k divides a /\ ~(2 EXP (k + 1) divides a) /\
               2 EXP (k + 1) divides r /\ 2 EXP (k + 1) divides b /\
               (d = 0 \/ d = 2)
               ==> ~(a + r = b + d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_TAC THENL
   [UNDISCH_TAC `~(2 EXP (k + 1) divides a)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_ADD_REVL THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `4 divides 2 EXP k /\ 4 divides 2 EXP (k + 1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 EXP 2`] THEN CONJ_TAC THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `4 divides 2` MP_TAC THENL
     [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `b:num` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[DIVIDES_TRANS]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      MATCH_MP_TAC DIVIDES_ADD THEN ASM_MESON_TAC[DIVIDES_TRANS];
      CONV_TAC(LAND_CONV DIVIDES_CONV) THEN REWRITE_TAC[]]]);;

let LEBESGUE_2ADIC = prove
 (`!h n d. 1 <= h /\ EVEN n /\ ~(n = 0) /\ (d = 0 \/ d = 2)
           ==> ~(nsum(1..h) (\l. if EVEN l then 0
                                 else binom(2 * h + 1,2 * l) * n EXP (2 * l)) =
                 nsum(1..h) (\l. if EVEN l
                                 then binom(2 * h + 1,2 * l) * n EXP (2 * l)
                                 else 0) + d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  ABBREV_TAC `M = index 2 (binom(2 * h + 1,2) * n EXP 2)` THEN
  SUBGOAL_THEN `~(binom(2 * h + 1,2) * n EXP 2 = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; BINOM_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 EXP (M + 1) divides binom(2 * h + 1,2) * n EXP 2)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 divides binom(2 * h + 1,2) * n EXP 2` ASSUME_TAC THENL
   [UNDISCH_TAC `EVEN n` THEN REWRITE_TAC[EVEN_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
    REWRITE_TAC[EXP_2] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= M` ASSUME_TAC THENL
   [MP_TAC(SPECL [`binom(2 * h + 1,2) * n EXP 2`; `2`; `2`]
      PRIMEPOW_DIVIDES_INDEX) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN 2..h
        ==> 2 EXP (M + 1) divides binom(2 * h + 1,2 * l) * n EXP (2 * l)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN
    MATCH_MP_TAC LEBESGUE_2ADIC_TERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum(1..h) (\l. if EVEN l then 0
                    else binom(2 * h + 1,2 * l) * n EXP (2 * l)) =
    binom(2 * h + 1,2) * n EXP 2 +
    nsum(2..h) (\l. if EVEN l then 0
                    else binom(2 * h + 1,2 * l) * n EXP (2 * l))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[NSUM_CLAUSES_LEFT] THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  MATCH_MP_TAC LEBESGUE_DIVIDES_LEMMA THEN EXISTS_TAC `M:num` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[EXP_INDEX_DIVIDES];
    MATCH_MP_TAC DIVIDES_NSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[DIVIDES_0];
    MATCH_MP_TAC DIVIDES_NSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[DIVIDES_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `~(l = 1)` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `EVEN 1` THEN
      REWRITE_TAC[ARITH];
      UNDISCH_TAC `l IN 1..h` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]]);;

let LEBESGUE_BINOMIAL_SUM = prove
 (`!h n. 1 <= h /\ EVEN n /\ ~(n = 0)
         ==> ~(sum(0..h) (\l. (-- &1) pow l * &(binom(2 * h + 1,2 * l)) *
                              &n pow (2 * l)) = &1) /\
             ~(sum(0..h) (\l. (-- &1) pow l * &(binom(2 * h + 1,2 * l)) *
                              &n pow (2 * l)) = -- &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LEBESGUE_SUM_SPLIT) THENL
   [MP_TAC(SPECL [`h:num`; `n:num`; `0`] LEBESGUE_2ADIC);
    MP_TAC(SPECL [`h:num`; `n:num`; `2`] LEBESGUE_2ADIC)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lebesgue for odd prime exponents, then for all exponents m >= 2.          *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_PRIME = prove
 (`!p x y. prime p /\ ODD p /\ 1 <= y ==> ~(x EXP p = y EXP 2 + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `ODD 2` THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS; ADD1] o check (fun th -> concl th = `ODD p`)) THEN
  SUBGOAL_THEN `1 <= h` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EVEN y` ASSUME_TAC THENL
   [MATCH_MP_TAC LEBESGUE_Y_EVEN THEN
    MAP_EVERY EXISTS_TAC [`2 * h + 1`; `x:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD x` ASSUME_TAC THENL
   [SUBGOAL_THEN `ODD(x EXP (2 * h + 1))` MP_TAC THENL
     [UNDISCH_TAC `x EXP (2 * h + 1) = y EXP 2 + 1` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ODD_ADD; ODD_EXP; ARITH; NOT_ODD] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ODD_EXP; ADD_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`2 * h + 1`; `x:num`; `y:num`] LEBESGUE_GAUSSIAN_DESCENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `abs(Im a) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC LEBESGUE_IM_UNIT THEN
    MAP_EVERY EXISTS_TAC [`2 * h + 1`; `y:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a:complex) pow 2 = &x` ASSUME_TAC THENL
   [MATCH_MP_TAC LEBESGUE_NORM THEN
    MAP_EVERY EXISTS_TAC [`2 * h + 1`; `y:num`] THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. abs(Re a) = &m` (X_CHOOSE_TAC `m:num`) THENL
   [ASM_MESON_TAC[gaussian_integer; integer]; ALL_TAC] THEN
  SUBGOAL_THEN `x = m EXP 2 + 1` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(a:complex) pow 2 = &x` THEN
    REWRITE_TAC[COMPLEX_SQNORM] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; EXP_ONE; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN m /\ ~(m = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ODD x` THEN ASM_REWRITE_TAC[ODD_ADD; ODD_EXP; ARITH] THEN
      REWRITE_TAC[NOT_ODD];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `x EXP (2 * h + 1) = y EXP 2 + 1` THEN
      ASM_REWRITE_TAC[ARITH; EXP_ONE; ARITH_RULE `1 = n + 1 <=> n = 0`;
                      EXP_EQ_0] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`Re a`; `Im a`; `h:num`] LEBESGUE_REDUCE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM COMPLEX_EXPAND] THEN
      ASM_REWRITE_TAC[IM_ADD; IM_CX; IM_II] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEBESGUE_RE_BINOMIAL] THEN
  SUBGOAL_THEN `!l. (--(Im a) * Re a) pow (2 * l) = &m pow (2 * l)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `m:num`] LEBESGUE_BINOMIAL_SUM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let LEBESGUE = prove
 (`!m x y. 2 <= m /\ 1 <= y ==> ~(x EXP m = y EXP 2 + 1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `EVEN m` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
      REWRITE_RULE[EVEN_EXISTS]) THEN
    MP_TAC(SPECL [`x EXP k`; `y:num`] LEBESGUE_SQUARE) THEN
    ASM_REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` PRIME_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [UNDISCH_TAC `~EVEN(p * q)` THEN REWRITE_TAC[NOT_EVEN; ODD_MULT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `x EXP q`; `y:num`] LEBESGUE_PRIME) THEN
  ASM_REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_REWRITE_TAC[]);;
