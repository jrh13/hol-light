(* ========================================================================= *)
(* Class number one gives a principal ideal domain (the form/ideal           *)
(* dictionary for h = 1).                                                    *)
(*                                                                           *)
(* Purpose: for squarefree d write w = quad_omega d, so that w^2 = t w - n   *)
(* with (t, n) = (1, (d + 1)/4) if d = 3 mod 4 and (0, d) otherwise, and the *)
(* ring of integers of Q(sqrt(-d)) is Z + Z w. A nonzero ideal I contains a  *)
(* positive integer (a N(a) argument); Hermite normal form: with a0 the      *)
(* least positive integer of I and c0 the least positive w-coordinate (of b  *)
(* + c0 w in I), I = Z a0 + Z (b + c0 w), a0 = c0 a, b = c0 b1 and a divides *)
(* N(b1 + w). The norm form N(x a + y (b1 + w))/a = a x^2 + (2 b1 + t) x y + *)
(* m y^2 has discriminant qdisc d; when form_classno (qdisc d) = 1 it        *)
(* represents 1 (the Lagrange reduction QFORM_REDUCE_VALUES gives a reduced  *)
(* form with the same values, primitive since all forms of discriminant      *)
(* qdisc d are primitive, hence the principal form by CLASSNO_FORMS_UNIQUE), *)
(* at (p, r) say; then g = c0 (p a + r (b1 + w)) generates I. Hence the ring *)
(* of integers is a PID (QUAD_CLASSNO_ONE_IMP_PID).                          *)
(*                                                                           *)
(* Main results: QUAD_CLASSNO_ONE_IMP_PID; library-style: QUAD_PID_FORM_ONE  *)
(* (for h = 1 every positive definite form of discriminant qdisc d           *)
(* represents 1), QUAD_PID_PRIMITIVE (for squarefree d all forms of          *)
(* discriminant qdisc d are primitive), QUAD_PID_ABSTRACT (an ideal of Z + Z *)
(* w is principal under the representation property); helper names           *)
(* QUAD_PID_*.                                                               *)
(*                                                                           *)
(* Uses: Baker/quadint_ring.ml (IMAG_QUADRATIC_INTEGERS_CARRIER,             *)
(* QUAD_OMEGA_SQUARE, QUAD_OMEGA_NORM), Baker/quadint_ant.ml                 *)
(* (IMAG_QUADRATIC_INTEGERS_CLAUSES,                                         *)
(* IMAG_QUADRATIC_INTEGERS_INTEGRAL_DOMAIN), Baker/quadint_ufd.ml            *)
(* (QUAD_UFD_PRINCIPAL_FORM), Baker/classno_defs.ml (qform),                 *)
(* Baker/classno_forms.ml (QFORM_REDUCE_VALUES, CLASSNO_FORMS_UNIQUE,        *)
(* QF_PRIMITIVE_SQUAREFREE, CLASSNO_FORMS_MOD4, CLASSNO_PRINCIPAL_REDUCED),  *)
(* Library/ringtheory.ml (PID, principal_ideal,                              *)
(* IDEAL_GENERATED_SING).                                                    *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Baker/quadint_ufd.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Binary quadratic forms of discriminant qdisc d.                           *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_SQUAREFREE_SQUARE = prove
 (`!d g:int. &0 <= g /\ g pow 2 divides &d /\ squarefree d ==> g = &1`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[INT_OF_NUM_POW; GSYM num_divides; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[squarefree] THEN MESON_TAC[]);;

let QUAD_PID_GCD_DISC = prove
 (`!a b c x:int.
        b pow 2 - &4 * a * c = --x ==> gcd(a,gcd(b,c)) pow 2 divides x`,
  INTEGER_TAC);;

let QUAD_PID_ODD_SQUARE_DIVIDES = prove
 (`!g q x:int.
        g = q * &2 + &1 /\ g pow 2 divides &4 * x ==> g pow 2 divides x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `m:int`)) THEN
  EXISTS_TAC `x - (q pow 2 + q) * m:int` THEN
  MAP_EVERY UNDISCH_TAC
   [`&4 * x = g pow 2 * m:int`; `g = q * &2 + &1:int`] THEN
  CONV_TAC INT_RING);;

let QUAD_PID_FORM_EVEN = prove
 (`!d a b c:int.
        b pow 2 - &4 * a * c = --(&4 * &d) /\ squarefree d /\
        &2 divides a /\ &2 divides b /\ &2 divides c
        ==> d MOD 4 = 3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `a1:int`)
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `b1:int`) (X_CHOOSE_TAC `c1:int`))))) THEN
  MATCH_MP_TAC CLASSNO_FORMS_MOD4 THEN EXISTS_TAC `b1:int` THEN
  ASM_REWRITE_TAC[int_divides] THEN EXISTS_TAC `a1 * c1:int` THEN
  UNDISCH_TAC `b pow 2 - &4 * a * c = --(&4 * &d:int)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING);;

(* Every form of discriminant qdisc d (d squarefree) is primitive: for       *)
(* -4 d a common factor 2 of (a,b,c) would give d = 3 mod 4.                 *)

let QUAD_PID_PRIMITIVE = prove
 (`!d a b c:int.
        squarefree d /\ b pow 2 - &4 * a * c = qdisc d
        ==> gcd(a,gcd(b,c)) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qdisc] THEN
  COND_CASES_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `&4 * &d:int`]
    QUAD_PID_GCD_DISC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int`; `gcd(b:int,c)`] int_gcd) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `~((&2:int) divides gcd(a,gcd(b,c)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`d:num`; `a:int`; `b:int`; `c:int`] QUAD_PID_FORM_EVEN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(&2:int) divides gcd(a,gcd(b,c))` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN INTEGER_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `g = gcd(a:int,gcd(b,c))` THEN
  MATCH_MP_TAC QUAD_PID_SQUAREFREE_SQUARE THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g:int`; `&2:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN STRIP_TAC THEN
  MATCH_MP_TAC QUAD_PID_ODD_SQUARE_DIVIDES THEN EXISTS_TAC `g div &2` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN `~(g rem &2 = &0)` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((&2:int) divides g)` THEN
    REWRITE_TAC[int_divides] THEN EXISTS_TAC `g div &2` THEN
    UNDISCH_TAC `g = g div &2 * &2 + g rem &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`g = g div &2 * &2 + g rem &2`; `&0 <= g rem &2`; `g rem &2 < &2`] THEN
  INT_ARITH_TAC);;

(* Class number one: every positive definite form of discriminant qdisc d   *)
(* represents 1.                                                             *)

let QUAD_PID_FORM_ONE = prove
 (`!d a b c:int.
        squarefree d /\ form_classno (qdisc d) = 1 /\
        &0 < a /\ b pow 2 - &4 * a * c = qdisc d
        ==> ?p r. a * p pow 2 + b * p * r + c * r pow 2 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `qdisc d < &0` ASSUME_TAC THENL
   [REWRITE_TAC[qdisc] THEN
    SUBGOAL_THEN `~(d = 0)` MP_TAC THENL
     [ASM_MESON_TAC[SQUAREFREE_0]; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN COND_CASES_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_REDUCE_VALUES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`b pow 2 - &4 * a * c = qdisc d`; `qdisc d < &0`] THEN
    INT_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM qform; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a':int`; `b':int`; `c':int`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> REWRITE_TAC[GSYM th]))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:int` (X_CHOOSE_THEN `n:int`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) o
    MATCH_MP QUAD_UFD_PRINCIPAL_FORM) THEN
  MP_TAC(SPECL [`qdisc d`; `&1:int`; `t:int`; `n:int`;
                `a':int`; `b':int`; `c':int`] CLASSNO_FORMS_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_GCD_1] THEN
    MATCH_MP_TAC QUAD_PID_PRIMITIVE THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM))] THEN
  MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`] THEN REWRITE_TAC[qform] THEN
  INT_ARITH_TAC);;

(* The same over the integer-valued reals.                                   *)

let QUAD_PID_FORM_ONE_REAL = prove
 (`!d a b c.
        squarefree d /\ form_classno (qdisc d) = 1 /\
        integer a /\ integer b /\ integer c /\
        &0 < a /\ b pow 2 - &4 * a * c = real_of_int(qdisc d)
        ==> ?p r. integer p /\ integer r /\
                  a * p pow 2 + b * p * r + c * r pow 2 = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `int_of_real a`; `int_of_real b`; `int_of_real c`]
    QUAD_PID_FORM_ONE) THEN
  REWRITE_TAC[int_lt; int_eq; int_sub_th; int_mul_th; int_pow_th;
              int_add_th; int_of_num_th] THEN
  ASM_SIMP_TAC[REAL_OF_INT_OF_REAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:int` (X_CHOOSE_TAC `r:int`)) THEN
  MAP_EVERY EXISTS_TAC [`real_of_int p`; `real_of_int r`] THEN
  ASM_REWRITE_TAC[INTEGER_REAL_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* The generator w = quad_omega d: w^2 = t w - n, norm(x + y w)^2 =          *)
(* x^2 + t x y + n y^2 and t^2 - 4 n = qdisc d.                              *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_OMEGA_DATA = prove
 (`!d. ?t n. integer t /\ integer n /\
             quad_omega d pow 2 = Cx t * quad_omega d - Cx n /\
             (!x y. norm(Cx x + Cx y * quad_omega d) pow 2 =
                    x pow 2 + t * x * y + n * y pow 2) /\
             t pow 2 - &4 * n = real_of_int(qdisc d)`,
  GEN_TAC THEN REWRITE_TAC[QUAD_OMEGA_SQUARE; QUAD_OMEGA_NORM; qdisc] THEN
  COND_CASES_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&((d + 1) DIV 4)`] THEN
    REWRITE_TAC[INTEGER_CLOSED; COMPLEX_MUL_LID; REAL_MUL_LID] THEN
    MP_TAC(SPEC `d:num` CLASSNO_PRINCIPAL_REDUCED) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[int_eq; int_sub_th; int_mul_th; int_pow_th; int_of_num_th;
                int_neg_th; REAL_MUL_LID];
    MAP_EVERY EXISTS_TAC [`&0`; `&d`] THEN
    REWRITE_TAC[INTEGER_CLOSED; int_neg_th; int_mul_th; int_of_num_th] THEN
    CONJ_TAC THENL [CONV_TAC COMPLEX_RING; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Division with remainder for integer-valued reals; minimal elements.      *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_DIVISION = prove
 (`!m k. integer m /\ integer k /\ &0 < k
         ==> ?q. integer q /\ integer(m - k * q) /\
                 &0 <= m - k * q /\ m - k * q < k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `floor(m / k)` THEN
  MP_TAC(SPEC `m / k` FLOOR) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let QUAD_PID_MIN_DIVIDES = prove
 (`!a0 m. 0 < a0 /\ integer m /\
          (!q k. integer q /\ m - &a0 * q = &k /\ k < a0 ==> k = 0)
          ==> ?q. integer q /\ m = &a0 * q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:real`; `&a0:real`] QUAD_PID_DIVISION) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `m - &a0 * q` NONNEGATIVE_INTEGER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `k = 0` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q:real` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `m - &a0 * q = &0` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Two tactics: discharge a conjunction of hypotheses into labelled          *)
(* assumptions; prove integer(e) for a polynomial e in integer atoms (the    *)
(* simplifier with INTEGER_CLOSED gives up on larger polynomials).          *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_LABELS_TAC (l:string list) : tactic =
  MAP_EVERY (fun s -> DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC s) MP_TAC))
            (butlast l) THEN
  DISCH_THEN(LABEL_TAC (last l));;

let QUAD_PID_INTEGER_TAC : tactic =
  REPEAT CONJ_TAC THEN
  REPEAT(FIRST(map MATCH_MP_TAC (tl(CONJUNCTS INTEGER_CLOSED))) THEN
         REPEAT CONJ_TAC) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED];;

(* ------------------------------------------------------------------------- *)
(* A nonzero ideal of Z + Z w contains a positive integer: z * conj(z).     *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_POSITIVE_INT = prove
 (`!w t n j z.
        integer t /\ integer n /\ w pow 2 = Cx t * w - Cx n /\
        (!x y. norm(Cx x + Cx y * w) pow 2 =
               x pow 2 + t * x * y + n * y pow 2) /\
        (!z. z IN j ==> ?x y. integer x /\ integer y /\ z = Cx x + Cx y * w) /\
        (!x y z. integer x /\ integer y /\ z IN j
                 ==> (Cx x + Cx y * w) * z IN j) /\
        z IN j /\ ~(z = Cx(&0))
        ==> ?N. 0 < N /\ Cx(&N) IN j`,
  REPEAT GEN_TAC THEN
  QUAD_PID_LABELS_TAC
   ["t"; "n"; "wsq"; "norm"; "coord"; "mul"; "zj"; "znz"] THEN
  USE_THEN "coord" (fun th -> USE_THEN "zj" (MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
  SUBGOAL_THEN `Cx(x pow 2 + t * x * y + n * y pow 2) IN j` MP_TAC THENL
   [SUBGOAL_THEN `Cx(x pow 2 + t * x * y + n * y pow 2) =
                  (Cx(x + t * y) + Cx(--y) * w) * (Cx x + Cx y * w)`
    SUBST1_TAC THENL
     [REWRITE_TAC[CX_ADD; CX_MUL; CX_NEG; CX_POW] THEN
      UNDISCH_TAC `w pow 2 = Cx t * w - Cx n` THEN CONV_TAC COMPLEX_RING;
      USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x pow 2 + t * x * y + n * y pow 2` ASSUME_TAC THENL
   [USE_THEN "norm" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[COMPLEX_NORM_NZ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?N. x pow 2 + t * x * y + n * y pow 2 = &N`
  (X_CHOOSE_THEN `N:num` SUBST_ALL_TAC) THENL
   [REWRITE_TAC[GSYM NONNEGATIVE_INTEGER] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN QUAD_PID_INTEGER_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `N:num` THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT]);;

(* ------------------------------------------------------------------------- *)
(* Hermite normal form: the least positive integer a0 of the ideal and the  *)
(* least positive w-coordinate c0 (of an element b + c0 w).                 *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_HERMITE = prove
 (`!w j N.
     (!z. z IN j ==> ?x y. integer x /\ integer y /\ z = Cx x + Cx y * w) /\
     (!x y. x IN j /\ y IN j ==> x - y IN j) /\
     (!q z. integer q /\ z IN j ==> Cx q * z IN j) /\
     (!z. z IN j ==> w * z IN j) /\
     0 < N /\ Cx(&N) IN j
     ==> ?a0 c0 b. 0 < a0 /\ 0 < c0 /\ integer b /\
                   Cx(&a0) IN j /\ Cx b + Cx(&c0) * w IN j /\
                   (!m. integer m /\ Cx m IN j
                        ==> ?q. integer q /\ m = &a0 * q) /\
                   (!x y. integer x /\ integer y /\ Cx x + Cx y * w IN j
                          ==> ?q. integer q /\ y = &c0 * q)`,
  REPEAT GEN_TAC THEN
  QUAD_PID_LABELS_TAC ["coord"; "sub"; "zmul"; "wmul"; "Npos"; "Nj"] THEN
  MP_TAC(ISPEC `\k. 0 < k /\ Cx(&k) IN j` num_WOP) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "amin"))) THEN
  MP_TAC(ISPEC `\k. 0 < k /\ ?x. integer x /\ Cx x + Cx(&k) * w IN j`
    num_WOP) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `a0:num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN `Cx(&0) + Cx(&a0) * w = w * Cx(&a0)` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING;
      USE_THEN "wmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:num` (CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC))
   (LABEL_TAC "cmin"))) THEN
  MAP_EVERY EXISTS_TAC [`a0:num`; `c0:num`; `b:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `m:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC QUAD_PID_MIN_DIVIDES THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`q:real`; `k:num`] THEN STRIP_TAC THEN
    USE_THEN "amin" (MP_TAC o C MP (ASSUME `k < a0`) o SPEC `k:num`) THEN
    SUBGOAL_THEN `Cx(&k) IN j` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `Cx(&k) = Cx m - Cx q * Cx(&a0)` SUBST1_TAC THENL
       [UNDISCH_TAC `m - &a0 * q = &k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[CX_SUB; CX_MUL] THEN CONV_TAC COMPLEX_RING;
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "zmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC QUAD_PID_MIN_DIVIDES THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`q:real`; `k:num`] THEN STRIP_TAC THEN
    USE_THEN "cmin" (MP_TAC o C MP (ASSUME `k < c0`) o SPEC `k:num`) THEN
    SUBGOAL_THEN `?x'. integer x' /\ Cx x' + Cx(&k) * w IN j`
     (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `x - q * b:real` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
      SUBGOAL_THEN `Cx(x - q * b) + Cx(&k) * w =
                    (Cx x + Cx y * w) - Cx q * (Cx b + Cx(&c0) * w)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `y - &c0 * q = &k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[CX_SUB; CX_MUL; CX_ADD] THEN CONV_TAC COMPLEX_RING;
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "zmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The ideal is c0 (Z a + Z (b1 + w)) with a0 = c0 a, b = c0 b1, and a      *)
(* divides N(b1 + w) = b1^2 + t b1 + n.                                      *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_STRUCTURE = prove
 (`!w t n j a0 c0 b.
     integer t /\ integer n /\ w pow 2 = Cx t * w - Cx n /\
     (!z. z IN j ==> ?x y. integer x /\ integer y /\ z = Cx x + Cx y * w) /\
     (!x y. x IN j /\ y IN j ==> x - y IN j) /\
     (!q z. integer q /\ z IN j ==> Cx q * z IN j) /\
     (!z. z IN j ==> w * z IN j) /\
     0 < a0 /\ 0 < c0 /\ integer b /\
     Cx(&a0) IN j /\ Cx b + Cx(&c0) * w IN j /\
     (!m. integer m /\ Cx m IN j ==> ?q. integer q /\ m = &a0 * q) /\
     (!x y. integer x /\ integer y /\ Cx x + Cx y * w IN j
            ==> ?q. integer q /\ y = &c0 * q)
     ==> ?a b1 m. integer a /\ integer b1 /\ integer m /\ &0 < a /\
                  &a0 = &c0 * a /\ b = &c0 * b1 /\
                  a * m = b1 pow 2 + t * b1 + n /\
                  !z. z IN j
                      ==> ?u v. integer u /\ integer v /\
                                z = Cx u * Cx(&a0) +
                                    Cx v * (Cx b + Cx(&c0) * w)`,
  REPEAT GEN_TAC THEN
  QUAD_PID_LABELS_TAC ["t"; "n"; "wsq"; "coord"; "sub"; "zmul"; "wmul";
     "a0pos"; "c0pos"; "b"; "a0j"; "bj"; "F1"; "F2"] THEN
  SUBGOAL_THEN `?a. integer a /\ &a0 = &c0 * a`
  (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "F2" MATCH_MP_TAC THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN `Cx(&0) + Cx(&a0) * w = w * Cx(&a0)` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING;
      USE_THEN "wmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &c0 * a` MP_TAC THENL
     [UNDISCH_TAC `&a0 = &c0 * a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT];
      ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_OF_NUM_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?q. integer q /\ b + &c0 * t = &c0 * q`
  (X_CHOOSE_THEN `q2:real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "F2" MATCH_MP_TAC THEN EXISTS_TAC `--(&c0 * n)` THEN
    CONJ_TAC THENL [QUAD_PID_INTEGER_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [QUAD_PID_INTEGER_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Cx(--(&c0 * n)) + Cx(b + &c0 * t) * w =
                  w * (Cx b + Cx(&c0) * w)` SUBST1_TAC THENL
     [REWRITE_TAC[CX_NEG; CX_MUL; CX_ADD] THEN
      UNDISCH_TAC `w pow 2 = Cx t * w - Cx n` THEN CONV_TAC COMPLEX_RING;
      USE_THEN "wmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b1. integer b1 /\ b = &c0 * b1`
  (X_CHOOSE_THEN `b1:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `q2 - t:real` THEN CONJ_TAC THENL
     [QUAD_PID_INTEGER_TAC; ALL_TAC] THEN
    UNDISCH_TAC `b + &c0 * t = &c0 * q2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  UNDISCH_TAC `b = &c0 * b1` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `?q. integer q /\ --(&c0 * (b1 pow 2 + t * b1 + n)) = &a0 * q`
  (X_CHOOSE_THEN `q3:real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "F1" MATCH_MP_TAC THEN
    CONJ_TAC THENL [QUAD_PID_INTEGER_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `Cx(--(&c0 * (b1 pow 2 + t * b1 + n))) =
      w * (Cx(&c0 * b1) + Cx(&c0) * w) -
      Cx(b1 + t) * (Cx(&c0 * b1) + Cx(&c0) * w)`
    SUBST1_TAC THENL
     [REWRITE_TAC[CX_NEG; CX_MUL; CX_ADD; CX_POW] THEN
      UNDISCH_TAC `w pow 2 = Cx t * w - Cx n` THEN CONV_TAC COMPLEX_RING;
      USE_THEN "sub" MATCH_MP_TAC THEN CONJ_TAC THENL
       [USE_THEN "wmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "zmul" MATCH_MP_TAC THEN CONJ_TAC THENL
         [QUAD_PID_INTEGER_TAC; ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * --q3 = b1 pow 2 + t * b1 + n` ASSUME_TAC THENL
   [SUBGOAL_THEN `&c0 * (a * --q3) = &c0 * (b1 pow 2 + t * b1 + n)`
    MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`--(&c0 * (b1 pow 2 + t * b1 + n)) = &a0 * q3`; `&a0 = &c0 * a`] THEN
      CONV_TAC REAL_RING;
      REWRITE_TAC[REAL_EQ_MUL_LCANCEL; REAL_OF_NUM_EQ] THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < c ==> ~(c = 0)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN j
        ==> ?u v. integer u /\ integer v /\
                  z = Cx u * Cx(&a0) + Cx v * (Cx(&c0 * b1) + Cx(&c0) * w)`
  (LABEL_TAC "struct") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    USE_THEN "coord" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       SUBST_ALL_TAC)))) THEN
    USE_THEN "F2" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "F1" (MP_TAC o SPEC `x - v * &c0 * b1`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [QUAD_PID_INTEGER_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `Cx(x - v * &c0 * b1) =
        (Cx x + Cx y * w) - Cx v * (Cx(&c0 * b1) + Cx(&c0) * w)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `y = &c0 * v` THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[CX_SUB; CX_MUL; CX_ADD] THEN CONV_TAC COMPLEX_RING;
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "zmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x = &a0 * u + v * &c0 * b1` SUBST1_TAC THENL
     [UNDISCH_TAC `x - v * &c0 * b1 = &a0 * u` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `y = &c0 * v` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CX_ADD; CX_MUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b1:real`; `--q3:real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_REWRITE_TAC[INTEGER_NEG]);;

(* ------------------------------------------------------------------------- *)
(* The generator: if a p^2 + (2 b1 + t) p r + m r^2 = 1 then                 *)
(* g = c0 (p a + r (b1 + w)) divides every c0 (u a + v (b1 + w)).            *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_GENERATOR_IDENTITY_COMPLEX = prove
 (`!w t n a b m p r u v c:complex.
        w pow 2 = t * w - n /\
        a * m = b pow 2 + t * b + n /\
        a * p pow 2 + (Cx(&2) * b + t) * p * r + m * r pow 2 = Cx(&1) /\
        ~(a = Cx(&0))
        ==> u * (c * a) + v * (c * b + c * w) =
            (p * (c * a) + r * (c * b + c * w)) *
            ((u * p * a + u * r * (b + t) + v * p * b + v * r * m) +
             (v * p - u * r) * w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `a * ((u * p * a + u * r * (b + t) + v * p * b + v * r * m) +
         (v * p - u * r) * w) =
    (u * a + v * (b + w)) * ((p * a + r * b + r * t) - r * w:complex)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`w pow 2 = t * w - n:complex`;
      `a * m = b pow 2 + t * b + n:complex`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p * a + r * (b + w)) * ((p * a + r * b + r * t) - r * w) = a:complex`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`w pow 2 = t * w - n:complex`; `a * m = b pow 2 + t * b + n:complex`;
      `a * p pow 2 + (Cx(&2) * b + t) * p * r + m * r pow 2 = Cx(&1)`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `!a x y:complex. ~(a = Cx(&0)) /\ a * x = a * y ==> x = y`) THEN
  EXISTS_TAC `a:complex` THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`a * ((u * p * a + u * r * (b + t) + v * p * b + v * r * m) +
          (v * p - u * r) * w) =
     (u * a + v * (b + w)) * ((p * a + r * b + r * t) - r * w:complex)`;
    `(p * a + r * (b + w)) * ((p * a + r * b + r * t) - r * w) =
     a:complex`] THEN
  CONV_TAC COMPLEX_RING);;

let QUAD_PID_GENERATOR_IDENTITY = prove
 (`!w t n a b m p r u v c.
        w pow 2 = Cx t * w - Cx n /\
        a * m = b pow 2 + t * b + n /\
        a * p pow 2 + (&2 * b + t) * p * r + m * r pow 2 = &1 /\
        ~(a = &0)
        ==> Cx u * Cx(c * a) + Cx v * (Cx(c * b) + Cx c * w) =
            (Cx p * Cx(c * a) + Cx r * (Cx(c * b) + Cx c * w)) *
            (Cx(u * p * a + u * r * (b + t) + v * p * b + v * r * m) +
             Cx(v * p - u * r) * w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CX_ADD; CX_MUL; CX_SUB] THEN
  MATCH_MP_TAC QUAD_PID_GENERATOR_IDENTITY_COMPLEX THEN
  EXISTS_TAC `Cx n` THEN ASM_REWRITE_TAC[CX_INJ] THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_MUL; GSYM CX_POW; CX_INJ] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The abstract statement: an ideal j of Z + Z w (w^2 = t w - n) is         *)
(* principal when every positive definite integer form of discriminant      *)
(* t^2 - 4 n represents 1.                                                   *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_ABSTRACT = prove
 (`!w t n j.
        integer t /\ integer n /\ w pow 2 = Cx t * w - Cx n /\
        (!x y. norm(Cx x + Cx y * w) pow 2 =
               x pow 2 + t * x * y + n * y pow 2) /\
        (!a b c. integer a /\ integer b /\ integer c /\ &0 < a /\
                 b pow 2 - &4 * a * c = t pow 2 - &4 * n
                 ==> ?p r. integer p /\ integer r /\
                           a * p pow 2 + b * p * r + c * r pow 2 = &1) /\
        (!z. z IN j ==> ?x y. integer x /\ integer y /\ z = Cx x + Cx y * w) /\
        Cx(&0) IN j /\
        (!x y. x IN j /\ y IN j ==> x + y IN j) /\
        (!x y. x IN j /\ y IN j ==> x - y IN j) /\
        (!x y z. integer x /\ integer y /\ z IN j
                 ==> (Cx x + Cx y * w) * z IN j)
        ==> ?g. g IN j /\
                !z. z IN j ==> ?x y. integer x /\ integer y /\
                                     z = g * (Cx x + Cx y * w)`,
  REPEAT GEN_TAC THEN
  QUAD_PID_LABELS_TAC ["t"; "n"; "wsq"; "norm"; "forms"; "coord"; "zero";
                       "add"; "sub"; "mul"] THEN
  ASM_CASES_TAC `!z. z IN j ==> z = Cx(&0)` THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN
    REWRITE_TAC[INTEGER_CLOSED; COMPLEX_MUL_LZERO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!q z. integer q /\ z IN j ==> Cx q * z IN j`
  (LABEL_TAC "zmul") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `Cx q * z = (Cx q + Cx(&0) * w) * z` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING;
      USE_THEN "mul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:complex. z IN j ==> w * z IN j` (LABEL_TAC "wmul") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `w * z = (Cx(&0) + Cx(&1) * w) * z` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING;
      USE_THEN "mul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`w:complex`; `t:real`; `n:real`; `j:complex->bool`;
                `z0:complex`] QUAD_PID_POSITIVE_INT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w:complex`; `j:complex->bool`; `N:num`] QUAD_PID_HERMITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a0:num`; `c0:num`; `b:real`] THEN
  QUAD_PID_LABELS_TAC ["a0pos"; "c0pos"; "b"; "a0j"; "bj"; "F1"; "F2"] THEN
  MP_TAC(SPECL [`w:complex`; `t:real`; `n:real`; `j:complex->bool`;
                `a0:num`; `c0:num`; `b:real`] QUAD_PID_STRUCTURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b1:real`; `m:real`] THEN
  QUAD_PID_LABELS_TAC ["a"; "b1"; "m"; "apos"; "a0eq"; "beq"; "am";
                       "struct"] THEN
  USE_THEN "forms" (MP_TAC o SPECL [`a:real`; `&2 * b1 + t`; `m:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [QUAD_PID_INTEGER_TAC;
      UNDISCH_TAC `a * m = b1 pow 2 + t * b1 + n` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `Cx p * Cx(&a0) + Cx r * (Cx b + Cx(&c0) * w)` THEN
  CONJ_TAC THENL
   [USE_THEN "add" MATCH_MP_TAC THEN CONJ_TAC THEN
    USE_THEN "zmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  USE_THEN "struct" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`u * p * a + u * r * (b1 + t) + v * p * b1 + v * r * m:real`;
    `v * p - u * r:real`] THEN
  REPEAT CONJ_TAC THENL
   [QUAD_PID_INTEGER_TAC; QUAD_PID_INTEGER_TAC; ALL_TAC] THEN
  USE_THEN "a0eq" SUBST1_TAC THEN USE_THEN "beq" SUBST1_TAC THEN
  MATCH_MP_TAC QUAD_PID_GENERATOR_IDENTITY THEN EXISTS_TAC `n:real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* Class number one: the ring of integers of Q(sqrt(-d)) is a PID.          *)
(* ------------------------------------------------------------------------- *)

let QUAD_CLASSNO_ONE_IMP_PID = prove
 (`!d. squarefree d /\ form_classno (qdisc d) = 1
       ==> PID (imag_quadratic_integers d)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[PID; IMAG_QUADRATIC_INTEGERS_INTEGRAL_DOMAIN] THEN
  X_GEN_TAC `j:complex->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[principal_ideal] THEN
  SUBGOAL_THEN
   `?g. g IN ring_carrier(imag_quadratic_integers d) /\
        j = {x | ring_divides (imag_quadratic_integers d) g x}`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `g:complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:complex` THEN ASM_SIMP_TAC[IDEAL_GENERATED_SING]] THEN
  UNDISCH_TAC `ring_ideal (imag_quadratic_integers d) j` THEN
  REWRITE_TAC[ring_ideal; ring_divides; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CARRIER] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  QUAD_PID_LABELS_TAC ["coord"; "zero"; "neg"; "add"; "mul"] THEN
  X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)
    (SPEC `d:num` QUAD_PID_OMEGA_DATA) THEN
  MP_TAC(SPECL [`quad_omega d`; `t:real`; `n:real`; `j:complex->bool`]
    QUAD_PID_ABSTRACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC QUAD_PID_FORM_ONE_REAL THEN
      EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[complex_sub] THEN
      USE_THEN "add" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "mul" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen"))) THEN
  EXISTS_TAC `g:complex` THEN CONJ_TAC THENL
   [USE_THEN "coord" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "coord" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "coord" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "gen" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `Cx x + Cx y * quad_omega d` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `y:complex` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `y1:real` STRIP_ASSUME_TAC))
        SUBST1_TAC)))) THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    USE_THEN "mul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`x1:real`; `y1:real`] THEN ASM_REWRITE_TAC[]]);;
