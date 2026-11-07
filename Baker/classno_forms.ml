(* ========================================================================= *)
(* Reduced binary quadratic forms: reduction, the evaluator of the class     *)
(* number, witnesses, the nine discriminants, the search up to 46500.        *)
(*                                                                           *)
(* Purpose: the elementary theory of reduced positive definite forms over    *)
(* int used for the class number problems (Gauss, Disquisitiones             *)
(* Arithmeticae, sec. V; Baker, Transcendental Number Theory, Ch. 5). Bounds *)
(* for reduced forms and finiteness (CLASSNO_FORMS_FINITE); the principal    *)
(* form is reduced (CLASSNO_PRINCIPAL_REDUCED) and, if form_classno D = 1,   *)
(* it is the only reduced primitive form (CLASSNO_FORMS_UNIQUE). Reduction:  *)
(* the Lagrange reduction CUBIC_QF_REDUCE transferred to int                 *)
(* (QF_REDUCE_INT) turns every positive definite form into a reduced form of *)
(* the same discriminant with the same represented integers                  *)
(* (QFORM_REDUCE_VALUES), primitive if the given form is                     *)
(* (QFORM_REDUCE_PRIMITIVE; QFORM_REDUCE_FORM for a squarefree discriminant  *)
(* -d); so r is represented by a reduced primitive form of discriminant -n   *)
(* when b^2 + n = 4 r c with gcd(r, gcd(b, c)) = 1                           *)
(* (QFORM_REPRESENTED_REDUCED), and if form_classno(-d) = 1 and -d is a      *)
(* square modulo 4 p, then p is represented by the principal form            *)
(* (CLASSNO_SPLIT_REPRESENTED). The evaluator: form_classno(-n) is the       *)
(* number of the reduced primitive forms with a <= m, abs b <= m,            *)
(* 3 (m + 1)^2 > n, c solved from the discriminant (QF_FORMS_EVAL); the      *)
(* conversion FORM_CLASSNO_CONV computes the forms and proves                *)
(* form_classno(-n) = k for a numeral n. Genus theory is replaced by         *)
(* explicit witnesses: a second reduced primitive form (a, abs b, c) with    *)
(* a >= 2 (CLASSNO_WITNESS; primitivity from d squarefree), the ambiguous    *)
(* form of a factorisation (QFORM_AMBIGUOUS_WITNESS), which give             *)
(* CLASSNO_ONE_CASES: for squarefree d with form_classno (qdisc d) = 1, d is *)
(* 1, 2, 7 or a prime = 3 mod 8. CLASSNO_NINE: the nine d of Gauss have      *)
(* class number one. CLASSNO_SEARCH: every d <= 46500 with d = 3 mod 8,      *)
(* except 3, 11, 19, 43, 67, 163, has a witness: for 99 of the 105 residues  *)
(* of d modulo 840 a witness with a in {3, 5, 7} works uniformly, and the    *)
(* remaining 330 values of d are covered by an explicit table of witnesses   *)
(* (found by a computer search; every entry is checked in the proof).        *)
(*                                                                           *)
(* Main results: CLASSNO_FORMS_FINITE, CLASSNO_PRINCIPAL_REDUCED,            *)
(* CLASSNO_FORMS_UNIQUE, QF_REDUCE_INT, QFORM_REDUCE_VALUES,                 *)
(* QFORM_REDUCE_PRIMITIVE, QFORM_REDUCE_FORM, QFORM_REPRESENTED_REDUCED,     *)
(* CLASSNO_SPLIT_REPRESENTED, QF_FORMS_EVAL, FORM_CLASSNO_CONV,              *)
(* CLASSNO_WITNESS, QFORM_AMBIGUOUS_WITNESS, CLASSNO_ONE_CASES,              *)
(* CLASSNO_NINE, CLASSNO_SEARCH; helper names QF_*, CNF_QFORM_* and          *)
(* CLASSNO_FORMS_*.                                                          *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (qf_reduced, form_classno, qdisc, prin_form,  *)
(* qform, QFORM_PRIN), Baker/cubic_reduction.ml (CUBIC_QF_REDUCE);           *)
(* Library/pocklington.ml (squarefree), Library/prime.ml (GCD_CONV),         *)
(* Library/integer.ml (INT_DIVIDES_ONE_POS, INT_GCD_1).                      *)
(* ========================================================================= *)

needs "Library/integer.ml";;
needs "Baker/classno_defs.ml";;
needs "Baker/cubic_reduction.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary bounds for reduced forms; finiteness.                          *)
(* ------------------------------------------------------------------------- *)

let QF_REDUCED_BOUNDS = prove
 (`!a b c:int.
        qf_reduced a b c
        ==> &0 < a /\ abs b <= a /\ a <= c /\
            b pow 2 <= a pow 2 /\ a pow 2 <= a * c /\
            a <= a pow 2 /\ c <= a * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qf_reduced] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_LE_SQUARE_ABS] THEN
    UNDISCH_TAC `abs b <= a:int` THEN UNDISCH_TAC `&0 < a:int` THEN
    INT_ARITH_TAC;
    REWRITE_TAC[INT_POW_2] THEN MATCH_MP_TAC INT_LE_LMUL THEN
    UNDISCH_TAC `a <= c:int` THEN UNDISCH_TAC `&0 < a:int` THEN
    INT_ARITH_TAC;
    REWRITE_TAC[INT_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_RID] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN
    UNDISCH_TAC `&0 < a:int` THEN INT_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
    MATCH_MP_TAC INT_LE_RMUL THEN
    MAP_EVERY UNDISCH_TAC [`a <= c:int`; `&0 < a:int`] THEN
    INT_ARITH_TAC]);;

let QF_REDUCED_DISC = prove
 (`!a b c:int.
        qf_reduced a b c
        ==> &3 * a pow 2 <= &4 * a * c - b pow 2 /\
            a <= &4 * a * c - b pow 2 /\
            abs b <= &4 * a * c - b pow 2 /\
            c <= &4 * a * c - b pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP QF_REDUCED_BOUNDS) THEN INT_ARITH_TAC);;

let QF_FORMS_IN = prove
 (`!D a b c:int.
        (a,b,c) IN {(a,b,c) | qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
                              gcd(a,gcd(b,c)) = &1} <=>
        qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\ gcd(a,gcd(b,c)) = &1`,
  REWRITE_TAC[IN_ELIM_TRIPLE_THM]);;

let CLASSNO_FORMS_FINITE = prove
 (`!D. FINITE {(a,b,c) | qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
                        gcd(a,gcd(b,c)) = &1}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:int | D <= x /\ x <= --D} CROSS
              {x:int | D <= x /\ x <= --D} CROSS
              {x:int | D <= x /\ x <= --D}` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_INT_SEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; QF_FORMS_IN; IN_CROSS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QF_REDUCED_BOUNDS) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QF_REDUCED_DISC) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The principal form; primitivity; uniqueness when form_classno D = 1.      *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_PRINCIPAL_REDUCED = prove
 (`!d. d MOD 4 = 3 ==> qf_reduced (&1) (&1) (&((d + 1) DIV 4)) /\
                      &1 pow 2 - &4 * &1 * &((d + 1) DIV 4) = --(&d:int)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(d + 1) DIV 4 = d DIV 4 + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `int_of_num` o CONJUNCT1) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN DISCH_TAC THEN
  REWRITE_TAC[qf_reduced; GSYM INT_OF_NUM_ADD] THEN ASM_INT_ARITH_TAC);;

let QF_PRIMITIVE_BEZOUT = prove
 (`!a b c x y z:int. a * x + b * y + c * z = &1 ==> gcd(a,gcd(b,c)) = &1`,
  REPEAT STRIP_TAC THEN SIMP_TAC[GSYM INT_DIVIDES_ONE_POS; INT_GCD_POS] THEN
  UNDISCH_TAC `a * x + b * y + c * z = &1:int` THEN INTEGER_TAC);;


let QF_PRIMITIVE_SQUAREFREE = prove
 (`!a b c:int d. b pow 2 - &4 * a * c = --(&d) /\ squarefree d
                 ==> gcd(a,gcd(b,c)) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `gcd(a:int,gcd(b,c)) pow 2 divides &d` MP_TAC THENL
   [ONCE_REWRITE_TAC[INTEGER_RULE `(x:int) divides y <=> x divides --y`] THEN
    UNDISCH_TAC `b pow 2 - &4 * a * c = --(&d:int)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN INTEGER_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `gcd(b:int,c)`] int_gcd) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`gcd(a:int,gcd(b,c))`,`g:int`) THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[INT_OF_NUM_POW; GSYM num_divides; INT_OF_NUM_EQ] THEN
  UNDISCH_TAC `squarefree d` THEN REWRITE_TAC[squarefree]);;

(* A form whose first coefficient is coprime to the discriminant is         *)
(* primitive.                                                                *)

let QF_PRIMITIVE_COPRIME = prove
 (`!a b c:int n. b pow 2 - &4 * a * c = --n /\ coprime(a,n)
                 ==> gcd(a,gcd(b,c)) = &1`,
  REPEAT STRIP_TAC THEN SIMP_TAC[GSYM INT_DIVIDES_ONE_POS; INT_GCD_POS] THEN
  MAP_EVERY UNDISCH_TAC
   [`b pow 2 - &4 * a * c = --n:int`; `coprime(a:int,n)`] THEN
  CONV_TAC INTEGER_RULE);;

let CLASSNO_FORMS_CARD_1_EQ = prove
 (`!s:A->bool x y. FINITE s /\ CARD s = 1 /\ x IN s /\ y IN s ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:A->bool` CARD_LE_1) THEN ASM_REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[SUBSET; IN_SING] THEN ASM_MESON_TAC[]);;

let CLASSNO_FORMS_UNIQUE = prove
 (`!D a b c a' b' c'.
        form_classno D = 1 /\
        qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
        gcd(a,gcd(b,c)) = &1 /\
        qf_reduced a' b' c' /\ b' pow 2 - &4 * a' * c' = D /\
        gcd(a',gcd(b',c')) = &1
        ==> a = a' /\ b = b' /\ c = c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{(a,b,c) | qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
                             gcd(a,gcd(b,c)) = &1}`;
                 `(a:int,b:int,c:int)`; `(a':int,b':int,c':int)`]
         CLASSNO_FORMS_CARD_1_EQ) THEN
  REWRITE_TAC[CLASSNO_FORMS_FINITE; QF_FORMS_IN; PAIR_EQ;
              GSYM form_classno] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reduction (Lagrange): every positive definite form is equivalent to a     *)
(* reduced form of the same discriminant that represents the same integers;  *)
(* primitivity is preserved.                                                 *)
(* ------------------------------------------------------------------------- *)

let QF_REDUCE_INT = prove
 (`!A B C:int.
        &0 < A /\ &0 < &4 * A * C - B pow 2
        ==> ?p q r s.
              p * s - q * r = &1 /\
              abs(&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s)
              <= A * p pow 2 + B * p * r + C * r pow 2 /\
              A * p pow 2 + B * p * r + C * r pow 2
              <= A * q pow 2 + B * q * s + C * s pow 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_lt; int_le; int_eq; int_sub_th; int_mul_th; int_pow_th;
              int_add_th; int_abs_th; int_of_num_th] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CUBIC_QF_REDUCE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p':real`; `q':real`; `r':real`; `s':real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`int_of_real p'`; `int_of_real q'`; `int_of_real r'`; `int_of_real s'`] THEN
  ASM_SIMP_TAC[REAL_OF_INT_OF_REAL]);;

let QFORM_NEG = prove
 (`!a b c x y:int. qform a (--b) c x y = qform a b c x (--y)`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_ABS = prove
 (`!a b c n:int.
        (?x y. qform a (abs b) c x y = n) <=> (?x y. qform a b c x y = n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_ABS] THEN COND_CASES_TAC THEN
  REWRITE_TAC[QFORM_NEG] THEN
  MESON_TAC[INT_NEG_NEG]);;

let QFORM_SUBST = prove
 (`!A B C P Q R S x y:int.
        qform A B C (P * x + Q * y) (R * x + S * y) =
        qform (qform A B C P R)
              (&2 * A * P * Q + B * (P * S + Q * R) + &2 * C * R * S)
              (qform A B C Q S) x y`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_UNIMODULAR_INV = prove
 (`!P Q R S x y:int.
        P * S - Q * R = &1
        ==> P * (S * x - Q * y) + Q * (--R * x + P * y) = x /\
            R * (S * x - Q * y) + S * (--R * x + P * y) = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  UNDISCH_TAC `P * S - Q * R = &1:int` THEN CONV_TAC INT_RING);;

let QFORM_REDUCE_VALUES = prove
 (`!A B C:int.
        &0 < A /\ &0 < &4 * A * C - B pow 2
        ==> ?a b c. qf_reduced a b c /\
                    b pow 2 - &4 * a * c = B pow 2 - &4 * A * C /\
                    !n. (?x y. qform a b c x y = n) <=>
                        (?x y. qform A B C x y = n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A:int`; `B:int`; `C:int`] QF_REDUCE_INT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM qform; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:int`; `Q:int`; `R:int`; `S:int`] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `B':int = &2 * A * P * Q + B * (P * S + Q * R) + &2 * C * R * S` THEN
  SUBGOAL_THEN
   `!x y:int. qform (qform A B C P R) B' (qform A B C Q S) x y =
              qform A B C (P * x + Q * y) (R * x + S * y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "B'" THEN REWRITE_TAC[QFORM_SUBST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `B' pow 2 - &4 * qform A B C P R * qform A B C Q S =
    B pow 2 - &4 * A * C:int`
  ASSUME_TAC THENL
   [EXPAND_TAC "B'" THEN REWRITE_TAC[qform] THEN
    UNDISCH_TAC `P * S - Q * R = &1:int` THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`qform A B C P R`; `abs B':int`; `qform A B C Q S`] THEN
  REWRITE_TAC[INT_POW2_ABS; QFORM_ABS] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[qf_reduced; INT_ABS_ABS; INT_ABS_POS] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[INT_LT_LE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `abs B' <= qform A B C P R` THEN INT_ARITH_TAC;
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      SUBGOAL_THEN `B':int = &0` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`abs B' <= qform A B C P R`; `qform A B C P R = &0`] THEN
        INT_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC
       `B' pow 2 - &4 * qform A B C P R * qform A B C Q S =
        B pow 2 - &4 * A * C:int` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0:int < &4 * A * C - B pow 2` THEN INT_ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `n:int` THEN EQ_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THENL
     [MAP_EVERY EXISTS_TAC [`P * x + Q * y:int`; `R * x + S * y:int`] THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      MAP_EVERY EXISTS_TAC [`S * x - Q * y:int`; `--R * x + P * y:int`] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`P:int`; `Q:int`; `R:int`; `S:int`; `x:int`; `y:int`]
        QFORM_UNIMODULAR_INV) THEN
      ASM_SIMP_TAC[]]]);;

(* The reduced form of a primitive form is primitive: its content divides    *)
(* the values A = f(1,0), C = f(0,1) and A + B + C = f(1,1) of the given     *)
(* form f = (A,B,C).                                                         *)

let QFORM_REDUCE_PRIMITIVE = prove
 (`!A B C:int.
        &0 < A /\ &0 < &4 * A * C - B pow 2 /\ gcd(A,gcd(B,C)) = &1
        ==> ?a b c. qf_reduced a b c /\
                    b pow 2 - &4 * a * c = B pow 2 - &4 * A * C /\
                    gcd(a,gcd(b,c)) = &1 /\
                    !n. (?x y. qform a b c x y = n) <=>
                        (?x y. qform A B C x y = n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:int`; `B:int`; `C:int`] QFORM_REDUCE_VALUES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM INT_DIVIDES_ONE_POS; INT_GCD_POS] THEN
  SUBGOAL_THEN `!x y. gcd(a,gcd(b,c)) divides qform A B C x y` MP_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `qform A B C x y`) THEN
    MATCH_MP_TAC(TAUT `(p ==> r) /\ q ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[qform] THEN
    CONV_TAC INTEGER_RULE;
    DISCH_THEN(fun th -> MP_TAC(SPECL [`&1:int`; `&0:int`] th) THEN
      MP_TAC(SPECL [`&0:int`; `&1:int`] th) THEN
      MP_TAC(SPECL [`&1:int`; `&1:int`] th)) THEN
    REWRITE_TAC[qform] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_MUL_RID; INT_ADD_LID; INT_ADD_RID; INT_MUL_RZERO] THEN
    UNDISCH_TAC `gcd(A,gcd(B,C)) = &1` THEN CONV_TAC INTEGER_RULE]);;

let QFORM_REDUCE_FORM = prove
 (`!A B C d. &0 < A /\ B pow 2 - &4 * A * C = --(&d) /\ squarefree d
             ==> ?a b c. qf_reduced a b c /\ b pow 2 - &4 * a * c = --(&d) /\
                         gcd(a,gcd(b,c)) = &1 /\
                         !n. (?x y. qform A B C x y = n) <=>
                             (?x y. qform a b c x y = n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:int`; `B:int`; `C:int`] QFORM_REDUCE_PRIMITIVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[INT_ARITH `&0:int < x - y <=> --(y - x) > &0`] THEN
      ASM_REWRITE_TAC[INT_NEG_NEG; INT_GT; INT_OF_NUM_LT] THEN
      ASM_MESON_TAC[SQUAREFREE_IMP_NZ; LT_NZ];
      MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `d:num` THEN
      ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

(* A positive integer r with b^2 + n = 4 r c and gcd(r, gcd(b, c)) = 1 is    *)
(* represented by a reduced primitive form of discriminant -n (the reduction *)
(* of (r,b,c); for a prime r the gcd condition holds if r^2 does not divide  *)
(* n, by QF_PRIMITIVE_COPRIME if r does not divide n).                       *)

let QFORM_REPRESENTED_REDUCED = prove
 (`!n r b c.
        ~(n = 0) /\ b pow 2 + &n = &4 * &r * c /\ gcd(&r,gcd(b,c)) = &1
        ==> ?a' b' c' x y. qf_reduced a' b' c' /\
                           b' pow 2 - &4 * a' * c' = --(&n) /\
                           gcd(a',gcd(b',c')) = &1 /\
                           qform a' b' c' x y = &r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0:int < &n /\ &0:int < &r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_REWRITE_TAC[LT_NZ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(n = 0)` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
    MP_TAC(SPEC `b:int` INT_LE_POW_2) THEN
    UNDISCH_TAC `b pow 2 + &n = &4 * &0 * c:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&r:int`; `b:int`; `c:int`] QFORM_REDUCE_PRIMITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `b pow 2 + &n = &4 * &r * c:int` THEN
    UNDISCH_TAC `&0:int < &n` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [UNDISCH_TAC `b pow 2 + &n = &4 * &r * c:int` THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`] THEN REWRITE_TAC[qform] THEN
    INT_ARITH_TAC]);;

(* Split primes are represented by the principal form when the class number  *)
(* is one: the reduction of (p,b,(b^2+d)/(4p)) is the principal form.        *)

let CLASSNO_SPLIT_REPRESENTED = prove
 (`!d p. prime d /\ d MOD 4 = 3 /\ form_classno (--(&d)) = 1 /\
        (?b:int. (b pow 2 + &d == &0) (mod (&4 * &p)))
        ==> ?x y. prin_form d x y = &p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `b:int`)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `c:int` o
    REWRITE_RULE[int_congruent; INT_SUB_RZERO]) THEN
  MP_TAC(SPECL [`d:num`; `p:num`; `b:int`; `c:int`]
    QFORM_REPRESENTED_REDUCED) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[INT_MUL_ASSOC]; ALL_TAC] THEN
    MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `d:num` THEN
    ASM_SIMP_TAC[PRIME_IMP_SQUAREFREE] THEN
    UNDISCH_TAC `b pow 2 + &d = (&4 * &p) * c:int` THEN INT_ARITH_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a':int`; `b':int`; `c':int`; `x:int`; `y:int`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN
  MP_TAC(SPEC `d:num` CLASSNO_PRINCIPAL_REDUCED) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`--(&d):int`; `&1:int`; `&1:int`; `&((d + 1) DIV 4):int`;
                `a':int`; `b':int`; `c':int`] CLASSNO_FORMS_UNIQUE) THEN
  ASM_REWRITE_TAC[INT_GCD_1] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[GSYM QFORM_PRIN]);;

(* ------------------------------------------------------------------------- *)
(* The evaluator: form_classno(-n) counts the reduced primitive forms with   *)
(* a <= m and abs b <= m, 3 (m + 1)^2 > n (c solved from the discriminant,   *)
(* no enumeration of c).                                                     *)
(* ------------------------------------------------------------------------- *)

let QF_SOLVE_C = prove
 (`!A B n c:int.
        &B pow 2 - &4 * &(A + 1) * c = --(&n) <=>
        (B EXP 2 + n) MOD (4 * (A + 1)) = 0 /\
        c = &((B EXP 2 + n) DIV (4 * (A + 1)))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `k = 4 * (A + 1)` THEN ABBREV_TAC `N = B EXP 2 + n` THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&B pow 2 - &4 * &(A + 1) * c = --(&n) <=> &k * c = &N:int`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["k"; "N"] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD;
                GSYM INT_OF_NUM_POW] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= c:int` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`c:int`; `&0:int`; `&k:int`] INT_LT_LMUL_EQ) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_LT; INT_MUL_RZERO] THEN
      UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      SUBST1_TAC(SYM(MATCH_MP INT_OF_NUM_OF_INT th))) THEN
    REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MOD_MULT; DIV_MULT];
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    UNDISCH_TAC `N MOD k = 0` THEN REWRITE_TAC[MOD_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT] THEN
    MATCH_ACCEPT_TAC MULT_SYM]);;

let QF_FORMS_EVAL = prove
 (`!n m s.
        (!a b c. (a,b,c) IN s
                 ==> qf_reduced a b c /\ b pow 2 - &4 * a * c = --(&n) /\
                     gcd(a,gcd(b,c)) = &1) /\
        n < 3 * (m + 1) EXP 2 /\
        (!A. A < m
             ==> !B. B < m + 1
                     ==> (B EXP 2 + n) MOD (4 * (A + 1)) = 0
                         ==> (qf_reduced (&(A + 1)) (&B)
                               (&((B EXP 2 + n) DIV (4 * (A + 1)))) /\
                              gcd(&(A + 1),gcd(&B,
                                  &((B EXP 2 + n) DIV (4 * (A + 1))))) = &1
                              ==> (&(A + 1),&B,
                                   &((B EXP 2 + n) DIV (4 * (A + 1)))) IN s) /\
                             (qf_reduced (&(A + 1)) (--(&B))
                               (&((B EXP 2 + n) DIV (4 * (A + 1)))) /\
                              gcd(&(A + 1),gcd(--(&B),
                                  &((B EXP 2 + n) DIV (4 * (A + 1))))) = &1
                              ==> (&(A + 1),--(&B),
                                   &((B EXP 2 + n) DIV (4 * (A + 1)))) IN s))
        ==> form_classno (--(&n)) = CARD s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
  REWRITE_TAC[form_classno] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; QF_FORMS_IN] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP QF_REDUCED_BOUNDS) THEN
  SUBGOAL_THEN `&3 * a pow 2 <= &n:int` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP QF_REDUCED_DISC) THEN
    UNDISCH_TAC `b pow 2 - &4 * a * c = --(&n:int)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= &m:int` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&m + &1:int) pow 2 <= a pow 2` MP_TAC THENL
     [MATCH_MP_TAC INT_POW_LE2 THEN UNDISCH_TAC `&m < a:int` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `n < 3 * (m + 1) EXP 2` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW;
                GSYM INT_OF_NUM_ADD] THEN
    UNDISCH_TAC `&3 * a pow 2 <= &n:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INT_ARITH `&0 < a:int ==> &0 <= a - &1`)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS; INT_OF_NUM_ADD;
              INT_ARITH `a - &1:int = x <=> a = x + &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `A < m` ASSUME_TAC THENL
   [UNDISCH_TAC `&(A + 1) <= &m:int` THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. (b:int = &B \/ b = --(&B)) /\ B < m + 1`
  (X_CHOOSE_THEN `B:num` (CONJUNCTS_THEN ASSUME_TAC)) THENL
   [EXISTS_TAC `num_of_int(abs b)` THEN
    SUBGOAL_THEN `&(num_of_int(abs b)) = abs b:int` MP_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN REWRITE_TAC[INT_ABS_POS];
      ALL_TAC] THEN
    SPEC_TAC(`num_of_int(abs b)`,`B:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&B = abs b:int` THEN REWRITE_TAC[INT_ABS] THEN
      COND_CASES_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_NEG_NEG];
      REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD] THEN
      MAP_EVERY UNDISCH_TAC
       [`&B = abs b:int`; `abs b <= &(A + 1):int`; `&(A + 1) <= &m:int`] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&B pow 2 - &4 * &(A + 1) * c = --(&n:int)` MP_TAC THENL
   [UNDISCH_TAC `b pow 2 - &4 * &(A + 1) * c = --(&n:int)` THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[INT_POW_2; INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[QF_SOLVE_C] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  REMOVE_THEN "H" (fun th ->
    MP_TAC(MP (SPEC `B:num` (MP (SPEC `A:num` th) (ASSUME `A < m`)))
              (ASSUME `B < m + 1`))) THEN
  REWRITE_TAC[ASSUME `(B EXP 2 + n) MOD (4 * (A + 1)) = 0`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1); DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[]);;

(* FORM_CLASSNO_CONV maps the term form_classno (--(&n)), n a numeral, to   *)
(* the theorem form_classno (--(&n)) = k: it lists the reduced primitive    *)
(* forms (a <= m = isqrt(n DIV 3), abs b <= a, c solved from the            *)
(* discriminant) and proves the hypotheses of QF_FORMS_EVAL for that set.   *)

let FORM_CLASSNO_CONV =
  let mk_int k =
    if k < 0 then mk_comb(`int_neg`,mk_comb(`int_of_num`,mk_small_numeral(-k)))
    else mk_comb(`int_of_num`,mk_small_numeral k) in
  let rec isqrt n r = if (r + 1) * (r + 1) <= n then isqrt n (r + 1) else r in
  let rec gcd a b = if b = 0 then abs a else gcd b (a mod b) in
  let reduced (a,b,c) =
    0 < a && abs b <= a && a <= c && (not(abs b = a || a = c) || 0 <= b) in
  let forms n m =
    let rec loopa a acc =
      if a > m then rev acc else
      let rec loopb b acc =
        if b > m then acc else
        let k = b * b + n in
        if k mod (4 * a) <> 0 then loopb (b + 1) acc else
        let c = k / (4 * a) in
        let cands = if b = 0 then [(a,0,c)] else [(a,b,c); (a,-b,c)] in
        let good = filter (fun (a,b,c) -> reduced (a,b,c) &&
                                          gcd a (gcd b c) = 1) cands in
        loopb (b + 1) (rev good @ acc) in
      loopa (a + 1) (loopb 0 acc) in
    loopa 1 [] in
  let gcd_conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV [INT_GCD_RNEG; INT_GCD_LNEG] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM NUM_GCD] THENC
    DEPTH_CONV GCD_CONV in
  let fin_conv =
    NUM_REDUCE_CONV THENC REWRITE_CONV[qf_reduced] THENC gcd_conv THENC
    INT_REDUCE_CONV THENC REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THENC
    INT_REDUCE_CONV THENC REWRITE_CONV[] in
  let card_conv =
    let pth0 = prove
     (`CARD({}:int#int#int->bool) = 0`, REWRITE_TAC[CARD_CLAUSES])
    and pth1 = prove
     (`!x:int#int#int s. FINITE s /\ ~(x IN s)
                         ==> CARD(x INSERT s) = SUC(CARD s)`,
      SIMP_TAC[CARD_CLAUSES])
    and ant_conv =
      REWRITE_CONV[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
                   PAIR_EQ] THENC INT_REDUCE_CONV THENC REWRITE_CONV[] in
    let rec conv tm =
      match rand tm with
        Comb(Comb(Const("INSERT",_),x),s) ->
          let th = SPECL [x; s] pth1 in
          let th1 = MP th (EQT_ELIM(ant_conv(lhand(concl th)))) in
          TRANS th1 (AP_TERM `SUC` (conv(rand(rand(concl th1)))))
      | _ -> pth0 in
    conv THENC NUM_REDUCE_CONV in
  let ty = `:int#int#int` and fc = `form_classno` in
  fun tm ->
    let f,arg = dest_comb tm in
    if f <> fc then failwith "FORM_CLASSNO_CONV" else
    let n = dest_small_numeral(rand(rand arg)) in
    if arg <> mk_comb(`int_neg`,mk_comb(`int_of_num`,mk_small_numeral n))
    then failwith "FORM_CLASSNO_CONV" else
    let m = isqrt (n / 3) 0 in
    let fs = forms n m in
    let s = mk_setenum(map (fun (a,b,c) ->
              mk_pair(mk_int a,mk_pair(mk_int b,mk_int c))) fs, ty) in
    let th = SPECL [mk_small_numeral n; mk_small_numeral m; s] QF_FORMS_EVAL in
    let ath = prove(lhand(concl th),
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN REPEAT GEN_TAC THEN
        DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
          (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC)) THEN
        CONV_TAC fin_conv;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
        CONV_TAC fin_conv]) in
    let th1 = MP th ath in
    TRANS th1 (card_conv(rand(concl th1)));;

(* ------------------------------------------------------------------------- *)
(* Finite case analysis on residues: generalise the terms t MOD k (numeral   *)
(* k) of the list to variables below k and expand all cases.                 *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_FORMS_MOD_CASES_TAC (tms:term list) : tactic =
  let gen_tac tm =
    let v = genvar `:num` in
    SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,tm),rand tm))
    MP_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SPEC_TAC(tm,v) in
  MAP_EVERY gen_tac tms THEN
  MAP_EVERY (fun _ -> CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) tms THEN
  CONV_TAC NUM_REDUCE_CONV;;

let CLASSNO_FORMS_SQUARE_MOD4 = prove
 (`!n d. (n EXP 2 + d) MOD 4 = 0 /\ ~(d MOD 4 = 0) ==> d MOD 4 = 3`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  ONCE_REWRITE_TAC[GSYM MOD_EXP_MOD] THEN
  CLASSNO_FORMS_MOD_CASES_TAC [`n MOD 4`; `d MOD 4`]);;

let CLASSNO_FORMS_SQUAREFREE_MOD4 = prove
 (`!d. squarefree d ==> ~(d MOD 4 = 0)`,
  GEN_TAC THEN REWRITE_TAC[squarefree] THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[DIVIDES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CLASSNO_FORMS_MOD4 = prove
 (`!b:int d. &4 divides (b pow 2 + &d) /\ squarefree d ==> d MOD 4 = 3`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
  MP_TAC(SPEC `abs b:int` INT_OF_NUM_OF_INT) THEN REWRITE_TAC[INT_ABS_POS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SPEC_TAC(`num_of_int(abs b)`,`n:num`) THEN GEN_TAC THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_ADD; GSYM num_divides;
              DIVIDES_MOD] THEN
  STRIP_TAC THEN MATCH_MP_TAC CLASSNO_FORMS_SQUARE_MOD4 THEN
  EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[CLASSNO_FORMS_SQUAREFREE_MOD4]);;

(* ------------------------------------------------------------------------- *)
(* The witness lemma: a reduced form (a,|b|,c) with a >= 2 of discriminant   *)
(* -d (c = (b^2 + d)/(4a)) besides the principal form.                       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_WITNESS = prove
 (`!d a b. &2 <= a /\ abs b <= a /\ &4 * a pow 2 <= b pow 2 + &d /\
          (&4 * a) divides (b pow 2 + &d) /\ squarefree d
          ==> ~(form_classno (--(&d)) = 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `d MOD 4 = 3` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_FORMS_MOD4 THEN EXISTS_TAC `b:int` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(&4 * a) divides (b pow 2 + &d:int)` THEN
    MATCH_ACCEPT_TAC
     (INTEGER_RULE `!x y z:int. (x * y) divides z ==> x divides z`);
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `c:int` o REWRITE_RULE[int_divides]) THEN
  SUBGOAL_THEN `abs b pow 2 - &4 * a * c = --(&d:int)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_POW2_ABS] THEN
    UNDISCH_TAC `b pow 2 + &d = (&4 * a) * c:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= c:int` ASSUME_TAC THENL
   [SUBGOAL_THEN `a * a <= a * c:int` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`b pow 2 + &d = (&4 * a) * c:int`;
        `&4 * a pow 2 <= b pow 2 + &d:int`] THEN
      INT_ARITH_TAC;
      MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
      MATCH_MP_TAC INT_LE_LMUL_EQ THEN
      UNDISCH_TAC `&2 <= a:int` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `qf_reduced a (abs b) c` ASSUME_TAC THENL
   [REWRITE_TAC[qf_reduced; INT_ABS_ABS; INT_ABS_POS] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&2 <= a:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `gcd(a:int,gcd(abs b,c)) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`--(&d:int)`; `&1:int`; `&1:int`; `&((d + 1) DIV 4):int`;
                `a:int`; `abs b:int`; `c:int`] CLASSNO_FORMS_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLASSNO_PRINCIPAL_REDUCED; INT_GCD_1];
    UNDISCH_TAC `&2 <= a:int` THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Genus theory by witnesses: CLASSNO_ONE_CASES.                             *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_FORMS_MOD4_CASES = prove
 (`!d. squarefree d ==> d MOD 4 = 1 \/ d MOD 4 = 2 \/ d MOD 4 = 3`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLASSNO_FORMS_SQUAREFREE_MOD4) THEN
  CLASSNO_FORMS_MOD_CASES_TAC [`d MOD 4`]);;

let CLASSNO_FORMS_MOD8_CASES = prove
 (`!d. d MOD 4 = 3 ==> d MOD 8 = 3 \/ d MOD 8 = 7`,
  GEN_TAC THEN
  SUBGOAL_THEN `d MOD 4 = (d MOD 8) MOD 4` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 = 4 * 2`; MOD_MOD];
    CLASSNO_FORMS_MOD_CASES_TAC [`d MOD 8`]]);;

let CLASSNO_FORMS_PRODUCT_MOD4 = prove
 (`!m n. (m * n) MOD 4 = 3 ==> (m + n) MOD 4 = 0`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2; GSYM MOD_ADD_MOD] THEN
  CLASSNO_FORMS_MOD_CASES_TAC [`m MOD 4`; `n MOD 4`]);;

(* d = 1 mod 4, d > 1: the forms (1,0,d) and (2,2,(d+1)/2) of disc -4d.      *)

let CLASSNO_FORMS_MOD4_1 = prove
 (`!d. d MOD 4 = 1 /\ ~(d = 1) ==> ~(form_classno(--(&4 * &d)) = 1)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `k = d DIV 4` THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`d = k * 4 + 1`; `~(d = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&d:int = &4 * &k + &1 /\ &1:int <= &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
                INT_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 4 + 1`; `1 <= k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `qf_reduced (&1) (&0) (&d) /\
                &0 pow 2 - &4 * &1 * &d = --(&4 * &d:int) /\
                gcd(&1:int,gcd(&0,&d)) = &1 /\
                qf_reduced (&2) (&2) (&2 * &k + &1) /\
                &2 pow 2 - &4 * &2 * (&2 * &k + &1) = --(&4 * &d:int) /\
                gcd(&2:int,gcd(&2,&2 * &k + &1)) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[qf_reduced] THEN CONV_TAC INT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC QF_PRIMITIVE_BEZOUT) THENL
     [UNDISCH_TAC `&d:int = &4 * &k + &1` THEN INT_ARITH_TAC;
      INT_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`; `&0:int`] THEN INT_ARITH_TAC;
      UNDISCH_TAC `&1:int <= &k` THEN INT_ARITH_TAC;
      UNDISCH_TAC `&d:int = &4 * &k + &1` THEN INT_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`--(&k):int`; `&0:int`; `&1:int`] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`--(&4 * &d:int)`; `&1:int`; `&0:int`; `&d:int`;
                `&2:int`; `&2:int`; `&2 * &k + &1:int`]
         CLASSNO_FORMS_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; INT_ARITH_TAC]);;

(* d = 2 mod 4, d > 2: the forms (1,0,d) and (2,0,d/2) of disc -4d.          *)

let CLASSNO_FORMS_MOD4_2 = prove
 (`!d. d MOD 4 = 2 /\ ~(d = 2) ==> ~(form_classno(--(&4 * &d)) = 1)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `k = d DIV 4` THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`d = k * 4 + 2`; `~(d = 2)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&d:int = &4 * &k + &2 /\ &1:int <= &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
                INT_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 4 + 2`; `1 <= k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `qf_reduced (&1) (&0) (&d) /\
                &0 pow 2 - &4 * &1 * &d = --(&4 * &d:int) /\
                gcd(&1:int,gcd(&0,&d)) = &1 /\
                qf_reduced (&2) (&0) (&2 * &k + &1) /\
                &0 pow 2 - &4 * &2 * (&2 * &k + &1) = --(&4 * &d:int) /\
                gcd(&2:int,gcd(&0,&2 * &k + &1)) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[qf_reduced] THEN CONV_TAC INT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC QF_PRIMITIVE_BEZOUT) THENL
     [UNDISCH_TAC `&d:int = &4 * &k + &2` THEN INT_ARITH_TAC;
      INT_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`; `&0:int`] THEN INT_ARITH_TAC;
      UNDISCH_TAC `&1:int <= &k` THEN INT_ARITH_TAC;
      UNDISCH_TAC `&d:int = &4 * &k + &2` THEN INT_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`--(&k):int`; `&0:int`; `&1:int`] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`--(&4 * &d:int)`; `&1:int`; `&0:int`; `&d:int`;
                `&2:int`; `&0:int`; `&2 * &k + &1:int`]
         CLASSNO_FORMS_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; INT_ARITH_TAC]);;

(* d = 7 mod 8, d > 7: the witness (2,1).                                    *)

let CLASSNO_FORMS_MOD8_7 = prove
 (`!d. squarefree d /\ d MOD 8 = 7 /\ ~(d = 7) ==> ~(form_classno(--(&d)) = 1)`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CLASSNO_WITNESS THEN
  MAP_EVERY EXISTS_TAC [`&2:int`; `&1:int`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `k = d DIV 8` THEN
  SUBGOAL_THEN `&d:int = &8 * &k + &7 /\ &1:int <= &k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
                INT_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 8 + 7`; `~(d = 7)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[int_divides] THEN CONV_TAC INT_REDUCE_CONV THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&1:int <= &k` THEN INT_ARITH_TAC;
    EXISTS_TAC `&k + &1:int` THEN INT_ARITH_TAC]);;

(* The ambiguous form of a factorisation d = m n (1 < m < n, d = 3 mod 4):   *)
(* (m,m,(m+n)/4) if n >= 3m, ((m+n)/4,(n-m)/2,(m+n)/4) if n < 3m; m is       *)
(* recovered from the form (a,b,c) as a (first family, a = b) or as 2a - b   *)
(* (second family, b < a).                                                   *)

let QFORM_AMBIGUOUS_WITNESS = prove
 (`!d m n. d = m * n /\ 1 < m /\ m < n /\ d MOD 4 = 3
           ==> ?a b c. qf_reduced a b c /\
                       b pow 2 - &4 * a * c = --(&d) /\ &2 <= a /\
                       (a = b /\ a = &m \/ b < a /\ &2 * a - b = &m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `d:num`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLASSNO_FORMS_PRODUCT_MOD4) THEN
  REWRITE_TAC[MOD_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `t:num`) THEN
  ASM_CASES_TAC `3 * m <= n` THENL
   [MAP_EVERY EXISTS_TAC [`&m:int`; `&m:int`; `&t:int`] THEN
    REWRITE_TAC[qf_reduced; INT_ABS_NUM; INT_OF_NUM_LT; INT_OF_NUM_LE] THEN
    REWRITE_TAC[INT_ARITH `x - y = --z <=> z + x = y:int`] THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
                INT_OF_NUM_EQ] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 < m` THEN ARITH_TAC;
      ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`m + n = t * 4`; `3 * m <= n`] THEN ARITH_TAC;
      ARITH_TAC;
      UNDISCH_TAC `m + n = t * 4` THEN CONV_TAC NUM_RING;
      UNDISCH_TAC `1 < m` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u. m + u = 2 * t /\ n = 2 * t + u` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `2 * t - m` THEN
    MAP_EVERY UNDISCH_TAC [`m + n = t * 4`; `m < n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&t:int`; `&u:int`; `&t:int`] THEN
  REWRITE_TAC[qf_reduced; INT_ABS_NUM; INT_OF_NUM_LT; INT_OF_NUM_LE] THEN
  REWRITE_TAC[INT_ARITH `x - y = --z <=> z + x = y:int`;
              INT_ARITH `x - y = z <=> x = z + y:int`] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
              INT_OF_NUM_EQ] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m + n = t * 4`; `1 < m`] THEN ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`m + u = 2 * t`; `n = 2 * t + u`; `~(3 * m <= n)`]
    THEN ARITH_TAC;
    ARITH_TAC;
    ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`m + u = 2 * t`; `n = 2 * t + u`] THEN
    CONV_TAC NUM_RING;
    MAP_EVERY UNDISCH_TAC [`m + n = t * 4`; `1 < m`; `m < n`] THEN ARITH_TAC;
    DISJ2_TAC THEN
    MAP_EVERY UNDISCH_TAC [`m + u = 2 * t`; `n = 2 * t + u`; `~(3 * m <= n)`]
    THEN ARITH_TAC]);;

(* d = 3 mod 4 composite, d = m n with 1 < m <= n: the ambiguous form is a   *)
(* second reduced primitive form.                                            *)

let CLASSNO_FORMS_COMPOSITE = prove
 (`!m n. 1 < m /\ m <= n /\ squarefree(m * n) /\ (m * n) MOD 4 = 3
         ==> ~(form_classno(--(&(m * n))) = 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m < n` ASSUME_TAC THENL
   [REWRITE_TAC[LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `squarefree(n * n)` THEN REWRITE_TAC[squarefree] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[EXP_2; DIVIDES_REFL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m * n`; `m:num`; `n:num`] QFORM_AMBIGUOUS_WITNESS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int`
    (X_CHOOSE_THEN `c:int` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (K ALL_TAC))))))) THEN
  MP_TAC(SPEC `m * n` CLASSNO_PRINCIPAL_REDUCED) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`--(&(m * n)):int`; `&1:int`; `&1:int`;
                `&((m * n + 1) DIV 4):int`; `a:int`; `b:int`; `c:int`]
    CLASSNO_FORMS_UNIQUE) THEN
  ASM_REWRITE_TAC[INT_GCD_1] THEN
  SUBGOAL_THEN `gcd(a,gcd(b,c)) = &1` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `m * n` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `&2 <= a:int` THEN INT_ARITH_TAC]);;

let CLASSNO_FORMS_NONPRIME = prove
 (`!d. ~prime d /\ ~(d = 0) /\ ~(d = 1) ==> ?m n. d = m * n /\ 1 < m /\ m <= n`,
  GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~prime d` THEN
  ASM_REWRITE_TAC[prime; NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:num` o REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `1 < x /\ 1 < y` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `d = x * y` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      ALL_TAC] THEN
    ASM_CASES_TAC `y = 0` THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `d = x * y` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      ALL_TAC] THEN
    ASM_CASES_TAC `y = 1` THENL
     [UNDISCH_TAC `d = x * y` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
      UNDISCH_TAC `~(x:num = d)` THEN
      CONV_TAC(LAND_CONV(RAND_CONV SYM_CONV)) THEN MESON_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`~(x = 0)`; `~(x = 1)`; `~(y = 0)`; `~(y = 1)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THENL
   [MAP_EVERY EXISTS_TAC [`x:num`; `y:num`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`y:num`; `x:num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_SYM]]);;

let CLASSNO_ONE_CASES = prove
 (`!d. squarefree d /\ form_classno (qdisc d) = 1
      ==> d = 1 \/ d = 2 \/ d = 7 \/ (prime d /\ d MOD 8 = 3)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLASSNO_FORMS_MOD4_CASES) THENL
   [UNDISCH_TAC `form_classno (qdisc d) = 1` THEN
    ASM_REWRITE_TAC[qdisc; ARITH_EQ] THEN DISCH_TAC THEN
    ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `d:num` CLASSNO_FORMS_MOD4_1) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `form_classno (qdisc d) = 1` THEN
    ASM_REWRITE_TAC[qdisc; ARITH_EQ] THEN DISCH_TAC THEN
    ASM_CASES_TAC `d = 2` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `d:num` CLASSNO_FORMS_MOD4_2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `form_classno (qdisc d) = 1` THEN
  ASM_REWRITE_TAC[qdisc] THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP CLASSNO_FORMS_MOD8_CASES) THENL
   [ALL_TAC;
    ASM_CASES_TAC `d = 7` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `d:num` CLASSNO_FORMS_MOD8_7) THEN ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `prime d` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(d = 0) /\ ~(d = 1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `d MOD 8 = 3` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CLASSNO_FORMS_NONPRIME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num`
   (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`m:num`; `n:num`] CLASSNO_FORMS_COMPOSITE) THEN
  UNDISCH_TAC `d = m * n` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The nine discriminants of Gauss with class number one.                    *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_NINE = prove
 (`!d. d IN {1,2,3,7,11,19,43,67,163} ==> form_classno (qdisc d) = 1`,
  GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[qdisc] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV FORM_CLASSNO_CONV THENC NUM_REDUCE_CONV));;

(* ------------------------------------------------------------------------- *)
(* The search for witnesses up to 46500 (d = 3 mod 8, d not one of the six   *)
(* with class number one): d = 840 q + r; for 99 of the 105 residues r a     *)
(* witness (a,b) with a in {3,5,7} (4a divides 840) works for all q; the     *)
(* remaining 330 d (residues 43, 67, 163, 403, 547, 667) are in the table    *)
(* classno_search_table (found by a computer search; checked here).          *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_FORMS_WITNESS_NUM = prove
 (`!d x y. 2 <= x /\ y <= x /\ 4 * x EXP 2 <= y EXP 2 + d /\
           (y EXP 2 + d) MOD (4 * x) = 0
           ==> ?a b. &2 <= a /\ abs b <= a /\ &4 * a pow 2 <= b pow 2 + &d /\
                     (&4 * a) divides (b pow 2 + &d:int)`,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`&x:int`; `&y:int`] THEN
  ASM_REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_LE; INT_OF_NUM_POW; INT_OF_NUM_MUL;
                  INT_OF_NUM_ADD; GSYM num_divides; DIVIDES_MOD]);;

let CLASSNO_FORMS_SEARCH_RES = prove
 (`!r x y. 2 <= x /\ y <= x /\ (y EXP 2 + r) MOD (4 * x) = 0 /\
           840 MOD (4 * x) = 0
           ==> !q. 4 * x EXP 2 <= y EXP 2 + 840 * q + r
                   ==> ?a b. &2 <= a /\ abs b <= a /\
                             &4 * a pow 2 <= b pow 2 + &(840 * q + r) /\
                             (&4 * a) divides (b pow 2 + &(840 * q + r):int)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLASSNO_FORMS_WITNESS_NUM THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `y:num`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`840 MOD (4 * x) = 0`; `(y EXP 2 + r) MOD (4 * x) = 0`] THEN
  REWRITE_TAC[GSYM DIVIDES_MOD] THEN SPEC_TAC(`y EXP 2`,`z:num`) THEN
  SPEC_TAC(`4 * x`,`k:num`) THEN SPEC_TAC(`840`,`m:num`) THEN
  CONV_TAC NUMBER_RULE);;

let CLASSNO_FORMS_SEARCH_RES_ALL = prove
 (`!r x y. 2 <= x /\ y <= x /\ (y EXP 2 + r) MOD (4 * x) = 0 /\
           840 MOD (4 * x) = 0 /\ 4 * x EXP 2 <= y EXP 2 + r
           ==> !q. 840 * q + r <= 46500 /\
                   ~(840 * q + r IN {3,11,19,43,67,163})
                   ==> ?a b. &2 <= a /\ abs b <= a /\
                             &4 * a pow 2 <= b pow 2 + &(840 * q + r) /\
                             (&4 * a) divides (b pow 2 + &(840 * q + r):int)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:num`; `x:num`; `y:num`] CLASSNO_FORMS_SEARCH_RES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `4 * x EXP 2 <= y EXP 2 + r` THEN ARITH_TAC);;

let CLASSNO_FORMS_BOUNDED_Q = prove
 (`!P r. (!q. q < 56 ==> 840 * q + r <= 46500 ==> P q)
         ==> (!q. 840 * q + r <= 46500 ==> P q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `840 * q + r <= 46500` THEN
  ARITH_TAC);;

(* The table: triples (d,a,b) with 2 <= a, 0 <= b <= a, 4a | b^2 + d and     *)
(* 4a^2 <= b^2 + d.                                                          *)

let classno_search_table = [
  (403,11,9); (547,11,5); (667,11,9); (883,13,1); (907,13,9); (1003,11,3);
  (1243,11,11); (1387,13,11); (1507,11,11); (1723,11,9); (1747,17,15);
  (1843,11,7); (2083,13,7); (2227,13,3); (2347,17,13); (2563,11,11);
  (2587,11,3); (2683,11,1); (2923,11,5); (3067,13,1); (3187,11,5);
  (3403,13,9); (3427,11,7); (3523,13,13); (3763,23,3); (3907,11,3);
  (4027,13,9); (4243,11,5); (4267,11,1); (4363,11,9); (4603,13,5);
  (4747,11,7); (4867,19,15); (5083,13,13); (5107,19,17); (5203,11,11);
  (5443,13,11); (5587,11,1); (5707,13,13); (5923,19,9); (5947,11,9);
  (6043,17,3); (6283,11,3); (6427,17,13); (6547,11,3); (6763,13,7);
  (6787,11,11); (6883,11,5); (7123,11,7); (7267,11,9); (7387,11,7);
  (7603,11,3); (7627,13,11); (7723,13,5); (7963,11,1); (8107,11,11);
  (8227,11,1); (8443,11,7); (8467,11,5); (8563,13,11); (8803,23,11);
  (8947,13,7); (9067,23,15); (9283,11,1); (9307,13,1); (9403,13,3);
  (9643,11,9); (9787,11,5); (9907,11,9); (10123,13,11); (10147,17,11);
  (10243,11,3); (10483,11,11); (10627,17,7); (10747,11,11); (10963,11,9);
  (10987,29,27); (11083,11,7); (11323,13,13); (11467,13,5); (11587,13,3);
  (11803,11,11); (11827,11,3); (11923,11,1); (12163,11,5); (12307,13,11);
  (12427,11,5); (12643,19,7); (12667,11,7); (12763,13,9); (13003,13,7);
  (13147,11,3); (13267,23,21); (13483,11,5); (13507,11,1); (13603,11,9);
  (13843,23,7); (13987,11,7); (14107,29,25); (14323,13,9); (14347,17,1);
  (14443,11,11); (14683,19,17); (14827,11,1); (14947,13,9); (15163,17,1);
  (15187,11,9); (15283,17,17); (15523,11,3); (15667,29,15); (15787,11,3);
  (16003,13,13); (16027,11,11); (16123,11,5); (16363,11,7); (16507,11,9);
  (16627,11,7); (16843,11,3); (16867,19,9); (16963,19,17); (17203,11,1);
  (17347,11,11); (17467,11,1); (17683,11,7); (17707,11,5); (17803,17,9);
  (18043,13,1); (18187,13,13); (18307,13,7); (18523,11,1); (18547,13,11);
  (18643,13,5); (18883,11,9); (19027,11,5); (19147,11,9); (19363,17,17);
  (19387,13,3); (19483,11,3); (19723,11,11); (19867,13,7); (19987,11,11);
  (20203,11,9); (20227,13,1); (20323,11,7); (20563,13,9); (20707,17,13);
  (20827,13,5); (21043,11,11); (21067,11,3); (21163,11,1); (21403,11,5);
  (21547,17,3); (21667,11,5); (21883,13,3); (21907,11,7); (22003,23,13);
  (22243,13,13); (22387,11,3); (22507,13,3); (22723,11,5); (22747,11,1);
  (22843,11,9); (23083,23,3); (23227,11,7); (23347,13,1); (23563,17,13);
  (23587,17,3); (23683,11,11); (23923,13,7); (24067,11,1); (24187,17,15);
  (24403,17,3); (24427,11,9); (24523,17,5); (24763,11,3); (24907,13,1);
  (25027,11,3); (25243,13,9); (25267,11,11); (25363,11,5); (25603,11,7);
  (25747,11,9); (25867,11,7); (26083,11,3); (26107,13,7); (26203,19,13);
  (26443,11,1); (26587,11,11); (26707,11,1); (26923,11,7); (26947,11,5);
  (27043,13,7); (27283,13,11); (27427,13,9); (27547,13,13); (27763,11,1);
  (27787,17,5); (27883,19,3); (28123,11,9); (28267,11,5); (28387,11,9);
  (28603,13,7); (28627,13,5); (28723,11,3); (28963,11,11); (29107,13,13);
  (29227,11,11); (29443,11,9); (29467,13,11); (29563,11,7); (29803,17,7);
  (29947,19,15); (30067,29,21); (30283,11,11); (30307,11,3); (30403,11,1);
  (30643,11,5); (30787,13,7); (30907,11,5); (31123,13,5); (31147,11,7);
  (31243,13,3); (31483,13,9); (31627,11,3); (31747,13,5); (31963,11,5);
  (31987,11,1); (32083,11,9); (32323,31,17); (32467,11,7); (32587,13,11);
  (32803,13,3); (32827,17,17); (32923,11,11); (33163,13,13); (33307,11,1);
  (33427,13,3); (33643,13,1); (33667,11,9); (33763,17,13); (34003,11,3);
  (34147,13,11); (34267,11,3); (34483,31,19); (34507,11,11); (34603,11,5);
  (34843,11,7); (34987,11,9); (35107,11,7); (35323,11,3); (35347,13,13);
  (35443,17,11); (35683,11,1); (35827,11,11); (35947,11,1); (36163,11,7);
  (36187,11,5); (36283,13,13); (36523,23,1); (36667,17,11); (36787,13,9);
  (37003,11,1); (37027,13,7); (37123,37,5); (37363,11,9); (37507,11,5);
  (37627,11,9); (37843,13,13); (37867,17,3); (37963,11,3); (38203,11,11);
  (38347,13,9); (38467,11,11); (38683,11,9); (38707,17,11); (38803,11,7);
  (39043,13,3); (39187,17,7); (39307,19,17); (39523,11,11); (39547,11,3);
  (39643,11,1); (39883,11,5); (40027,13,13); (40147,11,5); (40363,23,5);
  (40387,11,7); (40483,13,5); (40723,17,3); (40867,11,3); (40987,17,17);
  (41203,11,5); (41227,11,1); (41323,11,9); (41563,17,11); (41707,11,7);
  (41827,19,7); (42043,13,5); (42067,13,1); (42163,11,11); (42403,13,9);
  (42547,11,1); (42667,13,5); (42883,13,11); (42907,11,9); (43003,13,1);
  (43243,11,3); (43387,19,3); (43507,11,3); (43723,13,3); (43747,11,11);
  (43843,11,5); (44083,11,7); (44227,11,9); (44347,11,7); (44563,11,3);
  (44587,13,9); (44683,19,9); (44923,11,1); (45067,11,11); (45187,11,1);
  (45403,11,7); (45427,11,5); (45523,13,9); (45763,13,7); (45907,13,3);
  (46027,17,3); (46243,11,1); (46267,13,13); (46363,17,9)
];;

let CLASSNO_FORMS_DIRECT_WITNESS d =
  let mk = mk_small_numeral in
  let (_,a,b) = find (fun (d',_,_) -> d' = d) classno_search_table in
  let th = SPECL [mk d; mk a; mk b] CLASSNO_FORMS_WITNESS_NUM in
  MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

(* For a goal d <= 46500 ==> ~(d IN six) ==> W d (or with /\), d a numeral.  *)

let CLASSNO_FORMS_DIRECT_TAC : tactic =
  let rec imp_concl t = if is_imp t then imp_concl(rand t) else t in
  let wnum w =
    let bod = snd(strip_exists(imp_concl w)) in
    try dest_small_numeral(rand(rand(rand(el 2 (conjuncts bod)))))
    with Failure _ -> 0 in
  W(fun (asl,w) ->
     let d = wnum w in
     if exists (fun (d',_,_) -> d' = d) classno_search_table then
       REPEAT DISCH_TAC THEN ACCEPT_TAC(CLASSNO_FORMS_DIRECT_WITNESS d)
     else
       CONV_TAC(NUM_REDUCE_CONV THENC
                REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY] THENC
                NUM_REDUCE_CONV THENC REWRITE_CONV[]));;

(* For a goal !q. 840 * q + r <= 46500 /\ ~(840 * q + r IN six)              *)
(* ==> W(840 * q + r), r a numeral: the residue lemma with a in {3,5,7}      *)
(* (for r in {3,11,19} only for q > 0, q = 0 giving one of the six), or      *)
(* q < 56 and the table.                                                     *)

let CLASSNO_FORMS_RESIDUE_TAC : tactic = fun (asl,w) ->
  let q,bod = dest_forall w in
  let r = dest_small_numeral(rand(lhand(lhand(lhand bod)))) in
  let cands = [3,0; 3,1; 3,2; 3,3; 5,0; 5,1; 5,2; 5,3; 5,4; 5,5;
               7,0; 7,1; 7,2; 7,3; 7,4; 7,5; 7,6; 7,7] in
  match filter (fun (a,b) -> (b * b + r) mod (4 * a) = 0) cands with
    (a,b)::_ ->
      let mk = mk_small_numeral in
      if 4 * a * a <= b * b + r then
        let th = SPECL [mk r; mk a; mk b] CLASSNO_FORMS_SEARCH_RES_ALL in
        ACCEPT_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) (asl,w)
      else
        let th = SPECL [mk r; mk a; mk b] CLASSNO_FORMS_SEARCH_RES in
        let th = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
        (X_GEN_TAC q THEN ASM_CASES_TAC (mk_eq(q,`0`)) THENL
          [ASM_REWRITE_TAC[] THEN CLASSNO_FORMS_DIRECT_TAC;
           DISCH_TAC THEN MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN
           UNDISCH_TAC (mk_neg(mk_eq(q,`0`))) THEN ARITH_TAC]) (asl,w)
  | [] ->
      (REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC CLASSNO_FORMS_BOUNDED_Q THEN
       CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
       REPEAT CONJ_TAC THEN CLASSNO_FORMS_DIRECT_TAC) (asl,w);;

let CLASSNO_SEARCH = prove
 (`!d. d <= 46500 /\ d MOD 8 = 3 /\ ~(d IN {3,11,19,43,67,163})
      ==> ?a b. &2 <= a /\ abs b <= a /\ &4 * a pow 2 <= b pow 2 + &d /\
                (&4 * a) divides (b pow 2 + &d:int)`,
  SUBGOAL_THEN
   `!j. j < 105
        ==> !q. 840 * q + 8 * j + 3 <= 46500 /\
                ~(840 * q + 8 * j + 3 IN {3,11,19,43,67,163})
                ==> ?a b. &2 <= a /\ abs b <= a /\
                          &4 * a pow 2 <= b pow 2 + &(840 * q + 8 * j + 3) /\
                          (&4 * a) divides
                          (b pow 2 + &(840 * q + 8 * j + 3):int)`
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN CLASSNO_FORMS_RESIDUE_TAC;
    ALL_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q j. j < 105 /\ d = 840 * q + 8 * j + 3` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`d DIV 840`; `(d MOD 840) DIV 8`] THEN
    MP_TAC(SPECL [`d:num`; `840`] DIVISION) THEN
    MP_TAC(SPECL [`d MOD 840`; `8`] DIVISION) THEN
    SUBGOAL_THEN `(d MOD 840) MOD 8 = 3` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[ARITH_RULE `840 = 8 * 105`; MOD_MOD] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
