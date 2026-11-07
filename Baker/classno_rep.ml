(* ========================================================================= *)
(* Representation numbers of positive definite binary quadratic forms; the   *)
(* representation numbers of the principal form when the class number is     *)
(* one.                                                                      *)
(*                                                                           *)
(* Purpose: counting tools for the integer points on a x^2 + b x y + c y^2   *)
(* = n, shared with the class number two problem (section 22): finiteness    *)
(* (QFORM_REP_FINITE), linear substitutions of nonzero determinant           *)
(* (QFORM_REP_LINEAR_IMAGE, QFORM_REP_LINEAR_CARD), scaling                  *)
(* (QFORM_CARD_SCALE), multiplication by pi in Z[w] (QFORM_REP_CARD_MUL_P),  *)
(* the splitting of a prime (QFORM_REP_SPLIT_DECOMP), inert primes           *)
(* (QFORM_REP_INERT2, QFORM_REP_INERT_DIVIDES), the divisor sums of          *)
(* convolutions (QFORM_REP_DIVSUM_CONV_REC). For d prime, d = 3 mod 4, d > 3 *)
(* and form_classno(-d) = 1, the number r(l) of integer pairs (x,y) with x^2 *)
(* + x y + c y^2 = l, c = (1 + d) / 4, is 2 times the sum over the divisors  *)
(* m of l of the Jacobi symbol (m | d) (CLASSNO_REPRESENTATION).             *)
(* This is the case of one class of the formula of Dirichlet for the         *)
(* representation numbers of the forms of a discriminant (Landau,            *)
(* Vorlesungen ueber Zahlentheorie, Satz 204), the expansion of              *)
(* L(s, chi_k) L(s, chi_kd) as a lattice sum in Baker, Transcendental Number *)
(* Theory, Ch. 5, sec. 2; it is the only place of the analytic argument      *)
(* where the class number hypothesis is used.                                *)
(*                                                                           *)
(* Method: the arithmetic of Z[w], w = (1 + sqrt(-d)) / 2, on integer pairs: *)
(* (a,b) (u,v) = (a u - c b v, a v + b u + b v), conj (a,b) = (a + b, -b),   *)
(* and the norm N(x,y) = prin_form d x y = (x,y) conj(x,y) is                *)
(* multiplicative; multiplication by pi is a linear substitution of          *)
(* determinant N pi. For a prime p the representation numbers satisfy        *)
(* r(p n) = (1 + chi p) r(n) - [p | n] chi(p) r(n / p), chi p = (p | d)      *)
(* (CLASSNO_REP_RECURSION), by local arguments: an inert p (chi p = -1)      *)
(* divides both coordinates of z whenever it divides N z; the ramified p = d *)
(* is the norm of (-1,2); a split p (chi p = 1) is the norm of some pi       *)
(* (CLASSNO_SPLIT_REPRESENTED), every z with p dividing N z is divisible by  *)
(* pi or by conj pi, and by both iff p divides z. The divisor sums of any    *)
(* function that is completely multiplicative at p satisfy the same          *)
(* recursion (CLASSNO_REP_DIVISOR_SUM_REC); r(1) = 2 (d > 3) and strong      *)
(* induction over the prime factorisation (CLASSNO_REP_PRIME_INDUCT) finish. *)
(* The splitting character is identified with n -> jacobi(n,d) by Jacobi     *)
(* reciprocity.                                                              *)
(*                                                                           *)
(* Main results: CLASSNO_REPRESENTATION; QFORM_REP_FINITE,                   *)
(* QFORM_REP_LINEAR_IMAGE, QFORM_REP_LINEAR_CARD, QFORM_REP_LINEAR_CARD0,    *)
(* QFORM_CARD_SCALE, QFORM_REP_CARD_MUL_P, QFORM_REP_CARD_SCALE_P,           *)
(* QFORM_REP_SPLIT_CASES, QFORM_REP_SPLIT_BOTH, QFORM_REP_SPLIT_DECOMP,      *)
(* QFORM_REP_INERT2, QFORM_REP_JACOBI_ODD, QFORM_REP_INERT_DIVIDES,          *)
(* QFORM_REP_DIVSUM_CONV_REC; CLASSNO_REP_RECURSION,                         *)
(* CLASSNO_REP_DIVISOR_SUM_REC, CLASSNO_REP_PRIME_INDUCT; helper names       *)
(* CLASSNO_REP_* and CNR_*.                                                  *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (form_classno, prin_form, prin_rep, qform,    *)
(* QFORM_PRIN), Baker/classno_chardefs.ml (qchar), Baker/classno_forms.ml    *)
(* (CLASSNO_SPLIT_REPRESENTED, CLASSNO_FORMS_MOD8_CASES); Library/jacobi.ml  *)
(* (JACOBI_RECIPROCITY, JACOBI_MINUS1, JACOBI_OF_2_CASES, JACOBI_PRIME),     *)
(* ANT/quadratic.ml (INT_NORM_FORM_4_IMAGINARY).                             *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "ANT/quadratic.ml";;
needs "Baker/classno_forms.ml";;
needs "Baker/classno_chardefs.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Elementary facts: d = 4 k + 3, the identity 4 N = (2x + y)^2 + d y^2,  *)
(*    finiteness of the representation sets of a positive definite form.     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_REP_DMOD4 = prove
 (`!d. d MOD 4 = 3 ==> ?k. d = 4 * k + 3 /\ (d + 1) DIV 4 = k + 1`,
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `d DIV 4` THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC);;

let CLASSNO_REP_PRIN_FORM = prove
 (`!k x y. prin_form (4 * k + 3) x y = x pow 2 + x * y + (&k + &1) * y pow 2`,
  REWRITE_TAC[prin_form; ARITH_RULE `(4 * k + 3) + 1 = 4 * (k + 1)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; GSYM INT_OF_NUM_ADD]);;

let CLASSNO_REP_NORM4 = prove
 (`!d x y. d MOD 4 = 3
           ==> &4 * prin_form d x y = (&2 * x + y) pow 2 + &d * y pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (SUBST1_TAC o CONJUNCT1) o
    MATCH_MP CLASSNO_REP_DMOD4) THEN
  REWRITE_TAC[CLASSNO_REP_PRIN_FORM; GSYM INT_OF_NUM_ADD;
              GSYM INT_OF_NUM_MUL] THEN
  INT_ARITH_TAC);;

let CLASSNO_REP_ABS_LE_POW2 = prove
 (`!t:int. abs t <= t pow 2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
  MP_TAC(SPEC `t:int` INT_ABS_POS) THEN SPEC_TAC(`abs t:int`,`a:int`) THEN
  GEN_TAC THEN REWRITE_TAC[INT_POW_2] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a:int = &0` THEN
  ASM_REWRITE_TAC[INT_MUL_LZERO; INT_LE_REFL] THEN
  MATCH_MP_TAC(INT_ARITH `&0 <= a * (a - &1) ==> a:int <= a * a`) THEN
  MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC);;

let QFORM_REP_FINITE = prove
 (`!a b c n. &0 < a /\ b pow 2 < &4 * a * c
             ==> FINITE {(x,y) | qform a b c x y = &n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:int | --(&4 * c * &n) <= x /\ x <= &4 * c * &n} CROSS
              {y:int | --(&4 * a * &n) <= y /\ y <= &4 * a * &n}` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_INT_SEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
              IN_ELIM_THM; qform] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < c:int` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `a * c <= &0:int` MP_TAC THENL
     [REWRITE_TAC[INT_ARITH `a * c <= &0 <=> &0 <= a * --c:int`] THEN
      MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC;
      MP_TAC(SPEC `b:int` INT_LE_POW_2) THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0:int) <= (&4 * a * c - b pow 2 - &1) * y pow 2 /\
                (&0:int) <= (&4 * a * c - b pow 2 - &1) * x pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_LE_POW_2] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN
  MP_TAC(SPEC `x:int` CLASSNO_REP_ABS_LE_POW2) THEN
  MP_TAC(SPEC `&2 * a * x + b * y:int` INT_LE_POW_2) THEN
  MP_TAC(SPEC `&2 * c * y + b * x:int` INT_LE_POW_2) THEN
  SUBGOAL_THEN
   `&4 * a * &n = (&2 * a * x + b * y) pow 2 +
                  (&4 * a * c - b pow 2) * (y:int) pow 2 /\
    &4 * c * &n = (&2 * c * y + b * x) pow 2 +
                  (&4 * a * c - b pow 2) * (x:int) pow 2`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    CONJ_TAC THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN INT_ARITH_TAC);;

let CLASSNO_REP_PRIN_POSDEF = prove
 (`!d. d MOD 4 = 3
       ==> (&0:int) < &1 /\ (&1:int) pow 2 < &4 * &1 * &((d + 1) DIV 4)`,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` (SUBST1_TAC o CONJUNCT2) o
    MATCH_MP CLASSNO_REP_DMOD4) THEN
  REWRITE_TAC[INT_LT_01; INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_LT] THEN
  ARITH_TAC);;

let CLASSNO_REP_FINITE = prove
 (`!d l. d MOD 4 = 3 ==> FINITE {(x,y) | prin_form d x y = &l}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM QFORM_PRIN] THEN
  MATCH_MP_TAC QFORM_REP_FINITE THEN
  ASM_SIMP_TAC[CLASSNO_REP_PRIN_POSDEF; INT_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* 2. Linear substitutions: if F(M(u,v)) = k G(u,v) for an integer matrix    *)
(*    M = (al be; ga de) of determinant D <> 0, the image of the solutions   *)
(*    of G = n is the set of solutions of F = k n satisfying the two         *)
(*    congruences of the adjugate matrix modulo D (with predicates P, Q      *)
(*    transported along M). Scaling by s: M = s I.                           *)
(* ------------------------------------------------------------------------- *)

let QFORM_REP_LINEAR_IMAGE = prove
 (`!ff gg P Q al be ga de k n.
        (!u v:int. ff (al * u + be * v) (ga * u + de * v) =
                   (k:int) * gg u v) /\
        (!u v. P (al * u + be * v) (ga * u + de * v) <=> Q u v) /\
        ~(k = &0) /\ ~(al * de - be * ga = &0)
        ==> {(x,y) | ff x y = k * &n /\
                     (al * de - be * ga) divides de * x - be * y /\
                     (al * de - be * ga) divides al * y - ga * x /\
                     P x y} =
            IMAGE (\z. al * FST z + be * SND z, ga * FST z + de * SND z)
                  {(u,v) | gg u v = &n /\ Q u v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_IMAGE;
              EXISTS_PAIR_THM; PAIR_EQ; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN EQ_TAC THENL
   [REWRITE_TAC[int_divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `u:int`) (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `v:int`) ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u:int`; `v:int`] THEN
    SUBGOAL_THEN
     `(al * de - be * ga) * x = (al * de - be * ga) * (al * u + be * v) /\
      (al * de - be * ga) * y = (al * de - be * ga) * (ga * u + de * v:int)`
    MP_TAC THENL
     [CONJ_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_eq(concl th) && type_of(lhs(concl th)) = `:int`))) THEN
      CONV_TAC INT_RING;
      ASM_REWRITE_TAC[INT_EQ_MUL_LCANCEL] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `P (al * u + be * v) (ga * u + de * (v:int)):bool` THEN
      UNDISCH_TAC
       `ff (al * u + be * v) (ga * u + de * (v:int)) = (k:int) * &n` THEN
      ASM_REWRITE_TAC[INT_EQ_MUL_LCANCEL] THEN CONV_TAC TAUT];
    DISCH_THEN(X_CHOOSE_THEN `u:int` (X_CHOOSE_THEN `v:int`
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST1_TAC) STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[int_divides] THEN CONJ_TAC THENL
     [EXISTS_TAC `u:int`; EXISTS_TAC `v:int`] THEN
    CONV_TAC INT_RING]);;

let QFORM_REP_LINEAR_CARD = prove
 (`!ff gg P Q al be ga de k n.
        (!u v:int. ff (al * u + be * v) (ga * u + de * v) =
                   (k:int) * gg u v) /\
        (!u v. P (al * u + be * v) (ga * u + de * v) <=> Q u v) /\
        ~(k = &0) /\ ~(al * de - be * ga = &0) /\
        FINITE {(u,v) | gg u v = &n /\ Q u v}
        ==> CARD {(x,y) | ff x y = k * &n /\
                          (al * de - be * ga) divides de * x - be * y /\
                          (al * de - be * ga) divides al * y - ga * x /\
                          P x y} =
            CARD {(u,v) | gg u v = &n /\ Q u v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ff:int->int->int`; `gg:int->int->int`;
                `P:int->int->bool`; `Q:int->int->bool`;
                `al:int`; `be:int`; `ga:int`; `de:int`; `k:int`; `n:num`]
    QFORM_REP_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`u:int`; `v:int`; `u':int`; `v':int`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN
   `(al * de - be * ga) * u = (al * de - be * ga) * u' /\
    (al * de - be * ga) * v = (al * de - be * ga) * (v':int)`
  MP_TAC THENL
   [CONJ_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_eq(concl th) && type_of(lhs(concl th)) = `:int`))) THEN
    CONV_TAC INT_RING;
    ASM_REWRITE_TAC[INT_EQ_MUL_LCANCEL]]);;

let QFORM_REP_LINEAR_CARD0 = prove
 (`!ff gg al be ga de k n.
        (!u v:int. ff (al * u + be * v) (ga * u + de * v) =
                   (k:int) * gg u v) /\
        ~(k = &0) /\ ~(al * de - be * ga = &0) /\
        FINITE {(u,v) | gg u v = &n}
        ==> CARD {(x,y) | ff x y = k * &n /\
                          (al * de - be * ga) divides de * x - be * y /\
                          (al * de - be * ga) divides al * y - ga * x} =
            CARD {(u,v) | gg u v = &n}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ff:int->int->int`; `gg:int->int->int`;
                `\x:int y:int. T`; `\x:int y:int. T`;
                `al:int`; `be:int`; `ga:int`; `de:int`; `k:int`; `n:num`]
    QFORM_REP_LINEAR_CARD) THEN
  ASM_REWRITE_TAC[]);;

let QFORM_CARD_SCALE = prove
 (`!a b c s n P.
        &0 < a /\ b pow 2 < &4 * a * c /\ ~(s = 0) /\
        (!x y. P (&s * x) (&s * y) <=> P x y)
        ==> CARD {(x,y) | qform a b c x y = &(s * n) /\
                          &s divides x /\ &s divides y /\ P x y} =
            if s divides n
            then CARD {(x,y) | qform a b c x y = &(n DIV s) /\ P x y}
            else 0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN
    MP_TAC(ISPECL [`qform a b c`; `qform a b c`; `P:int->int->bool`;
                   `P:int->int->bool`; `&s:int`; `&0:int`; `&0:int`; `&s:int`;
                   `&s * &s:int`; `m:num`] QFORM_REP_LINEAR_CARD) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID; INT_ADD_RID; INT_SUB_RZERO] THEN
    ASM_REWRITE_TAC[INT_ENTIRE; INT_OF_NUM_EQ] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[qform] THEN REPEAT GEN_TAC THEN CONV_TAC INT_RING;
        ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{(u,v) | qform a b c u v = &m}` THEN
      ASM_SIMP_TAC[QFORM_REP_FINITE] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[INT_DIVIDES_LMUL2_EQ; INT_OF_NUM_EQ] THEN
      REWRITE_TAC[INT_OF_NUM_MUL; MULT_ASSOC]];
    MATCH_MP_TAC(MESON[CARD_CLAUSES] `s:int#int->bool = {} ==> CARD s = 0`) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
                int_divides] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:int` SUBST1_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:int` SUBST1_TAC) (K ALL_TAC)))) THEN
    REWRITE_TAC[qform; GSYM INT_OF_NUM_MUL] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(s divides n)` THEN
    REWRITE_TAC[num_divides; int_divides] THEN
    EXISTS_TAC `a * (u:int) pow 2 + b * u * v + c * v pow 2` THEN
    SUBGOAL_THEN
     `(&s:int) * &n = &s * &s * (a * u pow 2 + b * u * v + c * v pow 2)`
    MP_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC INT_RING;
      ASM_REWRITE_TAC[INT_EQ_MUL_LCANCEL; INT_OF_NUM_EQ]]]);;
(* ------------------------------------------------------------------------- *)
(* 3. Multiplication in Z[w], w = (1 + sqrt(-d)) / 2, as integer pairs (the  *)
(*    norm is prin_form d), with a predicate P invariant under the map.      *)
(*    For pi = (a,b) of norm s > 0 the elements of norm s n divisible by pi  *)
(*    (s divides both coordinates of conj(pi) z) are the products pi w with  *)
(*    N w = n (the substitution w -> pi w has determinant N pi); similarly   *)
(*    for the scalar multiples p w.                                          *)
(* ------------------------------------------------------------------------- *)

let QFORM_REP_CARD_MUL_P = prove
 (`!d a b s n P.
        d MOD 4 = 3 /\ prin_form d a b = &s /\ ~(s = 0) /\
        (!u v. P (a * u - &((d + 1) DIV 4) * b * v) (a * v + b * u + b * v) <=>
               P u v)
        ==> CARD {(x,y) | prin_form d x y = &(s * n) /\
                          &s divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
                          &s divides a * y - b * x /\ P x y} =
            CARD {(u,v) | prin_form d u v = &n /\ P u v}`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `c:int = &((d + 1) DIV 4)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `a * (a + b) - --(c * b) * b = &s:int` ASSUME_TAC THENL
   [UNDISCH_TAC `prin_form d a b = &s` THEN ASM_REWRITE_TAC[prin_form] THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prin_form d`; `prin_form d`; `P:int->int->bool`;
                 `P:int->int->bool`; `a:int`; `--(c * b):int`; `b:int`;
                 `a + b:int`; `&s:int`; `n:num`] QFORM_REP_LINEAR_CARD) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_MUL] THEN
  REWRITE_TAC[INT_ARITH `(a + b) * x - --(c * b) * y:int =
                         (a + b) * x + c * b * y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `prin_form d a b = &s` THEN ASM_REWRITE_TAC[prin_form] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    CONV_TAC INT_RING;
    REPEAT GEN_TAC THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    BINOP_TAC THEN INT_ARITH_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(u,v) | prin_form d u v = &n}` THEN
    ASM_SIMP_TAC[CLASSNO_REP_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[]]);;
let CLASSNO_REP_CARD_MUL = prove
 (`!d a b q n.
        d MOD 4 = 3 /\ prin_form d a b = &q /\ ~(q = 0)
        ==> CARD {(x,y) | prin_form d x y = &(q * n) /\
                          &q divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
                          &q divides a * y - b * x} = prin_rep d n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `a:int`; `b:int`; `q:num`; `n:num`;
                 `\x:int y:int. T`] QFORM_REP_CARD_MUL_P) THEN
  ASM_REWRITE_TAC[prin_rep]);;

let QFORM_REP_CARD_SCALE_P = prove
 (`!d s n P.
        d MOD 4 = 3 /\ ~(s = 0) /\ (!x y. P (&s * x) (&s * y) <=> P x y)
        ==> CARD {(x,y) | prin_form d x y = &(s * n) /\
                          &s divides x /\ &s divides y /\ P x y} =
            if s divides n
            then CARD {(x,y) | prin_form d x y = &(n DIV s) /\ P x y}
            else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM QFORM_PRIN] THEN
  MATCH_MP_TAC QFORM_CARD_SCALE THEN
  ASM_SIMP_TAC[CLASSNO_REP_PRIN_POSDEF; INT_LT_01]);;

let CLASSNO_REP_CARD_SCALE = prove
 (`!d p n. d MOD 4 = 3 /\ ~(p = 0)
           ==> CARD {(x,y) | prin_form d x y = &(p * n) /\
                             &p divides x /\ &p divides y} =
               if p divides n then prin_rep d (n DIV p) else 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `p:num`; `n:num`; `\x:int y:int. T`]
    QFORM_REP_CARD_SCALE_P) THEN
  ASM_REWRITE_TAC[prin_rep]);;

(* ------------------------------------------------------------------------- *)
(* 4. Local behaviour of the primes: inert (both coordinates divisible),     *)
(*    ramified (p = d), split (r | N z: divisible by pi or by conj pi, by    *)
(*    both iff divisible by r, when r | N pi, r^2 not dividing N pi).        *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_REP_INT_PARITY = prove
 (`!x:int. (x == &0) (mod &2) \/ (x == &1) (mod &2)`,
  GEN_TAC THEN MP_TAC(SPECL [`x:int`; `&2:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x rem &2 = &0 \/ x rem &2 = &1` STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC;
    DISJ1_TAC;
    DISJ2_TAC] THEN
  REWRITE_TAC[int_congruent] THEN EXISTS_TAC `x div &2` THEN
  ASM_INT_ARITH_TAC);;

let CLASSNO_REP_PARITY_FORM = prove
 (`!x y c:int. (c == &1) (mod &2) /\
               &2 divides x pow 2 + x * y + c * y pow 2
               ==> &2 divides x /\ &2 divides y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r s:int. (x == r) (mod &2) /\ (y == s) (mod &2)
              ==> &2 divides r pow 2 + r * s + &1 * s pow 2`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!m n v:int. m divides n /\ (n == v) (mod m) ==> m divides v`) THEN
    EXISTS_TAC `(x:int) pow 2 + x * y + c * y pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!m x y c r s t:int.
        (x == r) (mod m) /\ (y == s) (mod m) /\ (c == t) (mod m)
        ==> (x pow 2 + x * y + c * y pow 2 == r pow 2 + r * s + t * s pow 2)
            (mod m)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`&1:int`; `&0:int`] th) THEN
    MP_TAC(SPECL [`&0:int`; `&1:int`] th) THEN
    MP_TAC(SPECL [`&1:int`; `&1:int`] th)) THEN
  MP_TAC(SPEC `x:int` CLASSNO_REP_INT_PARITY) THEN
  MP_TAC(SPEC `y:int` CLASSNO_REP_INT_PARITY) THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM num_divides] THEN
  CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN
  REWRITE_TAC[INTEGER_RULE `!m x:int. (x == &0) (mod m) <=> m divides x`] THEN
  CONV_TAC TAUT);;

let CLASSNO_REP_JACOBI_2 = prove
 (`!d. d MOD 4 = 3
       ==> (jacobi(2,d) = &1 <=> d MOD 8 = 7) /\
           (jacobi(2,d) = -- &1 <=> d MOD 8 = 3)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `ODD d` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `k:num` (SUBST1_TAC o CONJUNCT1) o
      MATCH_MP CLASSNO_REP_DMOD4) THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[JACOBI_OF_2_CASES; GSYM NOT_ODD; CONG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
                MATCH_MP CLASSNO_FORMS_MOD8_CASES) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN CONV_TAC INT_REDUCE_CONV);;

let CLASSNO_REP_INERT_2 = prove
 (`!d x y. d MOD 8 = 3 /\ &2 divides prin_form d x y
           ==> &2 divides x /\ &2 divides y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CLASSNO_REP_PARITY_FORM THEN
  EXISTS_TAC `&((d + 1) DIV 4):int` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[prin_form]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(d + 1) DIV 4 = 2 * (d DIV 8) + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    MP_TAC(SPECL [`d:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ARITH_TAC;
    REWRITE_TAC[int_congruent; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    EXISTS_TAC `&(d DIV 8):int` THEN INT_ARITH_TAC]);;

(* An inert prime r (-d not a square mod r) dividing x^2 + d y^2 divides x   *)
(* and y; for the principal form apply it to 4 N = (2x + y)^2 + d y^2.      *)

let QFORM_REP_INERT2 = prove
 (`!d r x y. prime r /\ ~(?s:int. &r divides s pow 2 + &d) /\
             &r divides x pow 2 + &d * y pow 2
             ==> &r divides x /\ &r divides y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&r divides (y:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`y:int`; `&r:int`] INT_BEZOUT_PRIME) THEN
    ASM_REWRITE_TAC[INT_PRIME] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:int` (X_CHOOSE_TAC `w:int`)) THEN
    UNDISCH_TAC `~(?s:int. &r divides s pow 2 + &d)` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `x * v:int` THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!p s y f v w:int. p divides s pow 2 + f * y pow 2 /\ y * v = p * w + &1
                        ==> p divides (s * v) pow 2 + f`) THEN
    MAP_EVERY EXISTS_TAC [`y:int`; `w:int`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&r divides (x:int) * x` MP_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `!q s y f:int. q divides y /\ q divides s pow 2 + f * y pow 2
                    ==> q divides s * s`) THEN
    MAP_EVERY EXISTS_TAC [`y:int`; `&d:int`] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]]);;

let CLASSNO_REP_INERT_ODD = prove
 (`!d p x y. d MOD 4 = 3 /\ prime p /\ ~(p = 2) /\
             ~(?t:int. &p divides t pow 2 + &d) /\
             &p divides prin_form d x y
             ==> &p divides x /\ &p divides y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `p:num`; `&2 * x +
    y:int`; `y:int`] QFORM_REP_INERT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`d:num`; `x:int`; `y:int`] CLASSNO_REP_NORM4) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INT_DIVIDES_LMUL THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&p divides &2 * (x:int)` MP_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `!q s y:int. q divides y /\ q divides s + y ==> q divides s`) THEN
    EXISTS_TAC `y:int` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN REWRITE_TAC[GSYM num_divides] THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2]]);;

let CLASSNO_REP_RAMIFIED = prove
 (`!d x y. prime d /\ d MOD 4 = 3 /\ &d divides prin_form d x y
           ==> &d divides (-- &1 + &2) * x + &((d + 1) DIV 4) * &2 * y /\
               &d divides -- &1 * y - &2 * x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&d divides (&2 * x + y:int)` MP_TAC THENL
   [SUBGOAL_THEN `&d divides (&2 * x + y) * (&2 * x + y:int)` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!e n s y:int. e divides n /\ &4 * n = s pow 2 + e * y pow 2
                      ==> e divides s * s`) THEN
      MAP_EVERY EXISTS_TAC [`prin_form d x y`; `y:int`] THEN
      ASM_SIMP_TAC[CLASSNO_REP_NORM4];
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) o
    MATCH_MP CLASSNO_REP_DMOD4) THEN
  SUBGOAL_THEN `&d = &4 * &k + &3:int` MP_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; int_divides] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `a:int`) THEN CONJ_TAC THENL
   [EXISTS_TAC `x + y - (&2 * &k + &1) * a:int`;
    EXISTS_TAC `--a:int`] THEN
  MAP_EVERY UNDISCH_TAC
   [`&d = &4 * &k + &3:int`; `&2 * x + y = &d * a:int`] THEN
  CONV_TAC INT_RING);;

let QFORM_REP_SPLIT_CASES = prove
 (`!d r a b x y.
        prime r /\ &r divides prin_form d a b /\ &r divides prin_form d x y
        ==> (&r divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
             &r divides a * y - b * x) \/
            (&r divides ((a + b) + --b) * x + &((d + 1) DIV 4) * --b * y /\
             &r divides (a + b) * y - --b * x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[prin_form] THEN
  SPEC_TAC(`&((d + 1) DIV 4):int`,`c:int`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&r:int`; `c:int`; `a:int`; `b:int`; `x:int`; `y:int`]
   (INTEGER_RULE
     `!q c a b x y:int.
        q divides a pow 2 + a * b + c * b pow 2 /\
        q divides x pow 2 + x * y + c * y pow 2
        ==> q divides (a * y - b * x) * ((a + b) * y - --b * x)`)) THEN
  ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&r:int`; `c:int`; `a:int`; `b:int`; `x:int`; `y:int`]
     (INTEGER_RULE
       `!q c a b x y:int.
          q divides a pow 2 + a * b + c * b pow 2 /\
          q divides x pow 2 + x * y + c * y pow 2 /\
          q divides a * y - b * x
          ==> q divides ((a + b) * x + c * b * y) *
                        ((a + b) * x + c * b * y)`));
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&r:int`; `c:int`; `a:int`; `b:int`; `x:int`; `y:int`]
     (INTEGER_RULE
       `!q c a b x y:int.
          q divides a pow 2 + a * b + c * b pow 2 /\
          q divides x pow 2 + x * y + c * y pow 2 /\
          q divides (a + b) * y - --b * x
          ==> q divides (((a + b) + --b) * x + c * --b * y) *
                        (((a + b) + --b) * x + c * --b * y)`))] THEN
  ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]);;

let QFORM_REP_SPLIT_BOTH = prove
 (`!d r a b x y.
        d MOD 4 = 3 /\ prime r /\ ~(&r divides &d) /\
        &r divides prin_form d a b /\ ~(&r * &r divides prin_form d a b)
        ==> ((&r divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
              &r divides a * y - b * x) /\
             (&r divides ((a + b) + --b) * x + &((d + 1) DIV 4) * --b * y /\
              &r divides (a + b) * y - --b * x) <=>
             &r divides x /\ &r divides y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&r divides &2 * a + (b:int))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&r divides &d * (b:int) * b` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!q n s D y:int. q divides n /\ q divides s /\
                        &4 * n = s pow 2 + D * y pow 2
                        ==> q divides D * y * y`) THEN
      MAP_EVERY EXISTS_TAC [`prin_form d a b`; `&2 * a + (b:int)`] THEN
      ASM_SIMP_TAC[CLASSNO_REP_NORM4];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&r divides (a:int) * a` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!q n a b c:int. q divides b /\ q divides n /\
                        n = a pow 2 + a * b + c * b pow 2
                        ==> q divides a * a`) THEN
      MAP_EVERY EXISTS_TAC
       [`prin_form d a b`; `b:int`; `&((d + 1) DIV 4):int`] THEN
      ASM_REWRITE_TAC[prin_form];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(&r * &r divides prin_form d a b)` THEN
    REWRITE_TAC[prin_form] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!q a b c:int. q divides a /\ q divides b
                    ==> (q * q) divides a pow 2 + a * b + c * b pow 2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`&r:int`; `&((d + 1) DIV 4):int`; `a:int`; `b:int`;
                   `x:int`; `y:int`]
     (INTEGER_RULE
       `!q c a b x y:int.
          q divides (a + b) * x + c * b * y /\
          q divides ((a + b) + --b) * x + c * --b * y /\
          q divides a * y - b * x /\ q divides (a + b) * y - --b * x
          ==> q divides (&2 * a + b) * x /\ q divides (&2 * a + b) * y`)) THEN
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ];
    MP_TAC(ISPECL [`&r:int`; `&((d + 1) DIV 4):int`; `a:int`; `b:int`;
                   `x:int`; `y:int`]
     (INTEGER_RULE
       `!q c a b x y:int.
          q divides x /\ q divides y
          ==> (q divides (a + b) * x + c * b * y /\ q divides a * y - b * x) /\
              (q divides ((a + b) + --b) * x + c * --b * y /\
               q divides (a + b) * y - --b * x)`)) THEN
    REWRITE_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* 5. The splitting character: for an odd prime r coprime to d, jacobi(r,d)  *)
(*    = 1 iff -d is a square mod r (Jacobi reciprocity, d = 3 mod 4); inert  *)
(*    primes divide both coordinates; split primes are norms                 *)
(*    (CLASSNO_SPLIT_REPRESENTED of Baker/classno_forms.ml, h(-d) = 1).      *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_REP_INT_SQUARE = prove
 (`!p d. (?x. p divides x EXP 2 + d) <=> (?t:int. &p divides t pow 2 + &d)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN EXISTS_TAC `&x:int` THEN
    ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_ADD; GSYM num_divides];
    DISCH_THEN(X_CHOOSE_TAC `t:int`) THEN EXISTS_TAC `num_of_int(abs t)` THEN
    REWRITE_TAC[num_divides; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_POW] THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_POW2_ABS]]);;

let CLASSNO_REP_DMOD4_ODD = prove
 (`!d. d MOD 4 = 3 ==> ODD d /\ ~EVEN((d - 1) DIV 2)`,
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (SUBST1_TAC o CONJUNCT1) o
    MATCH_MP CLASSNO_REP_DMOD4) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH;
              ARITH_RULE `(4 * k + 3) - 1 = 2 * (2 * k + 1)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let QFORM_REP_JACOBI_ODD = prove
 (`!d r. d MOD 4 = 3 /\ prime r /\ ~(r = 2) /\ coprime(r,d)
         ==> (jacobi(r,d) = &1 <=> ?t:int. &r divides t pow 2 + &d)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLASSNO_REP_DMOD4_ODD) THEN
  SUBGOAL_THEN `ODD r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_ODD]; ALL_TAC] THEN
  SUBGOAL_THEN `jacobi((r - 1) * d,r) = jacobi(r,d)` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[JACOBI_LMUL] THEN ASM_SIMP_TAC[JACOBI_MINUS1] THEN
    MP_TAC(SPECL [`r:num`; `d:num`] JACOBI_RECIPROCITY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; EVEN_MULT] THEN
    COND_CASES_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[JACOBI_PRIME] THEN
  SUBGOAL_THEN `~(r divides (r - 1) * d)` (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `~(r divides d)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CLASSNO_REP_INT_SQUARE] THEN
  SUBGOAL_THEN `!x. (x EXP 2 == (r - 1) * d) (mod r) <=> r divides x EXP 2 + d`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`x EXP 2`; `r - 1`; `d:num`]
     (NUMBER_RULE `!x s d:num. (x == s * d) (mod (s + 1)) <=>
                               (s + 1) divides x + d`)) THEN
    SUBGOAL_THEN `r - 1 + 1 = r` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      REWRITE_TAC[]];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV]);;

let CLASSNO_REP_JACOBI_SELF = prove
 (`!d. prime d ==> jacobi(d,d) = &0`,
  SIMP_TAC[JACOBI_EQ_0; COPRIME_REFL] THEN MESON_TAC[PRIME_1]);;

let QFORM_REP_JACOBI_NZ = prove
 (`!r d. ~(jacobi(r,d) = &0) ==> coprime(r,d)`,
  MESON_TAC[JACOBI_EQ_0]);;

let QFORM_REP_INERT_DIVIDES = prove
 (`!d r x y. d MOD 4 = 3 /\ prime r /\ jacobi(r,d) = --(&1) /\
             &r divides prin_form d x y
             ==> &r divides x /\ &r divides y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `coprime(r:num,d)` ASSUME_TAC THENL
   [MATCH_MP_TAC QFORM_REP_JACOBI_NZ THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC CLASSNO_REP_INERT_2 THEN
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP CLASSNO_REP_JACOBI_2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_REP_INERT_ODD THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:num`; `r:num`] QFORM_REP_JACOBI_ODD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC INT_REDUCE_CONV);;

let CLASSNO_REP_SPLIT_B = prove
 (`!d p t:int. d MOD 4 = 3 /\ ODD p /\ &p divides t pow 2 + &d
               ==> ?b:int. (b pow 2 + &d == &0) (mod (&4 * &p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` ASSUME_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (ASSUME_TAC o CONJUNCT1) o
    MATCH_MP CLASSNO_REP_DMOD4) THEN
  SUBGOAL_THEN `&p = &2 * &e + &1:int /\ &d = &4 * &k + &3:int`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ADD1; INT_OF_NUM_ADD; INT_OF_NUM_MUL]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:int` o REWRITE_RULE[int_divides]) THEN
  MP_TAC(SPEC `t:int` CLASSNO_REP_INT_PARITY) THEN
  REWRITE_TAC[int_congruent; INT_SUB_RZERO] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC `f:int`)) THENL
   [EXISTS_TAC `t + &p:int` THEN REWRITE_TAC[int_congruent] THEN
    EXISTS_TAC `&p * ((f + &e) pow 2 + (f + &e) + &k + &1) -
                (&e pow 2 + &e) * (z + &2 * t + &p):int`;
    EXISTS_TAC `t:int` THEN REWRITE_TAC[int_congruent] THEN
    EXISTS_TAC `&p * (f pow 2 + f + &k + &1) - (&e pow 2 + &e) * z:int`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_eq(concl th) && type_of(lhs(concl th)) = `:int`))) THEN
  CONV_TAC INT_RING);;

let CLASSNO_REP_SPLIT_PI = prove
 (`!d p. prime d /\ d MOD 4 = 3 /\ form_classno (--(&d)) = 1 /\
         prime p /\ jacobi(p,d) = &1
         ==> ?a b. prin_form d a b = &p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLASSNO_SPLIT_REPRESENTED THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `p = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CLASSNO_REP_JACOBI_2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `&1:int` THEN
    REWRITE_TAC[int_congruent; INT_POW_ONE] THEN
    EXISTS_TAC `&(d DIV 8) + &1:int` THEN
    MP_TAC(SPECL [`d:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o AP_TERM `int_of_num` o CONJUNCT1) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:num = d)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `jacobi(d,d) = &1` THEN
    ASM_SIMP_TAC[CLASSNO_REP_JACOBI_SELF] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `p:num`] QFORM_REP_JACOBI_ODD) THEN
  ASM_SIMP_TAC[DISTINCT_PRIME_COPRIME] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:int`) THEN
  MATCH_MP_TAC CLASSNO_REP_SPLIT_B THEN EXISTS_TAC `t:int` THEN
  ASM_MESON_TAC[PRIME_ODD]);;
(* ------------------------------------------------------------------------- *)
(* 6. The recursion of the representation numbers at a prime p:              *)
(*    r(p n) = (1 + chi p) r(n) - [p | n] chi(p) r(n / p); the               *)
(*    inclusion-exclusion at a split prime is QFORM_REP_SPLIT_DECOMP.        *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_REP_CARD_UNION_INTER = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t
        ==> CARD(s UNION t) + CARD(s INTER t) = CARD s + CARD t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  MATCH_MP_TAC SUB_ADD THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(s:A->bool)` THEN
  ASM_SIMP_TAC[CARD_SUBSET; INTER_SUBSET; LE_ADD]);;

let CLASSNO_REP_DIVIDES_MUL = prove
 (`!p n. &p divides &(p * n):int`,
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MESON_TAC[INT_DIVIDES_RMUL; INT_DIVIDES_REFL]);;

let QFORM_REP_SPLIT_DECOMP = prove
 (`!d r a b m P.
        d MOD 4 = 3 /\ prime r /\ ~(&r divides &d) /\
        &r divides prin_form d a b /\ ~(&r * &r divides prin_form d a b)
        ==> CARD {(x,y) | prin_form d x y = &(r * m) /\ P x y} +
            CARD {(x,y) | prin_form d x y = &(r * m) /\
                          &r divides x /\ &r divides y /\ P x y} =
            CARD {(x,y) | prin_form d x y = &(r * m) /\
                          &r divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
                          &r divides a * y - b * x /\ P x y} +
            CARD {(x,y) | prin_form d x y = &(r * m) /\
                          &r divides ((a + b) + --b) * x +
                                     &((d + 1) DIV 4) * --b * y /\
                          &r divides (a + b) * y - --b * x /\ P x y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{(x,y) | prin_form d x y = &(r * m) /\
              &r divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
              &r divides a * y - b * x /\ P x y}`;
    `{(x,y) | prin_form d x y = &(r * m) /\
              &r divides ((a + b) + --b) * x + &((d + 1) DIV 4) * --b * y /\
              &r divides (a + b) * y - --b * x /\ P x y}`]
   CLASSNO_REP_CARD_UNION_INTER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(x,y) | prin_form d x y = &(r * m)}` THEN
    ASM_SIMP_TAC[CLASSNO_REP_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; FORALL_PAIR_THM;
              IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THENL
   [ASM_CASES_TAC `prin_form d x y = &(r * m)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(P:int->int->bool) x y` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC QFORM_REP_SPLIT_CASES THEN
    ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL];
    MP_TAC(SPECL [`d:num`; `r:num`; `a:int`; `b:int`; `x:int`; `y:int`]
      QFORM_REP_SPLIT_BOTH) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT]);;

let CLASSNO_REP_RAMIFIED_REC = prove
 (`!d n. prime d /\ d MOD 4 = 3 ==> prin_rep d (d * n) = prin_rep d n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `-- &1:int`; `&2:int`; `d:num`; `n:num`]
    CLASSNO_REP_CARD_MUL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `k:num` (SUBST1_TAC o CONJUNCT1) o
      MATCH_MP CLASSNO_REP_DMOD4) THEN
    REWRITE_TAC[CLASSNO_REP_PRIN_FORM; GSYM INT_OF_NUM_ADD;
                GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[prin_rep] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
    MATCH_MP_TAC CLASSNO_REP_RAMIFIED THEN
    ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL]]);;

let CLASSNO_REP_INERT_REC = prove
 (`!d p n. prime d /\ d MOD 4 = 3 /\ prime p /\ jacobi(p,d) = -- &1
           ==> prin_rep d (p * n) =
               if p divides n then prin_rep d (n DIV p) else 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `p:num`; `n:num`] CLASSNO_REP_CARD_SCALE) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[prin_rep] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC QFORM_REP_INERT_DIVIDES THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL]);;

let CLASSNO_REP_SPLIT_REC = prove
 (`!d p n. prime d /\ d MOD 4 = 3 /\ form_classno (--(&d)) = 1 /\
           prime p /\ jacobi(p,d) = &1
           ==> prin_rep d (p * n) +
               (if p divides n then prin_rep d (n DIV p) else 0) =
               2 * prin_rep d n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `p:num`] CLASSNO_REP_SPLIT_PI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_TAC `b:int`)) THEN
  SUBGOAL_THEN `~(p:num = d)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `jacobi(d,d) = &1` THEN
    ASM_SIMP_TAC[CLASSNO_REP_JACOBI_SELF] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= p /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `prin_form d (a + b) (--b) = &p` ASSUME_TAC THENL
   [UNDISCH_TAC `prin_form d a b = &p` THEN REWRITE_TAC[prin_form] THEN
    SPEC_TAC(`&((d + 1) DIV 4):int`,`c:int`) THEN GEN_TAC THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:num`; `p:num`; `a:int`; `b:int`; `n:num`;
                 `\x:int y:int. T`] QFORM_REP_SPLIT_DECOMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_DIVIDES_REFL; INT_OF_NUM_MUL; GSYM num_divides] THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    MP_TAC(SPECL [`p:num`; `p:num`; `1`] LE_MULT_LCANCEL) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[CLASSNO_REP_CARD_MUL; CLASSNO_REP_CARD_SCALE;
                 GSYM prin_rep] THEN
    ARITH_TAC]);;

let CLASSNO_REP_RECURSION = prove
 (`!d p n. prime d /\ d MOD 4 = 3 /\ form_classno (--(&d)) = 1 /\ prime p
           ==> &(prin_rep d (p * n)) =
               (&1 + qchar d p) * &(prin_rep d n) -
               (if p divides n then qchar d p * &(prin_rep d (n DIV p))
                else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qchar] THEN
  ASM_CASES_TAC `p:num = d` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[CLASSNO_REP_JACOBI_SELF; CLASSNO_REP_RAMIFIED_REC] THEN
    REWRITE_TAC[int_of_num_th] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(p,d) = &1 \/ jacobi(p,d) = -- &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `d:num`] JACOBI_CASES) THEN
    ASM_SIMP_TAC[JACOBI_EQ_0; COPRIME_PRIME_PRIME] THEN MESON_TAC[];
    MP_TAC(SPECL [`d:num`; `p:num`; `n:num`] CLASSNO_REP_SPLIT_REC) THEN
    ASM_REWRITE_TAC[int_of_num_th] THEN
    DISCH_THEN(MP_TAC o AP_TERM `real_of_num`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`d:num`; `p:num`; `n:num`] CLASSNO_REP_INERT_REC) THEN
    ASM_REWRITE_TAC[int_neg_th; int_of_num_th] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 7. Divisor sums of the Dirichlet convolution of two functions that are    *)
(*    completely multiplicative at a prime r (local factor                   *)
(*    1 / ((1 - f(r) X) (1 - g(r) X))), library style; the divisor sums of   *)
(*    one such function are the case g = 1.                                  *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_REP_DIVISORS_MULTIPLE = prove
 (`!p n. ~(p = 0)
         ==> {m | m divides n /\ p divides m} =
             if p divides n then IMAGE (\m. p * m) {m | m divides n DIV p}
             else {}`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `m:num` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
        (X_CHOOSE_THEN `j:num` SUBST1_TAC o REWRITE_RULE[divides])) THEN
      ASM_SIMP_TAC[DIVIDES_LMUL2_EQ] THEN DISCH_TAC THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `j:num`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      ASM_SIMP_TAC[DIVIDES_LMUL2_EQ] THEN
      MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[DIVIDES_TRANS]]);;

let CLASSNO_REP_DIVISORS_COPRIME = prove
 (`!p n. prime p
         ==> {m | m divides (p * n) /\ ~(p divides m)} =
             {m | m divides n /\ ~(p divides m)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN ASM_CASES_TAC `(p:num) divides m` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `coprime(m:num,p)` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM]; CONV_TAC NUMBER_RULE]);;

let QFORM_REP_DIVSUM_SPLIT = prove
 (`!h:num->real r n.
        ~(n = 0)
        ==> sum {m | m divides n} h =
            sum {m | m divides n /\ r divides m} h +
            sum {m | m divides n /\ ~(r divides m)} h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{m | m divides n} = {m | m divides n /\ r divides m} UNION
                        {m | m divides n /\ ~(r divides m)}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{m | m divides n}` THEN
    ASM_SIMP_TAC[FINITE_DIVISORS] THEN SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{m | m divides n}` THEN
    ASM_SIMP_TAC[FINITE_DIVISORS] THEN SET_TAC[];
    SET_TAC[]]);;

let QFORM_REP_DIVSUM_MULTIPLE = prove
 (`!f g:num->real r n.
        ~(r = 0) /\ (!m. f(r * m) = f r * f m)
        ==> sum {m | m divides n /\ r divides m} (\m. f m * g(n DIV m)) =
            if r divides n
            then f r * sum {m | m divides n DIV r}
                           (\m. f m * g((n DIV r) DIV m))
            else &0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLASSNO_REP_DIVISORS_MULTIPLE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[SUM_CLAUSES] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  ASM_SIMP_TAC[DIV_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[EQ_MULT_LCANCEL]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[DIV_MULT2] THEN REAL_ARITH_TAC);;

let QFORM_REP_DIVSUM_CONV_REC = prove
 (`!f g:num->real r n.
        prime r /\ ~(n = 0) /\
        (!m. f(r * m) = f r * f m) /\ (!m. g(r * m) = g r * g m)
        ==> sum {m | m divides (r * n)} (\m. f m * g((r * n) DIV m)) =
            (f r + g r) * sum {m | m divides n} (\m. f m * g(n DIV m)) -
            (if r divides n
             then f r * g r *
                  sum {m | m divides (n DIV r)}
                      (\m. f m * g((n DIV r) DIV m))
             else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. (f:num->real) m * g((r * n) DIV m)`; `r:num`; `r * n`]
    QFORM_REP_DIVSUM_SPLIT) THEN
  ASM_REWRITE_TAC[MULT_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[QFORM_REP_DIVSUM_MULTIPLE; DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT;
               CLASSNO_REP_DIVISORS_COPRIME] THEN
  SUBGOAL_THEN
   `sum {m | m divides n /\ ~(r divides m)} (\m. f m * g((r * n) DIV m)) =
    g r * sum {m | m divides n /\ ~(r divides m)} (\m. f m * g(n DIV m))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC] THEN
    SUBST1_TAC(ARITH_RULE `r * m * k = m * r * k`) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. (f:num->real) m * g(n DIV m)`; `r:num`; `n:num`]
    QFORM_REP_DIVSUM_SPLIT) THEN
  ASM_SIMP_TAC[QFORM_REP_DIVSUM_MULTIPLE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`sum {m | m divides n /\ ~(r divides m)}
                (\m. (f:num->real) m * g(n DIV m))`,`b:real`) THEN
  SPEC_TAC(`sum {m | m divides n DIV r}
                (\m. (f:num->real) m * g(n DIV r DIV m))`,`c:real`) THEN
  SPEC_TAC(`sum {m | m divides n} (\m. (f:num->real) m * g(n DIV m))`,
           `a:real`) THEN
  SPEC_TAC(`(f:num->real) r`,`x:real`) THEN
  SPEC_TAC(`(g:num->real) r`,`y:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let CLASSNO_REP_DIVISOR_SUM_REC = prove
 (`!f p n. prime p /\ ~(n = 0) /\ (!m. f(p * m) = f p * f m)
           ==> sum {m | m divides (p * n)} f =
               (&1 + f p) * sum {m | m divides n} f -
               (if p divides n then f p * sum {m | m divides (n DIV p)} f
                else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `\m:num. &1`; `p:num`; `n:num`]
    QFORM_REP_DIVSUM_CONV_REC) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; ETA_AX] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[REAL_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* 8. The representation formula.                                            *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_REP_ONE = prove
 (`!d. d MOD 4 = 3 /\ 3 < d ==> prin_rep d 1 = 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[prin_rep] THEN
  SUBGOAL_THEN `{(x,y) | prin_form d x y = &1} = {(&1,&0), (-- &1,&0)}`
  SUBST1_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_INSERT;
              NOT_IN_EMPTY; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  SUBGOAL_THEN `~(d = 4)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `~(4 MOD 4 = 3)`]; ALL_TAC] THEN
  MP_TAC(SPECL [`&2 * x + y:int`; `y:int`; `--(&d):int`]
    INT_NORM_FORM_4_IMAGINARY) THEN
  MP_TAC(SPECL [`d:num`; `x:int`; `y:int`] CLASSNO_REP_NORM4) THEN
  ASM_SIMP_TAC[INT_EQ_NEG2; INT_OF_NUM_EQ; INT_NEG_LT0; INT_OF_NUM_LT;
               ARITH_RULE `3 < d ==> 0 < d /\ ~(d = 1) /\ ~(d = 3)`] THEN
  REPEAT DISCH_TAC THEN EQ_TAC THENL
   [ASM_INT_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[prin_form] THEN INT_ARITH_TAC]);;

let CLASSNO_REP_DIVSUM_ONE = prove
 (`!d. sum {m | m divides 1} (\m. qchar d m) = &1`,
  REWRITE_TAC[DIVIDES_ONE; SING_GSPEC; SUM_SING; qchar; JACOBI_1;
              int_of_num_th]);;

let CLASSNO_REP_PRIME_INDUCT = prove
 (`!P:num->bool.
        P 1 /\
        (!p n. prime p /\ ~(n = 0) /\ (!j. 1 <= j /\ j < p * n ==> P j)
               ==> P(p * n))
        ==> !l. 1 <= l ==> P l`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun step ->
    MATCH_MP_TAC num_WF THEN X_GEN_TAC `l:num` THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `l = 1` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    MATCH_MP_TAC step THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[]]));;

let CLASSNO_REPRESENTATION = prove
 (`!d l. prime d /\ d MOD 4 = 3 /\ 3 < d /\ form_classno (--(&d)) = 1 /\
        1 <= l
        ==> &(prin_rep d l) = &2 * sum {m | m divides l} (\m. qchar d m)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC CLASSNO_REP_PRIME_INDUCT THEN
  ASM_SIMP_TAC[CLASSNO_REP_ONE; CLASSNO_REP_DIVSUM_ONE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `1 <= n /\ n < p * n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `2 * n <= p * n` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. qchar d m`; `p:num`; `n:num`]
    CLASSNO_REP_DIVISOR_SUM_REC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[qchar; JACOBI_LMUL; int_mul_th]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CLASSNO_REP_RECURSION] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[DIV_MULT; PRIME_IMP_NZ] THEN
    SUBGOAL_THEN `1 <= k /\ k < p * p * k` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `k = 0` THENL
       [UNDISCH_TAC `1 <= p * k` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p * k` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * k <= p * k ==> k <= p * k`) THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[] THEN
      SPEC_TAC(`sum {m | m divides p * k} (\m. qchar d m)`,`A:real`) THEN
      SPEC_TAC(`sum {m | m divides k} (\m. qchar d m)`,`B:real`) THEN
      SPEC_TAC(`qchar d p`,`q:real`) THEN CONV_TAC REAL_RING];
    ASM_SIMP_TAC[] THEN
    SPEC_TAC(`sum {m | m divides n} (\m. qchar d m)`,`A:real`) THEN
    SPEC_TAC(`qchar d p`,`q:real`) THEN CONV_TAC REAL_RING]);;
