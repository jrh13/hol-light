(* ========================================================================= *)
(* The representation numbers of the two forms of discriminant -d, d = p q,  *)
(* when the class number is two.                                             *)
(*                                                                           *)
(* Purpose: for primes p = 1 mod 4, q = 3 mod 4 with form_classno(-p q) = 2  *)
(* let f = x^2 + x y + ((d + 1)/4) y^2 (the principal form, the norm of      *)
(* Z[w], w = (1 + sqrt(-d))/2) and f2 = q x^2 + q x y + ((p + q)/4) y^2 (the *)
(* second class: N(z)/q on the ideal Q = (q, (q - 1)/2 + w) above q), and    *)
(* let r_f, r_f2 count the integer pairs (qform_rep). Then for l >= 1        *)
(*   r_f(l) + r_f2(l) = 2 sum_(m | l) (m | d)            (CN_REP_TOTAL_ODD)  *)
(*   r_f(l) - r_f2(l) = 2 sum_(m | l) (m | p) (l/m | q)  (CN_REP_GENUS_ODD)  *)
(* with (n | m) = qchar m n = jacobi(n,m). This is the case of two classes   *)
(* of the formula of Dirichlet for the representation numbers of the forms   *)
(* of a discriminant (Landau, Vorlesungen ueber Zahlentheorie, Satz 204),    *)
(* the arithmetic input of the lattice sum identities in Baker,              *)
(* Transcendental Number Theory, Ch. 5, sec. 5.                              *)
(*                                                                           *)
(* Method: two lattices, with the counting tools of Baker/classno_rep.ml.    *)
(* Z[w] is the set of integer pairs with the multiplicative norm             *)
(* prin_form d, the ideal Q is the set of pairs with q | 2 x + y, and its    *)
(* elements of norm q n correspond to the solutions of f2(u,v) = n by        *)
(* (u,v) -> (q u + h v, v), h = (q - 1)/2 (CNR_B_CARD). The lemma on linear  *)
(* substitutions F(M(u,v)) = k G(u,v) with det M <> 0                        *)
(* (QFORM_REP_LINEAR_CARD0) gives all cross maps between the two forms.      *)
(* Ramified primes: r_f(p n) = r_f2(n) and                                   *)
(* r_f2(p n) = r_f(n) (z -> z sqrt(-d)/p), r_f(q n) = r_f2(n) and            *)
(* r_f2(q n) = r_f(n) (z -> q z). Inert primes r: r | N z forces r | z       *)
(* (QFORM_REP_INERT_DIVIDES), so r_F(r n) = [r | n] r_F(n/r) for both forms  *)
(* (CNR_INERT_REC). Split primes r: r is represented by f or by f2 (a        *)
(* reduced form representing r, QFORM_REPRESENTED_REDUCED, and               *)
(* form_classno(-d) = 2: CNR_TWO_FORMS_REP); values of f prime to p are      *)
(* residues mod p and values of f2 have the character (q | p) = -1           *)
(* (CN_GENUS_CHARACTER), so (r | p) decides which one                        *)
(* (CNR_SPLIT_REPRESENTED). For pi in Z[w] with N pi = r, multiplication by  *)
(* pi and by conj pi acts on both lattices:                                  *)
(* r_F(r n) = 2 r_F(n) - [r | n] r_F(n/r) (CNR_SPLIT_PLUS); for pi in Q with *)
(* N pi = q r the cross maps by pi and conj pi give                          *)
(* r_f(r n) = 2 r_f2(n) - [r | n] r_f(n/r) and                               *)
(* r_f2(r n) = 2 r_f(n) - [r | n] r_f2(n/r) (CNR_SPLIT_MINUS); the           *)
(* inclusion-exclusion is QFORM_REP_SPLIT_DECOMP. The divisor sums of the    *)
(* convolutions 1 * chi_d and chi_p * chi_q satisfy the same recursions      *)
(* (CLASSNO_REP_DIVISOR_SUM_REC, QFORM_REP_DIVSUM_CONV_REC), r_f(1) = 2,     *)
(* r_f2(1) = 0, and strong induction over the prime factorisation            *)
(* (CLASSNO_REP_PRIME_INDUCT, CNR_REP_STEP) gives r_f = g + g2, r_f2 = g -   *)
(* g2 (CNR_REP_MAIN).                                                        *)
(*                                                                           *)
(* Main results: CN_REP_TOTAL_ODD, CN_REP_GENUS_ODD, CNR_REP_MAIN;           *)
(* CNR_TWO_FORMS_REP, CNR_SPLIT_REPRESENTED, CNR_INERT_REC, CNR_SPLIT_PLUS,  *)
(* CNR_SPLIT_MINUS; helper names CNR_*.                                      *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (form_classno, prin_form, prin_rep, qform,    *)
(* qform_rep, QFORM_PRIN, QFORM_REP_PRIN),                                   *)
(* Baker/classno_chardefs.ml (qchar), Baker/classno_forms.ml                 *)
(* (QFORM_REPRESENTED_REDUCED, QFORM_REDUCE_FORM, CLASSNO_PRINCIPAL_REDUCED, *)
(* QF_PRIMITIVE_SQUAREFREE), Baker/classno_rep.ml                            *)
(* (QFORM_REP_FINITE, QFORM_REP_LINEAR_CARD0, QFORM_REP_CARD_MUL_P,          *)
(* QFORM_REP_CARD_SCALE_P, QFORM_REP_SPLIT_DECOMP, QFORM_REP_INERT_DIVIDES,  *)
(* QFORM_REP_JACOBI_ODD, QFORM_REP_JACOBI_NZ, QFORM_REP_DIVSUM_CONV_REC,     *)
(* CLASSNO_REP_CARD_MUL, CLASSNO_REP_CARD_SCALE, CLASSNO_REP_SPLIT_B,        *)
(* CLASSNO_REP_DIVISOR_SUM_REC, CLASSNO_REP_PRIME_INDUCT, CLASSNO_REP_ONE    *)
(* and smaller facts), Baker/cn_forms.ml (CN_GENUS_CHARACTER,                *)
(* CNF_CLASSNO_TWO_OTHER); Library/jacobi.ml (JACOBI_RECIPROCITY,            *)
(* JACOBI_PRIME, JACOBI_RMUL, JACOBI_LMUL, JACOBI_NE_MINUS1),                *)
(* Library/pocklington.ml (SQUAREFREE_MUL).                                  *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Baker/cn_forms.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Parameters p = 4 j + 1, q = 4 k + 3; the two forms; finiteness.        *)
(* ------------------------------------------------------------------------- *)

let CNR_PQ_PARAM = prove
 (`!p q. p MOD 4 = 1 /\ q MOD 4 = 3
         ==> ?j k. (p * q + 1) DIV 4 = 4 * j * k + 3 * j + k + 1 /\
                   (p + q) DIV 4 = j + k + 1 /\
                   p = 4 * j + 1 /\ q = 4 * k + 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?j. p = 4 * j + 1` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `p DIV 4` THEN MP_TAC(SPECL [`p:num`; `4`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. q = 4 * k + 3` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `q DIV 4` THEN MP_TAC(SPECL [`q:num`; `4`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:num`] THEN REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC);;

let CNR_F2_NORM4 = prove
 (`!p q u v. p MOD 4 = 1 /\ q MOD 4 = 3
             ==> &4 * qform (&q) (&q) (&((p + q) DIV 4)) u v =
                 &q * (&2 * u + v) pow 2 + &p * v pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CNR_PQ_PARAM) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[qform; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INT_RING);;

let CNR_F2_FINITE = prove
 (`!p q n. p MOD 4 = 1 /\ q MOD 4 = 3
           ==> FINITE {(u,v) | qform (&q) (&q) (&((p + q) DIV 4)) u v = &n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC QFORM_REP_FINITE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CNR_PQ_PARAM) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_LT; EXP_2] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. The ideal Q = (q, (q + sqrt(-d)) / 2) of norm q, q a prime divisor of  *)
(*    d, as the set of pairs with q | 2 x + y (Z[w] is the set of integer    *)
(*    pairs with the norm prin_form d, Baker/classno_rep.ml).                *)
(* ------------------------------------------------------------------------- *)

let CNR_DIVIDES_HALF = prove
 (`!q h x y:int. q = &2 * h + &1
                 ==> (q divides x - h * y <=> q divides &2 * x + y)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[int_divides] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `t:int`) THENL
   [EXISTS_TAC `&2 * t + y:int`; EXISTS_TAC `x - h * t:int`] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC INT_RING);;

let CNR_INT_COPRIME_2 = prove
 (`!d q. d MOD 4 = 3 /\ prime q /\ q divides d ==> coprime(&q:int,&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM num_coprime] THEN
  ASM_SIMP_TAC[PRIME_COPRIME_EQ; DIVIDES_PRIME_PRIME; PRIME_2] THEN
  DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `2 divides d` THEN
  REWRITE_TAC[DIVIDES_MOD] THEN
  SUBGOAL_THEN `d MOD 2 = (d MOD 4) MOD 2` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; MOD_MOD]; ASM_REWRITE_TAC[]] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CNR_QC_SCALE = prove
 (`!q s x y. prime q /\ ~(q divides s)
             ==> (&q divides &2 * (&s * x) + &s * y <=>
                  &q divides &2 * x + y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INT_ARITH `&2 * (s * x) + s * y:int = s * (&2 * x + y)`] THEN
  ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ; GSYM num_divides]);;

let CNR_QC_NORM = prove
 (`!d q x y. d MOD 4 = 3 /\ prime q /\ q divides d /\
             &q divides prin_form d x y
             ==> &q divides &2 * x + y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&q divides (&2 * x + y) * (&2 * x + y:int)` MP_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `!e n s y w:int. e divides n /\ e divides w /\
                      &4 * n = s pow 2 + w * y pow 2
                      ==> e divides s * s`) THEN
    MAP_EVERY EXISTS_TAC [`prin_form d x y`; `y:int`; `&d:int`] THEN
    ASM_SIMP_TAC[CLASSNO_REP_NORM4; GSYM num_divides];
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]]);;

let CNR_QC_MUL = prove
 (`!d q a b u v.
        d MOD 4 = 3 /\ prime q /\ q divides d /\
        ~(&q divides &2 * a + b)
        ==> (&q divides &2 * (a * u - &((d + 1) DIV 4) * b * v) +
                        (a * v + b * u + b * v) <=>
             &q divides &2 * u + v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `coprime(&q:int,&2) /\ coprime(&q:int,&2 * a + b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CNR_INT_COPRIME_2 THEN EXISTS_TAC `d:num` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[INT_PRIME_COPRIME_EQ; INT_PRIME]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (&2 * (a * u - &((d + 1) DIV 4) * b * v) + (a * v + b * u + b * v)) =
    (&2 * a + b) * (&2 * u + v) - &d * b * v:int`
  ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `k:num` (fun th ->
      SUBST1_TAC(CONJUNCT2 th) THEN SUBST1_TAC(CONJUNCT1 th)) o
      MATCH_MP CLASSNO_REP_DMOD4) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&q divides (&2 * a + b) * (&2 * u + v:int)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(INTEGER_RULE
     `!q a b:int. coprime(q,a) ==> (q divides a * b <=> q divides b)`) THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&q divides &2 * (&2 * (a * u - &((d + 1) DIV 4) * b * v) +
                               (a * v + b * u + b * v):int)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!q a b:int. coprime(q,a) ==> (q divides a * b <=> q divides b)`) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!q x y:int. q divides y ==> (q divides x - y <=> q divides x)`) THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN MATCH_MP_TAC INT_DIVIDES_RMUL THEN
    REWRITE_TAC[GSYM num_divides] THEN FIRST_ASSUM ACCEPT_TAC]);;
(* ------------------------------------------------------------------------- *)
(* 3. Polynomial identities of the substitutions (h = (q - 1) / 2,           *)
(*    g = (p + 1) / 2, c2 = (p + q) / 4), and the ideal Q: its elements of   *)
(*    norm q n correspond to the solutions of f2(u,v) = n by                 *)
(*    (u,v) -> (q u + h v, v).                                               *)
(* ------------------------------------------------------------------------- *)

let CNR_INT_PARAM = prove
 (`!p q. p MOD 4 = 1 /\ q MOD 4 = 3
         ==> ?j k. &((p * q + 1) DIV 4) =
                     (&4 * &j * &k + &3 * &j + &k + &1):int /\
                   &((p + q) DIV 4) = (&j + &k + &1):int /\
                   &((q - 1) DIV 2) = (&2 * &k + &1):int /\
                   &((p + 1) DIV 2) = (&2 * &j + &1):int /\
                   &p = (&4 * &j + &1):int /\ &q = (&4 * &k + &3):int`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_PARAM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:num`] THEN
  SUBGOAL_THEN `(q - 1) DIV 2 = 2 * k + 1 /\ (p + 1) DIV 2 = 2 * j + 1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL]]);;

let CNR_HALVES = prove
 (`!p q. p MOD 4 = 1 /\ q MOD 4 = 3
         ==> &2 * &((p + 1) DIV 2) - &1 = &p:int /\
             &2 * &((q - 1) DIV 2) + &1 = &q:int /\
             ~(p = 0) /\ ~(q = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[MOD_0; ARITH_RULE `~(0 = 1)`;
                                           ARITH_RULE `~(0 = 3)`]]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CNR_INT_PARAM) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let CNR_IDENT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CNR_INT_PARAM) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[prin_form; qform] THEN CONV_TAC INT_RING;;

let CNR_IDENT_B = prove
 (`!p q u v. p MOD 4 = 1 /\ q MOD 4 = 3
             ==> prin_form (p * q) (&q * u + &((q - 1) DIV 2) * v)
                                   (&0 * u + &1 * v) =
                 &q * qform (&q) (&q) (&((p + q) DIV 4)) u v`,
  CNR_IDENT_TAC);;

let CNR_IDENT_P1 = prove
 (`!p q u v. p MOD 4 = 1 /\ q MOD 4 = 3
             ==> prin_form (p * q) (&1 * u + &((p + 1) DIV 2) * v)
                                   (--(&2) * u + --(&1) * v) =
                 &p * qform (&q) (&q) (&((p + q) DIV 4)) u v`,
  CNR_IDENT_TAC);;

let CNR_IDENT_P2 = prove
 (`!p q u v. p MOD 4 = 1 /\ q MOD 4 = 3
             ==> qform (&q) (&q) (&((p + q) DIV 4))
                   (--(&1) * u + --(&((p + 1) DIV 2)) * v) (&2 * u + &1 * v) =
                 &p * prin_form (p * q) u v`,
  CNR_IDENT_TAC);;

let CNR_IDENT_Q2 = prove
 (`!p q u v. p MOD 4 = 1 /\ q MOD 4 = 3
             ==> qform (&q) (&q) (&((p + q) DIV 4))
                   (&1 * u + --(&((q - 1) DIV 2)) * v) (&0 * u + &q * v) =
                 &q * prin_form (p * q) u v`,
  CNR_IDENT_TAC);;

let CNR_IDENT_SPLIT = prove
 (`!p q u0 v0 u v.
        p MOD 4 = 1 /\ q MOD 4 = 3
        ==> prin_form (p * q)
              ((&q * u0 + &((q - 1) DIV 2) * v0) * u +
               (&((q - 1) DIV 2) * u0 +
                (&((q - 1) DIV 2) - &((p + q) DIV 4)) * v0) * v)
              (v0 * u + (u0 + v0) * v) =
            qform (&q) (&q) (&((p + q) DIV 4)) u0 v0 *
            qform (&q) (&q) (&((p + q) DIV 4)) u v`,
  CNR_IDENT_TAC);;

let CNR_B_CARD = prove
 (`!p q n. p MOD 4 = 1 /\ q MOD 4 = 3
           ==> CARD {(x,y) | prin_form (p * q) x y = &(q * n) /\
                             &q divides &2 * x + y} =
               qform_rep (&q) (&q) (&((p + q) DIV 4)) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[qform_rep] THEN
  MP_TAC(ISPECL [`prin_form (p * q)`; `qform (&q) (&q) (&((p + q) DIV 4))`;
                 `&q:int`; `&((q - 1) DIV 2):int`; `&0:int`; `&1:int`;
                 `&q:int`; `n:num`] QFORM_REP_LINEAR_CARD0) THEN
  ASM_SIMP_TAC[CNR_IDENT_B; CNR_F2_FINITE; INT_OF_NUM_EQ; INT_MUL_RID;
               INT_MUL_RZERO; INT_SUB_RZERO] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO; INT_MUL_LID;
              GSYM INT_OF_NUM_MUL; INTEGER_RULE `(q:int) divides q * y`] THEN
  MP_TAC(SPECL [`&q:int`; `&((q - 1) DIV 2):int`; `x:int`; `y:int`]
    CNR_DIVIDES_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. The ramified primes p and q: the cross maps between the two forms,     *)
(*    r_f(p n) = r_f2(n), r_f2(p n) = r_f(n), r_f(q n) = r_f2(n),            *)
(*    r_f2(q n) = r_f(n) (z -> z sqrt(-d) / p and z -> q z in coordinates).  *)
(* ------------------------------------------------------------------------- *)

let CNR_DIVIDES_HALF2 = prove
 (`!p g x y:int. p = &2 * g - &1 /\ p divides &2 * x + y
                 ==> p divides x + g * y`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[int_divides] THEN DISCH_THEN(X_CHOOSE_TAC `t:int`) THEN
  EXISTS_TAC `g * t - x:int` THEN POP_ASSUM MP_TAC THEN CONV_TAC INT_RING);;

let CNR_PQ_DISTINCT = prove
 (`!p q. p MOD 4 = 1 /\ q MOD 4 = 3 ==> ~(p = q)`,
  MESON_TAC[ARITH_RULE `~(1 = 3)`]);;

let CNR_PQ_BASICS = prove
 (`!p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
         ==> (p * q) MOD 4 = 3 /\ p divides p * q /\ q divides p * q /\
             ~(p divides q) /\ ~(q divides p) /\
             ~(&p divides &q:int) /\ ~(&q divides &p:int)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p:num = q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CNR_PQ_DISTINCT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM num_divides; DIVIDES_PRIME_PRIME; DIVIDES_RMUL;
               DIVIDES_LMUL; DIVIDES_REFL] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CNR_F2_RAMIFIED = prove
 (`!p q u v. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
             ==> (&p divides qform (&q) (&q) (&((p + q) DIV 4)) u v
                  ==> &p divides &2 * u + v) /\
                 (&q divides qform (&q) (&q) (&((p + q) DIV 4)) u v
                  ==> &q divides v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `u:int`; `v:int`] CNR_F2_NORM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `&p divides &q * (&2 * u + v) * (&2 * u + v:int)` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!p n v w:int. p divides n /\ &4 * n = w + p * v pow 2
                      ==> p divides w`) THEN
      MAP_EVERY EXISTS_TAC
       [`qform (&q) (&q) (&((p + q) DIV 4)) u v`; `v:int`] THEN
      ASM_REWRITE_TAC[INT_POW_2];
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]];
    SUBGOAL_THEN `&q divides &p * v * (v:int)` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!q n s w:int. q divides n /\ &4 * n = q * s + w ==> q divides w`) THEN
      MAP_EVERY EXISTS_TAC
       [`qform (&q) (&q) (&((p + q) DIV 4)) u v`; `(&2 * u + v:int) pow 2`] THEN
      ASM_REWRITE_TAC[INT_POW_2];
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]]]);;

let CNR_RAMIFIED_P1 = prove
 (`!p q n. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
           ==> prin_rep (p * q) (p * n) =
               qform_rep (&q) (&q) (&((p + q) DIV 4)) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[qform_rep; prin_rep] THEN
  MP_TAC(ISPECL [`prin_form (p * q)`; `qform (&q) (&q) (&((p + q) DIV 4))`;
                 `&1:int`; `&((p + 1) DIV 2):int`; `--(&2):int`; `--(&1):int`;
                 `&p:int`; `n:num`] QFORM_REP_LINEAR_CARD0) THEN
  SUBGOAL_THEN `&1 * --(&1) - &((p + 1) DIV 2) * --(&2) = &p:int`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&2 * &((p + 1) DIV 2) - &1 = &p:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR_IDENT_P1; CNR_F2_FINITE; INT_OF_NUM_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC(TAUT `(a ==> b /\ c) ==> (a <=> a /\ b /\ c)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&p divides &2 * x + y` ASSUME_TAC THENL
   [MATCH_MP_TAC CNR_QC_NORM THEN EXISTS_TAC `p * q` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTEGER_RULE `!p n:int. p divides p * n`];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `--(&1) * x - g * y = --(x + g * y):int`;
              INT_ARITH `&1 * y - --(&2) * x = &2 * x + y:int`;
              INTEGER_RULE `(p:int) divides --x <=> p divides x`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CNR_DIVIDES_HALF2 THEN
  ASM_REWRITE_TAC[]);;

let CNR_RAMIFIED_P2 = prove
 (`!p q n. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
           ==> qform_rep (&q) (&q) (&((p + q) DIV 4)) (p * n) =
               prin_rep (p * q) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[qform_rep; prin_rep] THEN
  MP_TAC(ISPECL [`qform (&q) (&q) (&((p + q) DIV 4))`; `prin_form (p * q)`;
                 `--(&1):int`; `--(&((p + 1) DIV 2)):int`; `&2:int`; `&1:int`;
                 `&p:int`; `n:num`] QFORM_REP_LINEAR_CARD0) THEN
  SUBGOAL_THEN `--(&1) * &1 - --(&((p + 1) DIV 2)) * &2 = &p:int`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&2 * &((p + 1) DIV 2) - &1 = &p:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR_IDENT_P2; CLASSNO_REP_FINITE; INT_OF_NUM_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC(TAUT `(a ==> b /\ c) ==> (a <=> a /\ b /\ c)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&p divides &2 * x + y` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `x:int`; `y:int`] CNR_F2_RAMIFIED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[INTEGER_RULE `!p n:int. p divides p * n`];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `&1 * x - --g * y = x + g * y:int`;
              INT_ARITH `--(&1) * y - &2 * x = --(&2 * x + y):int`;
              INTEGER_RULE `(p:int) divides --x <=> p divides x`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CNR_DIVIDES_HALF2 THEN
  ASM_REWRITE_TAC[]);;

let CNR_RAMIFIED_Q1 = prove
 (`!p q n. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
           ==> prin_rep (p * q) (q * n) =
               qform_rep (&q) (&q) (&((p + q) DIV 4)) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CNR_B_CARD] THEN REWRITE_TAC[prin_rep] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC CNR_QC_NORM THEN EXISTS_TAC `p * q` THEN
  ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL]);;

let CNR_RAMIFIED_Q2 = prove
 (`!p q n. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
           ==> qform_rep (&q) (&q) (&((p + q) DIV 4)) (q * n) =
               prin_rep (p * q) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[qform_rep; prin_rep] THEN
  MP_TAC(ISPECL [`qform (&q) (&q) (&((p + q) DIV 4))`; `prin_form (p * q)`;
                 `&1:int`; `--(&((q - 1) DIV 2)):int`; `&0:int`; `&q:int`;
                 `&q:int`; `n:num`] QFORM_REP_LINEAR_CARD0) THEN
  SUBGOAL_THEN `&1 * &q - --(&((q - 1) DIV 2)) * &0 = &q:int`
  SUBST1_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CNR_IDENT_Q2; CLASSNO_REP_FINITE; INT_OF_NUM_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC(TAUT `(a ==> b /\ c) ==> (a <=> a /\ b /\ c)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&q divides (y:int)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `x:int`; `y:int`] CNR_F2_RAMIFIED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[INTEGER_RULE `!p n:int. p divides p * n`];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `q * x - --h * y = q * x + h * y:int`;
              INT_ARITH `&1 * y - &0 * x = y:int`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!q x h y:int. q divides y ==> q divides q * x + h * y`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Inert primes (jacobi(r, p q) = -1): r | N z forces r | z, in both      *)
(*    lattices; r_F(r n) = [r | n] r_F(n / r).                               *)
(* ------------------------------------------------------------------------- *)

let CNR_COPRIME_DIVIDES_MUL = prove
 (`!q r n. prime q /\ prime r /\ ~(r = q)
           ==> (r divides q * n <=> r divides n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME]);;

let CNR_INERT_REC = prove
 (`!p q r n.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
        prime r /\ jacobi(r,p * q) = --(&1)
        ==> prin_rep (p * q) (r * n) =
              (if r divides n then prin_rep (p * q) (n DIV r) else 0) /\
            qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n) =
              (if r divides n
               then qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)
               else 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0) /\ ~(r:num = q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `jacobi(q,p * q) = --(&1)` THEN
    REWRITE_TAC[JACOBI_RMUL] THEN
    ASM_SIMP_TAC[CLASSNO_REP_JACOBI_SELF; INT_MUL_RZERO] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. &r divides prin_form (p * q) x y ==> &r divides x /\ &r divides y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC QFORM_REP_INERT_DIVIDES THEN
    EXISTS_TAC `p * q` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`p * q`; `r:num`; `n:num`] CLASSNO_REP_CARD_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[prin_rep] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n) =
    CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                  &r divides x /\ &r divides y /\ &q divides &2 * x + y}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM CNR_B_CARD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    SUBST1_TAC(ARITH_RULE `q * r * n = r * q * n`) THEN
    MATCH_MP_TAC(TAUT `(a ==> b /\ c) ==> (a /\ d <=> a /\ b /\ c /\ d)`) THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p * q`; `r:num`; `q * n`; `\x y:int. &q divides &2 * x + y`]
    QFORM_REP_CARD_SCALE_P) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC CNR_QC_SCALE THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CNR_COPRIME_DIVIDES_MUL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
  SUBST1_TAC(ARITH_RULE `q * r * m = r * q * m`) THEN
  ASM_SIMP_TAC[DIV_MULT; CNR_B_CARD]);;

(* ------------------------------------------------------------------------- *)
(* 6. Split primes r: an element tau of Z[w] with r | N tau, not r^2 | N tau *)
(*    (N tau = r, or N tau = q r for tau in Q). Every z with r | N z is      *)
(*    divisible by the prime above r through tau or through conj tau, by     *)
(*    both iff r | z: inclusion-exclusion with a predicate P                 *)
(*    (QFORM_REP_SPLIT_DECOMP of Baker/classno_rep.ml).                      *)
(* ------------------------------------------------------------------------- *)

let CNR_RR_NOT_DIVIDES = prove
 (`!r k. prime r /\ ~(r divides k) ==> ~(&r * &r divides &(k * r):int)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[INT_OF_NUM_MUL; GSYM num_divides] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIVIDES_LMUL2_EQ; PRIME_IMP_NZ]);;

let CNR_QC_PI = prove
 (`!d q a b k. d MOD 4 = 3 /\ prime q /\ q divides d /\ ~(q divides k) /\
               prin_form d a b = &k
               ==> ~(&q divides &2 * a + b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `coprime(&q:int,&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CNR_INT_COPRIME_2 THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(q divides k)` THEN REWRITE_TAC[num_divides] THEN
  SUBGOAL_THEN `&q divides &2 * &2 * (&k:int)` MP_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `!q s D y k:int. q divides s /\ q divides D /\
                      &4 * k = s pow 2 + D * y pow 2
                      ==> q divides &2 * &2 * k`) THEN
    MAP_EVERY EXISTS_TAC [`&2 * a + b:int`; `&d:int`; `b:int`] THEN
    ASM_REWRITE_TAC[GSYM num_divides] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[CLASSNO_REP_NORM4];
    ASM_SIMP_TAC[INTEGER_RULE
     `!q a b:int. coprime(q,a) ==> (q divides a * b <=> q divides b)`]]);;

let CNR_SPLIT_PLUS = prove
 (`!p q r a b n.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\ prime r /\
        ~(r divides p * q) /\ prin_form (p * q) a b = &r
        ==> prin_rep (p * q) (r * n) +
              (if r divides n then prin_rep (p * q) (n DIV r) else 0) =
            2 * prin_rep (p * q) n /\
            qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n) +
              (if r divides n
               then qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)
               else 0) =
            2 * qform_rep (&q) (&q) (&((p + q) DIV 4)) n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0) /\ ~(r:num = q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q divides r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `prin_form (p * q) (a + b) (--b) = &r` ASSUME_TAC THENL
   [UNDISCH_TAC `prin_form (p * q) a b = &r` THEN REWRITE_TAC[prin_form] THEN
    SPEC_TAC(`&((p * q + 1) DIV 4):int`,`c:int`) THEN GEN_TAC THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&r divides prin_form (p * q) a b /\
    ~(&r * &r divides prin_form (p * q) a b) /\
    ~(&r divides &(p * q):int)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_DIVIDES_REFL; DIVIDES_REFL; GSYM num_divides] THEN
    MATCH_MP_TAC(REWRITE_RULE[MULT_CLAUSES]
      (SPECL [`r:num`; `1`] CNR_RR_NOT_DIVIDES)) THEN
    ASM_REWRITE_TAC[DIVIDES_ONE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p * q`; `r:num`; `a:int`; `b:int`; `n:num`;
                   `\x:int y:int. T`] QFORM_REP_SPLIT_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CLASSNO_REP_CARD_MUL; CLASSNO_REP_CARD_SCALE;
                 GSYM prin_rep] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(&q divides &2 * a + b) /\ ~(&q divides &2 * (a + b) + --b)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_ARITH `&2 * (a + b) + --b = &2 * a + b:int`] THEN
    MATCH_MP_TAC CNR_QC_PI THEN
    MAP_EVERY EXISTS_TAC [`p * q`; `r:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p * q`; `r:num`; `a:int`; `b:int`; `q * n`;
                 `\x y:int. &q divides &2 * x + y`] QFORM_REP_SPLIT_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a' b'. prin_form (p * q) a' b' = &r /\ ~(&q divides &2 * a' + b')
            ==> CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                              &r divides (a' + b') * x +
                                         &((p * q + 1) DIV 4) * b' * y /\
                              &r divides a' * y - b' * x /\
                              &q divides &2 * x + y} =
                qform_rep (&q) (&q) (&((p + q) DIV 4)) n`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM CNR_B_CARD] THEN
    MP_TAC(ISPECL [`p * q`; `a':int`; `b':int`; `r:num`; `q * n`;
                   `\x y:int. &q divides &2 * x + y`] QFORM_REP_CARD_MUL_P) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC CNR_QC_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                  &q divides &2 * x + y} =
    qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM CNR_B_CARD] THEN
    SUBST1_TAC(ARITH_RULE `q * r * n = r * q * n`) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                  &r divides x /\ &r divides y /\ &q divides &2 * x + y} =
    if r divides n then qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)
    else 0`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p * q`; `r:num`; `q * n`;
                  `\x y:int. &q divides &2 * x +
                    y`] QFORM_REP_CARD_SCALE_P) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC CNR_QC_SCALE THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[CNR_COPRIME_DIVIDES_MUL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    SUBST1_TAC(ARITH_RULE `q * r * m = r * q * m`) THEN
    ASM_SIMP_TAC[DIV_MULT; CNR_B_CARD];
    ARITH_TAC]);;

(* An element (a,b) of the ideal Q (q | 2 a + b, q not dividing a): z is     *)
(* in Q iff q divides both coordinates of conj(a,b) z.                       *)

let CNR_DIVIDES_UNIT = prove
 (`!q u x y:int. coprime(q,u) /\ q divides x - u * y
                 ==> (q divides x <=> q divides y)`,
  INTEGER_TAC);;

let CNR_QC_DQ = prove
 (`!d q a b x y.
        d MOD 4 = 3 /\ prime q /\ q divides d /\
        &q divides &2 * a + b /\ ~(&q divides a)
        ==> (&q divides (a + b) * x + &((d + 1) DIV 4) * b * y /\
             &q divides a * y - b * x <=>
             &q divides &2 * x + y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `coprime(&q:int,&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CNR_INT_COPRIME_2 THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(&q:int,a) /\ coprime(&q:int,--a)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_PRIME_COPRIME_EQ; INT_PRIME; INT_DIVIDES_RNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * &((d + 1) DIV 4) = &d + &1:int` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `k:num` (fun th ->
      SUBST1_TAC(CONJUNCT2 th) THEN SUBST1_TAC(CONJUNCT1 th)) o
      MATCH_MP CLASSNO_REP_DMOD4) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&q divides (a + b) * x + &((d + 1) DIV 4) * b * y <=>
     &q divides x + &2 * &((d + 1) DIV 4) * y) /\
    (&q divides a * y - b * x <=> &q divides &2 * x + y) /\
    (&q divides &2 * x + y <=> &q divides x + &2 * &((d + 1) DIV 4) * y)`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CNR_DIVIDES_UNIT THENL
   [EXISTS_TAC `--a:int` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!q a b c x y:int. q divides &2 * a + b
        ==> q divides ((a + b) * x + c * b * y) - --a * (x + &2 * c * y)`) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `a:int` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!q a b x y:int. q divides &2 * a + b
        ==> q divides (a * y - b * x) - a * (&2 * x + y)`) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `&2:int` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!q c d x y:int. q divides d /\ &4 * c = d + &1
        ==> q divides (&2 * x + y) - &2 * (x + &2 * c * y)`) THEN
    EXISTS_TAC `&d:int` THEN ASM_REWRITE_TAC[GSYM num_divides]]);;

let CNR_IDENT_COND = prove
 (`!p q u0 v0 x y.
        p MOD 4 = 1 /\ q MOD 4 = 3
        ==> &q * ((u0 + v0) * x -
                  (&((q - 1) DIV 2) * (u0:int) +
                   (&((q - 1) DIV 2) - &((p + q) DIV 4)) * v0) * y) =
            (((&q * u0 + &((q - 1) DIV 2) * v0) + v0) * x +
             &((p * q + 1) DIV 4) * v0 * y) -
            &((q - 1) DIV 2) *
            ((&q * u0 + &((q - 1) DIV 2) * v0) * y - v0 * (x:int))`,
  CNR_IDENT_TAC);;

let CNR_CROSS_CARD = prove
 (`!p q r u0 v0 n.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
        prime r /\ ~(r = q) /\
        qform (&q) (&q) (&((p + q) DIV 4)) u0 v0 = &r
        ==> CARD {(x,y) | prin_form (p * q) x y = &(r * n) /\
                          &r divides
                            ((&q * u0 + &((q - 1) DIV 2) * v0) + v0) * x +
                            &((p * q + 1) DIV 4) * v0 * y /\
                          &r divides
                            (&q * u0 + &((q - 1) DIV 2) * v0) * y - v0 * x} =
            qform_rep (&q) (&q) (&((p + q) DIV 4)) n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `coprime(&r:int,&q)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM num_coprime] THEN ASM_SIMP_TAC[COPRIME_PRIME_PRIME];
    ALL_TAC] THEN
  REWRITE_TAC[qform_rep] THEN
  MP_TAC(ISPECL [`prin_form (p * q)`; `qform (&q) (&q) (&((p + q) DIV 4))`;
                 `&q * u0 + &((q - 1) DIV 2) * v0:int`;
                 `&((q - 1) DIV 2) * u0 +
                  (&((q - 1) DIV 2) - &((p + q) DIV 4)) * v0:int`;
                 `v0:int`; `u0 + v0:int`; `&r:int`; `n:num`]
    QFORM_REP_LINEAR_CARD0) THEN
  SUBGOAL_THEN
   `(&q * u0 + &((q - 1) DIV 2) * v0) * (u0 + v0) -
    (&((q - 1) DIV 2) * u0 + (&((q - 1) DIV 2) - &((p + q) DIV 4)) * v0) *
    v0 = &r:int`
  SUBST1_TAC THENL
   [UNDISCH_TAC `qform (&q) (&q) (&((p + q) DIV 4)) u0 v0 = &r` THEN
    REWRITE_TAC[qform] THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR_IDENT_SPLIT; CNR_F2_FINITE; INT_OF_NUM_EQ; PRIME_IMP_NZ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!r q x k1 k2 h:int. q * x = k1 - h * k2 /\ coprime(r,q)
                        ==> (r divides x /\ r divides k2 <=>
                             r divides k1 /\ r divides k2)`) THEN
  MAP_EVERY EXISTS_TAC [`&q:int`; `&((q - 1) DIV 2):int`] THEN
  ASM_SIMP_TAC[CNR_IDENT_COND]);;

let CNR_SPLIT_MINUS_GEN = prove
 (`!p q r a b n.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\ prime r /\
        ~(r divides p * q) /\ prin_form (p * q) a b = &(q * r) /\
        &q divides &2 * a + b /\
        CARD {(x,y) | prin_form (p * q) x y = &(r * n) /\
                      &r divides (a + b) * x + &((p * q + 1) DIV 4) * b * y /\
                      &r divides a * y - b * x} =
        qform_rep (&q) (&q) (&((p + q) DIV 4)) n /\
        CARD {(x,y) | prin_form (p * q) x y = &(r * n) /\
                      &r divides ((a + b) + --b) * x +
                                 &((p * q + 1) DIV 4) * --b * y /\
                      &r divides (a + b) * y - --b * x} =
        qform_rep (&q) (&q) (&((p + q) DIV 4)) n
        ==> prin_rep (p * q) (r * n) +
              (if r divides n then prin_rep (p * q) (n DIV r) else 0) =
            2 * qform_rep (&q) (&q) (&((p + q) DIV 4)) n /\
            qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n) +
              (if r divides n
               then qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)
               else 0) =
            2 * prin_rep (p * q) n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0) /\ ~(r:num = q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q divides r) /\ coprime(&q:int,&r)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIVIDES_PRIME_PRIME; GSYM num_coprime;
                  COPRIME_PRIME_PRIME] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `prin_form (p * q) (a + b) (--b) = &(q * r)` ASSUME_TAC THENL
   [UNDISCH_TAC `prin_form (p * q) a b = &(q * r)` THEN
    REWRITE_TAC[prin_form] THEN
    SPEC_TAC(`&((p * q + 1) DIV 4):int`,`c:int`) THEN GEN_TAC THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&r divides prin_form (p * q) a b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM num_divides] THEN
    MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&r * &r divides prin_form (p * q) a b)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CNR_RR_NOT_DIVIDES THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&r divides &(p * q):int)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM num_divides]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p * q`; `r:num`; `a:int`; `b:int`; `n:num`;
                   `\x:int y:int. T`] QFORM_REP_SPLIT_DECOMP) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CLASSNO_REP_CARD_SCALE; GSYM prin_rep] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&q divides a) /\ ~(&q divides a + b)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPECL [`q:num`; `r:num`] CNR_RR_NOT_DIVIDES) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `r * q = q * r`) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `prin_form (p * q) a b`)) THEN
      REWRITE_TAC[prin_form] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!q a b c:int. q divides a /\ q divides &2 * a + b
                      ==> (q * q) divides a pow 2 + a * b + c * b pow 2`) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `&q divides &2 * a + b` THEN
      MATCH_MP_TAC(TAUT `(a /\ b ==> c) ==> a ==> ~c ==> ~b`) THEN
      CONV_TAC INTEGER_RULE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p * q`; `r:num`; `a:int`; `b:int`; `q * n`;
                 `\x y:int. &q divides &2 * x + y`] QFORM_REP_SPLIT_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a' b'. prin_form (p * q) a' b' = &(q * r) /\
            &q divides &2 * a' + b' /\ ~(&q divides a')
            ==> CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                              &r divides (a' + b') * x +
                                         &((p * q + 1) DIV 4) * b' * y /\
                              &r divides a' * y - b' * x /\
                              &q divides &2 * x + y} =
                prin_rep (p * q) n`
  (fun th -> MP_TAC(SPECL [`a:int`; `b:int`] th) THEN
             MP_TAC(SPECL [`a + b:int`; `--b:int`] th)) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`p * q`; `a':int`; `b':int`; `q * r`; `n:num`]
      CLASSNO_REP_CARD_MUL) THEN
    ASM_SIMP_TAC[MULT_EQ_0; DE_MORGAN_THM; PRIME_IMP_NZ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    SUBST1_TAC(ARITH_RULE `r * q * n = (q * r) * n`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    MP_TAC(ISPECL [`&q:int`; `&r:int`;
                   `(a' + b') * x + &((p * q + 1) DIV 4) * b' * (y:int)`;
                   `a' * y - b' * (x:int)`]
     (INTEGER_RULE
       `!q r x y:int. coprime(q,r)
          ==> ((q * r) divides x /\ (q * r) divides y <=>
               (q divides x /\ q divides y) /\
               (r divides x /\ r divides y))`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`p * q`; `q:num`; `a':int`; `b':int`; `x:int`; `y:int`]
      CNR_QC_DQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `&2 * (a + b) + --b:int = &2 * a + b`] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                  &q divides &2 * x + y} =
    qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM CNR_B_CARD] THEN
    SUBST1_TAC(ARITH_RULE `q * r * n = r * q * n`) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {(x,y) | prin_form (p * q) x y = &(r * q * n) /\
                  &r divides x /\ &r divides y /\ &q divides &2 * x + y} =
    if r divides n then qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)
    else 0`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`p * q`; `r:num`; `q * n`;
                  `\x y:int. &q divides &2 * x +
                    y`] QFORM_REP_CARD_SCALE_P) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC CNR_QC_SCALE THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[CNR_COPRIME_DIVIDES_MUL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    SUBST1_TAC(ARITH_RULE `q * r * m = r * q * m`) THEN
    ASM_SIMP_TAC[DIV_MULT; CNR_B_CARD];
    ARITH_TAC]);;

let CNR_SPLIT_MINUS = prove
 (`!p q r u0 v0 n.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\ prime r /\
        ~(r divides p * q) /\
        qform (&q) (&q) (&((p + q) DIV 4)) u0 v0 = &r
        ==> prin_rep (p * q) (r * n) +
              (if r divides n then prin_rep (p * q) (n DIV r) else 0) =
            2 * qform_rep (&q) (&q) (&((p + q) DIV 4)) n /\
            qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n) +
              (if r divides n
               then qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)
               else 0) =
            2 * prin_rep (p * q) n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r:num = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CNR_SPLIT_MINUS_GEN THEN
  MAP_EVERY EXISTS_TAC [`&q * u0 + &((q - 1) DIV 2) * v0:int`; `v0:int`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `u0:int`; `v0:int`] CNR_IDENT_B) THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_ADD_LID] THEN
    REWRITE_TAC[INT_OF_NUM_MUL];
    REWRITE_TAC[int_divides] THEN EXISTS_TAC `&2 * u0 + v0:int` THEN
    UNDISCH_TAC `&2 * &((q - 1) DIV 2) + &1 = &q:int` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC INT_RING;
    MATCH_MP_TAC CNR_CROSS_CARD THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `u0 + v0:int`; `--v0:int`;
                  `n:num`] CNR_CROSS_CARD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `qform (&q) (&q) (&((p + q) DIV 4)) u0 v0 = &r` THEN
      REWRITE_TAC[qform] THEN CONV_TAC INT_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&q * (u0 + v0) + &((q - 1) DIV 2) * --v0 =
      (&q * u0 + &((q - 1) DIV 2) * v0) + v0:int`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&2 * &((q - 1) DIV 2) + &1 = &q:int` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC INT_RING;
      REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Split primes are represented by f or by f2 (form_classno(-d) = 2: a    *)
(*    reduced form representing r, QFORM_REPRESENTED_REDUCED, and the        *)
(*    reduction of f2, QFORM_REDUCE_FORM); which one is decided by           *)
(*    the value characters: values of f prime to p are residues mod p,       *)
(*    values of f2 have the character (q | p) = -1 (CN_GENUS_CHARACTER).     *)
(* ------------------------------------------------------------------------- *)

let CNR_PQ_SIZE = prove
 (`!p q. prime p /\ p MOD 4 = 1 /\ q MOD 4 = 3
         ==> &5 <= &p:int /\ &3 <= &q:int`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INT_OF_NUM_LE] THEN
  SUBGOAL_THEN `~(p = 1)` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `4`] DIVISION) THEN
  MP_TAC(SPECL [`q:num`; `4`] DIVISION) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  ASM_CASES_TAC `p DIV 4 = 0` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let CNR_F2_NOT_ONE = prove
 (`!p q x y. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
             ==> ~(qform (&q) (&q) (&((p + q) DIV 4)) x y = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:int`; `y:int`] CNR_F2_NORM4) THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_SIZE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:int = &0` THENL
     [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= (x:int) pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `x:int` CLASSNO_REP_ABS_LE_POW2) THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&0:int) <= (&q - &3) * x pow 2` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    SUBGOAL_THEN `&1 <= (y:int) pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&0:int) <= (&p - &5) * y pow 2 /\
                  (&0:int) <= &q * (&2 * x + y) pow 2`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN
      REWRITE_TAC[INT_LE_POW_2] THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC]);;

let CNR_TWO_FORMS_REP = prove
 (`!p q r. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
           form_classno (--(&(p * q))) = 2 /\ ~(r = 0) /\
           (?b:int. (b pow 2 + &(p * q) == &0) (mod (&4 * &r)))
           ==> (?x y. prin_form (p * q) x y = &r) \/
               (?x y. qform (&q) (&q) (&((p + q) DIV 4)) x y = &r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `squarefree(p * q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE; PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `c:int` o
    REWRITE_RULE[int_congruent; INT_SUB_RZERO]) THEN
  MP_TAC(SPECL [`p * q`; `r:num`; `b:int`; `c:int`]
    QFORM_REPRESENTED_REDUCED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_MUL_ASSOC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SQUAREFREE_IMP_NZ];
      MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `p * q` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `b pow 2 + &(p * q) = (&4 * &r) * c:int` THEN INT_ARITH_TAC];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a1:int`; `b1:int`; `c1:int`; `x:int`; `y:int`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`&q:int`; `&q:int`; `&((p + q) DIV 4):int`; `p * q`]
    QFORM_REDUCE_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `0 < q <=> ~(q = 0)`];
      MP_TAC(SPECL [`p:num`; `q:num`] CNR_INT_PARAM) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:int` (X_CHOOSE_THEN `b2:int`
    (X_CHOOSE_THEN `c2:int` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`--(&(p * q)):int`; `a2:int`; `b2:int`; `c2:int`;
                `&1:int`; `&1:int`; `&((p * q + 1) DIV 4):int`;
                `a1:int`; `b1:int`; `c1:int`] CNF_CLASSNO_TWO_OTHER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLASSNO_PRINCIPAL_REDUCED; INT_GCD_1] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1:int` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `qform (&q) (&q) (&((p + q) DIV 4))`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~a /\ b ==> ~(a <=> b)`) THEN CONJ_TAC THENL
     [REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC CNR_F2_NOT_ONE THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`] THEN
      REWRITE_TAC[qform] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [DISJ2_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&r:int` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `qform (&q) (&q) (&((p + q) DIV 4))`))
          (concl th))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN FIRST_ASSUM ACCEPT_TAC;
    DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN
    ASM_REWRITE_TAC[GSYM QFORM_PRIN]]);;

let CNR_JACOBI_SQUARE4 = prove
 (`!p m t:int. prime p /\ ~(p = 2) /\ ~(p divides m) /\
               &p divides t pow 2 - &4 * &m
               ==> jacobi(m,p) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `coprime(2,p) /\ coprime(m,p)` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ; DIVIDES_PRIME_PRIME; PRIME_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(4,p)` ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE `4 = 2 * 2`) THEN ASM_REWRITE_TAC[COPRIME_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(4 * m,p) = &1` MP_TAC THENL
   [MP_TAC(SPECL [`4 * m`; `p:num`] JACOBI_CASES) THEN
    SUBGOAL_THEN `~(jacobi(4 * m,p) = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[JACOBI_EQ_0; COPRIME_LMUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(jacobi(4 * m,p) = --(&1))` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC JACOBI_NE_MINUS1 THEN EXISTS_TAC `num_of_int(abs t)` THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_POW2_ABS] THEN
    REWRITE_TAC[int_congruent] THEN
    UNDISCH_TAC `&p divides t pow 2 - &4 * &m` THEN
    REWRITE_TAC[int_divides] THEN MESON_TAC[];
    REWRITE_TAC[JACOBI_LMUL; ARITH_RULE `4 = 2 EXP 2`; JACOBI_SQUARED] THEN
    ASM_REWRITE_TAC[INT_MUL_LID]]);;

let CNR_MOD4_NOT_2 = prove
 (`!p. p MOD 4 = 1 ==> ~(p = 2)`,
  GEN_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let CNR_F_VALUE_CHAR = prove
 (`!p q r x y. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
               ~(p divides r) /\ prin_form (p * q) x y = &r
               ==> jacobi(r,p) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CNR_JACOBI_SQUARE4 THEN EXISTS_TAC `&2 * x + y:int` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CNR_MOD4_NOT_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`p * q`; `x:int`; `y:int`] CLASSNO_REP_NORM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[int_divides] THEN EXISTS_TAC `--(&q * y pow 2):int` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INT_RING);;

let CNR_F2_VALUE_CHAR = prove
 (`!p q r x y. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
               ~(p divides r) /\
               qform (&q) (&q) (&((p + q) DIV 4)) x y = &r
               ==> jacobi(q * r,p) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CNR_JACOBI_SQUARE4 THEN
  EXISTS_TAC `&q * (&2 * x + y):int` THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CNR_MOD4_NOT_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:int`; `y:int`] CNR_F2_NORM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[int_divides] THEN EXISTS_TAC `--(&q * y pow 2):int` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INT_RING);;

let CNR_SPLIT_SQUARE = prove
 (`!p q r. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\ prime r /\
           jacobi(r,p * q) = &1
           ==> ?b:int. (b pow 2 + &(p * q) == &0) (mod (&4 * &r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `r = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPEC `p * q` CLASSNO_REP_JACOBI_2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN EXISTS_TAC `&1:int` THEN
    REWRITE_TAC[int_congruent; INT_POW_ONE] THEN
    EXISTS_TAC `&((p * q) DIV 8) + &1:int` THEN
    MP_TAC(SPECL [`p * q`; `8`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o AP_TERM `int_of_num` o CONJUNCT1) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(r,p * q)` ASSUME_TAC THENL
   [MATCH_MP_TAC QFORM_REP_JACOBI_NZ THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p * q`; `r:num`] QFORM_REP_JACOBI_ODD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t:int`) THEN
  MATCH_MP_TAC CLASSNO_REP_SPLIT_B THEN EXISTS_TAC `t:int` THEN
  ASM_MESON_TAC[PRIME_ODD]);;

let CNR_SPLIT_REPRESENTED = prove
 (`!p q r. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
           form_classno (--(&(p * q))) = 2 /\ prime r /\
           jacobi(r,p * q) = &1
           ==> (jacobi(r,p) = &1 /\ ?a b. prin_form (p * q) a b = &r) \/
               (jacobi(r,p) = --(&1) /\
                ?u v. qform (&q) (&q) (&((p + q) DIV 4)) u v = &r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `coprime(r,p * q)` ASSUME_TAC THENL
   [MATCH_MP_TAC QFORM_REP_JACOBI_NZ THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p divides r) /\ ~(r = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `coprime(r,r * q)` THEN
      REWRITE_TAC[COPRIME_RMUL; COPRIME_REFL] THEN
      ASM_MESON_TAC[PRIME_1];
      ASM_MESON_TAC[PRIME_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(q,p) = --(&1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`] CN_GENUS_CHARACTER) THEN
    ASM_REWRITE_TAC[qchar] THEN
    REWRITE_TAC[int_eq; int_neg_th; int_of_num_th];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`] CNR_TWO_FORMS_REP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CNR_SPLIT_SQUARE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CNR_F_VALUE_CHAR THEN
      MAP_EVERY EXISTS_TAC [`q:num`; `x:int`; `y:int`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `x:int`; `y:int`]
        CNR_F2_VALUE_CHAR) THEN
      ASM_REWRITE_TAC[JACOBI_LMUL] THEN
      MP_TAC(SPECL [`r:num`; `p:num`] JACOBI_CASES) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
      MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The characters at p and q; the induction step; the representation     *)
(*     formulas.                                                             *)
(* ------------------------------------------------------------------------- *)

let CNR_PQ_ODD = prove
 (`!p q. p MOD 4 = 1 /\ q MOD 4 = 3 ==> ODD p /\ ODD q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ODD_MOD] THEN
  ONCE_REWRITE_TAC[MESON[MOD_MOD; ARITH_RULE `4 = 2 * 2`]
   `n MOD 2 = (n MOD 4) MOD 2`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let CNR_CHI_P = prove
 (`!p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
         form_classno (--(&(p * q))) = 2
         ==> qchar (p * q) p = &0 /\ qchar p p = &0 /\ qchar q p = --(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_ODD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `coprime(q,p) /\ EVEN((p - 1) DIV 2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_PARAM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `(4 * j + 1) - 1 = 2 * 2 * j`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN REWRITE_TAC[EVEN_MULT; ARITH];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CN_GENUS_CHARACTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[qchar; JACOBI_RMUL] THEN
  ASM_SIMP_TAC[CLASSNO_REP_JACOBI_SELF; INT_MUL_LZERO; int_of_num_th] THEN
  MP_TAC(SPECL [`q:num`; `p:num`] JACOBI_RECIPROCITY) THEN
  ASM_REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; EVEN_MULT; INT_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `qchar p q = --(&1)` THEN REWRITE_TAC[qchar]);;

let CNR_CHI_Q = prove
 (`!p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
         form_classno (--(&(p * q))) = 2
         ==> qchar (p * q) q = &0 /\ qchar p q = --(&1) /\ qchar q q = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CN_GENUS_CHARACTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[qchar; JACOBI_RMUL] THEN
  ASM_SIMP_TAC[CLASSNO_REP_JACOBI_SELF; INT_MUL_RZERO; int_of_num_th]);;

let CNR_REP_STEP = prove
 (`!p q r n.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
        form_classno (--(&(p * q))) = 2 /\ prime r /\ ~(n = 0) /\
        &(prin_rep (p * q) n) =
          sum {m | m divides n} (\m. qchar (p * q) m) +
          sum {m | m divides n} (\m. qchar p m * qchar q (n DIV m)) /\
        &(qform_rep (&q) (&q) (&((p + q) DIV 4)) n) =
          sum {m | m divides n} (\m. qchar (p * q) m) -
          sum {m | m divides n} (\m. qchar p m * qchar q (n DIV m)) /\
        (r divides n
         ==> &(prin_rep (p * q) (n DIV r)) =
               sum {m | m divides n DIV r} (\m. qchar (p * q) m) +
               sum {m | m divides n DIV r}
                   (\m. qchar p m * qchar q (n DIV r DIV m)) /\
             &(qform_rep (&q) (&q) (&((p + q) DIV 4)) (n DIV r)) =
               sum {m | m divides n DIV r} (\m. qchar (p * q) m) -
               sum {m | m divides n DIV r}
                   (\m. qchar p m * qchar q (n DIV r DIV m)))
        ==> &(prin_rep (p * q) (r * n)) =
              sum {m | m divides r * n} (\m. qchar (p * q) m) +
              sum {m | m divides r * n}
                  (\m. qchar p m * qchar q ((r * n) DIV m)) /\
            &(qform_rep (&q) (&q) (&((p + q) DIV 4)) (r * n)) =
              sum {m | m divides r * n} (\m. qchar (p * q) m) -
              sum {m | m divides r * n}
                  (\m. qchar p m * qchar q ((r * n) DIV m))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))) THEN
  MP_TAC(ISPECL [`\m. qchar (p * q) m`; `r:num`; `n:num`]
    CLASSNO_REP_DIVISOR_SUM_REC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[qchar; JACOBI_LMUL; int_mul_th]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\m. qchar p m`; `\m. qchar q m`; `r:num`; `n:num`]
    QFORM_REP_DIVSUM_CONV_REC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[qchar; JACOBI_LMUL; int_mul_th]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SPEC_TAC(`sum {m | m divides n DIV r}
                (\m. qchar p m * qchar q (n DIV r DIV m))`,`g2k:real`) THEN
  SPEC_TAC(`sum {m | m divides n DIV r} (\m. qchar (p * q) m)`,`gk:real`) THEN
  SPEC_TAC(`sum {m | m divides n} (\m. qchar p m * qchar q (n DIV m))`,
           `g2n:real`) THEN
  SPEC_TAC(`sum {m | m divides n} (\m. qchar (p * q) m)`,`gn:real`) THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `r:num = p` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`p:num`; `q:num`] CNR_CHI_P) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `n:num`] CNR_RAMIFIED_P1) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `n:num`] CNR_RAMIFIED_P2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `p divides n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r:num = q` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`p:num`; `q:num`] CNR_CHI_Q) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `n:num`] CNR_RAMIFIED_Q1) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `n:num`] CNR_RAMIFIED_Q2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `q divides n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(r,p) /\ coprime(r,q) /\ ~(r divides p * q)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COPRIME_PRIME_PRIME; PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME];
    ALL_TAC] THEN
  SUBGOAL_THEN `qchar (p * q) r = qchar p r * qchar q r` SUBST1_TAC THENL
   [REWRITE_TAC[qchar; JACOBI_RMUL; int_mul_th]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(jacobi(r,p) = &1 \/ jacobi(r,p) = --(&1)) /\
    (jacobi(r,q) = &1 \/ jacobi(r,q) = --(&1))`
  MP_TAC THENL
   [MP_TAC(SPECL [`r:num`; `p:num`] JACOBI_CASES) THEN
    MP_TAC(SPECL [`r:num`; `q:num`] JACOBI_CASES) THEN
    ASM_REWRITE_TAC[JACOBI_EQ_0] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  REWRITE_TAC[qchar] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN ASSUME_TAC)
                             (DISJ_CASES_THEN ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[int_of_num_th; int_neg_th] THENL
   [MP_TAC(SPECL [`p:num`; `q:num`; `r:num`] CNR_SPLIT_REPRESENTED) THEN
    ASM_REWRITE_TAC[JACOBI_RMUL] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_TAC `b:int`)) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `a:int`; `b:int`; `n:num`]
      CNR_SPLIT_PLUS) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r divides n` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `real_of_num`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `n:num`] CNR_INERT_REC) THEN
    ASM_REWRITE_TAC[JACOBI_RMUL] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `r divides n` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `real_of_num`)) THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `n:num`] CNR_INERT_REC) THEN
    ASM_REWRITE_TAC[JACOBI_RMUL] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `r divides n` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `real_of_num`)) THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`] CNR_SPLIT_REPRESENTED) THEN
    ASM_REWRITE_TAC[JACOBI_RMUL] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u0:int` (X_CHOOSE_TAC `v0:int`)) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `u0:int`; `v0:int`; `n:num`]
      CNR_SPLIT_MINUS) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r divides n` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `real_of_num`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC]);;

let CNR_REP_ONE = prove
 (`!p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3
         ==> prin_rep (p * q) 1 = 2 /\
             qform_rep (&q) (&q) (&((p + q) DIV 4)) 1 = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLASSNO_REP_ONE THEN
    MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `q:num`] CNR_PQ_SIZE) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `5 * 3 <= p * q ==> 3 < p * q`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[qform_rep] THEN
    MATCH_MP_TAC(MESON[CARD_CLAUSES] `s:int#int->bool = {} ==> CARD s = 0`) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC CNR_F2_NOT_ONE THEN ASM_REWRITE_TAC[]]);;

let CNR_REP_MAIN = prove
 (`!p q l.
        prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
        form_classno (--(&(p * q))) = 2 /\ 1 <= l
        ==> &(prin_rep (p * q) l) =
              sum {m | m divides l} (\m. qchar (p * q) m) +
              sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m)) /\
            &(qform_rep (&q) (&q) (&((p + q) DIV 4)) l) =
              sum {m | m divides l} (\m. qchar (p * q) m) -
              sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC CLASSNO_REP_PRIME_INDUCT THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`p:num`; `q:num`] CNR_REP_ONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CLASSNO_REP_DIVSUM_ONE] THEN
    REWRITE_TAC[DIVIDES_ONE; SING_GSPEC; SUM_SING; DIV_1; qchar; JACOBI_1;
                int_of_num_th] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `1 <= n /\ n < r * n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `2 * n <= r * n` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CNR_REP_STEP THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o REWRITE_RULE[divides]) THEN
  ASM_SIMP_TAC[DIV_MULT; PRIME_IMP_NZ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `1 <= r * k` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `r * k` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * k <= r * k ==> k <= r * k`) THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let CN_REP_TOTAL_ODD = prove
 (`!p q l. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
           form_classno (--(&(p * q))) = 2 /\ 1 <= l
           ==> &(qform_rep (&1) (&1) (&((p * q + 1) DIV 4)) l) +
               &(qform_rep (&q) (&q) (&((p + q) DIV 4)) l) =
               &2 * sum {m | m divides l} (\m. qchar (p * q) m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[QFORM_REP_PRIN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CNR_REP_MAIN) THEN
  SPEC_TAC(`sum {m | m divides l} (\m. qchar (p * q) m)`,`a:real`) THEN
  SPEC_TAC(`sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m))`,
           `b:real`) THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let CN_REP_GENUS_ODD = prove
 (`!p q l. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
           form_classno (--(&(p * q))) = 2 /\ 1 <= l
           ==> &(qform_rep (&1) (&1) (&((p * q + 1) DIV 4)) l) -
               &(qform_rep (&q) (&q) (&((p + q) DIV 4)) l) =
               &2 * sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[QFORM_REP_PRIN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CNR_REP_MAIN) THEN
  SPEC_TAC(`sum {m | m divides l} (\m. qchar (p * q) m)`,`a:real`) THEN
  SPEC_TAC(`sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m))`,
           `b:real`) THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;
