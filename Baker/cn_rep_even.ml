(* ========================================================================= *)
(* The representation numbers of the two forms of discriminant -4 d when the *)
(* class number is two.                                                      *)
(*                                                                           *)
(* Purpose: for d a prime = 1 mod 4 or d = 2 p (p an odd prime) with         *)
(* form_classno (-4 d) = 2, the two reduced forms of discriminant -4 d are   *)
(* f = x^2 + d y^2 and f2 = 2 x^2 + 2 x y + ((d + 1) / 2) y^2 (d = 1 mod 4)  *)
(* or f2 = 2 x^2 + (d / 2) y^2 (d = 2 mod 4), and for every l >= 1           *)
(*   r_f(l) + r_f2(l) = 2 sum_(m | l) (-4 d / m)        (CN_REP_TOTAL_EVEN)  *)
(* (qform_rep counts the integer pairs; kchar4 d m = (-4 d / m) is the       *)
(* Kronecker symbol). This is the total representation formula used for the  *)
(* lattice sums of the discriminant -4 d in the class number two problem     *)
(* (Baker, Transcendental Number Theory, Ch. 5, sec. 5).                     *)
(*                                                                           *)
(* Method: an elementary two-lattice local analysis in Z[sqrt(-d)] on        *)
(* integer pairs, with the counting tools of Baker/classno_rep.ml. With      *)
(* t = 1 (d = 1 mod 4) or t = 0 (d = 2 mod 4) the ideal above 2 is the       *)
(* lattice Q2 of the pairs (x,y) with 2 | x - t y, and (u,v) -> (2 u + t v,  *)
(* v) maps the representations of l by f2 onto the z in Q2 of norm           *)
(* N z = x^2 + d y^2 = 2 l (CNR2_REP_TWO). Multiplication by a pair (a,b) of *)
(* norm k identifies the z of norm k n with k | z conj(a,b) with the w of    *)
(* norm n (CNR2_CARD_MUL: a linear substitution of determinant k,            *)
(* QFORM_REP_LINEAR_CARD); the multiples of p have the norms p^2 n           *)
(* (CNR2_CARD_SCALE, from QFORM_CARD_SCALE). Then R1 = r_f and R2 = r_f2     *)
(* satisfy R1(2 m) = R2(m) and R2(2 m) = R1(m) (the ramified prime 2) and,   *)
(* at an odd prime r: R1(d m) = R1(m) for d prime (sqrt(-d) of norm d);      *)
(* R2(p m) = R1(m) for d = 2 p (the cross map by sqrt(-d), of norm 2 p and   *)
(* in Q2); R1(r m) = [r | m] R1(m / r) for an inert r; and for a split r,    *)
(* represented by f or by f2 (a reduced form representing r,                 *)
(* QFORM_REPRESENTED_REDUCED, and form_classno = 2: CNR2_SPLIT_REPRESENTED), *)
(* R1(r m) = 2 R1(m) - [r | m] R1(m / r) (pi in O of norm r) or              *)
(* R2(r m) = 2 R1(m) - [r | m] R2(m / r) (pi in Q2 of norm 2 r).             *)
(* CNR2_TOTAL_TRANSFER turns each of these recursions into                   *)
(* T(r m) = (1 + chi r) T(m) - [r | m] chi(r) T(m / r) for T = R1 + R2 (by   *)
(* R2(m) = R1(2 m)), so that no genus character is needed; the divisor       *)
(* sums of the completely multiplicative kchar4 d satisfy the same           *)
(* recursion (CLASSNO_REP_DIVISOR_SUM_REC), and T(1) = 2.                    *)
(*                                                                           *)
(* Main results: CN_REP_TOTAL_EVEN; CNR2_REP_TOTAL_GEN (with the parameter   *)
(* t), CNR2_TOTAL_REC, CNR2_SPLIT_REPRESENTED, CNR2_CARD_MUL,                *)
(* CNR2_CARD_SCALE, CNR2_TOTAL_TRANSFER; helper names CNR2_*.                *)
(*                                                                           *)
(* Uses: Baker/cn_defs.ml (kchar4); Baker/cn_forms.ml                        *)
(* (CNF_CLASSNO_TWO_OTHER); Baker/cn_gauss_even.ml (CN_KCHAR4_1,             *)
(* CN_KCHAR4_2, CN_KCHAR4_PRIME_DIVIDES, CN_KCHAR4_ODD_PRIME,                *)
(* CN_KCHAR4_MUL);                                                           *)
(* Baker/classno_defs.ml (form_classno, qf_reduced, qform, qform_rep);       *)
(* Baker/classno_forms.ml (QFORM_REPRESENTED_REDUCED, QF_PRIMITIVE_COPRIME,  *)
(* QF_PRIMITIVE_BEZOUT); Baker/classno_rep.ml                                *)
(* (QFORM_REP_FINITE, QFORM_REP_LINEAR_CARD, QFORM_CARD_SCALE,               *)
(* QFORM_REP_INERT2, CLASSNO_REP_CARD_UNION_INTER,                           *)
(* CLASSNO_REP_DIVISOR_SUM_REC, CLASSNO_REP_PRIME_INDUCT,                    *)
(* CLASSNO_REP_INT_PARITY, CLASSNO_REP_ABS_LE_POW2,                          *)
(* CLASSNO_REP_DIVIDES_MUL).                                                 *)
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
needs "Baker/cn_gauss_even.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Integer points on x^2 + d y^2 = n: finiteness; multiplication by a     *)
(*    pair (a,b) of norm k (CNR2_CARD_MUL) and by a scalar p                 *)
(*    (CNR2_CARD_SCALE), both with an extra predicate P.                     *)
(* ------------------------------------------------------------------------- *)

let CNR2_QFORM_NORM = prove
 (`!d x y. qform (&1) (&0) (&d) x y = x pow 2 + &d * y pow 2`,
  REWRITE_TAC[qform; INT_MUL_LID; INT_MUL_LZERO; INT_ADD_LID]);;

let CNR2_REP_ONE = prove
 (`!d n. qform_rep (&1) (&0) (&d) n =
         CARD {(x,y) | x pow 2 + &d * y pow 2 = &n:int}`,
  REWRITE_TAC[qform_rep; CNR2_QFORM_NORM]);;

let CNR2_FINITE = prove
 (`!d n. ~(d = 0) ==> FINITE {(x,y) | x pow 2 + &d * y pow 2 = &n:int}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CNR2_QFORM_NORM] THEN
  MATCH_MP_TAC QFORM_REP_FINITE THEN
  REWRITE_TAC[INT_LT_01; INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

let CNR2_CARD_IMAGE_INJ_FINITE = prove
 (`!f:A->B s. (!x y. f x = f y ==> x = y) /\ FINITE(IMAGE f s)
              ==> CARD(IMAGE f s) = CARD s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_MESON_TAC[FINITE_IMAGE_INJ_EQ]);;

(* z = (a,b) w for w of norm n iff k divides both coordinates of             *)
(* z conj(a,b) = (a x + d b y, a y - b x).                                   *)

(* z = (a,b) w for w of norm n iff k divides both coordinates of             *)
(* z conj(a,b) = (a x + d b y, a y - b x): the substitution w -> (a,b) w has *)
(* determinant k.                                                            *)

let CNR2_CARD_MUL = prove
 (`!d a b k n P.
        ~(d = 0) /\ a pow 2 + &d * b pow 2 = &k:int /\ ~(k = 0)
        ==> CARD {(x,y) | x pow 2 + &d * y pow 2 = &(k * n):int /\
                          &k divides a * x + &d * b * y /\
                          &k divides a * y - b * x /\ P x y} =
            CARD {(u,v) | u pow 2 + &d * v pow 2 = &n:int /\
                          P (a * u - &d * b * v) (a * v + b * u)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x:int y:int. x pow 2 + &d * y pow 2`;
    `\x:int y:int. x pow 2 + &d * y pow 2`; `P:int->int->bool`;
    `\u:int v:int. (P:int->int->bool) (a * u - &d * b * v) (a * v + b * u)`;
    `a:int`; `--(&d * b):int`; `b:int`; `a:int`; `&k:int`; `n:num`]
   QFORM_REP_LINEAR_CARD)) THEN
  SUBGOAL_THEN `a * a - --(&d * b) * b = &k:int` SUBST1_TAC THENL
   [UNDISCH_TAC `a pow 2 + &d * b pow 2 = &k:int` THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_MUL;
              INT_ARITH `a * x - --(c * b) * y:int = a * x + c * b * y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `a pow 2 + &d * b pow 2 = &k:int` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT GEN_TAC THEN CONV_TAC INT_RING;
    REPEAT GEN_TAC THEN BINOP_TAC THEN INT_ARITH_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(u,v) | u pow 2 + &d * v pow 2 = &n:int}` THEN
    ASM_SIMP_TAC[CNR2_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[]]);;

let CNR2_CARD_MUL_PLAIN = prove
 (`!d a b k n.
        ~(d = 0) /\ a pow 2 + &d * b pow 2 = &k:int /\ ~(k = 0)
        ==> CARD {(x,y) | x pow 2 + &d * y pow 2 = &(k * n):int /\
                          &k divides a * x + &d * b * y /\
                          &k divides a * y - b * x} =
            CARD {(u,v) | u pow 2 + &d * v pow 2 = &n:int}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `a:int`; `b:int`; `k:num`; `n:num`;
                 `\x:int y:int. T`] CNR2_CARD_MUL) THEN
  ASM_REWRITE_TAC[]);;

let CNR2_CARD_SCALE = prove
 (`!d p n P.
        ~(d = 0) /\ ~(p = 0) /\ (!x y. P (&p * x) (&p * y) <=> P x y)
        ==> CARD {(x,y) | x pow 2 + &d * y pow 2 = &(p * n):int /\ P x y /\
                          &p divides x /\ &p divides y} =
            if p divides n
            then CARD {(x,y) | x pow 2 + &d * y pow 2 = &(n DIV p):int /\ P x y}
            else 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1:int`; `&0:int`; `&d:int`; `p:num`; `n:num`;
                 `P:int->int->bool`] QFORM_CARD_SCALE) THEN
  ASM_REWRITE_TAC[qform; INT_MUL_LID; INT_MUL_LZERO; INT_ADD_LID;
                  INT_LT_01] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[CONJ_ACI]]);;

let CNR2_CARD_SCALE_PLAIN = prove
 (`!d p n. ~(d = 0) /\ ~(p = 0)
           ==> CARD {(x,y) | x pow 2 + &d * y pow 2 = &(p * n):int /\
                             &p divides x /\ &p divides y} =
               if p divides n
               then CARD {(x,y) | x pow 2 + &d * y pow 2 = &(n DIV p):int}
               else 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `p:num`; `n:num`; `\x:int y:int. T`]
    CNR2_CARD_SCALE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. The lattice Q2 of the ideal above 2: the pairs with 2 | x - t y,       *)
(*    t = 1 (d = 1 mod 4) or t = 0 (d = 2 mod 4), i.e. t <= 1 and            *)
(*    (d + t) MOD 4 = 2; parity facts and r_f2 as a count of Q2.             *)
(* ------------------------------------------------------------------------- *)

let CNR2_DT = prove
 (`!d t. t <= 1 /\ (d + t) MOD 4 = 2
         ==> &t * &t = &t:int /\ &2 divides &d - &t:int /\
             ?k. &d + &t = &4 * &k + &2:int`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d + t`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(d + t) DIV 4`,`k:num`) THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `int_of_num` o CONJUNCT1) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `t = 0 \/ t = 1` (DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; CONV_TAC INT_REDUCE_CONV; CONV_TAC INT_REDUCE_CONV];
    REWRITE_TAC[int_divides] THEN EXISTS_TAC `&2 * &k + &1 - &t:int` THEN
    ASM_INT_ARITH_TAC;
    EXISTS_TAC `k:num` THEN ASM_INT_ARITH_TAC]);;

let CNR2_TWO_DIVIDES_SQ = prove
 (`!x:int. &2 divides x pow 2 - x`,
  GEN_TAC THEN MP_TAC(SPEC `x:int` CLASSNO_REP_INT_PARITY) THEN
  MESON_TAC[INTEGER_RULE `!m x:int. (x == &0) (mod m)
                                    ==> m divides x pow 2 - x`;
            INTEGER_RULE `!m x:int. (x == &1) (mod m)
                                    ==> m divides x pow 2 - x`]);;

let CNR2_EVEN_NORM = prove
 (`!d t x y. t <= 1 /\ (d + t) MOD 4 = 2 /\
             &2 divides x pow 2 + &d * y pow 2
             ==> &2 divides x - &t * y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `t:num`] CNR2_DT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m x y f s:int. m divides &2 /\ m divides x pow 2 + f * y pow 2 /\
                    m divides f - s /\ m divides y pow 2 - y /\
                    m divides x pow 2 - x
                    ==> m divides x - s * y`) THEN
  EXISTS_TAC `&d:int` THEN
  ASM_REWRITE_TAC[INT_DIVIDES_REFL; CNR2_TWO_DIVIDES_SQ]);;

let CNR2_QTWO_FOUR = prove
 (`!d t x y. t <= 1 /\ (d + t) MOD 4 = 2 /\ &2 divides x - &t * y /\
             &4 divides x pow 2 + &d * y pow 2
             ==> &2 divides x /\ &2 divides y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `t:num`] CNR2_DT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `k:num`))) THEN
  SUBGOAL_THEN `&2 divides (y:int)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 divides (y:int) * y` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`&2 divides x - &t * y`; `&4 divides x pow 2 + &d * y pow 2`] THEN
      REWRITE_TAC[int_divides] THEN
      DISCH_THEN(X_CHOOSE_TAC `q:int`) THEN
      DISCH_THEN(X_CHOOSE_TAC `w:int`) THEN
      EXISTS_TAC `(q:int) - &k * y pow 2 - &t * w * y - w pow 2` THEN
      MAP_EVERY UNDISCH_TAC
       [`x - &t * y = &2 * w:int`; `x pow 2 + &d * y pow 2 = &4 * q:int`;
        `&t * &t = &t:int`; `&d + &t = &4 * &k + &2:int`] THEN
      CONV_TAC INT_RING;
      SIMP_TAC[PRIME_INT_DIVPROD_EQ; PRIME_2]];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!m x y s:int. m divides y /\ m divides x - s * y ==> m divides x`) THEN
    MAP_EVERY EXISTS_TAC [`y:int`; `&t:int`] THEN ASM_REWRITE_TAC[]]);;

let CNR2_QTWO_MUL = prove
 (`!d t a b u v. t <= 1 /\ (d + t) MOD 4 = 2 /\ &2 divides a - &t * b
                 ==> &2 divides (a * u - &d * b * v) - &t * (a * v + b * u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `t:num`] CNR2_DT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`&2 divides a - &t * b`; `&2 divides &d - &t:int`] THEN
  REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `w1:int`) THEN
  DISCH_THEN(X_CHOOSE_TAC `w2:int`) THEN
  EXISTS_TAC `u * w2 - b * v * w1 - &t * v * w2 - &t * b * v:int` THEN
  MAP_EVERY UNDISCH_TAC
   [`a - &t * b = &2 * w2:int`; `&d - &t = &2 * w1:int`;
    `&t * &t = &t:int`] THEN
  CONV_TAC INT_RING);;

let CNR2_QTWO_CONJ = prove
 (`!d t a b x y. t <= 1 /\ (d + t) MOD 4 = 2 /\ &2 divides x - &t * y /\
                 &2 divides a - &t * b
                 ==> &2 divides a * x + &d * b * y /\
                     &2 divides a * y - b * x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `t:num`] CNR2_DT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`&2 divides a - &t * b`; `&2 divides x - &t * y`;
    `&2 divides &d - &t:int`] THEN
  REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `w1:int`) THEN
  DISCH_THEN(X_CHOOSE_TAC `w2:int`) THEN
  DISCH_THEN(X_CHOOSE_TAC `w3:int`) THEN CONJ_TAC THENL
   [EXISTS_TAC `a * w2 + &t * y * w3 + (&t + w1) * b * y:int`;
    EXISTS_TAC `y * w3 - b * w2:int`] THEN
  MAP_EVERY UNDISCH_TAC
   [`a - &t * b = &2 * w3:int`; `x - &t * y = &2 * w2:int`;
    `&d - &t = &2 * w1:int`; `&t * &t = &t:int`] THEN
  CONV_TAC INT_RING);;

let CNR2_QTWO_ODD_SCALE = prove
 (`!t r x y. ODD r
             ==> (&2 divides &r * x - &t * (&r * y) <=>
                  &2 divides x - &t * y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL; int_divides] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `w:int`) THENL
   [EXISTS_TAC `w - &m * (x - &t * y):int`;
    EXISTS_TAC `(&2 * &m + &1) * w:int`] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC INT_RING);;

let CNR2_QTWO_NEG = prove
 (`!t a b. &2 divides a - &t * b ==> &2 divides a - &t * --b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:int`) THEN
  EXISTS_TAC `w + &t * b:int` THEN POP_ASSUM MP_TAC THEN CONV_TAC INT_RING);;

let CNR2_REP_TWO = prove
 (`!d t n. t <= 1 /\ (d + t) MOD 4 = 2
           ==> qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) n =
               CARD {(x,y) | x pow 2 + &d * y pow 2 = &(2 * n):int /\
                             &2 divides x - &t * y}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `t:num`] CNR2_DT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `k:num`))) THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `&d + &t = &4 * &k + &2:int` THEN UNDISCH_TAC `t <= 1` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&((d + t) DIV 2) = &2 * &k + &1:int` SUBST1_TAC THENL
   [SUBGOAL_THEN `d + t = 2 * (2 * k + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `&d + &t = &4 * &k + &2:int` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
      ARITH_TAC;
      SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL]];
    ALL_TAC] THEN
  REWRITE_TAC[qform_rep] THEN
  SUBGOAL_THEN
   `{(x,y) | x pow 2 + &d * y pow 2 = &(2 * n):int /\
             &2 divides x - &t * y} =
    IMAGE (\z. &2 * FST z + &t * SND z, SND z)
          {(u,v) | qform (&2) (&2 * &t) (&2 * &k + &1) u v = &n}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_IMAGE;
                EXISTS_PAIR_THM; PAIR_EQ; FST; SND; qform] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN EQ_TAC THENL
     [REWRITE_TAC[int_divides] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `u:int`)) THEN
      MAP_EVERY EXISTS_TAC [`u:int`; `y:int`] THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `x - &t * y = &2 * u:int` THEN INT_ARITH_TAC;
        SUBGOAL_THEN
         `(&2:int) * (&2 * u pow 2 + (&2 * &t) * u * y +
                      (&2 * &k + &1) * y pow 2) = &2 * &n`
        MP_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`x pow 2 + &d * y pow 2 = &(2 * n):int`;
            `x - &t * y = &2 * u:int`; `&t * &t = &t:int`;
            `&d + &t = &4 * &k + &2:int`] THEN
          REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INT_RING;
          REWRITE_TAC[INT_EQ_MUL_LCANCEL; INT_OF_NUM_EQ; ARITH_EQ]]];
      DISCH_THEN(X_CHOOSE_THEN `u:int` (X_CHOOSE_THEN `v:int`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[int_divides] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`&2 * u pow 2 + (&2 * &t) * u * v + (&2 * &k + &1) * v pow 2 =
           &n:int`;
          `&t * &t = &t:int`; `&d + &t = &4 * &k + &2:int`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INT_RING;
        EXISTS_TAC `u:int` THEN INT_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th] THEN
                          ASSUME_TAC th) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CNR2_CARD_IMAGE_INJ_FINITE THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`u:int`; `v:int`; `u':int`; `v':int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(x,y) | x pow 2 + &d * y pow 2 = &(2 * n):int}` THEN
    ASM_SIMP_TAC[CNR2_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The ramified prime 2: r_f(2 m) = r_f2(m), r_f2(2 m) = r_f(m); the      *)
(*    transfer of a recursion of r_f (or r_f2) at an odd prime to the        *)
(*    total T = r_f + r_f2.                                                  *)
(* ------------------------------------------------------------------------- *)

let CNR2_REC_TWO_A = prove
 (`!d t m. t <= 1 /\ (d + t) MOD 4 = 2
           ==> qform_rep (&1) (&0) (&d) (2 * m) =
               qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) m`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CNR2_REP_ONE; CNR2_REP_TWO] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC CNR2_EVEN_NORM THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL]);;

let CNR2_REC_TWO_B = prove
 (`!d t m. t <= 1 /\ (d + t) MOD 4 = 2
           ==> qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (2 * m) =
               qform_rep (&1) (&0) (&d) m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(0 + t) MOD 4 = 2` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `t <= 1 ==> t < 4`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR2_REP_ONE; CNR2_REP_TWO] THEN
  MP_TAC(SPECL [`d:num`; `2`; `2 * m`] CNR2_CARD_SCALE_PLAIN) THEN
  ASM_SIMP_TAC[ARITH_EQ; DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  ASM_CASES_TAC `x pow 2 + &d * y pow 2 = &(2 * 2 * m):int` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC CNR2_QTWO_FOUR THEN
    MAP_EVERY EXISTS_TAC [`d:num`; `t:num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 * m = 4 * m`; CLASSNO_REP_DIVIDES_MUL];
    MATCH_ACCEPT_TAC(INTEGER_RULE
     `!m x y s:int. m divides x /\ m divides y ==> m divides x - s * y`)]);;

let CNR2_DIV_DOUBLE = prove
 (`!r m. ~(r = 0) /\ r divides m ==> (2 * m) DIV r = 2 * (m DIV r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q:num` SUBST1_TAC o REWRITE_RULE[divides])) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 * r * q = r * 2 * q`] THEN
  ASM_SIMP_TAC[DIV_MULT]);;

let CNR2_TOTAL_TRANSFER = prove
 (`!R1 R2:num->real r a1 a2 c1 c2.
        prime r /\ ~(r = 2) /\
        (!m. R1(2 * m) = R2 m) /\ (!m. R2(2 * m) = R1 m) /\
        (!m. R1(r * m) =
             a1 * R1 m + a2 * R2 m -
             (if r divides m then c1 * R1(m DIV r) + c2 * R2(m DIV r)
              else &0))
        ==> !m. R1(r * m) + R2(r * m) =
                (a1 + a2) * (R1 m + R2 m) -
                (if r divides m
                 then (c1 + c2) * (R1(m DIV r) + R2(m DIV r)) else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `(r divides 2 * m <=> r divides m)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    SUBGOAL_THEN `~(r divides 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R2:num->real)(r * m) = R1(r * (2 * m))` SUBST1_TAC THENL
   [SUBGOAL_THEN `r * 2 * m = 2 * r * m` SUBST1_TAC THENL
     [CONV_TAC NUM_RING; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CNR2_DIV_DOUBLE] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* 4. Local behaviour of an odd prime r: inert (r divides both               *)
(*    coordinates), split (r divides z conj pi or z pi, both iff r divides   *)
(*    z), and the combination with the parity facts.                         *)
(* ------------------------------------------------------------------------- *)

let CNR2_PRIME_DIVPROD_CANCEL = prove
 (`!r c x:int. prime r /\ ~(&r divides c) /\ &r divides c * x
               ==> &r divides x`,
  MESON_TAC[PRIME_INT_DIVPROD_EQ]);;

let CNR2_SPLIT_CASES = prove
 (`!d r a b x y.
        prime r /\ &r divides a pow 2 + &d * b pow 2 /\
        &r divides x pow 2 + &d * y pow 2
        ==> (&r divides a * x + &d * b * y /\ &r divides a * y - b * x) \/
            (&r divides a * x + &d * --b * y /\
             &r divides a * y - --b * x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&r:int`; `&d:int`; `a:int`; `b:int`; `x:int`; `y:int`]
   (INTEGER_RULE
     `!q f a b x y:int.
        q divides a pow 2 + f * b pow 2 /\ q divides x pow 2 + f * y pow 2
        ==> q divides (a * y - b * x) * (a * y - --b * x)`)) THEN
  ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&r:int`; `&d:int`; `a:int`; `b:int`; `x:int`; `y:int`]
     (INTEGER_RULE
       `!q f a b x y:int.
          q divides a pow 2 + f * b pow 2 /\
          q divides x pow 2 + f * y pow 2 /\ q divides a * y - b * x
          ==> q divides (a * x + f * b * y) * (a * x + f * b * y)`));
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&r:int`; `&d:int`; `a:int`; `b:int`; `x:int`; `y:int`]
     (INTEGER_RULE
       `!q f a b x y:int.
          q divides a pow 2 + f * b pow 2 /\
          q divides x pow 2 + f * y pow 2 /\ q divides a * y - --b * x
          ==> q divides (a * x + f * --b * y) * (a * x + f * --b * y)`))] THEN
  ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]);;

let CNR2_SPLIT_BOTH = prove
 (`!d r a b x y.
        prime r /\ ~(&r divides &2 * a)
        ==> ((&r divides a * x + &d * b * y /\ &r divides a * y - b * x) /\
             (&r divides a * x + &d * --b * y /\
              &r divides a * y - --b * x) <=>
             &r divides x /\ &r divides y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`&r:int`; `&d:int`; `a:int`; `b:int`; `x:int`; `y:int`]
     (INTEGER_RULE
       `!q f a b x y:int.
          q divides a * x + f * b * y /\ q divides a * x + f * --b * y /\
          q divides a * y - b * x /\ q divides a * y - --b * x
          ==> q divides (&2 * a) * x /\ q divides (&2 * a) * y`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CNR2_PRIME_DIVPROD_CANCEL];
    MP_TAC(ISPECL [`&r:int`; `&d:int`; `a:int`; `b:int`; `x:int`; `y:int`]
     (INTEGER_RULE
       `!q f a b x y:int.
          q divides x /\ q divides y
          ==> (q divides a * x + f * b * y /\ q divides a * y - b * x) /\
              (q divides a * x + f * --b * y /\
               q divides a * y - --b * x)`)) THEN
    REWRITE_TAC[]]);;

let CNR2_SPLIT_NONDIV = prove
 (`!d r s a b. prime r /\ ~(r = 2) /\ ~(r divides d) /\ ~(r divides s) /\
               a pow 2 + &d * b pow 2 = &r * &s
               ==> ~(&r divides &2 * a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&r divides (a:int)` ASSUME_TAC THENL
   [UNDISCH_TAC `&r divides &2 * (a:int)` THEN
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN
    REWRITE_TAC[GSYM num_divides] THEN
    ASM_MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&r divides (b:int)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&r divides &d * (b:int) * b` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!q a b f s:int. q divides a pow 2 + f * b pow 2 /\ q divides a
                        ==> q divides f * b * b`) THEN
      EXISTS_TAC `a:int` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[INT_DIVIDES_RMUL; INT_DIVIDES_REFL];
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ; GSYM num_divides] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&r divides (&s:int)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[GSYM num_divides]] THEN
  UNDISCH_TAC `&r divides (a:int)` THEN UNDISCH_TAC `&r divides (b:int)` THEN
  REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `b':int`) THEN DISCH_THEN(X_CHOOSE_TAC `a':int`) THEN
  EXISTS_TAC `(a':int) pow 2 + &d * b' pow 2` THEN
  SUBGOAL_THEN `(&r:int) * &s = &r * &r * (a' pow 2 + &d * b' pow 2)`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`a pow 2 + &d * b pow 2 = &r * &s:int`; `a = &r * a':int`;
      `b = &r * b':int`] THEN
    CONV_TAC INT_RING;
    ASM_SIMP_TAC[INT_EQ_MUL_LCANCEL; INT_OF_NUM_EQ; PRIME_IMP_NZ]]);;

let CNR2_DIVIDES_2R = prove
 (`!r z:int. ODD r /\ &2 divides z /\ &r divides z ==> &(2 * r) divides z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ODD r` THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  MAP_EVERY UNDISCH_TAC
   [`&2 divides (z:int)`; `&(2 * k + 1) divides (z:int)`] THEN
  REWRITE_TAC[int_divides; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  DISCH_THEN(X_CHOOSE_TAC `w2:int`) THEN DISCH_THEN(X_CHOOSE_TAC `w1:int`) THEN
  EXISTS_TAC `w1 - &k * w2:int` THEN
  MAP_EVERY UNDISCH_TAC [`z = &2 * w1:int`; `z = (&2 * &k + &1) * w2:int`] THEN
  CONV_TAC INT_RING);;

let CNR2_DIVIDES_2R_EQ = prove
 (`!r z:int. ODD r /\ &2 divides z ==> (&(2 * r) divides z <=> &r divides z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    MATCH_ACCEPT_TAC(INTEGER_RULE
     `!m n z:int. (m * n) divides z ==> n divides z`);
    ASM_MESON_TAC[CNR2_DIVIDES_2R]]);;

(* ------------------------------------------------------------------------- *)
(* 5. The recursions at an odd prime: inert, split by f (pi in O of norm     *)
(*    r), ramified d (d prime, pi = (0,1)), ramified p (d = 2 p, the cross   *)
(*    map by (0,1) of norm 2 p in Q2), split by f2 (pi in Q2 of norm 2 r).   *)
(* ------------------------------------------------------------------------- *)

let CNR2_REC_INERT = prove
 (`!d r m. ~(d = 0) /\ prime r /\ ~(?s:int. &r divides s pow 2 + &d)
           ==> qform_rep (&1) (&0) (&d) (r * m) =
               if r divides m then qform_rep (&1) (&0) (&d) (m DIV r) else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CNR2_REP_ONE] THEN
  MP_TAC(SPECL [`d:num`; `r:num`; `m:num`] CNR2_CARD_SCALE_PLAIN) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC QFORM_REP_INERT2 THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL]);;

let CNR2_REC_SPLIT_ONE = prove
 (`!d r a b m.
        ~(d = 0) /\ prime r /\ ~(r = 2) /\ ~(r divides d) /\
        a pow 2 + &d * b pow 2 = &r:int
        ==> qform_rep (&1) (&0) (&d) (r * m) +
            (if r divides m then qform_rep (&1) (&0) (&d) (m DIV r) else 0) =
            2 * qform_rep (&1) (&0) (&d) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CNR2_REP_ONE] THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&r divides &2 * (a:int))` ASSUME_TAC THENL
   [MATCH_MP_TAC CNR2_SPLIT_NONDIV THEN
    MAP_EVERY EXISTS_TAC [`d:num`; `1`; `b:int`] THEN
    ASM_REWRITE_TAC[INT_MUL_RID; DIVIDES_ONE] THEN
    ASM_MESON_TAC[PRIME_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `a pow 2 + &d * (--b) pow 2 = &r:int` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_POW_NEG; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
              &r divides a * x + &d * b * y /\ &r divides a * y - b * x}`;
    `{(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
              &r divides a * x + &d * --b * y /\
              &r divides a * y - --b * x}`]
   CLASSNO_REP_CARD_UNION_INTER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int}` THEN
    ASM_SIMP_TAC[CNR2_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR2_CARD_MUL_PLAIN] THEN
  SUBGOAL_THEN
   `{(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
             &r divides a * x + &d * b * y /\ &r divides a * y - b * x} UNION
    {(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
             &r divides a * x + &d * --b * y /\
             &r divides a * y - --b * x} =
    {(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    ASM_CASES_TAC `x pow 2 + &d * y pow 2 = &(r * m):int` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CNR2_SPLIT_CASES THEN
    ASM_REWRITE_TAC[CLASSNO_REP_DIVIDES_MUL; INT_DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
             &r divides a * x + &d * b * y /\ &r divides a * y - b * x} INTER
    {(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
             &r divides a * x + &d * --b * y /\
             &r divides a * y - --b * x} =
    {(x,y) | x pow 2 + &d * y pow 2 = &(r * m):int /\
             &r divides x /\ &r divides y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    MP_TAC(SPECL [`d:num`; `r:num`; `a:int`; `b:int`; `x:int`; `y:int`]
      CNR2_SPLIT_BOTH) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR2_CARD_SCALE_PLAIN] THEN ARITH_TAC);;

let CNR2_REC_RAMIFIED_D = prove
 (`!d m. prime d
         ==> qform_rep (&1) (&0) (&d) (d * m) = qform_rep (&1) (&0) (&d) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CNR2_REP_ONE] THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `&0:int`; `&1:int`; `d:num`; `m:num`]
    CNR2_CARD_MUL_PLAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> (a <=> a /\ b)`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&d divides (x:int)` MP_TAC THENL
   [SUBGOAL_THEN `&d divides (x:int) * x` MP_TAC THENL
     [REWRITE_TAC[int_divides] THEN EXISTS_TAC `(&m:int) - y pow 2` THEN
      UNDISCH_TAC `x pow 2 + &d * y pow 2 = &(d * m):int` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INT_RING;
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]];
    REWRITE_TAC[int_divides] THEN DISCH_THEN(X_CHOOSE_TAC `w:int`) THEN
    CONJ_TAC THENL [EXISTS_TAC `y:int`; EXISTS_TAC `--w:int`] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let CNR2_REC_RAMIFIED_P = prove
 (`!d t p m. d = 2 * p /\ t = 0 /\ prime p /\ ODD p
             ==> qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (p * m) =
                 qform_rep (&1) (&0) (&d) m`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  SUBGOAL_THEN `0 <= 1 /\ (2 * p + 0) MOD 4 = 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 <= 1`] THEN
    UNDISCH_TAC `ODD p` THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    REWRITE_TAC[ARITH_RULE `2 * (2 * k + 1) = k * 4 + 2`; MOD_MULT_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 * p = 0) /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ; MULT_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[CNR2_REP_ONE; CNR2_REP_TWO] THEN
  SUBGOAL_THEN
   `{(x,y) | x pow 2 + &(2 * p) * y pow 2 = &(2 * p * m):int /\
             &2 divides x - &0 * y} =
    {(x,y) | x pow 2 + &(2 * p) * y pow 2 = &((2 * p) * m):int /\
             &(2 * p) divides &0 * x + &(2 * p) * &1 * y /\
             &(2 * p) divides &0 * y - &1 * x /\ &2 divides x - &0 * y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; MULT_ASSOC] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    ASM_CASES_TAC `x pow 2 + &(2 * p) * y pow 2 = &((2 * p) * m):int` THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_SUB_RZERO;
                    INT_ADD_LID; INT_SUB_LZERO; INT_DIVIDES_RNEG] THEN
    ASM_CASES_TAC `&2 divides (x:int)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MESON_TAC[INT_DIVIDES_RMUL; INT_DIVIDES_REFL; INT_MUL_RID];
      ALL_TAC] THEN
    MATCH_MP_TAC CNR2_DIVIDES_2R THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&p divides (x:int) * x` MP_TAC THENL
     [REWRITE_TAC[int_divides] THEN
      EXISTS_TAC `&2 * &m - &2 * (y:int) pow 2` THEN
      UNDISCH_TAC
       `x pow 2 + &(2 * p) * y pow 2 = &((2 * p) * m):int` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INT_RING;
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`2 * p`; `&0:int`; `&1:int`; `2 * p`; `m:num`;
                 `\x:int y:int. &2 divides x - &0 * y`] CNR2_CARD_MUL)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:int`; `v:int`] THEN
  MATCH_MP_TAC(TAUT `b ==> (a /\ b <=> a)`) THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_MUL_RID; INT_SUB_RZERO;
              INT_SUB_LZERO; INT_DIVIDES_RNEG; INT_ADD_LID] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MESON_TAC[INT_DIVIDES_RMUL; INT_DIVIDES_REFL; INT_MUL_ASSOC]);;

let CNR2_REC_SPLIT_TWO = prove
 (`!d t r a b m.
        t <= 1 /\ (d + t) MOD 4 = 2 /\ prime r /\ ~(r = 2) /\
        ~(r divides d) /\ &2 divides a - &t * b /\
        a pow 2 + &d * b pow 2 = &(2 * r):int
        ==> qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (r * m) +
            (if r divides m
             then qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (m DIV r)
             else 0) =
            2 * qform_rep (&1) (&0) (&d) m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = 0) /\ ~(r = 0) /\ ODD r` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `(0 + t) MOD 4 = 2` THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `t <= 1 ==> t < 4`] THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[PRIME_IMP_NZ];
      ASM_MESON_TAC[PRIME_ODD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&r divides &2 * (a:int))` ASSUME_TAC THENL
   [MATCH_MP_TAC CNR2_SPLIT_NONDIV THEN
    MAP_EVERY EXISTS_TAC [`d:num`; `2`; `b:int`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_2];
      REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 divides a - &t * --b /\
                a pow 2 + &d * (--b) pow 2 = &(2 * r):int`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CNR2_QTWO_NEG] THEN ASM_REWRITE_TAC[INT_POW_NEG; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&r divides &(2 * r):int /\ &r divides &((2 * r) * m):int`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    MESON_TAC[INT_DIVIDES_LMUL; INT_DIVIDES_RMUL; INT_DIVIDES_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNR2_REP_ONE; CNR2_REP_TWO] THEN REWRITE_TAC[MULT_ASSOC] THEN
  MP_TAC(ISPECL
   [`{(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
              &(2 * r) divides a * x + &d * b * y /\
              &(2 * r) divides a * y - b * x /\ &2 divides x - &t * y}`;
    `{(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
              &(2 * r) divides a * x + &d * --b * y /\
              &(2 * r) divides a * y - --b * x /\ &2 divides x - &t * y}`]
   CLASSNO_REP_CARD_UNION_INTER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int}` THEN
    ASM_SIMP_TAC[CNR2_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
             &(2 * r) divides a * x + &d * b * y /\
             &(2 * r) divides a * y - b * x /\ &2 divides x - &t * y} UNION
    {(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
             &(2 * r) divides a * x + &d * --b * y /\
             &(2 * r) divides a * y - --b * x /\ &2 divides x - &t * y} =
    {(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
             &2 divides x - &t * y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    ASM_CASES_TAC `x pow 2 + &d * y pow 2 = &((2 * r) * m):int` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&2 divides x - &t * y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`d:num`; `t:num`; `a:int`; `b:int`; `x:int`; `y:int`]
      CNR2_QTWO_CONJ) THEN
    MP_TAC(SPECL [`d:num`; `t:num`; `a:int`; `--b:int`; `x:int`; `y:int`]
      CNR2_QTWO_CONJ) THEN
    MP_TAC(SPECL [`d:num`; `r:num`; `a:int`; `b:int`; `x:int`; `y:int`]
      CNR2_SPLIT_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CNR2_DIVIDES_2R_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
             &(2 * r) divides a * x + &d * b * y /\
             &(2 * r) divides a * y - b * x /\ &2 divides x - &t * y} INTER
    {(x,y) | x pow 2 + &d * y pow 2 = &((2 * r) * m):int /\
             &(2 * r) divides a * x + &d * --b * y /\
             &(2 * r) divides a * y - --b * x /\ &2 divides x - &t * y} =
    {(x,y) | x pow 2 + &d * y pow 2 = &(r * 2 * m):int /\
             &2 divides x - &t * y /\ &r divides x /\ &r divides y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    REWRITE_TAC[ARITH_RULE `r * 2 * m = (2 * r) * m`] THEN
    ASM_CASES_TAC `x pow 2 + &d * y pow 2 = &((2 * r) * m):int` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&2 divides x - &t * y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`d:num`; `t:num`; `a:int`; `b:int`; `x:int`; `y:int`]
      CNR2_QTWO_CONJ) THEN
    MP_TAC(SPECL [`d:num`; `t:num`; `a:int`; `--b:int`; `x:int`; `y:int`]
      CNR2_QTWO_CONJ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CNR2_DIVIDES_2R_EQ] THEN
    MP_TAC(SPECL [`d:num`; `r:num`; `a:int`; `b:int`; `x:int`; `y:int`]
      CNR2_SPLIT_BOTH) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`d:num`; `r:num`; `2 * m`;
    `\x:int y:int. &2 divides x - &t * y`] CNR2_CARD_SCALE)) THEN
  ASM_SIMP_TAC[CNR2_QTWO_ODD_SCALE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`d:num`; `a:int`; `b:int`; `2 * r`; `m:num`;
    `\x:int y:int. &2 divides x - &t * y`] CNR2_CARD_MUL)) THEN
  MP_TAC(BETA_RULE(ISPECL [`d:num`; `a:int`; `--b:int`; `2 * r`; `m:num`;
    `\x:int y:int. &2 divides x - &t * y`] CNR2_CARD_MUL)) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
  ASM_SIMP_TAC[CNR2_QTWO_MUL] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(r divides 2 * m <=> r divides m)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    SUBGOAL_THEN `~(r divides 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_2];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CNR2_DIV_DOUBLE] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 6. Split primes are represented by f or by f2: with s^2 + d = r w, r is  *)
(*    represented by a reduced primitive form of discriminant -4 d (the      *)
(*    reduction of (r, 2 s, w), primitive as r does not divide 4 d,          *)
(*    QFORM_REPRESENTED_REDUCED), one of the two forms (1, 0, d),            *)
(*    (2, 2 t, (d + t) / 2).                                                 *)
(* ------------------------------------------------------------------------- *)
let CNR2_SPLIT_REPRESENTED = prove
 (`!d t r. t <= 1 /\ (d + t) MOD 4 = 2 /\ 5 <= d /\
           form_classno (--(&4 * &d)) = 2 /\
           prime r /\ ~(r = 2) /\ ~(r divides d) /\
           (?s:int. &r divides s pow 2 + &d)
           ==> (?a b:int. a pow 2 + &d * b pow 2 = &r) \/
               (?a b:int. &2 divides a - &t * b /\
                          a pow 2 + &d * b pow 2 = &(2 * r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `t:num`] CNR2_DT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `k:num`))) THEN
  SUBGOAL_THEN `&1 <= &k:int /\ &t <= &1:int /\ &0 <= &t:int`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_POS; INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&d + &t = &4 * &k + &2:int` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&r divides s pow 2 + &d` THEN REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:int`) THEN
  MP_TAC(SPECL [`4 * d`; `r:num`; `&2 * s:int`; `w:int`]
    QFORM_REPRESENTED_REDUCED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
      UNDISCH_TAC `s pow 2 + &d = &r * w:int` THEN CONV_TAC INT_RING;
      MATCH_MP_TAC QF_PRIMITIVE_COPRIME THEN EXISTS_TAC `&4 * &d:int` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `s pow 2 + &d = &r * w:int` THEN CONV_TAC INT_RING;
        REWRITE_TAC[INT_OF_NUM_MUL; GSYM num_coprime] THEN
        ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_DIVPROD_EQ;
                     ARITH_RULE `4 = 2 * 2`; DIVIDES_PRIME_PRIME; PRIME_2]]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a1:int`; `b1:int`; `c1:int`; `x:int`; `y:int`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--(&4 * &d):int`; `&1:int`; `&0:int`; `&d:int`;
                `&2:int`; `&2 * &t:int`; `&2 * &k + &1:int`;
                `a1:int`; `b1:int`; `c1:int`] CNF_CLASSNO_TWO_OTHER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[qf_reduced] THEN UNDISCH_TAC `5 <= d` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
      INT_ARITH_TAC;
      REWRITE_TAC[INT_GCD_1];
      REWRITE_TAC[qf_reduced] THEN
      MAP_EVERY UNDISCH_TAC
       [`&1 <= &k:int`; `&t <= &1:int`; `&0 <= &t:int`] THEN
      INT_ARITH_TAC;
      REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
      MAP_EVERY UNDISCH_TAC
       [`&t * &t = &t:int`; `&d + &t = &4 * &k + &2:int`] THEN
      CONV_TAC INT_RING;
      MATCH_MP_TAC QF_PRIMITIVE_BEZOUT THEN
      MAP_EVERY EXISTS_TAC [`--(&k):int`; `&0:int`; `&1:int`] THEN
      INT_ARITH_TAC;
      INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN
    ASM_REWRITE_TAC[GSYM CNR2_QFORM_NORM];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`&2 * x + &t * y:int`; `y:int`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[int_divides] THEN EXISTS_TAC `x:int` THEN INT_ARITH_TAC;
      UNDISCH_TAC `qform (&2) (&2 * &t) (&2 * &k + &1) x y = &r` THEN
      REWRITE_TAC[qform; GSYM INT_OF_NUM_MUL] THEN
      MAP_EVERY UNDISCH_TAC
       [`&t * &t = &t:int`; `&d + &t = &4 * &k + &2:int`] THEN
      CONV_TAC INT_RING]]);;

(* ------------------------------------------------------------------------- *)
(* 7. The two cases of d (the values of kchar4 d at the primes and its       *)
(*    multiplicativity are in Baker/cn_gauss_even.ml).                       *)
(* ------------------------------------------------------------------------- *)

let CNR2_CASES_FACTS = prove
 (`!d t. (t = 1 /\ prime d /\ d MOD 4 = 1) \/
         (t = 0 /\ ?p. prime p /\ ODD p /\ d = 2 * p)
         ==> t <= 1 /\ (d + t) MOD 4 = 2 /\ 5 <= d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THENL
   [MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `~(d = 1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    SUBGOAL_THEN `~(d DIV 4 = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(d = 1)` THEN
      UNDISCH_TAC `d = d DIV 4 * 4 + 1` THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `d DIV 4` THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    SUBGOAL_THEN `3 <= p` ASSUME_TAC THENL
     [MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ODD p` THEN ASM_CASES_TAC `p = 2` THEN
      ASM_REWRITE_TAC[ARITH] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    UNDISCH_TAC `ODD p` THEN REWRITE_TAC[ODD_EXISTS; ADD1] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num` THEN ARITH_TAC]);;

let CNR2_CASES_RAMIFIED = prove
 (`!d t r. ((t = 1 /\ prime d /\ d MOD 4 = 1) \/
            (t = 0 /\ ?p. prime p /\ ODD p /\ d = 2 * p)) /\
           prime r /\ ~(r = 2) /\ r divides d
           ==> (t = 1 /\ r = d) \/ (t = 0 /\ d = 2 * r /\ ODD r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DIVIDES_PRIME_PRIME];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r = p:num` SUBST1_TAC THENL
     [UNDISCH_TAC `r divides d` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
      ASM_MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_2];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The total recursion and the representation formula.                    *)
(* ------------------------------------------------------------------------- *)

let CNR2_REP_ONE_ONE = prove
 (`!d. 2 <= d ==> qform_rep (&1) (&0) (&d) 1 = 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CNR2_REP_ONE] THEN
  SUBGOAL_THEN `{(x,y) | x pow 2 + &d * y pow 2 = &1:int} =
                {(&1,&0), (-- &1,&0)}`
  SUBST1_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_INSERT;
              NOT_IN_EMPTY; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  SUBGOAL_THEN `&2 <= &d:int` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `y:int = &0` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&1 <= (y:int) pow 2` MP_TAC THENL
       [MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN ASM_INT_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(&0:int) <= (&d - &2) * y pow 2` MP_TAC THENL
       [MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_LE_POW_2] THEN
        ASM_INT_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `x:int` INT_LE_POW_2) THEN
      UNDISCH_TAC `x pow 2 + &d * y pow 2 = &1:int` THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x - &1) * (x + &1) = &0:int` MP_TAC THENL
     [UNDISCH_TAC `x pow 2 + &d * &0 pow 2 = &1:int` THEN
      CONV_TAC INT_RING;
      REWRITE_TAC[INT_ENTIRE] THEN INT_ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let CNR2_REP_TWO_ONE = prove
 (`!d t. t <= 1 /\ (d + t) MOD 4 = 2 /\ 3 <= d
         ==> qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) 1 = 0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CNR2_REP_TWO] THEN
  MATCH_MP_TAC(MESON[CARD_CLAUSES] `s:int#int->bool = {} ==> CARD s = 0`) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&3 <= &d:int` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `y:int = &0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= (y:int) pow 2` MP_TAC THENL
     [MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&0:int) <= (&d - &3) * y pow 2` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_LE_POW_2] THEN
      ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `x:int` INT_LE_POW_2) THEN
    UNDISCH_TAC `x pow 2 + &d * y pow 2 = &2:int` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `x pow 2 + &d * &0 pow 2 = &2:int` THEN
  REWRITE_TAC[INT_POW_ZERO; ARITH_EQ; INT_MUL_RZERO; INT_ADD_RID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs x <= &1 \/ &2 <= abs(x:int)` STRIP_ASSUME_TAC THENL
   [INT_ARITH_TAC;
    SUBGOAL_THEN `(x:int) pow 2 <= &1 pow 2` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_LE_SQUARE_ABS] THEN ASM_INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV];
    SUBGOAL_THEN `(&2:int) pow 2 <= x pow 2` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_LE_SQUARE_ABS] THEN ASM_INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV]]);;

let CNR2_TOTAL_REC = prove
 (`!d t r m.
        ((t = 1 /\ prime d /\ d MOD 4 = 1) \/
         (t = 0 /\ ?p. prime p /\ ODD p /\ d = 2 * p)) /\
        form_classno (--(&4 * &d)) = 2 /\ prime r
        ==> &(qform_rep (&1) (&0) (&d) (r * m)) +
            &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (r * m)) =
            (&1 + kchar4 d r) *
            (&(qform_rep (&1) (&0) (&d) m) +
             &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) m)) -
            (if r divides m
             then kchar4 d r *
                  (&(qform_rep (&1) (&0) (&d) (m DIV r)) +
                   &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (m DIV r)))
             else &0)`,
  let r1 = `\n. &(qform_rep (&1) (&0) (&d) n):real`
  and r2 = `\n. &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) n):real` in
  let TRANSFER_TAC rr1 rr2 a1 a2 c1 c2 rec_tac =
    MP_TAC(BETA_RULE(ISPECL [rr1; rr2; `r:num`; a1; a2; c1; c2]
      CNR2_TOTAL_TRANSFER)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `n:num` THEN rec_tac];
      DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC] in
  let NUM_REC_TAC th =
    MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `real_of_num`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CNR2_CASES_FACTS) THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!m. &(qform_rep (&1) (&0) (&d) (2 * m)) =
         &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) m):real) /\
    (!m. &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) (2 * m)) =
         &(qform_rep (&1) (&0) (&d) m):real)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CNR2_REC_TWO_A; CNR2_REC_TWO_B]; ALL_TAC] THEN
  ASM_CASES_TAC `r = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[CN_KCHAR4_2; REAL_MUL_LZERO; COND_ID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r divides d` THENL
   [ASM_SIMP_TAC[CN_KCHAR4_PRIME_DIVIDES] THEN
    MP_TAC(SPECL [`d:num`; `t:num`; `r:num`] CNR2_CASES_RAMIFIED) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `prime d` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      TRANSFER_TAC r1 r2 `&1` `&0` `&0` `&0`
       (FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `r:num = d`))
        THEN ASM_SIMP_TAC[CNR2_REC_RAMIFIED_D] THEN
        COND_CASES_TAC THEN REAL_ARITH_TAC);
      TRANSFER_TAC r2 r1 `&0` `&1` `&0` `&0`
       (MP_TAC(SPECL [`d:num`; `t:num`; `r:num`; `n:num`]
          CNR2_REC_RAMIFIED_P) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        COND_CASES_TAC THEN REAL_ARITH_TAC)];
    ALL_TAC] THEN
  ASM_CASES_TAC `?s:int. &r divides s pow 2 + &d` THEN
  ASM_SIMP_TAC[CN_KCHAR4_ODD_PRIME] THENL
   [MP_TAC(SPECL [`d:num`; `t:num`; `r:num`] CNR2_SPLIT_REPRESENTED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `a:int`
      (X_CHOOSE_THEN `b:int` STRIP_ASSUME_TAC))) THENL
     [TRANSFER_TAC r1 r2 `&2` `&0` `&1` `&0`
       (NUM_REC_TAC(SPECL [`d:num`; `r:num`; `a:int`; `b:int`; `n:num`]
          CNR2_REC_SPLIT_ONE));
      TRANSFER_TAC r2 r1 `&0` `&2` `&1` `&0`
       (NUM_REC_TAC(SPECL [`d:num`; `t:num`; `r:num`; `a:int`; `b:int`;
                           `n:num`] CNR2_REC_SPLIT_TWO))];
    TRANSFER_TAC r1 r2 `&0` `&0` `-- &1` `&0`
     (MP_TAC(SPECL [`d:num`; `r:num`; `n:num`] CNR2_REC_INERT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC)]);;

let CNR2_REP_TOTAL_GEN = prove
 (`!d t l. ((t = 1 /\ prime d /\ d MOD 4 = 1) \/
            (t = 0 /\ ?p. prime p /\ ODD p /\ d = 2 * p)) /\
           form_classno (--(&4 * &d)) = 2 /\ 1 <= l
           ==> &(qform_rep (&1) (&0) (&d) l) +
               &(qform_rep (&2) (&2 * &t) (&((d + t) DIV 2)) l) =
               &2 * sum {m | m divides l} (\m. kchar4 d m)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC CLASSNO_REP_PRIME_INDUCT THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CNR2_CASES_FACTS) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CNR2_REP_ONE_ONE; CNR2_REP_TWO_ONE;
                 ARITH_RULE `5 <= d ==> 2 <= d /\ 3 <= d`] THEN
    REWRITE_TAC[DIVIDES_ONE; SING_GSPEC; SUM_SING; CN_KCHAR4_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `1 <= n /\ n < p * n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `2 * n <= p * n` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m. kchar4 d m`; `p:num`; `n:num`]
    CLASSNO_REP_DIVISOR_SUM_REC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CN_KCHAR4_MUL]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CNR2_TOTAL_REC] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[DIV_MULT; PRIME_IMP_NZ] THEN
    SUBGOAL_THEN `1 <= k /\ k < p * p * k` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `k = 0` THENL
       [UNDISCH_TAC `1 <= p * k` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p * k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * k <= p * k ==> k <= p * k`) THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[] THEN
      SPEC_TAC(`sum {m | m divides p * k} (\m. kchar4 d m)`,`A:real`) THEN
      SPEC_TAC(`sum {m | m divides k} (\m. kchar4 d m)`,`B:real`) THEN
      SPEC_TAC(`kchar4 d p`,`q:real`) THEN CONV_TAC REAL_RING];
    ASM_SIMP_TAC[] THEN
    SPEC_TAC(`sum {m | m divides n} (\m. kchar4 d m)`,`A:real`) THEN
    SPEC_TAC(`kchar4 d p`,`q:real`) THEN CONV_TAC REAL_RING]);;

let CN_REP_TOTAL_EVEN = prove
 (`!d l. (prime d /\ d MOD 4 = 1 \/ (?p. prime p /\ ODD p /\ d = 2 * p)) /\
         form_classno (--(&4 * &d)) = 2 /\ 1 <= l
         ==> &(qform_rep (&1) (&0) (&d) l) +
             &(qform_rep (&2) (if d MOD 4 = 1 then &2 else &0)
                         (if d MOD 4 = 1 then &((d + 1) DIV 2) else &(d DIV 2))
                         l) =
             &2 * sum {m | m divides l} (\m. kchar4 d m)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`d:num`; `1`; `l:num`] CNR2_REP_TOTAL_GEN) THEN
    ASM_REWRITE_TAC[INT_MUL_RID];
    SUBGOAL_THEN `~(d MOD 4 = 1)` ASSUME_TAC THENL
     [DISCH_TAC THEN MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN
      DISCH_THEN(MP_TAC o AP_TERM `EVEN` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
      ALL_TAC] THEN
    MP_TAC(SPECL [`d:num`; `0`; `l:num`] CNR2_REP_TOTAL_GEN) THEN
    ASM_REWRITE_TAC[INT_MUL_RZERO; ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `p:num` THEN
    ASM_REWRITE_TAC[]]);;
