(* ========================================================================= *)
(* Properties of complex polynomials (not canonically represented).          *)
(* ========================================================================= *)

needs "Complex/complexnumbers.ml";;

prioritize_complex();;

parse_as_infix("++",(16,"right"));;
parse_as_infix("**",(20,"right"));;
parse_as_infix("##",(20,"right"));;
parse_as_infix("divides",(14,"right"));;
parse_as_infix("exp",(22,"right"));;

do_list override_interface
  ["++",`poly_add:complex list->complex list->complex list`;
   "**",`poly_mul:complex list->complex list->complex list`;
   "##",`poly_cmul:complex->complex list->complex list`;
   "neg",`poly_neg:complex list->complex list`;
   "divides",`poly_divides:complex list->complex list->bool`;
   "exp",`poly_exp:complex list -> num -> complex list`;
   "diff",`poly_diff:complex list->complex list`];;

let SIMPLE_COMPLEX_ARITH tm = prove(tm,SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Polynomials.                                                              *)
(* ------------------------------------------------------------------------- *)

let poly = new_recursive_definition list_RECURSION
  `(poly [] x = Cx(&0)) /\
   (poly (CONS h t) x = h + x * poly t x)`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on polynomials.                                     *)
(* ------------------------------------------------------------------------- *)

let poly_add = new_recursive_definition list_RECURSION
  `([] ++ l2 = l2) /\
   ((CONS h t) ++ l2 =
        (if l2 = [] then CONS h t
                    else CONS (h + HD l2) (t ++ TL l2)))`;;

let poly_cmul = new_recursive_definition list_RECURSION
  `(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))`;;

let poly_neg = new_definition
  `neg = (##) (--(Cx(&1)))`;;

let poly_mul = new_recursive_definition list_RECURSION
  `([] ** l2 = []) /\
   ((CONS h t) ** l2 =
        if t = [] then h ## l2
        else (h ## l2) ++ CONS (Cx(&0)) (t ** l2))`;;

let poly_exp = new_recursive_definition num_RECURSION
  `(p exp 0 = [Cx(&1)]) /\
   (p exp (SUC n) = p ** p exp n)`;;

(* ------------------------------------------------------------------------- *)
(* Useful clausifications.                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_CLAUSES = prove
 (`([] ++ p2 = p2) /\
   (p1 ++ [] = p1) /\
   ((CONS h1 t1) ++ (CONS h2 t2) = CONS (h1 + h2) (t1 ++ t2))`,
  REWRITE_TAC[poly_add; NOT_CONS_NIL; HD; TL] THEN
  SPEC_TAC(`p1:complex list`,`p1:complex list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly_add]);;

let POLY_CMUL_CLAUSES = prove
 (`(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))`,
  REWRITE_TAC[poly_cmul]);;

let POLY_NEG_CLAUSES = prove
 (`(neg [] = []) /\
   (neg (CONS h t) = CONS (--h) (neg t))`,
  REWRITE_TAC[poly_neg; POLY_CMUL_CLAUSES;
              COMPLEX_MUL_LNEG; COMPLEX_MUL_LID]);;

let POLY_MUL_CLAUSES = prove
 (`([] ** p2 = []) /\
   ([h1] ** p2 = h1 ## p2) /\
   ((CONS h1 (CONS k1 t1)) ** p2 =
        h1 ## p2 ++ CONS (Cx(&0)) (CONS k1 t1 ** p2))`,
  REWRITE_TAC[poly_mul; NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Various natural consequences of syntactic definitions.                    *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD = prove
 (`!p1 p2 x. poly (p1 ++ p2) x = poly p1 x + poly p2 x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_add; poly; COMPLEX_ADD_LID] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; HD; TL; poly; COMPLEX_ADD_RID] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_CMUL = prove
 (`!p c x. poly (c ## p) x = c * poly p x`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly; poly_cmul] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_NEG = prove
 (`!p x. poly (neg p) x = --(poly p x)`,
  REWRITE_TAC[poly_neg; POLY_CMUL] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_MUL = prove
 (`!x p1 p2. poly (p1 ** p2) x = poly p1 x * poly p2 x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_mul; poly; COMPLEX_MUL_LZERO; POLY_CMUL; POLY_ADD] THEN
  SPEC_TAC(`h:complex`,`h:complex`) THEN
  SPEC_TAC(`t:complex list`,`t:complex list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_mul; POLY_CMUL; POLY_ADD; poly; POLY_CMUL;
    COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[POLY_ADD; POLY_CMUL; poly] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_EXP = prove
 (`!p n x. poly (p exp n) x = (poly p x) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[poly_exp; complex_pow; POLY_MUL] THEN
  REWRITE_TAC[poly] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_RZERO = prove
 (`!p. poly (p ++ []) = poly p`,
  REWRITE_TAC[FUN_EQ_THM; POLY_ADD; poly; COMPLEX_ADD_RID]);;

let POLY_MUL_ASSOC = prove
 (`!p q r. poly (p ** (q ** r)) = poly ((p ** q) ** r)`,
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL; COMPLEX_MUL_ASSOC]);;

let POLY_EXP_ADD = prove
 (`!d n p. poly(p exp (n + d)) = poly(p exp n ** p exp d)`,
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[POLY_MUL; ADD_CLAUSES; poly_exp; poly] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Key property that f(a) = 0 ==> (x - a) divides p(x). Very delicate!       *)
(* ------------------------------------------------------------------------- *)

let POLY_LINEAR_REM = prove
 (`!t h. ?q r. CONS h t = [r] ++ [--a; Cx(&1)] ** q`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[] THENL
   [GEN_TAC THEN EXISTS_TAC `[]:complex list` THEN
    EXISTS_TAC `h:complex` THEN
    REWRITE_TAC[poly_add; poly_mul; poly_cmul; NOT_CONS_NIL] THEN
    REWRITE_TAC[HD; TL; COMPLEX_ADD_RID];
    X_GEN_TAC `k:complex` THEN
    POP_ASSUM(STRIP_ASSUME_TAC o SPEC `h:complex`) THEN
    EXISTS_TAC `CONS (r:complex) q` THEN EXISTS_TAC `r * a + k` THEN
    ASM_REWRITE_TAC[POLY_ADD_CLAUSES; POLY_MUL_CLAUSES; poly_cmul] THEN
    REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`q:complex list`,`q:complex list`) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC[POLY_ADD_CLAUSES; POLY_MUL_CLAUSES; poly_cmul] THEN
    REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_ADD_AC]]);;

let POLY_LINEAR_DIVIDES = prove
 (`!a p. (poly p a = Cx(&0)) <=> (p = []) \/ ?q. p = [--a; Cx(&1)] ** q`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[poly]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [DISJ2_TAC THEN STRIP_ASSUME_TAC(SPEC_ALL POLY_LINEAR_REM) THEN
    EXISTS_TAC `q:complex list` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r = Cx(&0)` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `poly (CONS h t) a = Cx(&0)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLY_ADD; POLY_MUL] THEN
      REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID;
                  COMPLEX_MUL_RID] THEN
      REWRITE_TAC[COMPLEX_ADD_LINV] THEN SIMPLE_COMPLEX_ARITH_TAC;
      REWRITE_TAC[poly_mul] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
      SPEC_TAC(`q:complex list`,`q:complex list`) THEN LIST_INDUCT_TAC THENL
       [REWRITE_TAC[poly_cmul; poly_add; NOT_CONS_NIL;
                    HD; TL; COMPLEX_ADD_LID];
        REWRITE_TAC[poly_cmul; poly_add; NOT_CONS_NIL;
                    HD; TL; COMPLEX_ADD_LID]]];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly] THEN
    REWRITE_TAC[POLY_MUL] THEN REWRITE_TAC[poly] THEN
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_ADD_LINV] THEN SIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Thanks to the finesse of the above, we can use length rather than degree. *)
(* ------------------------------------------------------------------------- *)

let POLY_LENGTH_MUL = prove
 (`!q. LENGTH([--a; Cx(&1)] ** q) = SUC(LENGTH q)`,
  let lemma = prove
   (`!p h k a. LENGTH (k ## p ++ CONS h (a ## p)) = SUC(LENGTH p)`,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[poly_cmul; POLY_ADD_CLAUSES; LENGTH]) in
  REWRITE_TAC[poly_mul; NOT_CONS_NIL; lemma]);;

(* ------------------------------------------------------------------------- *)
(* Thus a nontrivial polynomial of degree n has no more than n roots.        *)
(* ------------------------------------------------------------------------- *)

let POLY_ROOTS_INDEX_LEMMA = prove
 (`!n. !p. ~(poly p = poly []) /\ (LENGTH p = n)
           ==> ?i. !x. (poly p x = Cx(&0)) ==> ?m. m <= n /\ (x = i m)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH_EQ_NIL] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `?a. poly p a = Cx(&0)` THENL
     [UNDISCH_TAC `?a. poly p a = Cx(&0)` THEN
      DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:complex list` SUBST_ALL_TAC) THEN
      FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
      UNDISCH_TAC `~(poly ([-- a; Cx(&1)] ** q) = poly [])` THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[POLY_LENGTH_MUL; SUC_INJ] THEN
      DISCH_TAC THEN ASM_CASES_TAC `poly q = poly []` THENL
       [ASM_REWRITE_TAC[POLY_MUL; poly; COMPLEX_MUL_RZERO; FUN_EQ_THM];
        DISCH_THEN(K ALL_TAC)] THEN
      DISCH_THEN(MP_TAC o SPEC `q:complex list`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `i:num->complex`) THEN
      EXISTS_TAC `\m. if m = SUC n then a:complex else i m` THEN
      REWRITE_TAC[POLY_MUL; LE; COMPLEX_ENTIRE] THEN
      X_GEN_TAC `x:complex` THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN(fun th -> EXISTS_TAC `SUC n` THEN MP_TAC th) THEN
        REWRITE_TAC[poly] THEN SIMPLE_COMPLEX_ARITH_TAC;
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `m:num <= n` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
      UNDISCH_TAC `~(?a. poly p a = Cx(&0))` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

let POLY_ROOTS_INDEX_LENGTH = prove
 (`!p. ~(poly p = poly [])
       ==> ?i. !x. (poly p(x) = Cx(&0)) ==> ?n. n <= LENGTH p /\ (x = i n)`,
  MESON_TAC[POLY_ROOTS_INDEX_LEMMA]);;

let POLY_ROOTS_FINITE_LEMMA = prove
 (`!p. ~(poly p = poly [])
       ==> ?N i. !x. (poly p(x) = Cx(&0)) ==> ?n:num. n < N /\ (x = i n)`,
  MESON_TAC[POLY_ROOTS_INDEX_LENGTH; LT_SUC_LE]);;

let FINITE_LEMMA = prove
 (`!i N P. (!x. P x ==> ?n:num. n < N /\ (x = i n))
           ==> ?a. !x. P x ==> norm(x) < a`,
  GEN_TAC THEN ONCE_REWRITE_TAC[RIGHT_IMP_EXISTS_THM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `P:complex->bool` THEN
  POP_ASSUM(MP_TAC o SPEC `\z. P z /\ ~(z = (i:num->complex) N)`) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `abs(a) + norm(i(N:num)) + &1` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LT] THEN
  SUBGOAL_THEN `(!x. norm(x) < abs(a) + norm(x) + &1) /\
                (!x y. norm(x) < a ==> norm(x) < abs(a) + norm(y) + &1)`
   (fun th -> MP_TAC th THEN MESON_TAC[]) THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN MP_TAC(SPEC `y:complex` COMPLEX_NORM_POS) THEN
  REAL_ARITH_TAC);;

let POLY_ROOTS_FINITE = prove
 (`!p. ~(poly p = poly []) <=>
       ?N i. !x. (poly p(x) = Cx(&0)) ==> ?n:num. n < N /\ (x = i n)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE_LEMMA] THEN
  REWRITE_TAC[FUN_EQ_THM; LEFT_IMP_EXISTS_THM; NOT_FORALL_THM; poly] THEN
  MP_TAC(GENL [`i:num->complex`; `N:num`]
   (SPECL [`i:num->complex`; `N:num`; `\x. poly p x = Cx(&0)`]
         FINITE_LEMMA)) THEN
  REWRITE_TAC[] THEN MESON_TAC[REAL_ARITH `~(abs(x) < x)`; COMPLEX_NORM_CX]);;

(* ------------------------------------------------------------------------- *)
(* Hence get entirety and cancellation for polynomials.                      *)
(* ------------------------------------------------------------------------- *)

let POLY_ENTIRE_LEMMA = prove
 (`!p q. ~(poly p = poly []) /\ ~(poly q = poly [])
         ==> ~(poly (p ** q) = poly [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (X_CHOOSE_TAC `i2:num->complex`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (X_CHOOSE_TAC `i1:num->complex`)) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  EXISTS_TAC `\n:num. if n < N1 then i1(n):complex else i2(n - N1)` THEN
  X_GEN_TAC `x:complex` THEN REWRITE_TAC[COMPLEX_ENTIRE; POLY_MUL] THEN
  DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN (X_CHOOSE_TAC `n:num`))) THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN ARITH_TAC;
    EXISTS_TAC `N1 + n:num` THEN ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `~(m + n < m:num)`] THEN
    AP_TERM_TAC THEN ARITH_TAC]);;

let POLY_ENTIRE = prove
 (`!p q. (poly (p ** q) = poly []) <=>
         (poly p = poly []) \/ (poly q = poly [])`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[POLY_ENTIRE_LEMMA];
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_MUL_LZERO; poly]]);;

let POLY_MUL_LCANCEL = prove
 (`!p q r. (poly (p ** q) = poly (p ** r)) <=>
           (poly p = poly []) \/ (poly q = poly r)`,
  let lemma1 = prove
   (`!p q. (poly (p ++ neg q) = poly []) <=> (poly p = poly q)`,
    REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_NEG; poly] THEN
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH `(p + --q = Cx(&0)) <=> (p = q)`]) in
  let lemma2 = prove
   (`!p q r. poly (p ** q ++ neg(p ** r)) = poly (p ** (q ++ neg(r)))`,
    REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_NEG; POLY_MUL] THEN
    SIMPLE_COMPLEX_ARITH_TAC) in
  ONCE_REWRITE_TAC[GSYM lemma1] THEN
  REWRITE_TAC[lemma2; POLY_ENTIRE] THEN
  REWRITE_TAC[lemma1]);;

let POLY_EXP_EQ_0 = prove
 (`!p n. (poly (p exp n) = poly []) <=> (poly p = poly []) /\ ~(n = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN
  REWRITE_TAC[LEFT_AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[poly_exp; poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID;
    CX_INJ; REAL_OF_NUM_EQ; ARITH; NOT_SUC] THEN
  ASM_REWRITE_TAC[POLY_MUL; poly; COMPLEX_ENTIRE] THEN
  CONV_TAC TAUT);;

let POLY_PRIME_EQ_0 = prove
 (`!a. ~(poly [a ; Cx(&1)] = poly [])`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&1) - a`) THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_EXP_PRIME_EQ_0 = prove
 (`!a n. ~(poly ([a ; Cx(&1)] exp n) = poly [])`,
  MESON_TAC[POLY_EXP_EQ_0; POLY_PRIME_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Can also prove a more "constructive" notion of polynomial being trivial.  *)
(* ------------------------------------------------------------------------- *)

let POLY_ZERO_LEMMA = prove
 (`!h t. (poly (CONS h t) = poly []) ==> (h = Cx(&0)) /\ (poly t = poly [])`,
  let lemma = REWRITE_RULE[FUN_EQ_THM; poly] POLY_ROOTS_FINITE in
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN
  ASM_CASES_TAC `h = Cx(&0)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[COMPLEX_ADD_LID];
    DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN
    POP_ASSUM MP_TAC THEN SIMPLE_COMPLEX_ARITH_TAC] THEN
  CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[lemma]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_TAC `i:num->complex`)) THEN
  MP_TAC(SPECL
    [`i:num->complex`; `N:num`; `\x. poly t x = Cx(&0)`] FINITE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(abs(a) + &1)`) THEN
  REWRITE_TAC[COMPLEX_ENTIRE; DE_MORGAN_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP
     (ASSUME `!x. (poly t x = Cx(&0)) ==> norm(x) < a`)) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC]);;

let POLY_ZERO = prove
 (`!p. (poly p = poly []) <=> ALL (\c. c = Cx(&0)) p`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP POLY_ZERO_LEMMA) THEN ASM_REWRITE_TAC[];
    POP_ASSUM(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; poly] THEN SIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Basics of divisibility.                                                   *)
(* ------------------------------------------------------------------------- *)

let divides = new_definition
  `p1 divides p2 <=> ?q. poly p2 = poly (p1 ** q)`;;

let POLY_PRIMES = prove
 (`!a p q. [a; Cx(&1)] divides (p ** q) <=>
           [a; Cx(&1)] divides p \/ [a; Cx(&1)] divides q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides; POLY_MUL; FUN_EQ_THM; poly] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; COMPLEX_MUL_RID] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:complex list` (MP_TAC o SPEC `--a`)) THEN
    REWRITE_TAC[COMPLEX_ENTIRE; GSYM complex_sub;
                COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO] THEN
    DISCH_THEN DISJ_CASES_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    (POP_ASSUM(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
     REWRITE_TAC[COMPLEX_NEG_NEG] THEN
     DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `s:complex list` SUBST_ALL_TAC)) THENL
      [EXISTS_TAC `[]:complex list` THEN REWRITE_TAC[poly; COMPLEX_MUL_RZERO];
       EXISTS_TAC `s:complex list` THEN GEN_TAC THEN
       REWRITE_TAC[POLY_MUL; poly] THEN SIMPLE_COMPLEX_ARITH_TAC]);
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_TAC `s:complex list`)) THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `s ** q`; EXISTS_TAC `p ** s`] THEN
    GEN_TAC THEN REWRITE_TAC[POLY_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC]);;

let POLY_DIVIDES_REFL = prove
 (`!p. p divides p`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN EXISTS_TAC `[Cx(&1)]` THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_DIVIDES_TRANS = prove
 (`!p q r. p divides q /\ q divides r ==> p divides r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:complex list` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex list` ASSUME_TAC) THEN
  EXISTS_TAC `t ** s` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; COMPLEX_MUL_ASSOC]);;

let POLY_DIVIDES_EXP = prove
 (`!p m n. m <= n ==> (p exp m) divides (p exp n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; POLY_DIVIDES_REFL] THEN
  MATCH_MP_TAC POLY_DIVIDES_TRANS THEN
  EXISTS_TAC `p exp (m + d)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[divides] THEN EXISTS_TAC `p:complex list` THEN
  REWRITE_TAC[poly_exp; FUN_EQ_THM; POLY_MUL] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_EXP_DIVIDES = prove
 (`!p q m n. (p exp n) divides q /\ m <= n ==> (p exp m) divides q`,
  MESON_TAC[POLY_DIVIDES_TRANS; POLY_DIVIDES_EXP]);;

let POLY_DIVIDES_ADD = prove
 (`!p q r. p divides q /\ p divides r ==> p divides (q ++ r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:complex list` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex list` ASSUME_TAC) THEN
  EXISTS_TAC `t ++ s` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_MUL] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_DIVIDES_SUB = prove
 (`!p q r. p divides q /\ p divides (q ++ r) ==> p divides r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:complex list` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex list` ASSUME_TAC) THEN
  EXISTS_TAC `s ++ neg(t)` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_MUL; POLY_NEG] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB; COMPLEX_MUL_RNEG] THEN
  ASM_REWRITE_TAC[] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_DIVIDES_SUB2 = prove
 (`!p q r. p divides r /\ p divides (q ++ r) ==> p divides q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_DIVIDES_SUB THEN
  EXISTS_TAC `r:complex list` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p divides (q ++ r)` THEN
  REWRITE_TAC[divides; POLY_ADD; FUN_EQ_THM; POLY_MUL] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:complex list`) THEN
  EXISTS_TAC `s:complex list` THEN
  X_GEN_TAC `x:complex` THEN POP_ASSUM(MP_TAC o SPEC `x:complex`) THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_DIVIDES_ZERO = prove
 (`!p q. (poly p = poly []) ==> q divides p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[divides] THEN
  EXISTS_TAC `[]:complex list` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; COMPLEX_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* At last, we can consider the order of a root.                             *)
(* ------------------------------------------------------------------------- *)

let POLY_ORDER_EXISTS = prove
 (`!a d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
             ==> ?n. ([--a; Cx(&1)] exp n) divides p /\
                     ~(([--a; Cx(&1)] exp (SUC n)) divides p)`,
  GEN_TAC THEN
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist num_RECURSION)
    `(!p q. mulexp 0 p q = q) /\
     (!p q n. mulexp (SUC n) p q = p ** (mulexp n p q))` THEN
  SUBGOAL_THEN
   `!d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
           ==> ?n q. (p = mulexp (n:num) [--a; Cx(&1)] q) /\
                     ~(poly q a = Cx(&0))`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH_EQ_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `p:complex list` THEN
    ASM_CASES_TAC `poly p a = Cx(&0)` THENL
     [STRIP_TAC THEN UNDISCH_TAC `poly p a = Cx(&0)` THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:complex list` SUBST_ALL_TAC) THEN
      UNDISCH_TAC
       `!p. (LENGTH p = d) /\ ~(poly p = poly [])
            ==> ?n q. (p = mulexp (n:num) [--a; Cx(&1)] q) /\
                      ~(poly q a = Cx(&0))` THEN
      DISCH_THEN(MP_TAC o SPEC `q:complex list`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[POLY_LENGTH_MUL; POLY_ENTIRE;
        DE_MORGAN_THM; SUC_INJ]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num`
       (X_CHOOSE_THEN `s:complex list` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `SUC n` THEN EXISTS_TAC `s:complex list` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `0` THEN EXISTS_TAC `p:complex list` THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num`
       (X_CHOOSE_THEN `s:complex list` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[divides] THEN CONJ_TAC THENL
     [EXISTS_TAC `s:complex list` THEN
      SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[poly_exp; FUN_EQ_THM; POLY_MUL; poly] THEN
      SIMPLE_COMPLEX_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `r:complex list` MP_TAC) THEN
      SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~(poly s a = Cx(&0))` THEN CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[poly; poly_exp; POLY_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC;
        REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[poly_exp] THEN
        REWRITE_TAC[GSYM POLY_MUL_ASSOC; POLY_MUL_LCANCEL] THEN
        REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `a + Cx(&1)`) THEN
          REWRITE_TAC[poly] THEN SIMPLE_COMPLEX_ARITH_TAC;
          DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]]]);;

let POLY_ORDER = prove
 (`!p a. ~(poly p = poly [])
         ==> ?!n. ([--a; Cx(&1)] exp n) divides p /\
                      ~(([--a; Cx(&1)] exp (SUC n)) divides p)`,
  MESON_TAC[POLY_ORDER_EXISTS; POLY_EXP_DIVIDES; LE_SUC_LT; LT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Definition of order.                                                      *)
(* ------------------------------------------------------------------------- *)

let order = new_definition
  `order a p = @n. ([--a; Cx(&1)] exp n) divides p /\
                   ~(([--a; Cx(&1)] exp (SUC n)) divides p)`;;

let ORDER = prove
 (`!p a n. ([--a; Cx(&1)] exp n) divides p /\
           ~(([--a; Cx(&1)] exp (SUC n)) divides p) <=>
           (n = order a p) /\
           ~(poly p = poly [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[order] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(poly p = poly [])` ASSUME_TAC THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[divides] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `[]:complex list` THEN
      REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; COMPLEX_MUL_RZERO];
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[]];
    ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV] THEN
  ASM_MESON_TAC[POLY_ORDER]);;

let ORDER_THM = prove
 (`!p a. ~(poly p = poly [])
         ==> ([--a; Cx(&1)] exp (order a p)) divides p /\
             ~(([--a; Cx(&1)] exp (SUC(order a p))) divides p)`,
  MESON_TAC[ORDER]);;

let ORDER_UNIQUE = prove
 (`!p a n. ~(poly p = poly []) /\
           ([--a; Cx(&1)] exp n) divides p /\
           ~(([--a; Cx(&1)] exp (SUC n)) divides p)
           ==> (n = order a p)`,
  MESON_TAC[ORDER]);;

let ORDER_POLY = prove
 (`!p q a. (poly p = poly q) ==> (order a p = order a q)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[order; divides; FUN_EQ_THM; POLY_MUL]);;

let ORDER_ROOT = prove
 (`!p a. (poly p a = Cx(&0)) <=> (poly p = poly []) \/ ~(order a p = 0)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `poly p = poly []` THEN
  ASM_REWRITE_TAC[poly] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
    ASM_CASES_TAC `p:complex list = []` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:complex list` SUBST_ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:complex` o MATCH_MP ORDER_THM) THEN
    ASM_REWRITE_TAC[poly_exp; DE_MORGAN_THM] THEN DISJ2_TAC THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `q:complex list` THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly] THEN SIMPLE_COMPLEX_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:complex` o MATCH_MP ORDER_THM) THEN
    UNDISCH_TAC `~(order a p = 0)` THEN
    SPEC_TAC(`order a p`,`n:num`) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[poly_exp; NOT_SUC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:complex list` SUBST1_TAC) THEN
    REWRITE_TAC[POLY_MUL; poly] THEN SIMPLE_COMPLEX_ARITH_TAC]);;

let ORDER_DIVIDES = prove
 (`!p a n. ([--a; Cx(&1)] exp n) divides p <=>
           (poly p = poly []) \/ n <= order a p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `poly p = poly []` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[divides] THEN EXISTS_TAC `[]:complex list` THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; COMPLEX_MUL_RZERO];
    ASM_MESON_TAC[ORDER_THM; POLY_EXP_DIVIDES; NOT_LE; LE_SUC_LT]]);;

let ORDER_DECOMP = prove
 (`!p a. ~(poly p = poly [])
         ==> ?q. (poly p = poly (([--a; Cx(&1)] exp (order a p)) ** q)) /\
                 ~([--a; Cx(&1)] divides q)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ORDER_THM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o SPEC `a:complex`) THEN
  DISCH_THEN(X_CHOOSE_TAC `q:complex list` o REWRITE_RULE[divides]) THEN
  EXISTS_TAC `q:complex list` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r: complex list` o REWRITE_RULE[divides]) THEN
  UNDISCH_TAC `~([-- a; Cx(&1)] exp SUC (order a p) divides p)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[divides] THEN
  EXISTS_TAC `r:complex list` THEN
  ASM_REWRITE_TAC[POLY_MUL; FUN_EQ_THM; poly_exp] THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Important composition properties of orders.                               *)
(* ------------------------------------------------------------------------- *)

let ORDER_MUL = prove
 (`!a p q. ~(poly (p ** q) = poly []) ==>
           (order a (p ** q) = order a p + order a q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[POLY_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(order a p + order a q = order a (p ** q)) /\
                ~(poly (p ** q) = poly [])`
  MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[GSYM ORDER] THEN CONJ_TAC THENL
   [MP_TAC(CONJUNCT1 (SPEC `a:complex`
      (MATCH_MP ORDER_THM (ASSUME `~(poly p = poly [])`)))) THEN
    DISCH_THEN(X_CHOOSE_TAC `r: complex list` o REWRITE_RULE[divides]) THEN
    MP_TAC(CONJUNCT1 (SPEC `a:complex`
      (MATCH_MP ORDER_THM (ASSUME `~(poly q = poly [])`)))) THEN
    DISCH_THEN(X_CHOOSE_TAC `s: complex list` o REWRITE_RULE[divides]) THEN
    REWRITE_TAC[divides; FUN_EQ_THM] THEN EXISTS_TAC `s ** r` THEN
    ASM_REWRITE_TAC[POLY_MUL; POLY_EXP_ADD] THEN SIMPLE_COMPLEX_ARITH_TAC;
    X_CHOOSE_THEN `r: complex list` STRIP_ASSUME_TAC
    (SPEC `a:complex` (MATCH_MP ORDER_DECOMP
       (ASSUME `~(poly p = poly [])`))) THEN
    X_CHOOSE_THEN `s: complex list` STRIP_ASSUME_TAC
    (SPEC `a:complex` (MATCH_MP ORDER_DECOMP
       (ASSUME `~(poly q = poly [])`))) THEN
    ASM_REWRITE_TAC[divides; FUN_EQ_THM; POLY_EXP_ADD; POLY_MUL; poly_exp] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:complex list` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `[--a; Cx(&1)] divides (r ** s)` MP_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[POLY_PRIMES]] THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `t:complex list` THEN
    SUBGOAL_THEN `poly ([-- a; Cx(&1)] exp (order a p) ** r ** s) =
                  poly ([-- a; Cx(&1)] exp (order a p) **
                       ([-- a; Cx(&1)] ** t))`
    MP_TAC THENL
     [ALL_TAC; MESON_TAC[POLY_MUL_LCANCEL; POLY_EXP_PRIME_EQ_0]] THEN
    SUBGOAL_THEN `poly ([-- a; Cx(&1)] exp (order a q) **
                        [-- a; Cx(&1)] exp (order a p) ** r ** s) =
                  poly ([-- a; Cx(&1)] exp (order a q) **
                        [-- a; Cx(&1)] exp (order a p) **
                        [-- a; Cx(&1)] ** t)`
    MP_TAC THENL
     [ALL_TAC; MESON_TAC[POLY_MUL_LCANCEL; POLY_EXP_PRIME_EQ_0]] THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_ADD] THEN
    FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
    REWRITE_TAC[COMPLEX_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Normalization of a polynomial.                                            *)
(* ------------------------------------------------------------------------- *)

let normalize = new_recursive_definition list_RECURSION
  `(normalize [] = []) /\
   (normalize (CONS h t) =
        if normalize t = [] then if h = Cx(&0) then [] else [h]
        else CONS h (normalize t))`;;

let POLY_NORMALIZE = prove
 (`!p. poly (normalize p) = poly p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[normalize; poly] THEN
  ASM_CASES_TAC `h = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[poly; FUN_EQ_THM] THEN
  UNDISCH_TAC `poly (normalize t) = poly t` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[poly] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID]);;

let LENGTH_NORMALIZE_LE = prove
 (`!p. LENGTH(normalize p) <= LENGTH p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; normalize; LE_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; LE_SUC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The degree of a polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

let degree = new_definition
  `degree p = PRE(LENGTH(normalize p))`;;

let DEGREE_ZERO = prove
 (`!p. (poly p = poly []) ==> (degree p = 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[degree] THEN
  SUBGOAL_THEN `normalize p = []` SUBST1_TAC THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`p:complex list`,`p:complex list`) THEN
    REWRITE_TAC[POLY_ZERO] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[normalize; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `normalize t = []` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LENGTH; PRE]]);;

(* ------------------------------------------------------------------------- *)
(* Show that the degree is welldefined.                                      *)
(* ------------------------------------------------------------------------- *)

let POLY_CONS_EQ = prove
 (`(poly (CONS h1 t1) = poly (CONS h2 t2)) <=>
   (h1 = h2) /\ (poly t1 = poly t2)`,
  REWRITE_TAC[FUN_EQ_THM] THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[poly]] THEN
  ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH `(a = b) <=> (a + --b = Cx(&0))`] THEN
  REWRITE_TAC[GSYM POLY_NEG; GSYM POLY_ADD] THEN DISCH_TAC THEN
  SUBGOAL_THEN `poly (CONS h1 t1 ++ neg(CONS h2 t2)) = poly []` MP_TAC THENL
   [ASM_REWRITE_TAC[poly; FUN_EQ_THM]; ALL_TAC] THEN
  REWRITE_TAC[poly_neg; poly_cmul; poly_add; NOT_CONS_NIL; HD; TL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP POLY_ZERO_LEMMA) THEN
  SIMP_TAC[poly; COMPLEX_MUL_LNEG; COMPLEX_MUL_LID]);;

let POLY_NORMALIZE_ZERO = prove
 (`!p. (poly p = poly []) <=> (normalize p = [])`,
  REWRITE_TAC[POLY_ZERO] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; normalize] THEN
  ASM_CASES_TAC `normalize t = []` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let POLY_NORMALIZE_EQ_LEMMA = prove
 (`!p q. (poly p = poly q) ==> (normalize p = normalize q)`,
  LIST_INDUCT_TAC THENL
   [MESON_TAC[POLY_NORMALIZE_ZERO]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [MESON_TAC[POLY_NORMALIZE_ZERO]; ALL_TAC] THEN
  REWRITE_TAC[POLY_CONS_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[normalize] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':complex list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let POLY_NORMALIZE_EQ = prove
 (`!p q. (poly p = poly q) <=> (normalize p = normalize q)`,
  MESON_TAC[POLY_NORMALIZE_EQ_LEMMA; POLY_NORMALIZE]);;

let DEGREE_WELLDEF = prove
 (`!p q. (poly p = poly q) ==> (degree p = degree q)`,
  SIMP_TAC[degree; POLY_NORMALIZE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Degree of a product with a power of linear terms.                         *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_EQ = prove
 (`!p. ~(LAST p = Cx(&0)) ==> (normalize p = p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  REWRITE_TAC[normalize; LAST] THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[normalize]));;

let NORMAL_DEGREE = prove
 (`!p. ~(LAST p = Cx(&0)) ==> (degree p = LENGTH p - 1)`,
  SIMP_TAC[degree; NORMALIZE_EQ] THEN REPEAT STRIP_TAC THEN ARITH_TAC);;

let LAST_LINEAR_MUL_LEMMA = prove
 (`!p a b x.
     LAST(a ## p ++ CONS x (b ## p)) = if p = [] then x else b * LAST(p)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_cmul; poly_add; LAST; HD; TL; NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `~(a ## t ++ CONS (b * h) (b ## t) = [])`
  ASSUME_TAC THENL
   [SPEC_TAC(`t:complex list`,`t:complex list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[poly_cmul; poly_add; NOT_CONS_NIL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let LAST_LINEAR_MUL = prove
 (`!p. ~(p = []) ==> (LAST([a; Cx(&1)] ** p) = LAST p)`,
  SIMP_TAC[poly_mul; NOT_CONS_NIL; LAST_LINEAR_MUL_LEMMA; COMPLEX_MUL_LID]);;

let NORMAL_NORMALIZE = prove
 (`!p. ~(normalize p = []) ==> ~(LAST(normalize p) = Cx(&0))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[normalize] THEN
  POP_ASSUM MP_TAC THEN ASM_CASES_TAC `normalize t = []` THEN
  ASM_REWRITE_TAC[LAST; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LAST]);;

let LINEAR_MUL_DEGREE = prove
 (`!p a. ~(poly p = poly []) ==> (degree([a; Cx(&1)] ** p) = degree(p) + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `degree([a; Cx(&1)] ** normalize p) = degree(normalize p) + 1`
  MP_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o
      GEN_REWRITE_RULE RAND_CONV [POLY_NORMALIZE_ZERO]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP NORMAL_NORMALIZE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LAST_LINEAR_MUL) THEN
    SIMP_TAC[NORMAL_DEGREE] THEN REPEAT STRIP_TAC THEN
    SUBST1_TAC(SYM(SPEC `a:complex` COMPLEX_NEG_NEG)) THEN
    REWRITE_TAC[POLY_LENGTH_MUL] THEN
    UNDISCH_TAC `~(normalize p = [])` THEN
    SPEC_TAC(`normalize p`,`p:complex list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LENGTH] THEN ARITH_TAC;
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN MATCH_MP_TAC DEGREE_WELLDEF THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_NORMALIZE]]);;

let LINEAR_POW_MUL_DEGREE = prove
 (`!n a p. degree([a; Cx(&1)] exp n ** p) =
                if poly p = poly [] then 0 else degree p + n`,
  INDUCT_TAC THEN REWRITE_TAC[poly_exp] THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `degree(p)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DEGREE_WELLDEF THEN
        REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; COMPLEX_MUL_RZERO;
                    COMPLEX_ADD_RID; COMPLEX_MUL_LID];
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `degree []` THEN CONJ_TAC THENL
         [MATCH_MP_TAC DEGREE_WELLDEF THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[degree; LENGTH; normalize; ARITH]]];
      REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC DEGREE_WELLDEF THEN
      REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; COMPLEX_MUL_RZERO;
                  COMPLEX_ADD_RID; COMPLEX_MUL_LID]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `degree([a; Cx (&1)] exp n ** ([a; Cx (&1)] ** p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DEGREE_WELLDEF THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; COMPLEX_MUL_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[POLY_ENTIRE] THEN
  ASM_CASES_TAC `poly p = poly []` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_MUL_DEGREE] THEN
  SUBGOAL_THEN `~(poly [a; Cx (&1)] = poly [])`
   (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  REWRITE_TAC[POLY_NORMALIZE_EQ] THEN
  REWRITE_TAC[normalize; CX_INJ; REAL_OF_NUM_EQ; ARITH; NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Show that the order of a root (or nonroot!) is bounded by degree.         *)
(* ------------------------------------------------------------------------- *)

let ORDER_DEGREE = prove
 (`!a p. ~(poly p = poly []) ==> order a p <= degree p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:complex` o MATCH_MP ORDER_THM) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[divides] o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:complex list` ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DEGREE_WELLDEF) THEN
  ASM_REWRITE_TAC[LINEAR_POW_MUL_DEGREE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[POLY_MUL] THENL
   [UNDISCH_TAC `~(poly p = poly [])` THEN
    SIMP_TAC[FUN_EQ_THM; POLY_MUL; poly; COMPLEX_MUL_RZERO];
    DISCH_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tidier versions of finiteness of roots.                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ROOTS_FINITE_SET = prove
 (`!p. ~(poly p = poly []) ==> FINITE { x | poly p x = Cx(&0)}`,
  GEN_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num->complex` ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:complex | ?n:num. n < N /\ (x = i n)}` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`N:num`,`N:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    INDUCT_TAC THENL
     [SUBGOAL_THEN `{x:complex | ?n. n < 0 /\ (x = i n)} = {}`
      (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LT];
      SUBGOAL_THEN `{x:complex | ?n. n < SUC N /\ (x = i n)} =
                    (i N) INSERT {x:complex | ?n. n < N /\ (x = i n)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; LT] THEN MESON_TAC[];
        MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN ASM_REWRITE_TAC[]]];
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RAT_MUL_CONV =
  GEN_REWRITE_CONV I [GSYM CX_MUL] THENC RAND_CONV REAL_RAT_MUL_CONV;;

let COMPLEX_RAT_ADD_CONV =
  GEN_REWRITE_CONV I [GSYM CX_ADD] THENC RAND_CONV REAL_RAT_ADD_CONV;;

let COMPLEX_RAT_EQ_CONV =
  GEN_REWRITE_CONV I [CX_INJ] THENC REAL_RAT_EQ_CONV;;

let POLY_CMUL_CONV =
  let cmul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_cmul]
  and cmul_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_cmul] in
  let rec POLY_CMUL_CONV tm =
   (cmul_conv0 ORELSEC
    (cmul_conv1 THENC
     LAND_CONV COMPLEX_RAT_MUL_CONV THENC
     RAND_CONV POLY_CMUL_CONV)) tm in
  POLY_CMUL_CONV;;

let POLY_ADD_CONV =
  let add_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_ADD_CLAUSES))
  and add_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_ADD_CLAUSES)] in
  let rec POLY_ADD_CONV tm =
   (add_conv0 ORELSEC
    (add_conv1 THENC
     LAND_CONV COMPLEX_RAT_ADD_CONV THENC
     RAND_CONV POLY_ADD_CONV)) tm in
  POLY_ADD_CONV;;

let POLY_MUL_CONV =
  let mul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 POLY_MUL_CLAUSES]
  and mul_conv1 = GEN_REWRITE_CONV I [CONJUNCT1(CONJUNCT2 POLY_MUL_CLAUSES)]
  and mul_conv2 = GEN_REWRITE_CONV I [CONJUNCT2(CONJUNCT2 POLY_MUL_CLAUSES)] in
  let rec POLY_MUL_CONV tm =
   (mul_conv0 ORELSEC
    (mul_conv1 THENC POLY_CMUL_CONV) ORELSEC
    (mul_conv2 THENC
     LAND_CONV POLY_CMUL_CONV THENC
     RAND_CONV(RAND_CONV POLY_MUL_CONV) THENC
     POLY_ADD_CONV)) tm in
  POLY_MUL_CONV;;

let POLY_NORMALIZE_CONV =
  let pth = prove
   (`normalize (CONS h t) =
      (\n. if n = [] then if h = Cx(&0) then [] else [h] else CONS h n)
      (normalize t)`,
    REWRITE_TAC[normalize]) in
  let norm_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 normalize]
  and norm_conv1 = GEN_REWRITE_CONV I [pth]
  and norm_conv2 = GEN_REWRITE_CONV DEPTH_CONV
   [COND_CLAUSES; NOT_CONS_NIL; EQT_INTRO(SPEC_ALL EQ_REFL)] in
  let rec POLY_NORMALIZE_CONV tm =
   (norm_conv0 ORELSEC
    (norm_conv1 THENC
     RAND_CONV POLY_NORMALIZE_CONV THENC
     BETA_CONV THENC
     RATOR_CONV(RAND_CONV(RATOR_CONV(LAND_CONV COMPLEX_RAT_EQ_CONV))) THENC
     norm_conv2)) tm in
  POLY_NORMALIZE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Now we're finished with polynomials...                                    *)
(* ------------------------------------------------------------------------- *)

(************** keep this for now

do_list reduce_interface
 ["divides",`poly_divides:complex list->complex list->bool`;
  "exp",`poly_exp:complex list -> num -> complex list`;
  "diff",`poly_diff:complex list->complex list`];;

unparse_as_infix "exp";;

 ****************)
