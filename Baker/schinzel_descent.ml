(* ========================================================================= *)
(* The bounded power descent over Z (for the Schinzel-Tijdeman theorem).     *)
(*                                                                           *)
(* Purpose: for integers G, W, y, c, R with G, c, R non-zero, G W = c y^m    *)
(* and a G + b W = R for some integers a, b, there are positive integers N1, *)
(* N2 and an integer Y with N1 dividing c R, N2 dividing R and               *)
(* abs(G) N2 = N1 abs(Y)^m: the factor G of a perfect power is an m-th power *)
(* up to a bounded rational factor N1 / N2 (Schinzel and Tijdeman 1976: the  *)
(* step from y^m = f(x) to a linear form in two logarithms in the norm-trick *)
(* proof of the reducible case; the general theorem of                       *)
(* Baker/schinzel_general.ml descends by S-units instead, and                *)
(* INT_POWER_DESCENT_BOUNDED is a result of its own).                        *)
(*                                                                           *)
(* The proof works over num with the p-adic index of Library/prime.ml: for a *)
(* prime p either index p G <= index p (c R), and p^(index p G) goes into    *)
(* N1, or else index p W <= index p R (a common divisor of G and W divides   *)
(* R) and index p G - m index p y = index p c - index p W is split between   *)
(* N1 and N2; N1, N2 and Y are built from their index functions with         *)
(* PRIME_FACTORIZATION_INDEX and the equation is checked prime by prime      *)
(* (EQ_INDEX).                                                               *)
(*                                                                           *)
(* Main results: INT_POWER_DESCENT_BOUNDED; the generic lemma                *)
(* INTEGER_DIVIDES_ABS; helper names INT_DESCENT_*.                          *)
(*                                                                           *)
(* Uses: Library/prime.ml (index, EQ_INDEX, PRIME_FACTORIZATION_INDEX,       *)
(* INDEX_MUL, INDEX_EXP) and Library/floor.ml (INTEGER_CLOSED).              *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/floor.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Prime-by-prime arithmetic of the three index functions.                   *)
(* ------------------------------------------------------------------------- *)

let INT_DESCENT_INDEX_ARITH = prove
 (`!g w c r s y m.
     s = c + r /\ g + w = c + m * y /\ (~(g <= s) ==> w <= r)
     ==> (if g <= s then g else c - w) <= s /\
         (if g <= s then 0 else w - c) <= r /\
         g + (if g <= s then 0 else w - c) =
         (if g <= s then g else c - w) + m * (if g <= s then 0 else y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* If p^(index p G) does not divide c R then index p W <= index p R.         *)
(* ------------------------------------------------------------------------- *)

let INT_DESCENT_INDEX_CASE2 = prove
 (`!G W c R p.
     prime p /\ ~(G = 0) /\ ~(W = 0) /\ ~(c = 0) /\ ~(R = 0) /\
     (!d. d divides G /\ d divides W ==> d divides R) /\
     ~(index p G <= index p (c * R))
     ==> index p W <= index p R`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `index p (c * R) = index p c + index p R` ASSUME_TAC THENL
   [MATCH_MP_TAC INDEX_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p EXP (index p R + 1) divides R` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(index p G <= index p (c * R))`;
      `index p (c * R) = index p c + index p R`;
      `index p R < index p W`] THEN
    ARITH_TAC;
    REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
    MP_TAC(MATCH_MP PRIME_GE_2 (ASSUME `prime p`)) THEN
    UNDISCH_TAC `~(R = 0)` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A num with prescribed indices, supported on the prime divisors of n.      *)
(* ------------------------------------------------------------------------- *)

let INT_DESCENT_FACTORIZATION = prove
 (`!n k. ~(n = 0) /\ (!p. prime p /\ ~(k p = 0) ==> p divides n)
         ==> ?N. ~(N = 0) /\ !p. prime p ==> index p N = k p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRIME_FACTORIZATION_INDEX THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides (n:num)}` THEN
  ASM_SIMP_TAC[FINITE_DIVISORS; SUBSET; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* The conclusion of the descent from prime-by-prime index inequalities.     *)
(* ------------------------------------------------------------------------- *)

let INT_DESCENT_FROM_INDEX = prove
 (`!G R c m N1 N2 Y.
     ~(G = 0) /\ ~(c = 0) /\ ~(R = 0) /\
     ~(N1 = 0) /\ ~(N2 = 0) /\ ~(Y = 0) /\
     (!p. prime p
          ==> index p N1 <= index p (c * R) /\ index p N2 <= index p R /\
              index p G + index p N2 = index p N1 + m * index p Y)
     ==> N1 divides c * R /\ N2 divides R /\ G * N2 = N1 * Y EXP m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIVIDES_INDEX];
    ASM_SIMP_TAC[DIVIDES_INDEX];
    ONCE_REWRITE_TAC[EQ_INDEX] THEN
    ASM_SIMP_TAC[INDEX_MUL; INDEX_EXP; MULT_EQ_0; EXP_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* The num core of the descent.                                              *)
(* ------------------------------------------------------------------------- *)

let INT_DESCENT_NUM = prove
 (`!G W y c R m.
     ~(G = 0) /\ ~(c = 0) /\ ~(R = 0) /\
     G * W = c * y EXP m /\
     (!d. d divides G /\ d divides W ==> d divides R)
     ==> ?N1 N2 Y. ~(N1 = 0) /\ ~(N2 = 0) /\
                   N1 divides c * R /\ N2 divides R /\
                   G * N2 = N1 * Y EXP m`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `W = 0` THENL
   [MAP_EVERY EXISTS_TAC [`G:num`; `1`; `1`] THEN
    REWRITE_TAC[DIVIDES_1; EXP_ONE; MULT_CLAUSES; ARITH_EQ] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIVIDES_LMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIVIDES_REFL; DIVIDES_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y EXP m = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `G * W = c * y EXP m` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; MULT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. prime p ==> index p G + index p W = index p c + m * index p y`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`G:num`; `W:num`] (SPEC `p:num` (GEN `p:num` INDEX_MUL))) THEN
    MP_TAC(SPECL [`c:num`; `y EXP m`]
      (SPEC `p:num` (GEN `p:num` INDEX_MUL))) THEN
    MP_TAC(SPECL [`p:num`; `y:num`; `m:num`] INDEX_EXP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. ~(index p G = 0) ==> p divides G` ASSUME_TAC THENL
   [MESON_TAC[INDEX_ZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:num`;
    `\p. if index p G <= index p (c * R) then 0 else index p y`]
    INT_DESCENT_FACTORIZATION) THEN
  MP_TAC(ISPECL [`G:num`;
    `\p. if index p G <= index p (c * R) then 0
         else index p W - index p c`]
    INT_DESCENT_FACTORIZATION) THEN
  MP_TAC(ISPECL [`G:num`;
    `\p. if index p G <= index p (c * R) then index p G
         else index p c - index p W`]
    INT_DESCENT_FACTORIZATION) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `Y:num` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`N1:num`; `N2:num`; `Y:num`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_DESCENT_FROM_INDEX THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`index p G`; `index p W`; `index p c`; `index p R`;
                `index p (c * R)`; `index p y`; `m:num`]
               INT_DESCENT_INDEX_ARITH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INDEX_MUL THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN MATCH_MP_TAC INT_DESCENT_INDEX_CASE2 THEN
      MAP_EVERY EXISTS_TAC [`G:num`; `c:num`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Integer-valued reals: from absolute values to nums and back; the          *)
(* divisors of a real integer v are those of the num abs v                   *)
(* (INTEGER_DIVIDES_ABS, also used by Baker/prime_factors.ml).               *)
(* ------------------------------------------------------------------------- *)

let INT_DESCENT_ABS_NZ = prove
 (`!x n. abs(x:real) = &n /\ ~(x = &0) ==> ~(n = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC);;

let INTEGER_DIVIDES_ABS = prove
 (`!v n p. abs v = &n ==> ((?k. integer k /\ v = &p * k) <=> p divides n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divides] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `integer(k:real)` THEN REWRITE_TAC[integer] THEN
    DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN EXISTS_TAC `j:num` THEN
    UNDISCH_TAC `abs v = &n` THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
     (REAL_ARITH `abs v = a ==> v = a \/ v = --a`)) THENL
     [EXISTS_TAC `&j:real`; EXISTS_TAC `-- &j:real`] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC]);;

let INT_DESCENT_ABS_EQ = prove
 (`!G W y c m g w u k.
     abs(G:real) = &g /\ abs(W:real) = &w /\ abs(y:real) = &u /\
     abs(c:real) = &k /\ G * W = c * y pow m
     ==> g * w = k * u EXP m`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `(G:real) * W = c * y pow m` THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs:real->real`) THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_EQ]);;

let INT_DESCENT_ABS_LINEAR = prove
 (`!a b t1 t2 d r q.
     abs((a:real) * (&d * t1) + b * (&d * t2)) = &r /\
     abs(a * t1 + b * t2) = &q
     ==> r = d * q`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_ARITH
   `(a:real) * (d * t1) + b * (d * t2) = d * (a * t1 + b * t2)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) SUBST1_TAC) THEN
  REFL_TAC);;

let INT_DESCENT_COMMON_DIVISOR = prove
 (`!G W a b g w r d.
     integer a /\ integer b /\
     abs(G:real) = &g /\ abs(W:real) = &w /\ abs(a * G + b * W) = &r /\
     d divides g /\ d divides w
     ==> d divides r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`W:real`; `w:num`; `d:num`] INTEGER_DIVIDES_ABS) THEN
  MP_TAC(SPECL [`G:real`; `g:num`; `d:num`] INTEGER_DIVIDES_ABS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `integer(a * t1 + b * t2)` MP_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[integer] THEN DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  REWRITE_TAC[divides] THEN EXISTS_TAC `q:num` THEN
  MATCH_MP_TAC INT_DESCENT_ABS_LINEAR THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `t1:real`; `t2:real`] THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bounded descent over Z.                                               *)
(* ------------------------------------------------------------------------- *)

let INT_POWER_DESCENT_BOUNDED = prove
 (`!G W y c R m.
    integer G /\ integer W /\ integer y /\ integer c /\ integer R /\
    ~(G = &0) /\ ~(c = &0) /\ ~(R = &0) /\
    G * W = c * y pow m /\
    (?a b. integer a /\ integer b /\ a * G + b * W = R)
    ==> ?N1 N2 Y. integer N1 /\ integer N2 /\ integer Y /\
                  &1 <= N1 /\ &1 <= N2 /\
                  (?t. integer t /\ c * R = N1 * t) /\
                  (?t. integer t /\ R = N2 * t) /\
                  abs G * N2 = N1 * abs Y pow m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `gn:num` o REWRITE_RULE[integer])
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `wn:num` o REWRITE_RULE[integer])
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `yn:num` o REWRITE_RULE[integer])
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `cn:num` o REWRITE_RULE[integer])
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `rn:num` o REWRITE_RULE[integer])
    STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`gn:num`; `wn:num`; `yn:num`; `cn:num`; `rn:num`; `m:num`]
    INT_DESCENT_NUM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INT_DESCENT_ABS_NZ THEN EXISTS_TAC `G:real` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC INT_DESCENT_ABS_NZ THEN EXISTS_TAC `c:real` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC INT_DESCENT_ABS_NZ THEN EXISTS_TAC `R:real` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC INT_DESCENT_ABS_EQ THEN
      MAP_EVERY EXISTS_TAC [`G:real`; `W:real`; `y:real`; `c:real`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC INT_DESCENT_COMMON_DIVISOR THEN
      MAP_EVERY EXISTS_TAC
       [`G:real`; `W:real`; `a:real`; `b:real`; `gn:num`; `wn:num`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      SUBST1_TAC(ASSUME `(a:real) * G + b * W = R`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `n2:num`
    (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`&n1:real`; `&n2:real`; `&v:real`] THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_LE; REAL_ABS_NUM] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(n1 = 0)` THEN ARITH_TAC;
    UNDISCH_TAC `~(n2 = 0)` THEN ARITH_TAC;
    MP_TAC(SPECL [`c * R:real`; `cn * rn`; `n1:num`] INTEGER_DIVIDES_ABS) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_OF_NUM_MUL];
    MP_TAC(SPECL [`R:real`; `rn:num`; `n2:num`] INTEGER_DIVIDES_ABS) THEN
    ASM_REWRITE_TAC[];
    SUBST1_TAC(ASSUME `abs(G:real) = &gn`) THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
    FIRST_ASSUM ACCEPT_TAC]);;
