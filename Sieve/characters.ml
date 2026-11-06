(* ========================================================================= *)
(* Primitive Dirichlet characters and induced characters.                    *)
(*                                                                           *)
(* primitive_character q c: c is a character mod q which is nontrivial on    *)
(* {a | a == 1 (mod r), (a,q) = 1} for every proper divisor r of q.  This    *)
(* characterisation avoids characters mod r altogether in the definition.    *)
(*                                                                           *)
(* PRIMITIVE_CHARACTER_EXISTS: every character mod q (q > 0) agrees on the   *)
(* units mod q with a primitive character mod some r | q, and                *)
(* PRIMITIVE_CHARACTER_UNIQUE: this r and character are unique (the          *)
(* conductor and the primitive character inducing c).                        *)
(* DIRICHLET_CHARACTER_INDUCED: conversely a character mod r | q induces one *)
(* mod q.  PRIMITIVE_CHARACTER_NONPRINCIPAL: for q > 1 a primitive character *)
(* is nonprincipal.                                                          *)
(* DIRICHLET_CHARACTER_NORM_LE: |c(n)| <= 1.                                 *)
(*                                                                           *)
(* Method.  The moduli r | q with c trivial on {a == 1 (mod r)} are closed   *)
(* under gcd (CHARACTER_TRIVIAL_GCD, via the strong Chinese remainder        *)
(* theorem CONG_CRT_STRONG); the least such r is the conductor.  A character *)
(* trivial on {a == 1 (mod r)} factors through the residues mod r, and       *)
(* every unit mod r lifts to a unit mod q (COPRIME_ADJUST), which defines    *)
(* the character mod r.                                                      *)
(* ========================================================================= *)

needs "Sieve/base.ml";;
needs "100/dirichlet.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Arithmetic preliminaries.                                                 *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_NPRODUCT_ELEMENT = prove
 (`!s x:A f. FINITE s /\ x IN s ==> f x divides nproduct s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->num`; `s:A->bool`; `x:A`] NPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]);;

let COPRIME_ADJUST = prove
 (`!n r q. coprime(n,r) /\ ~(q = 0) ==> ?k. coprime(n + k * r,q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides q /\ ~(p divides n)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | p divides q}` THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `S = {p | prime p /\ p divides q /\ ~(p divides n)}` THEN
  EXISTS_TAC `nproduct S (\p:num. p)` THEN
  REWRITE_TAC[COPRIME_PRIME_EQ] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:num) divides n` THENL
   [SUBGOAL_THEN `~(p divides r)` ASSUME_TAC THENL
     [ASM_MESON_TAC[COPRIME_PRIME]; ALL_TAC] THEN
    SUBGOAL_THEN `~(p divides nproduct S (\p:num. p))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM PRIME_COPRIME_EQ; COPRIME_NPRODUCT_EQ] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `p':num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; DIVIDES_PRIME_PRIME] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p divides nproduct S (\p:num. p) * r` MP_TAC THENL
     [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[PRIME_DIVPROD]];
    SUBGOAL_THEN `p divides nproduct S (\p:num. p)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S:num->bool`; `p:num`; `\p:num. p`]
        DIVIDES_NPRODUCT_ELEMENT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    UNDISCH_TAC `~(p divides n)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_ADD_REVL THEN
    EXISTS_TAC `nproduct S (\p:num. p) * r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN ASM_REWRITE_TAC[]]);;

let CONG_CRT_STRONG = prove
 (`!a b n1 n2. ~(n1 = 0) /\ ~(n2 = 0) /\ (a == b) (mod gcd(n1,n2))
               ==> ?x. (x == a) (mod n1) /\ (x == b) (mod n2)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(a:num == b) (mod gcd(n1,n2))` THEN
  REWRITE_TAC[num_congruent; NUM_GCD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `!a1 a2 n1 n2:int. (a1 == a2) (mod (gcd(n1,n2)))
                      ==> ?x. (x == a1) (mod n1) /\ (x == a2) (mod n2)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`y:int`; `&(n1 * n2):int`] INT_CONG_NUM_EXISTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ; MULT_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  UNDISCH_TAC `(y:int == &a) (mod &n1)` THEN
  UNDISCH_TAC `(y:int == &b) (mod &n2)` THEN
  CONV_TAC INTEGER_RULE);;

let CHARACTER_TRIVIAL_GCD = prove
 (`!q c r1 r2.
     dirichlet_character q c /\ ~(q = 0) /\ r1 divides q /\ r2 divides q /\
     (!a. (a == 1) (mod r1) /\ coprime(a,q) ==> c a = Cx(&1)) /\
     (!a. (a == 1) (mod r2) /\ coprime(a,q) ==> c a = Cx(&1))
     ==> !a. (a == 1) (mod gcd(r1,r2)) /\ coprime(a,q) ==> c a = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r1 = 0) /\ ~(r2 = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_ZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `a:num`; `r1:num`; `r2:num`] CONG_CRT_STRONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(a == 1) (mod gcd(r1,r2))` THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `coprime(x:num,r1 * r2)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x == 1) (mod r1)`; `(x:num == a) (mod r2)`; `coprime(a:num,q)`;
      `(r2:num) divides q`] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `r1 * (r2:num)`; `q:num`] COPRIME_ADJUST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  ABBREV_TAC `b = x + k * r1 * (r2:num)` THEN
  SUBGOAL_THEN `(b == 1) (mod r1) /\ (b == a) (mod r2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    MAP_EVERY UNDISCH_TAC [`(x == 1) (mod r1)`; `(x:num == a) (mod r2)`] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(b:num,q)` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REWRITE_TAC[GSYM MULT_ASSOC]; ALL_TAC] THEN
  MP_TAC(SPECL [`b:num`; `1`; `q:num`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b':num`) THEN
  SUBGOAL_THEN `(a * b' == 1) (mod r2) /\ coprime(a * b',q) /\
                (a == (a * b') * b) (mod q)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(b:num == a) (mod r2)`; `(b * b' == 1) (mod q)`; `(r2:num) divides q`;
      `coprime(a:num,q)`] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->complex)(a * b') = Cx(&1) /\ c b = Cx(&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `r2:num`)) (concl th)));
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `r1:num`)) (concl th)))]
    THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->complex) a = c((a * b') * b)` SUBST1_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Primitive characters.                                                     *)
(* ------------------------------------------------------------------------- *)

let primitive_character = new_definition
 `primitive_character q (c:num->complex) <=>
    dirichlet_character q c /\
    !r. r divides q /\ ~(r = q)
        ==> ?a. (a == 1) (mod r) /\ coprime(a,q) /\ ~(c a = Cx(&1))`;;

let CHARACTER_TRIVIAL_INDUCED = prove
 (`!q c r c'. dirichlet_character q c /\ r divides q /\
              dirichlet_character r c' /\
              (!n. coprime(n,q) ==> c' n = c n)
              ==> !a. (a == 1) (mod r) /\ coprime(a,q) ==> c a = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->complex) a = c' a` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `(c':num->complex) 1` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]]);;

let CHARACTER_WELLDEF_MOD = prove
 (`!q c r. dirichlet_character q c /\ r divides q /\
           (!a. (a == 1) (mod r) /\ coprime(a,q) ==> c a = Cx(&1))
           ==> !m1 m2. (m1 == m2) (mod r) /\ coprime(m1,q) /\ coprime(m2,q)
                       ==> c m1 = c m2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m1:num`; `1`; `q:num`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `u:num`) THEN
  SUBGOAL_THEN `(u * m2 == 1) (mod r) /\ coprime(u * m2,q) /\
                (m2 == m1 * (u * m2)) (mod q)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(m1:num == m2) (mod r)`; `(m1 * u == 1) (mod q)`;
      `(r:num) divides q`; `coprime(m2:num,q)`] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->complex) m2 = c(m1 * (u * m2))` SUBST1_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC RAND_CONV [MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  SUBGOAL_THEN `(c:num->complex)(u * m2) = Cx(&1)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[COMPLEX_MUL_RID]]);;

let PRIMITIVE_CHARACTER_EXISTS = prove
 (`!q c. dirichlet_character q c /\ ~(q = 0)
         ==> ?r c'. r divides q /\ primitive_character r c' /\
                    !n. coprime(n,q) ==> c' n = c n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\r. r divides q /\
        !a. (a == 1) (mod r) /\ coprime(a,q) ==> (c:num->complex) a = Cx(&1)`
   num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `q:num` THEN REWRITE_TAC[DIVIDES_REFL] THEN
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `(c:num->complex) 1` THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG; DIRICHLET_CHARACTER_EQ_1];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_ZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `c:num->complex`; `r:num`] CHARACTER_WELLDEF_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "wd") THEN
  SUBGOAL_THEN
   `!n. coprime(n:num,r) ==> ?m:num. (m == n) (mod r) /\ coprime(m,q)`
  (LABEL_TAC "ex") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPECL [`n:num`; `r:num`; `q:num`]
      COPRIME_ADJUST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    EXISTS_TAC `n + k * (r:num)` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  ABBREV_TAC
   `c' = \n:num. if coprime(n,r)
             then (c:num->complex)(@m:num. (m == n) (mod r) /\ coprime(m,q))
             else Cx(&0)` THEN
  SUBGOAL_THEN
   `!n m. coprime(n,r) /\ (m == n) (mod r) /\ coprime(m,q)
          ==> (c':num->complex) n = c m`
  (LABEL_TAC "val") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c'" THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((@m:num. (m == n) (mod r) /\ coprime(m,q)) == n) (mod r) /\
      coprime((@m:num. (m == n) (mod r) /\ coprime(m,q)),q)`
    MP_TAC THENL
     [CONV_TAC SELECT_CONV THEN USE_THEN "ex" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `m0 = @m:num. (m == n) (mod r) /\ coprime(m,q)` THEN
    STRIP_TAC THEN
    USE_THEN "wd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(m0:num == n) (mod r)`; `(m:num == n) (mod r)`]
    THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~coprime(n,r) ==> (c':num->complex) n = Cx(&0)`
  (LABEL_TAC "zero") THENL
   [EXPAND_TAC "c'" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dirichlet_character r (c':num->complex)` ASSUME_TAC THENL
   [REWRITE_TAC[dirichlet_character] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `coprime(n:num,r)` THENL
       [USE_THEN "ex" (MP_TAC o SPEC `n:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        TRANS_TAC EQ_TRANS `(c:num->complex) m` THEN
        CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
        USE_THEN "val" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(m:num == n) (mod r)` THEN
        UNDISCH_TAC `coprime(n:num,r)` THEN CONV_TAC NUMBER_RULE;
        SUBGOAL_THEN `~coprime(n + r:num,r)` ASSUME_TAC THENL
         [UNDISCH_TAC `~coprime(n:num,r)` THEN
          MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
          CONV_TAC NUMBER_RULE;
          USE_THEN "zero" (fun th -> ASM_SIMP_TAC[th])]];
      X_GEN_TAC `n:num` THEN ASM_CASES_TAC `coprime(n:num,r)` THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "ex" (MP_TAC o SPEC `n:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        USE_THEN "val" (MP_TAC o SPECL [`n:num`; `m:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        MP_TAC(SPECL [`q:num`; `c:num->complex`; `m:num`]
          DIRICHLET_CHARACTER_EQ_0) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "zero" (fun th -> ASM_SIMP_TAC[th])];
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
      ASM_CASES_TAC `coprime(m:num,r) /\ coprime(n:num,r)` THENL
       [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
        USE_THEN "ex" (MP_TAC o SPEC `m:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC) THEN
        USE_THEN "ex" (MP_TAC o SPEC `n:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
        TRANS_TAC EQ_TRANS `(c:num->complex)(m1 * n1)` THEN CONJ_TAC THENL
         [USE_THEN "val" MATCH_MP_TAC THEN
          MAP_EVERY UNDISCH_TAC
           [`coprime(m:num,r)`; `coprime(n:num,r)`;
            `(m1:num == m) (mod r)`; `(n1:num == n) (mod r)`;
            `coprime(m1:num,q)`; `coprime(n1:num,q)`] THEN
          CONV_TAC NUMBER_RULE;
          ALL_TAC] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th])
        THEN BINOP_TAC THEN CONV_TAC SYM_CONV THEN
        USE_THEN "val" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `~coprime(m * n:num,r)` ASSUME_TAC THENL
         [UNDISCH_TAC `~(coprime(m:num,r) /\ coprime(n:num,r))` THEN
          MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
          CONV_TAC NUMBER_RULE;
          ALL_TAC] THEN
        USE_THEN "zero" (fun th -> ASM_SIMP_TAC[th]) THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
        USE_THEN "zero" (fun th -> ASM_SIMP_TAC[th]) THEN
        CONV_TAC COMPLEX_RING]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:num`; `c':num->complex`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "val" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONG_REFL] THEN
    UNDISCH_TAC `coprime(n:num,q)` THEN UNDISCH_TAC `(r:num) divides q` THEN
    CONV_TAC NUMBER_RULE] THEN
  ASM_REWRITE_TAC[primitive_character] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  USE_THEN "min" (MP_TAC o SPEC `s:num`) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ q ==> ~(p ==> ~q)`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `(s:num) <= r /\ ~(s = r) ==> s < r`) THEN
    ASM_MESON_TAC[DIVIDES_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVIDES_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN
  SUBGOAL_THEN `coprime(a:num,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `coprime(a:num,q)` THEN UNDISCH_TAC `(r:num) divides q` THEN
    CONV_TAC NUMBER_RULE;
    ASM_REWRITE_TAC[]] THEN
  USE_THEN "val" (MP_TAC o SPECL [`a:num`; `a:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONG_REFL]; DISCH_THEN SUBST1_TAC] THEN
  MESON_TAC[]);;

let PRIMITIVE_CHARACTER_MINIMAL = prove
 (`!q c r c' s.
        dirichlet_character q c /\ ~(q = 0) /\ r divides q /\
        primitive_character r c' /\ (!n. coprime(n,q) ==> c' n = c n) /\
        s divides r /\
        (!a. (a == 1) (mod s) /\ coprime(a,q) ==> c a = Cx(&1))
        ==> s = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:num` o CONJUNCT2 o
    GEN_REWRITE_RULE I [primitive_character]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:num`; `r:num`; `q:num`] COPRIME_ADJUST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `dirichlet_character r (c':num->complex)` ASSUME_TAC THENL
   [ASM_MESON_TAC[primitive_character]; ALL_TAC] THEN
  UNDISCH_TAC `~((c':num->complex) a = Cx(&1))` THEN REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `(c':num->complex)(a + k * r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `(c:num->complex)(a + k * r)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`(a:num == 1) (mod s)`; `(s:num) divides r`] THEN
  CONV_TAC NUMBER_RULE);;

let PRIMITIVE_CHARACTER_UNIQUE = prove
 (`!q c r1 c1 r2 c2.
        dirichlet_character q c /\ ~(q = 0) /\
        r1 divides q /\ primitive_character r1 c1 /\
        (!n. coprime(n,q) ==> c1 n = c n) /\
        r2 divides q /\ primitive_character r2 c2 /\
        (!n. coprime(n,q) ==> c2 n = c n)
        ==> r1 = r2 /\ c1 = c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `dirichlet_character r1 (c1:num->complex) /\
                dirichlet_character r2 (c2:num->complex)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[primitive_character]; ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `c:num->complex`; `r1:num`; `c1:num->complex`]
    CHARACTER_TRIVIAL_INDUCED) THEN
  MP_TAC(SPECL [`q:num`; `c:num->complex`; `r2:num`; `c2:num->complex`]
    CHARACTER_TRIVIAL_INDUCED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`q:num`; `c:num->complex`; `r1:num`; `r2:num`]
    CHARACTER_TRIVIAL_GCD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `gcd(r1:num,r2) = r1 /\ gcd(r1,r2) = r2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PRIMITIVE_CHARACTER_MINIMAL THEN
    MAP_EVERY EXISTS_TAC [`q:num`; `c:num->complex`] THENL
     [EXISTS_TAC `c1:num->complex`; EXISTS_TAC `c2:num->complex`] THEN
    ASM_REWRITE_TAC[GCD] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r1:num = r2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rhs o concl)) THEN
  ASM_CASES_TAC `coprime(n:num,r2)` THENL
   [MP_TAC(SPECL [`n:num`; `r2:num`; `q:num`] COPRIME_ADJUST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    SUBGOAL_THEN `(n + k * r2 == n:num) (mod r2)` ASSUME_TAC THENL
     [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(c1:num->complex)(n + k * r2)` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN
      EXISTS_TAC `r2:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(c2:num->complex)(n + k * r2)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN
      EXISTS_TAC `r2:num` THEN ASM_REWRITE_TAC[]];
    MP_TAC(SPECL [`r2:num`; `c1:num->complex`; `n:num`]
      DIRICHLET_CHARACTER_EQ_0) THEN
    MP_TAC(SPECL [`r2:num`; `c2:num->complex`; `n:num`]
      DIRICHLET_CHARACTER_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Nonprincipality and induced characters.                                   *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_CHARACTER_NONPRINCIPAL = prove
 (`!q c. primitive_character q c /\ ~(q = 1) ==> ~(c = chi_0 q)`,
  REWRITE_TAC[primitive_character] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
  ASM_REWRITE_TAC[NUMBER_RULE `1 divides n`; NUMBER_RULE `(a == b) (mod 1)`;
                  chi_0] THEN
  MESON_TAC[]);;

let DIRICHLET_CHARACTER_INDUCED = prove
 (`!q r c. dirichlet_character r c /\ r divides q
           ==> dirichlet_character q
                 (\n. if coprime(n,q) then c n else Cx(&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dirichlet_character] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    REWRITE_TAC[NUMBER_RULE `coprime(n + q:num,q) <=> coprime(n,q)`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(r:num) divides q` THEN
    CONV_TAC NUMBER_RULE;
    X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
    MAP_EVERY UNDISCH_TAC [`coprime(n:num,q)`; `(r:num) divides q`] THEN
    CONV_TAC NUMBER_RULE;
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[COPRIME_LMUL] THEN
    MAP_EVERY ASM_CASES_TAC [`coprime(m:num,q)`; `coprime(n:num,q)`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th])]);;

(* ------------------------------------------------------------------------- *)
(* Conjugate characters and orthogonality.                                   *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_CHARACTER_CNJ = prove
 (`!q c. primitive_character q c ==> primitive_character q (\n. cnj(c n))`,
  REWRITE_TAC[primitive_character] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[DIRICHLET_CHARACTER_CNJ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  SIMP_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CNJ_CX] THEN
  ASM_REWRITE_TAC[CNJ_INJ]);;

let VSUM_GRAM_EXPAND = prove
 (`!(f:A->B->complex) b s t.
     FINITE s /\ FINITE t
     ==> vsum s (\i. vsum t (\a. f i a * b a) *
                     cnj(vsum t (\a. f i a * b a))) =
         vsum t (\a. vsum t (\a'. (b a * cnj(b a')) *
                                  vsum s (\i. f i a * cnj(f i a'))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CNJ_VSUM; CNJ_MUL] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  MP_TAC(ISPECL
   [`\i a. vsum t (\a'. ((f:A->B->complex) i a * b a) *
                        cnj(f i a') * cnj(b a'))`;
    `s:A->bool`; `t:B->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:B` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`\i a'. ((f:A->B->complex) i a * b a) * cnj(f i a') * cnj(b a')`;
    `s:A->bool`; `t:B->bool`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a':B` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN BETA_TAC THEN
  CONV_TAC COMPLEX_RING);;

let DIRICHLET_CHARACTER_SUM_CNJ_MUL = prove
 (`!q a b. 1 <= q
           ==> vsum {c | dirichlet_character q c} (\c. cnj(c a) * c b) =
               if coprime(a,q) /\ (a == b) (mod q) then Cx(&(phi q))
               else Cx(&0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `coprime(a:num,q)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`q:num`; `c:num->complex`; `a:num`]
      DIRICHLET_CHARACTER_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]] THEN
  MP_TAC(SPECL [`a:num`; `1`; `q:num`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a':num`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {c | dirichlet_character q c} (\c. c(a' * b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~((c:num->complex) a = Cx(&0))` ASSUME_TAC THENL
     [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `(c:num->complex) a * c a' = Cx(&1)` MP_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
        DIRICHLET_CHARACTER_MUL th)]) THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
        DIRICHLET_CHARACTER_EQ_1 th)]) THEN
      MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`q:num`; `c:num->complex`; `a:num`]
      DIRICHLET_CHARACTER_MUL_CNJ) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((c:num->complex) a = Cx(&0))` THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `(a * a' == 1) (mod q)` THEN CONV_TAC NUMBER_RULE);;

let DIRICHLET_CHARACTER_PARSEVAL = prove
 (`!q (b:num->complex).
     1 <= q
     ==> sum {c | dirichlet_character q c}
             (\c. norm(vsum {a | a < q} (\a. cnj(c a) * b a)) pow 2) =
         &(phi q) * sum {a | a < q /\ coprime(a,q)} (\a. norm(b a) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CX_INJ] THEN
  REWRITE_TAC[GSYM VSUM_CX; CX_POW; GSYM COMPLEX_MUL_CNJ] THEN
  SIMP_TAC[VSUM_GRAM_EXPAND; FINITE_DIRICHLET_CHARACTERS;
           FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[CNJ_CNJ; DIRICHLET_CHARACTER_SUM_CNJ_MUL] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum {a | a < q}
      (\a. Cx(if coprime(a,q) then &(phi q) * norm((b:num->complex) a) pow 2
              else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {a' | a' < q}
        (\a'. if a' = a
              then Cx(if coprime(a,q)
                      then &(phi q) * norm((b:num->complex) a) pow 2
                      else &0)
              else vec 0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a':num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(a:num == a') (mod q) <=> a' = a` SUBST1_TAC THENL
       [ASM_SIMP_TAC[CONG; MOD_LT] THEN MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `a':num = a` THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
      COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
      REWRITE_TAC[COMPLEX_MUL_CNJ; CX_MUL; CX_POW] THEN
      CONV_TAC COMPLEX_RING;
      REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[VSUM_CX; CX_INJ] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    SUBGOAL_THEN
     `{a:num | a < q /\ coprime(a,q)} =
      {a | a IN {a | a < q} /\ coprime(a,q)}`
    SUBST1_TAC THENL [SET_TAC[]; REWRITE_TAC[SUM_RESTRICT_SET]]]);;

(* ------------------------------------------------------------------------- *)
(* Characters are bounded by 1.                                              *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_NORM_LE = prove
 (`!d c n. dirichlet_character d c ==> norm(c n) <= &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;
