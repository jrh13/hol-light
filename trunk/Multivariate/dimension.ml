(* ========================================================================= *)
(* Results connected with topological dimension.                             *)
(*                                                                           *)
(* At the moment this is just Brouwer's fixpoint theorem. The proof is from  *)
(* Kuhn: "some combinatorial lemmas in topology", IBM J. v4. (1960) p. 518   *)
(* See "http://www.research.ibm.com/journal/rd/045/ibmrd0405K.pdf".          *)
(*                                                                           *)
(* The script below is quite messy, but at least we avoid formalizing any    *)
(* topological machinery; we don't even use barycentric subdivision; this is *)
(* the big advantage of Kuhn's proof over the usual Sperner's lemma one.     *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Multivariate/polytope.ml";;

let BROUWER_COMPACTNESS_LEMMA = prove
 (`!f:real^M->real^N s.
        compact s /\ f continuous_on s /\ ~(?x. x IN s /\ (f x = vec 0))
        ==> ?d. &0 < d /\ !x. x IN s ==> d <= norm(f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`norm o (f:real^M->real^N)`; `s:real^M->bool`]
                CONTINUOUS_ATTAINS_INF) THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; o_ASSOC; CONTINUOUS_ON_LIFT_NORM] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[NORM_POS_LT]);;

let KUHN_LABELLING_LEMMA = prove
 (`!f:real^N->real^N P Q.
        (!x. P x ==> P (f x))
        ==> (!x. P x ==> (!i. Q i ==> &0 <= x$i /\ x$i <= &1))
            ==> ?l. (!x i. l x i <= 1) /\
                    (!x i. P x /\ Q i /\ (x$i = &0) ==> (l x i = 0)) /\
                    (!x i. P x /\ Q i /\ (x$i = &1) ==> (l x i = 1)) /\
                    (!x i. P x /\ Q i /\ (l x i = 0) ==> x$i <= f(x)$i) /\
                    (!x i. P x /\ Q i /\ (l x i = 1) ==> f(x)$i <= x$i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM;  GSYM SKOLEM_THM] THEN
  REWRITE_TAC[ARITH_RULE `n <= 1 <=> (n = 0) \/ (n = 1)`;
              RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2; ARITH_EQ] THEN
  MESON_TAC[REAL_ARITH
   `!x y. &0 <= x /\ x <= &1 /\ &0 <= y /\ y <= &1
          ==> ~(x = &1) /\ x <= y \/ ~(x = &0) /\ y <= x`]);;

(* ------------------------------------------------------------------------- *)
(* The key "counting" observation, somewhat abstracted.                      *)
(* ------------------------------------------------------------------------- *)

let KUHN_COUNTING_LEMMA = prove
 (`!face:F->S->bool faces simplices comp comp' bnd.
        FINITE faces /\ FINITE simplices /\
        (!f. f IN faces /\ bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 1)) /\
        (!f. f IN faces /\ ~bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 2)) /\
        (!s. s IN simplices /\ comp s
             ==> (CARD {f | f IN faces /\ face f s /\ comp' f} = 1)) /\
        (!s. s IN simplices /\ ~comp s
             ==> (CARD {f | f IN faces /\ face f s /\ comp' f} = 0) \/
                 (CARD {f | f IN faces /\ face f s /\ comp' f} = 2))
        ==> ODD(CARD {f | f IN faces /\ comp' f /\ bnd f})
            ==> ODD(CARD {s | s IN simplices /\ comp s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum simplices
     (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum simplices
     (\s. &(CARD {f | f IN {f | f IN faces /\ comp' f /\ bnd f} /\
                      face f s})) +
    sum simplices
     (\s. &(CARD {f | f IN {f | f IN faces /\ comp' f /\ ~(bnd f)} /\
                      face f s}))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN GEN_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s f. (face:F->S->bool) f s`; `simplices:S->bool`;
    `{f:F | f IN faces /\ comp' f /\ bnd f}`; `1`] SUM_MULTICOUNT) THEN
  MP_TAC(ISPECL
   [`\s f. (face:F->S->bool) f s`; `simplices:S->bool`;
    `{f:F | f IN faces /\ comp' f /\ ~(bnd f)}`; `2`] SUM_MULTICOUNT) THEN
  REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SIMP_TAC[IN_ELIM_THM];
    DISCH_THEN SUBST1_TAC]) THEN
  SUBGOAL_THEN
   `sum simplices
     (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum {s | s IN simplices /\ comp s}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) +
    sum {s | s IN simplices /\ ~(comp s)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f}))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_UNION] THEN
    CONJ_TAC THEN GEN_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {s | s IN simplices /\ comp s}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum {s | s IN simplices /\ comp s} (\s. &1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {s | s IN simplices /\ ~(comp s)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
    sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = 0)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) +
    sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = 2)}
        (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f}))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[ARITH_RULE `~(2 = 0)`];
      ALL_TAC] THEN
    X_GEN_TAC `s:S` THEN UNDISCH_TAC
     `!s:S. s IN simplices /\ ~comp s
            ==> (CARD {f:F | f IN faces /\ face f s /\ comp' f} = 0) \/
                (CARD {f | f IN faces /\ face f s /\ comp' f} = 2)` THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = n)}
            (\s:S. &(CARD {f:F | f IN faces /\ face f s /\ comp' f})) =
        sum {s | s IN simplices /\ ~(comp s) /\
             (CARD {f | f IN faces /\ face f s /\ comp' f} = n)}
            (\s:S. &n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_0] THEN ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `ODD`) THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH_ODD; ODD]);;

(* ------------------------------------------------------------------------- *)
(* The odd/even result for faces of complete vertices, generalized.          *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_1_EXISTS = prove
 (`!s. s HAS_SIZE 1 <=> ?!x. x IN s`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[EXTENSION; IN_SING] THEN MESON_TAC[]);;

let HAS_SIZE_2_EXISTS = prove
 (`!s. s HAS_SIZE 2 <=> ?x y. ~(x = y) /\ !z. z IN s <=> (z = x) \/ (z = y)`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let IMAGE_LEMMA_0 = prove
 (`!f:A->B s n.
      {a | a IN s /\ (IMAGE f (s DELETE a) = t DELETE b)} HAS_SIZE n
      ==> {s' | ?a. a IN s /\ (s' = s DELETE a) /\ (IMAGE f s' = t DELETE b)}
          HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{s' | ?a. a IN s /\ (s' = s DELETE a) /\ (IMAGE f s' = t DELETE b)} =
    IMAGE (\a. s DELETE a)
          {a | a IN s /\ (IMAGE (f:A->B) (s DELETE a) = t DELETE b)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[]]);;

let IMAGE_LEMMA_1 = prove
 (`!f:A->B s t b.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\
        (IMAGE f s = t) /\ b IN t
        ==> (CARD {s' | ?a. a IN s /\ (s' = s DELETE a) /\
                            (IMAGE f s' = t DELETE b)} = 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  MATCH_MP_TAC IMAGE_LEMMA_0 THEN REWRITE_TAC[HAS_SIZE_1_EXISTS] THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN s /\ ((f:A->B) x = f y) ==> (x = y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[IMAGE_IMP_INJECTIVE_GEN]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; IN_ELIM_THM] THEN CONJ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_IMAGE] THENL
   [DISCH_THEN(fun th -> MP_TAC(SPEC `b:B` th) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[]]);;

let IMAGE_LEMMA_2 = prove
 (`!f:A->B s t b.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\
        (IMAGE f s) SUBSET t /\ ~(IMAGE f s = t) /\ b IN t
        ==> (CARD {s' | ?a. a IN s /\ (s' = s DELETE a) /\
                            (IMAGE f s' = t DELETE b)} = 0) \/
            (CARD {s' | ?a. a IN s /\ (s' = s DELETE a) /\
                            (IMAGE f s' = t DELETE b)} = 2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `{a | a IN s /\ (IMAGE (f:A->B) (s DELETE a) = t DELETE b)} = {}`
  THENL [DISJ1_TAC; DISJ2_TAC] THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  MATCH_MP_TAC IMAGE_LEMMA_0 THEN
  ASM_REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_2_EXISTS] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a1:A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) a1 IN (t DELETE b)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN
    ASM_MESON_TAC[SUBSET; IN_IMAGE; INSERT_DELETE; IMAGE_CLAUSES];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  DISCH_THEN(MP_TAC o SPEC `(f:A->B) a1`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a2:A` THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x y. x IN (s DELETE a1) /\ y IN (s DELETE a1) /\ ((f:A->B) x = f y)
          ==> (x = y)`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_IMP_INJECTIVE_GEN THEN EXISTS_TAC `t DELETE (b:B)` THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE];
    REWRITE_TAC[IN_DELETE] THEN DISCH_TAC] THEN
  X_GEN_TAC `a:A` THEN ASM_CASES_TAC `a:A = a1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:A) IN s` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(f:A->B) a = f a1` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[IN_DELETE]] THEN
  FIRST_X_ASSUM(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM t]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `(f:A->B) a`); ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combine this with the basic counting lemma.                               *)
(* ------------------------------------------------------------------------- *)

let KUHN_COMPLETE_LEMMA = prove
 (`!face:(A->bool)->(A->bool)->bool simplices rl bnd n.
        FINITE simplices /\
        (!f s. face f s <=> ?a. a IN s /\ (f = s DELETE a)) /\
        (!s. s IN simplices ==> s HAS_SIZE (n + 2) /\
                                (IMAGE rl s) SUBSET 0..n+1) /\
        (!f. f IN {f | ?s. s IN simplices /\ face f s} /\ bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 1)) /\
        (!f. f IN {f | ?s. s IN simplices /\ face f s} /\ ~bnd f
             ==> (CARD {s | s IN simplices /\ face f s} = 2))
        ==> ODD(CARD {f | f IN {f | ?s. s IN simplices /\ face f s} /\
                          (IMAGE rl f = 0..n) /\ bnd f})
            ==> ODD(CARD {s | s IN simplices /\ (IMAGE rl s = 0..n+1)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P f:A->bool s.
       s IN simplices
       ==> (f IN {f | ?s. s IN simplices /\ (?a. a IN s /\ (f = s DELETE a))} /\
            (?a. a IN s /\ (f = s DELETE a)) /\ P f <=>
           (?a. a IN s /\ (f = s DELETE a) /\ P f))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `0..n = (0..n+1) DELETE (n+1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_DELETE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC KUHN_COUNTING_LEMMA THEN
  EXISTS_TAC `face:(A->bool)->(A->bool)->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_SIMP_TAC[] THENL
   [SUBGOAL_THEN
     `{f:A->bool | ?s. s IN simplices /\ (?a. a IN s /\ (f = s DELETE a))} =
      UNIONS (IMAGE (\s. {f | ?a. a IN s /\ (f = s DELETE a)}) simplices)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:A->bool` THEN
    DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POWERSET THEN ASM_MESON_TAC[HAS_SIZE];
      SIMP_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_DELETE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_LEMMA_1;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_LEMMA_2] THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; LE_REFL] THEN
  REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `((n + 1) + 1) - 0 = n + 2`] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* We use the following notion of ordering rather than pointwise indexing.   *)
(* ------------------------------------------------------------------------- *)

let kle = new_definition
  `kle n x y <=> ?k. k SUBSET 1..n /\
                     (!j. y(j) = x(j) + (if j IN k then 1 else 0))`;;

let KLE_REFL = prove
 (`!n x. kle n x x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kle] THEN EXISTS_TAC `{}:num->bool` THEN
  REWRITE_TAC[ADD_CLAUSES; NOT_IN_EMPTY; EMPTY_SUBSET]);;

let KLE_ANTISYM = prove
 (`!n x y. kle n x y /\ kle n y x <=> (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [REWRITE_TAC[kle]; MESON_TAC[KLE_REFL]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[ARITH_RULE `(x = (x + a) + b) ==> (x = x + a:num)`]);;

let POINTWISE_MINIMAL,POINTWISE_MAXIMAL = (CONJ_PAIR o prove)
 (`(!s:(num->num)->bool.
        FINITE s
        ==> ~(s = {}) /\
            (!x y. x IN s /\ y IN s
                   ==> (!j. x(j) <= y(j)) \/ (!j. y(j) <= x(j)))
            ==> ?a. a IN s /\ !x. x IN s ==> !j. a(j) <= x(j)) /\
   (!s:(num->num)->bool.
        FINITE s
        ==> ~(s = {}) /\
            (!x y. x IN s /\ y IN s
                   ==> (!j. x(j) <= y(j)) \/ (!j. y(j) <= x(j)))
            ==> ?a. a IN s /\ !x. x IN s ==> !j. x(j) <= a(j))`,
  CONJ_TAC THEN
  (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
   MAP_EVERY X_GEN_TAC [`a:num->num`; `s:(num->num)->bool`] THEN
   ASM_CASES_TAC `s:(num->num)->bool = {}` THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[IN_SING] THEN MESON_TAC[LE_REFL]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:num->num`; `b:num->num`]) THEN
   ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[LE_CASES; LE_TRANS]));;

let KLE_IMP_POINTWISE = prove
 (`!n x y. kle n x y ==> !j. x(j) <= y(j)`,
  REWRITE_TAC[kle] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_ADD]);;

let POINTWISE_ANTISYM = prove
 (`!x y:num->num. (!j. x(j) <= y(j)) /\ (!j. y(j) <= x(j)) <=> (x = y)`,
  REWRITE_TAC[AND_FORALL_THM; FUN_EQ_THM; LE_ANTISYM]);;

let KLE_TRANS = prove
 (`!x y z n. kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x)
             ==> kle n x z`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x:num->num = z` (fun th -> REWRITE_TAC[KLE_REFL; th]) THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM LE_ANTISYM; FORALL_AND_THM] THEN
  ASM_MESON_TAC[KLE_IMP_POINTWISE; LE_TRANS]);;

let KLE_STRICT = prove
 (`!n x y. kle n x y /\ ~(x = y)
           ==> (!j. x(j) <= y(j)) /\ (?k. 1 <= k /\ k <= n /\ x(k) < y(k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kle] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->bool` MP_TAC) THEN
  ASM_CASES_TAC `k:num->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; ADD_CLAUSES; GSYM FUN_EQ_THM; ETA_AX];
    STRIP_TAC THEN ASM_REWRITE_TAC[LE_ADD] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
    ASM_MESON_TAC[SUBSET; IN_NUMSEG]]);;

let KLE_MINIMAL = prove
 (`!s n. FINITE s /\ ~(s = {}) /\
         (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)
         ==> ?a. a IN s /\ !x. x IN s ==> kle n a x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:num->num. a IN s /\ !x. x IN s ==> !j. a(j) <= x(j)`
  MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] POINTWISE_MINIMAL); ALL_TAC] THEN
  ASM_MESON_TAC[POINTWISE_ANTISYM; KLE_IMP_POINTWISE]);;

let KLE_MAXIMAL = prove
 (`!s n. FINITE s /\ ~(s = {}) /\
         (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)
         ==> ?a. a IN s /\ !x. x IN s ==> kle n x a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:num->num. a IN s /\ !x. x IN s ==> !j. x(j) <= a(j)`
  MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] POINTWISE_MAXIMAL); ALL_TAC] THEN
  ASM_MESON_TAC[POINTWISE_ANTISYM; KLE_IMP_POINTWISE]);;

let KLE_STRICT_SET = prove
 (`!n x y. kle n x y /\ ~(x = y) ==> 1 <= CARD {k | k IN 1..n /\ x(k) < y(k)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP KLE_STRICT) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {i:num}` THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; ARITH; NOT_IN_EMPTY];
    MATCH_MP_TAC CARD_SUBSET THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    SIMP_TAC[IN_ELIM_THM; IN_NUMSEG; SUBSET; IN_SING] THEN ASM_MESON_TAC[]]);;

let KLE_RANGE_COMBINE = prove
 (`!n x y m1 m2.
        kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x) /\
        m1 <= CARD {k | k IN 1..n /\ x(k) < y(k)} /\
        m2 <= CARD {k | k IN 1..n /\ y(k) < z(k)}
        ==> kle n x z /\ m1 + m2 <= CARD {k | k IN 1..n /\ x(k) < z(k)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KLE_TRANS]; DISCH_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {k | k IN 1..n /\ x(k):num < y(k)} +
              CARD {k | k IN 1..n /\ y(k) < z(k)}` THEN
  ASM_SIMP_TAC[LE_ADD2] THEN MATCH_MP_TAC EQ_IMP_LE THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN
  SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[KLE_IMP_POINTWISE; ARITH_RULE
     `x <= y:num /\ y <= z ==> (x < y \/ y < z <=> x < z)`]] THEN
  X_GEN_TAC `i:num` THEN UNDISCH_TAC `kle n x z` THEN
  REWRITE_TAC[kle] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i IN 1..n` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `d <= 1 ==> ~(a < x /\ x < a + d)`) THEN
  COND_CASES_TAC THEN REWRITE_TAC[ARITH]);;

let KLE_RANGE_COMBINE_L = prove
 (`!n x y m.
        kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x) /\
        m <= CARD {k | k IN 1..n /\ y(k) < z(k)}
        ==> kle n x z /\ m <= CARD {k | k IN 1..n /\ x(k) < z(k)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:num->num = y` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `kle n x z /\ 1 + m <= CARD {k | k IN 1 .. n /\ x k < z k}`
   (fun th -> MESON_TAC[th; ARITH_RULE `1 + m <= x ==> m <= x`]) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `y:num->num` THEN
  ASM_SIMP_TAC[KLE_STRICT_SET]);;

let KLE_RANGE_COMBINE_R = prove
 (`!n x y m.
        kle n x y /\ kle n y z /\ (kle n x z \/ kle n z x) /\
        m <= CARD {k | k IN 1..n /\ x(k) < y(k)}
        ==> kle n x z /\ m <= CARD {k | k IN 1..n /\ x(k) < z(k)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y:num->num = z` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `kle n x z /\ m + 1 <= CARD {k | k IN 1 .. n /\ x k < z k}`
   (fun th -> MESON_TAC[th; ARITH_RULE `m + 1 <= x ==> m <= x`]) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `y:num->num` THEN
  ASM_SIMP_TAC[KLE_STRICT_SET]);;

let KLE_RANGE_INDUCT = prove
 (`!n m s. s HAS_SIZE (SUC m)
           ==> (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)
               ==> ?x y. x IN s /\ y IN s /\ kle n x y /\
                         m <= CARD {k | k IN 1..n /\ x(k) < y(k)}`,
  GEN_TAC THEN INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ARITH; LE_0] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN MESON_TAC[IN_SING; KLE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `s:(num->num)->bool` THEN
  ONCE_REWRITE_TAC[HAS_SIZE_SUC] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num->num)->bool`; `n:num`] KLE_MINIMAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE_SUC; HAS_SIZE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:num->num)`) THEN
  REPEAT(ANTS_TAC THENL [ASM_MESON_TAC[IN_DELETE]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC m = 1 + m`] THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `x:num->num` THEN
  ASM_SIMP_TAC[KLE_STRICT_SET]);;

let KLE_SUC = prove
 (`!n x y. kle n x y ==> kle (n + 1) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kle] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `k <= n ==> k <= n + 1`]);;

let KLE_TRANS_1 = prove
 (`!n x y. kle n x y ==> !j. x j <= y j /\ y j <= x j + 1`,
  SIMP_TAC[kle; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ARITH_TAC);;

let KLE_TRANS_2 = prove
 (`!a b c. kle n a b /\ kle n b c /\ (!j. c j <= a j + 1)
           ==> kle n a c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[kle] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk1:num->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `kk2:num->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    EXISTS_TAC `(kk1:num->bool) UNION kk2` THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[UNION_SUBSET; IN_UNION] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `(i:num) IN kk1` THEN ASM_CASES_TAC `(i:num) IN kk2` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let KLE_BETWEEN_R = prove
 (`!a b c x. kle n a b /\ kle n b c /\ kle n a x /\ kle n c x
             ==> kle n b x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KLE_TRANS_2 THEN
  EXISTS_TAC `c:num->num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[KLE_TRANS_1; ARITH_RULE
   `x <= c + 1 /\ c <= b ==> x <= b + 1`]);;

let KLE_BETWEEN_L = prove
 (`!a b c x. kle n a b /\ kle n b c /\ kle n x a /\ kle n x c
             ==> kle n x b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KLE_TRANS_2 THEN
  EXISTS_TAC `a:num->num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[KLE_TRANS_1; ARITH_RULE
   `c <= x + 1 /\ b <= c ==> b <= x + 1`]);;

let KLE_ADJACENT = prove
 (`!a b x k.
        1 <= k /\ k <= n /\ (!j. b(j) = if j = k then a(j) + 1 else a(j)) /\
        kle n a x /\ kle n x b
        ==> (x = a) \/ (x = b)`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; IMP_IMP; AND_FORALL_THM] THEN
  ASM_CASES_TAC `(x:num->num) k = a k` THENL
   [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th);
    DISCH_THEN(fun th -> DISJ2_TAC THEN MP_TAC th)] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_ANTISYM] THEN
  ASM_MESON_TAC[ARITH_RULE
   `a <= x /\ x <= a + 1 /\ ~(x = a) ==> (x = a + 1)`]);;

(* ------------------------------------------------------------------------- *)
(* Kuhn's notion of a simplex (my reformulation to avoid so much indexing).  *)
(* ------------------------------------------------------------------------- *)

let ksimplex = new_definition
 `ksimplex p n s <=>
        s HAS_SIZE (n + 1) /\
        (!x j. x IN s ==> x(j) <= p) /\
        (!x j. x IN s /\ ~(1 <= j /\ j <= n) ==> (x j = p)) /\
        (!x y. x IN s /\ y IN s ==> kle n x y \/ kle n y x)`;;

let KSIMPLEX_EXTREMA = prove
 (`!p n s.
        ksimplex p n s
        ==> ?a b. a IN s /\ b IN s /\
                  (!x. x IN s ==> kle n a x /\ kle n x b) /\
                  (!i. b(i) = if 1 <= i /\ i <= n then a(i) + 1 else a(i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ksimplex] THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 0 <=> F`; GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
    CONV_TAC(LAND_CONV(LAND_CONV HAS_SIZE_CONV)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[KLE_REFL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num->num)->bool`; `n:num`] KLE_MINIMAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE; HAS_SIZE_SUC; ADD1]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num->num)->bool`; `n:num`] KLE_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE; HAS_SIZE_SUC; ADD1]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `n:num`; `s:(num->num)->bool`] KLE_RANGE_INDUCT) THEN
  ASM_REWRITE_TAC[ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num` (X_CHOOSE_THEN `d:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{k | k IN 1 .. n /\ a k :num < b k} = 1..n` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_LE THEN
    ASM_REWRITE_TAC[CARD_NUMSEG; ADD_SUB; FINITE_NUMSEG; SUBSET_RESTRICT] THEN
    SUBGOAL_THEN `kle n a b /\ n <= CARD {k | k IN 1..n /\ a(k) < b(k)}`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_L THEN EXISTS_TAC `c:num->num` THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `kle n c b /\ n <= CARD {k | k IN 1 .. n /\ c k < b k}`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_R THEN EXISTS_TAC `d:num->num` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `kle n a b` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [kle]) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
  ASM_MESON_TAC[SUBSET; IN_NUMSEG]);;

let KSIMPLEX_EXTREMA_STRONG = prove
 (`!p n s.
        ksimplex p n s /\ ~(n = 0)
        ==> ?a b. a IN s /\ b IN s /\ ~(a = b) /\
                  (!x. x IN s ==> kle n a x /\ kle n x b) /\
                  (!i. b(i) = if 1 <= i /\ i <= n then a(i) + 1 else a(i))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP KSIMPLEX_EXTREMA) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
  ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN ARITH_TAC);;

let KSIMPLEX_SUCCESSOR = prove
 (`!a p n s.
        ksimplex p n s /\ a IN s
        ==> (!x. x IN s ==> kle n x a) \/
            (?y. y IN s /\ ?k. 1 <= k /\ k <= n /\
                               !j. y(j) = if j = k then a(j) + 1 else a(j))`,
  REWRITE_TAC[ksimplex] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`{x | x IN s /\ ~kle n x a}`; `n:num`] KLE_MINIMAL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= CARD {k | k IN 1..n /\ a(k):num < b(k)}` MP_TAC THENL
   [MATCH_MP_TAC KLE_STRICT_SET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP (ARITH_RULE
   `1 <= n ==> (n = 1) \/ 2 <= n`))
  THENL
   [DISCH_TAC THEN
    MP_TAC(HAS_SIZE_CONV `{k | k IN 1 .. n /\ a k :num < b k} HAS_SIZE 1`) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_NUMSEG] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `kle n a b` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [kle]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    ASM_MESON_TAC[SUBSET; IN_NUMSEG; ARITH_RULE `~(a + 1 = a)`;
                  ARITH_RULE `a < a + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ ~(kle n x a)})`;
                `{x | x IN s /\ ~(kle n x a)}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num`
   (X_CHOOSE_THEN `d:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ kle n x a})`;
                `{x | x IN s /\ kle n x a}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[KLE_REFL]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->num`
    (X_CHOOSE_THEN `f:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `kle n e d /\ n + 1 <= CARD {k | k IN 1..n /\ e(k) < d(k)}`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 <= x) <=> x <= n`] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..n)` THEN
    SIMP_TAC[CARD_SUBSET; SUBSET_RESTRICT; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[CARD_NUMSEG; ADD_SUB; LE_REFL]] THEN
  SUBGOAL_THEN
   `(CARD {x | x IN s /\ kle n x a} - 1) +
    2 + (CARD {x | x IN s /\ ~kle n x a} - 1) = n + 1`
   (SUBST1_TAC o SYM)
  THENL
   [MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ ~(b = 0) /\ (a + b = n + 1)
       ==> ((a - 1) + 2 + (b - 1) = n + 1)`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT (CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `a:num->num` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN CONJ_TAC THENL
   [W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n e a`,w))
     (fun th -> REWRITE_TAC[th])) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_R THEN EXISTS_TAC `f:num->num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`];
    ALL_TAC] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n a d`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `b:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n b d`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE_L THEN EXISTS_TAC `c:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN ASM_MESON_TAC[KLE_TRANS]);;

let KSIMPLEX_PREDECESSOR = prove
 (`!a p n s.
        ksimplex p n s /\ a IN s
        ==> (!x. x IN s ==> kle n a x) \/
            (?y. y IN s /\ ?k. 1 <= k /\ k <= n /\
                               !j. a(j) = if j = k then y(j) + 1 else y(j))`,
  REWRITE_TAC[ksimplex] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`{x | x IN s /\ ~kle n a x}`; `n:num`] KLE_MAXIMAL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= CARD {k | k IN 1..n /\ b(k):num < a(k)}` MP_TAC THENL
   [MATCH_MP_TAC KLE_STRICT_SET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP (ARITH_RULE
   `1 <= n ==> (n = 1) \/ 2 <= n`))
  THENL
   [DISCH_TAC THEN
    MP_TAC(HAS_SIZE_CONV `{k | k IN 1 .. n /\ b k :num < a k} HAS_SIZE 1`) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_NUMSEG] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [MESON_TAC[th]; MP_TAC th]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `kle n b a` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [kle]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_REFL] THEN
    ASM_MESON_TAC[SUBSET; IN_NUMSEG; ARITH_RULE `~(a + 1 = a)`;
                  ARITH_RULE `a < a + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ ~(kle n a x)})`;
                `{x | x IN s /\ ~(kle n a x)}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num`
   (X_CHOOSE_THEN `c:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `PRE(CARD {x | x IN s /\ kle n a x})`;
                `{x | x IN s /\ kle n a x}`] KLE_RANGE_INDUCT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; CARD_EQ_0; GSYM MEMBER_NOT_EMPTY;
    ARITH_RULE `(n = SUC(PRE n)) <=> ~(n = 0)`] THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[KLE_REFL]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num`
    (X_CHOOSE_THEN `e:num->num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `kle n d e /\ n + 1 <= CARD {k | k IN 1..n /\ d(k) < e(k)}`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 <= x) <=> x <= n`] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..n)` THEN
    SIMP_TAC[CARD_SUBSET; SUBSET_RESTRICT; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[CARD_NUMSEG; ADD_SUB; LE_REFL]] THEN
  SUBGOAL_THEN
   `((CARD {x | x IN s /\ ~kle n a x} - 1) + 2) +
    (CARD {x | x IN s /\ kle n a x} - 1) = n + 1`
   (SUBST1_TAC o SYM)
  THENL
   [MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ ~(b = 0) /\ (a + b = n + 1)
       ==> (((b - 1) + 2) + (a - 1) = n + 1)`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT (CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `a:num->num` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n a e`,w))
     (fun th -> REWRITE_TAC[th])) THEN
    MATCH_MP_TAC KLE_RANGE_COMBINE_L THEN EXISTS_TAC `f:num->num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`]] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n d a`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE THEN EXISTS_TAC `b:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_TRANS]; ALL_TAC] THEN
  W(fun(asl,w) -> SUBGOAL_THEN(mk_conj(`kle n d b`,w))
     (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC KLE_RANGE_COMBINE_R THEN EXISTS_TAC `c:num->num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - 1 = PRE k`] THEN ASM_MESON_TAC[KLE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* The lemmas about simplices that we need.                                  *)
(* ------------------------------------------------------------------------- *)

let FINITE_SIMPLICES = prove
 (`!p n. FINITE {s | ksimplex p n s}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s | s SUBSET {f | (!i. i IN 1..n ==> f(i) IN 0..p) /\
                                 (!i. ~(i IN 1..n) ==> (f(i) = p))}}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_FUNSPACE; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; ksimplex] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0]);;

let SIMPLEX_TOP_FACE = prove
 (`0 < p /\
   (!x. x IN f ==> (x(n + 1) = p))
   ==> ((?s a. ksimplex p (n + 1) s /\ a IN s /\ (f = s DELETE a)) <=>
        ksimplex p n f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[ksimplex; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(s:(num->num)->bool) HAS_SIZE ((n + 1) + 1)` THEN
      SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_DELETE] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN X_GEN_TAC `j:num` THEN
      ONCE_REWRITE_TAC[ARITH_RULE
       `(1 <= j /\ j <= n) <=> (1 <= j /\ j <= n + 1) /\ ~(j = (n + 1))`] THEN
      ASM_MESON_TAC[IN_DELETE];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `kle (n + 1) x y \/ kle (n + 1) y x` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
      (REWRITE_TAC[kle] THEN
       MATCH_MP_TAC MONO_EXISTS THEN
       REWRITE_TAC[GSYM ADD1; NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`] THEN
       X_GEN_TAC `k:num->bool` THEN SIMP_TAC[] THEN
       REWRITE_TAC[SUBSET; IN_INSERT] THEN
       ASM_CASES_TAC `(SUC n) IN k` THENL
        [ALL_TAC; ASM_MESON_TAC[]] THEN
       DISCH_THEN(MP_TAC o SPEC `n + 1` o CONJUNCT2) THEN
       ASM_REWRITE_TAC[GSYM ADD1] THEN
       ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
       MATCH_MP_TAC(ARITH_RULE `(x = p) /\ (y = p) ==> ~(x = SUC y)`) THEN
       CONJ_TAC THEN ASM_MESON_TAC[ADD1; IN_DELETE])];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP KSIMPLEX_EXTREMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->num` (X_CHOOSE_THEN `b:num->num`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = \i. if i = (n + 1) then p - 1 else a(i)` THEN
  MAP_EVERY EXISTS_TAC [`(c:num->num) INSERT f`; `c:num->num`] THEN
  REWRITE_TAC[IN_INSERT; DELETE_INSERT] THEN
  SUBGOAL_THEN `~((c:num->num) IN f)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `!x:num->num. x IN f ==> (x (n + 1) = p)` THEN
    DISCH_THEN(MP_TAC o SPEC `c:num->num`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[] THEN UNDISCH_TAC `0 < p` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; UNDISCH_TAC `~((c:num->num) IN f)` THEN SET_TAC[]] THEN
  UNDISCH_TAC `ksimplex p n f` THEN REWRITE_TAC[ksimplex] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [SIMP_TAC[HAS_SIZE; FINITE_RULES; CARD_CLAUSES] THEN ASM_REWRITE_TAC[ADD1];
    EXPAND_TAC "c" THEN REWRITE_TAC[IN_INSERT] THEN
    SIMP_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
    ASM_MESON_TAC[ARITH_RULE `p - 1 <= p`];
    EXPAND_TAC "c" THEN REWRITE_TAC[IN_INSERT; TAUT
      `(a \/ b) /\ c ==> d <=> (a /\ c ==> d) /\ (b /\ c ==> d)`] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN CONJ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC); ALL_TAC] THEN
    ASM_MESON_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`;
                  ARITH_RULE `j <= n ==> j <= n + 1`];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  SUBGOAL_THEN `!x. x IN f ==> kle (n + 1) c x`
    (fun th -> ASM_MESON_TAC[th; KLE_SUC; KLE_REFL]) THEN
  X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `kle (n + 1) a x` MP_TAC THENL
   [ASM_MESON_TAC[KLE_SUC]; ALL_TAC] THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[kle] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(n + 1) INSERT k` THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG] THEN
  ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_INSERT] THEN
  ASM_CASES_TAC `j = n + 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n + 1 IN k)`
   (fun th -> ASM_MESON_TAC[th; ARITH_RULE `0 < p ==> (p = (p - 1) + 1)`]) THEN
  DISCH_TAC THEN UNDISCH_TAC `!x:num->num. x IN f ==> (x (n + 1) = p)` THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x:num->num` th) THEN
                       MP_TAC(SPEC `a:num->num` th)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[ARITH_RULE `~(p + 1 = p)`]);;

let KSIMPLEX_FIX_PLANE = prove
 (`!p q n j s a a0 a1.
        ksimplex p n s /\ a IN s /\
        1 <= j /\ j <= n /\ (!x. x IN (s DELETE a) ==> (x j = q)) /\
        a0 IN s /\ a1 IN s /\
        (!i. a1 i = (if 1 <= i /\ i <= n then a0 i + 1 else a0 i))
        ==> (a = a0) \/ (a = a1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN STRIP_TAC THEN
  UNDISCH_TAC `!x:num->num. x IN s DELETE a ==> (x j = q)` THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `a0:num->num` th) THEN MP_TAC(SPEC `a1:num->num` th)) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC);;

let KSIMPLEX_FIX_PLANE_0 = prove
 (`!p n j s a a0 a1.
        ksimplex p n s /\ a IN s /\
        1 <= j /\ j <= n /\ (!x. x IN (s DELETE a) ==> (x j = 0)) /\
        a0 IN s /\ a1 IN s /\
        (!i. a1 i = (if 1 <= i /\ i <= n then a0 i + 1 else a0 i))
        ==> (a = a1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a = a0) \/ (a = a1:num->num)` MP_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN
    MAP_EVERY EXISTS_TAC
     [`p:num`; `0`; `n:num`; `j:num`; `s:(num->num)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a0:num->num = a1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~a ==> (a \/ b ==> b)`) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a1:num->num`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC);;

let KSIMPLEX_FIX_PLANE_P = prove
 (`!p n j s a a0 a1.
        ksimplex p n s /\ a IN s /\
        1 <= j /\ j <= n /\ (!x. x IN (s DELETE a) ==> (x j = p)) /\
        a0 IN s /\ a1 IN s /\
        (!i. a1 i = (if 1 <= i /\ i <= n then a0 i + 1 else a0 i))
        ==> (a = a0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a = a0) \/ (a = a1:num->num)` MP_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN
    MAP_EVERY EXISTS_TAC
     [`p:num`; `p:num`; `n:num`; `j:num`; `s:(num->num)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a0:num->num = a1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~b ==> (a \/ b ==> a)`) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a0:num->num`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ksimplex]) THEN
  DISCH_THEN(MP_TAC o SPEC `a1:num->num` o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let KSIMPLEX_REPLACE_0 = prove
 (`ksimplex p n s /\ a IN s /\ ~(n = 0) /\
   (?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = 0))
   ==> (CARD
         {s' | ksimplex p n s' /\ ?b. b IN s' /\ (s' DELETE b = s DELETE a)} =
        1)`,
  let lemma = prove
   (`!a a'. (s' DELETE a' = s DELETE a) /\ (a' = a) /\ a' IN s' /\ a IN s
            ==> (s' = s)`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  REWRITE_TAC[HAS_SIZE_1_EXISTS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!s' a'. ksimplex p n s' /\ a' IN s' /\ (s' DELETE a' = s DELETE a)
            ==> (s' = s)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` (X_CHOOSE_THEN `a1:num->num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:num->num` (X_CHOOSE_THEN `b1:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a:num->num = a1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_0 THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s:(num->num)->bool`; `a0:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a':num->num = b1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_0 THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s':(num->num)->bool`; `b0:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`a1:num->num`; `b1:num->num`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b0:num->num = a0` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM KLE_ANTISYM] THEN ASM_MESON_TAC[IN_DELETE];
    ASM_REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]]);;

let KSIMPLEX_REPLACE_1 = prove
 (`ksimplex p n s /\ a IN s /\ ~(n = 0) /\
   (?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = p))
   ==> (CARD
         {s' | ksimplex p n s' /\ ?b. b IN s' /\ (s' DELETE b = s DELETE a)} =
        1)`,
  let lemma = prove
   (`!a a'. (s' DELETE a' = s DELETE a) /\ (a' = a) /\ a' IN s' /\ a IN s
            ==> (s' = s)`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
  REWRITE_TAC[HAS_SIZE_1_EXISTS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!s' a'. ksimplex p n s' /\ a' IN s' /\ (s' DELETE a' = s DELETE a)
            ==> (s' = s)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` (X_CHOOSE_THEN `a1:num->num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:num->num` (X_CHOOSE_THEN `b1:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a:num->num = a0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_P THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s:(num->num)->bool`; `a1:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a':num->num = b0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KSIMPLEX_FIX_PLANE_P THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `n:num`; `j:num`; `s':(num->num)->bool`; `b1:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`a0:num->num`; `b0:num->num`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b1:num->num = a1` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM KLE_ANTISYM] THEN ASM_MESON_TAC[IN_DELETE];
    ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC[EQ_ADD_RCANCEL]]);;

let KSIMPLEX_REPLACE_2 = prove
 (`ksimplex p n s /\ a IN s /\ ~(n = 0) /\
   ~(?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = 0)) /\
   ~(?j. 1 <= j /\ j <= n /\ !x. x IN (s DELETE a) ==> (x j = p))
   ==> (CARD
         {s' | ksimplex p n s' /\ ?b. b IN s' /\ (s' DELETE b = s DELETE a)} =
        2)`,
  let lemma = prove
   (`!a a'. (s' DELETE a' = s DELETE a) /\ (a' = a) /\ a' IN s' /\ a IN s
            ==> (s' = s)`,
    SET_TAC[])
  and lemma_1 = prove
   (`a IN s /\ ~(b = a) ==> ~(s = b INSERT (s DELETE a))`,
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
       KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` (X_CHOOSE_THEN `a1:num->num`
   STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `a:num->num = a0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`a0:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
                 KSIMPLEX_SUCCESSOR) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `a1:num->num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP KLE_IMP_POINTWISE) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; ARITH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:num->num`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `a3 = \j:num. if j = k then a1 j + 1 else a1 j` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    MATCH_MP_TAC HAS_SIZE_CARD THEN CONV_TAC HAS_SIZE_CONV THEN
    MAP_EVERY EXISTS_TAC
     [`s:(num->num)->bool`; `a3 INSERT (s DELETE (a0:num->num))`] THEN
    SUBGOAL_THEN `~((a3:num->num) IN s)` ASSUME_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `kle n a3 a1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP KLE_IMP_POINTWISE) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a3:num->num = a0) /\ ~(a3 = a1)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(a2:num->num = a0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[ARITH_RULE `~(x + 1 = x)`];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN (s DELETE a0) ==> kle n a2 x` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      SUBGOAL_THEN `kle n a2 x \/ kle n x a2` MP_TAC THENL
       [ASM_MESON_TAC[ksimplex]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~b ==> ~a) ==> b \/ a ==> b`) THEN
      DISCH_TAC THEN SUBGOAL_THEN `kle n a0 x` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:num->num = a0) \/ (x = a2)`
       (fun th -> ASM_MESON_TAC[KLE_REFL; th]) THEN
      MATCH_MP_TAC KLE_ADJACENT THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ksimplex p n (a3 INSERT (s DELETE a0))` ASSUME_TAC THENL
     [MP_TAC(ASSUME `ksimplex p n s`) THEN REWRITE_TAC[ksimplex] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE; CARD_CLAUSES;
                 CARD_DELETE] THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
        SUBGOAL_THEN `!j. (a3:num->num) j <= p`
         (fun th -> ASM_MESON_TAC[th]) THEN
        X_GEN_TAC `j:num` THEN ONCE_ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC
         `~(?j. 1 <= j /\ j <= n /\
                (!x. x IN s DELETE a0 ==> (x j = (p:num))))` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
        REWRITE_TAC[ASSUME `1 <= k`; ASSUME `k:num <= n`; NOT_FORALL_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `a4:num->num` MP_TAC) THEN
        REWRITE_TAC[IN_DELETE; NOT_IMP] THEN STRIP_TAC THEN
        UNDISCH_TAC `!x. x IN s DELETE a0 ==> kle n a2 x` THEN
        DISCH_THEN(MP_TAC o SPEC `a4:num->num`) THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN
        DISCH_THEN(MP_TAC o MATCH_MP KLE_IMP_POINTWISE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((a4:num->num) k = p)` THEN
        SUBGOAL_THEN `(a4:num->num) k <= p` MP_TAC THENL
         [ASM_MESON_TAC[ksimplex]; ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN REPEAT STRIP_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ONCE_ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      SUBGOAL_THEN `!x. x IN s /\ ~(x = a0) ==> kle n x a3`
       (fun th -> ASM_MESON_TAC[th; KLE_REFL]) THEN
      X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `kle n a2 x /\ kle n x a1` MP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
      REWRITE_TAC[IMP_CONJ] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP KLE_IMP_POINTWISE) THEN
      DISCH_TAC THEN REWRITE_TAC[kle] THEN
      DISCH_THEN(X_CHOOSE_THEN `kk:num->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(k:num) INSERT kk` THEN
      REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_CASES_TAC `j:num = k` THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
       `a2 <= x ==> !a0. x <= a1 /\ (a1 = a0 + 1) /\ (a2 = a0 + 1)
             ==> (a1 + 1 = x + 1)`)) THEN
      EXISTS_TAC `(a0:num->num) k` THEN
      ASM_MESON_TAC[KLE_IMP_POINTWISE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s':(num->num)->bool` THEN EQ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `a3:num->num` THEN
      REWRITE_TAC[IN_INSERT; DELETE_INSERT] THEN
      UNDISCH_TAC `~((a3:num->num) IN s)` THEN SET_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num->num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
                 KSIMPLEX_EXTREMA_STRONG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a_min:num->num` (X_CHOOSE_THEN `a_max:num->num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a':num->num = a_min) \/ (a' = a_max)` MP_TAC THENL
     [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN MAP_EVERY EXISTS_TAC
       [`p:num`; `(a2:num->num) k`; `n:num`;
        `k:num`; `s':(num->num)->bool`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
      X_GEN_TAC `x:num->num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `kle n a2 x /\ kle n x a1` MP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `k:num` o MATCH_MP
        KLE_IMP_POINTWISE)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a0:num->num`; `a_min:num->num`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a_max:num->num = a1` MP_TAC THENL
       [SUBGOAL_THEN `a1:num->num IN (s' DELETE a_min) /\
                      a_max:num->num IN (s DELETE a0)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL];
      DISJ2_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a3:num->num`; `a_max:num->num`] THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(a3:num->num IN s)` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `a_min:num->num = a2` MP_TAC THENL
       [SUBGOAL_THEN `a2:num->num IN (s' DELETE a_max) /\
                      a_min:num->num IN (s DELETE a0)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:num->num = a1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`a1:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
                 KSIMPLEX_PREDECESSOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `a0:num->num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP KLE_IMP_POINTWISE) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; ARITH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:num->num`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!x. x IN (s DELETE a1) ==> kle n x a2` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      SUBGOAL_THEN `kle n a2 x \/ kle n x a2` MP_TAC THENL
       [ASM_MESON_TAC[ksimplex]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~b ==> ~a) ==> a \/ b ==> b`) THEN
      DISCH_TAC THEN SUBGOAL_THEN `kle n x a1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:num->num = a2) \/ (x = a1)`
       (fun th -> ASM_MESON_TAC[KLE_REFL; th]) THEN
      MATCH_MP_TAC KLE_ADJACENT THEN EXISTS_TAC `k:num` THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a2:num->num = a1)` ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[ARITH_RULE `~(x + 1 = x)`];
      ALL_TAC] THEN
    ABBREV_TAC `a3 = \j:num. if j = k then a0 j - 1 else a0 j` THEN
    SUBGOAL_THEN `!j:num. a0(j) = if j = k then a3(j) + 1 else a3 j`
    ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN EXPAND_TAC "a3" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[ARITH_RULE `(a = a - 1 + 1) <=> ~(a = 0)`] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)` THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(0 + 1 = x + 1) <=> (x = 0)`] THEN DISCH_TAC THEN
      UNDISCH_TAC
       `~(?j. 1 <= j /\ j <= n /\ (!x. x IN s DELETE a1 ==> (x j = 0)))` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[KLE_IMP_POINTWISE; LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(kle n a0 a3)` ASSUME_TAC THENL
     [ASM_MESON_TAC[KLE_IMP_POINTWISE; ARITH_RULE `~(a + 1 <= a)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(a3:num->num IN s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `kle n a3 a2` ASSUME_TAC THENL
     [SUBGOAL_THEN `kle n a0 a1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[kle] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[
        ASSUME `!j:num. a0 j = (if j = k then a3 j + 1 else a3 j)`;
        ASSUME `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)`] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `kle n a3 a0` ASSUME_TAC THENL
     [REWRITE_TAC[kle] THEN EXISTS_TAC `{k:num}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_SING; IN_NUMSEG] THEN
      ASM_MESON_TAC[ADD_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_CARD THEN CONV_TAC HAS_SIZE_CONV THEN
    MAP_EVERY EXISTS_TAC
     [`s:(num->num)->bool`; `a3 INSERT (s DELETE (a1:num->num))`] THEN
    SUBGOAL_THEN `~(a3:num->num = a1) /\ ~(a3 = a0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `ksimplex p n (a3 INSERT (s DELETE a1))` ASSUME_TAC THENL
     [MP_TAC(ASSUME `ksimplex p n s`) THEN REWRITE_TAC[ksimplex] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE; CARD_CLAUSES;
                 CARD_DELETE] THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
        SUBGOAL_THEN `!j. (a3:num->num) j <= p`
         (fun th -> ASM_MESON_TAC[th]) THEN
        X_GEN_TAC `j:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num->num`; `j:num`]) THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN REPEAT STRIP_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        EXPAND_TAC "a3" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      SUBGOAL_THEN `!x. x IN s /\ ~(x = a1) ==> kle n a3 x`
       (fun th -> ASM_MESON_TAC[th; KLE_REFL]) THEN
      X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      MATCH_MP_TAC KLE_BETWEEN_L THEN
      MAP_EVERY EXISTS_TAC [`a0:num->num`; `a2:num->num`] THEN
      ASM_MESON_TAC[IN_DELETE];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s':(num->num)->bool` THEN EQ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `a3:num->num` THEN
      REWRITE_TAC[IN_INSERT; DELETE_INSERT] THEN
      UNDISCH_TAC `~((a3:num->num) IN s)` THEN SET_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num->num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`p:num`; `n:num`; `s':(num->num)->bool`]
                 KSIMPLEX_EXTREMA_STRONG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a_min:num->num` (X_CHOOSE_THEN `a_max:num->num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a':num->num = a_min) \/ (a' = a_max)` MP_TAC THENL
     [MATCH_MP_TAC KSIMPLEX_FIX_PLANE THEN MAP_EVERY EXISTS_TAC
       [`p:num`; `(a2:num->num) k`; `n:num`;
        `k:num`; `s':(num->num)->bool`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
      X_GEN_TAC `x:num->num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `kle n a0 x /\ kle n x a2` MP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `k:num` o MATCH_MP
        KLE_IMP_POINTWISE)) THEN
      SUBGOAL_THEN `(a2:num->num) k <= a0 k`
        (fun th -> MP_TAC th THEN ARITH_TAC) THEN
      UNDISCH_TAC `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)` THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [DISJ2_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a3:num->num`; `a_min:num->num`] THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(a3:num->num IN s)` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `a_max:num->num = a2` MP_TAC THENL
       [SUBGOAL_THEN `a2:num->num IN (s' DELETE a_min) /\
                      a_max:num->num IN (s DELETE a1)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!j. a2 j = if 1 <= j /\ j <= n then a3 j + 1 else a3 j`
       (fun th -> ASM_REWRITE_TAC[th; FUN_EQ_THM])
      THENL
       [ALL_TAC;
        MATCH_MP_TAC MONO_FORALL THEN MESON_TAC[EQ_ADD_RCANCEL]] THEN
      UNDISCH_TAC `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL];
      DISJ1_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a1:num->num`; `a_max:num->num`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      SUBGOAL_THEN `a_min:num->num = a0` MP_TAC THENL
       [SUBGOAL_THEN `a0:num->num IN (s' DELETE a_max) /\
                      a_min:num->num IN (s DELETE a1)`
        MP_TAC THENL
         [ASM_MESON_TAC[IN_DELETE]; ASM_MESON_TAC[KLE_ANTISYM; IN_DELETE]];
        ALL_TAC] THEN
      UNDISCH_THEN `!j:num. a1 j = (if j = k then a2 j + 1 else a2 j)`
       (K ALL_TAC) THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      MESON_TAC[EQ_ADD_RCANCEL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
        KSIMPLEX_PREDECESSOR) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KLE_ANTISYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->num`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:num->num`; `p:num`; `n:num`; `s:(num->num)->bool`]
        KSIMPLEX_SUCCESSOR) THEN
  REWRITE_TAC[ASSUME `ksimplex p n s`; ASSUME `a:num->num IN s`] THEN
  MATCH_MP_TAC(TAUT `~a /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KLE_ANTISYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->num`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a' = \j:num. if j = l then u(j) + 1 else u(j)` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN `~(k:num = l)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `!j:num. v j = (if j = l then a j + 1 else a j)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ksimplex]) THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:num->num`; `v:num->num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[kle] THEN
    DISCH_THEN(DISJ_CASES_THEN (CHOOSE_THEN (MP_TAC o SPEC `l:num` o
      CONJUNCT2))) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':num->num = a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a':num->num) IN s)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ksimplex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:num->num`; `a':num->num`] o
      last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THENL
     [DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `kle n u a /\ kle n u a' /\ kle n a v /\ kle n a' v`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[kle] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `{k:num}`;
      EXISTS_TAC `{l:num}`;
      EXISTS_TAC `{l:num}`;
      EXISTS_TAC `{k:num}`] THEN
    ASM_REWRITE_TAC[IN_SING; SUBSET; IN_NUMSEG] THEN
    ASM_MESON_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. kle n u x /\ kle n x v
                    ==> ((x = u) \/ (x = a) \/ (x = a') \/ (x = v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->num` THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; IMP_IMP; AND_FORALL_THM] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ASM_CASES_TAC `(x:num->num) k = u k` THEN
    ASM_CASES_TAC `(x:num->num) l = u l` THENL
     [DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th);
      DISCH_THEN(fun th -> DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
                           MP_TAC th);
      DISCH_THEN(fun th -> DISJ2_TAC THEN DISJ1_TAC THEN MP_TAC th);
      DISCH_THEN(fun th -> REPEAT DISJ2_TAC THEN MP_TAC th)] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[LE_ANTISYM;
       ARITH_RULE `x <= u + 1 /\ u <= x <=> (x = u) \/ (x = u + 1)`]);
    ALL_TAC] THEN
  SUBGOAL_THEN `kle n u v` ASSUME_TAC THENL
   [ASM_MESON_TAC[KLE_TRANS; ksimplex]; ALL_TAC] THEN
  SUBGOAL_THEN `ksimplex p n (a' INSERT (s DELETE a))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `ksimplex p n s`) THEN REWRITE_TAC[ksimplex] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE; CARD_CLAUSES;
               CARD_DELETE; IN_DELETE] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `j:num` THEN MP_TAC th) THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `v:num->num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
      SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[EXISTS_REFL; LEFT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ kle n v x ==> kle n a' x`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      MATCH_MP_TAC KLE_BETWEEN_R THEN
      MAP_EVERY EXISTS_TAC [`u:num->num`; `v:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ksimplex; KLE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ kle n x u ==> kle n x a'`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
      MATCH_MP_TAC KLE_BETWEEN_L THEN
      MAP_EVERY EXISTS_TAC [`u:num->num`; `v:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ksimplex; KLE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ ~(x = a) ==> kle n a' x \/ kle n x a'`
     (fun th -> MESON_TAC[th; KLE_REFL; ASSUME `(a:num->num) IN s`]) THEN
    X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `kle n v x` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `kle n x u` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:num->num = u) \/ (x = a) \/ (x = a') \/ (x = v)`
     (fun th -> ASM_MESON_TAC[th; KLE_REFL]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[ksimplex];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_CARD THEN CONV_TAC HAS_SIZE_CONV THEN
  MAP_EVERY EXISTS_TAC
   [`s:(num->num)->bool`; `a' INSERT (s DELETE (a:num->num))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `s':(num->num)->bool` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a':num->num` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE] THEN ASM_MESON_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a'':num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:num->num) IN s' \/ a' IN s'` MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN
    MP_TAC(ASSUME `s' DELETE a'' = s DELETE (a:num->num)`) THEN
    REWRITE_TAC[EXTENSION] THEN
    DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THENL
     [DISCH_THEN(MP_TAC o SPEC `a:num->num`);
      DISCH_THEN(MP_TAC o SPEC `a':num->num`)] THEN
    REWRITE_TAC[IN_DELETE] THEN ASM_REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `~(u:num->num = v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(kle n v u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[KLE_ANTISYM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(u:num->num = a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:num->num = a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u:num->num IN s' /\ v IN s'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION; IN_DELETE]; ALL_TAC] THEN
  ASM_CASES_TAC
   `!x. x IN s' ==> kle n x u \/ kle n v x`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num->num` MP_TAC) THEN
    REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:num->num = u) \/ (w = a) \/ (w = a') \/ (w = v)`
     (fun th -> ASM_MESON_TAC[KLE_REFL; th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[ksimplex]] THEN
  MP_TAC(SPECL [`u:num->num`; `p:num`; `n:num`; `s':(num->num)->bool`]
               KSIMPLEX_SUCCESSOR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[EXTENSION; IN_DELETE]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (MP_TAC o SPEC `v:num->num`) MP_TAC) THENL
   [ASM_MESON_TAC[EXTENSION; IN_DELETE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `!x. x IN s' ==> kle n x u \/ kle n v x` THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `w:num->num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN(MP_TAC o MATCH_MP KLE_IMP_POINTWISE)) THEN
  ASM_REWRITE_TAC[] THENL
   [MESON_TAC[ARITH_RULE `~(i + 1 <= i)`]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `k:num` th) THEN
                       MP_TAC(SPEC `l:num` th)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN TRY ARITH_TAC THEN
  UNDISCH_TAC `~(k:num = l)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence another step towards concreteness.                                  *)
(* ------------------------------------------------------------------------- *)

let KUHN_SIMPLEX_LEMMA = prove
 (`!p n. (!s. ksimplex p (n + 1) s ==> (IMAGE rl s SUBSET 0..n+1)) /\
         ODD(CARD{f | (?s a. ksimplex p (n + 1) s /\
                             a IN s /\
                             (f = s DELETE a)) /\
                      (IMAGE rl f = 0 .. n) /\
                      ((?j. 1 <= j /\ j <= n + 1 /\
                            !x. x IN f ==> (x j = 0)) \/
                       (?j. 1 <= j /\ j <= n + 1 /\
                            !x. x IN f ==> (x j = p)))})
         ==>  ODD(CARD {s | s IN {s | ksimplex p (n + 1) s} /\
                            (IMAGE rl s = 0..n+1)})`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `ODD(CARD {f | f IN {f | ?s. s IN {s | ksimplex p (n + 1) s} /\
                             (?a. a IN s /\ (f = s DELETE a))} /\
               (IMAGE rl f = 0..n) /\
               ((?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = 0)) \/
                (?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = p)))})`
  MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; RIGHT_AND_EXISTS_THM]; ALL_TAC] THEN
  MATCH_MP_TAC KUHN_COMPLETE_LEMMA THEN  REWRITE_TAC[FINITE_SIMPLICES] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ksimplex; ARITH_RULE `(n + 1) + 1 = n + 2`];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC KSIMPLEX_REPLACE_0;
    MATCH_MP_TAC KSIMPLEX_REPLACE_1;
    MATCH_MP_TAC KSIMPLEX_REPLACE_2] THEN
  ASM_MESON_TAC[ARITH_RULE `~(n + 1 = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* Reduced labelling.                                                        *)
(* ------------------------------------------------------------------------- *)

let reduced = new_definition
 `reduced label n (x:num->num) =
     @k. k <= n /\
         (!i. 1 <= i /\ i < k + 1 ==> (label x i = 0)) /\
         ((k = n) \/ ~(label x (k + 1) = 0))`;;

let REDUCED_LABELLING = prove
 (`!label x n.
      reduced label n x <= n /\
      (!i. 1 <= i /\ i < reduced label n x + 1 ==> (label x i = 0)) /\
      ((reduced label n x = n) \/ ~(label x (reduced label n x + 1) = 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reduced] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `\j. j <= n /\ ~(label (x:num->num) (j + 1) = 0) \/ (n = j)`
     num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k = n:num` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
  SIMP_TAC[LT_IMP_LE] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i < n + 1 ==> i - 1 < n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i < n + 1 ==> ~(n = i - 1)`] THEN
  ASM_SIMP_TAC[SUB_ADD] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ARITH_TAC);;

let REDUCED_LABELLING_UNIQUE = prove
 (`!label x n.
      r <= n /\
      (!i. 1 <= i /\ i < r + 1 ==> (label x i = 0)) /\
      ((r = n) \/ ~(label x (r + 1) = 0))
      ==> (reduced label n x = r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC(SPECL
        [`label:(num->num)->(num->num)`; `x:num->num`; `n:num`]
        REDUCED_LABELLING) THEN
  MATCH_MP_TAC(ARITH_RULE `~(a < b) /\ ~(b < a:num) ==> (a = b)`) THEN
  ASM_MESON_TAC[ARITH_RULE `s < r:num /\ r <= n ==> ~(s = n)`;
                ARITH_RULE `s < r ==> 1 <= s + 1 /\ s + 1 < r + 1`]);;

let REDUCED_LABELLING_0 = prove
 (`!label n x j.
        1 <= j /\ j <= n /\ (label x j = 0)
        ==> ~(reduced label n x = j - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `x:num->num`; `n:num`]
               REDUCED_LABELLING) THEN
  ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `1 <= j /\ j <= n ==> ~(j - 1 = n)`]);;

let REDUCED_LABELLING_1 = prove
 (`!label n x j.
        1 <= j /\ j <= n /\ ~(label x j = 0)
        ==> reduced label n x < j`,
  REWRITE_TAC[GSYM NOT_LE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `x:num->num`; `n:num`]
               REDUCED_LABELLING) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[ARITH_RULE `y < x + 1 <=> (y <= x)`]);;

let REDUCED_LABELLING_SUC = prove
 (`!lab n x.
        ~(reduced lab (n + 1) x = n + 1)
        ==> (reduced lab (n + 1) x = reduced lab n x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REDUCED_LABELLING_UNIQUE THEN
  ASM_MESON_TAC[REDUCED_LABELLING; ARITH_RULE
   `x <= n + 1 /\ ~(x = n + 1) ==> x <= n`]);;

let COMPLETE_FACE_TOP = prove
 (`!lab f n.
         (!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = 0)
                ==> (lab x j = 0)) /\
         (!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = p)
                ==> (lab x j = 1))
         ==> ((IMAGE (reduced lab (n + 1)) f = 0..n) /\
              ((?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = 0)) \/
               (?j. 1 <= j /\ j <= n + 1 /\ !x. x IN f ==> (x j = p))) <=>
              (IMAGE (reduced lab (n + 1)) f = 0..n) /\
              (!x. x IN f ==> (x (n + 1) = p)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[ARITH_RULE `1 <= n + 1`; LE_REFL]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THENL
   [DISCH_THEN(MP_TAC o SPEC `j - 1`) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[IN_IMAGE; IN_NUMSEG; LE_0; NOT_EXISTS_THM;
                 ARITH_RULE `j <= n + 1 ==> j - 1 <= n`] THEN
    ASM_MESON_TAC[REDUCED_LABELLING_0];
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0; NOT_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `j <= n + 1 ==> ((j <= n) <=> ~(j = n + 1))`] THEN
    ASM_MESON_TAC[REDUCED_LABELLING_1; ARITH_RULE `~(1 = 0)`; LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get just about the nice induction.                               *)
(* ------------------------------------------------------------------------- *)

let KUHN_INDUCTION = prove
 (`!p n. 0 < p /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n + 1 /\ (x j = 0)
                ==> (lab x j = 0)) /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n + 1 /\ (x j = p)
                ==> (lab x j = 1))
         ==> ODD(CARD {f | ksimplex p n f /\
                           (IMAGE (reduced lab n) f = 0..n)})
             ==> ODD(CARD {s | ksimplex p (n + 1) s /\
                           (IMAGE (reduced lab (n + 1)) s = 0..n+1)})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IN_ELIM_THM] KUHN_SIMPLEX_LEMMA) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
    MESON_TAC[ARITH_RULE `x <= n ==> x <= n + 1`; REDUCED_LABELLING];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `f:(num->num)->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `(!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = 0) ==> (lab x j = 0)) /\
    (!x j. x IN f /\ 1 <= j /\ j <= n + 1 /\ (x j = p) ==> (lab x j = 1))`
  THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a /\ c <=> b /\ d)`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN REWRITE_TAC[ksimplex] THEN
    ASM_MESON_TAC[IN_DELETE]] THEN
  ASM_SIMP_TAC[COMPLETE_FACE_TOP] THEN
  ASM_CASES_TAC `!x. x IN f ==> (x(n + 1):num = p)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[ksimplex] THEN
    ASM_MESON_TAC[ARITH_RULE `~(n + 1 <= n)`]] THEN
  ASM_SIMP_TAC[SIMPLEX_TOP_FACE] THEN
  ASM_CASES_TAC `ksimplex p n f` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `x:num->num` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:num->num) IN f` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REDUCED_LABELLING_SUC THEN
  MATCH_MP_TAC(ARITH_RULE `a:num < b ==> ~(a = b)`) THEN
  MATCH_MP_TAC REDUCED_LABELLING_1 THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  MATCH_MP_TAC(ARITH_RULE `(n = 1) ==> ~(n = 0)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  ASM_MESON_TAC[ksimplex]);;

(* ------------------------------------------------------------------------- *)
(* And so we get the final combinatorial result.                             *)
(* ------------------------------------------------------------------------- *)

let KSIMPLEX_0 = prove
 (`ksimplex p 0 s <=> (s = {(\x. p)})`,
  REWRITE_TAC[ksimplex; ADD_CLAUSES] THEN
  CONV_TAC(LAND_CONV(LAND_CONV HAS_SIZE_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `1 <= j /\ j <= 0 <=> F`] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC[IN_SING] THEN
  SIMP_TAC[RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[KLE_REFL] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[AND_FORALL_THM; ARITH_RULE
   `x <= y:num /\ (x = y) <=> (x = y)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2]);;

let REDUCE_LABELLING_0 = prove
 (`!lab x. reduced lab 0 x = 0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REDUCED_LABELLING_UNIQUE THEN
  REWRITE_TAC[LE_REFL] THEN ARITH_TAC);;

let KUHN_COMBINATORIAL = prove
 (`!lab p n.
         0 < p /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n /\ (x j = 0)
                ==> (lab x j = 0)) /\
         (!x j. (!j. x(j) <= p) /\ 1 <= j /\ j <= n  /\ (x j = p)
                ==> (lab x j = 1))
         ==> ODD(CARD {s | ksimplex p n s /\
                           (IMAGE (reduced lab n) s = 0..n)})`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `{s | ksimplex p 0 s /\ (IMAGE (reduced lab 0) s = 0 .. 0)} =
                  {{(\x. p)}}`
     (fun th -> SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY;
                         FINITE_RULES; th; ARITH]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; KSIMPLEX_0; IN_SING] THEN
    GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[NUMSEG_SING; EXTENSION; IN_SING; IN_IMAGE] THEN
    REWRITE_TAC[REDUCE_LABELLING_0] THEN MESON_TAC[];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `j <= n ==> j <= SUC n`];
      ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN MATCH_MP_TAC KUHN_INDUCTION THEN
    ASM_REWRITE_TAC[GSYM ADD1]]);;

let KUHN_LEMMA = prove
 (`!n p label.
        0 < p /\ 0 < n /\
        (!x. (!i. 1 <= i /\ i <= n ==> x(i) <= p)
             ==> !i. 1 <= i /\ i <= n ==> (label x i = 0) \/ (label x i = 1)) /\
        (!x. (!i. 1 <= i /\ i <= n ==> x(i) <= p)
             ==> !i. 1 <= i /\ i <= n /\ (x i = 0) ==> (label x i = 0)) /\
        (!x. (!i. 1 <= i /\ i <= n ==> x(i) <= p)
             ==> !i. 1 <= i /\ i <= n /\ (x i = p) ==> (label x i = 1))
        ==> ?q. (!i. 1 <= i /\ i <= n ==> q(i) < p) /\
                (!i. 1 <= i /\ i <= n
                     ==> ?r s. (!j. 1 <= j /\ j <= n
                                    ==> q(j) <= r(j) /\ r(j) <= q(j) + 1) /\
                               (!j. 1 <= j /\ j <= n
                                    ==> q(j) <= s(j) /\ s(j) <= q(j) + 1) /\
                               ~(label r i = label s i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `p:num`; `n:num`]
               KUHN_COMBINATORIAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `{s | ksimplex p n s /\ (IMAGE (reduced label n) s = 0 .. n)} = {}`
  THENL [ASM_REWRITE_TAC[CARD_CLAUSES; ARITH]; ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(num->num)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`p:num`; `n:num`; `s:(num->num)->bool`]
               KSIMPLEX_EXTREMA_STRONG) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->num` THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->num` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x + 1 <= y ==> x < y`) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(b:num->num) i` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_MESON_TAC[ksimplex];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (reduced label n) s = 0 .. n` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `i - 1` th) THEN MP_TAC(SPEC `i:num` th)) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> i - 1 <= n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  MAP_EVERY EXISTS_TAC [`u:num->num`; `v:num->num`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[KLE_IMP_POINTWISE]; ALL_TAC] THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `u:num->num`; `n:num`]
                REDUCED_LABELLING) THEN
  MP_TAC(SPECL [`label:(num->num)->num->num`; `v:num->num`; `n:num`]
                REDUCED_LABELLING) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> ~(i - 1 = n)`] THEN
  ASM_SIMP_TAC[SUB_ADD] THEN ASM_MESON_TAC[ARITH_RULE `i < i + 1`]);;

(* ------------------------------------------------------------------------- *)
(* The main result for the unit cube.                                        *)
(* ------------------------------------------------------------------------- *)

let BROUWER_CUBE = prove
 (`!f:real^N->real^N.
        f continuous_on (interval [vec 0,vec 1]) /\
        IMAGE f (interval [vec 0,vec 1]) SUBSET (interval [vec 0,vec 1])
        ==> ?x. x IN interval[vec 0,vec 1] /\ (f x = x)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = dimindex(:N)` THEN
  SUBGOAL_THEN `1 <= n /\ 0 < n /\ ~(n = 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[DIMINDEX_NONZERO; DIMINDEX_GE_1] THEN
    ASM_MESON_TAC[LT_NZ; DIMINDEX_NONZERO];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `?d. &0 < d /\ !x:real^N. x IN interval[vec 0,vec 1] ==> d <= norm(f x - x)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BROUWER_COMPACTNESS_LEMMA THEN
    ASM_SIMP_TAC[COMPACT_INTERVAL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_ID] THEN
    ASM_MESON_TAC[VECTOR_SUB_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  FREEZE_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th))
        (SPEC `f:real^N->real^N` KUHN_LABELLING_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC `\i. 1 <= i /\ i <= n`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_INTERVAL; VEC_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `label:real^N->num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x y i. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1] /\
            1 <= i /\ i <= n /\ ~(label (x:real^N) i :num = label y i)
            ==> abs((f(x) - x)$i) <= norm(f(y) - f(x)) + norm(y - x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(((f:real^N->real^N)(y) - f(x))$i) + abs((y - x)$i)` THEN
    ASM_SIMP_TAC[REAL_LE_ADD2; COMPONENT_LE_NORM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y fx fy d. (x <= fx /\ fy <= y \/ fx <= x /\ y <= fy)
             ==> abs(fx - x) <= abs(fy - fx) + abs(y - x)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(a = b)
      ==> a <= 1 /\ b <= 1 ==> (a = 0) /\ (b = 1) \/ (a = 1) /\ (b = 0)`)) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !x y z i. x IN interval[vec 0,vec 1] /\
                  y IN interval[vec 0,vec 1] /\
                  z IN interval[vec 0,vec 1] /\
                  1 <= i /\ i <= n /\
                  norm(x - z) < e /\ norm(y - z) < e /\
                  ~(label (x:real^N) i :num = label y i)
                  ==> abs((f(z) - z)$i) < d / &n`
  MP_TAC THENL
   [SUBGOAL_THEN
     `(f:real^N->real^N) uniformly_continuous_on interval[vec 0,vec 1]`
    MP_TAC THENL
     [ASM_SIMP_TAC[COMPACT_UNIFORMLY_CONTINUOUS; COMPACT_INTERVAL];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `d / &n / &8`) THEN
    SUBGOAL_THEN `&0 < d / &n / &8` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LT_MULT; ARITH];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (e / &2) (d / &n / &8)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_MIN; REAL_HALF] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `z:real^N`; `i:num`] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x fx n1 n2 n3 n4 d4.
        abs(fx - x) <= n1 + n2 /\
        abs(fx - fz) <= n3 /\ abs(x - z) <= n4 /\
        n1 < d4 /\ n2 < &2 * d4 /\ n3 < d4 /\ n4 < d4 /\ (&8 * d4 = d)
        ==> abs(fz - z) < d`) THEN
    MAP_EVERY EXISTS_TAC
     [`(x:real^N)$i`; `(f:real^N->real^N)(x)$i`;
      `norm((f:real^N->real^N) y - f x)`; `norm(y - x:real^N)`;
      `norm((f:real^N->real^N) x - f z)`;
      `norm(x - z:real^N)`; `d / &n / &8`] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(x - z:real^N) + norm(y - z)` THEN
      ASM_SIMP_TAC[REAL_ARITH `a < e / &2 /\ b < e / &2 /\
                               (&2 * (e / &2) = e) ==> a + b < e`;
                   REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE; DIST_SYM];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(x - z:real^N) + norm(y - z)` THEN
      ASM_SIMP_TAC[REAL_ARITH `a < e /\ b < e ==> a + b < &2 * e`] THEN
      REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE; DIST_SYM];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
        `a < e / &2 /\ &0 < e /\ (&2 * (e / &2) = e) ==> a < e`) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  X_CHOOSE_THEN `p:num` MP_TAC (SPEC `&1 + &n / e` REAL_ARCH_SIMPLE) THEN
  DISJ_CASES_TAC(ARITH_RULE `(p = 0) \/ 0 < p`) THENL
   [DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LT_REFL; REAL_NOT_LE] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT;
                 REAL_ARITH `&0 < x ==> &0 < &1 + x`];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[NOT_FORALL_THM] THEN
  MP_TAC(SPECL [`n:num`; `p:num`;
            `\v:(num->num). label((lambda i. &(v i) / &p):real^N):num->num`]
               KUHN_LEMMA) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(x = 0) \/ (x = 1) <=> x <= 1`] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; IN_INTERVAL; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_MUL_LZERO; REAL_MUL_LID;
                 REAL_LT_IMP_NZ; REAL_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[LE_0; REAL_OF_NUM_LE] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  ABBREV_TAC `z:real^N = lambda i. &(q i) / &p` THEN EXISTS_TAC `z:real^N` THEN
  REWRITE_TAC[TAUT `~(a ==> b) <=> ~b /\ a`] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  SUBGOAL_THEN `z:real^N IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[LE_0; LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= n /\ d / &n <= abs((f z - z:real^N)$i)`
  MP_TAC THENL
   [SUBGOAL_THEN `d <= norm(f z - z:real^N)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. abs((f z - z:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; NUMSEG_EMPTY; CARD_NUMSEG] THEN
    ASM_REWRITE_TAC[NOT_LT; ADD_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (X_CHOOSE_THEN `s:num->num`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(lambda i. &(r i) / &p) :real^N` THEN
  EXISTS_TAC `(lambda i. &(s i) / &p) :real^N` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[LE_0; ARITH_RULE `r <= q + 1 /\ q < p ==> r <= p`];
    SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[LE_0; ARITH_RULE `r <= q + 1 /\ q < p ==> r <= p`];
    ALL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b < e ==> a < e`)
                        (SPEC_ALL NORM_LE_L1)) THEN
  MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; NUMSEG_EMPTY; CARD_NUMSEG] THEN
  ASM_REWRITE_TAC[NOT_LT; ADD_SUB] THEN EXPAND_TAC "z" THEN
  EXPAND_TAC "n" THEN SIMP_TAC[VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
  ASM_REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&1` THEN
  ASM_SIMP_TAC[REAL_ARITH `q <= r /\ r <= q + &1 ==> abs(r - q) <= &1`;
               REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN
  REWRITE_TAC[REAL_INV_DIV; REAL_INV_MUL] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ;
               REAL_OF_NUM_LT; ARITH] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[REAL_INV_1; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_ARITH `&1 + x <= y ==> x < y`]);;

(* ------------------------------------------------------------------------- *)
(* Retractions.                                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("retract_of",(12,"right"));;

let retraction = new_definition
  `retraction (s,t) (r:real^N->real^N) <=>
        t SUBSET s /\ r continuous_on s /\ (IMAGE r s SUBSET t) /\
        (!x. x IN t ==> (r x = x))`;;

let retract_of = new_definition
  `t retract_of s <=> ?r. retraction (s,t) r`;;

let RETRACTION = prove
 (`!s t r. retraction (s,t) r <=>
           t SUBSET s /\
           r continuous_on s /\
           IMAGE r s = t /\
           (!x. x IN t ==> r x = x)`,
  REWRITE_TAC[retraction] THEN SET_TAC[]);;

let RETRACT_OF_IMP_EXTENSIBLE = prove
 (`!f:real^M->real^N u s t.
        s retract_of t /\ f continuous_on s /\ IMAGE f s SUBSET u
        ==> ?g. g continuous_on t /\ IMAGE g t SUBSET u /\
                (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[RETRACTION; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^M->real^N) o (r:real^M->real^M)` THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
  ASM_MESON_TAC[]);;

let RETRACTION_IDEMPOTENT = prove
 (`!r s t. retraction (s,t) r ==> !x. x IN s ==> (r(r(x)) = r(x))`,
  REWRITE_TAC[retraction; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let IDEMPOTENT_IMP_RETRACTION = prove
 (`!f:real^N->real^N s.
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (!x. x IN s ==> f(f x) = f x)
        ==> retraction (s,IMAGE f s) f`,
  REWRITE_TAC[retraction] THEN SET_TAC[]);;

let RETRACTION_SUBSET = prove
 (`!r s s' t. retraction (s,t) r /\ t SUBSET s' /\ s' SUBSET s
              ==> retraction (s',t) r`,
  SIMP_TAC[retraction] THEN
  MESON_TAC[IMAGE_SUBSET; SUBSET_TRANS; CONTINUOUS_ON_SUBSET]);;

let RETRACT_OF_SUBSET = prove
 (`!s s' t. t retract_of s /\ t SUBSET s' /\ s' SUBSET s
            ==> t retract_of s'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[retract_of; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[RETRACTION_SUBSET]);;

let RETRACT_OF_TRANSLATION = prove
 (`!a t s:real^N->bool.
        t retract_of s
        ==> (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\x:real^N. a + x) o r o (\x:real^N. --a + x)` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
     SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`;
                    IMAGE_ID];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`; IMAGE_ID];
    ASM_SIMP_TAC[o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`]]);;

let RETRACT_OF_TRANSLATION_EQ = prove
 (`!a t s:real^N->bool.
        (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s) <=>
        t retract_of s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[RETRACT_OF_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o MATCH_MP RETRACT_OF_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [RETRACT_OF_TRANSLATION_EQ];;

let RETRACT_OF_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ t retract_of s
        ==> (IMAGE f t) retract_of (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) o r o (g:real^N->real^M)` THEN
  UNDISCH_THEN `!x y. (f:real^M->real^N) x = f y ==> x = y` (K ALL_TAC) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
           ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; IMAGE_ID];
    ASM_SIMP_TAC[o_DEF]]);;

let RETRACT_OF_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ((IMAGE f t) retract_of (IMAGE f s) <=> t retract_of s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[RETRACT_OF_INJECTIVE_LINEAR_IMAGE]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE) THEN
  SUBGOAL_THEN
   `!s. s = IMAGE (h:real^N->real^M) (IMAGE (f:real^M->real^N) s)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RETRACT_OF_INJECTIVE_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

add_linear_invariants [RETRACT_OF_LINEAR_IMAGE_EQ];;

let RETRACTION_REFL = prove
 (`!s. retraction (s,s) (\x. x)`,
  REWRITE_TAC[retraction; IMAGE_ID; SUBSET_REFL; CONTINUOUS_ON_ID]);;

let RETRACT_OF_REFL = prove
 (`!s. s retract_of s`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[RETRACTION_REFL]);;

let RETRACTION_CLOSEST_POINT = prove
 (`!s t:real^N->bool.
        convex t /\ closed t /\ ~(t = {}) /\ t SUBSET s
        ==> retraction (s,t) (closest_point t)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[retraction] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; CLOSEST_POINT_SELF;
               CLOSEST_POINT_IN_SET; CONTINUOUS_ON_CLOSEST_POINT]);;

let RETRACT_OF_IMP_SUBSET = prove
 (`!s t. s retract_of t ==> s SUBSET t`,
  SIMP_TAC[retract_of; retraction] THEN MESON_TAC[]);;

let RETRACT_OF_EMPTY = prove
 (`(!s:real^N->bool. {} retract_of s <=> s = {}) /\
   (!s:real^N->bool. s retract_of {} <=> s = {})`,
  REWRITE_TAC[retract_of; retraction; SUBSET_EMPTY; IMAGE_CLAUSES] THEN
  CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IMAGE_EQ_EMPTY; CONTINUOUS_ON_EMPTY;
                  SUBSET_REFL]);;

let RETRACT_OF_SING = prove
 (`!s x:real^N. {x} retract_of s <=> x IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; RETRACTION] THEN EQ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(\y. x):real^N->real^N` THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]);;

let RETRACTION_o = prove
 (`!f g s t u:real^N->bool.
        retraction (s,t) f /\ retraction (t,u) g
        ==> retraction (s,u) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retraction] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let RETRACT_OF_TRANS = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ t retract_of u ==> s retract_of u`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[RETRACTION_o]);;

let CLOSED_IN_RETRACT = prove
 (`!s t:real^N->bool.
        s retract_of t ==> closed_in (subtopology euclidean t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `s = {x:real^N | x IN t /\ lift(norm(r x - x)) = vec 0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP; NORM_EQ_0] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_SIMP_TAC[CONTINUOUS_ON_ID]]);;

let RETRACT_OF_CONTRACTIBLE = prove
 (`!s t:real^N->bool. contractible t /\ s retract_of t ==> contractible s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contractible; retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `r:real^N->real^N`)) THEN
  SIMP_TAC[HOMOTOPIC_WITH; PCROSS; LEFT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `h:real^(1,N)finite_sum->real^N`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`(r:real^N->real^N) a`;
    `(r:real^N->real^N) o (h:real^(1,N)finite_sum->real^N)`] THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o; SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
           CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let RETRACT_OF_COMPACT = prove
 (`!s t:real^N->bool. compact t /\ s retract_of t ==> compact s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[COMPACT_CONTINUOUS_IMAGE]);;

let RETRACT_OF_CLOSED = prove
 (`!s t. closed t /\ s retract_of t ==> closed s`,
  MESON_TAC[CLOSED_IN_CLOSED_EQ; CLOSED_IN_RETRACT]);;

let RETRACT_OF_CONNECTED = prove
 (`!s t:real^N->bool. connected t /\ s retract_of t ==> connected s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[CONNECTED_CONTINUOUS_IMAGE]);;

let RETRACT_OF_PATH_CONNECTED = prove
 (`!s t:real^N->bool. path_connected t /\ s retract_of t ==> path_connected s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let RETRACT_OF_SIMPLY_CONNECTED = prove
 (`!s t:real^N->bool.
       simply_connected t /\ s retract_of t ==> simply_connected s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] SIMPLY_CONNECTED_RETRACTION_GEN)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[IMAGE_ID; CONTINUOUS_ON_ID]);;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
               g continuous_on u /\ IMAGE g u SUBSET s
               ==> homotopic_with (\x. T) (u,s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                   g continuous_on u /\ IMAGE g u SUBSET t
                   ==> homotopic_with (\x. T) (u,t) f g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ q /\ T /\ r /\ s /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL_NULL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s
             ==> ?c. homotopic_with (\x. T) (u,s) f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t
                 ==> ?c. homotopic_with (\x. T) (u,t) f (\x. c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
               g continuous_on s /\ IMAGE g s SUBSET u
               ==> homotopic_with (\x. T) (s,u)  f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                   g continuous_on t /\ IMAGE g t SUBSET u
                   ==> homotopic_with (\x. T) (t,u) f g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ q /\ T /\ r /\ s /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL_NULL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u
             ==> ?c. homotopic_with (\x. T) (s,u) f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u
                 ==> ?c. homotopic_with (\x. T) (t,u) f (\x. c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACTION_IMP_QUOTIENT_MAP = prove
 (`!r s t:real^N->bool.
    retraction (s,t) r
    ==> !u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ r x IN u} <=>
                 open_in (subtopology euclidean t) u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; SUBSET_REFL; IMAGE_ID]);;

let RETRACT_OF_LOCALLY_CONNECTED = prove
 (`!s t:real^N->bool.
        s retract_of t /\ locally connected t ==> locally connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 2 o CONJUNCTS o GEN_REWRITE_RULE I
   [RETRACTION]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC RETRACTION_IMP_QUOTIENT_MAP THEN
  ASM_MESON_TAC[RETRACTION]);;

let RETRACT_OF_LOCALLY_PATH_CONNECTED = prove
 (`!s t:real^N->bool.
        s retract_of t /\ locally path_connected t
        ==> locally path_connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 2 o CONJUNCTS o GEN_REWRITE_RULE I
   [RETRACTION]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC RETRACTION_IMP_QUOTIENT_MAP THEN
  ASM_MESON_TAC[RETRACTION]);;

let RETRACT_OF_LOCALLY_COMPACT = prove
 (`!s t:real^N->bool.
        locally compact s /\ t retract_of s ==> locally compact t`,
  MESON_TAC[CLOSED_IN_RETRACT; LOCALLY_COMPACT_CLOSED_IN]);;

let RETRACT_OF_PCROSS = prove
 (`!s:real^M->bool s' t:real^N->bool t'.
        s retract_of s' /\ t retract_of t'
        ==> (s PCROSS t) retract_of (s' PCROSS t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  REWRITE_TAC[retract_of; retraction; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:real^M->real^M` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z. pastecart ((f:real^M->real^M) (fstcart z))
                            ((g:real^N->real^N) (sndcart z))` THEN
  REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let RETRACT_OF_PCROSS_EQ = prove
 (`!s s':real^M->bool t t':real^N->bool.
        s PCROSS t retract_of s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/
        s retract_of s' /\ t retract_of t'`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`s:real^M->bool = {}`;
    `s':real^M->bool = {}`;
    `t:real^N->bool = {}`;
    `t':real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; RETRACT_OF_EMPTY; PCROSS_EQ_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[RETRACT_OF_PCROSS] THEN
  REWRITE_TAC[retract_of; retraction; SUBSET; FORALL_IN_PCROSS;
              FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^(M,N)finite_sum->real^(M,N)finite_sum`
    STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `?b:real^N. b IN t` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x. fstcart((r:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart x b))` THEN
    ASM_SIMP_TAC[FSTCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `?a:real^M. a IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x. sndcart((r:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart a x))` THEN
    ASM_SIMP_TAC[SNDCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS;
                    MEMBER_NOT_EMPTY]]]);;

let HOMOTOPIC_INTO_RETRACT = prove
 (`!f:real^M->real^N g s t u.
        IMAGE f s SUBSET t /\ IMAGE g s SUBSET t /\ t retract_of u /\
        homotopic_with (\x. T) (s,u) f g
        ==> homotopic_with (\x. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  SIMP_TAC[HOMOTOPIC_WITH; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^(1,M)finite_sum->real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `(r:real^N->real^N) o (h:real^(1,M)finite_sum->real^N)` THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Absolute retracts (AR), absolute neighbourhood retracts (ANR) and also    *)
(* Euclidean neighbourhood retracts (ENR). We define AR and ANR by           *)
(* specializing the standard definitions for a set in R^n to embedding in    *)
(* spaces inside R^{n+1}. This turns out to be sufficient (since any set in  *)
(* R^n can be embedded as a closed subset of a convex subset of R^{n+1}) to  *)
(* derive the usual definitions, but we need to split them into two          *)
(* implications because of the lack of type quantifiers. Then ENR turns out  *)
(* to be equivalent to ANR plus local compactness.                           *)
(* ------------------------------------------------------------------------- *)

let AR = new_definition
 `AR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> s' retract_of u`;;

let ANR = new_definition
 `ANR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> ?t. open_in (subtopology euclidean u) t /\
                        s' retract_of t`;;

let ENR = new_definition
 `ENR s <=> ?u. open u /\ s retract_of u`;;

(* ------------------------------------------------------------------------- *)
(* First, show that we do indeed get the "usual" properties of ARs and ANRs. *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ABSOLUTE_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        AR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(g:real^N->real^(N,1)finite_sum) o (f:real^M->real^N)`;
    `c:real^(N,1)finite_sum->bool`; `u:real^M->bool`; `t:real^M->bool`]
        DUGUNDJI) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^(N,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^(N,1)finite_sum->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(h:real^(N,1)finite_sum->real^N) o r o
              (f':real^M->real^(N,1)finite_sum)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_IMP_ABSOLUTE_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        AR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> s' retract_of u`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `u:real^M->bool`; `s':real^M->bool`;
                 `s:real^N->bool`] AR_IMP_ABSOLUTE_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^M->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^M) o (h':real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_IMP_ABSOLUTE_RETRACT_UNIV = prove
 (`!s:real^N->bool s':real^M->bool.
    AR s /\ s homeomorphic s' /\ closed s' ==> s' retract_of (:real^M)`,
  MESON_TAC[AR_IMP_ABSOLUTE_RETRACT;
            TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV; OPEN_IN; CLOSED_IN]);;

let ABSOLUTE_EXTENSOR_IMP_AR = prove
 (`!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)
        ==> AR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPECL
    [`h:real^(N,1)finite_sum->real^N`;
     `u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(X_CHOOSE_THEN
    `h':real^(N,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^(N,1)finite_sum) o
              (h':real^(N,1)finite_sum->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_EQ_ABSOLUTE_EXTENSOR = prove
 (`!s:real^N->bool.
        AR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[AR_IMP_ABSOLUTE_EXTENSOR; ABSOLUTE_EXTENSOR_IMP_AR]);;

let AR_IMP_RETRACT = prove
 (`!s u:real^N->bool.
        AR s /\ closed_in (subtopology euclidean u) s ==> s retract_of u`,
  MESON_TAC[AR_IMP_ABSOLUTE_RETRACT; HOMEOMORPHIC_REFL]);;

let HOMEOMORPHIC_ARNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (AR s <=> AR t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t /\ AR t ==> AR s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
      AR_IMP_ABSOLUTE_RETRACT)) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `s:real^M->bool` THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[lemma]);;

let AR_TRANSLATION = prove
 (`!a:real^N s. AR(IMAGE (\x. a + x) s) <=> AR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [AR_TRANSLATION];;

let AR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (AR(IMAGE f s) <=> AR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [AR_LINEAR_IMAGE_EQ];;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
                  g continuous_on v /\ IMAGE g v SUBSET s /\
                  !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN
   `d:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(g:real^N->real^(N,1)finite_sum) o (f:real^M->real^N)`;
    `c:real^(N,1)finite_sum->bool`; `u:real^M->bool`; `t:real^M->bool`]
        DUGUNDJI) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^(N,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^(N,1)finite_sum->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN
  EXISTS_TAC `{x | x IN u /\ (f':real^M->real^(N,1)finite_sum) x IN d}` THEN
  EXISTS_TAC `(h:real^(N,1)finite_sum->real^N) o r o
              (f':real^M->real^(N,1)finite_sum)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN ASM_MESON_TAC[];
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v. open_in (subtopology euclidean u) v /\
                s' retract_of v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `u:real^M->bool`; `s':real^M->bool`;
                `s:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^M->real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^M) o (h':real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = prove
 (`!s:real^N->bool s':real^M->bool.
    ANR s /\ s homeomorphic s' /\ closed s' ==> ?v. open v /\ s' retract_of v`,
  MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT;
            TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV; OPEN_IN; CLOSED_IN]);;

let ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR = prove
 (`!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)
        ==> ANR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPECL
    [`h:real^(N,1)finite_sum->real^N`;
     `u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^(N,1)finite_sum->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^(N,1)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^(N,1)finite_sum) o
              (h':real^(N,1)finite_sum->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = prove
 (`!s:real^N->bool.
        ANR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR;
           ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR]);;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s' SUBSET v /\ v SUBSET w /\ s' retract_of w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z. open_in (subtopology euclidean u) z /\
                    (s':real^M->bool) retract_of z`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`s':real^M->bool`; `u DIFF z:real^M->bool`; `u:real^M->bool`]
    SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL; CLOSED_IN_DIFF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `v:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF w:real^M->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] RETRACT_OF_SUBSET)) THEN
  ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v w g. open_in (subtopology euclidean u) v /\
                    closed_in (subtopology euclidean u) w /\
                    t SUBSET v /\ v SUBSET w /\
                    g continuous_on w /\ IMAGE g w SUBSET s /\
                    !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
          g continuous_on v /\ IMAGE g v SUBSET s /\
          !x. x IN t ==> g x = (f:real^M->real^N) x`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`t:real^M->bool`; `u DIFF v:real^M->bool`; `u:real^M->bool`]
    SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL; CLOSED_IN_DIFF] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `w:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF z:real^M->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  EXISTS_TAC `g:real^M->real^N` THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let ANR_IMP_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v. open_in (subtopology euclidean u) v /\
                s retract_of v`,
  MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; HOMEOMORPHIC_REFL]);;

let ANR_IMP_CLOSED_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s SUBSET v /\ v SUBSET w /\ s retract_of w`,
  MESON_TAC[ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT;
            HOMEOMORPHIC_REFL]);;

let HOMEOMORPHIC_ANRNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ANR s <=> ANR t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t /\ ANR t ==> ANR s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
      ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT)) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `s:real^M->bool` THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[lemma]);;

let ANR_TRANSLATION = prove
 (`!a:real^N s. ANR(IMAGE (\x. a + x) s) <=> ANR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [ANR_TRANSLATION];;

let ANR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ANR(IMAGE f s) <=> ANR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [ANR_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Analogous properties of ENRs.                                             *)
(* ------------------------------------------------------------------------- *)

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^M->bool s':real^N->bool u.
        ENR s /\ s homeomorphic s' /\ s' SUBSET u
        ==> ?t'. open_in (subtopology euclidean u) t' /\ s' retract_of t'`,
  REWRITE_TAC[ENR; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`X:real^M->bool`; `Y:real^N->bool`;
    `K:real^N->bool`; `U:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `locally compact (Y:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RETRACT_OF_LOCALLY_COMPACT;
                  OPEN_IMP_LOCALLY_COMPACT; HOMEOMORPHIC_LOCAL_COMPACTNESS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?W:real^N->bool.
        open_in (subtopology euclidean K) W /\
        closed_in (subtopology euclidean W) Y`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC o
        MATCH_MP LOCALLY_COMPACT_CLOSED_IN_OPEN) THEN
    EXISTS_TAC `K INTER W:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; CLOSED_IN_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `W:real^N->bool`; `Y:real^N->bool`]
        TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN W /\ (h:real^N->real^M) x IN U}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSET_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; retract_of; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^M->real^N) o r o (h:real^N->real^M)` THEN
  SUBGOAL_THEN
   `(W:real^N->bool) SUBSET K /\ Y SUBSET W`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
  REWRITE_TAC[IMAGE_o] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = prove
 (`!s:real^M->bool s':real^N->bool.
        ENR s /\ s homeomorphic s' ==> ?t'. open t' /\ s' retract_of t'`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MATCH_MP_TAC ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT THEN
  ASM_MESON_TAC[SUBSET_UNIV]);;

let HOMEOMORPHIC_ENRNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ENR s <=> ENR t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ENR] THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`]
        ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV);
    MP_TAC(ISPECL [`t:real^N->bool`; `s:real^M->bool`]
        ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM]);;

let ENR_TRANSLATION = prove
 (`!a:real^N s. ENR(IMAGE (\x. a + x) s) <=> ENR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [ENR_TRANSLATION];;

let ENR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ENR(IMAGE f s) <=> ENR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [ENR_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Some relations among the concepts. We also relate AR to being a retract   *)
(* of UNIV, which is often a more convenient proxy in the closed case.       *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ANR = prove
 (`!s:real^N->bool. AR s ==> ANR s`,
  REWRITE_TAC[AR; ANR] THEN MESON_TAC[OPEN_IN_REFL; CLOSED_IN_IMP_SUBSET]);;

let ENR_IMP_ANR = prove
 (`!s:real^N->bool. ENR s ==> ANR s`,
  REWRITE_TAC[ANR] THEN
  MESON_TAC[ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; CLOSED_IN_IMP_SUBSET]);;

let ENR_ANR = prove
 (`!s:real^N->bool. ENR s <=> ANR s /\ locally compact s`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC[ENR_IMP_ANR] THENL
   [ASM_MESON_TAC[ENR; RETRACT_OF_LOCALLY_COMPACT; OPEN_IMP_LOCALLY_COMPACT];
    SUBGOAL_THEN
     `?t. closed t /\
          (s:real^N->bool) homeomorphic (t:real^(N,1)finite_sum->bool)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LOCALLY_COMPACT_HOMEOMORPHIC_CLOSED THEN
      ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`(:real^(N,1)finite_sum)`; `t:real^(N,1)finite_sum->bool`]) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; GSYM OPEN_IN] THEN
      REWRITE_TAC[GSYM ENR] THEN ASM_MESON_TAC[HOMEOMORPHIC_ENRNESS]]]);;

let AR_ANR = prove
 (`!s:real^N->bool. AR s <=> ANR s /\ contractible s /\ ~(s = {})`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[AR_IMP_ANR] THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[AR; HOMEOMORPHIC_EMPTY; RETRACT_OF_EMPTY;
           FORALL_UNWIND_THM2; CLOSED_IN_EMPTY; UNIV_NOT_EMPTY]] THEN
    SUBGOAL_THEN
     `?c s':real^(N,1)finite_sum->bool.
          convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
          (s:real^N->bool) homeomorphic s'`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
      REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AR]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM; HOMEOMORPHIC_CONTRACTIBLE;
                  RETRACT_OF_CONTRACTIBLE; CONVEX_IMP_CONTRACTIBLE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; homotopic_with] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `h:real^(1,N)finite_sum->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[AR_EQ_ABSOLUTE_EXTENSOR] THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^(N,1)finite_sum->real^N`; `w:real^(N,1)finite_sum->bool`;
    `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o  ISPECL
    [`f:real^(N,1)finite_sum->real^N`; `w:real^(N,1)finite_sum->bool`;
     `t:real^(N,1)finite_sum->bool`]  o
    REWRITE_RULE[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
    [`u:real^(N,1)finite_sum->bool`; `g:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`t:real^(N,1)finite_sum->bool`; `w DIFF u:real^(N,1)finite_sum->bool`;
    `w:real^(N,1)finite_sum->bool`] SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`v:real^(N,1)finite_sum->bool`; `v':real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`t:real^(N,1)finite_sum->bool`; `w DIFF v:real^(N,1)finite_sum->bool`;
    `w:real^(N,1)finite_sum->bool`; `vec 0:real^1`; `vec 1:real^1`]
        URYSOHN_LOCAL) THEN
  ASM_SIMP_TAC[SEGMENT_1; CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS] THEN
  X_GEN_TAC `e:real^(N,1)finite_sum->real^1` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x. if (x:real^(N,1)finite_sum) IN w DIFF v then a
        else (h:real^(1,N)finite_sum->real^N) (pastecart (e x) (g x))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `w:real^(N,1)finite_sum->bool = (w DIFF v) UNION (w DIFF v')`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th ->
        GEN_REWRITE_TAC RAND_CONV [th] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
        REWRITE_TAC[GSYM th]) THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL; CONTINUOUS_ON_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN RULE_ASSUM_TAC
     (REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS]) THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    COND_CASES_TAC THEN ASM SET_TAC[]]);;

let ANR_RETRACT_OF_ANR = prove
 (`!s t:real^N->bool. ANR t /\ s retract_of t ==> ANR s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(N,1)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:real^N->real^N) o (g:real^(N,1)finite_sum->real^N)` THEN
  ASM_SIMP_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let AR_RETRACT_OF_AR = prove
 (`!s t:real^N->bool. AR t /\ s retract_of t ==> AR s`,
  REWRITE_TAC[AR_ANR] THEN
  MESON_TAC[ANR_RETRACT_OF_ANR; RETRACT_OF_CONTRACTIBLE; RETRACT_OF_EMPTY]);;

let ENR_RETRACT_OF_ENR = prove
 (`!s t:real^N->bool. ENR t /\ s retract_of t ==> ENR s`,
  REWRITE_TAC[ENR] THEN MESON_TAC[RETRACT_OF_TRANS]);;

let RETRACT_OF_UNIV = prove
 (`!s:real^N->bool. s retract_of (:real^N) <=> AR s /\ closed s`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC AR_RETRACT_OF_AR THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTE_EXTENSOR_IMP_AR THEN
    MESON_TAC[DUGUNDJI; CONVEX_UNIV; UNIV_NOT_EMPTY];
    MATCH_MP_TAC RETRACT_OF_CLOSED THEN ASM_MESON_TAC[CLOSED_UNIV];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        AR_IMP_ABSOLUTE_RETRACT)) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; HOMEOMORPHIC_REFL]]);;

let COMPACT_AR = prove
 (`!s. compact s /\ AR s <=> compact s /\ s retract_of (:real^N)`,
  REWRITE_TAC[RETRACT_OF_UNIV] THEN MESON_TAC[COMPACT_IMP_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* More properties of ARs, ANRs and ENRs.                                    *)
(* ------------------------------------------------------------------------- *)

let NOT_AR_EMPTY = prove
 (`~(AR({}:real^N->bool))`,
  REWRITE_TAC[AR_ANR]);;

let ENR_EMPTY = prove
 (`ENR {}`,
  REWRITE_TAC[ENR; RETRACT_OF_EMPTY] THEN MESON_TAC[OPEN_EMPTY]);;

let ANR_EMPTY = prove
 (`ANR {}`,
  SIMP_TAC[ENR_EMPTY; ENR_IMP_ANR]);;

let CONVEX_IMP_AR = prove
 (`!s:real^N->bool. convex s /\ ~(s = {}) ==> AR s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTE_EXTENSOR_IMP_AR THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DUGUNDJI THEN
  ASM_REWRITE_TAC[]);;

let CONVEX_IMP_ANR = prove
 (`!s:real^N->bool. convex s ==> ANR s`,
  MESON_TAC[ANR_EMPTY; CONVEX_IMP_AR; AR_IMP_ANR]);;

let ENR_CONVEX_CLOSED = prove
 (`!s:real^N->bool. closed s /\ convex s ==> ENR s`,
  MESON_TAC[CONVEX_IMP_ANR; ENR_ANR; CLOSED_IMP_LOCALLY_COMPACT]);;

let AR_UNIV = prove
 (`AR(:real^N)`,
  MESON_TAC[CONVEX_IMP_AR; CONVEX_UNIV; UNIV_NOT_EMPTY]);;

let ANR_UNIV = prove
 (`ANR(:real^N)`,
  MESON_TAC[CONVEX_IMP_ANR; CONVEX_UNIV]);;

let ENR_UNIV = prove
 (`ENR(:real^N)`,
  MESON_TAC[ENR_CONVEX_CLOSED; CONVEX_UNIV; CLOSED_UNIV]);;

let AR_SING = prove
 (`!a:real^N. AR {a}`,
  SIMP_TAC[CONVEX_IMP_AR; CONVEX_SING; NOT_INSERT_EMPTY]);;

let ANR_SING = prove
 (`!a:real^N. ANR {a}`,
  SIMP_TAC[AR_IMP_ANR; AR_SING]);;

let ENR_SING = prove
 (`!a:real^N. ENR {a}`,
  SIMP_TAC[ENR_ANR; ANR_SING; CLOSED_IMP_LOCALLY_COMPACT; CLOSED_SING]);;

let ANR_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ ANR t ==> ANR s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^(N,1)finite_sum->real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^(N,1)finite_sum->bool`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN w /\ (g:real^(N,1)finite_sum->real^N) x IN s}` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `w:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN ASM_MESON_TAC[];
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]]);;

let ENR_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ ENR t ==> ENR s`,
  REWRITE_TAC[ENR_ANR] THEN MESON_TAC[ANR_OPEN_IN; LOCALLY_OPEN_SUBSET]);;

let ANR_NEIGHBORHOOD_RETRACT = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ open_in (subtopology euclidean u) t /\ ANR u
        ==> ANR s`,
  MESON_TAC[ANR_OPEN_IN; ANR_RETRACT_OF_ANR]);;

let ENR_NEIGHBORHOOD_RETRACT = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ open_in (subtopology euclidean u) t /\ ENR u
        ==> ENR s`,
  MESON_TAC[ENR_OPEN_IN; ENR_RETRACT_OF_ENR]);;

let ANR_RELATIVE_INTERIOR = prove
 (`!s. ANR(s) ==> ANR(relative_interior s)`,
  MESON_TAC[OPEN_IN_SET_RELATIVE_INTERIOR; ANR_OPEN_IN]);;

let ANR_DELETE = prove
 (`!s a:real^N. ANR(s) ==> ANR(s DELETE a)`,
  MESON_TAC[ANR_OPEN_IN; OPEN_IN_DELETE; OPEN_IN_REFL]);;

let ENR_RELATIVE_INTERIOR = prove
 (`!s. ENR(s) ==> ENR(relative_interior s)`,
  MESON_TAC[OPEN_IN_SET_RELATIVE_INTERIOR; ENR_OPEN_IN]);;

let ENR_DELETE = prove
 (`!s a:real^N. ENR(s) ==> ENR(s DELETE a)`,
  MESON_TAC[ENR_OPEN_IN; OPEN_IN_DELETE; OPEN_IN_REFL]);;

let OPEN_IMP_ENR = prove
 (`!s:real^N->bool. open s ==> ENR s`,
  REWRITE_TAC[OPEN_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MESON_TAC[ENR_UNIV; ENR_OPEN_IN]);;

let OPEN_IMP_ANR = prove
 (`!s:real^N->bool. open s ==> ANR s`,
  SIMP_TAC[OPEN_IMP_ENR; ENR_IMP_ANR]);;

let ANR_BALL = prove
 (`!a:real^N r. ANR(ball(a,r))`,
  MESON_TAC[CONVEX_IMP_ANR; CONVEX_BALL]);;

let ENR_BALL = prove
 (`!a:real^N r. ENR(ball(a,r))`,
  SIMP_TAC[ENR_ANR; ANR_BALL; OPEN_IMP_LOCALLY_COMPACT; OPEN_BALL]);;

let AR_BALL = prove
 (`!a:real^N r. AR(ball(a,r)) <=> &0 < r`,
  SIMP_TAC[AR_ANR; BALL_EQ_EMPTY; ANR_BALL; CONVEX_BALL;
           CONVEX_IMP_CONTRACTIBLE; REAL_NOT_LE]);;

let ANR_CBALL = prove
 (`!a:real^N r. ANR(cball(a,r))`,
  MESON_TAC[CONVEX_IMP_ANR; CONVEX_CBALL]);;

let ENR_CBALL = prove
 (`!a:real^N r. ENR(cball(a,r))`,
  SIMP_TAC[ENR_ANR; ANR_CBALL; CLOSED_IMP_LOCALLY_COMPACT; CLOSED_CBALL]);;

let AR_CBALL = prove
 (`!a:real^N r. AR(cball(a,r)) <=> &0 <= r`,
  SIMP_TAC[AR_ANR; CBALL_EQ_EMPTY; ANR_CBALL; CONVEX_CBALL;
           CONVEX_IMP_CONTRACTIBLE; REAL_NOT_LT]);;

let ANR_INTERVAL = prove
 (`(!a b:real^N. ANR(interval[a,b])) /\ (!a b:real^N. ANR(interval(a,b)))`,
  SIMP_TAC[CONVEX_IMP_ANR; CONVEX_INTERVAL; CLOSED_INTERVAL;
           OPEN_IMP_ANR; OPEN_INTERVAL]);;

let ENR_INTERVAL = prove
 (`(!a b:real^N. ENR(interval[a,b])) /\ (!a b:real^N. ENR(interval(a,b)))`,
  SIMP_TAC[ENR_CONVEX_CLOSED; CONVEX_INTERVAL; CLOSED_INTERVAL;
           OPEN_IMP_ENR; OPEN_INTERVAL]);;

let AR_INTERVAL = prove
 (`(!a b:real^N. AR(interval[a,b]) <=> ~(interval[a,b] = {})) /\
   (!a b:real^N. AR(interval(a,b)) <=> ~(interval(a,b) = {}))`,
  SIMP_TAC[AR_ANR; ANR_INTERVAL; CONVEX_IMP_CONTRACTIBLE; CONVEX_INTERVAL]);;

let ANR_INTERIOR = prove
 (`!s. ANR(interior s)`,
  SIMP_TAC[OPEN_INTERIOR; OPEN_IMP_ANR]);;

let ENR_INTERIOR = prove
 (`!s. ENR(interior s)`,
  SIMP_TAC[OPEN_INTERIOR; OPEN_IMP_ENR]);;

let AR_IMP_CONTRACTIBLE = prove
 (`!s:real^N->bool. AR s ==> contractible s`,
  SIMP_TAC[AR_ANR]);;

let ENR_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. ENR s ==> locally compact s`,
  SIMP_TAC[ENR_ANR]);;

let ANR_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. ANR s ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM; HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS;
                RETRACT_OF_LOCALLY_PATH_CONNECTED;
                CONVEX_IMP_LOCALLY_PATH_CONNECTED;
                LOCALLY_OPEN_SUBSET]);;

let ANR_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. ANR s ==> locally connected s`,
  SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let AR_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. AR s ==> locally path_connected s`,
  SIMP_TAC[AR_IMP_ANR; ANR_IMP_LOCALLY_PATH_CONNECTED]);;

let AR_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. AR s ==> locally connected s`,
  SIMP_TAC[AR_IMP_LOCALLY_PATH_CONNECTED;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let ENR_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. ENR s ==> locally path_connected s`,
  SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED; ENR_IMP_ANR]);;

let ENR_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. ENR s ==> locally connected s`,
  SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED; ENR_IMP_ANR]);;

let COUNTABLE_ANR_COMPONENTS = prove
 (`!s:real^N->bool. ANR s ==> COUNTABLE(components s)`,
  SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED; COUNTABLE_COMPONENTS]);;

let COUNTABLE_ANR_CONNECTED_COMPONENTS = prove
 (`!s:real^N->bool t.
        ANR s ==> COUNTABLE {connected_component s x | x IN t}`,
  SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED; COUNTABLE_CONNECTED_COMPONENTS]);;

let COUNTABLE_ANR_PATH_COMPONENTS = prove
 (`!s:real^N->bool t.
        ANR s ==> COUNTABLE {path_component s x | x IN t}`,
  SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED; COUNTABLE_PATH_COMPONENTS]);;

let FINITE_ANR_COMPONENTS = prove
 (`!s:real^N->bool. ANR s /\ compact s ==> FINITE(components s)`,
  SIMP_TAC[FINITE_COMPONENTS; ANR_IMP_LOCALLY_CONNECTED]);;

let FINITE_ENR_COMPONENTS = prove
 (`!s:real^N->bool. ENR s /\ compact s ==> FINITE(components s)`,
  SIMP_TAC[FINITE_COMPONENTS; ENR_IMP_LOCALLY_CONNECTED]);;

let ANR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool. ANR s /\ ANR t ==> ANR(s PCROSS t)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^((M,N)finite_sum,1)finite_sum->real^(M,N)finite_sum`;
    `u:real^((M,N)finite_sum,1)finite_sum->bool`;
    `c:real^((M,N)finite_sum,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`fstcart o (f:real^((M,N)finite_sum,1)finite_sum->real^(M,N)finite_sum)`;
    `u:real^((M,N)finite_sum,1)finite_sum->bool`;
    `c:real^((M,N)finite_sum,1)finite_sum->bool`;
    `s:real^M->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  MP_TAC(ISPECL
   [`sndcart o (f:real^((M,N)finite_sum,1)finite_sum->real^(M,N)finite_sum)`;
    `u:real^((M,N)finite_sum,1)finite_sum->bool`;
    `c:real^((M,N)finite_sum,1)finite_sum->bool`;
    `t:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART; IMAGE_o] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; PCROSS; IN_ELIM_THM]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SNDCART_PASTECART]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`w2:real^((M,N)finite_sum,1)finite_sum->bool`;
    `h:real^((M,N)finite_sum,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FSTCART_PASTECART]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`w1:real^((M,N)finite_sum,1)finite_sum->bool`;
    `g:real^((M,N)finite_sum,1)finite_sum->real^M`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`w1 INTER w2:real^((M,N)finite_sum,1)finite_sum->bool`;
    `\x:real^((M,N)finite_sum,1)finite_sum.
        pastecart (g x:real^M) (h x:real^N)`] THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER; o_DEF; PASTECART_IN_PCROSS;
               PASTECART_FST_SND] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]);;

let ANR_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        ANR(s PCROSS t) <=> s = {} \/ t = {} \/ ANR s /\ ANR t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; ANR_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; ANR_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[ANR_PCROSS] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ANR ((s:real^M->bool) PCROSS {b:real^N})` MP_TAC THENL
     [ALL_TAC; MESON_TAC[HOMEOMORPHIC_PCROSS_SING; HOMEOMORPHIC_ANRNESS]];
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ANR ({a:real^M} PCROSS (t:real^N->bool))` MP_TAC THENL
     [ALL_TAC; MESON_TAC[HOMEOMORPHIC_PCROSS_SING; HOMEOMORPHIC_ANRNESS]]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ANR_RETRACT_OF_ANR)) THEN
  REWRITE_TAC[retract_of; retraction] THENL
   [EXISTS_TAC`\x:real^(M,N)finite_sum. pastecart (fstcart x) (b:real^N)`;
    EXISTS_TAC`\x:real^(M,N)finite_sum. pastecart (a:real^M) (sndcart x)`] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_PCROSS; FORALL_IN_IMAGE; IN_SING;
               FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
               CONTINUOUS_ON_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART;
               LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST]);;

let AR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool. AR s /\ AR t ==> AR(s PCROSS t)`,
  SIMP_TAC[AR_ANR; ANR_PCROSS; CONTRACTIBLE_PCROSS; PCROSS_EQ_EMPTY]);;

let ENR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool. ENR s /\ ENR t ==> ENR(s PCROSS t)`,
  SIMP_TAC[ENR_ANR; ANR_PCROSS; LOCALLY_COMPACT_PCROSS]);;

let ENR_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        ENR(s PCROSS t) <=> s = {} \/ t = {} \/ ENR s /\ ENR t`,
  REWRITE_TAC[ENR_ANR; ANR_PCROSS_EQ; LOCALLY_COMPACT_PCROSS_EQ] THEN
  CONV_TAC TAUT);;

let AR_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        AR(s PCROSS t) <=> AR s /\ AR t /\ ~(s = {}) /\ ~(t = {})`,
  SIMP_TAC[AR_ANR; ANR_PCROSS_EQ; CONTRACTIBLE_PCROSS_EQ; PCROSS_EQ_EMPTY] THEN
  CONV_TAC TAUT);;

let AR_CLOSED_UNION_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s) /\ AR(t) /\ AR(s INTER t)
        ==> AR(s UNION t)`,
  let lemma = prove
   (`!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        AR s /\ AR t /\ AR(s INTER t)
        ==> (s UNION t) retract_of u`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `s INTER t:real^N->bool = {}` THENL
     [ASM_MESON_TAC[NOT_AR_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET u /\ t SUBSET u` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [`s' = {x:real^N | x IN u /\ setdist({x},s) <= setdist({x},t)}`;
      `t' = {x:real^N | x IN u /\ setdist({x},t) <= setdist({x},s)}`;
      `w = {x:real^N | x IN u /\ setdist({x},s) = setdist({x},t)}`] THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean u) (s':real^N->bool) /\
                  closed_in (subtopology euclidean u) (t':real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN REWRITE_TAC[SET_RULE
       `a <= drop(lift x) <=> lift x IN {x | a <= drop x}`] THEN
      REWRITE_TAC[LIFT_DROP; LIFT_SUB] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      SIMP_TAC[CLOSED_SING; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST;
               drop; CLOSED_HALFSPACE_COMPONENT_LE;
               REWRITE_RULE[real_ge] CLOSED_HALFSPACE_COMPONENT_GE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(s:real^N->bool) SUBSET s' /\ (t:real^N->bool) SUBSET t'`
    STRIP_ASSUME_TAC THENL
      [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
       SIMP_TAC[SUBSET; IN_ELIM_THM; SETDIST_SING_IN_SET; SETDIST_POS_LE] THEN
       ASM SET_TAC[];
       ALL_TAC] THEN
    SUBGOAL_THEN `(s INTER t:real^N->bool) retract_of w` MP_TAC THENL
     [MATCH_MP_TAC AR_IMP_ABSOLUTE_RETRACT THEN
      EXISTS_TAC `s INTER t:real^N->bool` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_REFL] THEN
      MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
      CONJ_TAC THENL [EXPAND_TAC "w"; ASM SET_TAC[]] THEN
      SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; SETDIST_SING_IN_SET] THEN
      ASM SET_TAC[];
      GEN_REWRITE_TAC LAND_CONV [retract_of] THEN
      REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `r0:real^N->real^N` THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `!x:real^N. x IN w ==> (x IN s <=> x IN t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> EQ_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC[SETDIST_SING_IN_SET] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&0 = setdist p <=> setdist p = &0`] THEN
      MATCH_MP_TAC(SET_RULE
       `~(s = {}) /\ (p <=> s = {} \/ x IN s) ==> p ==> x IN s`) THEN
      (CONJ_TAC THENL
       [ASM SET_TAC[]; MATCH_MP_TAC SETDIST_EQ_0_CLOSED_IN]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s' INTER t':real^N->bool = w` ASSUME_TAC THENL
     [ASM SET_TAC[REAL_LE_ANTISYM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `closed_in (subtopology euclidean u) (w:real^N->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[CLOSED_IN_INTER]; ALL_TAC] THEN
    ABBREV_TAC `r = \x:real^N. if x IN w then r0 x else x` THEN
    SUBGOAL_THEN
     `IMAGE (r:real^N->real^N) (w UNION s) SUBSET s /\
      IMAGE (r:real^N->real^N) (w UNION t) SUBSET t`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(r:real^N->real^N) continuous_on  (w UNION s UNION t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?g:real^N->real^N.
          g continuous_on u /\
          IMAGE g u SUBSET s /\
          !x. x IN w UNION s ==> g x = r x`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC AR_IMP_ABSOLUTE_EXTENSOR THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; IN_UNION];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?h:real^N->real^N.
          h continuous_on u /\
          IMAGE h u SUBSET t /\
          !x. x IN w UNION t ==> h x = r x`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC AR_IMP_ABSOLUTE_EXTENSOR THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; IN_UNION];
      ALL_TAC] THEN
    REWRITE_TAC[retract_of; retraction] THEN
    EXISTS_TAC `\x. if x IN s' then (g:real^N->real^N) x else h x` THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ALL_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN ASM SET_TAC[];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[IN_UNION; COND_ID] THENL
       [COND_CASES_TAC THENL [EXPAND_TAC "r"; ASM SET_TAC[]];
        COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        TRANS_TAC EQ_TRANS `(r:real^N->real^N) x` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "r"]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
    SUBGOAL_THEN
     `u:real^N->bool = s' UNION t'`
     (fun th -> ONCE_REWRITE_TAC[th] THEN
                MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
                REWRITE_TAC[GSYM th])
    THENL [ASM SET_TAC[REAL_LE_TOTAL]; ASM_SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]) THEN
    REWRITE_TAC[TAUT `p /\ ~p \/ q /\ p <=> p /\ q`] THEN
    ASM_SIMP_TAC[GSYM IN_INTER; IN_UNION]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `c:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`f:real^N->real^(N,1)finite_sum`; `g:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean u)
              {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN s} /\
    closed_in (subtopology euclidean u)
              {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN t}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_TRANS THEN
    EXISTS_TAC `c:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN s} UNION
    {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN t} = c`
   (fun th -> SUBST1_TAC(SYM th)) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `AR(s:real^N->bool)`;
    UNDISCH_TAC `AR(t:real^N->bool)`;
    UNDISCH_TAC `AR(s INTER t:real^N->bool)`] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  REWRITE_TAC[homeomorphic; homeomorphism] THEN MAP_EVERY EXISTS_TAC
   [`f:real^N->real^(N,1)finite_sum`; `g:real^(N,1)finite_sum->real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))) THEN
  ASM SET_TAC[]);;

let ANR_CLOSED_UNION_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ANR(s) /\ ANR(t) /\ ANR(s INTER t)
        ==> ANR(s UNION t)`,
  let lemma = prove
   (`!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        ANR s /\ ANR t /\ ANR(s INTER t)
        ==> ?v. open_in (subtopology euclidean u) v /\
                (s UNION t) retract_of v`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[UNION_EMPTY] THENL
     [ASM_MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; HOMEOMORPHIC_REFL];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real^N->bool = {}` THEN ASM_REWRITE_TAC[UNION_EMPTY] THENL
     [ASM_MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; HOMEOMORPHIC_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET u /\ t SUBSET u`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [`s' = {x:real^N | x IN u /\ setdist({x},s) <= setdist({x},t)}`;
      `t' = {x:real^N | x IN u /\ setdist({x},t) <= setdist({x},s)}`;
      `w = {x:real^N | x IN u /\ setdist({x},s) = setdist({x},t)}`] THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean u) (s':real^N->bool) /\
                  closed_in (subtopology euclidean u) (t':real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN REWRITE_TAC[SET_RULE
       `a <= drop(lift x) <=> lift x IN {x | a <= drop x}`] THEN
      REWRITE_TAC[LIFT_DROP; LIFT_SUB] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      SIMP_TAC[CLOSED_SING; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST;
               drop; CLOSED_HALFSPACE_COMPONENT_LE;
               REWRITE_RULE[real_ge] CLOSED_HALFSPACE_COMPONENT_GE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(s:real^N->bool) SUBSET s' /\ (t:real^N->bool) SUBSET t'`
    STRIP_ASSUME_TAC THENL
      [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
       SIMP_TAC[SUBSET; IN_ELIM_THM; SETDIST_SING_IN_SET; SETDIST_POS_LE] THEN
       ASM SET_TAC[];
       ALL_TAC] THEN
    SUBGOAL_THEN `s' UNION t':real^N->bool = u` ASSUME_TAC THENL
     [ASM SET_TAC[REAL_LE_TOTAL]; ALL_TAC] THEN
    SUBGOAL_THEN `w SUBSET s' /\ (w:real^N->bool) SUBSET t'`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?w' w0. open_in (subtopology euclidean w) w' /\
               closed_in (subtopology euclidean w) w0 /\
               s INTER t SUBSET w' /\ w' SUBSET w0 /\
               (s INTER t:real^N->bool) retract_of w0`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC ANR_IMP_CLOSED_NEIGHBOURHOOD_RETRACT THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
      CONJ_TAC THENL [EXPAND_TAC "w"; ASM SET_TAC[]] THEN
      SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; SETDIST_SING_IN_SET] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean u) (w:real^N->bool)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `w = s' INTER t':real^N->bool` SUBST1_TAC THENL
       [ASM SET_TAC[REAL_LE_ANTISYM]; ASM_SIMP_TAC[CLOSED_IN_INTER]];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean u) (w0:real^N->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[CLOSED_IN_TRANS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?u0. open_in (subtopology euclidean u) (u0:real^N->bool) /\
           s INTER t SUBSET u0 /\
           u0 INTER w SUBSET w0`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `z:real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      EXISTS_TAC `u INTER z:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
    REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r0:real^N->real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `w0 SUBSET (w:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:real^N. x IN w ==> (x IN s <=> x IN t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> EQ_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC[SETDIST_SING_IN_SET] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&0 = setdist p <=> setdist p = &0`] THEN
      MATCH_MP_TAC(SET_RULE
       `~(s = {}) /\ (p <=> s = {} \/ x IN s) ==> p ==> x IN s`) THEN
      (CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC SETDIST_EQ_0_CLOSED_IN]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `r = \x:real^N. if x IN w0 then r0 x else x` THEN
    SUBGOAL_THEN
     `IMAGE (r:real^N->real^N) (w0 UNION s) SUBSET s /\
      IMAGE (r:real^N->real^N) (w0 UNION t) SUBSET t`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(r:real^N->real^N) continuous_on  (w0 UNION s UNION t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:real^N->real^N`;
                   `s':real^N->bool`;
                   `w0 UNION s:real^N->bool`;
                   `s:real^N->bool`]
          ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
        EXISTS_TAC `u:real^N->bool` THEN ASM_SIMP_TAC[CLOSED_IN_UNION] THEN
        ASM SET_TAC[]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`w1:real^N->bool`; `g:real^N->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`r:real^N->real^N`;
                   `t':real^N->bool`;
                   `w0 UNION t:real^N->bool`;
                   `t:real^N->bool`]
          ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
        EXISTS_TAC `u:real^N->bool` THEN ASM_SIMP_TAC[CLOSED_IN_UNION] THEN
        ASM SET_TAC[]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`w2:real^N->bool`; `h:real^N->real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `s' INTER t':real^N->bool = w` ASSUME_TAC THENL
     [ASM SET_TAC[REAL_LE_ANTISYM]; ALL_TAC] THEN
    EXISTS_TAC
     `(w1 DIFF (w DIFF u0)) UNION (w2 DIFF (w DIFF u0)):real^N->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `open_in (subtopology euclidean t') (w2:real^N->bool)` THEN
      UNDISCH_TAC `open_in (subtopology euclidean s') (w1:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `o1:real^N->bool` THEN STRIP_TAC THEN
      X_GEN_TAC `o2:real^N->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[GSYM OPEN_IN_OPEN] THEN
      SUBGOAL_THEN
       `s' INTER o1 DIFF (w DIFF u0) UNION t' INTER o2 DIFF (w DIFF u0)
         :real^N->bool =
        ((u DIFF t') INTER o1 UNION (u DIFF s') INTER o2 UNION
         u INTER o1 INTER o2) DIFF (w DIFF u0)`
      SUBST1_TAC THENL
       [REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
        REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[CLOSED_IN_DIFF] THEN
      REPEAT(MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC) THEN
      MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; OPEN_INTER];
      ALL_TAC] THEN
    REWRITE_TAC[retract_of; retraction] THEN
    EXISTS_TAC `\x. if  x IN s' then g x else (h:real^N->real^N) x` THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ALL_TAC;
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
      ASM SET_TAC[];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[IN_UNION; COND_ID] THENL
       [COND_CASES_TAC THENL [EXPAND_TAC "r"; ASM SET_TAC[]];
        COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        TRANS_TAC EQ_TRANS `(r:real^N->real^N) x` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "r"]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `closed_in (subtopology euclidean u) (s':real^N->bool)` THEN
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
      ASM SET_TAC[];
      UNDISCH_TAC `closed_in (subtopology euclidean u) (t':real^N->bool)` THEN
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
       X_GEN_TAC `x:real^N` THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`)) THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
      ASM SET_TAC[]]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `c:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`f:real^N->real^(N,1)finite_sum`; `g:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean u)
              {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN s} /\
    closed_in (subtopology euclidean u)
              {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN t}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_TRANS THEN
    EXISTS_TAC `c:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN s} UNION
    {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN t} = c`
   (fun th -> SUBST1_TAC(SYM th)) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ANR(s:real^N->bool)`;
    UNDISCH_TAC `ANR(t:real^N->bool)`;
    UNDISCH_TAC `ANR(s INTER t:real^N->bool)`] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  REWRITE_TAC[homeomorphic; homeomorphism] THEN MAP_EVERY EXISTS_TAC
   [`f:real^N->real^(N,1)finite_sum`; `g:real^(N,1)finite_sum->real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))) THEN
  ASM SET_TAC[]);;

let AR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ AR(s) /\ AR(t) /\ AR(s INTER t)
        ==> AR(s UNION t)`,
  MESON_TAC[AR_CLOSED_UNION_LOCAL; CLOSED_SUBSET; SUBSET_UNION]);;

let ANR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ANR(s) /\ ANR(t) /\ ANR(s INTER t)
        ==> ANR(s UNION t)`,
  MESON_TAC[ANR_CLOSED_UNION_LOCAL; CLOSED_SUBSET; SUBSET_UNION]);;

let ENR_CLOSED_UNION_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ENR(s) /\ ENR(t) /\ ENR(s INTER t)
        ==> ENR(s UNION t)`,
  SIMP_TAC[ENR_ANR; ANR_CLOSED_UNION_LOCAL; LOCALLY_COMPACT_CLOSED_UNION]);;

let ENR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ENR(s) /\ ENR(t) /\ ENR(s INTER t)
        ==> ENR(s UNION t)`,
  MESON_TAC[ENR_CLOSED_UNION_LOCAL; CLOSED_SUBSET; SUBSET_UNION]);;

let ABSOLUTE_RETRACT_UNION = prove
 (`!s t. s retract_of (:real^N) /\
         t retract_of (:real^N) /\
         (s INTER t) retract_of (:real^N)
         ==> (s UNION t) retract_of (:real^N)`,
  SIMP_TAC[RETRACT_OF_UNIV; AR_CLOSED_UNION; CLOSED_UNION]);;

let RETRACT_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        (s UNION t) retract_of u /\ (s INTER t) retract_of t
        ==> s retract_of u`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(s UNION t) retract_of (u:real^N->bool)` THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] RETRACT_OF_TRANS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; retract_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. if x IN s then x else r x` THEN
  SIMP_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN ASM SET_TAC[]);;

let AR_FROM_UNION_AND_INTER_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s) /\ AR(t)`,
  SUBGOAL_THEN
   `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s)`
  MP_TAC THENL [ALL_TAC; MESON_TAC[UNION_COMM; INTER_COMM]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AR_RETRACT_OF_AR THEN
  EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RETRACT_FROM_UNION_AND_INTER THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[RETRACT_OF_REFL] THEN
  MATCH_MP_TAC RETRACT_OF_SUBSET THEN EXISTS_TAC `s UNION t:real^N->bool` THEN
  REWRITE_TAC[INTER_SUBSET; SUBSET_UNION] THEN
  MATCH_MP_TAC AR_IMP_RETRACT THEN ASM_SIMP_TAC[CLOSED_IN_INTER]);;

let AR_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s) /\ AR(t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC AR_FROM_UNION_AND_INTER_LOCAL THEN
  ASM_MESON_TAC[CLOSED_SUBSET; SUBSET_UNION]);;

let ANR_FROM_UNION_AND_INTER_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s) /\ ANR(t)`,
  SUBGOAL_THEN
   `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s)`
  MP_TAC THENL [ALL_TAC; MESON_TAC[UNION_COMM; INTER_COMM]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANR_NEIGHBORHOOD_RETRACT THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s INTER t:real^N->bool`; `s UNION t:real^N->bool`]
        ANR_IMP_NEIGHBOURHOOD_RETRACT) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  EXISTS_TAC `s UNION u:real^N->bool` THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `s UNION u:real^N->bool =
      ((s UNION t) DIFF t) UNION u`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_UNION; OPEN_IN_DIFF; OPEN_IN_REFL]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retract_of; retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. if x IN s then x else r x` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN `s UNION u:real^N->bool = s UNION (u INTER t)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC
     `closed_in(subtopology euclidean (s UNION t)) (s:real^N->bool)`;
    UNDISCH_TAC
       `closed_in(subtopology euclidean (s UNION t)) (t:real^N->bool)`] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM SET_TAC[]);;

let ANR_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s) /\ ANR(t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ANR_FROM_UNION_AND_INTER_LOCAL THEN
  ASM_MESON_TAC[CLOSED_SUBSET; SUBSET_UNION]);;

let ANR_FINITE_UNIONS_CONVEX_CLOSED = prove
 (`!t:(real^N->bool)->bool.
        FINITE t /\ (!c. c IN t ==> closed c /\ convex c) ==> ANR(UNIONS t)`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(t:(real^N->bool)->bool)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TAUT `p ==> q /\ r ==> s <=> q ==> p ==> r ==> s`] THEN
  SPEC_TAC(`t:(real^N->bool)->bool`,`t:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[ANR_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `t:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ANR_CLOSED_UNION THEN ASM_SIMP_TAC[CLOSED_UNIONS] THEN
  ASM_SIMP_TAC[CONVEX_IMP_ANR] THEN REWRITE_TAC[INTER_UNIONS] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LT_SUC_LE; LE_REFL] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; CLOSED_INTER; CONVEX_INTER] THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE]);;

let FINITE_IMP_ANR = prove
 (`!s:real^N->bool. FINITE s ==> ANR s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s = UNIONS {{a:real^N} | a IN s}` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
    MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; SIMPLE_IMAGE; FINITE_IMAGE] THEN
    REWRITE_TAC[CLOSED_SING; CONVEX_SING]]);;

let ANR_INSERT = prove
 (`!s a:real^N. closed s /\ ANR s ==> ANR(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  MATCH_MP_TAC ANR_CLOSED_UNION THEN
  ASM_MESON_TAC[CLOSED_SING; ANR_SING; ANR_EMPTY;
                SET_RULE `{a} INTER s = {a} \/ {a} INTER s = {}`]);;

let ANR_TRIANGULATION = prove
 (`!tr. triangulation tr ==> ANR(UNIONS tr)`,
  REWRITE_TAC[triangulation] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN
  ASM_MESON_TAC[CLOSED_SIMPLEX; CONVEX_SIMPLEX]);;

let ANR_SIMPLICIAL_COMPLEX = prove
 (`!c. simplicial_complex c ==>  ANR(UNIONS c)`,
  MESON_TAC[ANR_TRIANGULATION; SIMPLICIAL_COMPLEX_IMP_TRIANGULATION]);;

let ANR_PATH_COMPONENT_ANR = prove
 (`!s x:real^N. ANR(s) ==> ANR(path_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ANR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED THEN
  ASM_SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED]);;

let ANR_CONNECTED_COMPONENT_ANR = prove
 (`!s x:real^N. ANR(s) ==> ANR(connected_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ANR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED THEN
  ASM_SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED]);;

let ANR_COMPONENT_ANR = prove
 (`!s:real^N->bool.
        ANR s /\ c IN components s ==> ANR c`,
  REWRITE_TAC[IN_COMPONENTS] THEN MESON_TAC[ANR_CONNECTED_COMPONENT_ANR]);;

(* ------------------------------------------------------------------------- *)
(* Original ANR material, now for ENRs. Eventually more of this will be      *)
(* updated and generalized for AR and ANR as well.                           *)
(* ------------------------------------------------------------------------- *)

let ENR_BOUNDED = prove
 (`!s:real^N->bool.
        bounded s
        ==> (ENR s <=> ?u. open u /\ bounded u /\ s retract_of u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ENR] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(vec 0:real^N,r) INTER u` THEN
  ASM_SIMP_TAC[BOUNDED_INTER; OPEN_INTER; OPEN_BALL; BOUNDED_BALL] THEN
  MATCH_MP_TAC RETRACT_OF_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ASM SET_TAC[]);;

let ABSOLUTE_RETRACT_IMP_AR_GEN = prove
 (`!s:real^M->bool s':real^N->bool t u.
      s retract_of t /\ convex t /\ ~(t = {}) /\
      s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
      ==> s' retract_of u`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`s:real^M->bool`; `t:real^M->bool`]
    AR_RETRACT_OF_AR) THEN ASM_SIMP_TAC[CONVEX_IMP_AR] THEN
  ASM_MESON_TAC[AR_IMP_ABSOLUTE_RETRACT]);;

let ABSOLUTE_RETRACT_IMP_AR = prove
 (`!s s'. s retract_of (:real^M) /\ s homeomorphic s' /\ closed s'
          ==> s' retract_of (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTE_RETRACT_IMP_AR_GEN THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `(:real^M)`] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  REWRITE_TAC[CONVEX_UNIV; CLOSED_UNIV; UNIV_NOT_EMPTY]);;

let HOMEOMORPHIC_COMPACT_ARNESS = prove
 (`!s s'. s homeomorphic s'
          ==> (compact s /\ s retract_of (:real^M) <=>
               compact s' /\ s' retract_of (:real^N))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `compact(s:real^M->bool) /\ compact(s':real^N->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS]] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] ABSOLUTE_RETRACT_IMP_AR) THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM; COMPACT_IMP_CLOSED]);;

let EXTENSION_INTO_AR_LOCAL = prove
 (`!f:real^M->real^N c s t.
        f continuous_on c /\ IMAGE f c SUBSET t /\ t retract_of (:real^N) /\
        closed_in (subtopology euclidean s) c
        ==> ?g. g continuous_on s /\ IMAGE g (:real^M) SUBSET t /\
                !x. x IN c ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `c:real^M->bool`]
        TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^M->real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:real^N->real^N) o (g:real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let EXTENSION_INTO_AR = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ t retract_of (:real^N) /\
        closed s
        ==> ?g. g continuous_on (:real^M) /\ IMAGE g (:real^M) SUBSET t /\
                !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s:real^M->bool`; `(:real^M)`; `t:real^N->bool`]
   EXTENSION_INTO_AR_LOCAL) THEN
  REWRITE_TAC[GSYM OPEN_IN; GSYM CLOSED_IN; SUBTOPOLOGY_UNIV]);;

let NEIGHBOURHOOD_EXTENSION_INTO_ANR = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ ANR t /\ closed s
        ==> ?v g. s SUBSET v /\ open v /\ g continuous_on v /\
                  IMAGE g v SUBSET t /\ !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `(:real^M)`; `s:real^M->bool`; `t:real^N->bool`]
   ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  REWRITE_TAC[GSYM OPEN_IN; GSYM CLOSED_IN; SUBTOPOLOGY_UNIV] THEN
  CONV_TAC TAUT);;

let EXTENSION_FROM_COMPONENT = prove
 (`!f:real^M->real^N s c u.
        (locally connected s \/ compact s /\ ANR u) /\
        c IN components s /\
        f continuous_on c /\ IMAGE f c SUBSET u
        ==> ?g. g continuous_on s /\ IMAGE g s SUBSET u /\
                !x. x IN c ==> g x = f x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?t g. open_in (subtopology euclidean s) t /\
          closed_in (subtopology euclidean s) t /\
          c SUBSET t /\
          (g:real^M->real^N) continuous_on t /\ IMAGE g t SUBSET u /\
          !x. x IN c ==> g x = f x`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [MAP_EVERY EXISTS_TAC [`c:real^M->bool`; `f:real^M->real^N`] THEN
      ASM_SIMP_TAC[SUBSET_REFL; CLOSED_IN_COMPONENT;
                   OPEN_IN_COMPONENTS_LOCALLY_CONNECTED];
      MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `c:real^M->bool`;
                     `u:real^N->bool`]
       ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`w:real^M->bool`; `g:real^M->real^N`] THEN
      STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
      MP_TAC(ISPECL [`s:real^M->bool`; `c:real^M->bool`; `v:real^M->bool`]
        SURA_BURA_CLOPEN_SUBSET) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_IMP_LOCALLY_COMPACT] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_COMPONENTS]; ASM SET_TAC[]];
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
      EXISTS_TAC `g:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN
        ASM_MESON_TAC[COMPACT_IMP_CLOSED; OPEN_IN_IMP_SUBSET];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM SET_TAC[];
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM SET_TAC[]]];
    MP_TAC(ISPECL [`g:real^M->real^N`; `s:real^M->bool`;
                   `t:real^M->bool`; `u:real^N->bool`]
      EXTENSION_FROM_CLOPEN) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
    ASM SET_TAC[]]);;

let ABSOLUTE_RETRACT_FROM_UNION_AND_INTER = prove
 (`!s t. (s UNION t) retract_of (:real^N) /\
         (s INTER t) retract_of (:real^N) /\
         closed s /\ closed t
         ==> s retract_of (:real^N)`,
  MESON_TAC[RETRACT_OF_UNIV; AR_FROM_UNION_AND_INTER]);;

let COUNTABLE_ENR_COMPONENTS = prove
 (`!s:real^N->bool. ENR s ==> COUNTABLE(components s)`,
  SIMP_TAC[ENR_IMP_ANR; COUNTABLE_ANR_COMPONENTS]);;

let COUNTABLE_ENR_CONNECTED_COMPONENTS = prove
 (`!s:real^N->bool t.
        ENR s ==> COUNTABLE {connected_component s x | x | x IN t}`,
  SIMP_TAC[ENR_IMP_ANR; COUNTABLE_ANR_CONNECTED_COMPONENTS]);;

let COUNTABLE_ENR_PATH_COMPONENTS = prove
 (`!s:real^N->bool.
        ENR s ==> COUNTABLE {path_component s x | x | x IN s}`,
  SIMP_TAC[ENR_IMP_ANR; COUNTABLE_ANR_PATH_COMPONENTS]);;

let ENR_FROM_UNION_AND_INTER_GEN = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ENR(s UNION t) /\ ENR(s INTER t)
        ==> ENR s`,
  REWRITE_TAC[ENR_ANR] THEN
  MESON_TAC[LOCALLY_COMPACT_CLOSED_IN; ANR_FROM_UNION_AND_INTER_LOCAL]);;

let ENR_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ENR(s UNION t) /\ ENR(s INTER t)
        ==> ENR s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENR_FROM_UNION_AND_INTER_GEN THEN
  ASM_MESON_TAC[CLOSED_SUBSET; SUBSET_UNION]);;

let ENR_FINITE_UNIONS_CONVEX_CLOSED = prove
 (`!t:(real^N->bool)->bool.
        FINITE t /\ (!c. c IN t ==> closed c /\ convex c) ==> ENR(UNIONS t)`,
  SIMP_TAC[ENR_ANR; ANR_FINITE_UNIONS_CONVEX_CLOSED] THEN
  SIMP_TAC[CLOSED_IMP_LOCALLY_COMPACT; CLOSED_UNIONS]);;

let FINITE_IMP_ENR = prove
 (`!s:real^N->bool. FINITE s ==> ENR s`,
  SIMP_TAC[FINITE_IMP_ANR; FINITE_IMP_CLOSED; ENR_ANR;
           CLOSED_IMP_LOCALLY_COMPACT]);;

let ENR_INSERT = prove
 (`!s a:real^N. closed s /\ ENR s ==> ENR(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  MATCH_MP_TAC ENR_CLOSED_UNION THEN
  ASM_MESON_TAC[CLOSED_SING; ENR_SING; ENR_EMPTY;
                SET_RULE `{a} INTER s = {a} \/ {a} INTER s = {}`]);;

let ENR_TRIANGULATION = prove
 (`!tr. triangulation tr ==> ENR(UNIONS tr)`,
  REWRITE_TAC[triangulation] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENR_FINITE_UNIONS_CONVEX_CLOSED THEN
  ASM_MESON_TAC[CLOSED_SIMPLEX; CONVEX_SIMPLEX]);;

let ENR_SIMPLICIAL_COMPLEX = prove
 (`!c. simplicial_complex c ==>  ENR(UNIONS c)`,
  MESON_TAC[ENR_TRIANGULATION; SIMPLICIAL_COMPLEX_IMP_TRIANGULATION]);;

let ENR_PATH_COMPONENT_ENR = prove
 (`!s x:real^N. ENR(s) ==> ENR(path_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ENR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED THEN
  MATCH_MP_TAC RETRACT_OF_LOCALLY_PATH_CONNECTED THEN
  ASM_MESON_TAC[ENR; OPEN_IMP_LOCALLY_PATH_CONNECTED]);;

let ENR_CONNECTED_COMPONENT_ENR = prove
 (`!s x:real^N. ENR(s) ==> ENR(connected_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ENR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED THEN
  MATCH_MP_TAC RETRACT_OF_LOCALLY_CONNECTED THEN
  ASM_MESON_TAC[ENR; OPEN_IMP_LOCALLY_CONNECTED]);;

let ENR_COMPONENT_ENR = prove
 (`!s:real^N->bool.
        ENR s /\ c IN components s ==> ENR c`,
  REWRITE_TAC[IN_COMPONENTS] THEN MESON_TAC[ENR_CONNECTED_COMPONENT_ENR]);;

let ABSOLUTE_RETRACT_HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t u:real^M->bool.
        s homeomorphic u /\ ~(s = {}) /\ s SUBSET t /\ convex u /\ compact u
        ==> s retract_of t`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`u:real^M->bool`; `t:real^N->bool`; `s:real^N->bool`]
        AR_IMP_ABSOLUTE_RETRACT) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[CONVEX_IMP_AR; HOMEOMORPHIC_EMPTY; HOMEOMORPHIC_SYM;
                CLOSED_SUBSET; COMPACT_IMP_CLOSED; HOMEOMORPHIC_COMPACTNESS]);;

let ABSOLUTE_RETRACT_PATH_IMAGE_ARC = prove
 (`!g s:real^N->bool.
        arc g /\ path_image g SUBSET s ==> (path_image g) retract_of s`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`path_image g:real^N->bool`; `s:real^N->bool`;
            `interval[vec 0:real^1,vec 1:real^1]`]
        ABSOLUTE_RETRACT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
  REWRITE_TAC[COMPACT_INTERVAL; CONVEX_INTERVAL] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  EXISTS_TAC `g:real^1->real^N` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[arc; path; path_image]) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; path_image]);;

let RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX = prove
 (`!s t a:real^N.
        convex s /\ convex t /\ bounded s /\ a IN relative_interior s /\
        relative_frontier s SUBSET t /\ t SUBSET affine hull s
        ==> ?r. homotopic_with (\x. T) (t DELETE a,t DELETE a) (\x. x) r /\
                retraction (t DELETE a,relative_frontier s) r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[relative_frontier; VECTOR_ADD_LID] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; retraction] THEN
  X_GEN_TAC `dd:real^N->real` THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. a + dd(x - a) % (x - a)` THEN
  SUBGOAL_THEN
   `((\x:real^N. a + dd x % x) o (\x. x - a)) continuous_on t DELETE a`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `affine hull s DELETE (a:real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SIMP_TAC[VECTOR_ARITH `x - a:real^N = y - a <=> x = y`; VECTOR_SUB_REFL;
             SET_RULE `(!x y. f x = f y <=> x = y)
                       ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPACT_SURFACE_PROJECTION THEN
    EXISTS_TAC `relative_frontier (IMAGE (\x:real^N. x - a) s)` THEN
    ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED;
                 VECTOR_ARITH `x - a:real^N = --a + x`;
                 RELATIVE_FRONTIER_TRANSLATION; COMPACT_TRANSLATION_EQ] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET t /\ ~(a IN IMAGE f s)
        ==> IMAGE f s SUBSET IMAGE f t DELETE a`) THEN
      REWRITE_TAC[IN_IMAGE; UNWIND_THM2;
                  VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
      ASM_REWRITE_TAC[relative_frontier; IN_DIFF] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t`) THEN
      REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL];
      MATCH_MP_TAC SUBSPACE_IMP_CONIC THEN
      MATCH_MP_TAC AFFINE_IMP_SUBSPACE THEN
      SIMP_TAC[AFFINE_TRANSLATION; AFFINE_AFFINE_HULL; IN_IMAGE] THEN
      REWRITE_TAC[UNWIND_THM2;
                  VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
      ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[IN_DELETE; IMP_CONJ; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`] THEN
      MAP_EVERY X_GEN_TAC [`k:real`; `x:real^N`] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[IN_IMAGE; UNWIND_THM2; relative_frontier; VECTOR_ARITH
       `y:real^N = --a + x <=> x = a + y`] THEN
      EQ_TAC THENL
       [STRIP_TAC;
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`;
                        VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`]] THEN
      MATCH_MP_TAC(REAL_ARITH `~(a < b) /\ ~(b < a) ==> a = b`) THEN
      CONJ_TAC THEN DISCH_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `x IN c DIFF i ==> x IN i ==> F`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_ARITH `a + --a + x:real^N = x`;
                     VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`]] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `a + k % (--a + x):real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SEGMENT; NOT_FORALL_THM] THEN
      EXISTS_TAC `a + dd(--a + x) % (--a + x):real^N` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a:real^N = a + k % (--a + x) <=>
                                    k % (x - a) = vec 0`] THEN
      ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
       [EXISTS_TAC `(dd:real^N->real) (--a + x) / k` THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
        REWRITE_TAC[VECTOR_ARITH `a + b:real^N = (&1 - u) % a + u % c <=>
                                  b = u % (c - a)`] THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_SUB; REAL_DIV_RMUL;
                     REAL_LT_IMP_NZ] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE
         `a IN closure s /\ ~(a IN relative_interior s)
          ==> ~(a IN relative_interior s)`)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`;
                      VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`]];
    REWRITE_TAC[o_DEF] THEN STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[segment; SUBSET; FORALL_IN_GSPEC; IN_DELETE] THEN
    REPEAT(GEN_TAC THEN STRIP_TAC) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
      ASM_REWRITE_TAC[REAL_ARITH `&1 - u + u = &1`; REAL_SUB_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[relative_frontier] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a + x - a:real^N = x`; VECTOR_SUB_EQ] THEN
      ASM_MESON_TAC[HULL_SUBSET; RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
       `(&1 - u) % x + u % (a + d % (x - a)):real^N = a <=>
        (&1 - u + u * d) % (x - a) = vec 0`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ &0 <= u /\ u <= &1 /\ ~(x = &0 /\ u = &1)
        ==> ~(&1 - u + x = &0)`) THEN
      ASM_SIMP_TAC[REAL_ENTIRE; REAL_ARITH
       `(u = &0 \/ d = &0) /\ u = &1 <=> d = &0 /\ u = &1`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE;
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0 /\ u = &1)`)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`] THEN
      ASM SET_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[relative_frontier]) THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!s t. s SUBSET t /\ IMAGE f (t DELETE a) SUBSET u
            ==> IMAGE f (s DELETE a) SUBSET u`) THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = a` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dd(x - a:real^N) = &1`
     (fun th -> REWRITE_TAC[th] THEN CONV_TAC VECTOR_ARITH) THEN
    MATCH_MP_TAC(REAL_ARITH `~(d < &1) /\ ~(&1 < d) ==> d = &1`) THEN
    CONJ_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT)
    THENL
     [DISCH_THEN(MP_TAC o SPEC `x:real^N`);
      DISCH_THEN(MP_TAC o SPEC `a + dd(x - a) % (x - a):real^N`)] THEN
    ASM_REWRITE_TAC[SUBSET; NOT_IMP; IN_SEGMENT; NOT_FORALL_THM] THENL
     [EXISTS_TAC `a + dd(x - a) % (x - a):real^N` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0; REAL_SUB_0; VECTOR_ARITH
       `a + d % (x - a):real^N = (&1 - u) % a + u % x <=>
        (u - d) % (x - a) = vec 0`] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `(dd:real^N->real)(x - a)` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE
         `x IN closure s DIFF relative_interior s
          ==> ~(x IN relative_interior s)`)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`] THEN
      ASM_MESON_TAC[CLOSURE_SUBSET_AFFINE_HULL; SUBSET];
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `x IN closure s DIFF relative_interior s
          ==> x IN closure s`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`] THEN
        ASM_MESON_TAC[CLOSURE_SUBSET_AFFINE_HULL; SUBSET];
        EXISTS_TAC `x:real^N` THEN
        ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0;
                     VECTOR_ARITH `a = a + d <=> d:real^N = vec 0`;
           VECTOR_ARITH `x:real^N = (&1 - u) % a + u % (a + d % (x - a)) <=>
                         (u * d - &1) % (x - a) = vec 0`] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
        EXISTS_TAC `inv((dd:real^N->real)(x - a))` THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_SUB_REFL; REAL_LT_INV_EQ] THEN
        ASM_SIMP_TAC[REAL_INV_LT_1] THEN ASM_REAL_ARITH_TAC]]]);;

let RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL = prove
 (`!s a:real^N.
        convex s /\ bounded s /\ a IN relative_interior s
        ==> relative_frontier s retract_of (affine hull s DELETE a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `affine hull s:real^N->bool`; `a:real^N`]
      RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX) THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; SUBSET_REFL] THEN
  REWRITE_TAC[retract_of] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s DIFF t SUBSET u`) THEN
  REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL]);;

let RELATIVE_BOUNDARY_RETRACT_OF_PUNCTURED_AFFINE_HULL = prove
 (`!s a:real^N.
        convex s /\ compact s /\ a IN relative_interior s
        ==> (s DIFF relative_interior s) retract_of
            (affine hull s DELETE a)`,
  MP_TAC RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[relative_frontier; COMPACT_IMP_BOUNDED; COMPACT_IMP_CLOSED;
               CLOSURE_CLOSED]);;

let PATH_CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
        convex s /\ bounded s /\ ~(aff_dim s = &1)
        ==> path_connected(relative_frontier s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `relative_interior s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; PATH_CONNECTED_EMPTY;
                  RELATIVE_FRONTIER_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RETRACT_OF_PATH_CONNECTED THEN
    EXISTS_TAC `affine hull s DELETE (a:real^N)` THEN
    ASM_SIMP_TAC[PATH_CONNECTED_PUNCTURED_CONVEX; AFFINE_AFFINE_HULL;
                 AFFINE_IMP_CONVEX; AFF_DIM_AFFINE_HULL;
                 RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL]]);;

let CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
        convex s /\ bounded s /\ ~(aff_dim s = &1)
        ==> connected(relative_frontier s)`,
  SIMP_TAC[PATH_CONNECTED_SPHERE_GEN; PATH_CONNECTED_IMP_CONNECTED]);;

let ENR_RELATIVE_FRONTIER_CONVEX = prove
 (`!s:real^N->bool. bounded s /\ convex s ==> ENR(relative_frontier s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[ENR; RELATIVE_FRONTIER_EMPTY] THENL
   [ASM_MESON_TAC[RETRACT_OF_REFL; OPEN_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior s:real^N->bool = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `{x | x IN (:real^N) /\
                   closest_point (affine hull s) x IN
                   ((:real^N) DELETE a)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `(:real^N)` THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL; SUBSET_UNIV; ETA_AX];
    MATCH_MP_TAC RETRACT_OF_TRANS THEN
    EXISTS_TAC `(affine hull s) DELETE (a:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[retract_of; retraction] THEN
      EXISTS_TAC `closest_point (affine hull s:real^N->bool)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
      ASM_SIMP_TAC[IN_ELIM_THM; IN_UNIV; CLOSEST_POINT_SELF;
                   CLOSEST_POINT_IN_SET; AFFINE_HULL_EQ_EMPTY;
                   CLOSED_AFFINE_HULL]]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL;
               CLOSED_AFFINE_HULL; AFFINE_HULL_EQ_EMPTY]);;

let ANR_RELATIVE_FRONTIER_CONVEX = prove
 (`!s:real^N->bool. bounded s /\ convex s ==> ANR(relative_frontier s)`,
  SIMP_TAC[ENR_IMP_ANR; ENR_RELATIVE_FRONTIER_CONVEX]);;

let FRONTIER_RETRACT_OF_PUNCTURED_UNIVERSE = prove
 (`!s a. convex s /\ bounded s /\ a IN interior s
         ==> (frontier s) retract_of ((:real^N) DELETE a)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `a IN s ==> ~(s = {})`)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
        RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR;
               RELATIVE_INTERIOR_NONEMPTY_INTERIOR;
               AFFINE_HULL_NONEMPTY_INTERIOR]);;

let SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN = prove
 (`!a r b:real^N.
      b IN ball(a,r) ==> sphere(a,r) retract_of ((:real^N) DELETE b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  MATCH_MP_TAC FRONTIER_RETRACT_OF_PUNCTURED_UNIVERSE THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; INTERIOR_CBALL]);;

let SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE = prove
 (`!a r. &0 < r ==> sphere(a,r) retract_of ((:real^N) DELETE a)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL]);;

let ENR_SPHERE = prove
 (`!a:real^N r. ENR(sphere(a,r))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < r` THENL
   [REWRITE_TAC[ENR] THEN EXISTS_TAC `(:real^N) DELETE a` THEN
    ASM_SIMP_TAC[SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE;
                 OPEN_DELETE; OPEN_UNIV];
    ASM_MESON_TAC[FINITE_IMP_ENR; REAL_NOT_LE; FINITE_SPHERE]]);;

let ANR_SPHERE = prove
 (`!a:real^N r. ANR(sphere(a,r))`,
  SIMP_TAC[ENR_SPHERE; ENR_IMP_ANR]);;

let LOCALLY_PATH_CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
       bounded s /\ convex s ==> locally path_connected (relative_frontier s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `relative_interior(s:real^N->bool) = {}` THENL
   [UNDISCH_TAC `relative_interior(s:real^N->bool) = {}` THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[LOCALLY_EMPTY; RELATIVE_FRONTIER_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    MATCH_MP_TAC RETRACT_OF_LOCALLY_PATH_CONNECTED THEN
    EXISTS_TAC `(affine hull s) DELETE (a:real^N)` THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL] THEN
    MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THEN
    SIMP_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED; AFFINE_IMP_CONVEX;
             AFFINE_AFFINE_HULL]]);;

let LOCALLY_CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
       bounded s /\ convex s ==> locally connected (relative_frontier s)`,
  SIMP_TAC[LOCALLY_PATH_CONNECTED_SPHERE_GEN;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let LOCALLY_PATH_CONNECTED_SPHERE = prove
 (`!a:real^N r. locally path_connected (sphere(a,r))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `cball(a:real^N,r)` LOCALLY_PATH_CONNECTED_SPHERE_GEN) THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`] RELATIVE_FRONTIER_CBALL) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[SPHERE_SING; LOCALLY_SING; PATH_CONNECTED_SING;
               BOUNDED_CBALL; CONVEX_CBALL]);;

let LOCALLY_CONNECTED_SPHERE = prove
 (`!a:real^N r. locally connected(sphere(a,r))`,
  SIMP_TAC[LOCALLY_PATH_CONNECTED_SPHERE;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let ABSOLUTE_RETRACTION_CONVEX_CLOSED_RELATIVE = prove
 (`!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> ?r. retraction (t,s) r /\
                !x. x IN (affine hull s) DIFF (relative_interior s)
                    ==> r(x) IN relative_frontier s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[retraction] THEN
  EXISTS_TAC `closest_point(s:real^N->bool)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CLOSEST_POINT_SELF] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; CLOSEST_POINT_IN_SET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSEST_POINT_IN_RELATIVE_FRONTIER THEN
  ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]);;

let ABSOLUTE_RETRACTION_CONVEX_CLOSED = prove
 (`!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> ?r. retraction (t,s) r /\
                (!x. ~(x IN s) ==> r(x) IN frontier s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[retraction] THEN
  EXISTS_TAC `closest_point(s:real^N->bool)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CLOSEST_POINT_SELF] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; CLOSEST_POINT_IN_SET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSEST_POINT_IN_FRONTIER THEN
  ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]);;

let ABSOLUTE_RETRACT_CONVEX_CLOSED = prove
 (`!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> s retract_of t`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[ABSOLUTE_RETRACTION_CONVEX_CLOSED]);;

let ABSOLUTE_RETRACT_CONVEX = prove
 (`!s u:real^N->bool.
        convex s /\ ~(s = {}) /\ closed_in (subtopology euclidean u) s
        ==> s retract_of u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `s:real^N->bool`; `u:real^N->bool`;
                 `s:real^N->bool`] DUGUNDJI) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_ID; IMAGE_ID; SUBSET_REFL;
                CLOSED_IN_IMP_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Borsuk homotopy extension thorem. It's only this late so we can use the   *)
(* concept of retraction, saying that the domain sets or range set are ANRs. *)
(* ------------------------------------------------------------------------- *)

let BORSUK_HOMOTOPY_EXTENSION_HOMOTOPIC = prove
 (`!f:real^M->real^N g s t u.
        closed_in (subtopology euclidean t) s /\
        (ANR s /\ ANR t \/ ANR u) /\
        f continuous_on t /\ IMAGE f t SUBSET u /\
        homotopic_with (\x. T) (s,u) f g
        ==> ?g'. homotopic_with (\x. T) (t,u) f g' /\
                 g' continuous_on t /\ IMAGE g' t SUBSET u /\
                 !x. x IN s ==> g'(x) = g(x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  MAP_EVERY ABBREV_TAC
   [`h' = \z. if sndcart z IN s then (h:real^(1,M)finite_sum->real^N) z
             else f(sndcart z)`;
    `B:real^(1,M)finite_sum->bool =
       {vec 0} PCROSS t UNION interval[vec 0,vec 1] PCROSS s`] THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (interval[vec 0:real^1,vec 1] PCROSS t))
              ({vec 0} PCROSS (t:real^M->bool)) /\
    closed_in (subtopology euclidean (interval[vec 0:real^1,vec 1] PCROSS t))
              (interval[vec 0,vec 1] PCROSS s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_PCROSS THEN
    ASM_REWRITE_TAC[CLOSED_IN_SING; CLOSED_IN_REFL; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^(1,M)finite_sum->real^N) continuous_on B`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h'"; "B"] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[IMP_CONJ] CLOSED_IN_SUBSET_TRANS)) THEN
      REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; SUBSET_PCROSS] THEN
      ASM_REWRITE_TAC[SING_SUBSET; SUBSET_REFL; ENDS_IN_UNIT_INTERVAL];
     ASM_SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                   SNDCART_PASTECART; TAUT `(p /\ q) /\ ~q <=> F`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON;
                   IMAGE_SNDCART_PCROSS; NOT_INSERT_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h':real^(1,M)finite_sum->real^N) B SUBSET u`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h'"; "B"] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
           SNDCART_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_SING] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[COND_ID] THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o SIMP_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?V k:real^(1,M)finite_sum->real^N.
        B SUBSET V /\
        open_in (subtopology euclidean (interval [vec 0,vec 1] PCROSS t)) V /\
        k continuous_on V /\
        IMAGE k V SUBSET u /\
        (!x. x IN B ==> k x = h' x)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [SUBGOAL_THEN `ANR(B:real^(1,M)finite_sum->bool)` MP_TAC THENL
       [EXPAND_TAC "B" THEN MATCH_MP_TAC ANR_CLOSED_UNION_LOCAL THEN
        ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (ONCE_REWRITE_RULE[IMP_CONJ] CLOSED_IN_SUBSET_TRANS)) THEN
          REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; SUBSET_PCROSS] THEN
          ASM_REWRITE_TAC[SING_SUBSET; SUBSET_REFL; ENDS_IN_UNIT_INTERVAL];
          ASM_SIMP_TAC[INTER_PCROSS; SET_RULE `s SUBSET t ==> t INTER s = s`;
                       ENDS_IN_UNIT_INTERVAL;
                       SET_RULE `a IN s ==> {a} INTER s = {a}`] THEN
          REPEAT CONJ_TAC THEN MATCH_MP_TAC ANR_PCROSS THEN
          ASM_REWRITE_TAC[ANR_INTERVAL; ANR_SING]];
        DISCH_THEN(MP_TAC o SPEC
          `interval[vec 0:real^1,vec 1] PCROSS (t:real^M->bool)` o
         MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
           ANR_IMP_NEIGHBOURHOOD_RETRACT)) THEN
        ANTS_TAC THENL
         [EXPAND_TAC "B" THEN MATCH_MP_TAC CLOSED_IN_UNION THEN
          CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_PCROSS THEN
          ASM_REWRITE_TAC[CLOSED_IN_REFL; CLOSED_IN_SING;
                          ENDS_IN_UNIT_INTERVAL];
          MATCH_MP_TAC MONO_EXISTS] THEN
        X_GEN_TAC `V:real^(1,M)finite_sum->bool` THEN STRIP_TAC THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
        REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `r:real^(1,M)finite_sum->real^(1,M)finite_sum` THEN
        STRIP_TAC THEN
        EXISTS_TAC `(h':real^(1,M)finite_sum->real^N) o
                    (r:real^(1,M)finite_sum->real^(1,M)finite_sum)` THEN
        ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "B" THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION]];
    ABBREV_TAC `s' = {x | ?u. u IN interval[vec 0,vec 1] /\
                              pastecart (u:real^1) (x:real^M) IN
                              interval [vec 0,vec 1] PCROSS t DIFF V}` THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean t) (s':real^M->bool)`
    ASSUME_TAC THENL
     [EXPAND_TAC "s'" THEN MATCH_MP_TAC CLOSED_IN_COMPACT_PROJECTION THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `s':real^M->bool`; `t:real^M->bool`;
                   `vec 1:real^1`; `vec 0:real^1`] URYSOHN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "s'" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[NOT_IN_EMPTY; IN_DIFF; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `x:real^M` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SEGMENT_1; DROP_VEC; REAL_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `(\x. (k:real^(1,M)finite_sum->real^N) (pastecart (a x) x))` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[HOMOTOPIC_WITH] THEN
      EXISTS_TAC `(k:real^(1,M)finite_sum->real^N) o
          (\z. pastecart (drop(fstcart z) % a(sndcart z)) (sndcart z))` THEN
      REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
          MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_FSTCART; LINEAR_CONTINUOUS_ON;
                   ETA_AX] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
          ASM_SIMP_TAC[IMAGE_SNDCART_PCROSS; UNIT_INTERVAL_NONEMPTY];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET))];
        REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `IMAGE k t SUBSET u
                    ==> s SUBSET t ==> IMAGE k s SUBSET u`));
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        SUBGOAL_THEN `pastecart (vec 0:real^1) (x:real^M) IN B` MP_TAC THENL
         [EXPAND_TAC "B" THEN
          ASM_REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_SING];
          DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
           `(h':real^(1,M)finite_sum->real^N) (pastecart (vec 0) x)` THEN
          CONJ_TAC THENL [ASM_MESON_TAC[]; EXPAND_TAC "h'"] THEN
          ASM_REWRITE_TAC[SNDCART_PASTECART; COND_ID]]] THEN
      (REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
       MAP_EVERY X_GEN_TAC [`p:real^1`; `x:real^M`] THEN STRIP_TAC THEN
       REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
       ASM_CASES_TAC `(x:real^M) IN s'` THENL
        [ASM_SIMP_TAC[VECTOR_MUL_RZERO] THEN
         FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
         EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
         ASM_REWRITE_TAC[IN_SING];
         UNDISCH_TAC `~((x:real^M) IN s')` THEN
         EXPAND_TAC "s'" THEN
         REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM]  THEN
         DISCH_THEN(MP_TAC o SPEC `drop p % (a:real^M->real^1) x`) THEN
         REWRITE_TAC[PASTECART_IN_PCROSS; IN_DIFF] THEN
         ASM_REWRITE_TAC[CONJ_ASSOC] THEN
         MATCH_MP_TAC(TAUT `p ==> ~(p /\ ~q) ==> q`) THEN
         REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
         ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_LMUL; REAL_ARITH
          `p * a <= p * &1 /\ p <= &1 ==> p * a <= &1`]]);
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC;
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]);
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(h':real^(1,M)finite_sum->real^N) (pastecart (vec 1) x)` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; EXPAND_TAC "h'"] THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART] THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]] THEN
    (ASM_CASES_TAC `(x:real^M) IN s'` THEN ASM_SIMP_TAC[] THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
       EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
       ASM SET_TAC[];
       UNDISCH_TAC `~((x:real^M) IN s')` THEN EXPAND_TAC "s'" THEN
       REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM]  THEN
       DISCH_THEN(MP_TAC o SPEC `(a:real^M->real^1) x`) THEN
       ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_DIFF] THEN ASM SET_TAC[]])]);;

let BORSUK_HOMOTOPY_EXTENSION = prove
 (`!f:real^M->real^N g s t u.
        closed_in (subtopology euclidean t) s /\
        (ANR s /\ ANR t \/ ANR u) /\
        f continuous_on t /\ IMAGE f t SUBSET u /\
        homotopic_with (\x. T) (s,u) f g
        ==> ?g'. g' continuous_on t /\ IMAGE g' t SUBSET u /\
                 !x. x IN s ==> g'(x) = g(x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP BORSUK_HOMOTOPY_EXTENSION_HOMOTOPIC) THEN
  MESON_TAC[]);;

let NULLHOMOTOPIC_INTO_ANR_EXTENSION = prove
 (`!f:real^M->real^N s t.
      closed s /\ f continuous_on s /\ ~(s = {}) /\ IMAGE f s SUBSET t /\ ANR t
      ==> ((?c. homotopic_with (\x. T) (s,t) f (\x. c)) <=>
           (?g. g continuous_on (:real^M) /\
                IMAGE g (:real^M) SUBSET t /\
                !x. x IN s ==> g x = f x))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC BORSUK_HOMOTOPY_EXTENSION THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    EXISTS_TAC `(\x. c):real^M->real^N` THEN
    ASM_REWRITE_TAC[CLOSED_UNIV; CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    ASM SET_TAC[];
    MP_TAC(ISPECL [`g:real^M->real^N`; `(:real^M)`; `t:real^N->bool`]
         NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `(\x. c):real^M->real^N`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_LEFT THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION = prove
 (`!f:real^M->real^N s t.
        closed s /\ f continuous_on s /\ ~(s = {}) /\
        IMAGE f s SUBSET relative_frontier t /\ convex t /\ bounded t
        ==> ((?c. homotopic_with (\x. T) (s,relative_frontier t) f (\x. c)) <=>
             (?g. g continuous_on (:real^M) /\
                  IMAGE g (:real^M) SUBSET relative_frontier t /\
                  !x. x IN s ==> g x = f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NULLHOMOTOPIC_INTO_ANR_EXTENSION THEN
  MP_TAC(ISPEC `t:real^N->bool` ANR_RELATIVE_FRONTIER_CONVEX) THEN
  ASM_REWRITE_TAC[]);;

let NULLHOMOTOPIC_INTO_SPHERE_EXTENSION = prove
 (`!f:real^M->real^N s a r.
     closed s /\ f continuous_on s /\ ~(s = {}) /\ IMAGE f s SUBSET sphere(a,r)
     ==> ((?c. homotopic_with (\x. T) (s,sphere(a,r)) f (\x. c)) <=>
          (?g. g continuous_on (:real^M) /\
               IMAGE g (:real^M) SUBSET sphere(a,r) /\
               !x. x IN s ==> g x = f x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`] RELATIVE_FRONTIER_CBALL) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[SPHERE_SING] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [EXISTS_TAC `a:real^N` THEN SIMP_TAC[HOMOTOPIC_WITH; PCROSS] THEN
      EXISTS_TAC `\y:real^(1,M)finite_sum. (a:real^N)`;
      EXISTS_TAC `(\x. a):real^M->real^N`] THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
    MATCH_MP_TAC NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL]]);;

let ABSOLUTE_RETRACT_CONTRACTIBLE_ANR = prove
 (`!s u:real^N->bool.
      closed_in (subtopology euclidean u) s /\
      contractible s /\ ~(s = {}) /\ ANR s
      ==> s retract_of u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AR_IMP_RETRACT THEN
  ASM_SIMP_TAC[AR_ANR]);;

(* ------------------------------------------------------------------------- *)
(* More homotopy extension results and relations to components.              *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ON_COMPONENTS = prove
 (`!s t f g:real^M->real^N.
        locally connected s /\
        (!c. c IN components s ==> homotopic_with (\x. T) (c,t) f g)
        ==> homotopic_with (\x. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
  MATCH_MP_TAC HOMOTOPIC_ON_CLOPEN_UNIONS THEN
  X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM UNIONS_COMPONENTS] THEN
  ASM_MESON_TAC[CLOSED_IN_COMPONENT; OPEN_IN_COMPONENTS_LOCALLY_CONNECTED]);;

let INESSENTIAL_ON_COMPONENTS = prove
 (`!f:real^M->real^N s t.
        locally connected s /\ path_connected t /\
        (!c. c IN components s ==> ?a. homotopic_with (\x. T) (c,t) f (\x. a))
        ==> ?a. homotopic_with (\x. T) (s,t) f (\x. a)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `components(s:real^M->bool) = {}` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[COMPONENTS_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[HOMOTOPIC_ON_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a IN t` MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
     DISCH_THEN(X_CHOOSE_TAC `c:real^M->bool`) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
     GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN SET_TAC[];
     MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_ON_COMPONENTS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN FIRST_X_ASSUM
   (MATCH_MP_TAC o REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN ASM SET_TAC[]);;

let HOMOTOPIC_NEIGHBOURHOOD_EXTENSION = prove
 (`!f g:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET u /\
        g continuous_on s /\ IMAGE g s SUBSET u /\
        closed_in (subtopology euclidean s) t /\ ANR u /\
        homotopic_with (\x. T) (t,u) f g
        ==> ?v. t SUBSET v /\
                open_in (subtopology euclidean s) v /\
                homotopic_with (\x. T) (v,u) f g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `h' = \z. if fstcart z IN {vec 0} then f(sndcart z)
             else if fstcart z IN {vec 1} then g(sndcart z)
             else (h:real^(1,M)finite_sum->real^N) z` THEN
  MP_TAC(ISPECL
   [`h':real^(1,M)finite_sum->real^N`;
    `interval[vec 0:real^1,vec 1] PCROSS (s:real^M->bool)`;
    `{vec 0:real^1,vec 1} PCROSS (s:real^M->bool) UNION
     interval[vec 0,vec 1] PCROSS t`;
    `u:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_SIMP_TAC[ENR_IMP_ANR] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
      REWRITE_TAC[PCROSS_UNION; UNION_ASSOC] THEN EXPAND_TAC "h'" THEN
      REPLICATE_TAC 2 (MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
       REPLICATE_TAC 2 (CONJ_TAC THENL
        [MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
         EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (s:real^M->bool)` THEN
         REWRITE_TAC[SET_RULE `t UNION u SUBSET s UNION t UNION u`] THEN
         REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; SUBSET_PCROSS] THEN
         REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
         ASM_REWRITE_TAC[SUBSET_REFL] THEN
         TRY(MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC) THEN
         MATCH_MP_TAC CLOSED_IN_PCROSS THEN
         ASM_REWRITE_TAC[CLOSED_IN_REFL] THEN MATCH_MP_TAC CLOSED_SUBSET THEN
         REWRITE_TAC[SING_SUBSET; ENDS_IN_UNIT_INTERVAL; CLOSED_SING];
         ALL_TAC]) THEN
       REPEAT CONJ_TAC THENL
        [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
         MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
         SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
         ASM_REWRITE_TAC[IMAGE_SNDCART_PCROSS; NOT_INSERT_EMPTY];
         ASM_REWRITE_TAC[];
         REWRITE_TAC[FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS] THEN
         REWRITE_TAC[FSTCART_PASTECART; IN_SING; SNDCART_PASTECART] THEN
         MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^M`] THEN
         ASM_CASES_TAC `x:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[VEC_EQ; ARITH_EQ; ENDS_IN_UNIT_INTERVAL] THEN
          ASM_CASES_TAC `x:real^1 = vec 1` THEN ASM_REWRITE_TAC[]]);
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
      REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_SING; NOT_IN_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^M`] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      EXPAND_TAC "h'" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_SING] THEN
      REPEAT(COND_CASES_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]]) THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE f s SUBSET u ==> b IN s ==> f b IN u`)) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC CLOSED_IN_PCROSS THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL] THEN
      MATCH_MP_TAC CLOSED_SUBSET THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
      SIMP_TAC[CLOSED_INSERT; CLOSED_EMPTY]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`w:real^(1,M)finite_sum->bool`; `k:real^(1,M)finite_sum->real^N`] THEN
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`interval[vec 0:real^1,vec 1]`;
                 `t:real^M->bool`; `s:real^M->bool`;
                 `w:real^(1,M)finite_sum->bool`]
        TUBE_LEMMA_GEN) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `t':real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[HOMOTOPIC_WITH] THEN
  EXISTS_TAC `k:real^(1,M)finite_sum->real^N` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhs o snd o dest_imp) th o lhs o snd)) THEN
  REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_INSERT] THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  EXPAND_TAC "h'" THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_SING] THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ]);;

let HOMOTOPIC_ON_COMPONENTS_EQ = prove
 (`!s t f g:real^M->real^N.
        (locally connected s \/ compact s /\ ANR t)
        ==> (homotopic_with (\x. T) (s,t) f g <=>
             f continuous_on s /\ IMAGE f s SUBSET t /\
             g continuous_on s /\ IMAGE g s SUBSET t /\
             !c. c IN components s ==> homotopic_with (\x. T) (c,t) f g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `(q ==> r) /\ (r ==> (q <=> s)) ==> (q <=> r /\ s)`) THEN
  CONJ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_CONTINUOUS; HOMOTOPIC_WITH_IMP_SUBSET];
    ALL_TAC] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_SUBSET_LEFT; IN_COMPONENTS_SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!c. c IN components s
        ==> ?u. c SUBSET u /\
                closed_in (subtopology euclidean s) u /\
                open_in (subtopology euclidean s) u /\
                homotopic_with (\x. T) (u,t) (f:real^M->real^N) g`
  MP_TAC THENL
   [X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [EXISTS_TAC `c:real^M->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT; SUBSET_REFL;
                   OPEN_IN_COMPONENTS_LOCALLY_CONNECTED];
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(ISPECL
       [`f:real^M->real^N`; `g:real^M->real^N`;
        `s:real^M->bool`; `c:real^M->bool`; `t:real^N->bool`]
        HOMOTOPIC_NEIGHBOURHOOD_EXTENSION) THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
      MP_TAC(ISPECL [`s:real^M->bool`; `c:real^M->bool`; `v:real^M->bool`]
        SURA_BURA_CLOPEN_SUBSET) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_IMP_LOCALLY_COMPACT] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_COMPONENTS]; ASM SET_TAC[]];
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN
        ASM_MESON_TAC[COMPACT_IMP_CLOSED; OPEN_IN_IMP_SUBSET];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_SUBSET_LEFT)) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM SET_TAC[]]];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:(real^M->bool)->(real^M->bool)` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `s = UNIONS (IMAGE k (components(s:real^M->bool)))`
     (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))
    THENL
      [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
        [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
         MATCH_MP_TAC UNIONS_MONO THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
         ASM_MESON_TAC[];
         REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
         ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]];
       MATCH_MP_TAC HOMOTOPIC_ON_CLOPEN_UNIONS THEN
       ASM_SIMP_TAC[FORALL_IN_IMAGE]]]);;

let INESSENTIAL_ON_COMPONENTS_EQ = prove
 (`!s t f:real^M->real^N.
        (locally connected s \/ compact s /\ ANR t) /\
        path_connected t
        ==> ((?a. homotopic_with (\x. T) (s,t) f (\x. a)) <=>
             f continuous_on s /\ IMAGE f s SUBSET t /\
             !c. c IN components s
                 ==> ?a. homotopic_with (\x. T) (c,t) f (\x. a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(q ==> r) /\ (r ==> (q <=> s)) ==> (q <=> r /\ s)`) THEN
  CONJ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_CONTINUOUS; HOMOTOPIC_WITH_IMP_SUBSET];
    STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP HOMOTOPIC_ON_COMPONENTS_EQ th]) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_SIMP_TAC[COMPONENTS_EMPTY; IMAGE_CLAUSES; NOT_IN_EMPTY;
               EMPTY_SUBSET] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?c:real^M->bool. c IN components s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY; COMPONENTS_EQ_EMPTY]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `a:real^N` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `d:real^M->bool`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `d:real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real^N` MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
        MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY)) THEN
  ASM SET_TAC[]);;

let COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS = prove
 (`!s:real^M->bool t:real^N->bool.
        (locally connected s \/ compact s /\ ANR t)
         ==> ((!f g. f continuous_on s /\ IMAGE f s SUBSET t /\
                     g continuous_on s /\ IMAGE g s SUBSET t
                     ==> homotopic_with (\x. T) (s,t) f g) <=>
              (!c. c IN components s
                   ==> (!f g. f continuous_on c /\ IMAGE f c SUBSET t /\
                              g continuous_on c /\ IMAGE g c SUBSET t
                              ==> homotopic_with (\x. T) (c,t) f g)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`g:real^M->real^N`; `s:real^M->bool`;
                   `c:real^M->bool`; `t:real^N->bool`]
        EXTENSION_FROM_COMPONENT) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;
                   `c:real^M->bool`; `t:real^N->bool`]
        EXTENSION_FROM_COMPONENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ENR_IMP_ANR]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^N` STRIP_ASSUME_TAC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ENR_IMP_ANR]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real^M->real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`f':real^M->real^N`; `g':real^M->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:real^M->bool` o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_SUBSET_LEFT)) THEN
    ASM_SIMP_TAC[IN_COMPONENTS_SUBSET] THEN MATCH_MP_TAC
     (ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
    ASM_SIMP_TAC[];
    FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP HOMOTOPIC_ON_COMPONENTS_EQ th]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[]]);;

let COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS_NULL = prove
 (`!s:real^M->bool t:real^N->bool.
        (locally connected s \/ compact s /\ ANR t) /\ path_connected t
         ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET t
                   ==> ?a. homotopic_with (\x. T) (s,t) f (\x. a)) <=>
              (!c. c IN components s
                   ==> (!f. f continuous_on c /\ IMAGE f c SUBSET t
                            ==> ?a. homotopic_with (\x. T) (c,t) f (\x. a))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS) THEN
  ASM_SIMP_TAC[HOMOTOPIC_TRIVIALITY]);;

(* ------------------------------------------------------------------------- *)
(* A few simple lemmas about deformation retracts.                           *)
(* ------------------------------------------------------------------------- *)

let DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT = prove
 (`!s t:real^N->bool.
        (?r. homotopic_with (\x. T) (s,s) (\x. x) r /\ retraction(s,t) r)
        ==> s homotopy_equivalent t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[retraction] THEN STRIP_TAC THEN
  EXISTS_TAC `I:real^N->real^N` THEN REWRITE_TAC[I_O_ID] THEN
  ASM_REWRITE_TAC[I_DEF; CONTINUOUS_ON_ID; IMAGE_ID] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMOTOPIC_WITH_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

let DEFORMATION_RETRACT = prove
 (`!s t:real^N->bool.
        (?r. homotopic_with (\x. T) (s,s) (\x. x) r /\ retraction(s,t) r) <=>
        t retract_of s /\
        ?f. homotopic_with (\x. T) (s,s) (\x. x) f /\ IMAGE f s SUBSET t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `r:real^N->real^N` THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `r:real^N->real^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) MP_TAC) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `f:real^N->real^N` THEN
    STRIP_TAC THEN EXISTS_TAC `r:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `f:real^N->real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(r:real^N->real^N) o (f:real^N->real^N)`;
      `(r:real^N->real^N) o (\x. x)`] THEN
    ASM_SIMP_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HOMOTOPIC_WITH_SYM]; ASM SET_TAC[]]]);;

let DEFORMATION_RETRACT_OF_CONTRACTIBLE_SING = prove
 (`!s a:real^N.
        contractible s /\ a IN s
        ==> ?r. homotopic_with (\x. T) (s,s) (\x. x) r /\ retraction(s,{a}) r`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DEFORMATION_RETRACT; RETRACT_OF_SING] THEN
  EXISTS_TAC `(\x. a):real^N->real^N` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTRACTIBLE_IMP_PATH_CONNECTED) THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  ASM SET_TAC[]);;

let HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX = prove
 (`!s t a:real^N.
      convex s /\ bounded s /\ a IN relative_interior s /\
      convex t /\ relative_frontier s SUBSET t /\ t SUBSET affine hull s
      ==> (relative_frontier s) homotopy_equivalent (t DELETE a)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  MATCH_MP_TAC DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT THEN ASM_SIMP_TAC
   [RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX]);;

let HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL = prove
 (`!s a:real^N.
      convex s /\ bounded s /\ a IN relative_interior s
      ==> (relative_frontier s) homotopy_equivalent (affine hull s DELETE a)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; SUBSET_REFL] THEN
  REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s DIFF t SUBSET u`) THEN
  REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of fixpoints under (more general notion of) retraction.      *)
(* ------------------------------------------------------------------------- *)

let INVERTIBLE_FIXPOINT_PROPERTY = prove
 (`!s:real^M->bool t:real^N->bool i r.
     i continuous_on t /\ IMAGE i t SUBSET s /\
     r continuous_on s /\ IMAGE r s SUBSET t /\
     (!y. y IN t ==> (r(i(y)) = y))
     ==> (!f. f continuous_on s /\ IMAGE f s SUBSET s
              ==> ?x. x IN s /\ (f x = x))
         ==> !g. g continuous_on t /\ IMAGE g t SUBSET t
                 ==> ?y. y IN t /\ (g y = y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(i:real^N->real^M) o (g:real^N->real^N) o (r:real^M->real^N)`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CONTINUOUS_ON_COMPOSE; IMAGE_SUBSET;
                  SUBSET_TRANS; IMAGE_o];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

let HOMEOMORPHIC_FIXPOINT_PROPERTY = prove
 (`!s t. s homeomorphic t
         ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET s
                   ==> ?x. x IN s /\ (f x = x)) <=>
              (!g. g continuous_on t /\ IMAGE g t SUBSET t
                   ==> ?y. y IN t /\ (g y = y)))`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC INVERTIBLE_FIXPOINT_PROPERTY THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

let RETRACT_FIXPOINT_PROPERTY = prove
 (`!s t:real^N->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET s
             ==> ?x. x IN s /\ (f x = x))
        ==> !g. g continuous_on t /\ IMAGE g t SUBSET t
                ==> ?y. y IN t /\ (g y = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC INVERTIBLE_FIXPOINT_PROPERTY THEN
  EXISTS_TAC `\x:real^N. x` THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[retract_of] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REWRITE_TAC[retraction] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* So the Brouwer theorem for any set with nonempty interior.                *)
(* ------------------------------------------------------------------------- *)

let BROUWER_WEAK = prove
 (`!f:real^N->real^N s.
        compact s /\ convex s /\ ~(interior s = {}) /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  GEN_TAC THEN ONCE_REWRITE_TAC
   [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[vec 0:real^N,vec 1]`; `s:real^N->bool`]
                HOMEOMORPHIC_CONVEX_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL] THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_EQ_EMPTY] THEN
    MESON_TAC[VEC_COMPONENT; REAL_ARITH `~(&1 <= &0)`];
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_FIXPOINT_PROPERTY) THEN
    REWRITE_TAC[BROUWER_CUBE] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* And in particular for a closed ball.                                      *)
(* ------------------------------------------------------------------------- *)

let BROUWER_BALL = prove
 (`!f:real^N->real^N a e.
        &0 < e /\
        f continuous_on cball(a,e) /\ IMAGE f (cball(a,e)) SUBSET (cball(a,e))
        ==> ?x. x IN cball(a,e) /\ (f x = x)`,
  ASM_SIMP_TAC[BROUWER_WEAK; CONVEX_CBALL; COMPACT_CBALL; INTERIOR_CBALL;
               REAL_LT_IMP_LE; REAL_NOT_LE; BALL_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Still more general form; could derive this directly without using the     *)
(* rather involved HOMEOMORPHIC_CONVEX_COMPACT theorem, just using           *)
(* a scaling and translation to put the set inside the unit cube.            *)
(* ------------------------------------------------------------------------- *)

let BROUWER = prove
 (`!f:real^N->real^N s.
        compact s /\ convex s /\ ~(s = {}) /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?e. &0 < e /\ s SUBSET cball(vec 0:real^N,e)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; NORM_ARITH `dist(vec 0,x) = norm(x)`] THEN
    ASM_MESON_TAC[BOUNDED_POS; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x:real^N. x IN cball(vec 0,e) /\ (f o closest_point s) x = x`
  MP_TAC THENL
   [MATCH_MP_TAC BROUWER_BALL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; COMPACT_IMP_CLOSED] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
      REPEAT STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET])) THEN
      REWRITE_TAC[o_THM; IN_IMAGE] THEN
      EXISTS_TAC `closest_point s x:real^N` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSEST_POINT_IN_SET]] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSEST_POINT_IN_SET];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_MESON_TAC[CLOSEST_POINT_SELF;
                  CLOSEST_POINT_IN_SET; COMPACT_IMP_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* So we get the no-retraction theorem, first for a ball, then more general. *)
(* ------------------------------------------------------------------------- *)

let NO_RETRACTION_CBALL = prove
 (`!a:real^N e. &0 < e ==> ~(sphere(a,e) retract_of cball(a,e))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
    RETRACT_FIXPOINT_PROPERTY)) THEN
  ASM_SIMP_TAC[BROUWER_BALL] THEN REWRITE_TAC[NOT_FORALL_THM] THEN
  EXISTS_TAC `\x:real^N. &2 % a - x` THEN REWRITE_TAC[NOT_IMP] THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE] THEN
  SIMP_TAC[dist; VECTOR_ARITH `a - (&2 % a - x) = --(a - x)`; NORM_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `(&2 % a - y = y) <=> (a - y = vec 0)`] THEN
  ASM_MESON_TAC[NORM_0; REAL_LT_REFL]);;

let FRONTIER_SUBSET_RETRACTION = prove
 (`!s:real^N->bool t r.
        bounded s /\
        frontier s SUBSET t /\
        r continuous_on (closure s) /\
        IMAGE r s SUBSET t /\
        (!x. x IN t ==> r x = x)
        ==> s SUBSET t`,
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[SET_RULE `~(s SUBSET t) <=> ?x. x IN s /\ ~(x IN t)`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  REPLICATE_TAC 3 GEN_TAC THEN X_GEN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = \z:real^N. if z IN closure s then r(z) else z` THEN
  SUBGOAL_THEN
    `(q:real^N->real^N) continuous_on
      closure(s) UNION closure((:real^N) DIFF s)`
  MP_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[TAUT `p /\ ~p <=> F`] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; frontier; IN_DIFF]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(s) UNION closure((:real^N) DIFF s) = (:real^N)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s SUBSET closure s /\ t SUBSET closure t /\ s UNION t = UNIV
      ==> closure s UNION closure t = UNIV`) THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN SET_TAC[];
    DISCH_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o SPEC `a:real^N` o
    MATCH_MP BOUNDED_SUBSET_BALL o MATCH_MP BOUNDED_CLOSURE) THEN
  SUBGOAL_THEN `!x. ~((q:real^N->real^N) x = a)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN COND_CASES_TAC THENL
     [ASM_CASES_TAC `(x:real^N) IN s` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN t` (fun th -> ASM_MESON_TAC[th]) THEN
      UNDISCH_TAC `frontier(s:real^N->bool) SUBSET t` THEN
      REWRITE_TAC[SUBSET; frontier; IN_DIFF] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET; CLOSURE_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `B:real`] NO_RETRACTION_CBALL) THEN
  ASM_REWRITE_TAC[retract_of; GSYM FRONTIER_CBALL] THEN
  EXISTS_TAC `(\y. a + B / norm(y - a) % (y - a)) o (q:real^N->real^N)` THEN
  REWRITE_TAC[retraction; FRONTIER_SUBSET_EQ; CLOSED_CBALL] THEN
  REWRITE_TAC[FRONTIER_CBALL; SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_SPHERE; DIST_0] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    SUBGOAL_THEN `(\x:real^N. lift(norm(x - a))) = (lift o norm) o (\x. x - a)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC[o_THM; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                NORM_ARITH `dist(a,a + b) = norm b`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; VECTOR_SUB_EQ; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_BALL]) THEN
      ASM_MESON_TAC[REAL_LT_REFL];
      REWRITE_TAC[NORM_ARITH `norm(x - a) = dist(a,x)`] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC]]);;

let NO_RETRACTION_FRONTIER_BOUNDED = prove
 (`!s:real^N->bool.
        bounded s /\ ~(interior s = {}) ==> ~((frontier s) retract_of s)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  REWRITE_TAC[FRONTIER_SUBSET_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `frontier s:real^N->bool`;
                 `r:real^N->real^N`] FRONTIER_SUBSET_RETRACTION) THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; SUBSET_REFL] THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

let COMPACT_SUBSET_FRONTIER_RETRACTION = prove
 (`!f:real^N->real^N s.
        compact s /\ f continuous_on s /\ (!x. x IN frontier s ==> f x = x)
        ==> s SUBSET IMAGE f s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s UNION (IMAGE f s):real^N->bool`; `vec 0:real^N`]
    BOUNDED_SUBSET_BALL) THEN
  ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED;
               COMPACT_CONTINUOUS_IMAGE; UNION_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \x:real^N. if x IN s then f(x) else x` THEN
  SUBGOAL_THEN `(g:real^N->real^N) continuous_on (:real^N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(:real^N) = s UNION closure((:real^N) DIFF s)` SUBST1_TAC
    THENL
     [MATCH_MP_TAC(SET_RULE `UNIV DIFF s SUBSET t ==> UNIV = s UNION t`) THEN
      REWRITE_TAC[CLOSURE_SUBSET];
      ALL_TAC] THEN
    EXPAND_TAC "g" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[CLOSED_CLOSURE; CONTINUOUS_ON_ID; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[TAUT `p /\ ~p <=> F`] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[frontier; IN_DIFF] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?h:real^N->real^N.
        retraction (UNIV DELETE p,sphere(vec 0,r)) h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM retract_of] THEN
    MATCH_MP_TAC SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `r:real`] NO_RETRACTION_CBALL) THEN
  ASM_REWRITE_TAC[retract_of; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) o (g:real^N->real^N)`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[retraction] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  SIMP_TAC[SUBSET; IN_SPHERE; IN_CBALL; REAL_EQ_IMP_LE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN cball (vec 0,r) ==> ~((g:real^N->real^N) x = p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    COND_CASES_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE];
    SUBGOAL_THEN `(g:real^N->real^N) x = x` (fun th -> ASM_SIMP_TAC[th]) THEN
    EXPAND_TAC "g" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_BALL; REAL_LT_REFL; SUBSET]]);;

let NOT_ABSOLUTE_RETRACT_COBOUNDED = prove
 (`!s. bounded s /\ ((:real^N) DIFF s) retract_of (:real^N) ==> s = {}`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> F) ==> s = {}`) THEN
  X_GEN_TAC `a:real^N` THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o
    MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP NO_RETRACTION_CBALL) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RETRACT_OF_SUBSET THEN
  EXISTS_TAC `(:real^N)` THEN SIMP_TAC[SUBSET_UNIV; SPHERE_SUBSET_CBALL] THEN
  MATCH_MP_TAC RETRACT_OF_TRANS THEN EXISTS_TAC `(:real^N) DIFF s` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RETRACT_OF_SUBSET THEN
  EXISTS_TAC `(:real^N) DELETE (vec 0)` THEN
  ASM_SIMP_TAC[SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_SPHERE; IN_DIFF; IN_UNIV] THEN
  MESON_TAC[REAL_LT_REFL]);;

let CONTRACTIBLE_SPHERE = prove
 (`!a:real^N r. contractible(sphere(a,r)) <=> r <= &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contractible; GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[NULLHOMOTOPIC_FROM_SPHERE_EXTENSION] THEN
  ASM_CASES_TAC `&0 < r` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o ISPEC `a:real^N` o MATCH_MP NO_RETRACTION_CBALL) THEN
    SIMP_TAC[retract_of; retraction; SPHERE_SUBSET_CBALL];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
    EXISTS_TAC `\x:real^N. x` THEN REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_SPHERE; IN_ELIM_THM] THEN
    POP_ASSUM MP_TAC THEN NORM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Some more theorems about connectivity of retract complements.             *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_COMPONENT_RETRACT_COMPLEMENT_MEETS = prove
 (`!s t c. closed s /\ s retract_of t /\
           c IN components((:real^N) DIFF s) /\ bounded c
           ==> ~(c SUBSET t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `frontier(c:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS `frontier((:real^N) DIFF s)` THEN
    ASM_SIMP_TAC[FRONTIER_OF_COMPONENTS_SUBSET] THEN
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(c:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_RETRACTION THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
    REWRITE_TAC[retraction] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
    ASM SET_TAC[]]);;

let COMPONENT_RETRACT_COMPLEMENT_MEETS = prove
 (`!s t c. closed s /\ s retract_of t /\ bounded t /\
           c IN components((:real^N) DIFF s)
           ==> ~(c SUBSET t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ASM_CASES_TAC `bounded(c:real^N->bool)` THENL
   [ASM_MESON_TAC[BOUNDED_COMPONENT_RETRACT_COMPLEMENT_MEETS];
    ASM_MESON_TAC[BOUNDED_SUBSET]]);;

let FINITE_COMPLEMENT_ENR_COMPONENTS = prove
 (`!s. compact s /\ ENR s ==> FINITE(components((:real^N) DIFF s))`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[DIFF_EMPTY] THEN
    MESON_TAC[COMPONENTS_EQ_SING; CONNECTED_UNIV; UNIV_NOT_EMPTY; FINITE_SING];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[ENR_BOUNDED; COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!c. c IN components((:real^N) DIFF s) ==> ~(c SUBSET u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPONENT_RETRACT_COMPLEMENT_MEETS THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `vec 0:real^N`]
        BOUNDED_SUBSET_CBALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `cball(vec 0:real^N,r) DIFF u` COMPACT_EQ_HEINE_BOREL) THEN
  ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `components((:real^N) DIFF s)`) THEN
  REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[OPEN_COMPONENTS; closed; COMPACT_IMP_CLOSED];
    DISCH_THEN(X_CHOOSE_THEN `cs:(real^N->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `components((:real^N) DIFF s) = cs`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `c:real^N->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(c INTER (cball(vec 0:real^N,r) DIFF u) = {})` MP_TAC THENL
   [SUBGOAL_THEN `~(c INTER frontier(u:real^N->bool) = {})` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      ASM_SIMP_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      W(MP_TAC o PART_MATCH (rand o rand)
        OPEN_INTER_CLOSURE_EQ_EMPTY o rand o snd) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN
      MATCH_MP_TAC(SET_RULE
       `~(t = {}) /\ t SUBSET u
        ==> ~(u INTER (s UNION t) = {})`) THEN
      ASM_REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      TRANS_TAC SUBSET_TRANS `frontier((:real^N) DIFF s)` THEN
      ASM_SIMP_TAC[FRONTIER_OF_COMPONENTS_SUBSET] THEN
      REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
      ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `s SUBSET t
        ==> ~(c INTER s = {}) ==> ~(c INTER t = {})`) THEN
      ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t DIFF u`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[CLOSED_CBALL]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS cs` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^N) DIFF s`; `c:real^N->bool`; `c':real^N->bool`]
        COMPONENTS_NONOVERLAP) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `c:real^N->bool = c'` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let FINITE_COMPLEMENT_ANR_COMPONENTS = prove
 (`!s. compact s /\ ANR s ==> FINITE(components((:real^N) DIFF s))`,
  MESON_TAC[FINITE_COMPLEMENT_ENR_COMPONENTS; ENR_ANR;
            COMPACT_IMP_CLOSED; CLOSED_IMP_LOCALLY_COMPACT]);;

let CARD_LE_RETRACT_COMPLEMENT_COMPONENTS = prove
 (`!s t. compact s /\ s retract_of t /\ bounded t
         ==> components((:real^N) DIFF s) <=_c components((:real^N) DIFF t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  MATCH_MP_TAC(ISPEC `SUBSET` CARD_LE_RELATIONAL_FULL) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC
     [`d:real^N->bool`; `c:real^N->bool`; `c':real^N->bool`] THEN
    STRIP_TAC THEN MP_TAC(ISPEC `(:real^N) DIFF s` COMPONENTS_EQ) THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `d:real^N->bool = {}` THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((u:real^N->bool) SUBSET t)` MP_TAC THENL
   [MATCH_MP_TAC COMPONENT_RETRACT_COMPLEMENT_MEETS THEN
    ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `~(s SUBSET t) <=> ?p. p IN s /\ ~(p IN t)`] THEN
  REWRITE_TAC[components; EXISTS_IN_GSPEC; IN_UNIV; IN_DIFF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u = connected_component ((:real^N) DIFF s) p`
  SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DIFF s`; `u:real^N->bool`]
      COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[components; FORALL_IN_GSPEC; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM SET_TAC[]]);;

let CONNECTED_RETRACT_COMPLEMENT = prove
 (`!s t. compact s /\ s retract_of t /\ bounded t /\
         connected((:real^N) DIFF t)
         ==> connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONNECTED_EQ_COMPONENTS_SUBSET_SING_EXISTS] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real^N->bool`) THEN
  SUBGOAL_THEN `FINITE(components((:real^N) DIFF t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        CARD_LE_RETRACT_COMPLEMENT_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `FINITE(components((:real^N) DIFF s)) /\
    CARD(components((:real^N) DIFF s)) <= CARD(components((:real^N) DIFF t))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_LE_CARD_IMP; CARD_LE_FINITE]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  REWRITE_TAC[EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM HAS_SIZE_0; GSYM(HAS_SIZE_CONV `s HAS_SIZE 1`)] THEN
  ASM_REWRITE_TAC[HAS_SIZE; ARITH_RULE `n = 0 \/ n = 1 <=> n <= 1`] THEN
  TRANS_TAC LE_TRANS `CARD{u:real^N->bool}` THEN CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `CARD(components((:real^N) DIFF t))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_SING];
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* We also get fixpoint properties for suitable ANRs.                        *)
(* ------------------------------------------------------------------------- *)

let BROUWER_INESSENTIAL_ANR = prove
 (`!f:real^N->real^N s.
        compact s /\ ~(s = {}) /\ ANR s /\
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (?a. homotopic_with (\x. T) (s,s) f (\x. a))
        ==> ?x. x IN s /\ f x = x`,
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:real` o SPEC `vec 0:real^N` o
    MATCH_MP BOUNDED_SUBSET_CBALL o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  MP_TAC(ISPECL
   [`(\x. a):real^N->real^N`; `f:real^N->real^N`;
    `s:real^N->bool`; `cball(vec 0:real^N,r)`; `s:real^N->bool`]
    BORSUK_HOMOTOPY_EXTENSION) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_SUBSET;
               CONTINUOUS_ON_CONST; CLOSED_CBALL] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `cball(vec 0:real^N,r)`]
        BROUWER) THEN
  ASM_SIMP_TAC[COMPACT_CBALL; CONVEX_CBALL; CBALL_EQ_EMPTY] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> ~(r < &0)`] THEN ASM SET_TAC[]);;

let BROUWER_CONTRACTIBLE_ANR = prove
 (`!f:real^N->real^N s.
        compact s /\ contractible s /\ ~(s = {}) /\ ANR s /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_INESSENTIAL_ANR THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NULLHOMOTOPIC_FROM_CONTRACTIBLE THEN ASM_REWRITE_TAC[]);;

let FIXED_POINT_INESSENTIAL_SPHERE_MAP = prove
 (`!f a:real^N r c.
     &0 < r /\ homotopic_with (\x. T) (sphere(a,r),sphere(a,r)) f (\x. c)
     ==> ?x. x IN sphere(a,r) /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_INESSENTIAL_ANR THEN
  REWRITE_TAC[ANR_SPHERE] THEN
  ASM_SIMP_TAC[SPHERE_EQ_EMPTY; COMPACT_SPHERE; OPEN_DELETE; OPEN_UNIV] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN ASM_MESON_TAC[]);;

let BROUWER_AR = prove
 (`!f s:real^N->bool.
        compact s /\ AR s /\ f continuous_on s /\ IMAGE f s SUBSET s
         ==> ?x. x IN s /\ f x = x`,
  REWRITE_TAC[AR_ANR] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_CONTRACTIBLE_ANR THEN
  ASM_REWRITE_TAC[]);;

let BROUWER_ABSOLUTE_RETRACT = prove
 (`!f s. compact s /\ s retract_of (:real^N) /\
         f continuous_on s /\ IMAGE f s SUBSET s
         ==> ?x. x IN s /\ f x = x`,
  REWRITE_TAC[RETRACT_OF_UNIV; AR_ANR] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_CONTRACTIBLE_ANR THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* This interresting lemma is no longer used for Schauder but we keep it.    *)
(* ------------------------------------------------------------------------- *)

let SCHAUDER_PROJECTION = prove
 (`!s:real^N->bool e.
        compact s /\ &0 < e
        ==> ?t f. FINITE t /\ t SUBSET s /\
                  f continuous_on s /\ IMAGE f s SUBSET (convex hull t) /\
                  (!x. x IN s ==> norm(f x - x) < e)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o SPEC `e:real` o MATCH_MP COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = \p x:real^N. max (&0) (e - norm(x - p))` THEN
  SUBGOAL_THEN
   `!x. x IN s ==> &0 < sum t (\p. (g:real^N->real^N->real) p x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[REAL_ARITH `&0 <= max (&0) b`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < max (&0) b <=> &0 < b`; REAL_SUB_LT] THEN
    UNDISCH_TAC `s SUBSET UNIONS (IMAGE (\x:real^N. ball(x,e)) t)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_BALL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[dist; NORM_SUB];
    ALL_TAC] THEN
  EXISTS_TAC
   `(\x. inv(sum t (\p. g p x)) % vsum t (\p. g p x % p)):real^N->real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; LIFT_SUM; o_DEF];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
     [ALL_TAC; MATCH_MP_TAC CONTINUOUS_ON_MUL] THEN
    REWRITE_TAC[o_DEF; CONTINUOUS_ON_CONST] THEN
    EXPAND_TAC "g" THEN
    (SUBGOAL_THEN
      `(\x. lift (max (&0) (e - norm (x - y:real^N)))) =
       (\x. (lambda i. max (lift(&0)$i) (lift(e - norm (x - y))$i)))`
     SUBST1_TAC THENL
      [SIMP_TAC[CART_EQ; LAMBDA_BETA; FUN_EQ_THM] THEN
       REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP];
       MATCH_MP_TAC CONTINUOUS_ON_MAX] THEN
     REWRITE_TAC[CONTINUOUS_ON_CONST; LIFT_SUB] THEN
     MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
     REWRITE_TAC[ONCE_REWRITE_RULE[NORM_SUB] (GSYM dist)] THEN
     REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DIST]);
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
    ASM_SIMP_TAC[HULL_INC; CONVEX_CONVEX_HULL; SUM_LMUL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "g" THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[REWRITE_RULE[dist] (GSYM IN_BALL)] THEN
    REWRITE_TAC[GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC CONVEX_VSUM_STRONG THEN
    ASM_REWRITE_TAC[CONVEX_BALL; SUM_LMUL; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_LT_INV_EQ;
                 REAL_LE_MUL_EQ] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[IN_BALL; dist; NORM_SUB] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Some other related fixed-point theorems.                                  *)
(* ------------------------------------------------------------------------- *)

let BROUWER_FACTOR_THROUGH_AR = prove
 (`!f:real^M->real^N g:real^N->real^M s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        compact s /\ AR t
        ==> ?x. x IN s /\ g(f x) = x`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [COMPACT_EQ_BOUNDED_CLOSED]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^M` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`;
                 `s:real^M->bool`; `t:real^N->bool`]
        AR_IMP_ABSOLUTE_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(g:real^N->real^M) o (h:real^M->real^N)`;
                 `a:real^M`; `r:real`] BROUWER_BALL) THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV; IMAGE_SUBSET]);;

let BROUWER_ABSOLUTE_RETRACT_GEN = prove
 (`!f s:real^N->bool.
           s retract_of (:real^N) /\
           f continuous_on s /\ IMAGE f s SUBSET s /\ bounded(IMAGE f s)
           ==> ?x. x IN s /\ f x = x`,
  REWRITE_TAC[RETRACT_OF_UNIV] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `f:real^N->real^N`;
                 `closure(IMAGE (f:real^N->real^N) s)`; `s:real^N->bool`]
        BROUWER_FACTOR_THROUGH_AR) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; COMPACT_CLOSURE; IMAGE_ID] THEN
  REWRITE_TAC[CLOSURE_SUBSET] THEN
  MATCH_MP_TAC(TAUT `(p /\ q ==> r) /\ p ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC CLOSURE_MINIMAL] THEN
  ASM_MESON_TAC[RETRACT_OF_CLOSED; CLOSED_UNIV]);;

let SCHAUDER_GEN = prove
 (`!f s t:real^N->bool.
     AR s /\ f continuous_on s /\ IMAGE f s SUBSET t /\ t SUBSET s /\ compact t
     ==> ?x. x IN t /\ f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `f:real^N->real^N`;
                 `t:real^N->bool`; `s:real^N->bool`]
        BROUWER_FACTOR_THROUGH_AR) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let SCHAUDER = prove
 (`!f s t:real^N->bool.
        convex s /\ ~(s = {}) /\ t SUBSET s /\ compact t /\
        f continuous_on s /\ IMAGE f s SUBSET t
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`; `t:real^N->bool`]
        SCHAUDER_GEN) THEN
  ASM_SIMP_TAC[CONVEX_IMP_AR] THEN ASM SET_TAC[]);;

let SCHAUDER_UNIV = prove
 (`!f:real^N->real^N.
        f continuous_on (:real^N) /\ bounded (IMAGE f (:real^N))
        ==> ?x. f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `(:real^N)`;
                 `closure(IMAGE (f:real^N->real^N) (:real^N))`] SCHAUDER) THEN
  ASM_REWRITE_TAC[UNIV_NOT_EMPTY; CONVEX_UNIV; COMPACT_CLOSURE; IN_UNIV] THEN
  REWRITE_TAC[SUBSET_UNIV; CLOSURE_SUBSET]);;

let ROTHE = prove
 (`!f s:real^N->bool.
        closed s /\ convex s /\ ~(s = {}) /\
        f continuous_on s /\ bounded(IMAGE f s) /\
        IMAGE f (frontier s) SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
    ABSOLUTE_RETRACTION_CONVEX_CLOSED) THEN
  ASM_REWRITE_TAC[retraction; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`(r:real^N->real^N) o (f:real^N->real^N)`; `s:real^N->bool`;
    `IMAGE (r:real^N->real^N) (closure(IMAGE (f:real^N->real^N) s))`]
   SCHAUDER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET; IMAGE_o] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[o_THM] THEN STRIP_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Perron-Frobenius theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let PERRON_FROBENIUS = prove
 (`!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> &0 <= A$i$j)
        ==> ?v c. norm v = &1 /\ &0 <= c /\ A ** v = c % v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?v. ~(v = vec 0) /\ (A:real^N^N) ** v = vec 0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv(norm v) % v:real^N` THEN EXISTS_TAC `&0` THEN
    ASM_SIMP_TAC[REAL_LE_REFL; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                 REAL_MUL_LINV; NORM_EQ_0; MATRIX_VECTOR_MUL_RMUL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\x:real^N. inv(vec 1 dot (A ** x)) % ((A:real^N^N) ** x)`;
    `{x:real^N | vec 1 dot x = &1} INTER
     {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}`]
   BROUWER) THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_POSITIVE_ORTHANT; CONVEX_HYPERPLANE] THEN
  SUBGOAL_THEN
   `!x. (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i)
        ==> !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= ((A:real^N^N) ** x)$i`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_MESON_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i) /\ vec 1 dot x = &1
        ==> &0 < vec 1 dot ((A:real^N^N) ** x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    DISCH_TAC THEN REWRITE_TAC[dot; VEC_COMPONENT; REAL_MUL_LID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        SUM_POS_EQ_0_NUMSEG)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CART_EQ; VEC_COMPONENT]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER; CLOSED_HYPERPLANE;
               CLOSED_POSITIVE_ORTHANT] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^N,vec 1]` THEN
      SIMP_TAC[BOUNDED_INTERVAL; SUBSET; IN_INTER; IN_ELIM_THM; IN_INTERVAL;
               dot; VEC_COMPONENT; REAL_MUL_LID] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      TRANS_TAC REAL_LE_TRANS `sum {i} (\i. (x:real^N)$i)` THEN
      CONJ_TAC THENL [REWRITE_TAC[SUM_SING; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_SING; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[SING_SUBSET; IN_SING; IN_DIFF; IN_NUMSEG];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^N` THEN
      SIMP_TAC[IN_INTER; IN_ELIM_THM; BASIS_COMPONENT] THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[REAL_POS]] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL; VEC_COMPONENT];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR; o_DEF] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_DOT2; MATRIX_VECTOR_MUL_LINEAR;
               CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_LT_REFL];
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_RMUL] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
        REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_MESON_TAC[REAL_LT_IMP_LE]]];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    STRIP_TAC THEN EXISTS_TAC `inv(norm x) % x:real^N` THEN
    EXISTS_TAC `vec 1 dot ((A:real^N^N) ** x)` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      ASM_MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o AP_TERM
        `(%) (vec 1 dot ((A:real^N^N) ** x)):real^N->real^N`) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_EQ_0; VECTOR_ARITH
       `v:real^N = c % v <=> (c - &1) % v = vec 0`] THEN
      DISJ1_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Bijections between intervals.                                             *)
(* ------------------------------------------------------------------------- *)

let interval_bij = new_definition
 `interval_bij (a:real^N,b:real^N) (u:real^N,v:real^N) (x:real^N) =
    (lambda i. u$i + (x$i - a$i) / (b$i - a$i) * (v$i - u$i)):real^N`;;

let INTERVAL_BIJ_AFFINE = prove
 (`interval_bij (a,b) (u,v) =
        \x. (lambda i. (v$i - u$i) / (b$i - a$i) * x$i) +
            (lambda i. u$i - (v$i - u$i) / (b$i - a$i) * a$i)`,
  SIMP_TAC[FUN_EQ_THM; CART_EQ; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
           interval_bij] THEN
  REAL_ARITH_TAC);;

let CONTINUOUS_INTERVAL_BIJ = prove
 (`!a b u v x. (interval_bij (a:real^N,b:real^N) (u:real^N,v:real^N))
                  continuous at x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INTERVAL_BIJ_AFFINE] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  SIMP_TAC[linear; CART_EQ; LAMBDA_BETA;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let CONTINUOUS_ON_INTERVAL_BIJ = prove
 (`!a b u v s. interval_bij (a,b) (u,v) continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[CONTINUOUS_INTERVAL_BIJ]);;

let IN_INTERVAL_INTERVAL_BIJ = prove
 (`!a b u v x:real^N.
        x IN interval[a,b] /\ ~(interval[u,v] = {})
        ==> (interval_bij (a,b) (u,v) x) IN interval[u,v]`,
  SIMP_TAC[IN_INTERVAL; interval_bij; LAMBDA_BETA; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[REAL_ARITH `u <= u + x <=> &0 <= x`;
              REAL_ARITH `u + x <= v <=> x <= &1 * (v - u)`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_SIMP_TAC[REAL_SUB_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_SUB_LE] THEN
    SUBGOAL_THEN `(a:real^N)$i <= (b:real^N)$i` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
      ASM_SIMP_TAC[REAL_ARITH `a <= x /\ x <= b ==> x - a <= &1 * (b - a)`];
      ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_INV_0] THEN
      REAL_ARITH_TAC]]);;

let INTERVAL_BIJ_BIJ = prove
 (`!a b u v x:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i /\ u$i < v$i)
        ==> interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x`,
  SIMP_TAC[interval_bij; CART_EQ; LAMBDA_BETA; REAL_ADD_SUB] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Fashoda meet theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let INFNORM_2 = prove
 (`infnorm (x:real^2) = max (abs(x$1)) (abs(x$2))`,
  REWRITE_TAC[infnorm; INFNORM_SET_IMAGE; NUMSEG_CONV `1..2`; DIMINDEX_2] THEN
  REWRITE_TAC[IMAGE_CLAUSES; GSYM REAL_MAX_SUP]);;

let INFNORM_EQ_1_2 = prove
 (`infnorm (x:real^2) = &1 <=>
        abs(x$1) <= &1 /\ abs(x$2) <= &1 /\
        (x$1 = -- &1 \/ x$1 = &1 \/ x$2 = -- &1 \/ x$2 = &1)`,
  REWRITE_TAC[INFNORM_2] THEN REAL_ARITH_TAC);;

let INFNORM_EQ_1_IMP = prove
 (`infnorm (x:real^2) = &1 ==> abs(x$1) <= &1 /\ abs(x$2) <= &1`,
  SIMP_TAC[INFNORM_EQ_1_2]);;

let FASHODA_UNIT = prove
 (`!f:real^1->real^2 g:real^1->real^2.
        IMAGE f (interval[--vec 1,vec 1]) SUBSET interval[--vec 1,vec 1] /\
        IMAGE g (interval[--vec 1,vec 1]) SUBSET interval[--vec 1,vec 1] /\
        f continuous_on interval[--vec 1,vec 1] /\
        g continuous_on interval[--vec 1,vec 1] /\
        f(--vec 1)$1 = -- &1 /\ f(vec 1)$1 = &1 /\
        g(--vec 1)$2 = -- &1 /\ g(vec 1)$2 = &1
        ==> ?s t. s IN interval[--vec 1,vec 1] /\
                  t IN interval[--vec 1,vec 1] /\
                  f(s) = g(t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN DISCH_TAC THEN
  ABBREV_TAC `sqprojection = \z:real^2. inv(infnorm z) % z` THEN
  ABBREV_TAC `(negatex:real^2->real^2) = \x. vector[--(x$1); x$2]` THEN
  SUBGOAL_THEN `!z:real^2. infnorm(negatex z:real^2) = infnorm z` ASSUME_TAC
  THENL
   [EXPAND_TAC "negatex" THEN SIMP_TAC[VECTOR_2; INFNORM_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z = vec 0) ==> infnorm((sqprojection:real^2->real^2) z) = &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "sqprojection" THEN
    REWRITE_TAC[INFNORM_MUL; REAL_ABS_INFNORM; REAL_ABS_INV] THEN
    SIMP_TAC[REAL_MUL_LINV; INFNORM_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\w. (negatex:real^2->real^2)
                       (sqprojection(f(lift(w$1)) - g(lift(w$2)):real^2)))
                  :real^2->real^2`;
                 `interval[--vec 1,vec 1]:real^2->bool`]
         BROUWER_WEAK) THEN
  REWRITE_TAC[NOT_IMP; COMPACT_INTERVAL; CONVEX_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN EXPAND_TAC "negatex" THEN
      SIMP_TAC[linear; VECTOR_2; CART_EQ; FORALL_2; DIMINDEX_2;
               VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
               VECTOR_ADD_COMPONENT; ARITH] THEN
      REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[--vec 1:real^1,vec 1]`;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      EXPAND_TAC "sqprojection" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_AT_INV THEN
      REWRITE_TAC[CONTINUOUS_AT_LIFT_INFNORM; INFNORM_EQ_0; VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL])] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
             VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; REAL_BOUNDS_LE;
             VECTOR_NEG_COMPONENT; VEC_COMPONENT; ARITH] THEN
    MATCH_MP_TAC INFNORM_EQ_1_IMP THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
             VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `infnorm(x:real^2) = &1` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [SYM th]) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
             VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x i. 1 <= i /\ i <= 2 /\ ~(x = vec 0)
           ==> (&0 < ((sqprojection:real^2->real^2) x)$i <=> &0 < x$i)) /\
    (!x i. 1 <= i /\ i <= 2 /\ ~(x = vec 0)
           ==> ((sqprojection x)$i < &0 <=> x$i < &0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sqprojection" THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; INFNORM_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  REWRITE_TAC[INFNORM_EQ_1_2; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (REPEAT_TCL DISJ_CASES_THEN (fun th -> ASSUME_TAC th THEN MP_TAC th))) THEN
  MAP_EVERY EXPAND_TAC ["x"; "negatex"] THEN REWRITE_TAC[VECTOR_2] THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `--x = -- &1 ==> &0 < x`));
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `--x = &1 ==> x < &0`));
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x = -- &1 ==> x < &0`));
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x = &1 ==> &0 < x`))] THEN
  W(fun (_,w) -> FIRST_X_ASSUM(fun th ->
   MP_TAC(PART_MATCH (lhs o rand) th (lhand w)))) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[VECTOR_SUB_EQ; ARITH] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
     ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
     SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
              VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
     REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH;
               LIFT_NEG; LIFT_NUM]
  THENL
   [MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(&0 < -- &1 - x$1)`);
    MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(&1 - x$1 < &0)`);
    MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(x$2 - -- &1 < &0)`);
    MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(&0 < x$2 - &1)`)] THEN
  (SUBGOAL_THEN `!z:real^2. abs(z$1) <= &1 /\ abs(z$2) <= &1 <=>
                           z IN interval[--vec 1,vec 1]`
    (fun th -> REWRITE_TAC[th]) THENL
    [SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
              VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s SUBSET t ==> x IN s ==> f x IN t`)) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
  ASM_REWRITE_TAC[REAL_BOUNDS_LE]);;

let FASHODA_UNIT_PATH = prove
 (`!f:real^1->real^2 g:real^1->real^2.
        path f /\ path g /\
        path_image f SUBSET interval[--vec 1,vec 1] /\
        path_image g SUBSET interval[--vec 1,vec 1] /\
        (pathstart f)$1 = -- &1 /\ (pathfinish f)$1 = &1 /\
        (pathstart g)$2 = -- &1 /\ (pathfinish g)$2 = &1
        ==> ?z. z IN path_image f /\ z IN path_image g`,
  SIMP_TAC[path; path_image; pathstart; pathfinish] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `iscale = \z:real^1. inv(&2) % (z + vec 1)` THEN
  MP_TAC(ISPECL
   [`(f:real^1->real^2) o (iscale:real^1->real^1)`;
    `(g:real^1->real^2) o (iscale:real^1->real^1)`]
   FASHODA_UNIT) THEN
  SUBGOAL_THEN
   `IMAGE (iscale:real^1->real^1) (interval[--vec 1,vec 1])
    SUBSET interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "iscale" THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(iscale:real^1->real^1) continuous_on interval [--vec 1,vec 1]`
  ASSUME_TAC THENL
   [EXPAND_TAC "iscale" THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_ADD;
             CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
   [REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ALL_TAC]) THEN
    EXPAND_TAC "iscale" THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `inv(&2) % (--x + x) = vec 0`;
                    VECTOR_ARITH `inv(&2) % (x + x) = x`];
    REWRITE_TAC[o_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN ASM SET_TAC[]]);;

let FASHODA = prove
 (`!f g a b:real^2.
        path f /\ path g /\
        path_image f SUBSET interval[a,b] /\
        path_image g SUBSET interval[a,b] /\
        (pathstart f)$1 = a$1 /\ (pathfinish f)$1 = b$1 /\
        (pathstart g)$2 = a$2 /\ (pathfinish g)$2 = b$2
        ==> ?z. z IN path_image f /\ z IN path_image g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^2,b] = {})` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`)) THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `(a:real^2)$1 <= (b:real^2)$1`) THEN
  REWRITE_TAC[REAL_ARITH `a <= b <=> b = a \/ a < b`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN
      `?z:real^2. z IN path_image g /\ z$2 = (pathstart f:real^2)$2`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [`pathstart(g:real^1->real^2)`;
                            `pathfinish(g:real^1->real^2)`] THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE; REAL_LE_REFL;
                   PATHFINISH_IN_PATH_IMAGE; DIMINDEX_2; ARITH] THEN
      UNDISCH_TAC `path_image f SUBSET interval[a:real^2,b]` THEN
      REWRITE_TAC[SUBSET; path_image; IN_INTERVAL_1; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN SIMP_TAC[pathstart] THEN
      SIMP_TAC[DROP_VEC; REAL_POS; IN_INTERVAL; FORALL_2; DIMINDEX_2];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[path_image; IN_IMAGE] THEN
    EXISTS_TAC `vec 0:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
    ASM_REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2; pathstart] THEN
    SUBGOAL_THEN
     `(z:real^2) IN interval[a,b] /\ f(vec 0:real^1) IN interval[a,b]`
    MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; path_image; IN_IMAGE; PATHSTART_IN_PATH_IMAGE;
                    pathstart];
      ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ASSUME `(a:real^2)$2 <= (b:real^2)$2`) THEN
  REWRITE_TAC[REAL_ARITH `a <= b <=> b = a \/ a < b`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN
      `?z:real^2. z IN path_image f /\ z$1 = (pathstart g:real^2)$1`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [`pathstart(f:real^1->real^2)`;
                            `pathfinish(f:real^1->real^2)`] THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE; REAL_LE_REFL;
                   PATHFINISH_IN_PATH_IMAGE; DIMINDEX_2; ARITH] THEN
      UNDISCH_TAC `path_image g SUBSET interval[a:real^2,b]` THEN
      REWRITE_TAC[SUBSET; path_image; IN_INTERVAL_1; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN SIMP_TAC[pathstart] THEN
      SIMP_TAC[DROP_VEC; REAL_POS; IN_INTERVAL; FORALL_2; DIMINDEX_2];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[path_image; IN_IMAGE] THEN
    EXISTS_TAC `vec 0:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
    ASM_REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2; pathstart] THEN
    SUBGOAL_THEN
     `(z:real^2) IN interval[a,b] /\ g(vec 0:real^1) IN interval[a,b]`
    MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; path_image; IN_IMAGE; PATHSTART_IN_PATH_IMAGE;
                    pathstart];
      ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval_bij (a,b) (--vec 1,vec 1) o (f:real^1->real^2)`;
    `interval_bij (a,b) (--vec 1,vec 1) o (g:real^1->real^2)`]
   FASHODA_UNIT_PATH) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path; path_image; pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish; o_THM] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; CONTINUOUS_ON_INTERVAL_BIJ] THEN
    REWRITE_TAC[IMAGE_o] THEN REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_INTERVAL_INTERVAL_BIJ THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM SET_TAC[];
      ALL_TAC]) THEN
    ASM_SIMP_TAC[interval_bij; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
    REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    SIMP_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT; DIMINDEX_2; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2`
   (fun th -> EXISTS_TAC `interval_bij (--vec 1,vec 1) (a,b) (z:real^2)` THEN
              MP_TAC th)) THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> g(f(x)) = x) ==> x IN IMAGE f s ==> g x IN s`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERVAL_BIJ_BIJ THEN
  ASM_SIMP_TAC[FORALL_2; DIMINDEX_2; VECTOR_NEG_COMPONENT; VEC_COMPONENT;
               ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad hoc lemmas I use below                                   *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_VERTICAL = prove
 (`!a:real^2 b:real^2 x:real^2.
      a$1 = b$1
      ==> (x IN segment[a,b] <=>
           x$1 = a$1 /\ x$1 = b$1 /\
           (a$2 <= x$2 /\ x$2 <= b$2 \/ b$2 <= x$2 /\ x$2 <= a$2))`,
  GEOM_ORIGIN_TAC `a:real^2` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_LE_LADD;
              REAL_EQ_ADD_LCANCEL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBST1_TAC(SYM(ISPEC `b:real^2` BASIS_EXPANSION)) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^2 = &0 % basis 2`) THEN
  REWRITE_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM; CART_EQ] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH;
           REAL_MUL_RZERO; REAL_MUL_RID] THEN MESON_TAC[]);;

let SEGMENT_HORIZONTAL = prove
 (`!a:real^2 b:real^2 x:real^2.
      a$2 = b$2
      ==> (x IN segment[a,b] <=>
           x$2 = a$2 /\ x$2 = b$2 /\
           (a$1 <= x$1 /\ x$1 <= b$1 \/ b$1 <= x$1 /\ x$1 <= a$1))`,
  GEOM_ORIGIN_TAC `a:real^2` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_LE_LADD;
              REAL_EQ_ADD_LCANCEL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBST1_TAC(SYM(ISPEC `b:real^2` BASIS_EXPANSION)) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^2 = &0 % basis 1`) THEN
  REWRITE_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM; CART_EQ] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH;
           REAL_MUL_RZERO; REAL_MUL_RID] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful Fashoda corollary pointed out to me by Tom Hales.                  *)
(* ------------------------------------------------------------------------- *)

let FASHODA_INTERLACE = prove
 (`!f g a b:real^2.
        path f /\ path g /\
        path_image f SUBSET interval[a,b] /\
        path_image g SUBSET interval[a,b] /\
        (pathstart f)$2 = a$2 /\ (pathfinish f)$2 = a$2 /\
        (pathstart g)$2 = a$2 /\ (pathfinish g)$2 = a$2 /\
        (pathstart f)$1 < (pathstart g)$1 /\
        (pathstart g)$1 < (pathfinish f)$1 /\
        (pathfinish f)$1 < (pathfinish g)$1
        ==> ?z. z IN path_image f /\ z IN path_image g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^2,b] = {})` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`)) THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart (f:real^1->real^2) IN interval[a,b] /\
    pathfinish f IN interval[a,b] /\
    pathstart g IN interval[a,b] /\
    pathfinish g IN interval[a,b]`
  MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`linepath(vector[a$1 - &2;a$2 - &2],vector[(pathstart f)$1;a$2 - &2]) ++
     linepath(vector[(pathstart f)$1;(a:real^2)$2 - &2],pathstart f) ++
     (f:real^1->real^2) ++
     linepath(pathfinish f,vector[(pathfinish f)$1;a$2 - &2]) ++
     linepath(vector[(pathfinish f)$1;a$2 - &2],
              vector[(b:real^2)$1 + &2;a$2 - &2])`;
    `linepath(vector[(pathstart g)$1; (pathstart g)$2 - &3],pathstart g) ++
     (g:real^1->real^2) ++
     linepath(pathfinish g,vector[(pathfinish g)$1;(a:real^2)$2 - &1]) ++
     linepath(vector[(pathfinish g)$1;a$2 - &1],vector[b$1 + &1;a$2 - &1]) ++
     linepath(vector[b$1 + &1;a$2 - &1],vector[(b:real^2)$1 + &1;b$2 + &3])`;
    `vector[(a:real^2)$1 - &2; a$2 - &3]:real^2`;
    `vector[(b:real^2)$1 + &2; b$2 + &3]:real^2`]
   FASHODA) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
  REWRITE_TAC[VECTOR_2] THEN ANTS_TAC THENL
   [CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC
            (SET_RULE `s SUBSET u /\ t SUBSET u ==> (s UNION t) SUBSET u`) THEN
           CONJ_TAC) THEN
    TRY(REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
        MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT]
           (CONJUNCT1 (SPEC_ALL CONVEX_INTERVAL))) THEN
        ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
        ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[a:real^2,b:real^2]` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
  SUBGOAL_THEN
   `!f s:real^2->bool. path_image f UNION s =
                       path_image f UNION (s DIFF {pathstart f,pathfinish f})`
   (fun th -> ONCE_REWRITE_TAC[th] THEN
              REWRITE_TAC[GSYM UNION_ASSOC] THEN
              ONCE_REWRITE_TAC[SET_RULE `(s UNION t) UNION u =
                                         u UNION t UNION s`] THEN
              ONCE_REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; IN_DIFF; GSYM DISJ_ASSOC; LEFT_OR_DISTRIB;
              RIGHT_OR_DISTRIB; GSYM CONJ_ASSOC;
              SET_RULE `~(z IN {x,y}) <=> ~(z = x) /\ ~(z = y)`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THEN
  ASM_SIMP_TAC[SEGMENT_VERTICAL; SEGMENT_HORIZONTAL; VECTOR_2] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image (f:real^1->real^2) SUBSET interval [a,b]` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  UNDISCH_TAC `path_image (g:real^1->real^2) SUBSET interval [a,b]` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN
  REPEAT(DISCH_THEN(fun th -> if is_imp(concl th) then ALL_TAC else
    ASSUME_TAC th)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN TRY REAL_ARITH_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Complement in dimension N >= 2 of set homeomorphic to any interval in     *)
(* any dimension is (path-)connected. This naively generalizes the argument  *)
(* in Ryuji Maehara's paper "The Jordan curve theorem via the Brouwer        *)
(* fixed point theorem", American Mathematical Monthly 1984.                 *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_COMPONENTS_COMPLEMENT_ABSOLUTE_RETRACT = prove
 (`!s c. compact s /\ AR s /\ c IN components((:real^N) DIFF s)
         ==> ~bounded c`,
  REWRITE_TAC[CONJ_ASSOC; COMPACT_AR] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; components; FORALL_IN_GSPEC] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open((:real^N) DIFF s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`connected_component ((:real^N) DIFF s) y`;
                 `s:real^N->bool`;
                 `r:real^N->real^N`]
                FRONTIER_SUBSET_RETRACTION) THEN
  ASM_SIMP_TAC[NOT_IMP; INTERIOR_OPEN; OPEN_CONNECTED_COMPONENT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[INTERIOR_OPEN; OPEN_CONNECTED_COMPONENT] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^N` THEN
    ASM_CASES_TAC `(z:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IN_CLOSURE_CONNECTED_COMPONENT; IN_UNIV; IN_DIFF] THEN
    CONV_TAC TAUT;
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `~(c = {}) /\ c SUBSET (:real^N) DIFF s ==> ~(c SUBSET s)`) THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; CONNECTED_COMPONENT_EQ_EMPTY] THEN
    ASM_REWRITE_TAC[IN_UNIV; IN_DIFF]]);;

let CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT = prove
 (`!s. 2 <= dimindex(:N) /\ compact s /\ AR s
       ==> connected((:real^N) DIFF s)`,
  REWRITE_TAC[COMPACT_AR] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONNECTED_EQ_CONNECTED_COMPONENT_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT THEN
  ASM_SIMP_TAC[SET_RULE`UNIV DIFF (UNIV DIFF s) = s`; COMPACT_IMP_BOUNDED] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC UNBOUNDED_COMPONENTS_COMPLEMENT_ABSOLUTE_RETRACT THEN
  EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[CONJ_ASSOC; COMPACT_AR] THEN
  ASM_REWRITE_TAC[IN_COMPONENTS] THEN ASM_MESON_TAC[]);;

let PATH_CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT = prove
 (`!s:real^N->bool.
        2 <= dimindex(:N) /\ compact s /\ AR s
        ==> path_connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT) THEN
  MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC PATH_CONNECTED_EQ_CONNECTED THEN
  REWRITE_TAC[GSYM closed] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_INTERVAL;
                COMPACT_IMP_CLOSED]);;

let CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^M->bool.
        2 <= dimindex(:N) /\ s homeomorphic t /\ convex t /\ compact t
        ==> connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; CONNECTED_UNIV] THEN
  MATCH_MP_TAC CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_ARNESS) THEN
  ASM_MESON_TAC[CONVEX_IMP_AR; HOMEOMORPHIC_EMPTY]);;

let PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^M->bool.
        2 <= dimindex(:N) /\ s homeomorphic t /\ convex t /\ compact t
        ==> path_connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
  MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC PATH_CONNECTED_EQ_CONNECTED THEN
  REWRITE_TAC[GSYM closed] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_INTERVAL;
                COMPACT_IMP_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* In particular, apply all these to the special case of an arc.             *)
(* ------------------------------------------------------------------------- *)

let RETRACTION_ARC = prove
 (`!p. arc p
       ==> ?f. f continuous_on (:real^N) /\
               IMAGE f (:real^N) SUBSET path_image p /\
               (!x. x IN path_image p ==> f x = x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(:real^N)` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTE_RETRACT_PATH_IMAGE_ARC)) THEN
  REWRITE_TAC[SUBSET_UNIV; retract_of; retraction]);;

let PATH_CONNECTED_ARC_COMPLEMENT = prove
 (`!p. 2 <= dimindex(:N) /\ arc p
       ==> path_connected((:real^N) DIFF path_image p)`,
  REWRITE_TAC[arc; path] THEN REPEAT STRIP_TAC THEN SIMP_TAC[path_image] THEN
  MP_TAC(ISPECL [`path_image p:real^N->bool`; `interval[vec 0:real^1,vec 1]`]
        PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; path_image] THEN
  DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  EXISTS_TAC `p:real^1->real^N` THEN ASM_REWRITE_TAC[COMPACT_INTERVAL]);;

let CONNECTED_ARC_COMPLEMENT = prove
 (`!p. 2 <= dimindex(:N) /\ arc p
       ==> connected((:real^N) DIFF path_image p)`,
  SIMP_TAC[PATH_CONNECTED_ARC_COMPLEMENT; PATH_CONNECTED_IMP_CONNECTED]);;

let INSIDE_ARC_EMPTY = prove
 (`!p:real^1->real^N. arc p ==> inside(path_image p) = {}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [MATCH_MP_TAC INSIDE_CONVEX THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED_1_GEN; CONNECTED_PATH_IMAGE; ARC_IMP_PATH];
    MATCH_MP_TAC INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY THEN
    ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; ARC_IMP_PATH] THEN
    MATCH_MP_TAC CONNECTED_ARC_COMPLEMENT THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 <= n /\ ~(n = 1)`] THEN
    REWRITE_TAC[DIMINDEX_GE_1]]);;

let INSIDE_SIMPLE_CURVE_IMP_CLOSED = prove
 (`!g x:real^N.
        simple_path g /\ x IN inside(path_image g)
        ==> pathfinish g = pathstart g`,
  MESON_TAC[ARC_SIMPLE_PATH; INSIDE_ARC_EMPTY; NOT_IN_EMPTY]);;
