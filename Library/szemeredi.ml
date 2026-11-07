(* ========================================================================= *)
(* Szemeredi's theorem and related results of Ramsey theory: the             *)
(* Hales-Jewett, Folkman, Graham-Rothschild (for lines), density             *)
(* Hales-Jewett, van der Waerden, Roth and Szemeredi theorems (finite,       *)
(* density, counting and Z_N forms), multidimensional Szemeredi,             *)
(* Gallai-Witt and the corners theorem.                                      *)
(*                                                                           *)
(* Words: hj_cube k n is [k]^n, the words of length n over {0, ..., k - 1}   *)
(* as functions num->num that are 0 from n on.  An m-variable word z         *)
(* (hj_subspace k m n z) has the letters k + j (j < m) as variables, each    *)
(* used at least once, and hj_subst k z a substitutes a IN hj_cube k m for   *)
(* them, so z describes the m-dimensional subspace                           *)
(* hj_subst k z (hj_cube k m).  Lines are the 1-variable words               *)
(* (hj_line k n l); hj_line_point k l a is the point with letter a and       *)
(* hj_has_line k n A says that some line lies in A.  The density of A is     *)
(* hj_density k n A = fmean (hj_cube k n) (indicator of A).                  *)
(*                                                                           *)
(* Main results:                                                             *)
(* * HALES_JEWETT, HALES_JEWETT_FINITE: for k >= 1 and n large every         *)
(*   finite colouring of [k]^n has a monochromatic line;                     *)
(*   MULTIDIM_HALES_JEWETT, the same for m-dimensional subspaces.            *)
(* * FOLKMAN; GRAHAM_ROTHSCHILD_LINES: every r-colouring of the lines of     *)
(*   [k]^n, n large, is constant on the lines of some m-dimensional          *)
(*   subspace.                                                               *)
(* * DENSITY_HALES_JEWETT (Furstenberg-Katznelson): density_hales_jewett k   *)
(*   for k >= 1, i.e. for delta > 0 and n large, every A with                *)
(*   hj_density k n A >= delta contains a line;                              *)
(*   MULTIDIM_DENSITY_HALES_JEWETT, the same for m-dimensional subspaces.    *)
(* * WEIGHTED_SZEMEREDI: weighted_szemeredi k for k >= 1, i.e. for           *)
(*   delta > 0 there is c > 0 with E_{a,d < N} prod_{j<k} f((a + j d) mod    *)
(*   N) >= c for every large prime N and f : Z_N -> [0, 1] with mean         *)
(*   >= delta.                                                               *)
(* * SZEMEREDI_COUNT (Varnavides): for k >= 2 and N large, every             *)
(*   A SUBSET 1..N with |A| >= delta N contains at least c N^2 k-term        *)
(*   progressions; SZEMEREDI, ROTH, SZEMEREDI_DENSITY (sets of positive      *)
(*   upper density) and VAN_DER_WAERDEN.                                     *)
(* * MULTIDIM_SZEMEREDI (Furstenberg-Katznelson): every dense                *)
(*   A SUBSET [0, M)^d, M large, contains a homothetic copy of any given     *)
(*   finite pattern; GALLAI_WITT, CORNERS (Ajtai-Szemeredi).                 *)
(*                                                                           *)
(* The route is purely combinatorial: Hales-Jewett by colour focusing,       *)
(* density Hales-Jewett by the density increment argument of Dodos,          *)
(* Kanellopoulos and Tyros, "A simple proof of the density Hales-Jewett      *)
(* theorem", IMRN 2014 (DKT below), with Graham-Rothschild for lines as      *)
(* the Ramsey input; Szemeredi's theorem in Z_N from the lines of [k]^n      *)
(* along progressions mod N, and in 1..N from a prime in (2 N, 4 N]          *)
(* (Bertrand's postulate, 100/bertrand.ml).  Besides that file only          *)
(* Library/prime.ml and Library/products.ml are needed.  Names: the          *)
(* combinatorics of words uses the prefix hj_ (Hales-Jewett), the            *)
(* template formulation inside the proof of Hales-Jewett hjt_.               *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/products.ml";;
needs "100/bertrand.ml";;

(* ========================================================================= *)
(* Finite means: fmean s f = sum s f / &(CARD s), with linearity and         *)
(* monotonicity, and the invariance of means over Z_N under translation      *)
(* (SUM_SHIFT_MOD, FMEAN_SHIFT_MOD).                                         *)
(* ========================================================================= *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Finite means.                                                             *)
(* ------------------------------------------------------------------------- *)

let fmean = new_definition
 `fmean (X:A->bool) (g:A->real) = sum X g / &(CARD X)`;;

let FMEAN_ADD = prove
 (`!(X:A->bool) f g. FINITE X
        ==> fmean X (\x. f x + g x) = fmean X f + fmean X g`,
  SIMP_TAC[fmean; SUM_ADD] THEN REAL_ARITH_TAC);;

let FMEAN_SUB = prove
 (`!(X:A->bool) f g. FINITE X
        ==> fmean X (\x. f x - g x) = fmean X f - fmean X g`,
  SIMP_TAC[fmean; SUM_SUB] THEN REAL_ARITH_TAC);;

let FMEAN_LMUL = prove
 (`!(X:A->bool) c f. fmean X (\x. c * f x) = c * fmean X f`,
  REWRITE_TAC[fmean; SUM_LMUL] THEN REAL_ARITH_TAC);;

let FMEAN_CONST = prove
 (`!(X:A->bool) c. FINITE X /\ ~(X = {}) ==> fmean X (\x. c) = c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[fmean; SUM_CONST] THEN
  SUBGOAL_THEN `~(&(CARD(X:A->bool)) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[CARD_EQ_0];
    CONV_TAC REAL_FIELD]);;

let FMEAN_EQ = prove
 (`!(X:A->bool) f g. (!x. x IN X ==> f x = g x) ==> fmean X f = fmean X g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[]);;

let FMEAN_LE = prove
 (`!(X:A->bool) f g. FINITE X /\ (!x. x IN X ==> f x <= g x)
        ==> fmean X f <= fmean X g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; real_div] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[]);;

let FMEAN_ABS_LE = prove
 (`!(X:A->bool) f. FINITE X ==> abs(fmean X f) <= fmean X (\x. abs(f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; REAL_ABS_DIV; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC SUM_ABS THEN ASM_REWRITE_TAC[]);;

let FMEAN_SUM = prove
 (`!(X:A->bool) (Ix:B->bool) f. FINITE X /\ FINITE Ix
        ==> fmean X (\x. sum Ix (\i. f i x)) = sum Ix (\i. fmean X (f i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; real_div; GSYM SUM_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX]);;

let FMEAN_POS = prove
 (`!(X:A->bool) f. FINITE X /\ (!x. x IN X ==> &0 <= f x) ==> &0 <= fmean X f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[SUM_POS_LE; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* Means over Z_N are invariant under translation.                           *)
(* ------------------------------------------------------------------------- *)

let SUM_SHIFT_MOD = prove
 (`!(f:num->real) n t.
     ~(n = 0)
     ==> sum {m | m < n} (\m. f((m + t) MOD n)) = sum {m | m < n} f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\m. (m + t) MOD n` THEN
  EXISTS_TAC `\m. (m + (n - 1) * t) MOD n` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; MOD_LT_EQ] THEN
  SUBGOAL_THEN `(n - 1) + 1 = n` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`n - 1`,`e:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
   [GSYM(MATCH_MP MOD_LT th)]) THEN
  REWRITE_TAC[GSYM CONG] THEN UNDISCH_TAC `e + 1 = n` THEN
  CONV_TAC NUMBER_RULE);;

let FMEAN_SHIFT_MOD = prove
 (`!N c (g:num->real).
        fmean {r | r < N} (\r. g((c + r) MOD N)) = fmean {r | r < N} g`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `N = 0` THEN
  ASM_REWRITE_TAC[LT; EMPTY_GSPEC; fmean; SUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_SIMP_TAC[SUM_SHIFT_MOD]);;

(* ========================================================================= *)
(* Words, variable words, lines and densities.                               *)
(*                                                                           *)
(* * hj_cube k n: the words of length n over {0, ..., k - 1}, as functions   *)
(*   num->num that are 0 from n on.  hj_concat l x y puts y after the first  *)
(*   l letters of x; hj_take and hj_drop split a word (HJ_CONCAT_SPLIT,      *)
(*   SUM_HJ_CONCAT).                                                         *)
(* * hj_subspace k m n z: z is an m-variable word of length n over [k]:      *)
(*   z IN hj_cube (k + m) n, letters < k, variable j encoded as k + j, and   *)
(*   every variable occurs.  hj_subst k z a substitutes the word a for the   *)
(*   variables: the point z(a) for a IN hj_cube k m, and the composition     *)
(*   of subspaces for a variable word a (HJ_SUBST_SUBST, without side        *)
(*   conditions).                                                            *)
(* * hj_line k n l <=> hj_subspace k 1 n l, so a line of [k]^n is literally  *)
(*   a point of [k + 1]^n; hj_line_point k l a is its point with letter a,   *)
(*   and hj_has_line k n A says that some line has all its k points in A.    *)
(*   HJ_HAS_LINE_PULLBACK: a line of the pullback {a | hj_subst k z a IN A}  *)
(*   gives a line of A.  hj_join and hj_lift concatenate and lift variable   *)
(*   words.                                                                  *)
(* * hj_density k n A = fmean (hj_cube k n) (indicator of A).                *)
(*   HJ_DENSITY_SECTIONS: hj_density k (l + m) A is the mean over x of the   *)
(*   densities of the sections {y | hj_concat l x y IN A}.  FMEAN_MARKOV,    *)
(*   HJ_DENSITY_MARKOV, CARD_PIGEONHOLE.                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Words: functions num->num that are 0 outside their length.                *)
(* ------------------------------------------------------------------------- *)

let hj_cube = new_definition
 `hj_cube k n = {x:num->num | (!i. i < n ==> x i < k) /\
                            (!i. n <= i ==> x i = 0)}`;;

let IN_HJ_CUBE = prove
 (`!k n x. x IN hj_cube k n <=>
           (!i. i < n ==> x i < k) /\ (!i. n <= i ==> x i = 0)`,
  REWRITE_TAC[hj_cube; IN_ELIM_THM]);;

let HAS_SIZE_HJ_CUBE = prove
 (`!k n. hj_cube k n HAS_SIZE k EXP n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`0`; `k:num`; `{a:num | a < k}`; `n:num`;
                 `{i:num | i < n}`] HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_HJ_CUBE; IN_ELIM_THM; NOT_LT]);;

let FINITE_HJ_CUBE = prove
 (`!k n. FINITE(hj_cube k n)`,
  MESON_TAC[HAS_SIZE_HJ_CUBE; HAS_SIZE]);;

let CARD_HJ_CUBE = prove
 (`!k n. CARD(hj_cube k n) = k EXP n`,
  MESON_TAC[HAS_SIZE_HJ_CUBE; HAS_SIZE]);;

let HJ_CUBE_NONEMPTY = prove
 (`!k n. 1 <= k ==> ~(hj_cube k n = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `\i:num. 0` THEN REWRITE_TAC[IN_HJ_CUBE] THEN ASM_ARITH_TAC);;

let HJ_CUBE_MONO = prove
 (`!k k' n. k <= k' ==> hj_cube k n SUBSET hj_cube k' n`,
  REWRITE_TAC[SUBSET; IN_HJ_CUBE] THEN MESON_TAC[LTE_TRANS]);;

let HJ_CUBE_0 = prove
 (`!k. hj_cube k 0 = {(\i. 0)}`,
  REWRITE_TAC[EXTENSION; IN_HJ_CUBE; IN_SING; LT; LE_0] THEN
  REWRITE_TAC[FUN_EQ_THM]);;

let hj_concat = new_definition
 `hj_concat l (x:num->num) (y:num->num) =
  \i. if i < l then x i else y (i - l)`;;

let hj_take = new_definition
 `hj_take l (w:num->num) = \i. if i < l then w i else 0`;;

let hj_drop = new_definition
 `hj_drop l (w:num->num) = \i. w (i + l)`;;

let HJ_CONCAT_CUBE = prove
 (`!k l m x y. x IN hj_cube k l /\ y IN hj_cube k m
               ==> hj_concat l x y IN hj_cube k (l + m)`,
  REWRITE_TAC[IN_HJ_CUBE; hj_concat] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let HJ_TAKE_CUBE = prove
 (`!k l m w. w IN hj_cube k (l + m) ==> hj_take l w IN hj_cube k l`,
  REWRITE_TAC[IN_HJ_CUBE; hj_take] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM NOT_LE]]);;

let HJ_DROP_CUBE = prove
 (`!k l m w. w IN hj_cube k (l + m) ==> hj_drop l w IN hj_cube k m`,
  REWRITE_TAC[IN_HJ_CUBE; hj_drop] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let HJ_CONCAT_SPLIT = prove
 (`!l w. hj_concat l (hj_take l w) (hj_drop l w) = w`,
  REWRITE_TAC[hj_concat; hj_take; hj_drop; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let HJ_TAKE_CONCAT = prove
 (`!k l x y. x IN hj_cube k l ==> hj_take l (hj_concat l x y) = x`,
  REWRITE_TAC[IN_HJ_CUBE; hj_concat; hj_take; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let HJ_DROP_CONCAT = prove
 (`!l x y. hj_drop l (hj_concat l x y) = y`,
  REWRITE_TAC[hj_concat; hj_drop; FUN_EQ_THM; ARITH_RULE `~(i + l < l:num)`;
              ADD_SUB]);;

let HJ_CONCAT_INJ = prove
 (`!k l x y x' y'. x IN hj_cube k l /\ x' IN hj_cube k l /\
                   hj_concat l x y = hj_concat l x' y'
                   ==> x = x' /\ y = y'`,
  MESON_TAC[HJ_TAKE_CONCAT; HJ_DROP_CONCAT]);;

let HJ_CUBE_CONCAT_IMAGE = prove
 (`!k l m. hj_cube k (l + m) =
           IMAGE (\(x,y). hj_concat l x y) (hj_cube k l CROSS hj_cube k m)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  X_GEN_TAC `w:num->num` THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
      [`hj_take l (w:num->num)`; `hj_drop l (w:num->num)`] THEN
    REWRITE_TAC[HJ_CONCAT_SPLIT] THEN
    ASM_MESON_TAC[HJ_TAKE_CUBE; HJ_DROP_CUBE];
    MESON_TAC[HJ_CONCAT_CUBE]]);;

let SUM_HJ_CONCAT = prove
 (`!k l m f. sum (hj_cube k (l + m)) f =
             sum (hj_cube k l)
               (\x. sum (hj_cube k m) (\y. f (hj_concat l x y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_CUBE_CONCAT_IMAGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    MESON_TAC[HJ_CONCAT_INJ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_HJ_CUBE] THEN
  REWRITE_TAC[CROSS] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Variable words and substitution.                                          *)
(* ------------------------------------------------------------------------- *)

let hj_subspace = new_definition
 `hj_subspace k m n (z:num->num) <=>
    z IN hj_cube (k + m) n /\ !j. j < m ==> ?i. i < n /\ z i = k + j`;;

let hj_subst = new_definition
 `hj_subst k (z:num->num) (a:num->num) =
    \i. if z i < k then z i else a (z i - k)`;;

let HJ_SUBSPACE_0 = prove
 (`!k n z. hj_subspace k 0 n z <=> z IN hj_cube k n`,
  REWRITE_TAC[hj_subspace; ADD_CLAUSES; LT]);;

let HJ_SUBSPACE_CUBE = prove
 (`!k m n z. hj_subspace k m n z ==> z IN hj_cube (k + m) n`,
  SIMP_TAC[hj_subspace]);;

let HJ_SUBST_SUBST = prove
 (`!k z w a. hj_subst k (hj_subst k z w) a = hj_subst k z (hj_subst k w a)`,
  REWRITE_TAC[hj_subst; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(z:num->num) x < k` THEN ASM_REWRITE_TAC[]);;

let HJ_SUBSPACE_SUBST = prove
 (`!k m m' n z w. 1 <= k /\ hj_subspace k m n z /\ hj_subspace k m' m w
                  ==> hj_subspace k m' n (hj_subst k z w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_subst] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `~(z < k) /\ z < k + m ==> z - k < m:num`) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?i. i < n /\ (z:num->num) i = k + p`
     (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(k + p < k:num)`; ADD_SUB2]]);;

let HJ_SUBST_CUBE = prove
 (`!k m n z a. 1 <= k /\ hj_subspace k m n z /\ a IN hj_cube k m
               ==> hj_subst k z a IN hj_cube k n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM HJ_SUBSPACE_0] THEN
  MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[HJ_SUBSPACE_0]);;

let HJ_SUBST_INJ = prove
 (`!k k' m n z a b.
        hj_subspace k m n z /\ a IN hj_cube k' m /\ b IN hj_cube k' m /\
        hj_subst k z a = hj_subst k z b
        ==> a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j:num < m` THENL
   [SUBGOAL_THEN `?i. i < n /\ (z:num->num) i = k + j`
     (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `hj_subst k z a = hj_subst k z b` THEN
    REWRITE_TAC[hj_subst; FUN_EQ_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(k + j < k:num)`; ADD_SUB2];
    ASM_MESON_TAC[NOT_LT]]);;

let HJ_SUBST_WORD = prove
 (`!k n y a. 1 <= k /\ y IN hj_cube k n ==> hj_subst k y a = y`,
  REWRITE_TAC[IN_HJ_CUBE; hj_subst; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:num < n` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[NOT_LT; ARITH_RULE `1 <= k ==> 0 < k`]);;

let hj_identity = new_definition
 `hj_identity k m = \i. if i < m then k + i else 0`;;

let HJ_SUBSPACE_IDENTITY = prove
 (`!k m. 1 <= k ==> hj_subspace k m m (hj_identity k m)`,
  REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_identity] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[LT_ADD_LCANCEL];
    ASM_REWRITE_TAC[GSYM NOT_LE];
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]]);;

let HJ_SUBST_IDENTITY = prove
 (`!k k' m a. 1 <= k /\ a IN hj_cube k' m
              ==> hj_subst k (hj_identity k m) a = a`,
  REWRITE_TAC[IN_HJ_CUBE; hj_subst; hj_identity; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:num < m` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(k + x < k:num)`; ADD_SUB2] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`] THEN
  ASM_MESON_TAC[NOT_LT]);;

let HJ_SUBST_RID = prove
 (`!k m n z. hj_subspace k m n z ==> hj_subst k z (hj_identity k m) = z`,
  REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_subst; hj_identity; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:num < n` THENL
   [SUBGOAL_THEN `(z:num->num) x - k < m` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC(ARITH_RULE `~(z < k) /\ z < k + m ==> z - k < m:num`) THEN
      ASM_SIMP_TAC[];
      ASM_ARITH_TAC];
    ASM_MESON_TAC[NOT_LT; ARITH_RULE `~(0 < k) ==> k = 0`;
                  ARITH_RULE `~(z < k) ==> k + z - k = z:num`]]);;

(* ------------------------------------------------------------------------- *)
(* Combinatorial lines; concatenating and lifting variable words.            *)
(* ------------------------------------------------------------------------- *)

let hj_line = new_definition
 `hj_line k n (l:num->num) <=> hj_subspace k 1 n l`;;

let hj_line_point = new_definition
 `hj_line_point k (l:num->num) a = hj_subst k l (\i. if i = 0 then a else 0)`;;

let hj_has_line = new_definition
 `hj_has_line k n (A:(num->num)->bool) <=>
    ?l. hj_line k n l /\ !a. a < k ==> hj_line_point k l a IN A`;;

let HJ_LETTER_IN_CUBE = prove
 (`!k a. a < k ==> (\i. if i = 0 then a else 0) IN hj_cube k 1`,
  REWRITE_TAC[IN_HJ_CUBE] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
    ASM_MESON_TAC[ARITH_RULE `i < 1 <=> i = 0`];
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`]]);;

let HJ_LINE_CUBE = prove
 (`!k n l. hj_line k n l ==> l IN hj_cube (k + 1) n`,
  SIMP_TAC[hj_line; hj_subspace]);;

let HJ_LINE_VAR = prove
 (`!k n l. hj_line k n l ==> ?i. i < n /\ l i = k`,
  REWRITE_TAC[hj_line; hj_subspace] THEN
  MESON_TAC[ARITH_RULE `0 < 1 /\ k + 0 = k`]);;

let HJ_LINE_POINT_CUBE = prove
 (`!k n l a. 1 <= k /\ hj_line k n l /\ a < k
             ==> hj_line_point k l a IN hj_cube k n`,
  REWRITE_TAC[hj_line; hj_line_point] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `1` THEN
  ASM_SIMP_TAC[HJ_LETTER_IN_CUBE]);;

let HJ_LINE_SUBST = prove
 (`!k m n z u. 1 <= k /\ hj_subspace k m n z /\ hj_line k m u
               ==> hj_line k n (hj_subst k z u)`,
  REWRITE_TAC[hj_line] THEN MESON_TAC[HJ_SUBSPACE_SUBST]);;

let HJ_LINE_POINT_SUBST = prove
 (`!k z u a. hj_line_point k (hj_subst k z u) a =
             hj_subst k z (hj_line_point k u a)`,
  REWRITE_TAC[hj_line_point; HJ_SUBST_SUBST]);;

let HJ_HAS_LINE_PULLBACK = prove
 (`!k m n z A. 1 <= k /\ hj_subspace k m n z /\
               hj_has_line k m {a | hj_subst k z a IN A}
               ==> hj_has_line k n A`,
  REWRITE_TAC[hj_has_line; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `hj_subst k z (l:num->num)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HJ_LINE_SUBST]; ASM_SIMP_TAC[HJ_LINE_POINT_SUBST]]);;

let hj_join = new_definition
 `hj_join k l m1 (z1:num->num) (z2:num->num) =
    \i. if i < l then z1 i
        else if z2 (i - l) < k then z2 (i - l) else z2 (i - l) + m1`;;

let HJ_SUBST_JOIN = prove
 (`!k l m1 z1 z2 a.
        hj_subst k (hj_join k l m1 z1 z2) a =
        hj_concat l (hj_subst k z1 a) (hj_subst k z2 (hj_drop m1 a))`,
  REWRITE_TAC[hj_subst; hj_join; hj_concat; hj_drop; FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:num < l` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(z2:num->num) (x - l) < k` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(z < k) ==> ~(z + m < k:num)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HJ_SUBSPACE_JOIN = prove
 (`!k l m1 m2 n2 z1 z2.
        1 <= k /\ hj_subspace k m1 l z1 /\ hj_subspace k m2 n2 z2
        ==> hj_subspace k (m1 + m2) (l + n2) (hj_join k l m1 z1 z2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_join] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num < l` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(ARITH_RULE `x < k + m1 ==> x < k + m1 + m2:num`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z2:num->num)(i - l) < k + m2` MP_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `~(i < l) /\ i < l + n2 ==> i - l < n2:num`];
      ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i:num < l) /\ (z2:num->num)(i - l) = 0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`]];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j:num < m1` THENL
     [SUBGOAL_THEN `?i. i < l /\ (z1:num->num) i = k + j`
       (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `?i. i < n2 /\ (z2:num->num) i = k + (j - m1)`
       (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `l + i:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(l + i < l:num)`; ADD_SUB2;
                      ARITH_RULE `~(k + j < k:num)`] THEN
      ASM_ARITH_TAC]]);;

let hj_lift = new_definition
 `hj_lift k (z:num->num) = \i. if z i < k then z i else z i + 1`;;

let HJ_SUBST_LIFT = prove
 (`!k z a. hj_subst (k + 1) (hj_lift k z) a = hj_subst k z a`,
  REWRITE_TAC[hj_subst; hj_lift; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(z:num->num) x < k` THEN
  ASM_SIMP_TAC[ARITH_RULE `z < k ==> z < k + 1`;
               ARITH_RULE `~(z < k) ==> ~(z + 1 < k + 1)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HJ_SUBSPACE_LIFT = prove
 (`!k m n z. 1 <= k /\ hj_subspace k m n z
             ==> hj_subspace (k + 1) m n (hj_lift k z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_lift] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:num->num) i < k + m` MP_TAC THENL
     [ASM_SIMP_TAC[]; ARITH_TAC];
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?i. i < n /\ (z:num->num) i = k + j`
     (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Densities of sets of words; sections, Markov and pigeonhole.              *)
(* ------------------------------------------------------------------------- *)

let hj_density = new_definition
 `hj_density k n (A:(num->num)->bool) =
    fmean (hj_cube k n) (\x. if x IN A then &1 else &0)`;;

let FMEAN_HJ_CONCAT = prove
 (`!k l m f. fmean (hj_cube k (l + m)) f =
             fmean (hj_cube k l)
               (\x. fmean (hj_cube k m) (\y. f (hj_concat l x y)))`,
  REWRITE_TAC[fmean; CARD_HJ_CUBE; SUM_HJ_CONCAT; EXP_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_div; SUM_RMUL; REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let HJ_DENSITY_SECTIONS = prove
 (`!k l m A. hj_density k (l + m) A =
             fmean (hj_cube k l)
               (\x. hj_density k m {y | hj_concat l x y IN A})`,
  REWRITE_TAC[hj_density; FMEAN_HJ_CONCAT; IN_ELIM_THM]);;

let HJ_DENSITY_CARD = prove
 (`!k n A. hj_density k n A =
           &(CARD {x | x IN hj_cube k n /\ x IN A}) / &(k EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_density; fmean; CARD_HJ_CUBE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `FINITE {x | x IN hj_cube k n /\ x IN A}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `hj_cube k n` THEN
    REWRITE_TAC[FINITE_HJ_CUBE] THEN SET_TAC[];
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]]);;

let HJ_DENSITY_POS = prove
 (`!k n A. &0 <= hj_density k n A`,
  REWRITE_TAC[HJ_DENSITY_CARD] THEN SIMP_TAC[REAL_LE_DIV; REAL_POS]);;

let HJ_DENSITY_LE_1 = prove
 (`!k n A. hj_density k n A <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_DENSITY_CARD] THEN
  ASM_CASES_TAC `k EXP n = 0` THEN
  ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_POS] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; GSYM CARD_HJ_CUBE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_HJ_CUBE] THEN SET_TAC[]);;

let HJ_DENSITY_MONO = prove
 (`!k n A B. (!x. x IN hj_cube k n /\ x IN A ==> x IN B)
             ==> hj_density k n A <= hj_density k n B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_density] THEN MATCH_MP_TAC FMEAN_LE THEN
  REWRITE_TAC[FINITE_HJ_CUBE] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[REAL_LE_REFL; REAL_POS]);;

let HJ_DENSITY_EQ = prove
 (`!k n A B. (!x. x IN hj_cube k n ==> (x IN A <=> x IN B))
             ==> hj_density k n A = hj_density k n B`,
  MESON_TAC[HJ_DENSITY_MONO; REAL_LE_ANTISYM]);;

let FMEAN_MARKOV = prove
 (`!(X:A->bool) f a b.
        FINITE X /\ (!x. x IN X ==> f x <= &1) /\ &0 <= b /\
        a <= fmean X f
        ==> (a - b) * &(CARD X) <= &(CARD {x | x IN X /\ b <= f x})`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `X:A->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; REAL_MUL_RZERO; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(CARD(X:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * &(CARD(X:A->bool)) <= sum X f` ASSUME_TAC THENL
   [UNDISCH_TAC `a <= fmean (X:A->bool) f` THEN
    ASM_SIMP_TAC[fmean; REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (X:A->bool) f <=
    &(CARD {x | x IN X /\ b <= f x}) + b * &(CARD X)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (X:A->bool) (\x. if b <= f x then &1 else b)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CASES] THEN
    SUBGOAL_THEN `FINITE {x:A | x IN X /\ b <= f x} /\
                  FINITE {x:A | x IN X /\ ~(b <= f x)}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `X:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `c2 * b <= cx * b ==> x + c2 * b <= x + b * cx:real`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c s y. a * c <= s /\ s <= y + b * c ==> (a - b) * c <= y:real`) THEN
  EXISTS_TAC `sum (X:A->bool) f` THEN ASM_REWRITE_TAC[]);;

let HJ_DENSITY_MARKOV = prove
 (`!k l f a b.
        1 <= k /\ (!x. x IN hj_cube k l ==> f x <= &1) /\ &0 <= b /\
        a <= fmean (hj_cube k l) f
        ==> a - b <= hj_density k l {x | b <= f x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HJ_DENSITY_CARD; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&0 < &(k EXP l)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REWRITE_TAC[GSYM CARD_HJ_CUBE] THEN
  MATCH_MP_TAC FMEAN_MARKOV THEN ASM_REWRITE_TAC[FINITE_HJ_CUBE]);;

let CARD_PIGEONHOLE = prove
 (`!(g:A->B) X S.
        FINITE X /\ FINITE S /\ ~(S = {}) /\ (!x. x IN X ==> g x IN S)
        ==> ?s. s IN S /\
                &(CARD X) <= &(CARD S) * &(CARD {x | x IN X /\ g x = s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (S:B->bool) (\s. &(CARD {x:A | x IN X /\ g x = s})) =
    &(CARD(X:A->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->B`; `(\x. &1):A->real`; `X:A->bool`; `S:B->bool`]
      SUM_GROUP) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    SUBGOAL_THEN `!s:B. FINITE {x:A | x IN X /\ g x = s}` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `X:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(!s:B. s IN S
           ==> &(CARD(S:B->bool)) * &(CARD {x:A | x IN X /\ g x = s}) <
               &(CARD(X:A->bool)))`
  MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\s:B. &(CARD(S:B->bool)) * &(CARD {x:A | x IN X /\ g x = s})`;
      `\s:B. &(CARD(X:A->bool))`; `S:B->bool`] SUM_LT_ALL) THEN
    ASM_SIMP_TAC[SUM_LMUL; SUM_CONST] THEN REAL_ARITH_TAC;
    MESON_TAC[REAL_NOT_LT]]);;

let FMEAN_EXISTS_GE = prove
 (`!(X:A->bool) f c. FINITE X /\ ~(X = {}) /\ c <= fmean X f
                     ==> ?x. x IN X /\ c <= f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(CARD(X:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  UNDISCH_TAC `c <= fmean (X:A->bool) f` THEN
  ASM_SIMP_TAC[fmean; REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LE; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `\x:A. (c:real)`; `X:A->bool`] SUM_LT_ALL) THEN
  ASM_SIMP_TAC[SUM_CONST] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Hales-Jewett theorem and multidimensional Hales-Jewett.               *)
(*                                                                           *)
(* * HALES_JEWETT_TEMPLATE: for t, r >= 1 there is N with                    *)
(*   hales_jewett_template t r N: every r-colouring chi of [t]^N has a       *)
(*   monochromatic combinatorial line.  Templates use the wildcard letter    *)
(*   t and hjt_subst substitutes a letter.  The step from t to t + 1 is by   *)
(*   colour focusing: HJT_KEY finds, by induction on s, either a             *)
(*   monochromatic line or s lines that are monochromatic on their first t   *)
(*   points with distinct colours and a common focus (hjt_focused);          *)
(*   HJT_STEP takes s = r and HJT_COLLAPSE turns the focused family into a   *)
(*   monochromatic line.  The block structure uses products of templates     *)
(*   (hjt_prod) and recolourings by patterns (NSUM_DIGITS_BOUND,             *)
(*   NSUM_DIGITS_UNIQUE).  This part is adapted from an existing HOL Light   *)
(*   proof of the theorem.                                                   *)
(* * HALES_JEWETT, HALES_JEWETT_FINITE: the same for the lines of            *)
(*   hj_cube k n (HJ_LINE_POINT_TEMPLATE relates hjt_subst and               *)
(*   hj_line_point) and for colourings with values in a finite set.          *)
(* * MULTIDIM_HALES_JEWETT: every finite colouring of hj_cube k n, n large,  *)
(*   is constant on hj_subst k z (hj_cube k m) for some m-variable word z.   *)
(*   By blocks: the last block is coloured by the pattern of colours of the  *)
(*   earlier ones (HJ_PATTERN_INDEX).                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Templates, combinatorial lines and monochromatic lines.                   *)
(* ------------------------------------------------------------------------- *)

let hjt_subst = new_definition
 `hjt_subst t N (tw:num->num) a =
    \i. if i < N then (if tw i = t then a else tw i) else 0`;;

let hjt_line = new_definition
 `hjt_line t N (tw:num->num) <=>
    (!i. i < N ==> tw i <= t) /\ (?i. i < N /\ tw i = t)`;;

let hjt_mono = new_definition
 `hjt_mono t N (chi:(num->num)->num) tw <=>
    !a a'. a < t /\ a' < t
           ==> chi(hjt_subst t N tw a) = chi(hjt_subst t N tw a')`;;

let hales_jewett_template = new_definition
 `hales_jewett_template t r N <=>
    !chi:(num->num)->num. (!x. chi x < r)
        ==> ?tw. hjt_line t N tw /\ hjt_mono t N chi tw`;;

let HJT_1 = prove
 (`!r. 1 <= r ==> hales_jewett_template 1 r 1`,
  REWRITE_TAC[hales_jewett_template] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i:num. if i = 0 then 1 else 0` THEN
  REWRITE_TAC[hjt_line; hjt_mono] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ARITH_TAC;
      EXISTS_TAC `0` THEN REWRITE_TAC[ARITH]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `a = 0 /\ a' = 0` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC]);;

let HJT_MONO_N = prove
 (`!t r N N'. 1 <= t /\ hales_jewett_template t r N /\ N <= N'
              ==> hales_jewett_template t r N'`,
  REWRITE_TAC[hales_jewett_template] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chi:(num->num)->num`) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tw:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i:num. if i < N then tw i else 0` THEN
  SUBGOAL_THEN
   `!a. hjt_subst t N' (\i. if i < N then tw i else 0) a = hjt_subst t N tw a`
   ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[hjt_subst; FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `hjt_line t N tw` THEN REWRITE_TAC[hjt_line] THEN
    STRIP_TAC THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i:num < N'` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    REWRITE_TAC[hjt_mono] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hjt_mono t N chi tw` THEN REWRITE_TAC[hjt_mono] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let hjt_prod = new_definition
 `hjt_prod D (sg:num->num) (rho:num->num) =
    \i. if i < D then sg i else rho (i - D)`;;

let HJT_SUBST_PROD = prove
 (`!u D M sg rho a.
      hjt_subst u (D + M) (hjt_prod D sg rho) a =
      hjt_prod D (hjt_subst u D sg a) (hjt_subst u M rho a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hjt_subst; hjt_prod; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let hjt_almost_mono = new_definition
 `hjt_almost_mono (chi:(num->num)->num) t N (L:num->num) (c:num) <=>
    hjt_line (t+1) N L /\ (!a. a < t ==> chi(hjt_subst (t+1) N L a) = c)`;;

let hjt_focused = new_definition
 `hjt_focused (chi:(num->num)->num) t N (Lf:num->num->num) (cf:num->num)
             (focus:num->num) s <=>
    (!i. i < s ==> hjt_almost_mono chi t N (Lf i) (cf i)) /\
    (!i j. i < s /\ j < s /\ cf i = cf j ==> i = j) /\
    (!i:num. i < s ==> hjt_subst (t+1) N (Lf i) t = focus)`;;

let HJT_ALMOST_MONO_LT = prove
 (`!chi t r N (Lf:num->num->num) cf i.
     1 <= t /\ (!x. chi x < r) /\ hjt_almost_mono chi t N (Lf i) (cf i)
     ==> cf i < r`,
  REWRITE_TAC[hjt_almost_mono] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let HJT_COLLAPSE = prove
 (`!chi t r N Lf cf focus.
      1 <= t /\ (!x. chi x < r) /\ hjt_focused chi t N Lf cf focus r
      ==> ?tw. hjt_line (t+1) N tw /\ hjt_mono (t+1) N chi tw`,
  REWRITE_TAC[hjt_focused] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= r` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `focus:num->num`) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. i < r ==> cf i < r` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`chi:(num->num)->num`;`t:num`;`r:num`;`N:num`;
                   `Lf:num->num->num`;`cf:num->num`;`i:num`]
                     HJT_ALMOST_MONO_LT) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?i:num. i < r /\
    cf i = (chi:(num->num)->num) focus` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cf:num->num`;
     `0..r-1`] (INST_TYPE [`:num`,`:B`] CARD_IMAGE_INJ)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (cf:num->num) (0..r-1) = 0..r-1` ASSUME_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG] THEN X_GEN_TAC `y:num` THEN
        DISCH_THEN(X_CHOOSE_THEN `x':num` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(cf:num->num) x' < r` MP_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `x':num`) THEN
           ASM_ARITH_TAC; ASM_ARITH_TAC];
        ASM_REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(chi:(num->num)->num) focus IN IMAGE cf
      (0..r-1)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_NUMSEG] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `focus:num->num`) THEN ARITH_TAC;
      REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(Lf:num->num->num) i` THEN
  SUBGOAL_THEN `hjt_almost_mono chi t N ((Lf:num->num->num) i) (cf i)`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[hjt_almost_mono] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[hjt_mono] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `a':num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b. b < t + 1 ==>
    chi(hjt_subst (t+1) N ((Lf:num->num->num) i) b) = (cf:num->num) i`
   (fun th -> ASM_MESON_TAC[th]) THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `b:num = t` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hjt_subst (t+1) N ((Lf:num->num->num) i) t = focus`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let hjt_lift = new_definition
 `hjt_lift t M (l:num->num) = \i. if i < M /\ l i = t then t + 1 else l i`;;

let NSUM_NUMSEG_LT_SHIFT = prove
 (`!f n. nsum {i | i < n} f = nsum(1..n) (\i. f(i - 1))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; NSUM_CLAUSES_NUMSEG; ARITH_EQ;
                  ARITH_RULE `1 <= SUC n`; SUC_SUB1]);;

let HJT_NSUM_DIGIT_SPLIT = prove
 (`!b (x:num->num) Ns i0. i0 < Ns ==>
    nsum {i:num | i < Ns} (\i. b EXP i * x i) =
    b EXP i0 * x i0 +
    (nsum {i:num | i < i0} (\i. b EXP i * x i) +
     nsum {i:num | i0 < i /\ i < Ns} (\i. b EXP i * x i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{i:num | i < Ns} = {i0} UNION ({i:num | i < i0} UNION {i:num | i0 <
     i /\ i < Ns})`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {i:num | i < i0} /\ FINITE {i:num | i0 < i /\ i < Ns}`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i:num | i < Ns}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum ({i0} UNION {i:num | i < i0} UNION {i:num | i0 < i /\ i < Ns})
         (\i. b EXP i * (x:num->num) i) =
    nsum {i0} (\i. b EXP i * x i) +
    nsum ({i:num | i < i0} UNION {i:num | i0 < i /\
      i < Ns}) (\i. b EXP i * x i)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_UNION_NONZERO THEN
    ASM_REWRITE_TAC[FINITE_SING; FINITE_UNION] THEN
    REWRITE_TAC[IN_INTER; IN_SING; IN_UNION; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NSUM_SING] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_UNION_NONZERO THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTER; IN_UNION; IN_ELIM_THM] THEN ARITH_TAC);;

let HJT_DIGIT_RECOVER = prove
 (`!b Ns x i0.
    2 <= b /\ (!i. i < Ns ==> x i < b) /\ i0 < Ns
    ==> (nsum {i:num | i < Ns} (\i. b EXP i * x i) DIV (b EXP i0))
      MOD b = x i0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HJT_NSUM_DIGIT_SPLIT] THEN
  SUBGOAL_THEN `nsum {i:num | i < i0} (\i. b EXP i * (x:num->num)
    i) < b EXP i0`
   ASSUME_TAC THENL
   [REWRITE_TAC[NSUM_NUMSEG_LT_SHIFT] THEN MATCH_MP_TAC NSUM_DIGITS_BOUND THEN
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?H. nsum {i:num | i0 < i /\ i < Ns} (\i. b EXP i * (x:num->num) i) =
        (b EXP i0 * b) * H` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM divides] THEN MATCH_MP_TAC DIVIDES_NSUM THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < Ns}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN
      SUBGOAL_THEN `b EXP i0 * b = b EXP (i0 + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXP_ADD; EXP_1]; ALL_TAC] THEN
      REWRITE_TAC[divides] THEN EXISTS_TAC `b EXP (i - (i0 + 1))` THEN
      REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `b EXP i0 * x i0 +
    nsum {i:num | i < i0} (\i. b EXP i * (x:num->num) i) + (b EXP i0 * b) * H =
    b EXP i0 * (x i0 + b * H) + nsum {i:num | i < i0} (\i. b EXP i * x i)`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(b EXP i0 = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; DIV_LT; ADD_CLAUSES] THEN
  SUBGOAL_THEN `(x:num->num) i0 < b` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let HJT_RECOLOUR = prove
 (`!chi t Ns M r.
    1 <= t /\ (!x. chi x < r)
    ==> ?psi.
          (!y. psi y < r EXP ((t+2) EXP Ns)) /\
          (!l'. hjt_mono t M psi l'
           ==> !x a a'.
                 (!i. i < Ns ==> x i <= t + 1) /\ (!i. Ns <= i ==> x i = 0) /\
                 a < t /\ a' < t
                 ==> chi(hjt_prod Ns x (hjt_subst t M l' a)) =
                     chi(hjt_prod Ns x (hjt_subst t M l' a')))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `\y. nsum {j:num | j < (t+2) EXP Ns}
             (\j. r EXP j *
                  (chi:(num->num)->num)
                    (hjt_prod Ns
                       (\i. if i < Ns then (j DIV ((t+2) EXP i))
                         MOD (t+2) else 0)
                       y))` THEN
  BETA_TAC THEN
  SUBGOAL_THEN `1 <= r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(\i:num. 0):num->num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[NSUM_NUMSEG_LT_SHIFT] THEN
    MATCH_MP_TAC NSUM_DIGITS_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l':num->num` THEN
  REWRITE_TAC[hjt_mono] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:num->num`; `a:num`; `a':num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `a':num`]) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`r:num`; `(t+2) EXP Ns`;
    `\j. (chi:(num->num)->num)
           (hjt_prod Ns
              (\i. if i < Ns then ((j - 1) DIV ((t+2) EXP i)) MOD (t+2)
                   else 0)
              (hjt_subst t M l' a))`;
    `\j. (chi:(num->num)->num)
           (hjt_prod Ns
              (\i. if i < Ns then ((j - 1) DIV ((t+2) EXP i)) MOD (t+2)
                   else 0)
              (hjt_subst t M l' a'))`]
   NSUM_DIGITS_UNIQUE) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NSUM_NUMSEG_LT_SHIFT]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\i. if i < Ns
         then (nsum {k | k < Ns} (\k. (t+2) EXP k * (x:num->num) k) DIV
               ((t+2) EXP i)) MOD (t+2)
         else 0) = x` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC HJT_DIGIT_RECOVER THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ARITH_TAC;
        X_GEN_TAC `i2:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:num->num) i2 <= t + 1` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC]];
      SUBGOAL_THEN `(x:num->num) i = 0` (fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum {k | k < Ns} (\k. (t+2) EXP k * (x:num->num) k) < (t+2) EXP Ns`
   ASSUME_TAC THENL
   [REWRITE_TAC[NSUM_NUMSEG_LT_SHIFT] THEN MATCH_MP_TAC NSUM_DIGITS_BOUND THEN
    REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `i2:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:num->num) (i2 - 1) <= t + 1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if (is_forall(concl th)) &&
       (let bd = snd(strip_forall(concl th)) in is_imp bd)
    then MP_TAC(SPEC
      `nsum {k | k < Ns} (\k. (t+2) EXP k * (x:num->num) k) + 1` th)
    else NO_TAC) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG;
                ARITH_RULE `1 <= c + 1 /\ c + 1 <= n <=> c < n`] THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_abs(lhs(concl th)) then
      RULE_ASSUM_TAC(REWRITE_RULE[th])
    else NO_TAC) THEN
  FIRST_X_ASSUM ACCEPT_TAC);;

let HJT_LIFT_SUBST_LE = prove
 (`!t M l a. hjt_line t M l /\ a <= t
      ==> hjt_subst (t+1) M (hjt_lift t M l) a = hjt_subst t M l a`,
  REWRITE_TAC[hjt_line] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[hjt_subst; hjt_lift; FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k:num < M` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `k:num` th)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `(l:num->num) k = t` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC);;

let HJT_PROD_LIFT_SUBST_LE = prove
 (`!t M l Ns p a.
     hjt_line t M l /\ a <= t
     ==> hjt_subst (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l)) a =
         hjt_prod Ns (hjt_subst (t+1) Ns p a) (hjt_subst t M l a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HJT_SUBST_PROD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC HJT_LIFT_SUBST_LE THEN ASM_REWRITE_TAC[]);;

let HJT_SUBST_FIXED = prove
 (`!u M rho a. (!i. i < M ==> rho i <= u) /\ (!i. M <= i ==> rho i = 0)
      ==> hjt_subst (u+1) M rho a = rho`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hjt_subst; FUN_EQ_THM] THEN
    X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `(rho:num->num) i <= u` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; REFL_TAC];
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let HJT_GEN_ALMOST_MONO = prove
 (`!chi:(num->num)->num.
   !t Ns M l0 p a.
    1 <= t /\ hjt_line t M l0 /\ a < t /\
    (!x a a'. (!i. i < Ns ==> x i <= t + 1) /\ (!i. Ns <= i ==> x i = 0) /\
              a < t /\ a' < t
              ==> chi(hjt_prod Ns x (hjt_subst t M l0 a)) =
                  chi(hjt_prod Ns x (hjt_subst t M l0 a'))) /\
    (!i. i < Ns ==> p i <= t + 1)
    ==> chi(hjt_subst (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l0)) a) =
        chi(hjt_prod Ns (hjt_subst (t+1) Ns p a) (hjt_subst t M l0 0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `hjt_subst (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l0)) a =
    hjt_prod Ns (hjt_subst (t+1) Ns p a) (hjt_subst t M l0 a)` SUBST1_TAC THENL
   [MATCH_MP_TAC HJT_PROD_LIFT_SUBST_LE THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   if is_forall(concl th) &&
      (let bd = snd(strip_forall(concl th)) in is_imp bd &&
       (length(conjuncts(fst(dest_imp bd))) >= 4))
   then MATCH_MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[hjt_subst] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; REFL_TAC];
    ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

let HJT_PROD_LINE = prove
 (`!t Ns M l0 p.
    hjt_line t M l0 /\ (!i. i < Ns ==> p i <= t + 1)
    ==> hjt_line (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hjt_line] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "l0b") (X_CHOOSE_THEN
      `iw:num` STRIP_ASSUME_TAC))
    ASSUME_TAC) THEN
  REWRITE_TAC[hjt_line; hjt_prod; hjt_lift] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `i - Ns < M:num` ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "l0b" (MP_TAC o SPEC `i - Ns:num`) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    EXISTS_TAC `Ns + iw:num` THEN
    SUBGOAL_THEN `~(Ns + iw < Ns:num)` ASSUME_TAC THENL
      [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Ns + iw) - Ns = iw:num` SUBST1_TAC THENL
      [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let HJT_FIXED_LINE_MONO = prove
 (`!chi:(num->num)->num.
   !t Ns M l0 sig.
    hjt_line (t+1) Ns sig /\ hjt_line t M l0 /\
    (!a. a < t + 1
         ==> chi (hjt_prod Ns (hjt_subst (t+1) Ns sig a)
                    (hjt_subst t M l0 0)) =
             chi (hjt_prod Ns (hjt_subst (t+1) Ns sig 0) (hjt_subst t M l0 0)))
    ==> hjt_line (t+1) (Ns+M) (hjt_prod Ns sig (hjt_subst t M l0 0)) /\
        hjt_mono (t+1) (Ns+M) chi (hjt_prod Ns sig (hjt_subst t M l0 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!i. i < M ==> hjt_subst t M l0 0 i <= t) /\
                (!i. M <= i ==> hjt_subst t M l0 0 i = 0)`
                STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[hjt_subst] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
     DISCH_TAC THENL
     [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
       [ARITH_TAC;
        UNDISCH_TAC `hjt_line t M l0` THEN REWRITE_TAC[hjt_line] THEN
          STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
          check (fun th -> is_forall(concl th))) THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~(i < M:num)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. hjt_subst (t+1) (Ns+M) (hjt_prod Ns sig (hjt_subst t M l0 0)) a =
        hjt_prod Ns (hjt_subst (t+1) Ns sig a) (hjt_subst t M l0 0)`
        ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[HJT_SUBST_PROD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC HJT_SUBST_FIXED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[hjt_line; hjt_prod] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [UNDISCH_TAC `hjt_line (t + 1) Ns sig` THEN REWRITE_TAC[hjt_line] THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `i - Ns:num` o
          check (fun th -> concl th = `!i. i < M ==>
            hjt_subst t M l0 0 i <= t`)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC]];
      UNDISCH_TAC `hjt_line (t + 1) Ns sig` THEN REWRITE_TAC[hjt_line] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `iw:num` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `iw:num` THEN
      SUBGOAL_THEN `iw < Ns:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM_ARITH_TAC];
    REWRITE_TAC[hjt_mono] THEN MAP_EVERY X_GEN_TAC [`a:num`; `a':num`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_forall c &&
         (let bd = snd(strip_forall c) in
          is_imp bd &&
          (let cc = snd(dest_imp bd) in
           is_eq cc && can (find_term (fun tm -> tm = `hjt_subst (t+1)
             Ns sig 0`)) cc))
      then (MP_TAC(SPEC `a:num` th) THEN
        MP_TAC(SPEC `a':num` th)) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let HJT_KEY = prove
 (`!t r.
  1 <= t /\ (!r'. 1 <= r' ==> ?N. hales_jewett_template t r' N)
  ==> !s. ?N. !chi:(num->num)->num. (!x. chi x < r)
              ==> (?tw. hjt_line (t+1) N tw /\ hjt_mono (t+1) N chi tw) \/
                  (?Lf cf focus. hjt_focused chi t N Lf cf focus s)`,
(REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(\i j:num. 0):num->num->num`; `(\i:num. 0):num->num`;
      `(\j:num. 0):num->num`] THEN
    REWRITE_TAC[hjt_focused; LT];
    ALL_TAC]) THEN
(ASM_CASES_TAC `r = 0` THENL
   [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `(\i:num. 0):num->num`) THEN ARITH_TAC;
    ALL_TAC]) THEN
(SUBGOAL_THEN `1 <= r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
(FIRST_X_ASSUM(X_CHOOSE_TAC `Ns:num`)) THEN
(SUBGOAL_THEN `?M. hales_jewett_template t (r EXP ((t+2) EXP Ns)) M`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) &&
         (let bd = snd(strip_forall(concl th)) in is_imp bd &&
          (fst(dest_imp bd) = `1 <= r'`))
      then MATCH_MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    REWRITE_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC]) THEN
(EXISTS_TAC `Ns + M:num` THEN X_GEN_TAC `chi:(num->num)->num` THEN
  DISCH_TAC) THEN
(MP_TAC(ISPECL [`chi:(num->num)->num`; `t:num`; `Ns:num`; `M:num`; `r:num`]
   HJT_RECOLOUR)) THEN
(ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:(num->num)->num` STRIP_ASSUME_TAC)) THEN
(FIRST_X_ASSUM(fun th ->
   if is_comb(concl th) &&
     (fst(strip_comb(concl th)) = `hales_jewett_template`) then
     MP_TAC(REWRITE_RULE[hales_jewett_template] th) else NO_TAC)) THEN
(DISCH_THEN(MP_TAC o SPEC `psi:(num->num)->num`)) THEN
(ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num->num` STRIP_ASSUME_TAC)) THEN
(FIRST_X_ASSUM(fun th ->
   if is_forall(concl th) &&
      (let bd = snd(strip_forall(concl th)) in is_imp bd &&
       (let ant = fst(dest_imp bd) in
        is_comb ant && (fst(strip_comb ant) = `hjt_mono`)))
   then MP_TAC(SPEC `l0:num->num` th) else NO_TAC)) THEN
(ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
(FIRST_X_ASSUM(fun th ->
   if is_forall(concl th) &&
      (let bd = snd(strip_forall(concl th)) in is_imp bd &&
       (let ant = fst(dest_imp bd) in is_forall ant))
   then MP_TAC(SPEC `\x. (chi:(num->num)->num)(hjt_prod Ns x (hjt_subst
     t M l0 0))` th)
   else NO_TAC)) THEN
(BETA_TAC) THEN
(ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
(DISCH_THEN DISJ_CASES_TAC) THENL
[ ((FIRST_X_ASSUM(X_CHOOSE_THEN `sg:num->num` STRIP_ASSUME_TAC)) THEN
(DISJ1_TAC THEN EXISTS_TAC `hjt_prod Ns sg (hjt_subst t M l0 0)`) THEN
(SUBGOAL_THEN `!i. hjt_subst t M l0 0 i <= t` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[hjt_subst] THEN
    COND_CASES_TAC THENL
     [COND_CASES_TAC THENL
       [ARITH_TAC;
        UNDISCH_TAC `hjt_line t M l0` THEN REWRITE_TAC[hjt_line] THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ARITH_TAC];
    ALL_TAC]) THEN
(SUBGOAL_THEN `!i. M <= i ==> hjt_subst t M l0 0 i = 0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[hjt_subst] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
(SUBGOAL_THEN
   `!a. hjt_subst (t+1) (Ns+M) (hjt_prod Ns sg (hjt_subst t M l0 0)) a =
        hjt_prod Ns (hjt_subst (t+1) Ns sg a) (hjt_subst t M l0 0)`
        ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[HJT_SUBST_PROD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC HJT_SUBST_FIXED THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
(CONJ_TAC THENL
   [REWRITE_TAC[hjt_line; hjt_prod] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [UNDISCH_TAC `hjt_line (t + 1) Ns sg` THEN REWRITE_TAC[hjt_line] THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(fun th ->
          if concl th = `!i. hjt_subst t M l0 0 i <= t` then
            MP_TAC(SPEC `i - Ns:num` th) else NO_TAC) THEN ARITH_TAC];
      UNDISCH_TAC `hjt_line (t + 1) Ns sg` THEN REWRITE_TAC[hjt_line] THEN
      STRIP_TAC THEN EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[] THEN
        ASM_ARITH_TAC];
    REWRITE_TAC[hjt_mono] THEN MAP_EVERY X_GEN_TAC [`a:num`; `a':num`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `hjt_mono (t + 1) Ns
        (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) sg` THEN
    REWRITE_TAC[hjt_mono] THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`a:num`; `a':num`]) THEN ASM_REWRITE_TAC[]]));
  ((FIRST_X_ASSUM(fun th ->
   if is_exists(concl th) then
     X_CHOOSE_THEN `Lf:num->num->num`
      (X_CHOOSE_THEN `cf:num->num`
        (X_CHOOSE_THEN `focus:num->num` STRIP_ASSUME_TAC)) th
   else NO_TAC)) THEN
(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[hjt_focused]) THEN STRIP_TAC) THEN
(ASM_CASES_TAC `s = 0`) THENL
[ ((ASM_REWRITE_TAC[ARITH] THEN DISJ2_TAC) THEN
(MAP_EVERY EXISTS_TAC
   [`\i:num. hjt_prod Ns (\j:num. 0) (hjt_lift t M l0)`;
    `\i:num. (chi:(num->num)->num)(hjt_prod Ns
                                     (\j:num. 0)(hjt_subst t M l0 0))`;
    `hjt_prod Ns (\j:num. 0)(hjt_subst t M l0 t)`]) THEN
(SUBGOAL_THEN `!a. hjt_subst (t+1) Ns (\j:num. 0) a = (\j:num. 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[hjt_subst; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC]) THEN
(REWRITE_TAC[hjt_focused] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[hjt_almost_mono] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJT_PROD_LINE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ARITH_TAC;
      X_GEN_TAC `a:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`chi:(num->num)->num`; `t:num`; `Ns:num`; `M:num`;
                     `l0:num->num`; `(\j:num. 0):num->num`;
                       `a:num`] HJT_GEN_ALMOST_MONO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LE_0] THEN
        REPEAT STRIP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN MESON_TAC[];
    REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`t:num`; `M:num`; `l0:num->num`; `Ns:num`;
                   `(\j:num. 0):num->num`;
                   `t:num`] HJT_PROD_LIFT_SUBST_LE) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]]));
  ((SUBGOAL_THEN `hjt_line (t+1) Ns (Lf(0:num))` MP_TAC THENL
   [UNDISCH_TAC `forall i:num. i < s ==> hjt_almost_mono
      (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)` THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(s=0) ==> 0 < s`; hjt_almost_mono] THEN
    MESON_TAC[];
    ALL_TAC]) THEN
(DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(REWRITE_RULE[hjt_line] th))) THEN
(SUBGOAL_THEN `hjt_subst (t+1) Ns (Lf(0:num)) t = focus` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `!i:num. i < s ==> hjt_subst (t + 1) Ns (Lf i) t = focus`
      then MATCH_MP_TAC th else NO_TAC) THEN ASM_ARITH_TAC;
    ALL_TAC]) THEN
(SUBGOAL_THEN
   `(!i. i < Ns ==> (focus:num->num) i <= t) /\ (!i. Ns <= i ==> focus i = 0)`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `hjt_subst (t+1) Ns (Lf(0:num)) t = focus` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[hjt_subst] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `k < Ns:num` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
        check (fun th -> concl th = `!i:num. i < Ns ==> Lf 0 i <= t + 1`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `~(k < Ns:num)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC];
    ALL_TAC]) THEN
(SUBGOAL_THEN `!a. hjt_subst (t+1) Ns focus a = focus` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HJT_SUBST_FIXED THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
(ASM_CASES_TAC
   `?i:num. i < s /\
            cf i = (chi:(num->num)->num)(hjt_prod Ns focus (hjt_subst t M
     l0 0))`) THENL
[ ((FIRST_X_ASSUM(X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC o
   check (fun th -> is_exists(concl th) &&
     (fst(dest_exists(concl th)) = `i:num`)))) THEN
(SUBGOAL_THEN `hjt_subst (t+1) Ns (Lf(i0:num)) t = focus` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `!i:num. i < s ==> hjt_subst (t + 1) Ns (Lf i) t = focus`
      then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
(SUBGOAL_THEN
   `hjt_almost_mono (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns
     (Lf(i0:num)) (cf i0)`
   MP_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `forall i:num. i < s ==> hjt_almost_mono
          (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)`
      then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
(REWRITE_TAC[hjt_almost_mono] THEN BETA_TAC THEN STRIP_TAC) THEN
(SUBGOAL_THEN
   `!a. a <= t ==>
        chi (hjt_prod Ns (hjt_subst (t + 1) Ns (Lf(i0:num)) a)
               (hjt_subst t M l0 0)) =
        (cf:num->num) i0` ASSUME_TAC THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN ASM_CASES_TAC `a:num < t` THENL
     [FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_forall c && (let bd = snd(strip_forall c) in
           is_imp bd && (fst(dest_imp bd) = `a:num < t`))
        then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `a:num = t` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM ACCEPT_TAC];
    ALL_TAC]) THEN
(DISJ1_TAC THEN
 EXISTS_TAC `hjt_prod Ns (Lf(i0:num)) (hjt_subst t M l0 0)`) THEN
(REWRITE_TAC[GSYM hjt_line] THEN
  MATCH_MP_TAC(ISPEC `chi:(num->num)->num` HJT_FIXED_LINE_MONO) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `chi (hjt_prod Ns (hjt_subst (t + 1) Ns (Lf(i0:num)) a)
           (hjt_subst t M l0 0)) =
    (cf:num->num) i0 /\
    chi (hjt_prod Ns (hjt_subst (t + 1) Ns (Lf i0) 0)
           (hjt_subst t M l0 0)) = cf i0`
   (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && (let bd = snd(strip_forall c) in
       is_imp bd && (fst(dest_imp bd) = `a:num <= t`))
    then MATCH_MP_TAC th else NO_TAC) THEN ASM_ARITH_TAC));
  ((DISJ2_TAC) THEN
(MAP_EVERY EXISTS_TAC
   [`\i:num. hjt_prod Ns (if i < s then Lf i else focus) (hjt_lift t M l0)`;
    `\i:num. if i < s then cf i
             else (chi:(num->num)->num)(hjt_prod Ns focus
                                          (hjt_subst t M l0 0))`;
    `hjt_prod Ns focus (hjt_subst t M l0 t)`]) THEN
(SUBGOAL_THEN
   `!p k. k < Ns ==> (if p:num < s then Lf p else focus) (k:num) <= t + 1`
   ASSUME_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `forall i:num. i < s ==> hjt_almost_mono
        (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)` THEN
      DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[hjt_almost_mono; hjt_line] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
        check (fun th -> concl th = `!i:num. i < Ns ==>
          (focus:num->num) i <= t`)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC]) THEN
(SUBGOAL_THEN
   `!p. hjt_subst (t+1) (Ns+M)
          (hjt_prod Ns (if p:num < s then Lf p else focus)
             (hjt_lift t M l0)) t =
        hjt_prod Ns (hjt_subst (t+1) Ns (if p:num < s then Lf p else focus) t)
                   (hjt_subst t M l0 t)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HJT_PROD_LIFT_SUBST_LE THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC]) THEN
(SUBGOAL_THEN
   `!p. p < SUC s ==> hjt_subst (t+1) Ns (if p:num < s then Lf p else
     focus) t = focus`
   ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        if concl th = `!i:num. i < s ==> hjt_subst (t + 1) Ns (Lf i) t = focus`
        then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
(REWRITE_TAC[hjt_focused] THEN REPEAT CONJ_TAC THENL
  [ ((X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[hjt_almost_mono] THEN
  BETA_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HJT_PROD_LINE THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
(X_GEN_TAC `a:num` THEN DISCH_TAC) THEN
(MP_TAC(ISPECL [`chi:(num->num)->num`; `t:num`; `Ns:num`; `M:num`;
                 `l0:num->num`;
                 `if p:num < s then Lf p else (focus:num->num)`;
                   `a:num`] HJT_GEN_ALMOST_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_forall c && (let bd = snd(strip_forall c) in
           is_imp bd &&
           (let cc = snd(dest_imp bd) in
            is_eq cc && can
              (find_term (fun tm -> tm = `hjt_prod Ns x (hjt_subst t
              M l0 a)`)) cc))
        then MATCH_ACCEPT_TAC th else NO_TAC);
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC) THEN
(COND_CASES_TAC THENL
   [REWRITE_TAC[] THEN
    UNDISCH_TAC `forall i:num. i < s ==> hjt_almost_mono
      (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)` THEN
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[hjt_almost_mono] THEN
    BETA_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = `forall a. hjt_subst (t + 1) Ns focus a = focus`
      then REWRITE_TAC[th] else NO_TAC)]));
    ((MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
  REWRITE_TAC[ARITH_RULE `n < SUC s <=> n < s \/ n = s`] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_forall c && (let b = snd(strip_forall c) in
         is_imp b && (snd(dest_imp b) = `i:num = j`))
      then MATCH_MP_TAC th else NO_TAC) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM ACCEPT_TAC; FIRST_X_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(MP_TAC o
        check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `~(q < s:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o
      check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?i. i < s /\
      (cf:num->num) i = chi (hjt_prod Ns focus (hjt_subst t M l0 0))`
     (fun th -> ASM_MESON_TAC[th]) THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(p < s:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o
      check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?i. i < s /\
      (cf:num->num) i = chi (hjt_prod Ns focus (hjt_subst t M l0 0))`
     (fun th -> ASM_MESON_TAC[th]) THEN
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]));
    ((X_GEN_TAC `p:num` THEN DISCH_TAC) THEN
(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && (fst(dest_forall c) = `p:num`) &&
      is_eq(snd(strip_forall c)) &&
       (can (find_term (fun tm -> tm = `hjt_lift t M l0`))
         (lhs(snd(strip_forall c))))
    then REWRITE_TAC[SPEC `p:num` th] else NO_TAC)) THEN
(SUBGOAL_THEN
   `hjt_subst (t+1) Ns (if p:num < s then Lf p else focus) t = focus`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REFL_TAC])) ])) ]) ]) ]);;

let HJT_STEP = prove
 (`!t. 1 <= t /\ (!r'. 1 <= r' ==> ?N. hales_jewett_template t r' N)
       ==> !r. 1 <= r ==> ?N. hales_jewett_template (t + 1) r N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:num`; `r:num`] HJT_KEY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN REWRITE_TAC[hales_jewett_template] THEN
  X_GEN_TAC `chi:(num->num)->num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chi:(num->num)->num`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ACCEPT_TAC th) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `Lf:num->num->num`
   (X_CHOOSE_THEN `cf:num->num`
     (X_CHOOSE_THEN `focus:num->num` ASSUME_TAC))) THEN
  MATCH_MP_TAC(ISPECL [`chi:(num->num)->num`; `t:num`; `r:num`; `N:num`;
                       `Lf:num->num->num`; `cf:num->num`; `focus:num->num`]
   HJT_COLLAPSE) THEN ASM_REWRITE_TAC[]);;

let HALES_JEWETT_TEMPLATE = prove
 (`!t r. 1 <= t /\ 1 <= r ==> ?N. hales_jewett_template t r N`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC;  (* t = 0 contradicts 1 <= SUC 0 *)
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(* SUC t = 1: base case via HJT_1 *)
    ASM_REWRITE_TAC[ARITH] THEN ASM_MESON_TAC[HJT_1];
    (* SUC t = t + 1, t >= 1: the outer induction hypothesis gives *)
    (* hales_jewett_template t for all numbers of colours          *)
    REWRITE_TAC[ADD1] THEN
    MP_TAC(ISPEC `t:num` HJT_STEP) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_ARITH_TAC;
        X_GEN_TAC `r':num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Hales-Jewett for lines of words and finite colour sets.                   *)
(* ------------------------------------------------------------------------- *)

let HJ_FINITE_INDEX = prove
 (`!s:A->bool. FINITE s
               ==> ?f. (!x. x IN s ==> f x < CARD s) /\
                       (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `{i:num | i < CARD(s:A->bool)}`]
    CARD_LE_INJ) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; LE_REFL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]);;

let HJ_LINE_POINT_TEMPLATE = prove
 (`!k n tw a. 1 <= k /\ (!i. i < n ==> tw i <= k)
              ==> hj_line_point k (\i. if i < n then tw i else 0) a =
                  hjt_subst k n tw a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[hj_line_point; hj_subst; hjt_subst; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num < n` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(tw:num->num) i = k` THEN
    ASM_REWRITE_TAC[LT_REFL; SUB_REFL] THEN
    SUBGOAL_THEN `(tw:num->num) i < k` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[LE_LT];
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`]]);;

let HALES_JEWETT = prove
 (`!k r. 1 <= k /\ 1 <= r
         ==> ?N. !n c. N <= n /\ (!x. c x < r)
                       ==> ?l. hj_line k n l /\
                               !a b. a < k /\ b < k
                                     ==> c(hj_line_point k l a) =
                                         c(hj_line_point k l b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `r:num`] HALES_JEWETT_TEMPLATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hales_jewett_template k r n` MP_TAC THENL
   [MATCH_MP_TAC HJT_MONO_N THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hales_jewett_template] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(num->num)->num`) THEN
  ASM_REWRITE_TAC[hjt_line; hjt_mono] THEN
  DISCH_THEN(X_CHOOSE_THEN `tw:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. if i < n then (tw:num->num) i else 0` THEN
  ASM_SIMP_TAC[HJ_LINE_POINT_TEMPLATE] THEN
  REWRITE_TAC[hj_line; hj_subspace; IN_HJ_CUBE] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `t <= k ==> t < k + 1`) THEN ASM_SIMP_TAC[];
    SIMP_TAC[GSYM NOT_LT];
    REWRITE_TAC[ARITH_RULE `j < 1 <=> j = 0`; ADD_CLAUSES] THEN
    X_GEN_TAC `j:num` THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ASM_REWRITE_TAC[]]);;

let HALES_JEWETT_FINITE = prove
 (`!k (S:A->bool).
        1 <= k /\ FINITE S /\ ~(S = {})
        ==> ?N. !n c. N <= n /\ (!x. x IN hj_cube k n ==> c x IN S)
                      ==> ?l. hj_line k n l /\
                              !a b. a < k /\ b < k
                                    ==> c(hj_line_point k l a) =
                                        c(hj_line_point k l b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `f:A->num` STRIP_ASSUME_TAC o
    MATCH_MP HJ_FINITE_INDEX) THEN
  MP_TAC(SPECL [`k:num`; `CARD(S:A->bool)`] HALES_JEWETT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`n:num`; `\x. if x IN hj_cube k n then (f:A->num)((c:(num->num)->A) x)
                  else 0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[CARD_EQ_0; LT_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`]) THEN
  ASM_SIMP_TAC[HJ_LINE_POINT_CUBE] THEN ASM_MESON_TAC[HJ_LINE_POINT_CUBE]);;

let HJ_SUBST_LINE = prove
 (`!k n l w. hj_line k n l ==> hj_subst k l w = hj_line_point k l (w 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_line; hj_subspace; IN_HJ_CUBE] THEN
  STRIP_TAC THEN
  REWRITE_TAC[hj_line_point; hj_subst; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(l:num->num) i - k = 0` (fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `i:num < n` THENL
   [SUBGOAL_THEN `(l:num->num) i < k + 1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ARITH_TAC];
    SUBGOAL_THEN `(l:num->num) i = 0` (fun th -> REWRITE_TAC[th; SUB_0]) THEN
    ASM_MESON_TAC[NOT_LT]]);;

let HJ_SUBST_TAKE = prove
 (`!k m n z a. 1 <= k /\ hj_subspace k m n z
               ==> hj_subst k z (hj_take m a) = hj_subst k z a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REWRITE_TAC[hj_subst; hj_take; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:num->num) i - k < m` (fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `i:num < n` THENL
   [SUBGOAL_THEN `(z:num->num) i < k + m` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    SUBGOAL_THEN `(z:num->num) i = 0` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Multidimensional Hales-Jewett.                                            *)
(* ------------------------------------------------------------------------- *)

let HJ_PATTERN_INDEX = prove
 (`!(D:B->bool) r.
        FINITE D
        ==> ?R idx. 1 <= R /\
                    (!f:B->num. (!w. w IN D ==> f w < r) ==> idx f < R) /\
                    (!f g:B->num. (!w. w IN D ==> f w < r) /\
                           (!w. w IN D ==> g w < r) /\ idx f = idx g
                           ==> !w. w IN D ==> f w = g w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE {f:B->num | (!w. w IN D ==> f w < r) /\
                       (!w. ~(w IN D) ==> f w = 0)}`
  MP_TAC THENL
   [MP_TAC(ISPECL [`0`; `r:num`; `{i:num | i < r}`; `CARD(D:B->bool)`;
                   `D:B->bool`] HAS_SIZE_FUNSPACE) THEN
    ASM_REWRITE_TAC[HAS_SIZE_NUMSEG_LT; GSYM FINITE_HAS_SIZE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[HAS_SIZE];
    ALL_TAC] THEN
  ABBREV_TAC
   `PS = {f:B->num | (!w. w IN D ==> f w < r) /\
                     (!w. ~(w IN D) ==> f w = 0)}` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ind:(B->num)->num` STRIP_ASSUME_TAC o
    MATCH_MP HJ_FINITE_INDEX) THEN
  SUBGOAL_THEN
   `!f:B->num. (!w. w IN D ==> f w < r)
               ==> (\w. if w IN D then f w else 0) IN PS`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "PS" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`CARD(PS:(B->num)->bool) + 1`;
    `\f:B->num. (ind:(B->num)->num)(\w. if w IN D then f w else 0)`] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x < n + 1`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w. if w IN D then (f:B->num) w else 0) =
    (\w. if w IN D then g w else 0)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]]);;

let MULTIDIM_HALES_JEWETT = prove
 (`!k m r. 1 <= k /\ 1 <= r
           ==> ?N. !n c. N <= n /\ (!x. c x < r)
                         ==> ?z. hj_subspace k m n z /\
                                 !a b. a IN hj_cube k m /\ b IN hj_cube k m
                                       ==> c(hj_subst k z a) =
                                           c(hj_subst k z b)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(\i. 0):num->num` THEN
    REWRITE_TAC[HJ_SUBSPACE_0; HJ_CUBE_0] THEN
    REWRITE_TAC[IN_SING; IN_HJ_CUBE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "ih")) THEN
  MP_TAC(ISPECL [`hj_cube k N1`; `r:num`] HJ_PATTERN_INDEX) THEN
  REWRITE_TAC[FINITE_HJ_CUBE] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num`
   (X_CHOOSE_THEN `idx:((num->num)->num)->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`k:num`; `R:num`] HALES_JEWETT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "hj")) THEN
  EXISTS_TAC `N1 + N2:num` THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "hj" (MP_TAC o SPECL
   [`n - N1:num`;
    `\y. (idx:((num->num)->num)->num)
           (\w. (c:(num->num)->num)(hj_concat N1 w y))`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!w a. w IN hj_cube k N1 /\ a < k
          ==> (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l a)) =
              c(hj_concat N1 w (hj_line_point k l 0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `0`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`\w. (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l a))`;
      `\w. (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l 0))`] o
     check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
   [`N1:num`;
    `\w. (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l 0))`]) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hj_join k N1 m z1 l` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `n = N1 + (n - N1):num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
    ASM_REWRITE_TAC[GSYM hj_line];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN hj_cube k (SUC m)
        ==> (c:(num->num)->num)(hj_subst k (hj_join k N1 m z1 l) a) =
            c(hj_concat N1 (hj_subst k z1 (hj_take m a))
                (hj_line_point k l 0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[HJ_SUBST_JOIN] THEN ASM_SIMP_TAC[HJ_SUBST_TAKE] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HJ_SUBST_LINE th]) THEN
    REWRITE_TAC[hj_drop; ADD_CLAUSES] THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `N1:num`; `z1:num->num`;
                   `a:num->num`] HJ_SUBST_TAKE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[GSYM ADD1];
      UNDISCH_TAC `(a:num->num) IN hj_cube k (SUC m)` THEN
      REWRITE_TAC[IN_HJ_CUBE] THEN MESON_TAC[LT]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[GSYM ADD1]);;

(* ========================================================================= *)
(* Graham-Rothschild for lines (DKT Proposition 2): for all k, m, r >= 1     *)
(* and n large, every r-colouring of the lines of [k]^n is constant on       *)
(* the lines of some m-dimensional subspace (GRAHAM_ROTHSCHILD_LINES).       *)
(*                                                                           *)
(* * FOLKMAN_FOCUS, FOLKMAN: the case k = 1, where lines of [1]^m are the    *)
(*   nonempty subsets of [m] (Folkman's theorem).  By multidimensional       *)
(*   Hales-Jewett over {0, 1}, the colour of a line depends only on its      *)
(*   first wildcard (hj_first_wildcard); in the alphabet-1 encoding the      *)
(*   fixed letters 1 of an alphabet-2 word are the variable 0                *)
(*   (HJ_SUBSPACE_HEAD1, HJ_SUBST_HEAD1), so the fixed part is absorbed      *)
(*   into the first variable.  Pigeonhole on the first wildcard then gives   *)
(*   FOLKMAN.                                                                *)
(* * HJ_LETTER_INDEP: the colour of a line can be made to depend only on     *)
(*   its wildcard set hj_wildcards k u, by induction on the number of        *)
(*   variables M with Hales-Jewett for the colouring by colour patterns of   *)
(*   the next block.                                                         *)
(* * GRAHAM_ROTHSCHILD_LINES: HJ_LETTER_INDEP, then FOLKMAN for the induced  *)
(*   colouring of the wildcard sets, merged back by hj_dlift                 *)
(*   (HJ_WILDCARDS_DLIFT).                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The first wildcard of a line of [1]^m.                                    *)
(* ------------------------------------------------------------------------- *)

let hj_first_wildcard = new_definition
 `hj_first_wildcard (u:num->num) = minimal i. u i = 1`;;

let HJ_FIRST_WILDCARD = prove
 (`!n u. hj_line 1 n u
         ==> hj_first_wildcard u < n /\ u (hj_first_wildcard u) = 1 /\
             !i. i < hj_first_wildcard u ==> ~(u i = 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_line; hj_subspace] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ARITH; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j. (u:num->num) j = 1` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN REWRITE_TAC[GSYM hj_first_wildcard] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NOT_LT; LET_TRANS]);;

let HJ_FIRST_WILDCARD_UNIQUE = prove
 (`!u i. u i = 1 /\ (!j. j < i ==> ~(u j = 1)) ==> hj_first_wildcard u = i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_first_wildcard] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[]);;

let HJ_LINE_1_DROP = prove
 (`!n u. hj_line 1 (n + 1) u /\ u 0 = 0 ==> hj_line 1 n (hj_drop 1 u)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[hj_line; hj_subspace; IN_HJ_CUBE; hj_drop] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i - 1` THEN
    SUBGOAL_THEN `~(i = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(u:num->num) i = 1 + j` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`] THEN
      ASM_ARITH_TAC]]);;

let HJ_FIRST_WILDCARD_DROP = prove
 (`!n u. hj_line 1 (n + 1) u /\ u 0 = 0
         ==> hj_first_wildcard u = hj_first_wildcard (hj_drop 1 u) + 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HJ_FIRST_WILDCARD_UNIQUE THEN
  MP_TAC(SPECL [`n:num`; `u:num->num`] HJ_LINE_1_DROP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP HJ_FIRST_WILDCARD) THEN
  REWRITE_TAC[hj_drop] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j = 0` THEN
  ASM_REWRITE_TAC[ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - 1`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(j = 0) ==> j - 1 + 1 = j`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Alphabet-2 words as variable words over the alphabet 1.                   *)
(* ------------------------------------------------------------------------- *)

let HJ_SUBST_IN_CUBE = prove
 (`!k k' m n z a. 1 <= k /\ k <= k' /\ hj_subspace k m n z /\ a IN hj_cube k' m
                  ==> hj_subst k z a IN hj_cube k' n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_subst] THEN
  STRIP_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `~(z < k) /\ z < k + m ==> z - k < m:num`) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`]]);;

let HJ_SUBSPACE_HEAD1 = prove
 (`!m n Y. hj_subspace 2 m n Y
           ==> hj_subspace 1 (m + 1) (1 + n)
                     (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_concat] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < 1` THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      SUBGOAL_THEN `(Y:num->num)(i - 1) < 2 + m` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ARITH_TAC]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i < 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j = 0` THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `?p. p < n /\ (Y:num->num) p = 2 + (j - 1)`
     (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `p + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(p + 1 < 1)`; ADD_SUB] THEN
    ASM_ARITH_TAC]);;

let HJ_SUBST_HEAD1 = prove
 (`!Y u. u 0 = 1
         ==> hj_subst 1 (hj_concat 1 (\i. if i = 0 then 1 else 0) Y) u =
             hj_concat 1 (\i. if i = 0 then 1 else 0)
               (hj_subst 2 Y (hj_drop 1 u))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[hj_subst; hj_concat; hj_drop; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < 1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH; SUB_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `(Y:num->num)(i - 1) < 1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `y < 1 ==> y < 2`]; ALL_TAC] THEN
  ASM_CASES_TAC `(Y:num->num)(i - 1) = 1` THENL
   [ASM_REWRITE_TAC[ARITH; SUB_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(y < 1) /\ ~(y = 1) ==> ~(y < 2)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HJ_SUBST_HEAD0 = prove
 (`!d u. u 0 = 0
           ==> hj_subst 1 (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d) u =
               hj_concat 1 (\i. 0) (hj_subst 1 d (hj_drop 1 u))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HJ_SUBST_JOIN] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[hj_subst; FUN_EQ_THM] THEN
  X_GEN_TAC `x:num` THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[ARITH; SUB_REFL]);;

let HJ_SUBST_HEAD1E = prove
 (`!d u. u 0 = 1
           ==> hj_subst 1 (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d) u =
               hj_concat 1 (\i. if i = 0 then 1 else 0)
                 (hj_subst 1 d (hj_drop 1 u))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HJ_SUBST_JOIN] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[hj_subst; FUN_EQ_THM] THEN
  X_GEN_TAC `x:num` THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[ARITH; SUB_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Folkman's theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let HJ_SUBSPACE_1_UNIT = prove
 (`hj_subspace 1 1 1 (\i. if i = 0 then 1 else 0)`,
  REWRITE_TAC[hj_subspace; IN_HJ_CUBE] THEN REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`];
    EXISTS_TAC `0` THEN ASM_ARITH_TAC]);;

let FOLKMAN_FOCUS = prove
 (`!m r. 1 <= r
         ==> ?N. !n c. N <= n /\ (!x. c x < r)
                       ==> ?d (ph:num->num).
                              hj_subspace 1 m n d /\
                              !u. hj_line 1 m u
                                  ==> c(hj_subst 1 d u) =
                                      ph(hj_first_wildcard u)`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(\i. 0):num->num`; `(\i. 0):num->num`] THEN
    REWRITE_TAC[HJ_SUBSPACE_0; IN_HJ_CUBE] THEN CONJ_TAC THENL
     [ARITH_TAC;
      REWRITE_TAC[hj_line; hj_subspace; LT] THEN
      MESON_TAC[ARITH_RULE `0 < 1`]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "ih")) THEN
  MP_TAC(SPECL [`2`; `N1:num`; `r:num`] MULTIDIM_HALES_JEWETT) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "mhj")) THEN
  EXISTS_TAC `N2 + 1` THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "mhj" (MP_TAC o SPECL
   [`n - 1`;
    `\y. (c:(num->num)->num)(hj_concat 1
                               (\i. if i = 0 then 1 else 0) y)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->num` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN
   `hj_subspace 1 (N1 + 1) n (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `n = 1 + (n - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC HJ_SUBSPACE_HEAD1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
   [`N1:num`;
    `\v. (c:(num->num)->num)
           (hj_subst 1 (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)
                   (hj_concat 1 (\i. 0) v))`]) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num`
   (X_CHOOSE_THEN `ph:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `hj_subspace 1 (SUC m) (N1 + 1)
      (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `SUC m = 1 + m /\ N1 + 1 = 1 + N1`] THEN
    MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
    ASM_REWRITE_TAC[HJ_SUBSPACE_1_UNIT; LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`hj_subst 1 (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)
            (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d)`;
    `\t. if t = 0
         then (c:(num->num)->num)
                (hj_concat 1 (\i. if i = 0 then 1 else 0)
                   (hj_subst 2 Y (\i. 0)))
         else (ph:num->num)(t - 1)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `N1 + 1` THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->num` THEN DISCH_TAC THEN REWRITE_TAC[HJ_SUBST_SUBST] THEN
  SUBGOAL_THEN `(u:num->num) 0 = 0 \/ u 0 = 1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `hj_line 1 (SUC m) u` THEN
    REWRITE_TAC[hj_line; hj_subspace; IN_HJ_CUBE] THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT1) THEN
    ARITH_TAC;
    (* first variable not a wildcard *)
    ASM_SIMP_TAC[HJ_SUBST_HEAD0] THEN
    SUBGOAL_THEN `hj_line 1 m (hj_drop 1 u)` ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_LINE_1_DROP THEN ASM_REWRITE_TAC[GSYM ADD1];
      ALL_TAC] THEN
    MP_TAC(SPECL [`m:num`; `u:num->num`] HJ_FIRST_WILDCARD_DROP) THEN
    ASM_REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN ASM_SIMP_TAC[];
    (* first variable a wildcard *)
    ASM_SIMP_TAC[HJ_SUBST_HEAD1E] THEN
    W(fun (_,w) -> SUBGOAL_THEN
      (mk_eq(lhand w, `(c:(num->num)->num)
          (hj_concat 1 (\i. if i = 0 then 1 else 0) (hj_subst 2 Y (\i. 0)))`))
      SUBST1_TAC) THENL
     [MP_TAC(ISPECL [`Y:num->num`;
                     `hj_concat 1 (\i. if i = 0 then 1 else 0)
                           (hj_subst 1 d (hj_drop 1 u))`] HJ_SUBST_HEAD1) THEN
      ANTS_TAC
      THENL [REWRITE_TAC[hj_concat; ARITH]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[HJ_DROP_CONCAT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HJ_SUBST_IN_CUBE THEN
        EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[ARITH] THEN
        MATCH_MP_TAC HJ_DROP_CUBE THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM ADD1] THEN
        MP_TAC(MATCH_MP HJ_LINE_CUBE (ASSUME `hj_line 1 (SUC m) u`)) THEN
        REWRITE_TAC[ARITH];
        REWRITE_TAC[IN_HJ_CUBE] THEN ARITH_TAC];
      SUBGOAL_THEN `hj_first_wildcard u = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC HJ_FIRST_WILDCARD_UNIQUE THEN ASM_REWRITE_TAC[LT];
        REWRITE_TAC[]]]]);;

let HJ_LINE_1_UNIT = prove
 (`!n i. i < n ==> hj_line 1 n (\j. if j = i then 1 else 0) /\
                   hj_first_wildcard (\j. if j = i then 1 else 0) = i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[hj_line; hj_subspace; IN_HJ_CUBE] THEN REPEAT STRIP_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC;
      COND_CASES_TAC THEN ASM_ARITH_TAC;
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC HJ_FIRST_WILDCARD_UNIQUE THEN REWRITE_TAC[] THEN ARITH_TAC]);;

let FOLKMAN = prove
 (`!m r. 1 <= r
         ==> ?N. !n c. N <= n /\ (!x. c x < r)
                       ==> ?d. hj_subspace 1 m n d /\
                               !u v. hj_line 1 m u /\ hj_line 1 m v
                                     ==> c(hj_subst 1 d u) =
                                         c(hj_subst 1 d v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r * m:num`; `r:num`] FOLKMAN_FOCUS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:(num->num)->num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `c:(num->num)->num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:num->num`
   (X_CHOOSE_THEN `ph:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!i. i < r * m ==> (ph:num->num) i < r` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HJ_LINE_1_UNIT) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\j:num. if j = i then 1 else 0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ph:num->num`; `{i:num | i < r * m}`; `{j:num | j < r}`]
    CARD_PIGEONHOLE) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `J = {i:num | i < r * m /\ (ph:num->num) i = s}` THEN
  SUBGOAL_THEN `FINITE(J:num->bool) /\ m <= CARD J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "J" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{i:num | i < r * m}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `&(r * m) <= &r * &(CARD(J:num->bool))` THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{j:num | j < m}`; `J:num->bool`] CARD_LE_INJ) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!j. j < m ==> (h:num->num) j < r * m /\ (ph:num->num)(h j) = s`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:num->num) j IN J` MP_TAC THENL
     [ASM_SIMP_TAC[]; EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC
   `sel = \i. if ?j. j < m /\ (h:num->num) j = i
              then 1 + (@j. j < m /\ h j = i) else 0` THEN
  SUBGOAL_THEN `!j. j < m ==> (sel:num->num)(h j) = 1 + j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sel" THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= (sel:num->num) i ==> ?j. j < m /\ (h:num->num) j = i`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "sel" THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hj_subspace 1 m (r * m) sel` ASSUME_TAC THENL
   [REWRITE_TAC[hj_subspace; IN_HJ_CUBE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `1 <= (sel:num->num) i` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `1 <= (sel:num->num) i` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[NOT_LT];
        ASM_ARITH_TAC];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXISTS_TAC `(h:num->num) j` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `hj_subst 1 d0 sel` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `r * m:num` THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. hj_line 1 m u ==>
    (c:(num->num)->num)(hj_subst 1 (hj_subst 1 d0 sel) u) = s`
   (fun th -> ASM_MESON_TAC[th]) THEN
  X_GEN_TAC `u:num->num` THEN DISCH_TAC THEN REWRITE_TAC[HJ_SUBST_SUBST] THEN
  SUBGOAL_THEN `hj_line 1 (r * m) (hj_subst 1 sel u)` ASSUME_TAC THENL
   [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HJ_FIRST_WILDCARD) THEN
  ABBREV_TAC `p = hj_first_wildcard(hj_subst 1 sel u)` THEN
  SUBGOAL_THEN `1 <= (sel:num->num) p` MP_TAC THENL
   [UNDISCH_TAC `hj_subst 1 sel u p = 1` THEN REWRITE_TAC[hj_subst] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Wildcard sets and their lifts.                                            *)
(* ------------------------------------------------------------------------- *)

let hj_wildcards = new_definition
 `hj_wildcards k (u:num->num) = \i. if u i = k then 1 else 0`;;

let hj_wlift = new_definition
 `hj_wlift k (w:num->num) = \i. if w i = 1 then k else 0`;;

let hj_dlift = new_definition
 `hj_dlift k (d:num->num) = \i. if d i = 0 then 0 else k + (d i - 1)`;;

let HJ_LINE_EQ = prove
 (`!k n u. hj_line k n u <=> u IN hj_cube (k + 1) n /\ ?i. i < n /\ u i = k`,
  REWRITE_TAC[hj_line; hj_subspace; ARITH_RULE `j < 1 <=> j = 0`] THEN
  MESON_TAC[ADD_CLAUSES]);;

let HJ_WILDCARDS_LINE = prove
 (`!k n u. 1 <= k /\ hj_line k n u ==> hj_line 1 n (hj_wildcards k u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE; hj_wildcards] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let HJ_WLIFT_LINE = prove
 (`!k n w. 1 <= k /\ hj_line 1 n w ==> hj_line k n (hj_wlift k w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE; hj_wlift] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ARITH_TAC;
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

let HJ_WILDCARDS_WLIFT = prove
 (`!k n w. 1 <= k /\ w IN hj_cube 2 n ==> hj_wildcards k (hj_wlift k w) = w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_HJ_CUBE; hj_wildcards; hj_wlift; FUN_EQ_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `(w:num->num) i = 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> ~(0 = k)`] THEN
  ASM_CASES_TAC `i:num < n` THENL
   [SUBGOAL_THEN `(w:num->num) i < 2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    ASM_MESON_TAC[NOT_LT]]);;

let HJ_SUBSPACE_DLIFT = prove
 (`!k m n d. 1 <= k /\ hj_subspace 1 m n d
             ==> hj_subspace k m n (hj_dlift k d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE; hj_dlift] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(d:num->num) i < 1 + m` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    ASM_SIMP_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?i. i < n /\ (d:num->num) i = 1 + j`
     (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let HJ_WILDCARDS_DLIFT = prove
 (`!k d u. 1 <= k
           ==> hj_wildcards k (hj_subst k (hj_dlift k d) u) =
               hj_subst 1 d (hj_wildcards k u)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[hj_wildcards; hj_subst; hj_dlift; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(d:num->num) i = 0` THEN
  ASM_REWRITE_TAC[ARITH] THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k /\ ~(0 = k)`]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> ~(k + d - 1 < k) /\ ~(d < 1)`;
               ARITH_RULE `(k + d - 1) - k = d - 1`]);;

let HJ_LINE_POINT_K = prove
 (`!k n x. hj_line k n x ==> hj_line_point k x k = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REWRITE_TAC[hj_line_point; hj_subst; FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j:num < n` THENL
   [SUBGOAL_THEN `(x:num->num) j = k` (fun th -> REWRITE_TAC[th;
     SUB_REFL]) THEN
    SUBGOAL_THEN `(x:num->num) j < k + 1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    SUBGOAL_THEN `(x:num->num) j = 0` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
    REWRITE_TAC[SUB_0] THEN ASM_ARITH_TAC]);;

let HJ_WILDCARDS_TAKE = prove
 (`!k M u. 1 <= k
           ==> hj_wildcards k (hj_take M u) = hj_take M (hj_wildcards k u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_wildcards; hj_take; FUN_EQ_THM] THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num < M` THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> ~(0 = k)`]);;

let HJ_PAIR_CODE = prove
 (`!r a b. a < r /\ b < r ==> r * a + b < r * (r:num)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `r * a + r:num` THEN ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
  REWRITE_TAC[ARITH_RULE `r * a + r = r * (a + 1)`; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let HJ_PAIR_DECODE = prove
 (`!r a b a' b'. b < r /\ b' < r /\ r * a + b = r * a' + (b':num)
                 ==> a = a' /\ b = b'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r * a + b:num`; `r:num`; `a:num`; `b:num`] DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(SPECL [`r * a' + b':num`; `r:num`; `a':num`; `b':num`]
    DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let HJ_LINE_SUC_CASES = prove
 (`!k M u. 1 <= k /\ hj_line k (SUC M) u
           ==> u M <= k /\
               ((?i. i < M /\ u i = k) ==> hj_line k M (hj_take M u)) /\
               (~(?i. i < M /\ u i = k) ==> hj_take M u IN hj_cube k M) /\
               (~(u M = k) ==> ?i. i < M /\ u i = k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < k + 1 ==> x <= k`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[hj_take] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE];
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    DISCH_TAC THEN REWRITE_TAC[hj_take] THEN CONJ_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(u:num->num) j < k + 1 /\ ~(u j = k)` MP_TAC THENL
       [ASM_SIMP_TAC[ARITH_RULE `j < M ==> j < SUC M`]; ARITH_TAC];
      ASM_REWRITE_TAC[GSYM NOT_LE]];
    DISCH_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `i < SUC M` THEN REWRITE_TAC[LT] THEN
    ASM_MESON_TAC[]]);;

let HJ_WILDCARDS_EQ_VAR = prove
 (`!k u u' i. hj_wildcards k u = hj_wildcards k u' ==> (u i = k <=> u' i = k)`,
  REWRITE_TAC[hj_wildcards; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Letter independence and Graham-Rothschild for lines.                      *)
(* ------------------------------------------------------------------------- *)

let HJ_LETTER_INDEP = prove
 (`!k M r. 1 <= k /\ 1 <= r
           ==> ?N. !n c. N <= n /\ (!x. c x < r)
                         ==> ?z. hj_subspace k M n z /\
                                 !u u'. hj_line k M u /\ hj_line k M u' /\
                                        hj_wildcards k u = hj_wildcards k u'
                                        ==> c(hj_subst k z u) =
                                            c(hj_subst k z u')`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(\i. 0):num->num` THEN
    REWRITE_TAC[HJ_SUBSPACE_0; IN_HJ_CUBE; HJ_LINE_EQ; LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r * r:num`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ni:num` (LABEL_TAC "ih")) THEN
  MP_TAC(SPECL [`k:num`; `Ni:num`; `r:num`] MULTIDIM_HALES_JEWETT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (LABEL_TAC "mhj")) THEN
  MP_TAC(ISPECL [`{w:num->num | hj_line k n1 w}`; `r:num`]
           HJ_PATTERN_INDEX) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `hj_cube (k + 1) n1` THEN
    REWRITE_TAC[FINITE_HJ_CUBE; SUBSET; IN_ELIM_THM; HJ_LINE_CUBE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num`
   (X_CHOOSE_THEN `idx:((num->num)->num)->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`k:num`; `R:num`] HALES_JEWETT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "hj")) THEN
  EXISTS_TAC `n1 + N2:num` THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "hj" (MP_TAC o SPECL
   [`n - n1:num`;
    `\y. (idx:((num->num)->num)->num)
           (\w. (c:(num->num)->num)(hj_concat n1 w y))`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!w a. hj_line k n1 w /\ a < k
          ==> (c:(num->num)->num)(hj_concat n1 w (hj_line_point k x a)) =
              c(hj_concat n1 w (hj_line_point k x 0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `0`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> 0 < k`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`\w. (c:(num->num)->num)(hj_concat n1 w (hj_line_point k x a))`;
      `\w. (c:(num->num)->num)(hj_concat n1 w (hj_line_point k x 0))`] o
     check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REMOVE_THEN "mhj" (MP_TAC o SPECL
   [`n1:num`; `\p. (c:(num->num)->num)(hj_concat n1 p x)`]) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->num` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
   [`Ni:num`;
    `\v. r *
         (c:(num->num)->num)(hj_concat n1 (hj_subst k Y v)
                               (hj_line_point k x 0)) +
         c(hj_concat n1 (hj_subst k Y v) x)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL] THEN GEN_TAC THEN MATCH_MP_TAC HJ_PAIR_CODE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:num->num` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  EXISTS_TAC `hj_join k n1 M (hj_subst k Y z2) x` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `n = n1 + (n - n1):num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
    ASM_REWRITE_TAC[GSYM hj_line] THEN MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN
    EXISTS_TAC `Ni:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. hj_subst k (hj_join k n1 M (hj_subst k Y z2) x) u =
        hj_concat n1 (hj_subst k Y (hj_subst k z2 (hj_take M u)))
          (hj_line_point k x (u M))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[HJ_SUBST_JOIN; HJ_SUBST_SUBST] THEN
    MP_TAC(ISPECL [`k:num`; `M:num`; `Ni:num`; `z2:num->num`;
                   `u:num->num`] HJ_SUBST_TAKE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HJ_SUBST_LINE th]) THEN
    REWRITE_TAC[hj_drop; ADD_CLAUSES];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:num->num`; `u':num->num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `M:num`; `u:num->num`] HJ_LINE_SUC_CASES) THEN
  MP_TAC(SPECL [`k:num`; `M:num`; `u':num->num`] HJ_LINE_SUC_CASES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:num->num) M = k <=> (u':num->num) M = k` ASSUME_TAC THENL
   [ASM_MESON_TAC[HJ_WILDCARDS_EQ_VAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(?i. i < M /\ (u:num->num) i = k) <=> (?i. i < M /\ (u':num->num) i = k)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HJ_WILDCARDS_EQ_VAR]; ALL_TAC] THEN
  SUBGOAL_THEN `hj_wildcards k (hj_take M u) = hj_wildcards k (hj_take M u')`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[HJ_WILDCARDS_TAKE]; ALL_TAC] THEN
  ASM_CASES_TAC `(u:num->num) M = k` THENL
   [SUBGOAL_THEN `(u':num->num) M = k` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATCH_MP HJ_LINE_POINT_K (ASSUME `hj_line k (n - n1) x`)] THEN
    ASM_CASES_TAC `?i. i < M /\ (u:num->num) i = k` THENL
     [SUBGOAL_THEN `hj_line k M (hj_take M u) /\ hj_line k M (hj_take M u')`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`hj_take M (u:num->num)`;
                                    `hj_take M (u':num->num)`] o
        check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
                         can (find_term ((=) `r:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP HJ_PAIR_DECODE o
        (fun th -> CONJ
           (SPEC `hj_concat n1 (hj_subst k Y (hj_subst k z2 (hj_take M u))) x`
                          (ASSUME `!x. (c:(num->num)->num) x < r`))
                    (CONJ (SPEC
                             `hj_concat n1
                                (hj_subst k Y
                                   (hj_subst k z2 (hj_take M u'))) x`
                          (ASSUME `!x. (c:(num->num)->num) x < r`)) th))) THEN
      SIMP_TAC[];
      SUBGOAL_THEN `hj_take M (u:num->num) IN hj_cube k M /\
                    hj_take M (u':num->num) IN hj_cube k M`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
                         can (find_term ((=) `Y:num->num`)) (concl th) &&
                         not (can (find_term ((=) `r:num`)) (concl th)))) THEN
      CONJ_TAC THEN MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `M:num` THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `~((u':num->num) M = k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `hj_line k M (hj_take M u) /\ hj_line k M (hj_take M u')`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!v. hj_line k M v
                      ==> hj_line k n1 (hj_subst k Y (hj_subst k z2 v))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HJ_LINE_SUBST THEN
      EXISTS_TAC `Ni:num` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC `M:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:num->num) M < k /\ (u':num->num) M < k`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(u:num->num) M <= k`; `(u':num->num) M <= k`;
        `~((u:num->num) M = k)`; `~((u':num->num) M = k)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`hj_take M (u:num->num)`;
                                  `hj_take M (u':num->num)`] o
      check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
                       can (find_term ((=) `r:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HJ_PAIR_DECODE o
      (fun th -> CONJ
         (SPEC `hj_concat n1 (hj_subst k Y (hj_subst k z2 (hj_take M u))) x`
                        (ASSUME `!x. (c:(num->num)->num) x < r`))
                  (CONJ (SPEC
                           `hj_concat n1
                              (hj_subst k Y (hj_subst k z2 (hj_take M u'))) x`
                        (ASSUME `!x. (c:(num->num)->num) x < r`)) th))) THEN
    SIMP_TAC[]]);;

let GRAHAM_ROTHSCHILD_LINES = prove
 (`!k m r. 1 <= k /\ 1 <= r
           ==> ?N. !n c. N <= n /\ (!x. c x < r)
                         ==> ?z. hj_subspace k m n z /\
                                 !u v. hj_line k m u /\ hj_line k m v
                                       ==> c(hj_subst k z u) =
                                           c(hj_subst k z v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `r:num`] FOLKMAN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "fk")) THEN
  MP_TAC(SPECL [`k:num`; `M:num`; `r:num`] HJ_LETTER_INDEP) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:(num->num)->num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `c:(num->num)->num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num->num` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "fk" (MP_TAC o SPECL
   [`M:num`; `\w. (c:(num->num)->num)(hj_subst k z (hj_wlift k w))`]) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  EXISTS_TAC `hj_subst k z (hj_dlift k d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `M:num` THEN
    ASM_SIMP_TAC[HJ_SUBSPACE_DLIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. hj_line k m u
        ==> (c:(num->num)->num)(hj_subst k (hj_subst k z (hj_dlift k d)) u) =
            c(hj_subst k z (hj_wlift k (hj_subst 1 d (hj_wildcards k u))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HJ_SUBST_SUBST] THEN
    SUBGOAL_THEN `hj_line 1 M (hj_subst 1 d (hj_wildcards k u))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[HJ_WILDCARDS_LINE; LE_REFL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> can (find_term ((=) `hj_wildcards`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[HJ_SUBSPACE_DLIFT];
      ASM_SIMP_TAC[HJ_WLIFT_LINE];
      ASM_SIMP_TAC[HJ_WILDCARDS_DLIFT] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC HJ_WILDCARDS_WLIFT THEN EXISTS_TAC `M:num` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`1`; `M:num`; `hj_subst 1 d (hj_wildcards k u)`]
               HJ_LINE_CUBE) THEN
      ASM_REWRITE_TAC[ARITH]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[HJ_WILDCARDS_LINE]);;

(* ========================================================================= *)
(* Tools for the density Hales-Jewett theorem (DKT Section 3).               *)
(* density_hales_jewett k: for every delta > 0 and n large, every A with     *)
(* hj_density k n A >= delta contains a combinatorial line.                  *)
(*                                                                           *)
(* * MULTIDIM_DENSITY_HALES_JEWETT (DKT Proposition 3):                      *)
(*   density_hales_jewett k gives, for every m, an m-dimensional subspace    *)
(*   inside every dense set.  Induction on m: the sections of A over a       *)
(*   dense set of prefixes contain lines by density_hales_jewett k,          *)
(*   pigeonhole over the lines fixes one of them (HJ_DENSITY_PIGEONHOLE),    *)
(*   and the induction hypothesis is applied to those prefixes.              *)
(* * DKT_LEMMA4: for every m and e > 0 and n large, there is an m-variable   *)
(*   word z of some length l < n such that all the sections                  *)
(*   {y | hj_concat l (hj_subst k z a) y IN A} have density at least         *)
(*   hj_density A - e (by iterating DKT_UNIFORM_STEP; FMEAN_SPREAD: a        *)
(*   point far below the mean forces a point above it).                      *)
(* * DKT_COR5: density_hales_jewett k gives m-dimensional subspaces of       *)
(*   [k + 1]^n whose points with letters < k all lie in A.                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The density Hales-Jewett property; pigeonhole for densities.              *)
(* ------------------------------------------------------------------------- *)

let density_hales_jewett = new_definition
 `density_hales_jewett k <=> !delta. &0 < delta
                    ==> ?N. !n A. N <= n /\ delta <= hj_density k n A
                                  ==> hj_has_line k n A`;;

let HJ_DENSITY_POS_EXISTS = prove
 (`!k n A. &0 < hj_density k n A ==> ?x. x IN hj_cube k n /\ x IN A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_DENSITY_CARD] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x | x IN hj_cube k n /\ x IN A} = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES; real_div; REAL_MUL_LZERO]] THEN
  REAL_ARITH_TAC);;

let FINITE_HJ_LINES = prove
 (`!k n. FINITE {l | hj_line k n l} /\
         CARD {l | hj_line k n l} <= (k + 1) EXP n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{l | hj_line k n l} SUBSET hj_cube (k + 1) n` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; HJ_LINE_CUBE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_HJ_CUBE];
    REWRITE_TAC[GSYM CARD_HJ_CUBE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_HJ_CUBE]]);;

let HJ_LINES_NONEMPTY = prove
 (`!k n. 1 <= n ==> ~({l | hj_line k n l} = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `\i:num. if i < n then k else 0` THEN
  REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[] THEN ARITH_TAC;
    SIMP_TAC[GSYM NOT_LT];
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let HJ_DENSITY_PIGEONHOLE = prove
 (`!k l B (g:(num->num)->A) S.
        FINITE S /\ ~(S = {}) /\ (!x. x IN hj_cube k l /\ x IN B ==> g x IN S)
        ==> ?s. s IN S /\
                hj_density k l B <= &(CARD S) *
                hj_density k l {x | x IN B /\ g x = s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:(num->num)->A`; `{x | x IN hj_cube k l /\ x IN B}`;
                 `S:A->bool`] CARD_PIGEONHOLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `hj_cube k l` THEN REWRITE_TAC[FINITE_HJ_CUBE] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HJ_DENSITY_CARD] THEN
  SUBGOAL_THEN
   `{x | x IN hj_cube k l /\ x IN {x | x IN B /\ (g:(num->num)->A) x = s}} =
    {x | x IN {x | x IN hj_cube k l /\ x IN B} /\ g x = s}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* Multidimensional density Hales-Jewett (DKT Proposition 3).                *)
(* ------------------------------------------------------------------------- *)

let MULTIDIM_DENSITY_HALES_JEWETT = prove
 (`!k. 1 <= k /\ density_hales_jewett k
       ==> !m delta.
             &0 < delta
             ==> ?N. !n A. N <= n /\ delta <= hj_density k n A
                           ==> ?z. hj_subspace k m n z /\
                                   !a. a IN hj_cube k m
                                       ==> hj_subst k z a IN A`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `n:num`;
      `A:(num->num)->bool`] HJ_DENSITY_POS_EXISTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:num->num` THEN
    ASM_REWRITE_TAC[HJ_SUBSPACE_0; HJ_CUBE_0; IN_SING] THEN
    X_GEN_TAC `a:num->num` THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:num`; `n:num`; `x:num->num`; `\i:num. 0`]
      HJ_SUBST_WORD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `delta / &2`
         (REWRITE_RULE[density_hales_jewett]
            (ASSUME `density_hales_jewett k`))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "density_hales_jewett")) THEN
  ABBREV_TAC `M = N0 + 1` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `delta / &2 / &((k + 1) EXP M)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nm:num` (LABEL_TAC "ih")) THEN
  EXISTS_TAC `Nm + M:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`] THEN STRIP_TAC THEN
  ABBREV_TAC `l = n - M:num` THEN
  SUBGOAL_THEN `n = l + M:num` SUBST_ALL_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
    `B = {x | delta / &2 <= hj_density k M {y | hj_concat l x y IN A}}` THEN
  SUBGOAL_THEN `delta / &2 <= hj_density k l B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(ISPECL [`k:num`; `l:num`;
                   `\x. hj_density k M {y | hj_concat l x y IN A}`;
                   `delta:real`; `delta / &2`] HJ_DENSITY_MARKOV) THEN
    ASM_REWRITE_TAC[HJ_DENSITY_LE_1; GSYM HJ_DENSITY_SECTIONS] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN B ==> hj_has_line k M {y | hj_concat l x y IN A}`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "density_hales_jewett" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "M" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `lx = \x. @l'. hj_line k M l' /\
                  !a. a < k
                      ==> hj_line_point k l' a IN
                            {y | hj_concat l x y IN A}` THEN
  SUBGOAL_THEN
   `!x. x IN B ==> hj_line k M (lx x) /\
                   !a. a < k ==> hj_concat l x (hj_line_point k (lx x) a) IN A`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num->num`) THEN
    ASM_REWRITE_TAC[hj_has_line] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN EXPAND_TAC "lx" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `l:num`; `B:(num->num)->bool`;
                 `lx:(num->num)->(num->num)`; `{l' | hj_line k M l'}`]
    HJ_DENSITY_PIGEONHOLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_HJ_LINES; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[HJ_LINES_NONEMPTY] THEN
    EXPAND_TAC "M" THEN SIMP_TAC[HJ_LINES_NONEMPTY; ARITH_RULE `1 <= N + 1`];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:num->num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `C = {x | x IN B /\ (lx:(num->num)->(num->num)) x = l0}` THEN
  SUBGOAL_THEN `delta / &2 / &((k + 1) EXP M) <= hj_density k l C`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `M:num`] FINITE_HJ_LINES) THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &(CARD {l' | hj_line k M l'})` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
      ASM_MESON_TAC[CARD_EQ_0; HJ_LINES_NONEMPTY; ARITH_RULE `1 <= N + 1`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `delta / &2 / &(CARD {l' | hj_line k M l'})` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!a b c d:real. a <= b /\ b <= c * d ==> a <= d * c`) THEN
      EXISTS_TAC `hj_density k l B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`l:num`; `C:(num->num)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hj_join k l m w l0` THEN CONJ_TAC THENL
   [REWRITE_TAC[ADD1] THEN MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
    ASM_REWRITE_TAC[GSYM hj_line];
    ALL_TAC] THEN
  X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[HJ_SUBST_JOIN] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HJ_SUBST_LINE th]) THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `l:num`; `w:num->num`; `a:num->num`]
    HJ_SUBST_TAKE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[hj_drop; ADD_CLAUSES] THEN
  SUBGOAL_THEN `hj_subst k w (hj_take m a) IN C` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[GSYM ADD1];
    ALL_TAC] THEN
  EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hj_subst k w (hj_take m a)` o
    check (fun th -> can (find_term ((=) `lx:(num->num)->(num->num)`))
                         (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `(a:num->num) IN hj_cube k (SUC m)` THEN
  REWRITE_TAC[IN_HJ_CUBE] THEN MESON_TAC[LT]);;

(* ------------------------------------------------------------------------- *)
(* Uniform subspaces (DKT Lemma 4).                                          *)
(* ------------------------------------------------------------------------- *)

let HJ_CONCAT_ASSOC = prove
 (`!L m x a y. hj_concat L x (hj_concat m a y) =
               hj_concat (L + m) (hj_concat L x a) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_concat; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i:num < L` THEN
    ASM_SIMP_TAC[ARITH_RULE `i < L ==> i < L + m:num`] THEN
  ASM_CASES_TAC `i:num < L + m` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    COND_CASES_TAC THENL [ASM_ARITH_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC]]);;

let HJ_CONCAT_0 = prove
 (`!x y. hj_concat 0 x y = y`,
  REWRITE_TAC[hj_concat; LT; SUB_0; ETA_AX]);;

let FMEAN_SPREAD = prove
 (`!(X:A->bool) f mu e y0.
        FINITE X /\ y0 IN X /\ 2 <= CARD X /\ mu <= fmean X f /\
        f y0 < mu - e /\ &0 <= e
        ==> ?y1. y1 IN X /\ mu + e / (&(CARD X) - &1) <= f y1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 < &(CARD(X:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mu * &(CARD(X:A->bool)) <= sum X f` ASSUME_TAC THENL
   [UNDISCH_TAC `mu <= fmean (X:A->bool) f` THEN
    REWRITE_TAC[fmean] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 < x ==> &0 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (X DELETE (y0:A)) f = sum X f - f y0 /\
    CARD(X DELETE (y0:A)) = CARD X - 1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUM_DELETE; CARD_DELETE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X DELETE (y0:A)`; `f:A->real`;
                 `mu + e / (&(CARD(X:A->bool)) - &1)`] FMEAN_EXISTS_GE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM HAS_SIZE_0] THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_CARD) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[fmean] THEN
    SUBGOAL_THEN `&(CARD(X:A->bool) - 1) = &(CARD X) - &1` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `2 <= n ==> 1 <= n`];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &(CARD(X:A->bool)) - &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!m s c f0 e. m * c <= s /\ f0 < m - e
                   ==> m * (c - &1) + e <= s - f0`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[IN_DELETE]);;

let HJ_SECTION_CONCAT = prove
 (`!L m x a A. {y | hj_concat m a y IN {y | hj_concat L x y IN A}} =
               {y | hj_concat (L + m) (hj_concat L x a) y IN A}`,
  REWRITE_TAC[IN_ELIM_THM; HJ_CONCAT_ASSOC]);;

let HJ_SUBSPACE_JOIN_POINT = prove
 (`!k m L x. 1 <= k /\ x IN hj_cube k L
             ==> hj_subspace k m (L + m) (hj_join k L 0 x (hj_identity k m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `L:num`; `0`; `m:num`; `m:num`; `x:num->num`;
                 `hj_identity k m`] HJ_SUBSPACE_JOIN) THEN
  ASM_SIMP_TAC[HJ_SUBSPACE_0; HJ_SUBSPACE_IDENTITY; ADD_CLAUSES]);;

let HJ_SUBST_JOIN_POINT = prove
 (`!k m L x a. 1 <= k /\ x IN hj_cube k L /\ a IN hj_cube k m
               ==> hj_subst k (hj_join k L 0 x (hj_identity k m)) a =
                   hj_concat L x a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HJ_SUBST_JOIN] THEN
  SUBGOAL_THEN `hj_drop 0 (a:num->num) = a` SUBST1_TAC THENL
   [REWRITE_TAC[hj_drop; ADD_CLAUSES; ETA_AX]; ALL_TAC] THEN
  ASM_MESON_TAC[HJ_SUBST_WORD; HJ_SUBST_IDENTITY]);;

let DKT_UNIFORM_STEP = prove
 (`!k m n L x A e.
        2 <= k /\ 1 <= m /\ L + m <= n /\ x IN hj_cube k L /\ &0 <= e /\
        hj_density k n A <= hj_density k (n - L) {y | hj_concat L x y IN A}
        ==> (!a. a IN hj_cube k m
                 ==> hj_density k n A - e <=
                     hj_density k (n - (L + m))
                          {y | hj_concat (L + m) (hj_concat L x a) y IN A}) \/
            (?a. a IN hj_cube k m /\
                 hj_density k (n - L) {y | hj_concat L x y IN A} +
                 e / (&(k EXP m) - &1) <=
                 hj_density k (n - (L + m))
                      {y | hj_concat (L + m) (hj_concat L x a) y IN A})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `mu = hj_density k (n - L) {y | hj_concat L x y IN A}` THEN
  SUBGOAL_THEN
   `mu = fmean (hj_cube k m)
          (\a. hj_density k (n - (L + m))
                 {y | hj_concat (L + m) (hj_concat L x a) y IN A})`
  ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN
    SUBGOAL_THEN `n - L = m + (n - (L + m)):num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[HJ_DENSITY_SECTIONS; HJ_SECTION_CONCAT]];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!a. a IN hj_cube k m
        ==> hj_density k n A - e <=
            hj_density k (n - (L + m))
              {y | hj_concat (L + m) (hj_concat L x a) y IN A}` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP;
    REAL_NOT_LE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`hj_cube k m`;
    `\a. hj_density k (n - (L + m))
           {y | hj_concat (L + m) (hj_concat L x a) y IN A}`;
    `mu:real`; `e:real`; `a0:num->num`] FMEAN_SPREAD) THEN
  ASM_REWRITE_TAC[FINITE_HJ_CUBE; CARD_HJ_CUBE; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k EXP 1` THEN
      ASM_REWRITE_TAC[EXP_1; LE_EXP] THEN ASM_ARITH_TAC;
      BETA_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `!x y z e. x < y - e /\ y <= z ==> x < z - e`) THEN
      EXISTS_TAC `hj_density k n A` THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `hj_density k n A <= mu` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[REAL_OF_NUM_POW]]);;

let DKT_LEMMA4 = prove
 (`!k m e. 2 <= k /\ 1 <= m /\ &0 < e
           ==> ?N. !n A. N <= n
                         ==> ?l z. l < n /\ hj_subspace k m l z /\
                                   !a. a IN hj_cube k m
                                       ==> hj_density k n A - e <=
                                           hj_density k (n - l)
                                                {y | hj_concat l (hj_subst k
                                                  z a) y IN A}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho = e / (&(k EXP m) - &1)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&2 <= x ==> &0 < x - &1`) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `k EXP 1` THEN ASM_REWRITE_TAC[EXP_1; LE_EXP] THEN
      ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_CHOOSE_TAC `NT:num` (SPEC `inv(rho:real)` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `(NT + 1) * m + 1` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. t * m <= n
        ==> (?l z. l <= t * m /\ hj_subspace k m l z /\
                   !a. a IN hj_cube k m
                       ==> hj_density k n A - e <=
                           hj_density k (n - l)
                             {y | hj_concat l (hj_subst k z a) y IN A}) \/
            (?x. x IN hj_cube k (t * m) /\
                 hj_density k n A + &t * rho <=
                 hj_density k (n - t * m) {y | hj_concat (t * m) x y IN A})`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `(\i. 0):num->num` THEN
      REWRITE_TAC[MULT_CLAUSES; HJ_CUBE_0; IN_SING; HJ_CONCAT_0; SUB_0] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID;
        SET_RULE `!A:(num->num)->bool. {y | y IN A} = A`;
                  REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `SUC t * m <= n` THEN REWRITE_TAC[MULT_CLAUSES] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`l:num`; `z:num->num`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l <= t * m:num` THEN
      REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `n:num`; `t * m:num`; `x:num->num`;
                   `A:(num->num)->bool`; `e:real`] DKT_UNIFORM_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `SUC t * m <= n` THEN REWRITE_TAC[MULT_CLAUSES] THEN
        ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `!a b c. &0 <= b /\ a + b <= c ==> a <= c`) THEN
        EXISTS_TAC `&t * (rho:real)` THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS;
                                                 REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC t * m = t * m + m`] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`t * m + m:num`;
        `hj_join k (t * m) 0 x (hj_identity k m)`] THEN
      REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_SUBSPACE_JOIN_POINT THEN ASM_REWRITE_TAC[] THEN
         ASM_ARITH_TAC;
        X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`k:num`; `m:num`; `t * m:num`; `x:num->num`;
                       `a:num->num`] HJ_SUBST_JOIN_POINT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
      DISJ2_TAC THEN EXISTS_TAC `hj_concat (t * m) x a` THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_CONCAT_CUBE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!d0 s1 s2 tr r. d0 + tr <= s1 /\ s1 + r <= s2
                        ==> d0 + (tr + r) <= s2`) THEN
      EXISTS_TAC
        `hj_density k (n - t * m) {y | hj_concat (t * m) x y IN A}` THEN
      EXPAND_TAC "rho" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `NT + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l:num`; `z:num->num`] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &NT * (rho:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(rho:real) * rho` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `rho:real`))
                                               (concl th) &&
                                          is_binary "real_le" (concl th) &&
                                          can (find_term ((=) `x:num->num`))
                                               (concl th))) THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c. &0 <= a /\ b <= &1 /\ &1 < c ==> ~(a + c <= b)`) THEN
  REWRITE_TAC[HJ_DENSITY_POS; HJ_DENSITY_LE_1] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Subspaces with all small points in A (DKT Corollary 5).                   *)
(* ------------------------------------------------------------------------- *)

let FMEAN_SWAP2 = prove
 (`!(X:A->bool) (Y:B->bool) f.
        FINITE X /\ FINITE Y
        ==> fmean X (\x. fmean Y (\y. f x y)) =
            fmean Y (\y. fmean X (\x. f x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; real_div; SUM_RMUL] THEN
  MATCH_MP_TAC(REAL_RING
   `!S S' a b:real. S = S' ==> (S * a) * b = (S' * b) * a`) THEN
  MP_TAC(ISPECL [`f:A->B->real`; `X:A->bool`; `Y:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX]);;

let HJ_CUBE_MONO_IN = prove
 (`!k k' n x. k <= k' /\ x IN hj_cube k n ==> x IN hj_cube k' n`,
  MESON_TAC[HJ_CUBE_MONO; SUBSET]);;

let DKT_COR5 = prove
 (`!k. 1 <= k /\ density_hales_jewett k
       ==> !m delta.
             1 <= m /\ &0 < delta
             ==> ?N. !n A. N <= n /\ delta <= hj_density (k + 1) n A
                           ==> ?z. hj_subspace (k + 1) m n z /\
                                   !a. a IN hj_cube k m
                                       ==> hj_subst (k + 1) z a IN A`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` MULTIDIM_DENSITY_HALES_JEWETT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `delta / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:num` (LABEL_TAC "mdhj")) THEN
  MP_TAC(SPECL [`k + 1`; `M0 + 1`; `delta / &2`] DKT_LEMMA4) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:(num->num)->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `w:num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?y0. y0 IN hj_cube (k + 1) (n - l) /\
         delta / &2 <=
         hj_density k (M0 + 1)
           {b | hj_concat l (hj_subst (k + 1) w b) y0 IN A}`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC FMEAN_EXISTS_GE THEN
    REWRITE_TAC[FINITE_HJ_CUBE] THEN
    ASM_SIMP_TAC[HJ_CUBE_NONEMPTY; ARITH_RULE `1 <= k ==> 1 <= k + 1`] THEN
    REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`hj_cube k (M0 + 1)`; `hj_cube (k + 1) (n - l)`;
      `\b y. if hj_concat l (hj_subst (k + 1) w b) y IN A then &1 else &0`]
     FMEAN_SWAP2)) THEN
    REWRITE_TAC[FINITE_HJ_CUBE] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fmean (hj_cube k (M0 + 1)) (\b. delta / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FMEAN_CONST THEN
      ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY];
      ALL_TAC] THEN
    MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_HJ_CUBE] THEN
    X_GEN_TAC `b:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:num->num`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC HJ_CUBE_MONO_IN THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hj_density (k + 1) n A - delta / &2` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC
       `hj_density (k + 1) n A - delta / &2 <=
        hj_density (k + 1) (n - l)
          {y | hj_concat l (hj_subst (k + 1) w b) y IN A}` THEN
      REWRITE_TAC[hj_density; IN_ELIM_THM]];
    ALL_TAC] THEN
  REMOVE_THEN "mdhj" (MP_TAC o SPECL
   [`M0 + 1`; `{b | hj_concat l (hj_subst (k + 1) w b) y0 IN A}`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `M0 <= M0 + 1`; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hj_join (k + 1) l m (hj_subst (k + 1) w (hj_lift k u)) y0` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `n = l + (n - l):num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV)
     [ARITH_RULE `m = m + 0`] THEN
    MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
    ASM_REWRITE_TAC[HJ_SUBSPACE_0; ARITH_RULE `1 <= k + 1`] THEN
    MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `M0 + 1` THEN
    ASM_SIMP_TAC[HJ_SUBSPACE_LIFT; ARITH_RULE `1 <= k + 1`];
    ALL_TAC] THEN
  X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[HJ_SUBST_JOIN; HJ_SUBST_SUBST; HJ_SUBST_LIFT] THEN
  MP_TAC(ISPECL [`k + 1`; `n - l:num`; `y0:num->num`; `hj_drop m a`]
    HJ_SUBST_WORD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The first half of the density increment (DKT Lemmas 7, 8, 10 and          *)
(* Corollary 11).  The constants come from delta while the reference         *)
(* density rho >= delta is the actual density of A, so that the              *)
(* increment of DKT Proposition 6 is uniform in rho.                         *)
(*                                                                           *)
(* * DKT_LEMMA7: an m-variable word U of length l < n such that all the      *)
(*   sections of A over the points of U have density >= rho - eps, and for   *)
(*   every line u of [k]^m the sections over the k points of u have a        *)
(*   common part of density >= theta (DKT_LEMMA4 and DKT_GOOD_LINE).         *)
(* * DKT_LEMMA8: either a density increment eta^2 / 2 on an m-dimensional    *)
(*   subspace, or a subspace W of density >= rho - 2 eta in which            *)
(*   theta / 2 of the lines of W restricted to [k]^m lie in A.               *)
(* * hj_insensitive q n i j D: D is (i, j)-insensitive, i.e. invariant       *)
(*   under the map hj_replace j i that replaces the letter j by i            *)
(*   (HJ_INSENSITIVE_REPLACE).                                               *)
(* * DKT_LEMMA10: in a line-free A of density >= rho - 2 eta with many       *)
(*   lines below, the set {x | !i. i < k ==> hj_replace k i x IN A} has      *)
(*   density >= theta / 4, and A has density >= rho - 3 eta off it           *)
(*   (HJ_LINE_EXTEND, HJ_LINE_FREE_POINTS).                                  *)
(* * DKT_COR11: for a line-free A of density >= rho there is a subspace W    *)
(*   and (i, k)-insensitive sets D i (i < k) with gamma <= hj_density(D)     *)
(*   and (rho + gamma) hj_density(D) <= hj_density(A restricted to D),       *)
(*   where D is the intersection of the D i (DKT_PARTITION_INCREMENT).       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Good lines (DKT Lemma 7).                                                 *)
(* ------------------------------------------------------------------------- *)

let DKT_GOOD_LINE = prove
 (`!k m0 N0 delta l n' A (g:(num->num)->(num->num)).
        1 <= k /\ N0 <= m0 /\ 1 <= m0 /\ &0 < delta /\
        (!n B. N0 <= n /\ delta / &4 <= hj_density k n B
               ==> hj_has_line k n B) /\
        (!b. b IN hj_cube k m0
             ==> delta / &2 <=
                 hj_density (k + 1) n' {y | hj_concat l (g b) y IN A})
        ==> ?u. hj_line k m0 u /\
                delta / &4 / &((k + 1) EXP m0) <=
                hj_density (k + 1) n'
                     {y | !a. a < k
                              ==> hj_concat l
                                    (g (hj_line_point k u a)) y IN A}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `B = {y | delta / &4 <=
         hj_density k m0 {b | hj_concat l ((g:(num->num)->(num->num))
     b) y IN A}}` THEN
  SUBGOAL_THEN `delta / &4 <= hj_density (k + 1) n' B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(ISPECL [`k + 1`; `n':num`;
                   `\y. hj_density k m0 {b | hj_concat l
                     ((g:(num->num)->(num->num)) b) y IN A}`;
                   `delta / &2`; `delta / &4`] HJ_DENSITY_MARKOV) THEN
    REWRITE_TAC[HJ_DENSITY_LE_1] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
      MP_TAC(BETA_RULE(ISPECL
       [`hj_cube k m0`; `hj_cube (k + 1) n'`;
        `\b y. if hj_concat l ((g:(num->num)->(num->num)) b) y IN A
               then &1 else &0`] FMEAN_SWAP2)) THEN
      REWRITE_TAC[FINITE_HJ_CUBE] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean (hj_cube k m0) (\b. delta / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FMEAN_CONST THEN
          ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY];
        ALL_TAC] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_HJ_CUBE] THEN
      X_GEN_TAC `b:num->num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b:num->num`) THEN
      ASM_REWRITE_TAC[hj_density; IN_ELIM_THM];
      DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `!d x. d / &2 - d / &4 <= x ==> d / &4 <= x`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN B ==> hj_has_line k m0 {b | hj_concat l
     ((g:(num->num)->(num->num)) b) y IN A}`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `ly = \y. @u. hj_line k m0 u /\
                 !a. a < k ==> hj_line_point k u a IN
                     {b | hj_concat l ((g:(num->num)->(num->num)) b)
                        y IN A}` THEN
  SUBGOAL_THEN
   `!y. y IN B ==> hj_line k m0 (ly y) /\
                   !a. a < k ==> hj_concat l ((g:(num->num)->(num->num))
                                          (hj_line_point k (ly y) a)) y IN A`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:num->num`) THEN
    ASM_REWRITE_TAC[hj_has_line] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN EXPAND_TAC "ly" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `n':num`; `B:(num->num)->bool`;
                 `ly:(num->num)->(num->num)`; `{u | hj_line k m0 u}`]
    HJ_DENSITY_PIGEONHOLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_HJ_LINES; HJ_LINES_NONEMPTY; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u0:num->num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`k:num`; `m0:num`] FINITE_HJ_LINES) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(CARD {u | hj_line k m0 u})` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    ASM_MESON_TAC[CARD_EQ_0; HJ_LINES_NONEMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `hj_density (k + 1) n' {y | y IN B /\ ly y = (u0:num->num)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `delta / &4 / &(CARD {u | hj_line k m0 u})` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!a b c d:real. a <= b /\ b <= c * d ==> a <= d * c`) THEN
      EXISTS_TAC `hj_density (k + 1) n' B` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC HJ_DENSITY_MONO THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `y:num->num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:num->num` o
      check (fun th -> can (find_term ((=) `ly:(num->num)->(num->num)`))
                           (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let HJ_SUBSPACE_MONO_LENGTH = prove
 (`!k m n n' z. 1 <= k /\ n <= n' /\ hj_subspace k m n z
                ==> hj_subspace k m n' z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_subspace; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num < n` THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(z:num->num) i = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ASM_ARITH_TAC];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[LTE_TRANS]]);;

let DKT_LEMMA7 = prove
 (`!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta
        ==> ?m0 theta.
              1 <= m0 /\ &0 < theta /\
              !m eps.
                m0 <= m /\ &0 < eps /\ eps <= delta / &2
                ==> ?N. !n A rho.
                      N <= n /\ delta <= rho /\ rho <= hj_density (k + 1) n A
                      ==> ?l U.
                            l < n /\ hj_subspace (k + 1) m l U /\
                            (!a. a IN hj_cube (k + 1) m
                                 ==> rho - eps <=
                                     hj_density (k + 1) (n - l)
                                       {y | hj_concat l (hj_subst (k + 1) U
                                         a) y IN A}) /\
                            (!u. hj_line k m u
                                 ==> theta <=
                                     hj_density (k + 1) (n - l)
                                       {y | !a. a < k
                                                ==> hj_concat l
                                                     (hj_subst (k + 1)
                                                       U (hj_line_point k u a))
                                                     y IN A})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `delta / &4`
         (REWRITE_RULE[density_hales_jewett]
            (ASSUME `density_hales_jewett k`))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "density_hales_jewett")) THEN
  ABBREV_TAC `theta = delta / &4 / &((k + 1) EXP (N0 + 1))` THEN
  MAP_EVERY EXISTS_TAC [`N0 + 1`; `theta:real`] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    EXPAND_TAC "theta" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `2`] GRAHAM_ROTHSCHILD_LINES) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ng:num` (LABEL_TAC "gr")) THEN
  MP_TAC(SPECL [`k + 1`; `Ng + 1`; `eps:real`] DKT_LEMMA4) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`; `rho:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:(num->num)->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `V:num->num`
    STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "gr" (MP_TAC o SPECL
   [`Ng + 1`;
    `\u. if theta <= hj_density (k + 1) (n - l)
                       {y | !a. a < k
                                ==> hj_concat l
                                      (hj_subst (k + 1) V
                                         (hj_line_point k u a)) y
                                    IN A}
         then 1 else 0`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `Ng <= Ng + 1`] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->num` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN `hj_subspace k (N0 + 1) m (hj_identity k (N0 + 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HJ_SUBSPACE_MONO_LENGTH THEN EXISTS_TAC `N0 + 1` THEN
    ASM_SIMP_TAC[HJ_SUBSPACE_IDENTITY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N0 + 1`; `N0:num`; `delta:real`; `l:num`;
                 `n - l:num`; `A:(num->num)->bool`;
                 `\b. hj_subst (k + 1) V
                        (hj_subst k
                           (hj_subst k Y (hj_identity k (N0 + 1))) b)`]
    DKT_GOOD_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `N0 <= N0 + 1 /\ 1 <= N0 + 1`] THEN
    X_GEN_TAC `b:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hj_density (k + 1) n A - eps` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> can (find_term ((=) `V:num->num`)) (concl th) &&
                       is_forall(concl th))) THEN
    MATCH_MP_TAC HJ_SUBST_IN_CUBE THEN EXISTS_TAC `N0 + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `k <= k + 1`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HJ_CUBE_MONO_IN THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:num->num`
   (STRIP_ASSUME_TAC o REWRITE_RULE[HJ_SUBST_SUBST])) THEN
  SUBGOAL_THEN
   `!u. hj_line k m u
        ==> theta <= hj_density (k + 1) (n - l)
                       {y | !a. a < k
                                ==> hj_concat l (hj_subst (k + 1) V
                                             (hj_line_point k (hj_subst k Y u)
                                                a)) y IN A}`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `hj_line k m (hj_subst k (hj_identity k (N0 + 1)) u0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC `N0 + 1` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:num->num`;
                                  `hj_subst k (hj_identity k (N0 + 1)) u0`] o
      check (fun th -> can (find_term ((=) `Y:num->num`)) (concl th) &&
                       is_forall(concl th))) THEN
    ASM_REWRITE_TAC[HJ_LINE_POINT_SUBST; HJ_SUBST_SUBST] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `hj_subst (k + 1) V (hj_lift k Y)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `Ng + 1` THEN
    ASM_SIMP_TAC[HJ_SUBSPACE_LIFT; ARITH_RULE `1 <= k + 1`];
    X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN REWRITE_TAC[HJ_SUBST_SUBST] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hj_density (k + 1) n A - eps` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> can (find_term ((=) `V:num->num`)) (concl th) &&
                       is_forall(concl th) &&
                       not (can (find_term ((=) `Y:num->num`))
                         (concl th)))) THEN
    MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
    ASM_SIMP_TAC[HJ_SUBSPACE_LIFT; ARITH_RULE `1 <= k + 1`];
    X_GEN_TAC `u:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[HJ_SUBST_SUBST; HJ_SUBST_LIFT] THEN
    REWRITE_TAC[GSYM HJ_LINE_POINT_SUBST] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Increment or many lines (DKT Lemma 8).                                    *)
(* ------------------------------------------------------------------------- *)

let FMEAN_REVERSE_MARKOV = prove
 (`!(X:A->bool) f c d t.
        FINITE X /\ ~(X = {}) /\ (!x. x IN X ==> f x <= c) /\
        c - d <= fmean X f /\ t < c
        ==> (c - t) * &(CARD {x | x IN X /\ f x < t}) <= d * &(CARD X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(CARD(X:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c - d) * &(CARD(X:A->bool)) <= sum X f` ASSUME_TAC THENL
   [UNDISCH_TAC `c - d <= fmean (X:A->bool) f` THEN
    ASM_SIMP_TAC[fmean; REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (X:A->bool) f <=
    c * &(CARD X) - (c - t) * &(CARD {x | x IN X /\ f x < t})`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (X:A->bool) (\x. if f x < t then t else c)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CASES] THEN
    SUBGOAL_THEN `FINITE {x:A | x IN X /\ f x < t} /\
                  FINITE {x:A | x IN X /\ ~(f x < t)}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `X:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST] THEN
    SUBGOAL_THEN
     `&(CARD (X:A->bool)) =
      &(CARD {x | x IN X /\ f x < t}) + &(CARD {x | x IN X /\ ~(f x < t)})`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(GSYM CARD_UNION_EQ) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_ACCEPT_TAC(REAL_ARITH
       `!a b c t:real. a * t + b * c <= c * (a + b) - (c - t) * a`)];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `!c d t s a b. (c - d) * a <= s /\ s <= c * a - (c - t) * b
                  ==> (c - t) * b <= d * a`) THEN
  EXISTS_TAC `sum (X:A->bool) f` THEN ASM_REWRITE_TAC[]);;

let HJ_JOIN_POINT_RIGHT = prove
 (`!k m l n2 U y. 1 <= k /\ hj_subspace k m l U /\ y IN hj_cube k n2
                  ==> hj_subspace k m (l + n2) (hj_join k l m U y) /\
                      !a. hj_subst k (hj_join k l m U y) a =
                          hj_concat l (hj_subst k U a) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `l:num`; `m:num`; `0`; `n2:num`; `U:num->num`;
                   `y:num->num`] HJ_SUBSPACE_JOIN) THEN
    ASM_REWRITE_TAC[HJ_SUBSPACE_0; ADD_CLAUSES];
    GEN_TAC THEN REWRITE_TAC[HJ_SUBST_JOIN] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[HJ_SUBST_WORD]]);;

let HJ_DENSITY_COMMON = prove
 (`!k n A B. &1 < hj_density k n A + hj_density k n B
             ==> ?x. x IN hj_cube k n /\ x IN A /\ x IN B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `n:num`; `A INTER B:(num->num)->bool`]
    HJ_DENSITY_POS_EXISTS) THEN
  REWRITE_TAC[IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `hj_density k n A + hj_density k n B <= &1 +
    hj_density k n (A INTER B:(num->num)->bool)`
  MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `k EXP n = 0` THENL
   [ASM_REWRITE_TAC[HJ_DENSITY_CARD; real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[hj_density] THEN
  SUBGOAL_THEN
   `&1 + fmean (hj_cube k n)
           (\x. if x IN A INTER B then &1 else &0) =
    fmean (hj_cube k n) (\x. &1 + (if x IN A INTER B then &1 else &0))`
  SUBST1_TAC THENL
   [SIMP_TAC[FMEAN_ADD; FINITE_HJ_CUBE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FMEAN_CONST THEN
    REWRITE_TAC[FINITE_HJ_CUBE; GSYM HAS_SIZE_0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_CARD) THEN
    ASM_REWRITE_TAC[CARD_HJ_CUBE];
    ALL_TAC] THEN
  SIMP_TAC[GSYM FMEAN_ADD; FINITE_HJ_CUBE] THEN MATCH_MP_TAC FMEAN_LE THEN
  REWRITE_TAC[FINITE_HJ_CUBE; IN_INTER] THEN X_GEN_TAC `x:num->num` THEN
  DISCH_TAC THEN ASM_CASES_TAC `(x:num->num) IN A` THEN
  ASM_CASES_TAC `(x:num->num) IN B` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let HJ_DENSITY_COMPL = prove
 (`!k n P. 1 <= k
           ==> hj_density k n {x | ~P x} = &1 - hj_density k n {x | P x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `a + b = &1 ==> b = &1 - a`) THEN
  SIMP_TAC[GSYM FMEAN_ADD; FINITE_HJ_CUBE] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `fmean (hj_cube k n) (\x. &1)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC FMEAN_CONST THEN
      ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY]]);;

let CARD_RESTRICT_SUM = prove
 (`!(L:A->bool) P. FINITE L
                   ==> &(CARD {u | u IN L /\ P u}) =
                       sum L (\u. if P u then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `FINITE {u:A | u IN L /\ P u}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]]);;

let DKT_ETA_BOUND = prove
 (`!e p. &0 < e /\ &0 <= p /\ (&2 * e + e pow 2 / &2) * p <= e pow 2
         ==> p <= e / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e * (&2 * p) <= e * e` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * e + e pow 2 / &2) * p` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b /\ &0 <= c ==> a <= b + c`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[GSYM REAL_POW_2]];
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]);;

let DKT_LEMMA8 = prove
 (`!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta
        ==> ?m0 theta.
              1 <= m0 /\ &0 < theta /\
              !m eta.
                m0 <= m /\ &0 < eta /\ eta <= &1 /\ eta pow 2 <= delta /\
                eta < theta
                ==> ?N. !n A rho.
                      N <= n /\ delta <= rho /\ rho <= hj_density (k + 1) n A
                      ==> (?X. hj_subspace (k + 1) m n X /\
                               rho + eta pow 2 / &2 <=
                               hj_density (k + 1) m
                                 {a | hj_subst (k + 1) X a IN A}) \/
                          (?W. hj_subspace (k + 1) m n W /\
                               rho - &2 * eta <=
                               hj_density (k + 1) m
                                 {a | hj_subst (k + 1) W a IN A} /\
                               theta / &2 * &(CARD {u | hj_line k m u}) <=
                               &(CARD {u | hj_line k m u /\
                                           !a. a < k
                                               ==> hj_subst (k + 1) W
                                                     (hj_line_point k u a)
                                                   IN A}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DKT_LEMMA7) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m0:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `theta:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `eta:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `(eta:real) pow 2 / &2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      ASM_SIMP_TAC[REAL_POW_LT];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`; `rho:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:(num->num)->bool`;
    `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `U:num->num`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC
   `?X. hj_subspace (k + 1) m n X /\
        rho + eta pow 2 / &2 <= hj_density (k + 1) m {a | hj_subst (k + 1)
          X a IN A}` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM;
                                      REAL_NOT_LE]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!y. y IN hj_cube (k + 1) (n - l)
        ==> hj_subspace (k + 1) m n (hj_join (k + 1) l m U y) /\
            !a. hj_subst (k + 1) (hj_join (k + 1) l m U y) a =
                hj_concat l (hj_subst (k + 1) U a) y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k + 1`; `m:num`; `l:num`; `n - l:num`; `U:num->num`;
                   `y:num->num`] HJ_JOIN_POINT_RIGHT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE `l < n ==> l + (n - l) = n:num`];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = \y. hj_density (k + 1) m
              {a | hj_concat l (hj_subst (k + 1) U a) y IN A}` THEN
  SUBGOAL_THEN
   `!y. y IN hj_cube (k + 1) (n - l) ==>
     (f:(num->num)->real) y < rho + eta pow 2 / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `hj_join (k + 1) l m U y` o
      check (fun th -> can (find_term ((=) `eta:real`)) (concl th) &&
                       is_forall(concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rho - eta pow 2 / &2 <= fmean (hj_cube (k + 1) (n - l)) f`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`hj_cube (k + 1) (n - l)`; `hj_cube (k + 1) m`;
      `\y a. if hj_concat l (hj_subst (k + 1) U a) y IN A then &1 else &0`]
     FMEAN_SWAP2)) THEN
    REWRITE_TAC[FINITE_HJ_CUBE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fmean (hj_cube (k + 1) m) (\a. rho - eta pow 2 / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FMEAN_CONST THEN
      ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY; ARITH_RULE `1 <= k + 1`];
      ALL_TAC] THEN
    MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_HJ_CUBE] THEN
    X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num->num` o
      check (fun th -> can (find_term ((=) `U:num->num`)) (concl th) &&
                       is_forall(concl th) &&
                       not(can (find_term ((=) `hj_line_point`)) (concl th)) &&
                       not(can (find_term ((=) `hj_join`)) (concl th)))) THEN
    ASM_REWRITE_TAC[hj_density; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 - eta / &2 <=
    hj_density (k + 1) (n - l) {y | rho - &2 * eta <= (f:(num->num)->real) y}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hj_cube (k + 1) (n - l)`; `f:(num->num)->real`;
                   `rho + (eta:real) pow 2 / &2`; `(eta:real) pow 2`;
                     `rho - &2 * eta`]
      FMEAN_REVERSE_MARKOV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY; ARITH_RULE `1 <= k + 1`;
                   REAL_LT_IMP_LE] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!r e s. &0 < e /\ &0 <= s ==> r - &2 * e < r + s`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE; REAL_POS];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`k + 1`; `n - l:num`;
                  `\y. rho - &2 * eta <= (f:(num->num)->real) y`]
                    HJ_DENSITY_COMPL) THEN
    REWRITE_TAC[ARITH_RULE `1 <= k + 1`; REAL_NOT_LE] THEN
    DISCH_THEN(fun th -> MP_TAC(SYM th)) THEN
    MATCH_MP_TAC(REAL_ARITH
     `!p q e. p <= e / &2 ==> &1 - q = p ==> &1 - e / &2 <= q`) THEN
    MATCH_MP_TAC DKT_ETA_BOUND THEN REWRITE_TAC[HJ_DENSITY_POS] THEN
    ASM_REWRITE_TAC[HJ_DENSITY_CARD; GSYM CARD_HJ_CUBE] THEN
    SUBGOAL_THEN `&0 < &(CARD(hj_cube (k + 1) (n - l)))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; CARD_HJ_CUBE; EXP_EQ_0]
        THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN
     `{x | x IN hj_cube (k + 1) (n - l) /\
           x IN {x | (f:(num->num)->real) x < rho - &2 * eta}} =
      {x | x IN hj_cube (k + 1) (n - l) /\ f x < rho - &2 * eta}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!r e c w. ((r + e pow 2 / &2) - (r - &2 * e)) * c <= e pow 2 * w
                ==> (&2 * e + e pow 2 / &2) * c <= e pow 2 * w`) THEN
    EXISTS_TAC `rho:real` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(CARD {u | hj_line k m u})` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    MP_TAC(SPECL [`k:num`; `m:num`] FINITE_HJ_LINES) THEN
    MP_TAC(SPECL [`k:num`; `m:num`] HJ_LINES_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[CARD_EQ_0]];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = \y. &(CARD {u | hj_line k m u /\
                       !a. a < k
                           ==> hj_concat l
                                 (hj_subst (k + 1) U
                                    (hj_line_point k u a)) y IN A}) /
            &(CARD {u | hj_line k m u})` THEN
  SUBGOAL_THEN
   `!y. (g:(num->num)->real) y =
        inv(&(CARD {u | hj_line k m u})) *
        sum {u | hj_line k m u}
          (\u. if !a. a < k
                      ==> hj_concat l
                            (hj_subst (k + 1) U (hj_line_point k u a)) y IN A
               then &1 else &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`{u | hj_line k m u}`;
                   `\u. !a. a < k
                        ==> hj_concat l
                              (hj_subst (k + 1) U
                                 (hj_line_point k u a)) y IN A`]
      CARD_RESTRICT_SUM) THEN
    REWRITE_TAC[FINITE_HJ_LINES; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `theta / &2 <= hj_density (k + 1) (n - l) {y | theta / &2 <=
     (g:(num->num)->real) y}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k + 1`; `n - l:num`; `g:(num->num)->real`; `theta:real`;
                   `theta / &2`] HJ_DENSITY_MARKOV) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC CARD_SUBSET THEN
        REWRITE_TAC[FINITE_HJ_LINES] THEN SET_TAC[];
        ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
        ASM_REWRITE_TAC[FMEAN_LMUL] THEN
        SIMP_TAC[FMEAN_SUM; FINITE_HJ_CUBE; FINITE_HJ_LINES] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `inv(&(CARD {u | hj_line k m u})) *
                    sum {u | hj_line k m u} (\u. theta)` THEN CONJ_TAC THENL
         [SIMP_TAC[SUM_CONST; FINITE_HJ_LINES] THEN
          ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                       REAL_MUL_LID; REAL_LE_REFL];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_HJ_LINES; IN_ELIM_THM] THEN
        X_GEN_TAC `u:num->num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `u:num->num` o
          check (fun th -> can (find_term ((=) `hj_line_point`)) (concl th) &&
                           is_forall(concl th) &&
                           can (find_term ((=) `theta:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[hj_density; IN_ELIM_THM]];
      DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `!d x. d - d / &2 <= x ==> d / &2 <= x`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k + 1`; `n - l:num`;
                `{y | rho - &2 * eta <= (f:(num->num)->real) y}`;
                `{y | theta / &2 <= (g:(num->num)->real) y}`]
                  HJ_DENSITY_COMMON) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!a b e t. &1 - e / &2 <= a /\ t / &2 <= b /\ e < t ==> &1 < a + b`) THEN
    MAP_EVERY EXISTS_TAC [`eta:real`; `theta:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hj_join (k + 1) l m U y0` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y0:num->num` o
    check (fun th -> can (find_term ((=) `hj_join`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `rho - &2 * eta <= (f:(num->num)->real) y0` THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[];
    UNDISCH_TAC `theta / &2 <= (g:(num->num)->real) y0` THEN
    EXPAND_TAC "g" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Insensitive sets.                                                         *)
(* ------------------------------------------------------------------------- *)

let hj_replace = new_definition
 `hj_replace j i (x:num->num) = \r. if x r = j then i else x r`;;

let hj_insensitive = new_definition
 `hj_insensitive q n i j (D:(num->num)->bool) <=>
    !x y. x IN hj_cube q n /\ y IN hj_cube q n /\
          hj_replace j i x = hj_replace j i y
          ==> (x IN D <=> y IN D)`;;

let HJ_INSENSITIVE_COMPL = prove
 (`!q n i j D. hj_insensitive q n i j D
               ==> hj_insensitive q n i j {x | ~(x IN D)}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN MESON_TAC[]);;

let HJ_INSENSITIVE_UNIV = prove
 (`!q n i j. hj_insensitive q n i j {x | T}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM]);;

let HJ_INSENSITIVE_REPLACE = prove
 (`!q n i j A. hj_insensitive q n i j {x | hj_replace j i x IN A}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN MESON_TAC[]);;

let HJ_REPLACE_WORD = prove
 (`!k m x i. 1 <= k /\ x IN hj_cube k m ==> hj_replace k i x = x`,
  REWRITE_TAC[IN_HJ_CUBE; hj_replace; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `x':num < m` THENL
   [SUBGOAL_THEN `(x:num->num) x' < k` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    SUBGOAL_THEN `(x:num->num) x' = 0` MP_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ASM_ARITH_TAC]]);;

let HJ_REPLACE_LINE = prove
 (`!k m u i. hj_line k m u ==> hj_replace k i u = hj_line_point k u i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REWRITE_TAC[hj_replace; hj_line_point; hj_subst; FUN_EQ_THM] THEN
  X_GEN_TAC `r:num` THEN
  ASM_CASES_TAC `(u:num->num) r = k` THEN
  ASM_REWRITE_TAC[LT_REFL; SUB_REFL] THEN
  ASM_CASES_TAC `r:num < m` THENL
   [SUBGOAL_THEN `(u:num->num) r < k + 1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    SUBGOAL_THEN `(u:num->num) r = 0` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let HJ_CUBE_SUC_CASES = prove
 (`!k m x. x IN hj_cube (k + 1) m ==> x IN hj_cube k m \/ hj_line k m x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?i. i < m /\ (x:num->num) i = k` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:num->num) IN hj_cube (k + 1) m` THEN
  REWRITE_TAC[IN_HJ_CUBE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:num->num) i < k + 1 /\ ~(x i = k)` MP_TAC THENL
   [ASM_MESON_TAC[]; ARITH_TAC]);;

let HJ_LINE_NOT_WORD = prove
 (`!k m x. hj_line k m x ==> ~(x IN hj_cube k m)`,
  REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE] THEN MESON_TAC[LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Line-free sets with many lines below (DKT Lemma 10).                      *)
(* ------------------------------------------------------------------------- *)

let HJ_LINES_EQ_DIFF = prove
 (`!k m. 1 <= k ==> {u | hj_line k m u} = hj_cube (k + 1) m DIFF hj_cube k m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num->num` THEN EQ_TAC THENL
   [MESON_TAC[HJ_LINE_CUBE; HJ_LINE_NOT_WORD];
    MESON_TAC[HJ_CUBE_SUC_CASES]]);;

let CARD_HJ_LINES = prove
 (`!k m. 1 <= k ==> CARD {u | hj_line k m u} = (k + 1) EXP m - k EXP m`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HJ_LINES_EQ_DIFF] THEN
  SIMP_TAC[CARD_DIFF; FINITE_HJ_CUBE; HJ_CUBE_MONO;
           ARITH_RULE `k <= k + 1`] THEN
  REWRITE_TAC[CARD_HJ_CUBE]);;

let HJ_LINE_EXTEND = prove
 (`!k m u. 1 <= k /\ hj_line k m u
           ==> hj_line (k + 1) m (\r. if u r = k then k + 1 else u r) /\
               !a. hj_line_point (k + 1)
                     (\r. if u r = k then k + 1 else u r) a =
                   hj_replace k a u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_LINE_EQ; IN_HJ_CUBE] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(u:num->num) r < k + 1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ARITH_TAC];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:num->num) r = 0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `a:num` THEN
    REWRITE_TAC[hj_line_point; hj_subst; hj_replace; FUN_EQ_THM] THEN
    X_GEN_TAC `r:num` THEN ASM_CASES_TAC `(u:num->num) r = k` THEN
    ASM_REWRITE_TAC[LT_REFL; SUB_REFL] THEN
    SUBGOAL_THEN `(u:num->num) r < k + 1` (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `r:num < m` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(u:num->num) r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[NOT_LT]; ARITH_TAC]]);;

let HJ_LINE_FREE_POINTS = prove
 (`!k m A x.
        1 <= k /\ ~hj_has_line (k + 1) m A /\
        x IN hj_cube (k + 1) m /\ x IN A /\
        (!i. i < k ==> hj_replace k i x IN A)
        ==> x IN hj_cube k m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP HJ_CUBE_SUC_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[hj_has_line] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  EXISTS_TAC `\r. if (x:num->num) r = k then k + 1 else x r` THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `x:num->num`] HJ_LINE_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN ASM_CASES_TAC `a:num < k` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `a = k:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `hj_replace k k (x:num->num) = x`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[hj_replace; FUN_EQ_THM] THEN MESON_TAC[]);;

let HJ_DENSITY_SMALL_CUBE = prove
 (`!k m. hj_density (k + 1) m (hj_cube k m) = &(k EXP m) / &((k + 1) EXP m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HJ_DENSITY_CARD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM CARD_HJ_CUBE] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`k:num`; `k + 1`; `m:num`] HJ_CUBE_MONO) THEN
  REWRITE_TAC[ARITH_RULE `k <= k + 1`] THEN SET_TAC[]);;

let DKT_POW_RATIO_SMALL = prove
 (`!k e. 1 <= k /\ &0 < e
         ==> ?M0. !m. M0 <= m ==> &(k EXP m) / &((k + 1) EXP m) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&k / &(k + 1)`; `e:real`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < k + 1`] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M0:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_POW_DIV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&k / &(k + 1)) pow M0` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < k + 1`] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN ARITH_TAC);;

let DKT_PARTITION_SUM = prove
 (`!k (P:num->bool).
        sum {i | i < k}
            (\i. if ~P i /\ (!j. j < i ==> P j) then &1 else &0) =
        if ?i. i < k /\ ~P i then &1 else &0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[MINIMAL]) THEN
    ABBREV_TAC `i0 = minimal i. i < k /\ ~(P:num->bool) i` THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {i:num | i < k} (\i. if i = i0 then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(~(P:num->bool) i /\ (!j. j < i ==> P j)) <=> i = i0`
       (fun th -> REWRITE_TAC[th]) THEN
      EQ_TAC THENL
       [STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
        ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[LT_TRANS]];
      REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

let HJ_DENSITY_PARTITION = prove
 (`!q n k S (C:num->(num->num)->bool).
        sum {i | i < k}
            (\i. hj_density q n {x | x IN S /\ ~(x IN C i) /\
                               !j. j < i ==> x IN C j}) =
        hj_density q n {x | x IN S /\ ?i. i < k /\ ~(x IN C i)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
  SIMP_TAC[GSYM FMEAN_SUM; FINITE_HJ_CUBE; FINITE_NUMSEG_LT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num->num` THEN
  ASM_CASES_TAC `(x:num->num) IN S` THEN ASM_REWRITE_TAC[SUM_0] THEN
  MP_TAC(SPECL [`k:num`; `\i:num. (x:num->num) IN (C:num->(num->num)->bool)
    i`] DKT_PARTITION_SUM) THEN
  REWRITE_TAC[]);;

let DKT_PARTITION_INCREMENT = prove
 (`!k q n (C:num->(num->num)->bool) A rho eta.
        1 <= k /\ &0 < eta /\ &0 <= rho /\
        (rho + &6 * eta) * hj_density q n {x | x IN hj_cube q n /\ ?i. i < k /\
          ~(x IN C i)} <=
        hj_density q n {x | x IN A /\ ?i. i < k /\ ~(x IN C i)}
        ==> ?i0. i0 < k /\
                 &3 * eta / &k *
                 hj_density q n
                   {x | x IN hj_cube q n /\ ?i. i < k /\ ~(x IN C i)} <=
                 hj_density q n {x | x IN hj_cube q n /\ ~(x IN C i0) /\
                               !j. j < i0 ==> x IN C j} /\
                 (rho + &3 * eta) *
                 hj_density q n {x | x IN hj_cube q n /\ ~(x IN C i0) /\
                               !j. j < i0 ==> x IN C j} <=
                 hj_density q n {x | x IN A /\ ~(x IN C i0) /\
                               !j. j < i0 ==> x IN C j}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = hj_density q n {x | x IN hj_cube q n /\ ?i. i < k /\
    ~(x IN (C:num->(num->num)->bool) i)}` THEN
  ABBREV_TAC `p = \i. hj_density q n {x | x IN hj_cube q n /\
    ~(x IN (C:num->(num->num)->bool) i) /\
                                    !j. j < i ==> x IN C j}` THEN
  ABBREV_TAC `a = \i. hj_density q n {x | x IN A /\
    ~(x IN (C:num->(num->num)->bool) i) /\
                                    !j. j < i ==> x IN C j}` THEN
  SUBGOAL_THEN `sum {i:num | i < k} p = d /\
                sum {i:num | i < k} a =
                hj_density q n {x | x IN A /\ ?i. i < k /\
                  ~(x IN (C:num->(num->num)->bool) i)}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "a"; "d"] THEN
    REWRITE_TAC[HJ_DENSITY_PARTITION];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (a:num->real) i <= p i` ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["a"; "p"] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HJ_DENSITY_MONO THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i0. i0 < k /\ &3 * eta / &k * d <= (p:num->real) i0 /\
         (rho + &3 * eta) * p i0 <= (a:num->real) i0`
  MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["p"; "a"] THEN REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE
   [NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`;
    REAL_NOT_LE]) THEN
  SUBGOAL_THEN `!i. &0 <= (p:num->real) i` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[HJ_DENSITY_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [UNDISCH_TAC `sum {i:num | i < k} p = d` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * eta / &k * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> (a:num->real) i < (rho + &3 * eta) * p i + &3 * eta / &k * d`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (rho + &3 * eta) * (p:num->real) i` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `i:num` (ASSUME `!i. (a:num->real) i <= p i`)) THEN
    ASM_CASES_TAC `&3 * eta / &k * d <= (p:num->real) i` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `rho:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num->real`;
                 `\i. (rho + &3 * eta) * (p:num->real) i + &3 * eta / &k * d`;
                 `{i:num | i < k}`] SUM_LT_ALL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `(rho + &6 * eta) * d <=
    hj_density q n {x | x IN A /\ ?i. i < k /\
                            ~(x IN (C:num->(num->num)->bool) i)}` THEN
  MATCH_MP_TAC(REAL_ARITH
   `!X r e d t. t = &3 * e * d
                ==> (r + &6 * e) * d <= X ==>
                  ~(X < (r + &3 * e) * d + t)`) THEN
  UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  CONV_TAC REAL_FIELD);;

let DKT_LEMMA10 = prove
 (`!k m A theta eta rho.
        1 <= k /\ ~hj_has_line (k + 1) m A /\ &0 < eta /\ eta <= &1 / &2 /\
        &(k EXP m) / &((k + 1) EXP m) <= eta /\ &0 <= theta /\
        rho - &2 * eta <= hj_density (k + 1) m A /\
        theta / &2 * &(CARD {u | hj_line k m u}) <=
        &(CARD {u | hj_line k m u /\ !a. a < k ==> hj_line_point k u a IN A})
        ==> theta / &4 <=
            hj_density (k + 1) m {x | x IN hj_cube (k + 1) m /\
                                !i. i < k ==> hj_replace k i x IN A} /\
            rho - &3 * eta <=
            hj_density (k + 1) m
              {x | x IN A /\ ?i. i < k /\ ~(hj_replace k i x IN A)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `C = {x | x IN hj_cube (k + 1) m /\ !i. i < k ==>
    hj_replace k i x IN A}` THEN
  SUBGOAL_THEN
   `{u | hj_line k m u /\ !a. a < k ==> hj_line_point k u a IN A} SUBSET C`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[HJ_LINE_CUBE; HJ_REPLACE_LINE];
    ALL_TAC] THEN
  SUBGOAL_THEN `C SUBSET hj_cube (k + 1) m` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[HJ_DENSITY_CARD] THEN
    SUBGOAL_THEN `{x | x IN hj_cube (k + 1) m /\ x IN C} = C` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &((k + 1) EXP m)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `&(CARD {u | hj_line k m u /\
               !a. a < k ==> hj_line_point k u a IN A})` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_MESON_TAC[FINITE_SUBSET; FINITE_HJ_CUBE]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `theta / &2 * &(CARD {u | hj_line k m u})` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    ASM_SIMP_TAC[CARD_HJ_LINES] THEN
    SUBGOAL_THEN `k EXP m <= (k + 1) EXP m` ASSUME_TAC THENL
     [REWRITE_TAC[EXP_MONO_LE] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    SUBGOAL_THEN `&(k EXP m) <= &((k + 1) EXP m) / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta * &((k + 1) EXP m)` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `&(k EXP m) / &((k + 1) EXP m) <= eta` THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
        MATCH_MP_TAC(REAL_ARITH
         `!e p. &0 <= (&1 / &2 - e) * p ==> e * p <= p / &2`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!t p q. t * (p / &4) <= t * ((p - q) / &2)
              ==> t / &4 * p <= t / &2 * (p - q)`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S1 = {x | x IN A /\ ?i. i < k /\ ~(hj_replace k i x IN A)}` THEN
  SUBGOAL_THEN
   `hj_density (k + 1) m A <= hj_density (k + 1) m (hj_cube k m) +
    hj_density (k + 1) m S1`
  MP_TAC THENL
   [EXPAND_TAC "S1" THEN
    REWRITE_TAC[hj_density] THEN SIMP_TAC[GSYM FMEAN_ADD; FINITE_HJ_CUBE] THEN
    MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_HJ_CUBE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:num->num) IN A` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      REPEAT COND_CASES_TAC THEN REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `?i. i < k /\ ~(hj_replace k i (x:num->num) IN A)` THEN
    ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:num->num) IN hj_cube k m`
    (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC HJ_LINE_FREE_POINTS THEN ASM_MESON_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[HJ_DENSITY_SMALL_CUBE] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Increment on an intersection of insensitive sets (DKT Corollary 11).      *)
(* ------------------------------------------------------------------------- *)

let HJ_DENSITY_CUBE = prove
 (`!q n. 1 <= q ==> hj_density q n (hj_cube q n) = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_density] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `fmean (hj_cube q n) (\x. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_EQ THEN SIMP_TAC[];
    MATCH_MP_TAC FMEAN_CONST THEN
      ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY]]);;

let HJ_DENSITY_COMPL_CUBE = prove
 (`!q n (P:(num->num)->bool).
        1 <= q
        ==> hj_density q n {x | x IN hj_cube q n /\ ~P x} =
            &1 - hj_density q n {x | x IN hj_cube q n /\ P x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `hj_density q n {x | x IN hj_cube q n /\ ~P x} =
    hj_density q n {x | ~P x} /\
    hj_density q n {x | x IN hj_cube q n /\ P x} = hj_density q n {x | P x}`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[HJ_DENSITY_COMPL]]);;

let DKT_COR11 = prove
 (`!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta /\ delta <= &1
        ==> ?gamma M0.
              &0 < gamma /\
              !m. M0 <= m
                  ==> ?N. !n A rho.
                        N <= n /\ delta <= rho /\
                        rho <= hj_density (k + 1) n A /\
                        ~hj_has_line (k + 1) n A
                        ==> ?W D.
                              hj_subspace (k + 1) m n W /\
                              (!i. i < k
                                   ==> hj_insensitive (k + 1) m i k (D i)) /\
                              gamma <=
                              hj_density (k + 1) m
                                {x | x IN hj_cube (k + 1) m /\
                                     !i. i < k ==> x IN D i} /\
                              (rho + gamma) *
                              hj_density (k + 1) m
                                {x | x IN hj_cube (k + 1) m /\
                                     !i. i < k ==> x IN D i} <=
                              hj_density (k + 1) m
                                {x | hj_subst (k + 1) W x IN A /\
                                     !i. i < k ==> x IN D i}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `delta:real`] DKT_LEMMA8) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:num` (X_CHOOSE_THEN `theta:real`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `th = min theta (&1)` THEN
  SUBGOAL_THEN `&0 < th /\ th <= theta /\ th <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = (delta * th) / &48` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= delta / &48 /\ eta <= th / &48 /\
                delta * th = &48 * eta`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      ASM_SIMP_TAC[REAL_LT_MUL];
      MATCH_MP_TAC(REAL_ARITH `!a b. a <= b ==> a / &48 <= b / &48`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `!a b. a <= b ==> a / &48 <= b / &48`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `eta pow 2 <= eta` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `eta:real`] DKT_POW_RATIO_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
  EXISTS_TAC `delta * eta pow 2 / (&2 * &k)` THEN
  EXISTS_TAC `m0 + M1:num` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `eta:real`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `theta:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta:real` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`; `rho:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:(num->num)->bool`;
    `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `delta * eta pow 2 / (&2 * &k) <= eta pow 2 / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `delta * eta pow 2 / (&2 * &k) = (eta pow 2 / &2) * (delta / &k)`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   ARITH_RULE `1 <= k ==> 0 < k`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`X:num->num`; `\i:num. {x:num->num | T}`] THEN
    ASM_REWRITE_TAC[HJ_INSENSITIVE_UNIV; IN_ELIM_THM] THEN
    REWRITE_TAC[SET_RULE `!s:(num->num)->bool. {x | x IN s} = s`] THEN
    ASM_SIMP_TAC[HJ_DENSITY_CUBE; ARITH_RULE `1 <= k + 1`; REAL_MUL_RID] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rho + eta pow 2 / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A' = {a | hj_subst (k + 1) W a IN A}` THEN
  SUBGOAL_THEN `~hj_has_line (k + 1) m A'` ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN DISCH_TAC THEN
    UNDISCH_TAC `~hj_has_line (k + 1) n A` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HJ_HAS_LINE_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `W:num->num`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `A':(num->num)->bool`; `th:real`;
                 `eta:real`; `rho:real`] DKT_LEMMA10) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `theta / &2 * &(CARD {u | hj_line k m u})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "A'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `Cs = {x | x IN hj_cube (k + 1) m /\
          !i. i < k ==> hj_replace k i x IN A'}` THEN
  ABBREV_TAC
   `NCs = {x | x IN hj_cube (k + 1) m /\
           ?i. i < k /\ ~(hj_replace k i x IN A')}` THEN
  ABBREV_TAC
    `ANC = {x | x IN A' /\ ?i. i < k /\ ~(hj_replace k i x IN A')}` THEN
  SUBGOAL_THEN `hj_density (k + 1) m NCs = &1 - hj_density (k + 1) m Cs`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["NCs"; "Cs"] THEN
    MP_TAC(ISPECL [`k + 1`; `m:num`;
                   `\x. !i. i < k
                            ==> hj_replace k i x IN (A':(num->num)->bool)`]
      HJ_DENSITY_COMPL_CUBE) THEN
    REWRITE_TAC[ARITH_RULE `1 <= k + 1`; NOT_FORALL_THM; NOT_IMP];
    ALL_TAC] THEN
  SUBGOAL_THEN `hj_density (k + 1) m ANC <= hj_density (k + 1) m NCs`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ANC"; "NCs"] THEN MATCH_MP_TAC HJ_DENSITY_MONO THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `k + 1`; `m:num`;
                 `\i:num. {x:num->num | hj_replace k i x IN A'}`;
                 `A':(num->num)->bool`; `rho:real`; `eta:real`]
    DKT_PARTITION_INCREMENT) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rho - &3 * eta` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(rho + &6 * eta) * (&1 - th / &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `delta * th <= rho * th /\ &0 <= eta * th` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `W:num->num` THEN
  EXISTS_TAC `\i. if i < i0 then {x | hj_replace k i x IN A'}
                  else if i = i0 then {x:num->num | ~(hj_replace k i0 x IN A')}
                  else {x | T}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num < i0` THEN
    ASM_REWRITE_TAC[HJ_INSENSITIVE_REPLACE] THEN
    ASM_CASES_TAC `i:num = i0` THEN ASM_REWRITE_TAC[HJ_INSENSITIVE_UNIV] THEN
    MP_TAC(ISPECL [`k + 1`; `m:num`; `i0:num`; `k:num`;
                   `{x:num->num | hj_replace k i0 x IN A'}`]
                     HJ_INSENSITIVE_COMPL) THEN
    REWRITE_TAC[HJ_INSENSITIVE_REPLACE; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (!i. i < k
             ==> x IN (if i < i0 then {x | hj_replace k i x IN A'}
                       else if i =
                       i0 then {x:num->num | ~(hj_replace k i0 x IN A')}
                       else {x | T})) <=>
        ~(hj_replace k i0 x IN A') /\ (!j. j < i0 ==> hj_replace k j x IN A')`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `x:num->num` THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i0:num`) THEN
        ASM_REWRITE_TAC[LT_REFL; IN_ELIM_THM];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
        ASM_SIMP_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
         [ASM_ARITH_TAC; SIMP_TAC[]]];
      STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num < i0` THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
      ASM_CASES_TAC `i:num = i0` THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | hj_subst (k + 1) W x IN A /\ ~(hj_replace k i0 x IN A') /\
         (!j. j < i0 ==> hj_replace k j x IN A')} =
    {x | x IN A' /\ ~(hj_replace k i0 x IN A') /\
         (!j. j < i0 ==> hj_replace k j x IN A')}`
  SUBST1_TAC THENL
   [EXPAND_TAC "A'" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `P0 = {x | x IN hj_cube (k + 1) m /\ ~(hj_replace k i0 x IN A') /\
              (!j. j < i0 ==> hj_replace k j x IN A')}` THEN
  ABBREV_TAC
   `AP0 = {x | x IN A' /\ ~(hj_replace k i0 x IN A') /\
               (!j. j < i0 ==> hj_replace k j x IN A')}` THEN
  SUBGOAL_THEN `&0 <= hj_density (k + 1) m P0` ASSUME_TAC THENL
   [REWRITE_TAC[HJ_DENSITY_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `delta * eta <= delta` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eta / &k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eta / &k * (delta * eta / &6) <= eta / &k * (&1 - hj_density (k + 1) m Cs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `delta * eta pow 2 / (&2 * &k) = &3 * (eta / &k * (delta * eta / &6))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(rho + &3 * eta) * hj_density (k + 1) m P0` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The tiling part of the density increment (DKT Lemma 12 and                *)
(* Corollary 13).                                                            *)
(*                                                                           *)
(* * hj_tiling q m n Fs E: Fs is a finite family of m-variable words of      *)
(*   length n whose subspaces lie in E and are pairwise disjoint;            *)
(*   hj_tiling_union is the union of the subspaces.                          *)
(*   HJ_DENSITY_TILING_UNION_RESTRICT computes densities inside a tiling;    *)
(*   HJ_TILING_AVERAGE: an increment on the union gives an increment on      *)
(*   one tile.                                                               *)
(* * hj_insert p M1 w z inserts the block z after the first p letters of     *)
(*   w.  DKT_TILE_STEP (one greedy step of DKT Lemma 12): if the sections    *)
(*   of E after any prefix of length p are insensitive on M1 + r letters     *)
(*   and hj_density E >= 2 beta, then DKT_COR5, HJ_INSENSITIVE_TRANSFER      *)
(*   and pigeonhole give one block V0 and a tiling of density >= Theta in    *)
(*   E such that the leftover is insensitive after any prefix of length      *)
(*   p + M1 (HJ_INSENSITIVE_LEFTOVER).                                       *)
(* * HJ_TILING_INSENSITIVE (DKT Lemma 12): every (i, k)-insensitive set of   *)
(*   large dimension has a tiling by m-dimensional subspaces whose           *)
(*   leftover has density < 2 beta (HJ_TILING_ITER, induction on the         *)
(*   number of steps).                                                       *)
(* * HJ_TILING_STRUCTURED (DKT Corollary 13): the same for intersections     *)
(*   of r such sets with leftover <= 2 r beta, by induction on r: each       *)
(*   tile of the first r sets is tiled again through the pullback of the     *)
(*   next set (HJ_INSENSITIVE_PULLBACK, HJ_TILING_COMPOSE,                   *)
(*   HJ_TILING_COMPOSE_DENS).                                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Tilings by subspaces.                                                     *)
(* ------------------------------------------------------------------------- *)

let hj_tiling = new_definition
 `hj_tiling q m n Fs E <=>
    FINITE Fs /\
    (!z. z IN Fs ==> hj_subspace q m n z /\ !a. a IN hj_cube q m ==>
      hj_subst q z a IN E) /\
    (!z z' a a'. z IN Fs /\ z' IN Fs /\ a IN hj_cube q m /\
                 a' IN hj_cube q m /\
                 hj_subst q z a = hj_subst q z' a' ==> z = z')`;;

let hj_tiling_union = new_definition
 `hj_tiling_union q m Fs =
  {x | ?z a. z IN Fs /\ a IN hj_cube q m /\ x = hj_subst q z a}`;;

let HJ_TILING_EMPTY = prove
 (`!q m n E. hj_tiling q m n {} E`,
  REWRITE_TAC[hj_tiling; FINITE_EMPTY; NOT_IN_EMPTY]);;

let HJ_TILING_UNION_EMPTY = prove
 (`!q m. hj_tiling_union q m {} = {}`,
  REWRITE_TAC[hj_tiling_union; NOT_IN_EMPTY; EXTENSION; IN_ELIM_THM]);;

let HJ_TILING_UNION_SUBSET = prove
 (`!q m n Fs E. hj_tiling q m n Fs E ==> hj_tiling_union q m Fs SUBSET E`,
  REWRITE_TAC[hj_tiling; hj_tiling_union; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let HJ_TILING_UNION_CUBE = prove
 (`!q m n Fs E. 1 <= q /\ hj_tiling q m n Fs E ==>
   hj_tiling_union q m Fs SUBSET hj_cube q n`,
  REWRITE_TAC[hj_tiling; hj_tiling_union; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[HJ_SUBST_CUBE]);;

let HJ_TILING_INJ = prove
 (`!q m n Fs E z z' a a'.
        hj_tiling q m n Fs E /\ z IN Fs /\ z' IN Fs /\
        a IN hj_cube q m /\ a' IN hj_cube q m /\
        hj_subst q z a = hj_subst q z' a'
        ==> z = z' /\ a = a'`,
  REWRITE_TAC[hj_tiling] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `z:num->num = z'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HJ_SUBST_INJ THEN
  MAP_EVERY EXISTS_TAC [`q:num`; `q:num`; `m:num`; `n:num`; `z':num->num`] THEN
  ASM_MESON_TAC[]);;

let CARD_HJ_TILING_UNION_RESTRICT = prove
 (`!q m n Fs E (P:(num->num)->bool).
        hj_tiling q m n Fs E
        ==> &(CARD {x | x IN hj_tiling_union q m Fs /\ P x}) =
            sum Fs (\z. &(CARD {a | a IN hj_cube q m /\ P (hj_subst q z a)}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hj_tiling]) THEN
  SUBGOAL_THEN
   `{x | x IN hj_tiling_union q m Fs /\ P x} =
    IMAGE (\(z,a). hj_subst q z a)
          {(z,a) | z IN Fs /\ a IN hj_cube q m /\ P (hj_subst q z a)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; hj_tiling_union; IN_ELIM_THM; IN_IMAGE;
                EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o rand o
    lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
      ASM_MESON_TAC[HJ_TILING_INJ];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(Fs:(num->num)->bool) CROSS hj_cube q m` THEN
      ASM_SIMP_TAC[FINITE_CROSS; FINITE_HJ_CUBE] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS] THEN
      MESON_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`Fs:(num->num)->bool`;
    `\z. {a | a IN hj_cube q m /\ (P:(num->num)->bool) (hj_subst q z a)}`;
    `\z:num->num a:num->num. &1`] SUM_SUM_PRODUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `hj_cube q m` THEN
    REWRITE_TAC[FINITE_HJ_CUBE] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(\(i:num->num,j:num->num). &1) =
                (\p:(num->num)#(num->num). &1)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {i,j | i IN Fs /\ j IN hj_cube q m /\
                  (P:(num->num)->bool) (hj_subst q i j)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(Fs:(num->num)->bool) CROSS hj_cube q m` THEN
    ASM_SIMP_TAC[FINITE_CROSS; FINITE_HJ_CUBE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; FINITE_RESTRICT; FINITE_HJ_CUBE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

let HJ_DENSITY_TILING_UNION_RESTRICT = prove
 (`!q m n Fs E (P:(num->num)->bool).
        1 <= q /\ hj_tiling q m n Fs E
        ==> hj_density q n {x | x IN hj_tiling_union q m Fs /\ P x} =
            sum Fs (\z. hj_density q m {a | P (hj_subst q z a)}) *
            &(q EXP m) / &(q EXP n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HJ_DENSITY_CARD; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `{x | x IN hj_cube q n /\ x IN hj_tiling_union q m Fs /\ P x} =
    {x | x IN hj_tiling_union q m Fs /\ P x}`
  SUBST1_TAC THENL
   [MP_TAC(SPEC_ALL HJ_TILING_UNION_CUBE) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:num`; `m:num`; `n:num`; `Fs:(num->num)->bool`;
                 `E:(num->num)->bool`; `P:(num->num)->bool`]
    CARD_HJ_TILING_UNION_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `z:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_FIELD
   `!c p r. ~(p = &0) ==> c * inv r = ((c * inv p) * p) * inv r`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; EXP_EQ_0] THEN ASM_ARITH_TAC);;

let HJ_TILING_AVERAGE = prove
 (`!q m n Fs E A c.
        1 <= q /\ hj_tiling q m n Fs E /\ ~(Fs = {}) /\
        c * hj_density q n (hj_tiling_union q m Fs) <=
        hj_density q n {x | x IN hj_tiling_union q m Fs /\ x IN A}
        ==> ?z. z IN Fs /\ c <= hj_density q m {a | hj_subst q z a IN A}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:num`; `m:num`; `n:num`; `Fs:(num->num)->bool`;
                 `E:(num->num)->bool`;
                   `\x:num->num. T`] HJ_DENSITY_TILING_UNION_RESTRICT) THEN
  MP_TAC(ISPECL [`q:num`; `m:num`; `n:num`; `Fs:(num->num)->bool`;
                 `E:(num->num)->bool`; `\x:num->num. x IN A`]
    HJ_DENSITY_TILING_UNION_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `!s:(num->num)->bool. {x | x IN s} = s`] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &(q EXP m) / &(q EXP n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
     REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hj_density q m {a:num->num | T} = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `hj_density q m (hj_cube q m)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC[IN_ELIM_THM];
                    ASM_SIMP_TAC[HJ_DENSITY_CUBE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE
   [NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`; REAL_NOT_LE]) THEN
  SUBGOAL_THEN `FINITE(Fs:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[hj_tiling]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Fs (\z. hj_density q m {a | hj_subst q z a IN A}) <
    &(CARD(Fs:(num->num)->bool)) * c`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. hj_density q m {a | hj_subst q z a IN A}`;
                   `\z:num->num. c:real`; `Fs:(num->num)->bool`]
      SUM_LT_ALL) THEN
    ASM_SIMP_TAC[SUM_CONST];
    ALL_TAC] THEN
  UNDISCH_TAC
   `c * hj_density q n (hj_tiling_union q m Fs) <=
    hj_density q n {x | x IN hj_tiling_union q m Fs /\ x IN A}` THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID] THEN
  MP_TAC(ISPECL [`sum Fs (\z. hj_density q m {a | hj_subst q z a IN A})`;
                 `&(CARD(Fs:(num->num)->bool)) * c`;
                 `&(q EXP m) / &(q EXP n)`] REAL_LT_RMUL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!s n c r. s * r < (n * c) * r ==> ~(c * n * r <= s * r)`));;

(* ------------------------------------------------------------------------- *)
(* Insensitivity under sections, pullbacks and intersections.                *)
(* ------------------------------------------------------------------------- *)

let HJ_REPLACE_CONCAT = prove
 (`!j i l x y. hj_replace j i (hj_concat l x y) =
               hj_concat l (hj_replace j i x) (hj_replace j i y)`,
  REWRITE_TAC[hj_replace; hj_concat; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x':num < l` THEN ASM_REWRITE_TAC[]);;

let HJ_INSENSITIVE_SECTION_PREFIX = prove
 (`!q l r i j D y.
        hj_insensitive q (l + r) i j D /\ y IN hj_cube q l
        ==> hj_insensitive q r i j {x | hj_concat l y x IN D}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HJ_CONCAT_CUBE; HJ_REPLACE_CONCAT]);;

let HJ_INSENSITIVE_SECTION_SUFFIX = prove
 (`!q l r i j D x'.
        hj_insensitive q (l + r) i j D /\ x' IN hj_cube q r
        ==> hj_insensitive q l i j {z | hj_concat l z x' IN D}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HJ_CONCAT_CUBE; HJ_REPLACE_CONCAT]);;

let HJ_INSENSITIVE_FORALL = prove
 (`!q n i j (X:A->bool) D.
        (!a. a IN X ==> hj_insensitive q n i j (D a))
        ==> hj_insensitive q n i j {x | !a. a IN X ==> x IN D a}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN MESON_TAC[]);;

let HJ_INSENSITIVE_DIFF = prove
 (`!q n i j D1 D2.
        hj_insensitive q n i j D1 /\ hj_insensitive q n i j D2
        ==> hj_insensitive q n i j {x | x IN D1 /\ ~(x IN D2)}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN MESON_TAC[]);;

let HJ_INSENSITIVE_PULLBACK = prove
 (`!k m n i z D.
        1 <= k /\ hj_insensitive (k + 1) n i k D /\ hj_subspace (k + 1) m n z
        ==> hj_insensitive (k + 1) m i k {a | hj_subst (k + 1) z a IN D}`,
  REWRITE_TAC[hj_insensitive; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HJ_SUBST_CUBE; ARITH_RULE `1 <= k + 1`];
    ASM_MESON_TAC[HJ_SUBST_CUBE; ARITH_RULE `1 <= k + 1`];
    ALL_TAC] THEN
  UNDISCH_TAC `hj_replace k i x = hj_replace k i (y:num->num)` THEN
  REWRITE_TAC[hj_replace; hj_subst; FUN_EQ_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `r:num` THEN ASM_CASES_TAC `(z:num->num) r < k + 1` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(z:num->num) r - (k + 1)`) THEN
  REWRITE_TAC[]);;

let HJ_INSENSITIVE_TRANSFER = prove
 (`!k m M1 i V D.
        1 <= k /\ i < k /\ hj_subspace (k + 1) m M1 V /\
        hj_insensitive (k + 1) M1 i k D /\
        (!a. a IN hj_cube k m ==> hj_subst (k + 1) V a IN D)
        ==> !a. a IN hj_cube (k + 1) m ==> hj_subst (k + 1) V a IN D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hj_replace k i (a:num->num) IN hj_cube k m` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:num->num) IN hj_cube (k + 1) m` THEN
    REWRITE_TAC[IN_HJ_CUBE; hj_replace] THEN STRIP_TAC THEN CONJ_TAC THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:num->num) r < k + 1` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM_ARITH_TAC];
      SUBGOAL_THEN `(a:num->num) r = 0` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `hj_insensitive (k + 1) M1 i k D` THEN
  REWRITE_TAC[hj_insensitive] THEN
  DISCH_THEN(MP_TAC o SPECL [`hj_subst (k + 1) V (hj_replace k i a)`;
                             `hj_subst (k + 1) V a`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
      ASM_MESON_TAC[HJ_CUBE_MONO_IN; ARITH_RULE `k <= k + 1`];
      MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`];
      REWRITE_TAC[hj_replace; hj_subst; FUN_EQ_THM] THEN X_GEN_TAC `r:num` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(a:num->num) ((V:num->num) r - (k + 1)) = k` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Block insertion.                                                          *)
(* ------------------------------------------------------------------------- *)

let hj_insert = new_definition
 `hj_insert p M1 (w:num->num) (z:num->num) =
    hj_concat p (hj_take p w) (hj_concat M1 z (hj_drop p w))`;;

let HJ_INSERT_CUBE = prove
 (`!q p M1 r w z. w IN hj_cube q (p + r) /\ z IN hj_cube q M1
                  ==> hj_insert p M1 w z IN hj_cube q (p + (M1 + r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_insert] THEN
  MATCH_MP_TAC HJ_CONCAT_CUBE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HJ_CONCAT_CUBE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC[]]);;

let HJ_INSERT_CONCAT = prove
 (`!q p M1 y x z. y IN hj_cube q p
                  ==> hj_insert p M1 (hj_concat p y x) z =
                      hj_concat p y (hj_concat M1 z x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_insert; HJ_DROP_CONCAT] THEN
  ASM_MESON_TAC[HJ_TAKE_CONCAT]);;

let HJ_INSERT_INJ = prove
 (`!q p M1 r w w' z z'.
        w IN hj_cube q (p + r) /\ w' IN hj_cube q (p + r) /\
        z IN hj_cube q M1 /\ z' IN hj_cube q M1 /\
        hj_insert p M1 w z = hj_insert p M1 w' z'
        ==> w = w' /\ z = z'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_insert] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `hj_take p (w:num->num) IN hj_cube q p /\
    hj_take p (w':num->num) IN hj_cube q p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:num`; `p:num`; `hj_take p (w:num->num)`;
                 `hj_concat M1 z (hj_drop p (w:num->num))`;
                 `hj_take p (w':num->num)`;
                 `hj_concat M1 z' (hj_drop p (w':num->num))`]
                   HJ_CONCAT_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:num`; `M1:num`; `z:num->num`; `hj_drop p (w:num->num)`;
                 `z':num->num`; `hj_drop p (w':num->num)`] HJ_CONCAT_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM HJ_CONCAT_SPLIT] THEN ASM_MESON_TAC[HJ_CONCAT_SPLIT]);;

let SUM_HJ_INSERT = prove
 (`!q p M1 r f.
        sum (hj_cube q (p + (M1 + r))) f =
        sum (hj_cube q (p + r))
            (\w. sum (hj_cube q M1) (\z. f (hj_insert p M1 w z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUM_HJ_CONCAT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[MATCH_MP HJ_INSERT_CONCAT
                (ASSUME `(y:num->num) IN hj_cube q p`)] THEN
  MP_TAC(ISPECL
           [`\z x. (f:(num->num)->real) (hj_concat p y (hj_concat M1 z x))`;
                 `hj_cube q M1`; `hj_cube q r`] SUM_SWAP) THEN
  REWRITE_TAC[FINITE_HJ_CUBE]);;

let HJ_DENSITY_INSERT = prove
 (`!q p M1 r E.
        hj_density q (p + (M1 + r)) E =
        fmean (hj_cube q (p + r))
          (\w. hj_density q M1 {z | hj_insert p M1 w z IN E})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[hj_density; fmean; IN_ELIM_THM; CARD_HJ_CUBE] THEN
  REWRITE_TAC[SUM_HJ_INSERT] THEN REWRITE_TAC[real_div; SUM_RMUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL] THEN REWRITE_TAC[REAL_MUL_AC]);;

let FINITE_HJ_SUBSPACES = prove
 (`!q m n. FINITE {V | hj_subspace q m n V} /\
           CARD {V | hj_subspace q m n V} <= (q + m) EXP n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{V | hj_subspace q m n V} SUBSET hj_cube (q + m) n`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; HJ_SUBSPACE_CUBE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_HJ_CUBE];
    REWRITE_TAC[GSYM CARD_HJ_CUBE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_HJ_CUBE]]);;

let HJ_DROP_ZERO = prove
 (`!a. hj_drop 0 a = a`,
  REWRITE_TAC[hj_drop; ADD_CLAUSES; ETA_AX]);;

let HJ_SUBST_TILE = prove
 (`!q p M1 r m V w a.
        1 <= q /\ w IN hj_cube q (p + r)
        ==> hj_subst q
              (hj_join q p 0 (hj_take p w)
                 (hj_join q M1 m V (hj_drop p w))) a =
            hj_insert p M1 w (hj_subst q V a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HJ_SUBST_JOIN; hj_insert; HJ_DROP_ZERO] THEN
  SUBGOAL_THEN `hj_take p (w:num->num) IN hj_cube q p /\
                hj_drop p (w:num->num) IN hj_cube q r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_MESON_TAC[HJ_SUBST_WORD]);;

(* ------------------------------------------------------------------------- *)
(* One greedy tiling step.                                                   *)
(* ------------------------------------------------------------------------- *)

let HJ_INSENSITIVE_EQ = prove
 (`!q n i j D D'.
        hj_insensitive q n i j D /\
        (!x. x IN hj_cube q n ==> (x IN D <=> x IN D'))
        ==> hj_insensitive q n i j D'`,
  REWRITE_TAC[hj_insensitive] THEN MESON_TAC[]);;

let HJ_INSENSITIVE_LEFTOVER = prove
 (`!q p M1 r i j E Z y.
        (!y0. y0 IN hj_cube q p
              ==> hj_insensitive q (M1 + r) i j {x | hj_concat p y0 x IN E}) /\
        Z SUBSET hj_cube q M1 /\ y IN hj_cube q (p + M1)
        ==> hj_insensitive q r i j
              {x | hj_concat (p + M1) y x IN E /\
                   ~(?w z. w IN hj_cube q (p + r) /\
                           (!z'. z' IN Z ==> hj_insert p M1 w z' IN E) /\
                           z IN Z /\
                           hj_concat (p + M1) y x = hj_insert p M1 w z)}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y0 = hj_take p (y:num->num)` THEN
  ABBREV_TAC `z0 = hj_drop p (y:num->num)` THEN
  SUBGOAL_THEN `(y0:num->num) IN hj_cube q p /\ (z0:num->num) IN hj_cube q M1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y0"; "z0"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC `M1:num` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!x. hj_concat (p + M1) y x = hj_concat p y0 (hj_concat M1 z0 x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[HJ_CONCAT_ASSOC] THEN
    MAP_EVERY EXPAND_TAC ["y0"; "z0"] THEN REWRITE_TAC[HJ_CONCAT_SPLIT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN hj_cube q r
        ==> ((?w z. w IN hj_cube q (p + r) /\
                    (!z'. z' IN Z ==> hj_insert p M1 w z' IN E) /\
                    z IN Z /\ hj_concat (p + M1) y x = hj_insert p M1 w z) <=>
             (z0:num->num) IN Z /\
             !z'. z' IN Z ==> hj_concat p y0 (hj_concat M1 z' x) IN E)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `hj_concat p y0 (x:num->num) IN hj_cube q (p + r)` ASSUME_TAC
    THENL [MATCH_MP_TAC HJ_CONCAT_CUBE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!z'. hj_insert p M1 (hj_concat p y0 x) z' =
                       hj_concat p y0 (hj_concat M1 z' (x:num->num))`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC HJ_INSERT_CONCAT THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`w:num->num`; `z:num->num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`q:num`; `p:num`; `M1:num`; `r:num`;
                     `hj_concat p y0 (x:num->num)`; `w:num->num`;
                     `z0:num->num`; `z:num->num`] HJ_INSERT_INJ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASM_MESON_TAC[];
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`hj_concat p y0 (x:num->num)`; `z0:num->num`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z'. z' IN hj_cube q M1
         ==> hj_insensitive q r i j
               {x | hj_concat M1 z' x IN {u | hj_concat p y0 u IN E}}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HJ_INSENSITIVE_SECTION_PREFIX THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HJ_INSENSITIVE_EQ THEN ASM_CASES_TAC `(z0:num->num) IN Z` THENL
   [EXISTS_TAC
     `{x | x IN {x | hj_concat M1 z0 x IN {u | hj_concat p y0 u IN E}} /\
           ~(x IN {x | !z'. z' IN Z ==>
                       x IN {x | hj_concat M1 z' x IN
                               {u | hj_concat p y0 u IN E}}})}`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_INSENSITIVE_DIFF THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC HJ_INSENSITIVE_FORALL THEN ASM SET_TAC[];
      ASM_SIMP_TAC[IN_ELIM_THM]];
    EXISTS_TAC `{x | hj_concat M1 z0 x IN {u | hj_concat p y0 u IN E}}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM]]);;

let DKT_TILE_STEP = prove
 (`!k m beta i.
        1 <= k /\ density_hales_jewett k /\ 1 <= m /\ &0 < beta /\ i < k
        ==> ?M1 Theta.
              &0 < Theta /\
              !p r E.
                (!y. y IN hj_cube (k + 1) p
                     ==> hj_insensitive (k + 1) (M1 + r) i k
                           {x | hj_concat p y x IN E}) /\
                &2 * beta <= hj_density (k + 1) (p + (M1 + r)) E
                ==> ?Fs. hj_tiling (k + 1) m (p + (M1 + r)) Fs E /\
                         Theta <=
                         hj_density (k + 1) (p + (M1 + r))
                           (hj_tiling_union (k + 1) m Fs) /\
                         !y. y IN hj_cube (k + 1) (p + M1)
                             ==> hj_insensitive (k + 1) r i k
                                   {x | hj_concat (p + M1) y x IN E /\
                                        ~(hj_concat (p + M1) y x IN
                                          hj_tiling_union (k + 1) m Fs)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` DKT_COR5) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `beta:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:num` (LABEL_TAC "mdhj")) THEN
  EXISTS_TAC `M1:num` THEN
  EXISTS_TAC `beta / &((k + 1 + m) EXP M1) * &((k + 1) EXP m) /
              &((k + 1) EXP M1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `r:num`; `E:(num->num)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN hj_cube (k + 1) (p + r)
        ==> hj_insensitive (k + 1) M1 i k {z | hj_insert p M1 w z IN E}`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:num->num` THEN DISCH_TAC THEN REWRITE_TAC[hj_insert] THEN
    MP_TAC(ISPECL [`k + 1`; `M1:num`; `r:num`; `i:num`; `k:num`;
                   `{u | hj_concat p (hj_take p w) u IN E}`;
                   `hj_drop p (w:num->num)`]
      HJ_INSENSITIVE_SECTION_SUFFIX) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = {w | beta <= hj_density (k + 1) M1 {z | hj_insert p M1 w z IN E}}` THEN
  SUBGOAL_THEN `beta <= hj_density (k + 1) (p + r) G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`k + 1`; `p + r:num`;
                   `\w. hj_density (k + 1) M1 {z | hj_insert p M1 w z IN E}`;
                   `&2 * beta`; `beta:real`] HJ_DENSITY_MARKOV) THEN
    REWRITE_TAC[HJ_DENSITY_LE_1; ARITH_RULE `1 <= k + 1`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM HJ_DENSITY_INSERT] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `!b x. &2 * b - b <= x ==> b <= x`) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `Vw = \w. @V. hj_subspace (k + 1) m M1 V /\
                 !a. a IN hj_cube (k + 1) m ==>
                   hj_insert p M1 w (hj_subst (k + 1) V a) IN E` THEN
  SUBGOAL_THEN
   `!w. w IN hj_cube (k + 1) (p + r) /\ w IN G
        ==> hj_subspace (k + 1) m M1 ((Vw:(num->num)->(num->num)) w) /\
            !a. a IN hj_cube (k + 1) m
                ==> hj_insert p M1 w (hj_subst (k + 1) (Vw w) a) IN E`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:num->num` THEN STRIP_TAC THEN EXPAND_TAC "Vw" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
    REMOVE_THEN "mdhj" (MP_TAC o SPECL
     [`M1:num`; `{z | hj_insert p M1 w z IN E}`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LE_REFL] THEN UNDISCH_TAC `(w:num->num) IN G` THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:num->num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `M1:num`; `i:num`; `V:num->num`;
                   `{z | hj_insert p M1 w z IN E}`]
                     HJ_INSENSITIVE_TRANSFER) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `p + r:num`; `G:(num->num)->bool`;
                 `Vw:(num->num)->(num->num)`;
                 `{V | hj_subspace (k + 1) m M1 V}`]
    HJ_DENSITY_PIGEONHOLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_HJ_SUBSPACES; IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MP_TAC(SPECL [`k + 1`; `p + r:num`; `G:(num->num)->bool`]
      HJ_DENSITY_POS_EXISTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:num->num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `S0 = {w | w IN hj_cube (k + 1) (p + r) /\
              !a. a IN hj_cube (k + 1) m
                  ==> hj_insert p M1 w (hj_subst (k + 1) V0 a) IN E}` THEN
  SUBGOAL_THEN
   `beta / &((k + 1 + m) EXP M1) <= hj_density (k + 1) (p + r) S0`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`k + 1`; `m:num`; `M1:num`] FINITE_HJ_SUBSPACES) THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) + m = k + 1 + m`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &(CARD {V | hj_subspace (k + 1) m M1 V})`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `V0:num->num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `hj_density (k + 1) (p + r) {w | w IN G /\
       (Vw:(num->num)->(num->num)) w = V0}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `beta / &(CARD {V | hj_subspace (k + 1) m M1 V})` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        MATCH_MP_TAC(REAL_ARITH
         `!a b c d:real. a <= b /\ b <= c * d ==> a <= d * c`) THEN
        EXISTS_TAC `hj_density (k + 1) (p + r) G` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC HJ_DENSITY_MONO THEN EXPAND_TAC "S0" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:num->num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:num->num` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `Vw:(num->num)->(num->num)`))
                             (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `tile = \w. hj_join (k + 1) p 0 (hj_take p w)
                   (hj_join (k + 1) M1 m V0 (hj_drop p (w:num->num)))` THEN
  SUBGOAL_THEN
   `!w a. w IN hj_cube (k + 1) (p + r)
          ==> hj_subst (k + 1) ((tile:(num->num)->(num->num)) w) a =
              hj_insert p M1 w (hj_subst (k + 1) V0 a)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tile" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HJ_SUBST_TILE THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN hj_cube (k + 1) (p + r)
        ==> hj_subspace (k + 1) m (p + (M1 + r))
              ((tile:(num->num)->(num->num)) w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tile" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k + 1`; `M1:num`; `m:num`; `0`; `r:num`; `V0:num->num`;
                   `hj_drop p (w:num->num)`] HJ_SUBSPACE_JOIN) THEN
    MP_TAC(ISPECL [`k + 1`; `p:num`; `0`; `m + 0`; `M1 + r:num`;
                   `hj_take p (w:num->num)`;
                   `hj_join (k + 1) M1 m V0 (hj_drop p (w:num->num))`]
                     HJ_SUBSPACE_JOIN) THEN
    REWRITE_TAC[ADD_CLAUSES; HJ_SUBSPACE_0] THEN
    SUBGOAL_THEN `hj_take p (w:num->num) IN hj_cube (k + 1) p /\
                  hj_drop p (w:num->num) IN hj_cube (k + 1) r`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC `r:num` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w w'. w IN hj_cube (k + 1) (p + r) /\
                       w' IN hj_cube (k + 1) (p + r) /\
                       ((tile:(num->num)->(num->num)) w = tile w')
                       ==> w = w'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\z. hj_subst (k + 1) z (\i:num. 0)` o
      check (is_eq o concl)) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k + 1`; `p:num`; `M1:num`; `r:num`; `w:num->num`;
                   `w':num->num`; `hj_subst (k + 1) V0 (\i:num. 0)`;
                   `hj_subst (k + 1) V0 (\i:num. 0)`] HJ_INSERT_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`; IN_HJ_CUBE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `S0 SUBSET hj_cube (k + 1) (p + r)` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hj_tiling (k + 1) m (p + (M1 + r))
           (IMAGE (tile:(num->num)->(num->num)) S0) E`
  ASSUME_TAC THENL
   [REWRITE_TAC[hj_tiling; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[FINITE_SUBSET; FINITE_HJ_CUBE];
      X_GEN_TAC `w:num->num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:num->num) IN hj_cube (k + 1) (p + r)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN UNDISCH_TAC `(w:num->num) IN S0` THEN
      EXPAND_TAC "S0" THEN SIMP_TAC[IN_ELIM_THM];
      REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(x:num->num) IN hj_cube (k + 1) (p + r) /\
                    (x':num->num) IN hj_cube (k + 1) (p + r)`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `hj_subst (k + 1) z a = hj_subst (k + 1) z' a'` THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k + 1`; `p:num`; `M1:num`; `r:num`; `x:num->num`;
                     `x':num->num`; `hj_subst (k + 1) V0 a`;
                     `hj_subst (k + 1) V0 a'`] HJ_INSERT_INJ) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (tile:(num->num)->(num->num)) S0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k + 1`; `m:num`; `p + (M1 + r):num`;
                   `IMAGE (tile:(num->num)->(num->num)) S0`;
                   `E:(num->num)->bool`; `\x:num->num. T`]
      HJ_DENSITY_TILING_UNION_RESTRICT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
    REWRITE_TAC[SET_RULE `!s:(num->num)->bool. {x | x IN s} = s`] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `hj_density (k + 1) m {a:num->num | T} = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
       EXISTS_TAC `hj_density (k + 1) m (hj_cube (k + 1) m)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC[IN_ELIM_THM];
                      SIMP_TAC[HJ_DENSITY_CUBE; ARITH_RULE `1 <= k + 1`]];
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE(S0:(num->num)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_HJ_CUBE]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_IMAGE; REAL_MUL_RID] THEN
    SUBGOAL_THEN `CARD (IMAGE (tile:(num->num)->(num->num)) S0) = CARD S0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(CARD(S0:(num->num)->bool)) =
      hj_density (k + 1) (p + r) S0 * &((k + 1) EXP (p + r))`
    SUBST1_TAC THENL
     [REWRITE_TAC[HJ_DENSITY_CARD] THEN
      SUBGOAL_THEN `{x | x IN hj_cube (k + 1) (p + r) /\ x IN S0} = S0`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_FIELD `~(b = &0) ==> a = a / b * b`) THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; EXP_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p + M1 + r = (p + r) + M1:num` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SUBST1_TAC(SPECL [`k + 1`; `p + r:num`; `M1:num`] EXP_ADD) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&0 < &((k + 1) EXP (p + r)) /\ &0 < &((k + 1) EXP M1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN
       ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hj_density (k + 1) (p + r) S0 *
                &((k + 1) EXP m) / &((k + 1) EXP M1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < &((k + 1) EXP M1)` THEN
      UNDISCH_TAC `&0 < &((k + 1) EXP (p + r))` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u. u IN hj_tiling_union (k + 1) m
          (IMAGE (tile:(num->num)->(num->num)) S0) <=>
        ?w z. w IN hj_cube (k + 1) (p + r) /\
              (!z'. z' IN IMAGE (hj_subst (k + 1) V0) (hj_cube (k + 1) m)
                    ==> hj_insert p M1 w z' IN E) /\
              z IN IMAGE (hj_subst (k + 1) V0) (hj_cube (k + 1) m) /\
              u = hj_insert p M1 w z`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `u:num->num` THEN
    REWRITE_TAC[hj_tiling_union; IN_ELIM_THM; FORALL_IN_IMAGE; IN_IMAGE] THEN
    SUBGOAL_THEN
     `!w. w IN S0 <=>
          w IN hj_cube (k + 1) (p + r) /\
          !a. a IN hj_cube (k + 1) m
              ==> hj_insert p M1 w (hj_subst (k + 1) V0 a) IN E`
    ASSUME_TAC THENL
     [EXPAND_TAC "S0" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HJ_INSENSITIVE_LEFTOVER THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`]);;

(* ------------------------------------------------------------------------- *)
(* Tiling an insensitive set (DKT Lemma 12).                                 *)
(* ------------------------------------------------------------------------- *)

let HJ_DENSITY_SPLIT = prove
 (`!q n A B. hj_density q n A =
             hj_density q n {x | x IN A /\ x IN B} +
             hj_density q n {x | x IN A /\ ~(x IN B)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
  SIMP_TAC[GSYM FMEAN_ADD; FINITE_HJ_CUBE] THEN
  MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:num->num) IN A` THEN
  ASM_CASES_TAC `(x:num->num) IN B` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let HJ_TILING_UNION_UNION = prove
 (`!q m Fs1 Fs2. hj_tiling_union q m (Fs1 UNION Fs2) =
                 hj_tiling_union q m Fs1 UNION hj_tiling_union q m Fs2`,
  REWRITE_TAC[hj_tiling_union; EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let HJ_TILING_APPEND = prove
 (`!q m n Fs1 Fs2 E.
        hj_tiling q m n Fs1 E /\
        hj_tiling q m n Fs2 {x | x IN E /\ ~(x IN hj_tiling_union q m Fs1)}
        ==> hj_tiling q m n (Fs1 UNION Fs2) E`,
  REWRITE_TAC[hj_tiling; FINITE_UNION; IN_UNION; IN_ELIM_THM;
              hj_tiling_union] THEN
  MESON_TAC[]);;

let HJ_TILING_ITER = prove
 (`!k m beta i.
        1 <= k /\ density_hales_jewett k /\ 1 <= m /\ &0 < beta /\ i < k
        ==> ?M1 Theta.
              &0 < Theta /\
              !s p r E.
                (!y. y IN hj_cube (k + 1) p
                     ==> hj_insensitive (k + 1) (s * M1 + r) i k
                               {x | hj_concat p y x IN E}) /\
                hj_density (k + 1) (p + (s * M1 + r)) E < &2 *
                beta + &s * Theta
                ==> ?Fs. hj_tiling (k + 1) m (p + (s * M1 + r)) Fs E /\
                         hj_density (k + 1) (p + (s * M1 + r))
                              {x | x IN E /\
                               ~(x IN hj_tiling_union (k + 1) m Fs)}
                         < &2 * beta`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DKT_TILE_STEP) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M1:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Theta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step")) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n E. hj_density (k + 1) n E < &2 * beta
          ==> ?Fs. hj_tiling (k + 1) m n Fs E /\
                   hj_density (k + 1) n
                     {x | x IN E /\ ~(x IN hj_tiling_union (k + 1) m Fs)}
                   < &2 * beta`
  (LABEL_TAC "small") THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `{}:(num->num)->bool` THEN
    ASM_REWRITE_TAC[HJ_TILING_EMPTY; HJ_TILING_UNION_EMPTY; NOT_IN_EMPTY;
                    SET_RULE `!s:(num->num)->bool. {x | x IN s} = s`];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    REPEAT STRIP_TAC THEN REMOVE_THEN "small" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `r:num`; `E:(num->num)->bool`] THEN
  SUBGOAL_THEN `SUC s * M1 + r = M1 + (s * M1 + r)` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `hj_density (k + 1) (p + (M1 + (s * M1 + r))) E < &2 * beta` THENL
   [REMOVE_THEN "small" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "step" (MP_TAC o SPECL
   [`p:num`; `s * M1 + r:num`; `E:(num->num)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs1:(num->num)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`p + M1:num`; `r:num`;
    `{x | x IN E /\ ~(x IN hj_tiling_union (k + 1) m Fs1)}`]) THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM ADD_ASSOC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k + 1`; `p + (M1 + (s * M1 + r)):num`;
      `E:(num->num)->bool`;
                   `hj_tiling_union (k + 1) m Fs1`] HJ_DENSITY_SPLIT) THEN
    SUBGOAL_THEN `{x | x IN E /\ x IN hj_tiling_union (k + 1) m Fs1} =
                  hj_tiling_union (k + 1) m Fs1`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`k + 1`; `m:num`; `p + (M1 + (s * M1 + r)):num`;
                     `Fs1:(num->num)->bool`; `E:(num->num)->bool`]
        HJ_TILING_UNION_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `dleft = hj_density (k + 1) (p + (M1 + (s * M1 + r)))
                          {x | x IN E /\
                           ~(x IN hj_tiling_union (k + 1) m Fs1)}` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs2:(num->num)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Fs1 UNION Fs2:(num->num)->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HJ_TILING_APPEND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN E /\ ~(x IN hj_tiling_union (k + 1) m (Fs1 UNION Fs2))} =
    {x | (x IN E /\ ~(x IN hj_tiling_union (k + 1) m Fs1)) /\
         ~(x IN hj_tiling_union (k + 1) m Fs2)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[HJ_TILING_UNION_UNION] THEN SET_TAC[]; ASM_REWRITE_TAC[]]);;

let HJ_TILING_INSENSITIVE = prove
 (`!k m beta i.
        1 <= k /\ density_hales_jewett k /\ 1 <= m /\ &0 < beta /\ i < k
        ==> ?N. !n D. N <= n /\ hj_insensitive (k + 1) n i k D
                      ==> ?Fs. hj_tiling (k + 1) m n Fs D /\
                               hj_density (k + 1) n
                                 {x | x IN D /\
                                  ~(x IN hj_tiling_union (k + 1) m Fs)}
                               < &2 * beta`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HJ_TILING_ITER) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`M1:num`; `Theta:real`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `Theta:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:num` o SPEC `&1`) THEN
  EXISTS_TAC `s * M1:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s:num`; `0`; `n - s * M1:num`; `D:(num->num)->bool`]) THEN
  SUBGOAL_THEN `0 + (s * M1 + (n - s * M1)) = n` SUBST1_TAC THENL
   [UNDISCH_TAC `s * M1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[HJ_CONCAT_0;
              SET_RULE `!s:(num->num)->bool. {x | x IN s} = s`] THEN
  SUBGOAL_THEN `s * M1 + (n - s * M1) = n:num` SUBST1_TAC THENL
   [UNDISCH_TAC `s * M1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`k + 1`; `n:num`; `D:(num->num)->bool`] HJ_DENSITY_LE_1) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tiling an intersection of insensitive sets (DKT Corollary 13).            *)
(* ------------------------------------------------------------------------- *)

let HJ_DENSITY_SUBADD = prove
 (`!q n A B C.
        (!x. x IN hj_cube q n /\ x IN A ==> x IN B \/ x IN C)
        ==> hj_density q n A <= hj_density q n B + hj_density q n C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `n:num`; `A:(num->num)->bool`;
                `B:(num->num)->bool`] HJ_DENSITY_SPLIT) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THEN MATCH_MP_TAC HJ_DENSITY_MONO THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let HJ_TILING_COMPOSE = prove
 (`!q m M n V1 B E P.
        1 <= q /\ hj_tiling q M n V1 E /\
        (!V. V IN V1 ==> hj_tiling q m M (B V) {a | hj_subst q V a IN P})
        ==> hj_tiling q m n {hj_subst q V W | V,W | V IN V1 /\ W IN B V}
                   {x | x IN E /\ x IN P}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!V W. V IN V1 /\ W IN B V
          ==> hj_subspace q M n V /\ hj_subspace q m M W /\
              hj_subspace q m n (hj_subst q V W) /\
              !a. a IN hj_cube q m
                  ==> hj_subst q W a IN hj_cube q M /\
                      hj_subst q V (hj_subst q W a) IN E /\
                      hj_subst q V (hj_subst q W a) IN P`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `V:num->num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[hj_tiling; IN_ELIM_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `hj_tiling q M n V1 E` THEN REWRITE_TAC[hj_tiling] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `hj_subspace q M n V /\ hj_subspace q m M (W:num->num)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `M:num` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `hj_subst q W a IN hj_cube q M` ASSUME_TAC THENL
       [MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC `m:num` THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[hj_tiling; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{z | hj_subspace q m n z}` THEN
    REWRITE_TAC[FINITE_HJ_SUBSPACES; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:num->num`; `V:num->num`; `W:num->num`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[HJ_SUBST_SUBST];
    SUBGOAL_THEN
     `!V W V' W' a a'. V IN V1 /\ W IN B V /\ V' IN V1 /\ W' IN B V' /\
                       a IN hj_cube q m /\ a' IN hj_cube q m /\
                       hj_subst q V (hj_subst q W a) =
                       hj_subst q V' (hj_subst q W' a')
                       ==> V = V' /\ W = W'`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN
        `hj_subst q W a IN hj_cube q M /\ hj_subst q W' a' IN hj_cube q M`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`q:num`; `M:num`; `n:num`; `V1:(num->num)->bool`;
                     `E:(num->num)->bool`; `V:num->num`; `V':num->num`;
                     `hj_subst q W a`; `hj_subst q W' a'`] HJ_TILING_INJ) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`q:num`; `m:num`; `M:num`;
                     `(B:(num->num)->(num->num)->bool) V'`;
                     `{a | hj_subst q V' a IN P}`; `W:num->num`; `W':num->num`;
                     `a:num->num`; `a':num->num`] HJ_TILING_INJ) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hj_subst q z a = hj_subst q z' a'` THEN
    ASM_REWRITE_TAC[HJ_SUBST_SUBST] THEN ASM_MESON_TAC[]]);;

let HJ_TILING_COMPOSE_DENS = prove
 (`!q m M n V1 B E P c.
        1 <= q /\ hj_tiling q M n V1 E /\ &0 <= c /\
        (!V. V IN V1
             ==> hj_density q M {a | hj_subst q V a IN P /\
                               ~(a IN hj_tiling_union q m (B V))} <= c)
        ==> hj_density q n {x | (x IN E /\ x IN P) /\
                          ~(x IN hj_tiling_union q m
                                 {hj_subst q V W | V,W | V IN V1 /\ W IN B V})}
            <= hj_density q n
              {x | x IN E /\ ~(x IN hj_tiling_union q M V1)} + c`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Fc = {hj_subst q V W | V,W | V IN V1 /\ W IN B V}` THEN
  ABBREV_TAC
    `L = {x | (x IN E /\ x IN P) /\ ~(x IN hj_tiling_union q m Fc)}` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `hj_density q n {x | x IN E /\ ~(x IN hj_tiling_union q M V1)} +
              hj_density q n {x | x IN hj_tiling_union q M V1 /\ x IN L}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HJ_DENSITY_SUBADD THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[REAL_LE_LADD]] THEN
  MP_TAC(ISPECL [`q:num`; `M:num`; `n:num`; `V1:(num->num)->bool`;
                 `E:(num->num)->bool`; `\x:num->num. x IN L`]
    HJ_DENSITY_TILING_UNION_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `FINITE(V1:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[hj_tiling]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(CARD(V1:(num->num)->bool)) * &(q EXP M) / &(q EXP n) <= &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:num`; `M:num`; `n:num`; `V1:(num->num)->bool`;
                   `E:(num->num)->bool`; `\x:num->num. T`]
      HJ_DENSITY_TILING_UNION_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hj_density q M {a:num->num | T} = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `hj_density q M (hj_cube q M)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC[IN_ELIM_THM];
                      ASM_SIMP_TAC[HJ_DENSITY_CUBE]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[HJ_DENSITY_LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(CARD(V1:(num->num)->bool)) * c) *
              &(q EXP M) / &(q EXP n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `V:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hj_density q M {a | hj_subst q V a IN P /\
      ~(a IN hj_tiling_union q m (B V))}` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC HJ_DENSITY_MONO THEN X_GEN_TAC `a:num->num` THEN
    EXPAND_TAC "L" THEN EXPAND_TAC "Fc" THEN
    REWRITE_TAC[hj_tiling_union; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`hj_subst q V z`; `a':num->num`] THEN
    ASM_REWRITE_TAC[HJ_SUBST_SUBST] THEN
    MAP_EVERY EXISTS_TAC [`V:num->num`; `z:num->num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(CARD(V1:(num->num)->bool)) * c) * &(q EXP M) / &(q EXP n) =
    c * (&(CARD V1) * &(q EXP M) / &(q EXP n))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let HJ_TILING_STRUCTURED = prove
 (`!k beta r m.
        1 <= k /\ density_hales_jewett k /\ &0 < beta /\ 1 <= r /\
        r <= k /\ 1 <= m
        ==> ?N. !n D.
                  N <= n /\ (!j. j < r ==> hj_insensitive (k + 1) n j k (D j))
                  ==> ?Fs. hj_tiling (k + 1) m n Fs {x | !j. j < r
                    ==> x IN D j} /\
                           hj_density (k + 1) n
                             {x | (!j. j < r ==> x IN D j) /\
                                  ~(x IN hj_tiling_union (k + 1) m Fs)}
                           <= &2 * &r * beta`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [ARITH_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `beta:real`; `r:num`]
           HJ_TILING_INSENSITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `SUC r <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  ASM_CASES_TAC `r = 0` THENL
   [EXISTS_TAC `N1:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `D:num->(num->num)->bool`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `(D:num->(num->num)->bool) r`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `j < SUC 0 <=> j = 0`; FORALL_UNWIND_THM2;
                    ARITH_RULE `j < 1 <=> j = 0`;
                    ARITH_RULE `SUC 0 = 1`;
                    SET_RULE `!s:(num->num)->bool. {x | x IN s} = s`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!a. a < &2 * beta ==> a <= &2 * &1 * beta`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `N1 + 1`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`SUC r <= k`; `~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N2:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `D:num->(num->num)->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `D:num->(num->num)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `j < r:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V1:(num->num)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!V. V IN V1
        ==> ?Fs. hj_tiling (k + 1) m (N1 + 1) Fs
                   {a | hj_subst (k + 1) V a IN (D:num->(num->num)->bool) r} /\
                 hj_density (k + 1) (N1 + 1)
                   {a | hj_subst (k + 1) V a IN D r /\
                        ~(a IN hj_tiling_union (k + 1) m Fs)} < &2 * beta`
  MP_TAC THENL
   [X_GEN_TAC `V:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`N1 + 1`;
      `{a | hj_subst (k + 1) V a IN (D:num->(num->num)->bool) r}`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `N1 <= N1 + 1`] THEN
      MATCH_MP_TAC HJ_INSENSITIVE_PULLBACK THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        ASM_MESON_TAC[hj_tiling]];
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:(num->num)->(num->num)->bool` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  EXISTS_TAC
   `{hj_subst (k + 1) V W | V,W | V IN V1 /\ W IN B V}` THEN
  SUBGOAL_THEN
   `!x. (!j. j < SUC r ==> x IN (D:num->(num->num)->bool) j) <=>
        x IN {x | !j. j < r ==> x IN D j} /\ x IN D r`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_ELIM_THM; LT] THEN MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HJ_TILING_COMPOSE THEN EXISTS_TAC `N1 + 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `hj_density (k + 1) n {x | x IN {x | !j. j < r:num ==> x IN D j} /\
                        ~(x IN hj_tiling_union (k + 1) (N1 + 1) V1)} +
                        &2 * beta` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HJ_TILING_COMPOSE_DENS THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; GSYM REAL_OF_NUM_SUC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a. a <= &2 * &r * beta ==> a + &2 * beta <= &2 * (&r + &1) * beta`) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* The density Hales-Jewett theorem: DENSITY_HALES_JEWETT, for every         *)
(* k >= 1 and delta > 0, every subset of [k]^n of density >= delta           *)
(* contains a combinatorial line once n is large enough.                     *)
(*                                                                           *)
(* * DKT_PROP6 (DKT Proposition 6): with beta = gamma^2 / (4 k), DKT         *)
(*   Corollary 11 gives W and insensitive D i, DKT Corollary 13 tiles        *)
(*   their intersection by d-dimensional subspaces up to density             *)
(*   gamma^2 / 2, and HJ_TILING_AVERAGE finds a d-dimensional subspace on    *)
(*   which a line-free A of density >= rho has density >= rho + gamma / 2.   *)
(* * DENSITY_HALES_JEWETT_STEP: density_hales_jewett k ==>                   *)
(*   density_hales_jewett (k + 1), iterating DKT_PROP6 through the           *)
(*   dimensions f (j + 1) = N(f j) + 1 (num_RECURSION) until the density     *)
(*   would exceed 1.  DENSITY_HALES_JEWETT_1 is trivial (the only point of   *)
(*   [1]^n is the zero word), so DENSITY_HALES_JEWETT follows by induction   *)
(*   on k.                                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The density increment (DKT Proposition 6).                                *)
(* ------------------------------------------------------------------------- *)

let DKT_PROP6 = prove
 (`!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta /\ delta <= &1
        ==> ?gam. &0 < gam /\
                  !d. 1 <= d
                      ==> ?N. !n A rho.
                                N <= n /\ delta <= rho /\
                                rho <= hj_density (k + 1) n A /\
                                ~hj_has_line (k + 1) n A
                                ==> ?z. hj_subspace (k + 1) d n z /\
                                        rho + gam <=
                                        hj_density (k + 1) d
                                          {a | hj_subst (k + 1) z a IN A}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `delta:real`] DKT_COR11) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma0:real` (X_CHOOSE_THEN `M0:num`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cor11")))) THEN
  EXISTS_TAC `gamma0 / &2` THEN
  ASM_REWRITE_TAC[REAL_ARITH `!x. &0 < x / &2 <=> &0 < x`] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `gamma0 pow 2 / (&4 * &k)`; `k:num`; `d:num`]
    HJ_TILING_STRUCTURED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N13:num`) THEN
  REMOVE_THEN "cor11" (MP_TAC o SPEC `MAX M0 N13`) THEN
  REWRITE_TAC[ARITH_RULE `M0 <= MAX M0 N13`] THEN
  ABBREV_TAC `m = MAX M0 N13` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`; `rho:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:(num->num)->bool`;
    `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->num`
   (X_CHOOSE_THEN `D:num->(num->num)->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `D:num->(num->num)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:(num->num)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `hj_density (k + 1) m (hj_tiling_union (k + 1) d Fs) <=
    hj_density (k + 1) m
      {x | x IN hj_cube (k + 1) m /\ !i. i < k ==> x IN D i}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HJ_DENSITY_MONO THEN
    MP_TAC(ISPECL [`k + 1`; `d:num`; `m:num`; `Fs:(num->num)->bool`;
                   `{x:num->num | !j. j < k ==>
                     x IN (D:num->(num->num)->bool) j}`]
                       HJ_TILING_UNION_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hj_density (k + 1) m
      {x | hj_subst (k + 1) W x IN A /\ !i. i < k ==> x IN D i} <=
    hj_density (k + 1) m {x | x IN hj_tiling_union (k + 1) d Fs /\
                        x IN {x | hj_subst (k + 1) W x IN A}} +
    hj_density (k + 1) m {x | (!j. j < k ==> x IN D j) /\
                        ~(x IN hj_tiling_union (k + 1) d Fs)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HJ_DENSITY_SUBADD THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &k * gamma0 pow 2 / (&4 * &k) = gamma0 pow 2 / &2`
  ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC
   `dD = hj_density (k + 1) m {x | x IN hj_cube (k + 1) m /\ !i. i < k ==>
     x IN D i}` THEN
  ABBREV_TAC
   `dAD = hj_density (k + 1) m {x | hj_subst (k + 1) W x IN A /\
                              !i. i < k ==> x IN D i}` THEN
  ABBREV_TAC
   `dL = hj_density (k + 1) m {x | (!j. j < k ==> x IN D j) /\
                             ~(x IN hj_tiling_union (k + 1) d Fs)}` THEN
  ABBREV_TAC `dT = hj_density (k + 1) m (hj_tiling_union (k + 1) d Fs)` THEN
  ABBREV_TAC
   `dTA = hj_density (k + 1) m {x | x IN hj_tiling_union (k + 1) d Fs /\
                              x IN {x | hj_subst (k + 1) W x IN A}}` THEN
  SUBGOAL_THEN `&0 <= rho` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(rho + gamma0 / &2) * dT <= (rho + gamma0 / &2) * dD /\
    (rho + gamma0) * gamma0 <= (rho + gamma0) * dD /\
    gamma0 * gamma0 <= gamma0 * dD /\ &0 < gamma0 * gamma0 /\
    &0 <= rho * gamma0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho + gamma0 / &2) * dT <= dTA /\ &0 < dTA`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&2 * &k * gamma0 pow 2 / (&4 * &k) = gamma0 pow 2 / &2` THEN
    REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + 1`; `d:num`; `m:num`; `Fs:(num->num)->bool`;
                 `{x:num->num | !j. j < k ==>
                   x IN (D:num->(num->num)->bool) j}`;
                 `{x | hj_subst (k + 1) W x IN A}`; `rho + gamma0 / &2`]
    HJ_TILING_AVERAGE) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN ANTS_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&0 < dTA` THEN EXPAND_TAC "dTA" THEN
    REWRITE_TAC[HJ_TILING_UNION_EMPTY; NOT_IN_EMPTY; EMPTY_GSPEC] THEN
    MP_TAC(SPECL [`k + 1`; `m:num`;
      `{}:(num->num)->bool`] HJ_DENSITY_POS_EXISTS) THEN
    REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hj_subst (k + 1) W z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN ASM_MESON_TAC[hj_tiling];
    UNDISCH_TAC `rho + gamma0 / &2 <=
                 hj_density (k + 1) d {a | hj_subst (k + 1) z a IN
                                     {x | hj_subst (k + 1) W x IN A}}` THEN
    REWRITE_TAC[IN_ELIM_THM; HJ_SUBST_SUBST]]);;

(* ------------------------------------------------------------------------- *)
(* The density Hales-Jewett theorem.                                         *)
(* ------------------------------------------------------------------------- *)

let DENSITY_HALES_JEWETT_STEP = prove
 (`!k. 1 <= k /\ density_hales_jewett k ==> density_hales_jewett (k + 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[density_hales_jewett] THEN
  X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `delta <= &1` THENL
   [ALL_TAC;
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`k + 1`; `n:num`; `A:(num->num)->bool`] HJ_DENSITY_LE_1) THEN
    ASM_REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `delta:real`] DKT_PROP6) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Nf:num->num` (LABEL_TAC "prop6") o
             GEN_REWRITE_RULE I [SKOLEM_THM] o
             GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  MP_TAC(ISPECL [`1`; `\(d:num) (j:num). (Nf:num->num) d + 1`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!j. 1 <= (f:num->num) j` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j n A rho. (f:num->num) j <= n /\ delta <= rho /\
                rho <= hj_density (k + 1) n A
                ==> hj_has_line (k + 1) n A \/ rho + &j * gam <= &1`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN DISJ2_TAC THEN
      MP_TAC(SPECL [`k + 1`; `n:num`; `A:(num->num)->bool`]
               HJ_DENSITY_LE_1) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN ASM_REAL_ARITH_TAC;
      POP_ASSUM(LABEL_TAC "ih")] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`; `rho:real`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `hj_has_line (k + 1) n A` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "prop6" (MP_TAC o SPEC `(f:num->num) j`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `A:(num->num)->bool`; `rho:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(f:num->num) (SUC j) <= n` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num->num` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL
     [`(f:num->num) j`; `{a | hj_subst (k + 1) z a IN A}`;
      `rho + gam:real`]) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`k + 1`; `(f:num->num) j`; `n:num`; `z:num->num`;
                     `A:(num->num)->bool`] HJ_HAS_LINE_PULLBACK) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`];
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `gam:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num` o SPEC `&1`) THEN
  EXISTS_TAC `(f:num->num) j` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(delta + &j * gam <= &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`j:num`; `n:num`; `A:(num->num)->bool`; `delta:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let DENSITY_HALES_JEWETT_1 = prove
 (`density_hales_jewett 1`,
  REWRITE_TAC[density_hales_jewett] THEN X_GEN_TAC `delta:real` THEN
  DISCH_TAC THEN
  EXISTS_TAC `1` THEN MAP_EVERY X_GEN_TAC [`n:num`; `A:(num->num)->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `n:num`; `A:(num->num)->bool`] HJ_DENSITY_POS_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x = (\i:num. 0)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN UNDISCH_TAC `(x:num->num) IN hj_cube 1 n` THEN
    REWRITE_TAC[IN_HJ_CUBE] THEN
    MESON_TAC[ARITH_RULE `a < 1 <=> a = 0`; NOT_LE];
    ALL_TAC] THEN
  REWRITE_TAC[hj_has_line] THEN
  EXISTS_TAC `\i:num. if i < n then 1 else 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[hj_line; hj_subspace; IN_HJ_CUBE;
                ARITH_RULE `j < 1 <=> j = 0`] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; ADD_CLAUSES] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC;
      GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      EXISTS_TAC `0` THEN ASM_ARITH_TAC];
    REWRITE_TAC[ARITH_RULE `a < 1 <=> a = 0`; FORALL_UNWIND_THM2] THEN
    SUBGOAL_THEN
      `hj_line_point 1 (\i:num. if i < n then 1 else 0) 0 = (\i:num. 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[hj_line_point; hj_subst; FUN_EQ_THM; COND_ID] THEN
      X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < n:num` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[]]]);;

let DENSITY_HALES_JEWETT = prove
 (`!k. 1 <= k ==> density_hales_jewett k`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(1 <= 0)`] THEN
  ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; DENSITY_HALES_JEWETT_1] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ADD1] THEN MATCH_MP_TAC DENSITY_HALES_JEWETT_STEP THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* The weighted Szemeredi theorem in Z_N from density Hales-Jewett.          *)
(* weighted_szemeredi k says that every f : Z_N -> [0, 1] with               *)
(* E f >= delta has                                                          *)
(*   AP_k(f) = E_{a,d < N} prod_{j<k} f((a + j d) mod N) >= c(delta) > 0     *)
(* for all large primes N; WEIGHTED_SZEMEREDI: weighted_szemeredi k for      *)
(* every k >= 1.                                                             *)
(*                                                                           *)
(* * FMEAN_AP_AFFINE: for N prime and s a unit mod N, the means over         *)
(*   t, d < N of prod_{j<k} h((t + d (s0 + j s)) mod N) equal AP_k(h)        *)
(*   (FMEAN_SHIFT_MOD for t, FMEAN_DIL_MOD for d).                           *)
(* * A line l of [k]^n has nsum (hj_line_point k l j) = s0 + j w with        *)
(*   0 < w <= n (NSUM_HJ_LINE_POINT), so for N prime > n the indicator       *)
(*   products along l average to AP_k(1_A) (FMEAN_HJ_LINE_AP).               *)
(* * SZEMEREDI_AP_INDICATOR_BOUND: if A has density >= delta in Z_N, the     *)
(*   sets B(t, d) = {x | (t + d nsum x) mod N IN A} of [k]^n have mean       *)
(*   density >= delta (FMEAN_HJ_DENSITY_AFFINE), so a proportion             *)
(*   >= delta / 2 of them contain a line by density_hales_jewett k at        *)
(*   delta / 2 (HJ_LINE_COUNT_BOUND); summing over the lines,                *)
(*   AP_k(1_A) >= delta / 2 / (k + 1)^n.                                     *)
(* * WEIGHTED_SZEMEREDI_DHJ: density_hales_jewett k ==>                      *)
(*   weighted_szemeredi k, applying SZEMEREDI_AP_INDICATOR_BOUND to          *)
(*   A = {y | f y >= delta / 2} and AP_k(f) >= (delta / 2)^k AP_k(1_A);      *)
(*   WEIGHTED_SZEMEREDI follows with DENSITY_HALES_JEWETT.                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The weighted Szemeredi property.                                          *)
(* ------------------------------------------------------------------------- *)

let weighted_szemeredi = new_definition
 `weighted_szemeredi k <=>
    !delta. &0 < delta
            ==> ?c N0. &0 < c /\
                !N f. N0 <= N /\ prime N /\
                      (!y. y < N ==> &0 <= f y /\ f y <= &1) /\
                      delta <= fmean {y | y < N} f
                      ==> c <= fmean {a | a < N}
                                 (\a. fmean {d | d < N}
                                        (\d. product {j | j < k}
                                               (\j. f((a + j * d) MOD N))))`;;

(* ------------------------------------------------------------------------- *)
(* Affine changes of variables in means over Z_N.                            *)
(* ------------------------------------------------------------------------- *)

let MOD_AFFINE_MOD = prove
 (`!N a b j. (a MOD N + j * (b MOD N)) MOD N = (a + j * b) MOD N`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN REFL_TAC);;

let FMEAN_DIL_MOD = prove
 (`!N s (g:num->real).
        ~(N = 0) /\ coprime(s,N)
        ==> fmean {d | d < N} (\d. g((d * s) MOD N)) = fmean {d | d < N} g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`g:num->real`; `\d. (d * s) MOD N`; `{d:num | d < N}`]
    SUM_INJECTION) THEN
  REWRITE_TAC[o_DEF; IN_ELIM_THM; FINITE_NUMSEG_LT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[CONG; MOD_LT]
   `!x y n:num. x < n /\ y < n /\ (x == y) (mod n) ==> x = y`) THEN
  EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`s:num`; `N:num`] CONG_MULT_RCANCEL_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CONG]);;

let FMEAN_AP_AFFINE = prove
 (`!N k s s0 (h:num->real).
        ~(N = 0) /\ coprime(s,N)
        ==> fmean {t | t < N}
              (\t. fmean {d | d < N}
                     (\d. product {j | j < k}
                            (\j. h((t + d * (s0 + j * s)) MOD N)))) =
            fmean {a | a < N}
              (\a. fmean {e | e < N}
                     (\e. product {j | j < k} (\j. h((a + j * e) MOD N))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean {d | d < N}
      (\d. fmean {t | t < N}
             (\t. product {j | j < k}
                    (\j. (h:num->real)((t + d * (s0 + j * s)) MOD N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean {d | d < N}
      (\d. fmean {a | a < N}
             (\a. product {j | j < k}
                    (\j. (h:num->real)((a + j * ((d * s) MOD N))
                      MOD N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`N:num`; `d * s0:num`;
                   `\a. product {j | j < k}
                          (\j. (h:num->real)((a + j * ((d * s)
                            MOD N)) MOD N))`]
      FMEAN_SHIFT_MOD) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[MOD_AFFINE_MOD] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean {a | a < N}
      (\a. fmean {d | d < N}
             (\d. product {j | j < k}
                    (\j. (h:num->real)((a + j * ((d * s) MOD N))
                      MOD N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`N:num`; `s:num`;
    `\e. product {j | j < k} (\j. (h:num->real)((a + j * e) MOD N))`]
   FMEAN_DIL_MOD)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lines of [k]^n along progressions mod N.                                  *)
(* ------------------------------------------------------------------------- *)

let NSUM_HJ_LINE_POINT_GEN = prove
 (`!k n l (g:num->num) a.
        hj_line k n l
        ==> nsum {r | r < n} (\r. g(hj_line_point k l a r)) =
            nsum {r | r < n} (\r. if l r < k then g(l r) else 0) +
            CARD {r | r < n /\ l r = k} * g a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < n ==> (l:num->num) i <= k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HJ_LINE_CUBE) THEN
    REWRITE_TAC[IN_HJ_CUBE] THEN
    MESON_TAC[ARITH_RULE `x < k + 1 <=> x <= k`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum {r | r < n} (\r. (g:num->num)(hj_line_point k l a r)) =
    nsum {r | r < n} (\r. (if (l:num->num) r < k then g(l r) else 0) +
                          (if l r = k then g a else 0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[hj_line_point; hj_subst] THEN
    ASM_CASES_TAC `(l:num->num) i < k` THEN
    ASM_SIMP_TAC[ARITH_RULE `x < k:num ==> ~(x = k)`; ADD_CLAUSES] THEN
    SUBGOAL_THEN `(l:num->num) i = k` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[SUB_REFL; ADD_CLAUSES]];
    ALL_TAC] THEN
  SIMP_TAC[NSUM_ADD; FINITE_NUMSEG_LT] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `nsum {r | r < n} (\r. if (l:num->num) r = k then (g:num->num) a else 0) =
    nsum {r | r IN {r | r < n} /\ l r = k} (\r. g a)`
  SUBST1_TAC THENL [REWRITE_TAC[NSUM_RESTRICT_SET]; ALL_TAC] THEN
  SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM]);;

let HJ_LINE_WILDCARDS = prove
 (`!k n l. hj_line k n l
           ==> 0 < CARD {r | r < n /\ l r = k} /\
               CARD {r | r < n /\ l r = k} <= n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {r | r < n /\ (l:num->num) r = k}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[LT_NZ; CARD_EQ_0] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    ASM_MESON_TAC[HJ_LINE_VAR];
    GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let NSUM_HJ_LINE_POINT = prove
 (`!k n l. hj_line k n l
           ==> ?s0 w. 0 < w /\ w <= n /\
                      !a. nsum {i | i < n} (hj_line_point k l a) = s0 + a * w`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`nsum {r | r < n} (\r. if (l:num->num) r < k then l r else 0)`;
    `CARD {r | r < n /\ (l:num->num) r = k}`] THEN
  ASM_SIMP_TAC[HJ_LINE_WILDCARDS] THEN X_GEN_TAC `a:num` THEN
  MP_TAC(ISPECL [`k:num`; `n:num`; `l:num->num`; `\x:num. x`; `a:num`]
    NSUM_HJ_LINE_POINT_GEN) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MULT_SYM]);;

let FMEAN_HJ_DENSITY_AFFINE = prove
 (`!k n N (A:num->bool).
        1 <= k /\ ~(N = 0)
        ==> fmean {t | t < N}
              (\t. fmean {d | d < N}
                     (\d. hj_density k n
                            {x | (t + d * nsum {i | i < n} x) MOD N IN A})) =
            fmean {y:num | y < N} (\y. if y IN A then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
  SUBGOAL_THEN `FINITE {y:num | y < N} /\ ~({y:num | y < N} = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean {d | d < N}
      (\d. fmean {t | t < N}
             (\t. fmean (hj_cube k n)
                    (\x. if (t + d * nsum {i | i < n} x) MOD N IN A
                         then &1 else &0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean {d | d < N}
      (\d:num. fmean {y:num | y < N} (\y. if y IN A then &1 else &0))` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC FMEAN_CONST THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean (hj_cube k n)
      (\x. fmean {t | t < N}
             (\t. if (t + d * nsum {i | i < n} x) MOD N IN A
                  then &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_SWAP2 THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_HJ_CUBE];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean (hj_cube k n)
      (\x:num->num. fmean {y:num | y < N} (\y. if y IN A then &1
        else &0))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FMEAN_CONST THEN
      ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY]] THEN
  MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean {t | t < N}
      (\t. (\y. if y IN A then &1 else &0)
           ((d * nsum {i | i < n} (x:num->num) + t) MOD N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ADD_SYM];
    ACCEPT_TAC(ISPECL [`N:num`; `d * nsum {i | i < n} (x:num->num)`;
                       `\y:num. if y IN A then &1 else &0`]
                         FMEAN_SHIFT_MOD)]);;

let FMEAN_HJ_LINE_AP = prove
 (`!k n N l (A:num->bool).
        prime N /\ n < N /\ hj_line k n l
        ==> fmean {t | t < N}
              (\t. fmean {d | d < N}
                     (\d. product {j | j < k}
                            (\j. if (t + d *
                                     nsum {i | i < n} (hj_line_point k l j))
                                    MOD N IN A then &1 else &0))) =
            fmean {a | a < N}
              (\a. fmean {e | e < N}
                     (\e. product {j | j < k}
                            (\j. if (a + j * e) MOD N IN A
                                 then &1 else &0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NSUM_HJ_LINE_POINT) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:num` (X_CHOOSE_THEN `w:num`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`N:num`; `k:num`; `w:num`; `s0:num`; `\y:num. if y IN A then &1 else &0`]
   FMEAN_AP_AFFINE)) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_0];
    MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Progressions in a dense subset of Z_N from density Hales-Jewett.          *)
(* ------------------------------------------------------------------------- *)

let HJ_LINE_COUNT_BOUND = prove
 (`!k n N (A:num->bool) t d delta.
        (!B. delta <= hj_density k n B ==> hj_has_line k n B) /\ &0 <= delta
        ==> hj_density k n
              {x | (t + d * nsum {i | i < n} x) MOD N IN A} - delta <=
            sum {l | hj_line k n l}
              (\l. product {j | j < k}
                     (\j. if (t + d *
                              nsum {i | i < n}
                                (hj_line_point k l j)) MOD N IN A
                          then &1 else &0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {l | hj_line k n l}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `hj_cube (k + 1) n` THEN
    REWRITE_TAC[FINITE_HJ_CUBE; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[HJ_LINE_CUBE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. &0 <= product {j | j < k}
                (\j. if (t + d *
                         nsum {i | i < n} (hj_line_point k l j)) MOD N IN A
                     then &1 else &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `B = {x:num->num | (t + d * nsum {i:num | i < n} x) MOD N IN A}` THEN
  ASM_CASES_TAC `delta <= hj_density k n B` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SUM_POS_LE] THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `B:(num->num)->bool`) THEN
  ASM_REWRITE_TAC[hj_has_line] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num->num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`k:num`; `n:num`; `B:(num->num)->bool`] HJ_DENSITY_LE_1) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `product {j | j < k}
      (\j. if (t + d * nsum {i | i < n} (hj_line_point k l j)) MOD N IN A
           then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\l. product {j | j < k}
           (\j. if (t + d * nsum {i | i < n} (hj_line_point k l j)) MOD N IN A
                then &1 else &0)`;
    `{l | hj_line k n l}`; `l:num->num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c. &0 <= a ==> a = b - c ==> c <= b`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FINITE_DELETE]);;

let SZEMEREDI_AP_INDICATOR_BOUND = prove
 (`!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta
        ==> ?n. !N (A:num->bool).
                  prime N /\ n < N /\
                  delta <= fmean {y | y < N} (\y. if y IN A then &1 else &0)
                  ==> delta / &2 / &((k + 1) EXP n) <=
                      fmean {a | a < N}
                        (\a. fmean {e | e < N}
                               (\e. product {j | j < k}
                                      (\j. if (a + j * e) MOD N IN A
                                           then &1 else &0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `delta / &2`
                o REWRITE_RULE[density_hales_jewett]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `!x. &0 < x / &2 <=> &0 < x`] THEN
  DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN EXISTS_TAC `n0:num` THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `A:num->bool`] THEN STRIP_TAC THEN
  ABBREV_TAC `aA = fmean {y:num | y < N} (\y. if y IN A then &1 else &0)` THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {y:num | y < N} /\ ~({y:num | y < N} = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {l | hj_line k n0 l} /\
    &(CARD {l | hj_line k n0 l}) <= &((k + 1) EXP n0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `{l | hj_line k n0 l} SUBSET hj_cube (k + 1) n0`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[HJ_LINE_CUBE];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_HJ_CUBE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM CARD_HJ_CUBE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_HJ_CUBE];
    ALL_TAC] THEN
  ABBREV_TAC
   `ap = fmean {a | a < N}
           (\a. fmean {e | e < N}
                  (\e. product {j | j < k}
                         (\j. if (a + j * e) MOD N IN A then &1
                           else &0)))` THEN
  SUBGOAL_THEN `&0 <= ap` ASSUME_TAC THENL
   [EXPAND_TAC "ap" THEN MATCH_MP_TAC FMEAN_POS THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FMEAN_POS THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aA - delta / &2 <=
    &(CARD {l | hj_line k n0 l}) * ap`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `fmean {t | t < N}
        (\t. fmean {d | d < N}
               (\d. hj_density k n0
                      {x | (t + d * nsum {i | i < n0} x) MOD N IN A} -
                    delta / &2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      ASM_SIMP_TAC[FMEAN_SUB; FINITE_NUMSEG_LT; FMEAN_CONST;
                   FMEAN_HJ_DENSITY_AFFINE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `fmean {t | t < N}
        (\t. fmean {d | d < N}
               (\d. sum {l | hj_line k n0 l}
                      (\l. product {j | j < k}
                             (\j. if (t + d *
                                      nsum {i | i < n0} (hj_line_point k l j))
                                     MOD N IN A then &1 else &0))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      X_GEN_TAC `d:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC HJ_LINE_COUNT_BOUND THEN
      CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ASM_SIMP_TAC[FMEAN_SUM; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {l | hj_line k n0 l} (\l. ap)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num->num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "ap" THEN
      MATCH_MP_TAC FMEAN_HJ_LINE_AP THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SUM_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &((k + 1) EXP n0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`delta / &2`; `ap:real`; `&((k + 1) EXP n0)`]
    REAL_LE_LDIV_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `cL = &(CARD {l | hj_line k n0 l})` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cL * ap:real` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The weighted Szemeredi theorem.                                           *)
(* ------------------------------------------------------------------------- *)

let WEIGHTED_SZEMEREDI_DHJ = prove
 (`!k. 1 <= k /\ density_hales_jewett k ==> weighted_szemeredi k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[weighted_szemeredi] THEN
  X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `delta / &2`] SZEMEREDI_AP_INDICATOR_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ARITH `!x. &0 < x / &2 <=> &0 < x`] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `(delta / &2) pow k * (delta / &2 / &2 / &((k + 1) EXP n))` THEN
  EXISTS_TAC `n + 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN
      REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `f:num->real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `n + 1 <= N` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {y:num | y < N} /\ ~({y:num | y < N} = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = {y | delta / &2 <= (f:num->real) y}` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `A:num->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a b. delta <= b /\ b <= a + delta / &2 ==> delta / &2 <= a`) THEN
    EXISTS_TAC `fmean {y:num | y < N} (f:num->real)` THEN
      ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fmean {y:num | y < N}
                  (\y. (if y IN A then &1 else &0) + delta / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `y:num` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[FMEAN_ADD; FMEAN_CONST; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(delta / &2) pow k *
    fmean {a | a < N}
      (\a. fmean {e | e < N}
             (\e. product {j | j < k}
                    (\j. if (a + j * e) MOD N IN A then &1 else &0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM FMEAN_LMUL] THEN
  MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `product {j | j < k}
      (\j. delta / &2 * (if (a + j * e) MOD N IN A then &1 else &0))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a + j * e) MOD N` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `f:num->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ] THEN EXPAND_TAC "A" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let WEIGHTED_SZEMEREDI = prove
 (`!k. 1 <= k ==> weighted_szemeredi k`,
  MESON_TAC[WEIGHTED_SZEMEREDI_DHJ; DENSITY_HALES_JEWETT]);;

(* ========================================================================= *)
(* Szemeredi's theorem in its common forms, with the multidimensional and    *)
(* colouring versions and the corners theorem.                               *)
(*                                                                           *)
(* * SZEMEREDI_COUNT (Varnavides): for k >= 2 and delta > 0 there is c > 0   *)
(*   such that every A SUBSET 1..N with |A| >= delta N, N large, contains    *)
(*   at least c N^2 progressions a, a + d, ..., a + (k - 1) d with d > 0.    *)
(*   From WEIGHTED_SZEMEREDI in Z_P for a prime P in (2 N, 4 N]              *)
(*   (BERTRAND): the terms with d = 0 contribute at most P                   *)
(*   (AP_COUNT_NONTRIVIAL), and a progression mod P inside [0, P/2) is a     *)
(*   genuine increasing or decreasing progression (MOD_AP_CASES), at most    *)
(*   two pairs mod P per progression (PROGRESSIONS_FROM_PAIRS, stated for    *)
(*   the terms W y + b and any property Q of them).                          *)
(* * SZEMEREDI (the finite form), ROTH (k = 3), SZEMEREDI_DENSITY (every     *)
(*   set of positive upper density contains progressions of every length)    *)
(*   and VAN_DER_WAERDEN (every finite colouring of 1..N, N large, has a     *)
(*   monochromatic k-term progression).                                      *)
(* * MULTIDIM_SZEMEREDI (Furstenberg-Katznelson): for every finite pattern   *)
(*   v_0, ..., v_(k-1) in N^d and delta > 0, every A SUBSET [0, M)^d of      *)
(*   density >= delta, M large, contains a homothetic copy                   *)
(*   {a + lm v_j | j < k} with lm > 0.  From DENSITY_HALES_JEWETT: a word    *)
(*   x over the letters 0, ..., k (0 for the origin, j + 1 for v_j) is       *)
(*   sent to t + sum_r u(x_r) mod 2 M; averaging over t                      *)
(*   (FMEAN_SHIFT_HJ_CUBE, HJ_DENSITY_SHIFT_MEAN) some t gives a dense set   *)
(*   of words, one of its lines gives a copy mod 2 M, and since all its      *)
(*   points lie in [0, M)^d the copy is genuine.                             *)
(* * GALLAI_WITT (the colouring version) and CORNERS (Ajtai-Szemeredi:       *)
(*   every dense A SUBSET [0, M)^2 contains a corner (x, y), (x + lm, y),    *)
(*   (x, y + lm) with lm > 0).                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Progressions mod N and genuine progressions.                              *)
(* ------------------------------------------------------------------------- *)

let CARD_PAIRS_SUM = prove
 (`!N (P:num->num->bool).
        &(CARD {(a,d) | a < N /\ d < N /\ P a d}) =
        sum {a | a < N} (\a. sum {d | d < N} (\d. if P a d then &1 else &0))`,
  REPEAT GEN_TAC THEN SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `{(a,d) | a < N /\ d < N /\ (P:num->num->bool) a d} =
    {x | x IN {i,j | i IN {a:num | a < N} /\ j IN {d:num | d < N}} /\
         P (FST x) (SND x)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    REWRITE_TAC[FST; SND; CONJ_ASSOC];
    ALL_TAC] THEN
  SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; FINITE_PRODUCT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM]);;

let AP_COUNT_NONTRIVIAL = prove
 (`!k N (f:num->real) B.
        1 <= N /\ (!y. y < N ==> &0 <= f y /\ f y <= B)
        ==> &N pow 2 *
            fmean {a | a < N}
              (\a. fmean {d | d < N}
                     (\d. product {j | j < k} (\j. f((a + j * d) MOD N))))
            <= &N * B pow k +
               &(CARD {(a,d) | a < N /\ 0 < d /\ d < N /\
                               !j. j < k ==> &0 < f((a + j * d) MOD N)}) *
               B pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y. &0 <= (f:num->real)(y MOD N) /\ f(y MOD N) <= B`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y MOD N`) THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= N ==> ~(N = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{(a,d) | a < N /\ 0 < d /\ d < N /\
             !j. j < k ==> &0 < (f:num->real)((a + j * d) MOD N)} =
    {(a,d) | a < N /\ d < N /\
             (0 < d /\ !j. j < k ==> &0 < f((a + j * d) MOD N))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CARD_PAIRS_SUM] THEN
  SUBGOAL_THEN
   `&N pow 2 *
    fmean {a | a < N}
      (\a. fmean {d | d < N}
             (\d. product {j | j < k} (\j. (f:num->real)((a + j *
               d) MOD N)))) =
    sum {a | a < N}
      (\a. sum {d | d < N}
             (\d. product {j | j < k} (\j. f((a + j * d) MOD N))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[fmean; CARD_NUMSEG_LT; real_div; SUM_RMUL] THEN
    MATCH_MP_TAC(REAL_FIELD
     `!n x. ~(n = &0) ==> n pow 2 * (x * inv n) * inv n = x`) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&N * B pow k = sum {a | a < N}
                     (\a. sum {d | d < N} (\d. if d = 0 then B pow k else &0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= N ==> 0 < N`; SUM_CONST; FINITE_NUMSEG_LT;
                 CARD_NUMSEG_LT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  SIMP_TAC[GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  ABBREV_TAC
   `P = product {j | j < k} (\j. (f:num->real)((a + j * d) MOD N))` THEN
  SUBGOAL_THEN `P <= B pow k` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product {j:num | j < k} (\j. B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
      SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT;
               REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[LT_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_NZ] THEN
  ASM_CASES_TAC `!j. j < k ==> &0 < (f:num->real)((a + j * d) MOD N)` THEN
  ASM_REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID; REAL_MUL_LZERO] THEN
  EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[NOT_IMP] THEN
  ASM_MESON_TAC[REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`]);;

let MOD_AP_LINEAR = prove
 (`!k N a d (n:num->num).
        2 <= k /\ 0 < d /\ d < N /\
        (!j. j < k ==> n j = (a + j * d) MOD N /\ 2 * n j < N)
        ==> ~(n 1 = n 0) /\
            !j. j < k ==> &(n j):int = &(n 0) + &j * (&(n 1) - &(n 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j + 1 < k ==> (&(n (j + 1)) - &(n j) == &d:int) (mod &N)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(&(n (j + 1)) == &(a + (j + 1) * d):int) (mod &N) /\
      (&(n j) == &(a + j * d):int) (mod &N)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM num_congruent] THEN
      ASM_SIMP_TAC[ARITH_RULE `j + 1 < k ==> j < k`; CONG_LMOD; CONG;
                   MOD_MOD_REFL];
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
      CONV_TAC INTEGER_RULE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < k ==> 2 * (n:num->num) j < N` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&(n 1) - &(n 0) == &d:int) (mod &N)` ASSUME_TAC THENL
   [MP_TAC(SPEC `0` (ASSUME
     `!j. j + 1 < k ==> (&((n:num->num) (j + 1)) - &(n j) == &d:int)
                        (mod &N)`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e0:int = &(n 1) - &(n 0)` THEN
  SUBGOAL_THEN `!j. j + 1 < k ==> &(n (j + 1)) - &(n j):int = e0`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "e0" THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&N:int` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `2 * (n:num->num) j < N /\ 2 * n (j + 1) < N /\
                    2 * n 0 < N /\ 2 * n 1 < N` MP_TAC THENL
       [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL] THEN
      MP_TAC(SPEC `n (j:num):num` INT_POS) THEN
      MP_TAC(SPEC `n (j + 1):num` INT_POS) THEN
      MP_TAC(SPEC `n 0:num` INT_POS) THEN
      MP_TAC(SPEC `n 1:num` INT_POS) THEN INT_ARITH_TAC;
      MATCH_MP_TAC(INTEGER_RULE
       `!x y d n:int. (x == d) (mod n) /\ (y == d) (mod n)
                      ==> (x == y) (mod n)`) THEN
      EXISTS_TAC `&d:int` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e0:int = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(e0 == &d:int) (mod &N)` THEN
    ASM_REWRITE_TAC[GSYM num_congruent] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`0`; `d:num`; `N:num`] (MESON[CONG; MOD_LT]
   `!x y n:num. x < n /\ y < n /\ (x == y) (mod n) ==> x = y`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(e0:int = &0)` THEN EXPAND_TAC "e0" THEN
    UNDISCH_TAC `(n:num->num) 1 = n 0` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_SUB_REFL];
    ALL_TAC] THEN
  INDUCT_TAC THENL [REWRITE_TAC[INT_MUL_LZERO; INT_ADD_RID]; ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `j:num < k ==> &(n j):int = &(n 0) + &j * e0` THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `j:num`
   (ASSUME `!j. j + 1 < k
                ==> &((n:num->num) (j + 1)) - &(n j):int = e0`)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let MOD_AP_CASES = prove
 (`!k N a d.
        2 <= k /\ a < N /\ 0 < d /\ d < N /\
        (!j. j < k ==> 2 * ((a + j * d) MOD N) < N)
        ==> ~((a + d) MOD N = a) /\
            (a < (a + d) MOD N
             ==> !j. j < k
                     ==> (a + j * d) MOD N = a + j * ((a + d) MOD N - a)) /\
            ((a + d) MOD N < a
             ==> !j. j < k
                     ==> (a + j * d) MOD N + j * (a - (a + d) MOD N) = a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `a:num`; `d:num`;
                 `\j. (a + j * d) MOD N`] MOD_AP_LINEAR) THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; MOD_LT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
              GSYM INT_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC);;

let MOD_ADD_LCANCEL = prove
 (`!N a d d'. d < N /\ d' < N /\ (a + d) MOD N = (a + d') MOD N ==> d = d'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CONG] THEN
  REWRITE_TAC[NUMBER_RULE
   `!a n x y:num. (a + x == a + y) (mod n) <=> (x == y) (mod n)`] THEN
  MESON_TAC[CONG; MOD_LT]);;

let SZEMEREDI_UP_PROGRESSION = prove
 (`!k N W b X a d (ok:num->bool) (Q:num->bool).
        2 <= k /\ 1 <= W /\
        (!y. ok y ==> 2 * y < N /\ Q(W * y + b) /\ W * y + b <= X) /\
        a < N /\ 0 < d /\ d < N /\ (!j. j < k ==> ok((a + j * d) MOD N)) /\
        a < (a + d) MOD N
        ==> 0 < W * ((a + d) MOD N - a) /\
            (W * a + b) + (k - 1) * (W * ((a + d) MOD N - a)) <= X /\
            !j. j < k
                ==> Q((W * a + b) + j * (W * ((a + d) MOD N - a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `a:num`; `d:num`] MOD_AP_CASES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e = (a + d) MOD N - a` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!j. (W * a + b) + j * (W * e) = W * (a + j * e) + b:num`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC NUM_RING; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LT_MULT] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a + (k - 1) * d) MOD N` o
      check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `ok:num->bool`)) (concl th) &&
                       can (find_term ((=) `Q:num->bool`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a + j * d) MOD N` o
      check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `ok:num->bool`)) (concl th) &&
                       can (find_term ((=) `Q:num->bool`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC; SIMP_TAC[]]]);;

let SZEMEREDI_DOWN_PROGRESSION = prove
 (`!k N W b X a d (ok:num->bool) (Q:num->bool).
        2 <= k /\ 1 <= W /\
        (!y. ok y ==> 2 * y < N /\ Q(W * y + b) /\ W * y + b <= X) /\
        a < N /\ 0 < d /\ d < N /\ (!j. j < k ==> ok((a + j * d) MOD N)) /\
        (a + d) MOD N < a
        ==> (a + (k - 1) * d) MOD N + (k - 1) * (a - (a + d) MOD N) = a /\
            0 < W * (a - (a + d) MOD N) /\
            (W * ((a + (k - 1) * d) MOD N) + b) +
            (k - 1) * (W * (a - (a + d) MOD N)) <= X /\
            !j. j < k
                ==> Q((W * ((a + (k - 1) * d) MOD N) + b) +
                          j * (W * (a - (a + d) MOD N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `a:num`; `d:num`] MOD_AP_CASES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e = a - (a + d) MOD N` THEN
  ABBREV_TAC `u = (a + (k - 1) * d) MOD N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `u + (k - 1) * e = a` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j. (W * u + b) + j * (W * e) = W * (u + j * e) + b:num`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC NUM_RING; ALL_TAC] THEN
  SUBGOAL_THEN `!y. ok y ==> W * y + b <= X /\ (Q:num->bool)(W * y + b)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ok:num->bool) a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      can (find_term ((=) `(a + j * d) MOD N`)) (concl th) &&
      can (find_term ((=) `ok:num->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; MOD_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LT_MULT] THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `u + j * e = (a + (k - 1 - j) * d) MOD N` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k - 1 - j` o check (fun th ->
        can (find_term ((=) `(a + j * d) MOD N`)) (concl th) &&
        can (find_term ((=) `e:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(k - 1) * e = (k - 1 - j) * e + j * e` MP_TAC THENL
       [REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `u + (k - 1) * e = a` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(ok:num->bool) ((a + (k - 1 - j) * d) MOD N)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `(a + j * d) MOD N`)) (concl th) &&
        not (can (find_term ((=) `e:num`)) (concl th)))) THEN
      ASM_ARITH_TAC;
      ASM_MESON_TAC[]]]);;

let PROGRESSIONS_FROM_PAIRS = prove
 (`!k N W b X (ok:num->bool) (Q:num->bool).
        2 <= k /\ 1 <= W /\
        (!y. ok y ==> 2 * y < N /\ Q(W * y + b) /\ W * y + b <= X)
        ==> CARD {(a,d) | a < N /\ 0 < d /\ d < N /\
                          !j. j < k ==> ok((a + j * d) MOD N)} <=
            2 * CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                              !j. j < k ==> Q(a + j * d)}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `S = {(a,d) | a < N /\ 0 < d /\ d < N /\
                 !j. j < k ==> (ok:num->bool)((a + j * d) MOD N)}` THEN
  ABBREV_TAC
   `Tp = {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                  !j. j < k ==> Q(a + j * d)}` THEN
  SUBGOAL_THEN `FINITE(S:num#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x,y | x IN {a:num | a < N} /\ y IN {d:num | d < N}}` THEN
    SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG_LT] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Tp:num#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x,y | x IN {a:num | a <= X} /\ y IN {d:num | d <= X}}` THEN
    SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG_LE] THEN EXPAND_TAC "Tp" THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `d:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `d <= (k - 1) * d` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `d = 1 * d`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S1 = {p | p IN S /\ FST p < (FST p + SND p) MOD N}` THEN
  ABBREV_TAC `S2 = {p | p IN S /\ (FST p + SND p) MOD N < FST p}` THEN
  SUBGOAL_THEN `FINITE(S1:num#num->bool) /\ FINITE(S2:num#num->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `S:num#num->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(S1:num#num->bool) + CARD(S2:num#num->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(S1 UNION S2:num#num->bool)` THEN
    ASM_SIMP_TAC[CARD_UNION_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN
    MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `d:num`] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    UNDISCH_TAC `(a:num,d:num) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `N:num`; `a:num`; `d:num`] MOD_AP_CASES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= t /\ b <= t ==> a + b <= 2 * t`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD(IMAGE (\p. W * FST p + b, W * ((FST p + SND p) MOD N - FST p))
                 (S1:num#num->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S1" THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM; FST; SND;
                  PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `d:num`; `a':num`; `d':num`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `a:num = a'` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `W * a + b = W * a' + b:num` THEN
        REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOD_ADD_LCANCEL THEN
      MAP_EVERY EXISTS_TAC [`N:num`; `a':num`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `W * ((a' + d) MOD N - a') = W * ((a' + d') MOD N - a')` THEN
      REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      EXPAND_TAC "S1" THEN EXPAND_TAC "S" THEN EXPAND_TAC "Tp" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_ELIM_PAIR_THM; FST; SND] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `d:num`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`k:num`; `N:num`; `W:num`; `b:num`; `X:num`; `a:num`;
                    `d:num`; `ok:num->bool`; `Q:num->bool`]
        SZEMEREDI_UP_PROGRESSION) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD(IMAGE (\p. W * ((FST p + (k - 1) * SND p) MOD N) + b,
                      W * (FST p - (FST p + SND p) MOD N))
                 (S2:num#num->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S2" THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM; FST; SND;
                  PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `d:num`; `a':num`; `d':num`] THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`k:num`; `N:num`; `W:num`; `b:num`; `X:num`; `a:num`;
                    `d:num`; `ok:num->bool`; `Q:num->bool`]
        SZEMEREDI_DOWN_PROGRESSION) THEN
      MP_TAC(SPECL [`k:num`; `N:num`; `W:num`; `b:num`; `X:num`; `a':num`;
                    `d':num`; `ok:num->bool`; `Q:num->bool`]
        SZEMEREDI_DOWN_PROGRESSION) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN
       `(a + (k - 1) * d) MOD N = (a' + (k - 1) * d') MOD N /\
        a - (a + d) MOD N = a' - (a' + d') MOD N`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`W * (a + (k - 1) * d) MOD N + b =
           W * (a' + (k - 1) * d') MOD N + b`;
          `W * (a - (a + d) MOD N) = W * (a' - (a' + d') MOD N)`] THEN
        REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN
        ASM_SIMP_TAC[ARITH_RULE `1 <= W ==> ~(W = 0)`];
        ALL_TAC] THEN
      SUBGOAL_THEN `a:num = a'` SUBST_ALL_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(a + (k - 1) * d) MOD N + (k - 1) * (a - (a + d) MOD N) = a`;
          `(a' + (k - 1) * d') MOD N + (k - 1) * (a' - (a' + d') MOD N) =
           a'`] THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOD_ADD_LCANCEL THEN
      MAP_EVERY EXISTS_TAC [`N:num`; `a':num`] THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      EXPAND_TAC "S2" THEN EXPAND_TAC "S" THEN EXPAND_TAC "Tp" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_ELIM_PAIR_THM; FST; SND] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `d:num`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`k:num`; `N:num`; `W:num`; `b:num`; `X:num`; `a:num`;
                    `d:num`; `ok:num->bool`; `Q:num->bool`]
        SZEMEREDI_DOWN_PROGRESSION) THEN
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Szemeredi's theorem: counting, finite and density forms; Roth.            *)
(* ------------------------------------------------------------------------- *)

let SZEMEREDI_COUNT = prove
 (`!k delta.
        2 <= k /\ &0 < delta
        ==> ?c N0. &0 < c /\
                   !N A. N0 <= N /\ A SUBSET 1..N /\ delta * &N <= &(CARD A)
                         ==> c * &N pow 2 <=
                             &(CARD {(a,d) | 0 < d /\
                                             !j. j < k ==> a + j * d IN A})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` WEIGHTED_SZEMEREDI) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[weighted_szemeredi] THEN
  DISCH_THEN(MP_TAC o SPEC `delta / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `csz:real` (X_CHOOSE_THEN `P1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wsz")))) THEN
  X_CHOOSE_TAC `R1:num` (SPEC `&2 / csz` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `csz:real` THEN EXISTS_TAC `P1 + R1 + 1` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `A:num->bool`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `2 * N` BERTRAND) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN A ==> 1 <= x /\ x <= N` (LABEL_TAC "Ab") THENL
   [UNDISCH_TAC `A SUBSET 1..N` THEN SIMP_TAC[SUBSET; IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(A:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  ABBREV_TAC `f = \y. if y + 1 IN A then &1 else &0` THEN
  SUBGOAL_THEN `!y. y < P ==> &0 <= (f:num->real) y /\
    f y <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {y:num | y < P} f = &(CARD(A:num->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    SIMP_TAC[GSYM CARD_RESTRICT_SUM; FINITE_NUMSEG_LT] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `CARD (IMAGE (\y. y + 1) {y | y IN {y:num | y < P} /\ y + 1 IN A})` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{y:num | y < P}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:num` THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN EXISTS_TAC `x - 1` THEN
        SUBGOAL_THEN `1 <= x /\ x <= N` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SUB_ADD] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta / &4 <= fmean {y:num | y < P} f` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[fmean; CARD_NUMSEG_LT] THEN
    SUBGOAL_THEN `&0 < &P` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta * &N` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&P <= &4 * &N` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `delta * &P <= delta * (&4 * &N)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "wsz" (MP_TAC o SPECL [`P:num`; `f:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `f:num->real`; `&1`]
    AP_COUNT_NONTRIVIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `P:num`; `1`; `1`; `N:num`;
                `\y. &0 < (f:num->real) y`;
                `\x:num. x IN A`] PROGRESSIONS_FROM_PAIRS) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `y:num` THEN EXPAND_TAC "f" THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN
    SUBGOAL_THEN `1 <= y + 1 /\ y + 1 <= N` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{(a,d) | 0 < d /\ a + (k - 1) * d <= N /\ !j. j < k ==> a + j * d IN A} =
    {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `d:num`] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_MUL] o
             GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
  ABBREV_TAC
   `ap = fmean {a | a < P}
           (\a. fmean {d | d < P}
                  (\d. product {j | j < k} (\j. f((a + j * d) MOD P))))` THEN
  ABBREV_TAC
   `sp = &(CARD {(a,d) | a < P /\ 0 < d /\ d < P /\
                         !j. j < k ==>
                           &0 < (f:num->real)((a + j * d) MOD P)})` THEN
  ABBREV_TAC
   `tc = &(CARD {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A})` THEN
  SUBGOAL_THEN `csz * &P pow 2 <= &P pow 2 * ap` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &P <= csz * &P pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `csz * &R1` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ];
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * &N pow 2 <= &P pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&4 * x pow 2 = (&2 * x) pow 2`] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; REAL_POS] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `csz * (&4 * &N pow 2) <= csz * &P pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SZEMEREDI = prove
 (`!k delta.
        &0 < delta
        ==> ?N0. !N A. N0 <= N /\ A SUBSET 1..N /\ delta * &N <= &(CARD A)
                       ==> ?a d. 0 < d /\ !j. j < k ==> a + j * d IN A`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= k` THENL
   [MP_TAC(SPECL [`k:num`; `delta:real`] SZEMEREDI_COUNT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `N0 + 1` THEN
    MAP_EVERY X_GEN_TAC [`N:num`; `A:num->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `A:num->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `Z = {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A}` THEN
    ASM_CASES_TAC `Z:num#num->bool = {}` THENL
     [ASM_REWRITE_TAC[CARD_CLAUSES] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      DISCH_THEN(K ALL_TAC) THEN UNDISCH_TAC `~(Z:num#num->bool = {})` THEN
      EXPAND_TAC "Z" THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM]];
    EXISTS_TAC `1` THEN MAP_EVERY X_GEN_TAC [`N:num`; `A:num->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(A:num->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `delta * &N <= &(CARD({}:num->bool))` THEN
      REWRITE_TAC[CARD_CLAUSES; REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `1`] THEN REWRITE_TAC[ARITH] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]]);;

let ROTH = prove
 (`!delta.
        &0 < delta
        ==> ?N0. !N A. N0 <= N /\ A SUBSET 1..N /\ delta * &N <= &(CARD A)
                       ==> ?a d. 0 < d /\ a IN A /\ a + d IN A /\
                                 a + 2 * d IN A`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`3`; `delta:real`] SZEMEREDI) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`;
    `A:num->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
      MP_TAC(SPEC `2` th))) THEN
  ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES] THEN SIMP_TAC[]);;

let SZEMEREDI_DENSITY = prove
 (`!A k delta.
        &0 < delta /\
        (!N0. ?N. N0 <= N /\ delta * &N <= &(CARD(A INTER (1..N))))
        ==> ?a d. 0 < d /\ !j. j < k ==> a + j * d IN A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `delta:real`] SZEMEREDI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC o SPEC `N0:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `A INTER (1..N)`]) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[IN_INTER]);;

(* ------------------------------------------------------------------------- *)
(* Van der Waerden's theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let VAN_DER_WAERDEN = prove
 (`!k r. 1 <= r
         ==> ?N. !col. (!n. col n < r)
                       ==> ?a d. 0 < d /\
                                 !j. j < k ==> a + j * d IN 1..N /\
                                               col(a + j * d) = col a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `inv(&r)`] SZEMEREDI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
  X_GEN_TAC `col:num->num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`col:num->num`; `1..N0`; `{c:num | c < r}`]
    CARD_PIGEONHOLE) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT; IN_ELIM_THM; CARD_NUMSEG_LT;
              CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`N0:num`; `{x | x IN 1..N0 /\ (col:num->num) x = c}`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `&0 < &r` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `0 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Multidimensional Szemeredi (Furstenberg-Katznelson).                      *)
(* ------------------------------------------------------------------------- *)

let FMEAN_SHIFT_HJ_CUBE = prove
 (`!Q d (s:num->num) (g:(num->num)->real).
        1 <= Q
        ==> fmean (hj_cube Q d)
              (\t. g(\i. if i < d then (t i + s i) MOD Q else 0)) =
            fmean (hj_cube Q d) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`g:(num->num)->real`;
    `\t:num->num. \i. if i < d then (t i + (s:num->num) i) MOD Q else 0`;
    `hj_cube Q d`] SUM_INJECTION) THEN
  REWRITE_TAC[o_DEF; FINITE_HJ_CUBE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_HJ_CUBE] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:num->num` THEN STRIP_TAC THEN CONJ_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THENL
     [ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= Q ==> ~(Q = 0)`];
      ASM_SIMP_TAC[ARITH_RULE `d <= i ==> ~(i < d:num)`]];
    MAP_EVERY X_GEN_TAC [`t:num->num`; `t':num->num`] THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i < d:num` THENL
     [FIRST_X_ASSUM(MP_TAC o C AP_THM `i:num`) THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN DISCH_TAC THEN
      MATCH_MP_TAC MOD_ADD_LCANCEL THEN
      MAP_EVERY EXISTS_TAC [`Q:num`; `(s:num->num) i`] THEN
      ASM_SIMP_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[]]]);;

let HJ_DENSITY_SHIFT_MEAN = prove
 (`!K n Q d (s:(num->num)->num->num) (A:(num->num)->bool).
        1 <= K /\ 1 <= Q /\ A SUBSET hj_cube Q d
        ==> fmean (hj_cube Q d)
              (\t. hj_density K n
                     {x | (\i. if i < d then (t i + s x i) MOD Q else 0)
                          IN A}) =
            &(CARD A) / &(Q EXP d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hj_density; IN_ELIM_THM] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean (hj_cube K n)
      (\x. fmean (hj_cube Q d)
             (\t. if (\i. if i < d then (t i + s x i) MOD Q else 0) IN A
                  then &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC[FINITE_HJ_CUBE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `fmean (hj_cube K n)
      (\x:num->num. &(CARD(A:(num->num)->bool)) / &(Q EXP d))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FMEAN_CONST THEN
      ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY]] THEN
  MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Q:num`; `d:num`; `(s:(num->num)->num->num) x`;
                 `\y:num->num. if y IN A then &1 else &0`]
                   FMEAN_SHIFT_HJ_CUBE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM hj_density; HJ_DENSITY_CARD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM SET_TAC[]);;

let MULTIDIM_SZEMEREDI = prove
 (`!d k (v:num->num->num) delta.
        &0 < delta /\ (!j i. j < k /\ d <= i ==> v j i = 0)
        ==> ?M0. !M A. M0 <= M /\ A SUBSET hj_cube M d /\
                       delta * &(M EXP d) <= &(CARD A)
                       ==> ?a lm. 0 < lm /\
                                   !j. j < k ==> (\i. a i + lm * v j i) IN A`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `u = \j:num. if j = 0 then (\i:num. 0) else (v:num->num->num) (j - 1)` THEN
  MP_TAC(SPEC `k + 1` DENSITY_HALES_JEWETT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= k + 1`; density_hales_jewett] THEN
  DISCH_THEN(MP_TAC o SPEC `delta / &2 pow d`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (LABEL_TAC "density_hales_jewett")) THEN
  MP_TAC(ISPECL [`\p:num#num. (v:num->num->num) (FST p) (SND p)`;
                 `{j,i | j IN {j:num | j < k} /\ i IN {i:num | i < d}}`]
    (prove
      (`!f:A->num s. FINITE s ==> ?a. !x. x IN s ==> f x <= a`,
       REPEAT STRIP_TAC THEN
       MP_TAC(ISPECL [`f:A->num`; `s:A->bool`] FINITE_IMAGE) THEN
       ASM_REWRITE_TAC[num_FINITE; FORALL_IN_IMAGE]))) THEN
  SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG_LT; FORALL_PAIR_THM;
           IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `V:num`) THEN
  EXISTS_TAC `n * V + 1` THEN
  MAP_EVERY X_GEN_TAC [`M:num`; `A:(num->num)->bool`] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = 2 * M` THEN
  SUBGOAL_THEN `1 <= M /\ 1 <= Q /\ M <= Q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(A:(num->num)->bool) SUBSET hj_cube Q d` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `hj_cube M d` THEN
    ASM_SIMP_TAC[HJ_CUBE_MONO];
    ALL_TAC] THEN
  ABBREV_TAC
   `s = \x:num->num. \i. nsum {r | r < n} (\r. (u:num->num->num) (x r) i)` THEN
  MP_TAC(ISPECL [`k + 1`; `n:num`; `Q:num`; `d:num`;
                 `s:(num->num)->num->num`; `A:(num->num)->bool`]
    HJ_DENSITY_SHIFT_MEAN) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `delta / &2 pow d <= &(CARD(A:(num->num)->bool)) / &(Q EXP d)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_POW_MUL] THEN
    SUBGOAL_THEN `&0 < &2 pow d /\ &0 < &M pow d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta * &(M EXP d)` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < &2 pow d` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`hj_cube Q d`;
    `\t. hj_density (k + 1) n
           {x | (\i. if i < d
                      then ((t:num->num) i +
                        (s:(num->num)->num->num) x i) MOD Q
                      else 0) IN (A:(num->num)->bool)}`;
    `delta / &2 pow d`] FMEAN_EXISTS_GE) THEN
  ASM_SIMP_TAC[FINITE_HJ_CUBE; HJ_CUBE_NONEMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "density_hales_jewett" (MP_TAC o SPECL
   [`n:num`;
    `{x | (\i. if i < d
               then ((t:num->num) i + (s:(num->num)->num->num) x i) MOD Q
               else 0) IN (A:(num->num)->bool)}`]) THEN
  ASM_REWRITE_TAC[LE_REFL; hj_has_line; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "pts"))) THEN
  ABBREV_TAC `w = CARD {r | r < n /\ (l:num->num) r = k + 1}` THEN
  SUBGOAL_THEN `0 < w /\ w <= n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC HJ_LINE_WILDCARDS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `s0 = \i. nsum {r | r < n}
               (\r. if (l:num->num) r < k + 1
                    then (u:num->num->num) (l r) i else 0)` THEN
  SUBGOAL_THEN
   `!a i. (s:(num->num)->num->num) (hj_line_point (k + 1) l a) i =
          (s0:num->num) i + w * (u:num->num->num) a i`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["s"; "s0"; "w"] THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k + 1`; `n:num`; `l:num->num`;
                   `\x. (u:num->num->num) x i`;
                   `a:num`] NSUM_HJ_LINE_POINT_GEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:num->num->num) 0 = (\i. 0) /\ !j. u (j + 1) = v j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[ADD_EQ_0; ARITH; ADD_SUB]; ALL_TAC] THEN
  USE_THEN "pts" (MP_TAC o REWRITE_RULE[ARITH_RULE `0 < k + 1`] o
    SPEC `0`) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < d ==> ((t:num->num) i + (s0:num->num) i) MOD Q < M`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\i. if i < d then ((t:num->num) i + (s0:num->num) i) MOD Q else 0)
      IN hj_cube M d`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_HJ_CUBE] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\i. if i < d then ((t:num->num) i + (s0:num->num) i) MOD Q else 0` THEN
  EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "pts" (MP_TAC o
    REWRITE_RULE[ARITH_RULE `j + 1 < k + 1 <=> j < k`] o SPEC `j + 1`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `!x y:num->num. x = y ==> x IN (A:(num->num)->bool) ==> y IN A`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < d:num` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`] o check (fun th ->
      can (find_term ((=) `v:num->num->num`)) (concl th) &&
      can (find_term ((=) `d:num`)) (concl th) && is_forall (concl th) &&
      not (can (find_term ((=) `V:num`)) (concl th)))) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN
  SUBGOAL_THEN `w * (v:num->num->num) j i < M` ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n * V:num` THEN
    CONJ_TAC THENL [MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `(((t:num->num) i + (s0:num->num) i) MOD Q + w * (v:num->num->num) j i)
    MOD Q` THEN
  CONJ_TAC THENL
   [CONV_TAC(BINOP_CONV MOD_DOWN_CONV) THEN REWRITE_TAC[ADD_ASSOC];
    MATCH_MP_TAC MOD_LT THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `s0:num->num`)) (concl th) && is_forall (concl th) &&
      can (find_term ((=) `M:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Gallai-Witt theorem and the corners theorem.                          *)
(* ------------------------------------------------------------------------- *)

let GALLAI_WITT = prove
 (`!d k (v:num->num->num) r.
        1 <= r /\ (!j i. j < k /\ d <= i ==> v j i = 0)
        ==> ?M. !col. (!x. col x < r)
                      ==> ?a lm c.
                            0 < lm /\
                            !j. j < k
                                ==> (\i. a i + lm * v j i) IN hj_cube M d /\
                                    col(\i. a i + lm * v j i) = c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `k:num`; `v:num->num->num`; `inv(&r)`]
    MULTIDIM_SZEMEREDI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M0:num`) THEN EXISTS_TAC `M0:num` THEN
  X_GEN_TAC `col:(num->num)->num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`col:(num->num)->num`; `hj_cube M0 d`; `{c:num | c < r}`]
    CARD_PIGEONHOLE) THEN
  REWRITE_TAC[FINITE_HJ_CUBE; FINITE_NUMSEG_LT; IN_ELIM_THM; CARD_NUMSEG_LT;
              CARD_HJ_CUBE] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`M0:num`; `{x | x IN hj_cube M0 d /\ (col:(num->num)->num) x = c}`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &r` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->num` (X_CHOOSE_THEN `lm:num`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:num->num`; `lm:num`; `c:num`] THEN
  ASM_SIMP_TAC[]);;

let CORNERS = prove
 (`!delta.
        &0 < delta
        ==> ?M0. !M A. M0 <= M /\ A SUBSET {(x,y) | x < M /\ y < M} /\
                       delta * &M pow 2 <= &(CARD A)
                       ==> ?x y lm. 0 < lm /\ (x,y) IN A /\
                                     (x + lm,y) IN A /\ (x,y + lm) IN A`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`2`; `3`;
    `\j i. if (j = 1 /\ i = 0) \/ (j = 2 /\ i = 1) then 1 else 0`;
    `delta:real`] MULTIDIM_SZEMEREDI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M0:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`M:num`; `A:num#num->bool`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `emb = \p:num#num. \i:num. if i = 0 then FST p
                               else if i = 1 then SND p else 0` THEN
  SUBGOAL_THEN
   `!p f. f = (emb:num#num->num->num) p ==> p = (f 0,f 1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "emb" THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`; PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(A:num#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x,y | x IN {x:num | x < M} /\ y IN {y:num | y < M}}` THEN
    SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG_LT] THEN
    UNDISCH_TAC `(A:num#num->bool) SUBSET {(x,y) | x < M /\ y < M:num}` THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`M:num`;
    `IMAGE (emb:num#num->num->num) A`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `x < M /\ y < M:num` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(A:num#num->bool) SUBSET {(x,y) | x < M /\
         y < M:num}` THEN
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "emb" THEN REWRITE_TAC[IN_HJ_CUBE] THEN CONJ_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `CARD(IMAGE (emb:num#num->num->num) A) = CARD A`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->num` (X_CHOOSE_THEN `lm:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pts")))) THEN
  MAP_EVERY EXISTS_TAC [`(a:num->num) 0`; `(a:num->num) 1`; `lm:num`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "pts" (MP_TAC o SPEC `0`);
    USE_THEN "pts" (MP_TAC o SPEC `1`);
    USE_THEN "pts" (MP_TAC o SPEC `2`)] THEN
  REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num#num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ASSUME
   `!p f. f = (emb:num#num->num->num) p ==> p = (f 0,f 1)`)) THEN
  REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;
