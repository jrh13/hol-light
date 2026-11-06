(* ========================================================================= *)
(* Integer lattices: subgroups of Z^s for a finite index set s:K->bool (any  *)
(* type K), as sets of functions K->int vanishing outside s.                 *)
(*                                                                           *)
(*   int_lattice s L      <=> L is a subgroup of Z^s                         *)
(*   int_matrix_image s M  =  { M z | z IN Z^s }                             *)
(*   int_cosets s L        =  the set of cosets of L in Z^s                  *)
(*                                                                           *)
(* Main results: images of integer matrices are lattices                     *)
(* (INT_LATTICE_INT_MATRIX_IMAGE) and every lattice is such an image         *)
(* (INT_LATTICE_MATRIX_IMAGE, Hermite form, existence only); the index of    *)
(* M Z^s is |det M| when det M is nonzero (INT_COSETS_MATRIX_IMAGE); det M   *)
(* nonzero gives independent columns (INT_MATRIX_IMAGE_INJECTIVE); a lattice *)
(* containing d Z^s has nonzero determinant (INT_LATTICE_FULL_RANK) and at   *)
(* most |d|^|s| cosets (INT_COSETS_FINITE); the Leibniz bound                *)
(* |det M| <= n! B^n (INT_DET_BOUND). The determinant is ring_det            *)
(* integer_ring s M of ring_det.ml.                                          *)
(*                                                                           *)
(* Proof route: induction on s. For s = a INSERT t, the vectors of L with    *)
(* a-coordinate 0 form a lattice L0 in Z^t, and the a-coordinates of L form  *)
(* m Z with m the a-coordinate of some w IN L (INT_LATTICE_SPLIT); a matrix  *)
(* for L0 completed by the column w is a matrix for L                        *)
(* (INT_LATTICE_INSERT_IMAGE). Matrices with the same image and a nonzero    *)
(* determinant have the same |det| (INT_MATRIX_IMAGE_EQ_DET, by RING_DET_MUL *)
(* and a unimodular change); the index is counted with explicit sets of      *)
(* representatives (INT_COSETS_TRANSVERSAL, INT_LATTICE_TRANSVERSAL_INSERT): *)
(* the index of L is |m| times the index of L0.                              *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (INTEGER_RING_SUM, INTEGER_RING_PRODUCT: isum *)
(* and iproduct as ring sums and products over integer_ring),                *)
(* Library/permutations.ml, Library/isum.ml (ISUM_DELTA_GEN),                *)
(* Library/products.ml (IPRODUCT_ABS_BOUND, through the needs lines of       *)
(* ANT/algmisc.ml), ANT/algmisc.ml (HAS_SIZE_INT_SEG_LT) and                 *)
(* Library/ring_det.ml.                                                      *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/permutations.ml";;
needs "Library/isum.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;

let int_lattice = new_definition
 `int_lattice (s:K->bool) (L:(K->int)->bool) <=>
  L SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
  (\i. &0) IN L /\
  (!x y. x IN L /\ y IN L ==> (\i. x i - y i) IN L)`;;

let int_matrix_image = new_definition
 `int_matrix_image (s:K->bool) (M:K->K->int) =
  IMAGE (\z i. if i IN s then isum s (\j. M i j * z j) else &0)
        (:K->int)`;;

let int_cosets = new_definition
 `int_cosets (s:K->bool) (L:(K->int)->bool) =
  {{y | (!i. ~(i IN s) ==> y i = &0) /\ (\i. y i - x i) IN L} | x |
   !i. ~(i IN s) ==> x i = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Closure properties of integer lattices.                                   *)
(* ------------------------------------------------------------------------- *)

let INT_LATTICE_0 = prove
 (`!s (L:(K->int)->bool). int_lattice s L ==> (\i. &0) IN L`,
  SIMP_TAC[int_lattice]);;

let INT_LATTICE_SUB = prove
 (`!s (L:(K->int)->bool) x y.
        int_lattice s L /\ x IN L /\ y IN L ==> (\i. x i - y i) IN L`,
  SIMP_TAC[int_lattice]);;

let INT_LATTICE_SUPPORT = prove
 (`!s (L:(K->int)->bool) x i.
        int_lattice s L /\ x IN L /\ ~(i IN s) ==> x i = &0`,
  REWRITE_TAC[int_lattice; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INT_LATTICE_NEG = prove
 (`!s (L:(K->int)->bool) x.
        int_lattice s L /\ x IN L ==> (\i. --(x i)) IN L`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INT_LATTICE_0) THEN
  MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `(\i. &0):K->int`;
                 `x:K->int`] INT_LATTICE_SUB) THEN
  ASM_REWRITE_TAC[INT_SUB_LZERO]);;

let INT_LATTICE_ADD = prove
 (`!s (L:(K->int)->bool) x y.
        int_lattice s L /\ x IN L /\ y IN L ==> (\i. x i + y i) IN L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `y:K->int`]
    INT_LATTICE_NEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `x:K->int`;
                 `(\i. --((y:K->int) i))`] INT_LATTICE_SUB) THEN
  ASM_REWRITE_TAC[INT_SUB_RNEG]);;

let INT_LATTICE_CMUL = prove
 (`!s (L:(K->int)->bool) c x.
        int_lattice s L /\ x IN L ==> (\i. c * x i) IN L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. (\i. &n * (x:K->int) i) IN L` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[INT_MUL_LZERO] THEN ASM_MESON_TAC[INT_LATTICE_0];
      REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ADD_RDISTRIB; INT_MUL_LID] THEN
      MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`;
                     `(\i. &n * (x:K->int) i)`; `x:K->int`]
        INT_LATTICE_ADD) THEN
      ASM_REWRITE_TAC[]];
    DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC)
     (SPEC `c:int` INT_IMAGE) THEN
    ASM_REWRITE_TAC[INT_MUL_LNEG] THEN
    MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`;
                   `(\i. &n * (x:K->int) i)`] INT_LATTICE_NEG) THEN
    ASM_REWRITE_TAC[]]);;

let INT_LATTICE_CLOSED = prove
 (`!s (L:(K->int)->bool).
        int_lattice s L
        ==> (\i. &0) IN L /\
            (!x y. x IN L /\ y IN L ==> (\i. x i - y i) IN L) /\
            (!x y. x IN L /\ y IN L ==> (\i. x i + y i) IN L) /\
            (!x. x IN L ==> (\i. --(x i)) IN L) /\
            (!c x. x IN L ==> (\i. c * x i) IN L)`,
  MESON_TAC[INT_LATTICE_0; INT_LATTICE_SUB; INT_LATTICE_ADD;
            INT_LATTICE_NEG; INT_LATTICE_CMUL]);;

let INT_LATTICE_ISUM = prove
 (`!s (L:(K->int)->bool) t (c:A->int) v.
        int_lattice s L /\ FINITE t /\ (!k. k IN t ==> v k IN L)
        ==> (\i. isum t (\k. c k * v k i)) IN L`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ISUM_CLAUSES; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Images of integer matrices.                                               *)
(* ------------------------------------------------------------------------- *)

let INT_MATRIX_IMAGE_IN = prove
 (`!s (M:K->K->int) x.
        x IN int_matrix_image s M <=>
        ?z. x = (\i. if i IN s then isum s (\j. M i j * z j) else &0)`,
  REWRITE_TAC[int_matrix_image; IN_IMAGE; IN_UNIV]);;

let INT_LATTICE_INT_MATRIX_IMAGE = prove
 (`!s (M:K->K->int). FINITE s ==> int_lattice s (int_matrix_image s M)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[int_lattice; SUBSET; IN_ELIM_THM; INT_MATRIX_IMAGE_IN] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    EXISTS_TAC `(\j. &0):K->int` THEN
    REWRITE_TAC[INT_MUL_RZERO; ISUM_0; COND_ID];
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:K->int`; `y:K->int`; `z:K->int`; `w:K->int`] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    EXISTS_TAC `\j. (z:K->int) j - w j` THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[INT_SUB_LDISTRIB; ISUM_SUB; INT_SUB_REFL]]);;

let INT_MATRIX_IMAGE_COLUMN = prove
 (`!s (M:K->K->int) j.
        j IN s
        ==> (\i. if i IN s then M i j else &0) IN int_matrix_image s M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_MATRIX_IMAGE_IN] THEN
  EXISTS_TAC `\k:K. if k = j then (&1:int) else &0` THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COND_RAND; INT_MUL_RID; INT_MUL_RZERO; ISUM_DELTA_GEN]);;

let INT_MATRIX_IMAGE_SUBSET = prove
 (`!s (L:(K->int)->bool) M.
        FINITE s /\ int_lattice s L /\
        (!j. j IN s ==> (\i. if i IN s then M i j else &0) IN L)
        ==> int_matrix_image s M SUBSET L`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; INT_MATRIX_IMAGE_IN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:K->int` THEN X_GEN_TAC `z:K->int` THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `s:K->bool`; `z:K->int`;
                 `\j i. if i IN s then (M:K->K->int) i j else &0`]
    INT_LATTICE_ISUM) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `i:K` THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; ISUM_0] THEN
  MATCH_MP_TAC ISUM_EQ THEN REWRITE_TAC[INT_MUL_AC]);;

let INT_MATRIX_IMAGE_FACTOR = prove
 (`!s (A:K->K->int) N.
        (!j. j IN s
             ==> (\i. if i IN s then A i j else &0) IN int_matrix_image s N)
        ==> ?U. !i j. i IN s /\ j IN s ==> A i j = isum s (\k. N i k * U k j)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    REWRITE_RULE[INT_MATRIX_IMAGE_IN]) THEN
  DISCH_THEN(X_CHOOSE_TAC `u:K->K->int`) THEN
  EXISTS_TAC `\k j. (u:K->K->int) j k` THEN REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `i:K`) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integer determinants.                                                     *)
(* ------------------------------------------------------------------------- *)

let INT_DET_MUL = prove
 (`!s (A:K->K->int) B.
        FINITE s
        ==> ring_det integer_ring s (\i j. isum s (\k. A i k * B k j)) =
            ring_det integer_ring s A * ring_det integer_ring s B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `s:K->bool`; `A:K->K->int`; `B:K->K->int`]
    RING_DET_MUL) THEN
  ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; INTEGER_RING_SUM]);;

let INT_DET_INSERT_ROW = prove
 (`!a t (N:K->K->int).
        FINITE t /\ ~(a IN t) /\ (!j. j IN t ==> N a j = &0)
        ==> ring_det integer_ring (a INSERT t) N =
            N a a * ring_det integer_ring t N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `t:K->bool`; `N:K->K->int`; `a:K`]
    RING_DET_LAPLACE_INSERT) THEN
  ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; INTEGER_RING_SUM] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[ISUM_CLAUSES; SWAP_REFL; RING_SIGN_I; I_THM; INTEGER_RING;
               ETA_AX] THEN
  MATCH_MP_TAC(INT_ARITH `(y:int) = &0 ==> x * &1 * z + y = x * z`) THEN
  TRANS_TAC EQ_TRANS `isum t (\b:K. &0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN ASM_SIMP_TAC[INT_MUL_LZERO];
    REWRITE_TAC[ISUM_0]]);;

let INT_MATRIX_MUL_ASSOC = prove
 (`!s (A:K->K->int) (B:K->K->int) (C:K->K->int) i j.
        FINITE s
        ==> isum s (\k. A i k * isum s (\l. B k l * C l j)) =
            isum s (\l. isum s (\k. A i k * B k l) * C l j)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM ISUM_LMUL; GSYM ISUM_RMUL] THEN
  REWRITE_TAC[INT_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`\k l. ((A:K->K->int) i k * B k l) * (C:K->K->int) l j`;
                 `s:K->bool`; `s:K->bool`]
    ISUM_SWAP) THEN
  ASM_REWRITE_TAC[]);;

let INT_MATRIX_IMAGE_INJECTIVE = prove
 (`!s (M:K->K->int) z z'.
        FINITE s /\ ~(ring_det integer_ring s M = &0) /\
        (!i. i IN s ==> isum s (\j. M i j * z j) = isum s (\j. M i j * z' j))
        ==> !j. j IN s ==> z j = z' j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
  ASM_CASES_TAC `(z:K->int) k - z' k = &0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(ring_det integer_ring s (M:K->K->int) = &0)` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`integer_ring`; `s:K->bool`; `M:K->K->int`;
                 `\j. (z:K->int) j - z' j`] RING_DET_DEPENDENT_COLUMNS) THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_INTEGER_RING; INTEGER_RING; IN_UNIV;
              INTEGER_RING_SUM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `k:K` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[INT_SUB_LDISTRIB; ISUM_SUB; INT_SUB_REFL]]);;

let INT_LATTICE_FULL_RANK = prove
 (`!s (L:(K->int)->bool) M d.
        FINITE s /\ L = int_matrix_image s M /\ ~(d = &0) /\
        (!x. (!i. ~(i IN s) ==> x i = &0) ==> (\i. d * x i) IN L)
        ==> ~(ring_det integer_ring s M = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `\i j:K. (d:int) * (if i = j then &1 else &0)`;
                 `M:K->K->int`] INT_MATRIX_IMAGE_FACTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i:K. if i = j then (&1:int) else &0`) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `i:K` THEN ASM_CASES_TAC `i:K = j` THEN
    ASM_REWRITE_TAC[INT_MUL_RID; INT_MUL_RZERO; COND_ID];
    DISCH_THEN(X_CHOOSE_THEN `U:K->K->int` (ASSUME_TAC o BETA_RULE))] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_det integer_ring s (\i j:K. (d:int) * (if i = j then &1 else &0)) =
    ring_det integer_ring s M * ring_det integer_ring s U`
  MP_TAC THENL
   [SIMP_TAC[GSYM INT_DET_MUL; ASSUME `FINITE(s:K->bool)`] THEN
    MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`integer_ring`; `s:K->bool`;
                   `\i j:K. if i = j then (&1:int) else &0`; `d:int`]
      RING_DET_CMUL) THEN
    MP_TAC(ISPECL [`integer_ring`; `s:K->bool`] RING_DET_I) THEN
    ASM_SIMP_TAC[INTEGER_RING; IN_UNIV; INTEGER_RING_POW; INT_MUL_RID] THEN
    DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[INT_MUL_LZERO; INT_POW_EQ_0]]);;

let INT_MATRIX_IMAGE_EQ_DET = prove
 (`!s (M:K->K->int) N.
        FINITE s /\ int_matrix_image s M = int_matrix_image s N /\
        ~(ring_det integer_ring s M = &0)
        ==> abs(ring_det integer_ring s N) = abs(ring_det integer_ring s M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `M:K->K->int`; `N:K->K->int`]
    INT_MATRIX_IMAGE_FACTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:K->bool`; `M:K->K->int`; `j:K`]
      INT_MATRIX_IMAGE_COLUMN) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `U:K->K->int` (LABEL_TAC "U"))] THEN
  MP_TAC(ISPECL [`s:K->bool`; `N:K->K->int`; `M:K->K->int`]
    INT_MATRIX_IMAGE_FACTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:K->bool`; `N:K->K->int`; `j:K`]
      INT_MATRIX_IMAGE_COLUMN) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `V:K->K->int` (LABEL_TAC "V"))] THEN
  SUBGOAL_THEN
   `ring_det integer_ring s (M:K->K->int) =
    ring_det integer_ring s N * ring_det integer_ring s U`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM INT_DET_MUL; ASSUME `FINITE(s:K->bool)`] THEN
    MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN s
        ==> !l. l IN s
                ==> isum s (\k. (V:K->K->int) l k * U k j) =
                    (\l:K. if l = j then &1 else &0) l`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC INT_MATRIX_IMAGE_INJECTIVE THEN
    EXISTS_TAC `M:K->K->int` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[COND_RAND; INT_MUL_RID; INT_MUL_RZERO; ISUM_DELTA_GEN] THEN
    SIMP_TAC[INT_MATRIX_MUL_ASSOC; ASSUME `FINITE(s:K->bool)`] THEN
    TRANS_TAC EQ_TRANS `isum s (\k. (N:K->K->int) i k * (U:K->K->int) k j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "V" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN USE_THEN "U" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_det integer_ring s (V:K->K->int) * ring_det integer_ring s U = &1`
  MP_TAC THENL
   [SIMP_TAC[GSYM INT_DET_MUL; ASSUME `FINITE(s:K->bool)`] THEN
    TRANS_TAC EQ_TRANS
     `ring_det integer_ring s (\i j:K. if i = j then &1 else &0)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(ISPECL [`integer_ring`; `s:K->bool`] RING_DET_I) THEN
      ASM_REWRITE_TAC[INTEGER_RING]] THEN
    MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[];
    REWRITE_TAC[INT_MUL_EQ_1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[INT_ABS_MUL; INT_ABS_NEG; INT_ABS_NUM; INT_MUL_RID]]);;

let INT_PRIMITIVE_UNIMODULAR_COLUMN = prove
 (`!s (v:K->int) a.
        FINITE s /\ a IN s /\
        (!d. (!i. i IN s ==> d divides v i) ==> d divides &1)
        ==> ?U. (!i. i IN s ==> U i a = v i) /\
                abs(ring_det integer_ring s U) = &1`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `num_of_int(isum s (\i. abs((v:K->int) i)))` THEN
  STRIP_TAC THEN
  ASM_CASES_TAC
   `?i j. i IN s /\ j IN s /\ ~(i = j) /\ ~((v:K->int) i = &0) /\
          ~(v j = &0)`
  THENL
   [SUBGOAL_THEN
     `?i j. i IN s /\ j IN s /\ ~(i = j) /\ ~((v:K->int) i = &0) /\
            ~(v j = &0) /\ abs(v i) <= abs(v j)`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `p:K` (X_CHOOSE_THEN `q:K`
        STRIP_ASSUME_TAC)) THEN
      DISJ_CASES_TAC(INT_ARITH `abs((v:K->int) p) <= abs(v q) \/
                                abs(v q) <= abs(v p)`) THENL
       [MAP_EVERY EXISTS_TAC [`p:K`; `q:K`];
        MAP_EVERY EXISTS_TAC [`q:K`; `p:K`]] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?c:int. abs((v:K->int) j - c * v i) = abs(v j) - abs(v i)`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= (v:K->int) i` THEN
      ASM_CASES_TAC `&0 <= (v:K->int) j` THENL
       [EXISTS_TAC `&1:int`; EXISTS_TAC `-- &1:int`;
        EXISTS_TAC `-- &1:int`; EXISTS_TAC `&1:int`] THEN
      ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`s:K->bool`; `\k. if k = j then (v:K->int) j - c * v i else v k`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o
        lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC ISUM_POS_LE THEN REWRITE_TAC[INT_ABS_POS];
        DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o
        rand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC ISUM_POS_LE THEN REWRITE_TAC[INT_ABS_POS];
        DISCH_THEN SUBST1_TAC] THEN
      TRANS_TAC INT_LET_TRANS
       `isum s (\k. abs((v:K->int) k) - (if k = j then abs(v i) else &0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_EQ_IMP_LE THEN MATCH_MP_TAC ISUM_EQ THEN
        X_GEN_TAC `k:K` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_SUB_RZERO];
        ASM_SIMP_TAC[ISUM_SUB; ISUM_DELTA] THEN
        MATCH_MP_TAC(INT_ARITH `&0 < b ==> a - b < a:int`) THEN
        ASM_REWRITE_TAC[INT_ARITH `&0 < abs x <=> ~(x:int = &0)`]];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `d:int` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        free_in `d:int` (concl th) = false && is_forall(concl th) &&
        free_in `(&1:int)` (concl th))) THEN
      X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      ASM_CASES_TAC `k:K = j` THENL
       [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:K` th) THEN
                                MP_TAC(SPEC `j:K` th)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC INTEGER_RULE;
        FIRST_X_ASSUM(MP_TAC o SPEC `k:K`) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:K->K->int` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\k l. if k = j then (U:K->K->int) j l + c * U i l
                      else U k l` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `k:K` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN INT_ARITH_TAC;
      MP_TAC(ISPECL [`integer_ring`; `s:K->bool`; `U:K->K->int`;
                     `j:K`; `i:K`; `c:int`] RING_DET_ROW_OPERATION) THEN
      ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i0:K. i0 IN s /\ ~((v:K->int) i0 = &0)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0:int` o check (fun th ->
      is_forall(concl th) && free_in `(&1:int)` (concl th) &&
      not(free_in `U:K->K->int` (concl th)))) THEN
    REWRITE_TAC[INTEGER_RULE `(&0:int) divides x <=> x = &0`] THEN
    CONV_TAC INT_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN s /\ ~(k = i0) ==> (v:K->int) k = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((v:K->int) i0) = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(v:K->int) i0` o check (fun th ->
      is_forall(concl th) && free_in `(&1:int)` (concl th) &&
      not(free_in `U:K->K->int` (concl th)))) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `k:K` THEN DISCH_TAC THEN ASM_CASES_TAC `k:K = i0` THEN
      ASM_SIMP_TAC[] THEN CONV_TAC INTEGER_RULE;
      DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC
   `\k l. if swap(a,i0) k = l then (if l = a then (v:K->int) i0 else &1)
          else &0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:K` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `swap(a,i0) (k:K) = a <=> k = i0` SUBST1_TAC THENL
     [REWRITE_TAC[swap] THEN MESON_TAC[]; REWRITE_TAC[]] THEN
    ASM_CASES_TAC `k:K = i0` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`integer_ring`; `s:K->bool`;
    `\k l:K. if k = l then (if l = a then (v:K->int) i0 else &1) else &0`]
   RING_DET_DIAGONAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[INTEGER_RING]; ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RING_PRODUCT] THEN
  ASM_SIMP_TAC[IPRODUCT_DELTA] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a:K = i0` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[SWAP_REFL; I_THM];
    MP_TAC(ISPECL
     [`integer_ring`; `s:K->bool`;
      `\k l:K. if k = l then (if l = a then (v:K->int) i0 else &1) else &0`;
      `a:K`; `i0:K`] RING_DET_SWAP_ROWS) THEN
    ASM_REWRITE_TAC[INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[INT_ABS_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* The Leibniz bound for integer determinants.                               *)
(* ------------------------------------------------------------------------- *)

let INT_DET_BOUND = prove
 (`!s (M:K->K->int) B.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> abs(M i j) <= B)
        ==> abs(ring_det integer_ring s M) <=
            &(FACT(CARD s)) * B pow (CARD s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_det; INTEGER_RING; INTEGER_RING_SUM;
              INTEGER_RING_PRODUCT] THEN
  ASM_SIMP_TAC[GSYM CARD_PERMUTATIONS] THEN
  MATCH_MP_TAC ISUM_ABS_BOUND THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `p:K->K` THEN DISCH_TAC THEN REWRITE_TAC[INT_ABS_MUL] THEN
  SUBGOAL_THEN `abs(ring_sign integer_ring (p:K->K)) = &1` SUBST1_TAC THENL
   [REWRITE_TAC[ring_sign; INTEGER_RING] THEN COND_CASES_TAC THEN
    REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM];
    REWRITE_TAC[INT_MUL_LID]] THEN
  MATCH_MP_TAC IPRODUCT_ABS_BOUND THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Cosets and sets of representatives.                                       *)
(* ------------------------------------------------------------------------- *)

let INT_LATTICE_CONG_SYM = prove
 (`!s (L:(K->int)->bool) x y.
        int_lattice s L /\ (\i. x i - y i) IN L ==> (\i. y i - x i) IN L`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  SUBGOAL_THEN `(\i. (y:K->int) i - x i) = (\i. --(x i - y i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN INT_ARITH_TAC; ASM_SIMP_TAC[ETA_AX]]);;

let INT_LATTICE_CONG_TRANS = prove
 (`!s (L:(K->int)->bool) x y z.
        int_lattice s L /\ (\i. x i - y i) IN L /\ (\i. y i - z i) IN L
        ==> (\i. x i - z i) IN L`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  SUBGOAL_THEN `(\i. (x:K->int) i - z i) = (\i. (x i - y i) + (y i - z i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN INT_ARITH_TAC; ASM_SIMP_TAC[ETA_AX]]);;

let INT_LATTICE_COSET_EQ = prove
 (`!s (L:(K->int)->bool) x x'.
        int_lattice s L /\ (\i. x i - x' i) IN L
        ==> {y | (!i. ~(i IN s) ==> y i = &0) /\ (\i. y i - x i) IN L} =
            {y | (!i. ~(i IN s) ==> y i = &0) /\ (\i. y i - x' i) IN L}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:K->int` THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `y:K->int`; `x:K->int`;
                   `x':K->int`] INT_LATTICE_CONG_TRANS) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `x:K->int`; `x':K->int`]
      INT_LATTICE_CONG_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `y:K->int`; `x':K->int`;
                   `x:K->int`] INT_LATTICE_CONG_TRANS) THEN
    ASM_REWRITE_TAC[]]);;

let INT_COSETS_COVER = prove
 (`!s (L:(K->int)->bool) R.
        int_lattice s L /\
        R SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
        (!x. (!i. ~(i IN s) ==> x i = &0)
             ==> ?r. r IN R /\ (\i. x i - r i) IN L)
        ==> int_cosets s L =
            IMAGE (\x. {y | (!i. ~(i IN s) ==> y i = &0) /\
                            (\i. y i - x i) IN L}) R`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[int_cosets] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `C:(K->int)->bool` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:K->int`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:K->int`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:K->int` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_LATTICE_COSET_EQ THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `r:K->int`
      (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    EXISTS_TAC `r:K->int` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC
     `(R:(K->int)->bool) SUBSET {x | !i. ~(i IN s) ==> x i = &0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let INT_COSETS_TRANSVERSAL = prove
 (`!s (L:(K->int)->bool) R n.
        int_lattice s L /\
        R SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
        (!x. (!i. ~(i IN s) ==> x i = &0)
             ==> ?r. r IN R /\ (\i. x i - r i) IN L) /\
        (!r r'. r IN R /\ r' IN R /\ (\i. r i - r' i) IN L ==> r = r') /\
        R HAS_SIZE n
        ==> int_cosets s L HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INT_LATTICE_0) THEN
  MP_TAC(ISPECL [`s:K->bool`; `L:(K->int)->bool`; `R:(K->int)->bool`]
    INT_COSETS_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`r:K->int`; `r':K->int`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:K->int` o REWRITE_RULE[EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; INT_SUB_REFL] THEN
  SUBGOAL_THEN `!i. ~(i IN s) ==> (r:K->int) i = &0`
   (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC
     `(R:(K->int)->bool) SUBSET {x | !i. ~(i IN s) ==> x i = &0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A lattice containing d Z^s has at most |d|^|s| cosets.                    *)
(* ------------------------------------------------------------------------- *)

let INT_COSETS_FINITE = prove
 (`!s (L:(K->int)->bool) d.
        FINITE s /\ int_lattice s L /\ ~(d = &0) /\
        (!x. (!i. ~(i IN s) ==> x i = &0) ==> (\i. d * x i) IN L)
        ==> FINITE(int_cosets s L) /\
            CARD(int_cosets s L) <= num_of_int(abs d) EXP CARD s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:K->bool`; `L:(K->int)->bool`;
    `{x:K->int | (!i. i IN s ==> x i IN {k | &0 <= k /\ k < abs d}) /\
                 (!i. ~(i IN s) ==> x i = &0)}`] INT_COSETS_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      X_GEN_TAC `x:K->int` THEN DISCH_TAC THEN
      EXISTS_TAC `\i. if i IN s then (x:K->int) i rem d else &0` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `i:K` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`(x:K->int) i`; `d:int`] INT_DIVISION) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o
          SPEC `\i. if i IN s then (x:K->int) i div d else &0`) THEN
        ANTS_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[INT_MUL_RZERO; INT_SUB_RZERO] THEN
        MP_TAC(SPECL [`(x:K->int) i`; `d:int`] INT_DIVISION) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(MESON[FINITE_IMAGE; CARD_IMAGE_LE; HAS_SIZE; LE_TRANS]
   `(s:A->bool) HAS_SIZE n
    ==> FINITE(IMAGE (f:A->B) s) /\ CARD(IMAGE f s) <= n`) THEN
  MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
  MP_TAC(SPEC `num_of_int(abs d)` HAS_SIZE_INT_SEG_LT) THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Splitting off one coordinate; every lattice is the image of a matrix.     *)
(* ------------------------------------------------------------------------- *)

let INT_LATTICE_COORDINATE_GENERATOR = prove
 (`!s (L:(K->int)->bool) a.
        int_lattice s L ==> ?w. w IN L /\ !x. x IN L ==> (w a) divides (x a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  ASM_CASES_TAC `!x:K->int. x IN L ==> x a = &0` THENL
   [EXISTS_TAC `(\i. &0):K->int` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:K->int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:K->int`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INTEGER_RULE `!d:int. d divides d`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x0:K->int` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `?n. 0 < n /\ ?x:K->int. x IN L /\ x a = &n` MP_TAC THENL
   [ASM_CASES_TAC `&0 < (x0:K->int) a` THENL
     [EXISTS_TAC `num_of_int((x0:K->int) a)` THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT; INT_LT_IMP_LE] THEN
      EXISTS_TAC `x0:K->int` THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LT_IMP_LE];
      SUBGOAL_THEN `&0 < --((x0:K->int) a)` ASSUME_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `num_of_int(--((x0:K->int) a))` THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT; INT_LT_IMP_LE] THEN
      EXISTS_TAC `\i. --((x0:K->int) i)` THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LT_IMP_LE; ETA_AX]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:K->int` STRIP_ASSUME_TAC))
    (LABEL_TAC "min"))) THEN
  EXISTS_TAC `w:K->int` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:K->int` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
  SUBGOAL_THEN `~(&n:int = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`(x:K->int) a`; `&n:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[INT_ABS_NUM] THEN
  ABBREV_TAC `q = (x:K->int) a div &n` THEN
  ABBREV_TAC `r = (x:K->int) a rem &n` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y:K->int. y IN L /\ y a = r` ASSUME_TAC THENL
   [EXISTS_TAC `\i. (x:K->int) i - q * w i` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ETA_AX]; ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "min" (MP_TAC o SPEC `num_of_int r`) THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN
  ASM_INT_ARITH_TAC);;

let INT_LATTICE_SPLIT = prove
 (`!a t (L:(K->int)->bool).
        int_lattice (a INSERT t) L
        ==> int_lattice t {x | x IN L /\ x a = &0} /\
            ?w. w IN L /\ !x. x IN L ==> (w a) divides (x a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[INT_LATTICE_COORDINATE_GENERATOR]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  REWRITE_TAC[int_lattice; SUBSET; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[INT_SUB_REFL] THEN
  X_GEN_TAC `x:K->int` THEN STRIP_TAC THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:K = a` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a INSERT t:K->bool`; `L:(K->int)->bool`; `x:K->int`;
                 `i:K`] INT_LATTICE_SUPPORT) THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let INT_MATRIX_IMAGE_INSERT = prove
 (`!a t (w:K->int) M x.
        FINITE t /\ ~(a IN t) /\ (!i. ~(i IN a INSERT t) ==> w i = &0)
        ==> (x IN int_matrix_image (a INSERT t)
                (\i j. if j = a then w i else if i IN t then M i j else &0) <=>
             ?q y. y IN int_matrix_image t M /\ x = (\i. q * w i + y i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. (\i. if i IN a INSERT t
             then isum (a INSERT t)
                    (\j. (if j = a then (w:K->int) i
                          else if i IN t then (M:K->K->int) i j else &0) *
                         z j)
             else &0) =
        (\i. z a * w i + (if i IN t then isum t (\j. M i j * z j) else &0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:K->int` THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `i:K` THEN ASM_SIMP_TAC[ISUM_CLAUSES] THEN
    SUBGOAL_THEN
     `isum t (\j. (if j = a then (w:K->int) i
                   else if i IN t then (M:K->K->int) i j else &0) * z j) =
      isum t (\j. (if i IN t then M i j else &0) * z j)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      BETA_TAC THEN SUBGOAL_THEN `~(j:K = a)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT] THEN
    ASM_CASES_TAC `(i:K) IN t` THEN ASM_REWRITE_TAC[] THENL
     [INT_ARITH_TAC;
      REWRITE_TAC[INT_MUL_LZERO; ISUM_0; INT_ADD_RID] THEN
      ASM_CASES_TAC `i:K = a` THEN ASM_REWRITE_TAC[] THENL
       [INT_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
        ASM_REWRITE_TAC[IN_INSERT] THEN DISCH_THEN SUBST1_TAC THEN
        INT_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_MATRIX_IMAGE_IN] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:K->int` SUBST1_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`(z:K->int) a`;
      `\i. if i IN t then isum t (\j. (M:K->K->int) i j * z j) else &0`] THEN
    CONJ_TAC THENL [EXISTS_TAC `z:K->int` THEN REWRITE_TAC[]; REWRITE_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:int`; `y:K->int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:K->int` ASSUME_TAC)
      SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    EXISTS_TAC `\j. if j = a then q else (z:K->int) j` THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    BETA_TAC THEN SUBGOAL_THEN `~(j:K = a)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[]]);;

let INT_LATTICE_INSERT_IMAGE = prove
 (`!a t (L:(K->int)->bool) w M0.
        FINITE t /\ ~(a IN t) /\ int_lattice (a INSERT t) L /\
        w IN L /\ (!x. x IN L ==> (w a) divides (x a)) /\
        {x | x IN L /\ x a = &0} = int_matrix_image t M0
        ==> L = int_matrix_image (a INSERT t)
                  (\i j. if j = a then w i else if i IN t then M0 i j else &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "div") (LABEL_TAC "M0")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:K->int` THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `w:K->int`; `M0:K->K->int`; `x:K->int`]
    INT_MATRIX_IMAGE_INSERT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a INSERT t:K->bool`; `L:(K->int)->bool`; `w:K->int`;
                   `i:K`] INT_LATTICE_SUPPORT) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REMOVE_THEN "M0" (fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    REMOVE_THEN "div" (MP_TAC o SPEC `x:K->int`) THEN
    ASM_REWRITE_TAC[int_divides] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:int`) THEN
    MAP_EVERY EXISTS_TAC [`k:int`; `\i. (x:K->int) i - k * w i`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ETA_AX];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      REWRITE_TAC[FUN_EQ_THM] THEN INT_ARITH_TAC];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:int`; `y:K->int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN
    ASM_SIMP_TAC[ETA_AX]]);;

let INT_LATTICE_MATRIX_IMAGE = prove
 (`!s (L:(K->int)->bool).
        FINITE s /\ int_lattice s L ==> ?M. L = int_matrix_image s M`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [X_GEN_TAC `L:(K->int)->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `(\i j. &0):K->K->int` THEN
    REWRITE_TAC[EXTENSION; INT_MATRIX_IMAGE_IN; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:K->int` THEN EQ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
      MP_TAC(ISPECL [`{}:K->bool`; `L:(K->int)->bool`; `x:K->int`; `i:K`]
        INT_LATTICE_SUPPORT) THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY];
      DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[INT_LATTICE_0]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `L:(K->int)->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `L:(K->int)->bool`]
    INT_LATTICE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `w:K->int` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x | x IN L /\ (x:K->int) a = &0}`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M0:K->K->int`) THEN
  EXISTS_TAC `\i j. if j = a then (w:K->int) i
                    else if i IN t then (M0:K->K->int) i j else &0` THEN
  MATCH_MP_TAC INT_LATTICE_INSERT_IMAGE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The index of the image of a matrix with nonzero determinant is |det|.     *)
(* ------------------------------------------------------------------------- *)

let INT_LATTICE_TRANSVERSAL_INSERT = prove
 (`!a t (L:(K->int)->bool) w R0 n.
        FINITE t /\ ~(a IN t) /\ int_lattice (a INSERT t) L /\
        w IN L /\ ~(w a = &0) /\
        R0 SUBSET {x | !i. ~(i IN t) ==> x i = &0} /\ R0 HAS_SIZE n /\
        (!x. x IN L ==> (w a) divides (x a)) /\
        (!x. (!i. ~(i IN t) ==> x i = &0)
             ==> ?r. r IN R0 /\ (\i. x i - r i) IN {x | x IN L /\ x a = &0}) /\
        (!r r'. r IN R0 /\ r' IN R0 /\
                (\i. r i - r' i) IN {x | x IN L /\ x a = &0} ==> r = r')
        ==> ?R. R SUBSET {x | !i. ~(i IN a INSERT t) ==> x i = &0} /\
                (!x. (!i. ~(i IN a INSERT t) ==> x i = &0)
                     ==> ?r. r IN R /\ (\i. x i - r i) IN L) /\
                (!r r'. r IN R /\ r' IN R /\ (\i. r i - r' i) IN L
                        ==> r = r') /\
                R HAS_SIZE (num_of_int(abs(w a)) * n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "supp")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "div")
   (CONJUNCTS_THEN2 (LABEL_TAC "cover") (LABEL_TAC "unique")))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INT_LATTICE_CLOSED) THEN
  ABBREV_TAC `N = num_of_int(abs((w:K->int) a))` THEN
  SUBGOAL_THEN `&N:int = abs((w:K->int) a)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\p. (\i. if i = a then &(FST p) else SND p i):K->int)
                    {(m:num,r:K->int) | m < N /\ r IN R0}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_IMAGE;
              EXISTS_IN_IMAGE; FORALL_PAIR_THM; EXISTS_PAIR_THM;
              IN_ELIM_PAIR_THM; IN_INSERT; DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THENL
   [REMOVE_THEN "unique" (K ALL_TAC) THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN X_GEN_TAC `r:K->int` THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(r:K->int) IN R0`; `~((i:K) IN t)`] THEN
    USE_THEN "supp"
       (fun th -> MESON_TAC[REWRITE_RULE[SUBSET; IN_ELIM_THM] th]);
    REMOVE_THEN "unique" (K ALL_TAC) THEN REMOVE_THEN "supp" (K ALL_TAC) THEN
    X_GEN_TAC `x:K->int` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(x:K->int) a`; `(w:K->int) a`] INT_DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC [`q = (x:K->int) a div w a`;
                          `rho = (x:K->int) a rem w a`] THEN
    STRIP_TAC THEN REMOVE_THEN "cover"
     (MP_TAC o SPEC `\i. if i = a then &0 else (x:K->int) i - q * w i`) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `i:K` THEN DISCH_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`a INSERT t:K->bool`; `L:(K->int)->bool`; `w:K->int`;
                     `i:K`] INT_LATTICE_SUPPORT) THEN
      ASM_SIMP_TAC[IN_INSERT] THEN INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `r0:K->int` STRIP_ASSUME_TAC o BETA_RULE)]
    THEN
    MAP_EVERY EXISTS_TAC [`num_of_int rho`; `r0:K->int`] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN
    SUBGOAL_THEN
     `(\i. (x:K->int) i - (if i = a then rho else r0 i)) =
      (\i. q * w i + ((if i = a then &0 else x i - q * w i) - r0 i))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_INT_ARITH_TAC;
      ASM_SIMP_TAC[ETA_AX]];
    X_GEN_TAC `m1:num` THEN DISCH_TAC THEN X_GEN_TAC `r1:K->int` THEN
    DISCH_TAC THEN X_GEN_TAC `m2:num` THEN DISCH_TAC THEN
    X_GEN_TAC `r2:K->int` THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(r1:K->int) a = &0 /\ (r2:K->int) a = &0`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(r1:K->int) IN R0`; `(r2:K->int) IN R0`;
                             `~((a:K) IN t)`] THEN
      USE_THEN "supp"
       (fun th -> MESON_TAC[REWRITE_RULE[SUBSET; IN_ELIM_THM] th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `m1:num = m2` SUBST_ALL_TAC THENL
     [REMOVE_THEN "div" (MP_TAC o SPEC
       `\i. (if i = a then &m1 else (r1:K->int) i) -
            (if i = a then &m2 else r2 i)`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
      UNDISCH_TAC `m1:num < N` THEN UNDISCH_TAC `m2:num < N` THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_EQ] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r1:K->int = r2` (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "unique" MATCH_MP_TAC THEN ASM_SIMP_TAC[INT_SUB_REFL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `(x:K->int) IN L ==> y = x ==> y IN L`)) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[INT_SUB_REFL];
    REMOVE_THEN "unique" (K ALL_TAC) THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ; FUN_EQ_THM] THEN
      MAP_EVERY X_GEN_TAC [`m1:num`; `r1:K->int`; `m2:num`; `r2:K->int`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(r1:K->int) a = &0 /\ (r2:K->int) a = &0`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(r1:K->int) IN R0`; `(r2:K->int) IN R0`;
                               `~((a:K) IN t)`] THEN
        USE_THEN "supp"
       (fun th -> MESON_TAC[REWRITE_RULE[SUBSET; IN_ELIM_THM] th]);
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[INT_OF_NUM_EQ];
        X_GEN_TAC `i:K` THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
        ASM_CASES_TAC `i:K = a` THEN ASM_SIMP_TAC[]];
      REWRITE_TAC[SET_RULE
       `{(m:num,r:K->int) | m < N /\ r IN R0} =
        {(m,r) | m IN {m | m < N} /\ r IN R0}`] THEN
      MATCH_MP_TAC HAS_SIZE_PRODUCT THEN
      ASM_REWRITE_TAC[HAS_SIZE_NUMSEG_LT]]]);;

let INT_MATRIX_IMAGE_TRANSVERSAL = prove
 (`!s (M:K->K->int).
        FINITE s /\ ~(ring_det integer_ring s M = &0)
        ==> ?R. R SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
                (!x. (!i. ~(i IN s) ==> x i = &0)
                     ==> ?r. r IN R /\
                             (\i. x i - r i) IN int_matrix_image s M) /\
                (!r r'. r IN R /\ r' IN R /\
                        (\i. r i - r' i) IN int_matrix_image s M ==> r = r') /\
                R HAS_SIZE num_of_int(abs(ring_det integer_ring s M))`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [X_GEN_TAC `M:K->K->int` THEN DISCH_TAC THEN
    EXISTS_TAC `{(\i. &0):K->int}` THEN
    REWRITE_TAC[RING_DET_EMPTY; INTEGER_RING; INT_ABS_NUM; NUM_OF_INT_OF_NUM;
                HAS_SIZE; FINITE_SING; CARD_SING; NOT_IN_EMPTY; SUBSET;
                IN_SING; IN_ELIM_THM; INT_MATRIX_IMAGE_IN] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(\i. &0):K->int` THEN ASM_REWRITE_TAC[FUN_EQ_THM] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `M:K->K->int` THEN DISCH_TAC THEN
  ABBREV_TAC `L = int_matrix_image (a INSERT t) (M:K->K->int)` THEN
  SUBGOAL_THEN `int_lattice (a INSERT t) (L:(K->int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC INT_LATTICE_INT_MATRIX_IMAGE THEN
    ASM_REWRITE_TAC[FINITE_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `L:(K->int)->bool`]
    INT_LATTICE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:K->int`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "div")))) THEN
  MP_TAC(ISPECL [`t:K->bool`; `{x | x IN L /\ (x:K->int) a = &0}`]
    INT_LATTICE_MATRIX_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:K->K->int` (LABEL_TAC "M0")) THEN
  ABBREV_TAC `N = \i j. if j = a then (w:K->int) i
                        else if i IN t then (M0:K->K->int) i j else &0` THEN
  SUBGOAL_THEN `L = int_matrix_image (a INSERT t) (N:K->K->int)`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN MATCH_MP_TAC INT_LATTICE_INSERT_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_det integer_ring (a INSERT t) (N:K->K->int) =
    w a * ring_det integer_ring t M0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:K`; `t:K->bool`; `N:K->K->int`] INT_DET_INSERT_ROW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      EXPAND_TAC "N" THEN
      SUBGOAL_THEN `~(j:K = a)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "N" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(j:K = a)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(ring_det integer_ring (a INSERT t) (N:K->K->int)) =
    abs(ring_det integer_ring (a INSERT t) (M:K->K->int))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INT_MATRIX_IMAGE_EQ_DET THEN
    ASM_REWRITE_TAC[FINITE_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((w:K->int) a = &0) /\ ~(ring_det integer_ring t (M0:K->K->int) = &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ring_det integer_ring (a INSERT t) (N:K->K->int) =
       w a * ring_det integer_ring t M0`;
      `abs(ring_det integer_ring (a INSERT t) (N:K->K->int)) =
       abs(ring_det integer_ring (a INSERT t) (M:K->K->int))`;
      `~(ring_det integer_ring (a INSERT t) (M:K->K->int) = &0)`] THEN
    REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM INT_ENTIRE] THEN
    MESON_TAC[INT_ABS_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `num_of_int(abs((w:K->int) a)) *
    num_of_int(abs(ring_det integer_ring t (M0:K->K->int))) =
    num_of_int(abs(ring_det integer_ring (a INSERT t) (M:K->K->int)))`
  (LABEL_TAC "size") THENL
   [SIMP_TAC[GSYM NUM_OF_INT_MUL; INT_ABS_POS; GSYM INT_ABS_MUL] THEN
    AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `abs(ring_det integer_ring (a INSERT t) (N:K->K->int))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M0:K->K->int`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "M0" (fun th -> REWRITE_TAC[GSYM th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:(K->int)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `L:(K->int)->bool`; `w:K->int`;
                 `R0:(K->int)->bool`;
                 `num_of_int(abs(ring_det integer_ring t (M0:K->K->int)))`]
    INT_LATTICE_TRANSVERSAL_INSERT) THEN
  ASM_REWRITE_TAC[]);;

let INT_COSETS_MATRIX_IMAGE = prove
 (`!s (M:K->K->int).
        FINITE s /\ ~(ring_det integer_ring s M = &0)
        ==> int_cosets s (int_matrix_image s M) HAS_SIZE
            num_of_int(abs(ring_det integer_ring s M))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `M:K->K->int`] INT_MATRIX_IMAGE_TRANSVERSAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:(K->int)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC INT_COSETS_TRANSVERSAL THEN EXISTS_TAC `R:(K->int)->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_LATTICE_INT_MATRIX_IMAGE THEN
  ASM_REWRITE_TAC[]);;
