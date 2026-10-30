(* ========================================================================= *)
(* Determinants over an arbitrary commutative ring, for square arrays        *)
(* f:A->A->B whose rows and columns are indexed by a finite set s:A->bool,   *)
(* characteristic polynomials, the trace, norm and discriminant of algebras  *)
(* with a finite projective or free basis, and resultants and discriminants  *)
(* of univariate polynomials.                                                *)
(*                                                                           *)
(*   ring_sign r p  = ring_1 r or ring_neg r (ring_1 r) (sign of p)          *)
(*   ring_det r s f = sum over p permutes s of                               *)
(*                    ring_sign r p * product over i IN s of f i (p i)       *)
(*   ring_cofactor r s f i j = ring_det of f with row i replaced by e_j      *)
(*   ring_charpoly r s f = ring_det of (X I - f) in poly_ring r (:1)         *)
(*   free_basis (k,l) h n g = g 0, ..., g (n - 1) is a basis of l as a       *)
(*                    module over k via h:A->B                               *)
(*   projective_basis (k,l) h n e f = x = sum_i h(f i x) e i for all x in l, *)
(*                    with the f i additive and k-linear maps from l to k    *)
(*   algebra_trace (k,l) h x, algebra_norm (k,l) h x = trace of A and        *)
(*                    determinant of A + I - E for A i j = f i (x e j) and   *)
(*                    E i j = f i (e j) in a finite projective basis (ring_0 *)
(*                    k and ring_1 k if there is none); in a free basis g    *)
(*                    the trace and determinant of mul_matrix (k,l) h n g x  *)
(*   basis_discriminant (k,l) h n g = ring_det of the trace form, the array  *)
(*                    of the algebra_trace (k,l) h (g i * g j) for i, j < n  *)
(*   poly_resultant r p q = ring_det of the Sylvester matrix of p and q      *)
(*   poly_discriminant r p = (-1)^(n(n-1)/2) Res(p,poly_deriv r p) / lc p    *)
(*                    for n = deg p, as a determinant without division (the  *)
(*                    derivative taken with the formal degree n - 1)         *)
(*                                                                           *)
(* With these degree conventions two constants have resultant 1, and every   *)
(* constant, including the zero polynomial, has discriminant 1.              *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/permutations.ml";;

(* ------------------------------------------------------------------------- *)
(* Sign of a permutation as a ring element, and the determinant.             *)
(* ------------------------------------------------------------------------- *)

let ring_sign = new_definition
 `ring_sign (r:B ring) (p:A->A) =
        if evenperm p then ring_1 r else ring_neg r (ring_1 r)`;;

let ring_det = new_definition
 `ring_det r (s:A->bool) (f:A->A->B) =
        ring_sum r {p | p permutes s}
                 (\p. ring_mul r (ring_sign r p)
                                 (ring_product r s (\i. f i (p i))))`;;

let RING_SIGN = prove
 (`!(r:B ring) (p:A->A). ring_sign r p IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_sign] THEN COND_CASES_TAC THEN
  SIMP_TAC[RING_1; RING_NEG]);;

let RING_SIGN_I = prove
 (`!r:B ring. ring_sign r (I:A->A) = ring_1 r`,
  REWRITE_TAC[ring_sign; EVENPERM_I]);;

let RING_SIGN_ID = prove
 (`!r:B ring. ring_sign r (\x:A. x) = ring_1 r`,
  REWRITE_TAC[ring_sign; EVENPERM_ID]);;

let RING_SIGN_SWAP = prove
 (`!(r:B ring) a b:A. ring_sign r (swap(a,b)) =
             if a = b then ring_1 r else ring_neg r (ring_1 r)`,
  REWRITE_TAC[ring_sign; EVENPERM_SWAP]);;

let RING_SIGN_COMPOSE = prove
 (`!(r:B ring) p q:A->A.
        permutation p /\ permutation q
        ==> ring_sign r (p o q) = ring_mul r (ring_sign r p) (ring_sign r q)`,
  SIMP_TAC[ring_sign; EVENPERM_COMPOSE] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`evenperm(p:A->A)`; `evenperm(q:A->A)`] THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_RID; RING_1; RING_NEG;
               RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG]);;

let RING_SIGN_INVERSE = prove
 (`!(r:B ring) p:A->A.
        permutation p ==> ring_sign r (inverse p) = ring_sign r p`,
  SIMP_TAC[ring_sign; EVENPERM_INVERSE]);;

let RING_SIGN_IDEMPOTENT = prove
 (`!(r:B ring) p:A->A. ring_mul r (ring_sign r p) (ring_sign r p) = ring_1 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_sign] THEN COND_CASES_TAC THEN
  SIMP_TAC[RING_MUL_LID; RING_1; RING_NEG; RING_MUL_LNEG; RING_MUL_RNEG;
           RING_NEG_NEG]);;

let RING_HOMOMORPHISM_SIGN = prove
 (`!(r:B ring) (r':C ring) (h:B->C) (p:A->A).
        ring_homomorphism(r,r') h ==> h(ring_sign r p) = ring_sign r' p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sign] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_1; RING_HOMOMORPHISM_NEG; RING_1]);;

(* ------------------------------------------------------------------------- *)
(* Reindexing ring sums over permutations and ring products.                 *)
(* ------------------------------------------------------------------------- *)

let RING_PRODUCT_PERMUTE = prove
 (`!(r:B ring) (f:A->B) p s.
        p permutes s ==> ring_product r s f = ring_product r s (f o p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `p:A->A`; `f:A->B`; `s:A->bool`]
    RING_PRODUCT_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PERMUTES_INJECTIVE]; ASM_SIMP_TAC[PERMUTES_IMAGE]]);;

let RING_SUM_PERMUTE = prove
 (`!(r:B ring) (f:A->B) p s.
        p permutes s ==> ring_sum r s f = ring_sum r s (f o p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `p:A->A`; `f:A->B`; `s:A->bool`]
    RING_SUM_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PERMUTES_INJECTIVE]; ASM_SIMP_TAC[PERMUTES_IMAGE]]);;

let RING_SUM_PERMUTATIONS_INVERSE = prove
 (`!(r:B ring) (f:(A->A)->B) s.
        ring_sum r {p | p permutes s} f =
        ring_sum r {p | p permutes s} (\p. f(inverse p))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM IMAGE_INVERSE_PERMUTATIONS] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [SET_RULE `{(f:(A->A)->(A->A)) x | (P:(A->A)->bool) x} =
              IMAGE f {x | P x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC RING_SUM_IMAGE THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PERMUTES_INVERSE_INVERSE]);;

let RING_SUM_PERMUTATIONS_COMPOSE_L = prove
 (`!(r:B ring) (f:(A->A)->B) s q.
        q permutes s
        ==> ring_sum r {p | p permutes s} f =
            ring_sum r {p | p permutes s} (\p. f(q o p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)]) THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [SET_RULE `{(f:(A->A)->(A->A)) x | (P:(A->A)->bool) x} =
              IMAGE f {x | P x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC RING_SUM_IMAGE THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\p:A->A. inverse(q:A->A) o p`) THEN
  REWRITE_TAC[o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_O_ID]);;

let RING_SUM_PERMUTATIONS_COMPOSE_R = prove
 (`!(r:B ring) (f:(A->A)->B) s q.
        q permutes s
        ==> ring_sum r {p | p permutes s} f =
            ring_sum r {p | p permutes s} (\p. f(p o q))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)]) THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [SET_RULE `{(f:(A->A)->(A->A)) x | (P:(A->A)->bool) x} =
              IMAGE f {x | P x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC RING_SUM_IMAGE THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\p:A->A. p o inverse(q:A->A)`) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_O_ID]);;

let PERMUTES_INJECTIVE_RESTRICT = prove
 (`!s (mu:A->A).
        FINITE s /\ (!x. x IN s ==> mu x IN s) /\
        (!x y. x IN s /\ y IN s /\ mu x = mu y ==> x = y)
        ==> (\x. if x IN s then mu x else x) permutes s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PERMUTES_FINITE_INJECTIVE; IMP_CONJ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties.                                                         *)
(* ------------------------------------------------------------------------- *)

let RING_DET = prove
 (`!(r:B ring) s (f:A->A->B). ring_det r s f IN ring_carrier r`,
  REWRITE_TAC[ring_det; RING_SUM]);;

let RING_DET_EQ = prove
 (`!(r:B ring) s (f:A->A->B) g.
        (!i j. i IN s /\ j IN s ==> f i j = g i j)
        ==> ring_det r s f = ring_det r s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let RING_DET_EMPTY = prove
 (`!(r:B ring) (f:A->A->B). ring_det r {} f = ring_1 r`,
  REWRITE_TAC[ring_det; PERMUTES_EMPTY;
              SET_RULE `{x:A->A | x = a} = {a}`] THEN
  REWRITE_TAC[RING_SUM_SING; RING_PRODUCT_CLAUSES; RING_SIGN_I] THEN
  SIMP_TAC[RING_MUL_LID; RING_1]);;

let RING_DET_TRANSP = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s ==> ring_det r s (\i j. f j i) = ring_det r s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  GEN_REWRITE_TAC RAND_CONV [RING_SUM_PERMUTATIONS_INVERSE] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `permutation(p:A->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTATION_PERMUTES]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SIGN_INVERSE] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `!x:A. inverse p ((p:A->A) x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_INVERSES]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:B ring`; `\i. (f:A->A->B) i (inverse p i)`;
                 `p:A->A`; `s:A->bool`] RING_PRODUCT_PERMUTE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let RING_DET_PERMUTE_ROWS = prove
 (`!(r:B ring) s (f:A->A->B) q.
        FINITE s /\ q permutes s
        ==> ring_det r s (\i j. f (q i) j) =
            ring_mul r (ring_sign r q) (ring_det r s f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP RING_SUM_PERMUTATIONS_COMPOSE_R th]) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_SIGN; FINITE_PERMUTATIONS; RING_MUL; RING_PRODUCT];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_product r s (\i. (f:A->A->B) (q i) ((p o q) i)) =
    ring_product r s (\i. f i (p i))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`r:B ring`; `\i. (f:A->A->B) i (p i)`;
                   `q:A->A`; `s:A->bool`] RING_PRODUCT_PERMUTE) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_sign (r:B ring) ((p:A->A) o q) =
                ring_mul r (ring_sign r p) (ring_sign r q)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SIGN_COMPOSE THEN
    ASM_MESON_TAC[PERMUTATION_PERMUTES];
    ALL_TAC] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r (ring_mul r a b) c = ring_mul r b (ring_mul r a (c:B))`) THEN
  REWRITE_TAC[RING_SIGN; RING_PRODUCT]);;

let RING_DET_PERMUTE_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B) q.
        FINITE s /\ q permutes s
        ==> ring_det r s (\i j. f i (q j)) =
            ring_mul r (ring_sign r q) (ring_det r s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `\i j. (f:A->A->B) i ((q:A->A) j)`]
    RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `\i j. (f:A->A->B) j i`;
                 `q:A->A`] RING_DET_PERMUTE_ROWS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[]);;

let RING_DET_SWAP_ROWS = prove
 (`!(r:B ring) s (f:A->A->B) a b.
        FINITE s /\ a IN s /\ b IN s /\ ~(a = b)
        ==> ring_det r s (\i j. f (swap(a,b) i) j) =
            ring_neg r (ring_det r s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `swap(a:A,b)`]
    RING_DET_PERMUTE_ROWS) THEN
  ASM_SIMP_TAC[PERMUTES_SWAP; RING_SIGN_SWAP; RING_MUL_LNEG; RING_MUL_LID;
               RING_1; RING_DET]);;

let RING_DET_SWAP_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B) a b.
        FINITE s /\ a IN s /\ b IN s /\ ~(a = b)
        ==> ring_det r s (\i j. f i (swap(a,b) j)) =
            ring_neg r (ring_det r s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `swap(a:A,b)`]
    RING_DET_PERMUTE_COLUMNS) THEN
  ASM_SIMP_TAC[PERMUTES_SWAP; RING_SIGN_SWAP; RING_MUL_LNEG; RING_MUL_LID;
               RING_1; RING_DET]);;

(* ------------------------------------------------------------------------- *)
(* Two equal rows (or columns) give determinant zero, in any characteristic: *)
(* the odd permutations are the even ones composed with a transposition.     *)
(* ------------------------------------------------------------------------- *)

let RING_DET_IDENTICAL_ROWS = prove
 (`!(r:B ring) s (f:A->A->B) a b.
        FINITE s /\ a IN s /\ b IN s /\ ~(a = b) /\
        (!j. j IN s ==> f a j = f b j)
        ==> ring_det r s f = ring_0 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  ABBREV_TAC
   `tt = \p:A->A. ring_mul r (ring_sign r p)
                     (ring_product r s (\i. (f:A->A->B) i (p i)))` THEN
  ABBREV_TAC `ev = {p:A->A | p permutes s /\ evenperm p}` THEN
  SUBGOAL_THEN
   `permutation(swap(a:A,b)) /\ ~evenperm(swap(a:A,b)) /\
    swap(a,b) permutes s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PERMUTATION_SWAP; EVENPERM_SWAP; PERMUTES_SWAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:A->A. p permutes s ==> permutation p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTATION_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(ev:(A->A)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p:A->A | p permutes s}` THEN
    ASM_SIMP_TAC[FINITE_PERMUTATIONS] THEN EXPAND_TAC "ev" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p:A->A | p permutes s} = ev UNION IMAGE (\p. p o swap(a,b)) ev`
  SUBST1_TAC THENL
   [EXPAND_TAC "ev" THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A->A` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `evenperm(p:A->A)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(p:A->A) o swap(a,b)` THEN
      REWRITE_TAC[GSYM o_ASSOC; SWAP_IDEMPOTENT; I_O_ID] THEN
      ASM_SIMP_TAC[PERMUTES_COMPOSE; EVENPERM_COMPOSE];
      STRIP_TAC THEN ASM_MESON_TAC[PERMUTES_COMPOSE]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN EXPAND_TAC "ev" THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[EVENPERM_COMPOSE];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\p:A->A. p o swap(a,b)`) THEN
    REWRITE_TAC[GSYM o_ASSOC; SWAP_IDEMPOTENT; I_O_ID];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_ADD o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "tt" THEN
    SIMP_TAC[o_THM; RING_MUL; RING_SIGN; RING_PRODUCT];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC `p:A->A` THEN
  EXPAND_TAC "ev" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXPAND_TAC "tt" THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `ring_sign (r:B ring) ((p:A->A) o swap(a,b)) =
                ring_neg r (ring_1 r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ring_sign] THEN ASM_SIMP_TAC[EVENPERM_COMPOSE]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_sign (r:B ring) (p:A->A) = ring_1 r` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[ring_sign]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product r s (\i. (f:A->A->B) i (p(swap(a,b) i))) =
    ring_product r s (\i. f i (p i))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`r:B ring`; `\i. (f:A->A->B) i (p(swap(a,b) i))`;
                   `swap(a:A,b)`; `s:A->bool`] RING_PRODUCT_PERMUTE) THEN
    ASM_REWRITE_TAC[o_DEF;
      REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[swap] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SIMP_TAC[RING_MUL_LID; RING_MUL_LNEG; RING_1; RING_PRODUCT;
           RING_ADD_RNEG]);;

let RING_DET_IDENTICAL_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B) a b.
        FINITE s /\ a IN s /\ b IN s /\ ~(a = b) /\
        (!i. i IN s ==> f i a = f i b)
        ==> ring_det r s f = ring_0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_IDENTICAL_ROWS THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linearity in one row.                                                     *)
(* ------------------------------------------------------------------------- *)

let RING_PRODUCT_DELETE = prove
 (`!(r:B ring) (f:A->B) s a.
        FINITE s /\ a IN s /\ f a IN ring_carrier r
        ==> ring_mul r (f a) (ring_product r (s DELETE a) f) =
            ring_product r s f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s = (a:A) INSERT (s DELETE a)` (fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th])
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE]);;

let RING_DET_ROW_EXPANSION = prove
 (`!(r:B ring) s (f:A->A->B) k v.
        FINITE s /\ k IN s /\ (!j. j IN s ==> v j IN ring_carrier r)
        ==> ring_det r s (\i j. if i = k then v j else f i j) =
            ring_sum r {p | p permutes s}
             (\p. ring_mul r (v (p k))
                    (ring_mul r (ring_sign r p)
                       (ring_product r (s DELETE k) (\i. f i (p i)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:A->B) ((p:A->A) k) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:B ring`;
                 `\i. if i = k then (v:A->B) ((p:A->A) i)
                      else (f:A->A->B) i (p i)`;
                 `s:A->bool`; `k:A`] RING_PRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `ring_product r (s DELETE k)
       (\i. if i = k then (v:A->B) ((p:A->A) i) else (f:A->A->B) i (p i)) =
    ring_product r (s DELETE k) (\i. f i (p i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))`) THEN
  ASM_REWRITE_TAC[RING_SIGN; RING_PRODUCT]);;

let RING_DET_ROW_CMUL = prove
 (`!(r:B ring) s (f:A->A->B) k c v.
        FINITE s /\ k IN s /\ c IN ring_carrier r /\
        (!j. j IN s ==> v j IN ring_carrier r)
        ==> ring_det r s (\i j. if i = k then ring_mul r c (v j) else f i j) =
            ring_mul r c (ring_det r s (\i j. if i = k then v j else f i j))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_EXPANSION o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_DET_ROW_EXPANSION] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
    ASM_MESON_TAC[RING_SIGN; RING_PRODUCT; PERMUTES_IN_IMAGE];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN
  ASM_SIMP_TAC[RING_MUL; RING_SIGN; RING_PRODUCT] THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let RING_DET_ROW_ADD = prove
 (`!(r:B ring) s (f:A->A->B) k u v.
        FINITE s /\ k IN s /\
        (!j. j IN s ==> u j IN ring_carrier r /\ v j IN ring_carrier r)
        ==> ring_det r s (\i j. if i = k then ring_add r (u j) (v j)
                                else f i j) =
            ring_add r (ring_det r s (\i j. if i = k then u j else f i j))
                       (ring_det r s (\i j. if i = k then v j else f i j))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_EXPANSION o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_ADD] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_DET_ROW_EXPANSION] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_ADD o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
    ASM_MESON_TAC[RING_SIGN; RING_PRODUCT; PERMUTES_IN_IMAGE];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_ADD_RDISTRIB THEN
  ASM_SIMP_TAC[RING_MUL; RING_SIGN; RING_PRODUCT] THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let RING_DET_ROW_SUM = prove
 (`!(r:B ring) s (f:A->A->B) k t (g:C->A->B).
        FINITE s /\ FINITE t /\ k IN s /\
        (!x j. x IN t /\ j IN s ==> g x j IN ring_carrier r)
        ==> ring_det r s (\i j. if i = k then ring_sum r t (\x. g x j)
                                else f i j) =
            ring_sum r t
             (\x. ring_det r s (\i j. if i = k then g x j else f i j))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_EXPANSION o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_DET_ROW_EXPANSION] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
    ASM_MESON_TAC[RING_SIGN; RING_PRODUCT; PERMUTES_IN_IMAGE];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RMUL THEN
  ASM_SIMP_TAC[RING_MUL; RING_SIGN; RING_PRODUCT] THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

let RING_DET_ROW_0 = prove
 (`!(r:B ring) s (f:A->A->B) k.
        FINITE s /\ k IN s
        ==> ring_det r s (\i j. if i = k then ring_0 r else f i j) =
            ring_0 r`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_EXPANSION o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_0] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN
  SIMP_TAC[RING_MUL_LZERO; RING_MUL; RING_SIGN; RING_PRODUCT]);;

let RING_DET_ROWS_MUL = prove
 (`!(r:B ring) s (c:A->B) (f:A->A->B).
        FINITE s /\ (!i. i IN s ==> c i IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_det r s (\i j. ring_mul r (c i) (f i j)) =
            ring_mul r (ring_product r s c) (ring_det r s f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_PRODUCT; FINITE_PERMUTATIONS; RING_MUL; RING_SIGN];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_MUL o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))`) THEN
  REWRITE_TAC[RING_SIGN; RING_PRODUCT]);;

let RING_DET_COLUMNS_MUL = prove
 (`!(r:B ring) s (c:A->B) (f:A->A->B).
        FINITE s /\ (!j. j IN s ==> c j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_det r s (\i j. ring_mul r (f i j) (c j)) =
            ring_mul r (ring_det r s f) (ring_product r s c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`;
                 `\i j. ring_mul r ((f:A->A->B) i j) ((c:A->B) j)`]
    RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRANS_TAC EQ_TRANS
   `ring_det r s (\i j. ring_mul r ((c:A->B) i) ((f:A->A->B) j i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[RING_MUL_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `c:A->B`; `\i j. (f:A->A->B) j i`]
    RING_DET_ROWS_MUL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_MUL_SYM THEN REWRITE_TAC[RING_PRODUCT; RING_DET]);;

let RING_DET_ROW_OPERATION = prove
 (`!(r:B ring) s (f:A->A->B) k l c.
        FINITE s /\ k IN s /\ l IN s /\ ~(k = l) /\ c IN ring_carrier r /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_det r s (\i j. if i = k
                                then ring_add r (f k j) (ring_mul r c (f l j))
                                else f i j) =
            ring_det r s f`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_ADD o lhand o snd) THEN
  ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_CMUL o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_det r s (\i j. if i = k then (f:A->A->B) l j else f i j) = ring_0 r`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`k:A`; `l:A`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_det r s (\i j. if i = k then (f:A->A->B) k j else f i j) =
    ring_det r s f`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; RING_ADD_RZERO; RING_DET]);;

(* ------------------------------------------------------------------------- *)
(* Expansion of all rows as sums: a sum over the cartesian product.          *)
(* ------------------------------------------------------------------------- *)

let RING_SUM_PRODUCT_CARTESIAN_PRODUCT = prove
 (`!(r:B ring) (k:K->bool) (t:K->A->bool) (g:K->A->B).
        FINITE k /\ (!i. i IN k ==> FINITE(t i)) /\
        (!i x. i IN k /\ x IN t i ==> g i x IN ring_carrier r)
        ==> ring_sum r (cartesian_product k t)
                       (\mu. ring_product r k (\i. g i (mu i))) =
            ring_product r k (\i. ring_sum r (t i) (g i))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[CARTESIAN_PRODUCT_EMPTY; RING_SUM_SING;
                RING_PRODUCT_CLAUSES; RING_1];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `k:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `t:K->A->bool` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  STRIP_TAC THEN X_GEN_TAC `g:K->A->B` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN t a ==> (g:K->A->B) a x IN ring_carrier r) /\
    (!i x. i IN k /\ x IN t i ==> g i x IN ring_carrier r)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product r (a INSERT k)
      (\i. ring_sum r ((t:K->A->bool) i) ((g:K->A->B) i)) =
    ring_mul r (ring_sum r (t a) (g a))
               (ring_product r k (\i. ring_sum r (t i) (g i)))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; RING_SUM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:K->A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:K->A->B`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `cartesian_product (a INSERT k) (t:K->A->bool) =
    IMAGE (\(x,y). \i. if i = a then y else x i)
          (cartesian_product k t CROSS t a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
                IN_CARTESIAN_PRODUCT; EXTENSIONAL; IN_ELIM_THM] THEN
    X_GEN_TAC `z:K->A` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`\i. if i = a then ARB else (z:K->A) i`; `(z:K->A) a`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[IN_INSERT];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:K->A`; `y:A`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(cartesian_product k (t:K->A->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:K->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FORALL_PAIR_THM; IN_CROSS;
                 IN_CARTESIAN_PRODUCT; EXTENSIONAL; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:K->A`; `y:A`; `x':K->A`; `y':A`] THEN
    REWRITE_TAC[FUN_EQ_THM; PAIR_EQ] THEN STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `i:K` THEN ASM_CASES_TAC `i:K = a` THENL
       [ASM_MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN REWRITE_TAC[CROSS] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUM_PRODUCT o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_PRODUCT]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_SUM; RING_PRODUCT]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `x:K->A` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_PRODUCT]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[RING_PRODUCT_CLAUSES] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i:K = a)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let RING_DET_MULTILINEAR = prove
 (`!(r:B ring) s (t:A->C->bool) (f:A->A->B) (g:A->C->A->B).
        FINITE s /\ (!i. i IN s ==> FINITE(t i)) /\
        (!i x j. i IN s /\ x IN t i /\ j IN s ==> g i x j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s ==> f i j = ring_sum r (t i) (\x. g i x j))
        ==> ring_det r s f =
            ring_sum r (cartesian_product s t)
                     (\mu. ring_det r s (\i j. g i (mu i) j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  SUBGOAL_THEN `FINITE(cartesian_product s (t:A->C->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PERMUTATIONS; RING_MUL; RING_SIGN; RING_PRODUCT];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_LMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_SIGN; RING_PRODUCT]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_product r s (\i. ring_sum r ((t:A->C->bool) i)
                          (\x. (g:A->C->A->B) i x ((p:A->A) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    CONV_TAC SYM_CONV] THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `t:A->C->bool`;
                 `\i x. (g:A->C->A->B) i x ((p:A->A) i)`]
    RING_SUM_PRODUCT_CARTESIAN_PRODUCT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    DISCH_THEN(ACCEPT_TAC o CONV_RULE(REDEPTH_CONV BETA_CONV))]);;

(* ------------------------------------------------------------------------- *)
(* Compatibility with ring homomorphisms.                                    *)
(* ------------------------------------------------------------------------- *)

let RING_DET_HOMOMORPHISM = prove
 (`!(r:B ring) (r':C ring) (h:B->C) s (f:A->A->B).
        ring_homomorphism(r,r') h /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> h(ring_det r s f) = ring_det r' s (\i j. h(f i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
    (MATCH_MP RING_HOMOMORPHISM_SUM th) o lhand o snd)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PERMUTATIONS; RING_MUL; RING_SIGN; RING_PRODUCT];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                                 RING_SIGN; RING_PRODUCT]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_SIGN th]) THEN
  AP_TERM_TAC THEN
  FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
    (MATCH_MP RING_HOMOMORPHISM_PRODUCT th) o lhand o snd)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

(* ------------------------------------------------------------------------- *)
(* Diagonal arrays and the identity.                                         *)
(* ------------------------------------------------------------------------- *)

let RING_DET_DIAGONAL = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s /\
        (!i j. i IN s /\ j IN s /\ ~(i = j) ==> f i j = ring_0 r)
        ==> ring_det r s f = ring_product r s (\i. f i i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p | p permutes s}
      (\p. if p = I then ring_product r s (\i. (f:A->A->B) i i)
           else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_SIGN_I; I_THM] THENL
     [SIMP_TAC[RING_MUL_LID; RING_PRODUCT]; ALL_TAC] THEN
    SUBGOAL_THEN `?i:A. i IN s /\ ~(p i = i)` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
      REWRITE_TAC[I_THM; NOT_FORALL_THM] THEN ASM_MESON_TAC[permutes];
      ALL_TAC] THEN
    SUBGOAL_THEN `ring_product r s (\i. (f:A->A->B) i (p i)) = ring_0 r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_ZERO THEN EXISTS_TAC `i:A` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE];
      SIMP_TAC[RING_MUL_RZERO; RING_SIGN]];
    REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; PERMUTES_I; RING_PRODUCT]]);;

let RING_DET_I = prove
 (`!(r:B ring) (s:A->bool).
        FINITE s
        ==> ring_det r s (\i j. if i = j then ring_1 r else ring_0 r) =
            ring_1 r`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
  ASM_SIMP_TAC[RING_PRODUCT_1]);;

(* ------------------------------------------------------------------------- *)
(* Cofactors (row i replaced by the unit vector e_j), cofactor expansion     *)
(* and the adjugate identities.                                              *)
(* ------------------------------------------------------------------------- *)

let ring_cofactor = new_definition
 `ring_cofactor r (s:A->bool) (f:A->A->B) i j =
        ring_det r s (\k l. if k = i then if l = j then ring_1 r else ring_0 r
                            else f k l)`;;

let RING_COFACTOR = prove
 (`!(r:B ring) s (f:A->A->B) i j. ring_cofactor r s f i j IN ring_carrier r`,
  REWRITE_TAC[ring_cofactor; RING_DET]);;

let RING_COFACTOR_EQ = prove
 (`!(r:B ring) s (f:A->A->B) g i j.
        (!k l. k IN s /\ l IN s /\ ~(k = i) ==> f k l = g k l)
        ==> ring_cofactor r s f i j = ring_cofactor r s g i j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_cofactor] THEN
  MATCH_MP_TAC RING_DET_EQ THEN ASM_MESON_TAC[]);;

let RING_DET_ROW_COFACTOR_EXPANSION = prove
 (`!(r:B ring) s (f:A->A->B) i v.
        FINITE s /\ i IN s /\ (!j. j IN s ==> v j IN ring_carrier r)
        ==> ring_det r s (\k l. if k = i then v l else f k l) =
            ring_sum r s (\j. ring_mul r (v j) (ring_cofactor r s f i j))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_det r s (\k l. if k = i
                        then ring_sum r s (\j. ring_mul r ((v:A->B) j)
                                (if l = j then ring_1 r else ring_0 r))
                        else (f:A->A->B) k l)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`k:A`; `l:A`] THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r s (\j. if j = l then (v:A->B) l else ring_0 r)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[RING_SUM_DELTA] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_CASES_TAC `j:A = l` THEN
      ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_SUM o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL; RING_1; RING_0];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
  REWRITE_TAC[ring_cofactor] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_CMUL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[RING_1; RING_0];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let RING_DET_COFACTOR_EXPANSION = prove
 (`!(r:B ring) s (f:A->A->B) i.
        FINITE s /\ i IN s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_det r s f =
            ring_sum r s (\j. ring_mul r (f i j) (ring_cofactor r s f i j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `i:A`;
                 `(f:A->A->B) i`] RING_DET_ROW_COFACTOR_EXPANSION) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_EQ THEN MESON_TAC[]);;

let RING_DET_ADJUGATE_ROWS = prove
 (`!(r:B ring) s (f:A->A->B) i k.
        FINITE s /\ i IN s /\ k IN s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_sum r s (\j. ring_mul r (f i j) (ring_cofactor r s f k j)) =
            if i = k then ring_det r s f else ring_0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `k:A`;
                 `(f:A->A->B) i`] RING_DET_ROW_COFACTOR_EXPANSION) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
    MESON_TAC[];
    MATCH_MP_TAC RING_DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`k:A`; `i:A`] THEN ASM_MESON_TAC[]]);;

let RING_COFACTOR_TRANSP = prove
 (`!(r:B ring) s (f:A->A->B) i j.
        FINITE s /\ i IN s /\ j IN s
        ==> ring_cofactor r s (\i j. f j i) i j = ring_cofactor r s f j i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_cofactor] THEN
  MP_TAC(ISPECL
   [`r:B ring`; `s:A->bool`;
    `\k l. if k = i then if l = j then ring_1 r else ring_0 r
           else (f:A->A->B) l k`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ring_det] THEN MATCH_MP_TAC RING_SUM_EQ THEN
  X_GEN_TAC `p:A->A` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN ASM_CASES_TAC `(p:A->A) j = i` THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `k:A = j` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((p:A->A) k = i)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A->A) (inverse p i) = i /\ inverse p i IN s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_INVERSE; PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(inverse (p:A->A) i = j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ring_0 r:B` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_ZERO THEN
    EXISTS_TAC `inverse(p:A->A) i` THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_ZERO THEN
    EXISTS_TAC `j:A` THEN ASM_REWRITE_TAC[]]);;

let RING_DET_ADJUGATE_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B) i k.
        FINITE s /\ i IN s /\ k IN s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_sum r s (\j. ring_mul r (ring_cofactor r s f j i) (f j k)) =
            if i = k then ring_det r s f else ring_0 r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_sum r s (\j. ring_mul r (ring_cofactor r s (f:A->A->B) j i)
                                 (f j k)) =
    ring_sum r s (\j. ring_mul r ((\i j. f j i) k j)
                                 (ring_cofactor r s (\i j. f j i) i j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[RING_COFACTOR_TRANSP] THEN
    MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_COFACTOR];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ADJUGATE_ROWS o
    lhand o snd) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closure: the determinant lies in any subset of the ring closed under the  *)
(* ring operations and containing the entries (e.g. a subring).              *)
(* ------------------------------------------------------------------------- *)

let RING_DET_CLOSED = prove
 (`!(r:B ring) P s (f:A->A->B).
        P(ring_0 r) /\ P(ring_1 r) /\
        (!x. x IN ring_carrier r /\ P x ==> P(ring_neg r x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_add r x y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_mul r x y)) /\
        (!i j. i IN s /\ j IN s ==> P(f i j))
        ==> P(ring_det r s f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  MATCH_MP_TAC RING_SUM_CLOSED THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(P:B->bool) (ring_sign r (p:A->A)) /\
    P(ring_product r s (\i. (f:A->A->B) i (p i)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ring_sign] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_1];
      MATCH_MP_TAC RING_PRODUCT_CLOSED THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE]];
    ASM_SIMP_TAC[RING_SIGN; RING_PRODUCT]]);;

let RING_DET_SUBRING = prove
 (`!(r:B ring) h s (f:A->A->B).
        h subring_of r /\ (!i j. i IN s /\ j IN s ==> f i j IN h)
        ==> ring_det r s f IN h`,
  REWRITE_TAC[subring_of] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `\x:B. x IN h`; `s:A->bool`; `f:A->A->B`]
    RING_DET_CLOSED) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cofactors only depend on the entries outside their row and column; the    *)
(* diagonal cofactor of an inserted index is the determinant on the rest.    *)
(* ------------------------------------------------------------------------- *)

let RING_COFACTOR_EQ_GEN = prove
 (`!(r:B ring) s (f:A->A->B) g i j.
        FINITE s /\ i IN s /\
        (!k l. k IN s /\ l IN s /\ ~(k = i) /\ ~(l = j) ==> f k l = g k l)
        ==> ring_cofactor r s f i j = ring_cofactor r s g i j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_cofactor; ring_det] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `(p:A->A) i = j` THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `k:A = i` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[PERMUTES_INJECTIVE; PERMUTES_IN_IMAGE];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ring_0 r:B` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC RING_PRODUCT_ZERO THEN EXISTS_TAC `i:A` THEN
    ASM_REWRITE_TAC[]]);;

let RING_COFACTOR_INSERT = prove
 (`!(r:B ring) s (f:A->A->B) a.
        FINITE s /\ ~(a IN s)
        ==> ring_cofactor r (a INSERT s) f a a = ring_det r s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_cofactor] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_EXPANSION o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SET_RULE `~((a:A) IN s) ==> (a INSERT s) DELETE a = s`] THEN
  REWRITE_TAC[ring_det] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p | p permutes (a INSERT s)}
      (\p. if (p:A->A) a = a
           then ring_mul r (ring_sign r p)
                  (ring_product r s (\i. (f:A->A->B) i (p i)))
           else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LZERO; RING_MUL; RING_SIGN;
                 RING_PRODUCT];
    REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A->A` THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SUPERSET THEN
      EXISTS_TAC `(a:A) INSERT s` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INSERT] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC PERMUTES_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ASM_MESON_TAC[permutes]]]]);;

(* ------------------------------------------------------------------------- *)
(* Linearly dependent rows: c_k det f = 0 for every k (any commutative       *)
(* ring), hence det f = 0 over an integral domain.                           *)
(* ------------------------------------------------------------------------- *)

let RING_DET_DEPENDENT_ROWS_MUL = prove
 (`!(r:B ring) s (f:A->A->B) c k.
        FINITE s /\ k IN s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        (!i. i IN s ==> c i IN ring_carrier r) /\
        (!j. j IN s ==> ring_sum r s (\i. ring_mul r (c i) (f i j)) =
                        ring_0 r)
        ==> ring_mul r (c k) (ring_det r s f) = ring_0 r`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_det r s (\i j. if i = k
                        then ring_sum r s
                               (\i. ring_mul r ((c:A->B) i) ((f:A->A->B) i j))
                        else f i j)` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_SUM o rand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r s (\x. if x = k
                        then ring_mul r ((c:A->B) k) (ring_det r s (f:A->A->B))
                        else ring_0 r)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL; RING_DET];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_ROW_CMUL o rand o snd) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC RING_DET_EQ THEN MESON_TAC[];
        SUBGOAL_THEN
         `ring_det r s (\i j. if i = k then (f:A->A->B) x j else f i j) =
          ring_0 r`
        SUBST1_TAC THENL
         [MATCH_MP_TAC RING_DET_IDENTICAL_ROWS THEN
          MAP_EVERY EXISTS_TAC [`k:A`; `x:A`] THEN ASM_MESON_TAC[];
          ASM_SIMP_TAC[RING_MUL_RZERO]]]];
    TRANS_TAC EQ_TRANS
     `ring_det r s (\i j. if i = k then ring_0 r else (f:A->A->B) i j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[RING_DET_ROW_0]]]);;

let RING_DET_DEPENDENT_ROWS = prove
 (`!(r:B ring) s (f:A->A->B) c.
        integral_domain r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        (!i. i IN s ==> c i IN ring_carrier r) /\
        (?i. i IN s /\ ~(c i = ring_0 r)) /\
        (!j. j IN s ==> ring_sum r s (\i. ring_mul r (c i) (f i j)) =
                        ring_0 r)
        ==> ring_det r s f = ring_0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `c:A->B`; `i:A`]
    RING_DET_DEPENDENT_ROWS_MUL) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_DET]);;

(* ------------------------------------------------------------------------- *)
(* Over a field: independent rows (indexed by u, columns by any set t) have  *)
(* a non-vanishing maximal minor; a square array with independent rows has   *)
(* non-zero determinant.                                                     *)
(* ------------------------------------------------------------------------- *)

let RING_DET_MINOR_SELECTION = prove
 (`!(r:B ring) (u:A->bool) (t:C->bool) (f:A->C->B).
        field r /\ FINITE u /\
        (!i j. i IN u /\ j IN t ==> f i j IN ring_carrier r) /\
        (!c. (!i. i IN u ==> c i IN ring_carrier r) /\
             (!j. j IN t
                  ==> ring_sum r u (\i. ring_mul r (c i) (f i j)) = ring_0 r)
             ==> !i. i IN u ==> c i = ring_0 r)
        ==> ?g. (!j. j IN u ==> g j IN t) /\
                (!j j'. j IN u /\ j' IN u /\ g j = g j' ==> j = j') /\
                ~(ring_det r u (\i j. f i (g j)) = ring_0 r)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s ==> t <=> p ==> q ==> r /\ s ==> t`]
  THEN DISCH_TAC THEN SPEC_TAC(`u:A->bool`,`u:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `\j:A. (ARB:C)` THEN
    REWRITE_TAC[NOT_IN_EMPTY; RING_DET_EMPTY] THEN ASM_MESON_TAC[field];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `u:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun ih -> DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun ind -> MP_TAC ind THEN MP_TAC ih THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
      X_GEN_TAC `c:A->B` THEN STRIP_TAC THEN
      MP_TAC(SPEC `\i:A. if i IN u then (c:A->B) i else ring_0 r` ind) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0];
                        ALL_TAC] THEN
        X_GEN_TAC `j:C` THEN DISCH_TAC THEN
        TRANS_TAC EQ_TRANS
         `ring_sum r u (\i. ring_mul r (if i IN u then (c:A->B) i
                                        else ring_0 r) ((f:A->C->B) i j))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RING_SUM_SUPERSET THEN
          ASM_SIMP_TAC[SUBSET; IN_INSERT; RING_MUL_LZERO];
          TRANS_TAC EQ_TRANS
           `ring_sum r u (\i. ring_mul r ((c:A->B) i) ((f:A->C->B) i j))` THEN
          CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[];
                          ASM_SIMP_TAC[]]];
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:A` THEN
        ASM_CASES_TAC `(i:A) IN u` THEN ASM_REWRITE_TAC[IN_INSERT]];
      DISCH_THEN(X_CHOOSE_THEN `g:A->C` STRIP_ASSUME_TAC)])) THEN
  ABBREV_TAC
   `cf = \i:A. ring_cofactor r ((a:A) INSERT u)
                 (\i j. (f:A->C->B) i ((g:A->C) j)) i a` THEN
  SUBGOAL_THEN
   `!y. y IN t
        ==> ring_det r ((a:A) INSERT u)
              (\i j. (f:A->C->B) i (if j = a then y else (g:A->C) j)) =
            ring_sum r (a INSERT u) (\i. ring_mul r ((cf:A->B) i) (f i y))`
  (LABEL_TAC "exp") THENL
   [X_GEN_TAC `y:C` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:B ring`; `(a:A) INSERT u`;
                   `\i j. (f:A->C->B) i (if j = a then y else (g:A->C) j)`;
                   `a:A`; `a:A`] RING_DET_ADJUGATE_COLUMNS) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[IN_INSERT];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    EXPAND_TAC "cf" THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RING_COFACTOR_EQ_GEN THEN
    ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cf:A->B) a = ring_det r u (\i j. (f:A->C->B) i ((g:A->C) j))`
  ASSUME_TAC THENL
   [EXPAND_TAC "cf" THEN MATCH_MP_TAC RING_COFACTOR_INSERT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `cf:A->B`) THEN
  MATCH_MP_TAC(TAUT `a /\ ~c /\ (~s ==> m) ==> (a /\ s ==> c) ==> m`) THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "cf" THEN REWRITE_TAC[RING_COFACTOR];
    ASM_MESON_TAC[IN_INSERT];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:C` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC
     `~(ring_sum r ((a:A) INSERT u)
          (\i. ring_mul r ((cf:A->B) i) ((f:A->C->B) i y)) = ring_0 r)` THEN
    REMOVE_THEN "exp" (MP_TAC o SPEC `y:C`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC] THEN
  SUBGOAL_THEN `!j. j IN u ==> ~((g:A->C) j = y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC
     `~(ring_det r ((a:A) INSERT u)
          (\i j. (f:A->C->B) i (if j = a then y else (g:A->C) j)) =
        ring_0 r)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_DET_IDENTICAL_COLUMNS THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `j:A`] THEN
    ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT] THEN ASM_MESON_TAC[];
    EXISTS_TAC `\j:A. if j = a then (y:C) else (g:A->C) j` THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]]);;

let RING_DET_INDEPENDENT_ROWS = prove
 (`!(r:B ring) s (f:A->A->B).
        field r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        (!c. (!i. i IN s ==> c i IN ring_carrier r) /\
             (!j. j IN s
                  ==> ring_sum r s (\i. ring_mul r (c i) (f i j)) = ring_0 r)
             ==> !i. i IN s ==> c i = ring_0 r)
        ==> ~(ring_det r s f = ring_0 r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `s:A->bool`; `f:A->A->B`]
    RING_DET_MINOR_SELECTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `q = \x:A. if x IN s then g x else x` THEN
  SUBGOAL_THEN `(q:A->A) permutes s` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC PERMUTES_INJECTIVE_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(ring_det r s (\i j. (f:A->A->B) i (g j)) = ring_0 r)` THEN
  SUBGOAL_THEN
   `ring_det r s (\i j. (f:A->A->B) i (g j)) =
    ring_det r s (\i j. f i ((q:A->A) j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN EXPAND_TAC "q" THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_DET_PERMUTE_COLUMNS; RING_MUL_RZERO; RING_SIGN]);;

let RING_DET_EQ_0_ROWS = prove
 (`!(r:B ring) s (f:A->A->B).
        field r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> (ring_det r s f = ring_0 r <=>
             ?c. (!i. i IN s ==> c i IN ring_carrier r) /\
                 (?i. i IN s /\ ~(c i = ring_0 r)) /\
                 (!j. j IN s
                      ==> ring_sum r s (\i. ring_mul r (c i) (f i j)) =
                          ring_0 r))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_DET_INDEPENDENT_ROWS THEN ASM_MESON_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC RING_DET_DEPENDENT_ROWS THEN
    EXISTS_TAC `c:A->B` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Column versions (via transposition).                                      *)
(* ------------------------------------------------------------------------- *)

let RING_DET_DEPENDENT_COLUMNS_MUL = prove
 (`!(r:B ring) s (f:A->A->B) c k.
        FINITE s /\ k IN s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        (!j. j IN s ==> c j IN ring_carrier r) /\
        (!i. i IN s ==> ring_sum r s (\j. ring_mul r (f i j) (c j)) =
                        ring_0 r)
        ==> ring_mul r (c k) (ring_det r s f) = ring_0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_DEPENDENT_ROWS_MUL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `j:A` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\i. ring_mul r ((f:A->A->B) j i) ((c:A->B) i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

(* A column dependency modulo an ideal: if the rows of f applied to c lie    *)
(* in the ideal k, then c l times the determinant lies in k.                 *)

let RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL = prove
 (`!r k s (f:A->A->B) (c:A->B) l.
      ring_ideal r k /\ FINITE s /\ l IN s /\
      (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
      (!j. j IN s ==> c j IN ring_carrier r) /\
      (!i. i IN s ==> ring_sum r s (\j. ring_mul r (f i j) (c j)) IN k)
      ==> ring_mul r (c l) (ring_det r s f) IN k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    RING_HOMOMORPHISM_IN_CARRIER)) THEN
  MP_TAC(ISPECL [`quotient_ring r (k:B->bool)`; `s:A->bool`;
                 `\i j. ring_coset r k ((f:A->A->B) i j)`;
                 `\j. ring_coset r k ((c:A->B) j)`; `l:A`]
    RING_DET_DEPENDENT_COLUMNS_MUL) THEN
  MP_TAC(ISPECL [`r:B ring`; `quotient_ring r (k:B->bool)`;
                 `ring_coset r (k:B->bool)`; `s:A->bool`; `f:A->A->B`]
    RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_MUL; RING_DET; QUOTIENT_RING_0;
               RING_COSET_EQ_IDEAL; RING_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (quotient_ring r k) s
      (\j. ring_coset r k (ring_mul r ((f:A->A->B) i j) (c j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[QUOTIENT_RING_MUL];
    FIRST_ASSUM(MP_TAC o ISPECL
     [`\j. ring_mul r ((f:A->A->B) i j) (c j)`; `s:A->bool`] o
     MATCH_MP RING_HOMOMORPHISM_SUM) THEN
    ASM_SIMP_TAC[RING_MUL; o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[RING_COSET_EQ_IDEAL; RING_SUM]]);;

let RING_DET_DEPENDENT_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B) c.
        integral_domain r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        (!j. j IN s ==> c j IN ring_carrier r) /\
        (?j. j IN s /\ ~(c j = ring_0 r)) /\
        (!i. i IN s ==> ring_sum r s (\j. ring_mul r (f i j) (c j)) =
                        ring_0 r)
        ==> ring_det r s f = ring_0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `c:A->B`; `j:A`]
    RING_DET_DEPENDENT_COLUMNS_MUL) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_DET]);;

let RING_DET_INDEPENDENT_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B).
        field r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        (!c. (!j. j IN s ==> c j IN ring_carrier r) /\
             (!i. i IN s
                  ==> ring_sum r s (\j. ring_mul r (f i j) (c j)) = ring_0 r)
             ==> !j. j IN s ==> c j = ring_0 r)
        ==> ~(ring_det r s f = ring_0 r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_INDEPENDENT_ROWS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
                  ALL_TAC] THEN
  X_GEN_TAC `c:A->B` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\j. ring_mul r ((c:A->B) j) ((f:A->A->B) i j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let RING_DET_EQ_0_COLUMNS = prove
 (`!(r:B ring) s (f:A->A->B).
        field r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> (ring_det r s f = ring_0 r <=>
             ?c. (!j. j IN s ==> c j IN ring_carrier r) /\
                 (?j. j IN s /\ ~(c j = ring_0 r)) /\
                 (!i. i IN s
                      ==> ring_sum r s (\j. ring_mul r (f i j) (c j)) =
                          ring_0 r))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_DET_INDEPENDENT_COLUMNS THEN ASM_MESON_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC RING_DET_DEPENDENT_COLUMNS THEN
    EXISTS_TAC `c:A->B` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Laplace expansion along an inserted row, with minors on the remaining     *)
(* index set (the column b is moved to the position a by swap(a,b)).         *)
(* ------------------------------------------------------------------------- *)

let RING_COFACTOR_INSERT_SWAP = prove
 (`!(r:B ring) s (f:A->A->B) a b.
        FINITE s /\ ~(a IN s) /\ b IN a INSERT s
        ==> ring_cofactor r (a INSERT s) f a b =
            ring_mul r (ring_sign r (swap(a,b)))
                       (ring_det r s (\i j. f i (swap(a,b) j)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `M = \k l. if k = a then if l = b then ring_1 r else ring_0 r
              else (f:A->A->B) k l` THEN
  SUBGOAL_THEN
   `ring_cofactor r (a INSERT s) (f:A->A->B) a b =
    ring_det r (a INSERT s) M`
  SUBST1_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[ring_cofactor]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:B ring`; `(a:A) INSERT s`; `M:A->A->B`; `swap(a:A,b)`]
    RING_DET_PERMUTE_COLUMNS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC PERMUTES_SWAP THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_det r ((a:A) INSERT s) (\i j. (M:A->A->B) i (swap(a,b) j)) =
    ring_det r s (\i j. (f:A->A->B) i (swap(a,b) j))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_cofactor r ((a:A) INSERT s)
        (\i j. (f:A->A->B) i (swap(a,b) j)) a a` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ring_cofactor] THEN MATCH_MP_TAC RING_DET_EQ THEN
      EXPAND_TAC "M" THEN MAP_EVERY X_GEN_TAC [`k:A`; `l:A`] THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[swap] THEN MESON_TAC[];
      MATCH_MP_TAC RING_COFACTOR_INSERT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_SIGN; RING_DET; RING_SIGN_IDEMPOTENT;
               RING_MUL_LID]);;

let RING_DET_LAPLACE_INSERT = prove
 (`!(r:B ring) s (f:A->A->B) a.
        FINITE s /\ ~(a IN s) /\
        (!i j. i IN a INSERT s /\ j IN a INSERT s ==> f i j IN ring_carrier r)
        ==> ring_det r (a INSERT s) f =
            ring_sum r (a INSERT s)
              (\b. ring_mul r (f a b)
                     (ring_mul r (ring_sign r (swap(a,b)))
                        (ring_det r s (\i j. f i (swap(a,b) j)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `(a:A) INSERT s`; `f:A->A->B`; `a:A`]
    RING_DET_COFACTOR_EXPANSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT] THEN SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `b:A` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_COFACTOR_INSERT_SWAP THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Multiplicativity: det(A B) = det A * det B.                               *)
(* ------------------------------------------------------------------------- *)

let RING_DET_MUL = prove
 (`!(r:B ring) s (a:A->A->B) b.
        FINITE s /\
        (!i j. i IN s /\ j IN s ==> a i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s ==> b i j IN ring_carrier r)
        ==> ring_det r s
              (\i j. ring_sum r s (\k. ring_mul r (a i k) (b k j))) =
            ring_mul r (ring_det r s a) (ring_det r s b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`r:B ring`; `s:A->bool`; `\i:A. (s:A->bool)`;
    `\i j. ring_sum r s (\k. ring_mul r ((a:A->A->B) i k) ((b:A->A->B) k j))`;
    `\i k j. ring_mul r ((a:A->A->B) i k) ((b:A->A->B) k j)`]
   RING_DET_MULTILINEAR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC
   `G = \mu:A->A. ring_mul r (ring_product r s (\i. (a:A->A->B) i (mu i)))
                            (ring_det r s (\i j. (b:A->A->B) (mu i) j))` THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r (cartesian_product s (\i:A. s)) (G:(A->A)->B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_DET_ROWS_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {mu | mu IN cartesian_product s (\i:A. s) /\
                     !x y. x IN s /\ y IN s /\ mu x = mu y ==> x = y}
              (G:(A->A)->B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CARTESIAN_PRODUCT] THEN
    SIMP_TAC[TAUT `p /\ ~(p /\ q) <=> p /\ ~q`; NOT_FORALL_THM; NOT_IMP] THEN
    X_GEN_TAC `mu:A->A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
     (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
    EXPAND_TAC "G" THEN
    SUBGOAL_THEN `ring_det r s (\i j. (b:A->A->B) ((mu:A->A) i) j) = ring_0 r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_DET_IDENTICAL_ROWS THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN ASM_REWRITE_TAC[];
      SIMP_TAC[RING_MUL_RZERO; RING_PRODUCT]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `ring_sum r {p | p permutes s} (G:(A->A)->B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [`\mu:A->A x. if x IN s then mu x else x`;
      `RESTRICTION (s:A->bool):(A->A)->A->A`] THEN
    REWRITE_TAC[IN_ELIM_THM; RESTRICTION_IN_CARTESIAN_PRODUCT;
                IN_CARTESIAN_PRODUCT] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [permutes]) THEN
      ASM_SIMP_TAC[RESTRICTION_DEFINED; PERMUTES_IN_IMAGE; FUN_EQ_THM] THEN
      CONJ_TAC THENL
       [SIMP_TAC[RESTRICTION_DEFINED; IMP_CONJ] THEN
        ASM_MESON_TAC[PERMUTES_INJECTIVE];
        GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `mu:A->A` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PERMUTES_INJECTIVE_RESTRICT THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[RESTRICTION_UNIQUE];
        EXPAND_TAC "G" THEN BINOP_TAC THENL
         [MATCH_MP_TAC RING_PRODUCT_EQ; MATCH_MP_TAC RING_DET_EQ] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p | p permutes s}
      (\p. ring_mul r
             (ring_mul r (ring_sign r p)
                         (ring_product r s (\i. (a:A->A->B) i (p i))))
             (ring_det r s (b:A->A->B)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    ASM_SIMP_TAC[RING_DET_PERMUTE_ROWS] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r x (ring_mul r y z) = ring_mul r (ring_mul r y x) (z:B)`) THEN
    REWRITE_TAC[RING_PRODUCT; RING_SIGN; RING_DET];
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_RMUL o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_PERMUTATIONS; RING_MUL; RING_SIGN; RING_PRODUCT;
                 RING_DET] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ring_det]]);;

(* Similar arrays (Q M) P with P Q = 1 have the same determinant.            *)
let RING_DET_SIMILAR = prove
 (`!(r:B ring) s (q:A->A->B) m p.
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> q i j IN ring_carrier r /\ m i j IN ring_carrier r /\
                   p i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s
               ==> ring_sum r s (\k. ring_mul r (p i k) (q k j)) =
                   if i = j then ring_1 r else ring_0 r)
        ==> ring_det r s
              (\i j. ring_sum r s
                      (\v. ring_mul r
                            (ring_sum r s (\u. ring_mul r (q i u) (m u v)))
                            (p v j))) =
            ring_det r s m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_mul r (ring_det r (s:A->bool) (p:A->A->B)) (ring_det r s q) =
    ring_1 r`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `p:A->A->B`; `q:A->A->B`]
      RING_DET_MUL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC EQ_TRANS
     `ring_det r s (\i j:A. if i = j then ring_1 r else ring_0 r:B)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ; MATCH_MP_TAC RING_DET_I] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`;
                 `\i v:A. ring_sum r s (\u. ring_mul r ((q:A->A->B) i u)
                                                       (m u v))`;
                 `p:A->A->B`] RING_DET_MUL) THEN
  ASM_SIMP_TAC[RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `q:A->A->B`; `m:A->A->B`]
      RING_DET_MUL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`] RING_DET) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `p:A->A->B` th) THEN
                       MP_TAC(SPEC `q:A->A->B` th) THEN
                       MP_TAC(SPEC `m:A->A->B` th)) THEN
  CONV_TAC RING_RULE);;

(* The cofactor matrix of A has determinant det(A)^(n - 1) when det(A) is    *)
(* nonzero in an integral domain: A times the transposed cofactor matrix is  *)
(* det(A) I.                                                                 *)
let RING_DET_COFACTOR = prove
 (`!r s (f:K->K->A).
        integral_domain r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        ~(ring_det r s f = ring_0 r)
        ==> ring_det r s (ring_cofactor r s f) =
            ring_pow r (ring_det r s f) (CARD s - 1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:K->bool = {}` THENL
   [ASM_REWRITE_TAC[RING_DET_EMPTY; CARD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ring_pow];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  MAP_EVERY EXISTS_TAC [`r:A ring`; `ring_det r s (f:K->K->A)`] THEN
  ASM_SIMP_TAC[RING_DET; RING_POW] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ring_pow)] THEN
  SUBGOAL_THEN `SUC(CARD(s:K->bool) - 1) = CARD s` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:K->bool`; `f:K->K->A`;
                 `\i j:K. ring_cofactor r s (f:K->K->A) j i`] RING_DET_MUL) THEN
  MP_TAC(ISPECL [`r:A ring`; `s:K->bool`; `ring_cofactor r s (f:K->K->A)`]
    RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[RING_COFACTOR] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRANS_TAC EQ_TRANS
   `ring_det r s (\i j:K. if i = j then ring_det r s (f:K->K->A)
                          else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[RING_DET_ADJUGATE_ROWS];
    ASM_SIMP_TAC[RING_DET_DIAGONAL; RING_PRODUCT_CONST; RING_DET]]);;

(* ------------------------------------------------------------------------- *)
(* Similar arrays have the same trace: tr(Q (M P)) = tr M when P Q = 1       *)
(* (RING_SUM_TRACE_SIMILAR), and tr M = tr N when A M = N A with det A a     *)
(* unit (RING_SUM_TRACE_SIMILAR_UNIT); if N is diagonal, then also det M =   *)
(* det N (RING_TRACE_DET_SIMILAR_DIAGONAL).                                  *)
(* ------------------------------------------------------------------------- *)

(* tr(Q (M P)) = tr M for square arrays with P Q = 1 (finite index set).     *)
let RING_SUM_TRACE_SIMILAR = prove
 (`!r:A ring s (q:K->K->A) m p.
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> q i j IN ring_carrier r /\ m i j IN ring_carrier r /\
                   p i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s
               ==> ring_sum r s (\k. ring_mul r (p i k) (q k j)) =
                   if i = j then ring_1 r else ring_0 r)
        ==> ring_sum r s
             (\i. ring_sum r s
                    (\j. ring_mul r (q i j)
                           (ring_sum r s (\k. ring_mul r (m j k) (p k i))))) =
            ring_sum r s (\i. m i i)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_SUM]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\i:K. ring_sum r s
      (\k. ring_mul r ((m:K->K->A) j k)
             (ring_mul r ((p:K->K->A) k i) ((q:K->K->A) i j))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[RING_MUL_AC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\k:K. if k = j then (m:K->K->A) j j else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO];
    ASM_SIMP_TAC[RING_SUM_DELTA]]);;

(* Exchange of two weighted finite sums in a ring.                           *)
let RING_SUM_MUL_SWAP = prove
 (`!r:A ring (s:K->bool) (t:L->bool) a b f.
        FINITE s /\ FINITE t /\
        (!i. i IN s ==> a i IN ring_carrier r) /\
        (!j. j IN t ==> b j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN t ==> f i j IN ring_carrier r)
        ==> ring_sum r s
              (\i. ring_mul r (a i)
                     (ring_sum r t (\j. ring_mul r (b j) (f i j)))) =
            ring_sum r t
              (\j. ring_mul r (b j)
                     (ring_sum r s (\i. ring_mul r (a i) (f i j))))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\i:K. ring_sum r t (\j:L.
      ring_mul r ((b:L->A) j) (ring_mul r ((a:K->A) i) (f i j))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[RING_MUL_AC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:L` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RING_SUM_LMUL THEN
  ASM_SIMP_TAC[RING_MUL]);;

let RING_SUM_TRACE_SIMILAR_UNIT = prove
 (`!r:A ring s (a:K->K->A) m m'.
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> a i j IN ring_carrier r /\ m i j IN ring_carrier r /\
                   m' i j IN ring_carrier r) /\
        ring_unit r (ring_det r s a) /\
        (!i j. i IN s /\ j IN s
               ==> ring_sum r s (\k. ring_mul r (a i k) (m k j)) =
                   ring_sum r s (\k. ring_mul r (m' i k) (a k j)))
        ==> ring_sum r s (\i. m i i) = ring_sum r s (\i. m' i i)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sim")))) THEN
  ABBREV_TAC `u = ring_inv r (ring_det r s (a:K->K->A))` THEN
  SUBGOAL_THEN `(u:A) IN ring_carrier r /\
                ring_mul r u (ring_det r s (a:K->K->A)) = ring_1 r`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[RING_INV; RING_DET; RING_MUL_LINV];
    ALL_TAC] THEN
  ABBREV_TAC `b = \i j:K. ring_mul r u (ring_cofactor r s (a:K->K->A) j i)` THEN
  SUBGOAL_THEN
   `!i j:K. i IN s /\ j IN s
            ==> b i j IN ring_carrier r /\
                ring_sum r s (\k. ring_mul r (b i k) ((a:K->K->A) k j)) =
                (if i = j then ring_1 r else ring_0 r) /\
                ring_sum r s (\k. ring_mul r (a i k) (b k j)) =
                (if i = j then ring_1 r else ring_0 r)`
  ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL; RING_COFACTOR] THEN CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_mul r u (ring_sum r s
          (\k:K. ring_mul r (ring_cofactor r s (a:K->K->A) k i) (a k j)))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_MUL; RING_COFACTOR] THEN
        MATCH_MP_TAC RING_SUM_EQ THEN
        ASM_SIMP_TAC[RING_MUL_ASSOC; RING_COFACTOR];
        ASM_SIMP_TAC[RING_DET_ADJUGATE_COLUMNS] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[RING_MUL_RZERO]];
      TRANS_TAC EQ_TRANS
       `ring_mul r u (ring_sum r s
          (\k:K. ring_mul r ((a:K->K->A) i k) (ring_cofactor r s a j k)))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_MUL; RING_COFACTOR] THEN
        MATCH_MP_TAC RING_SUM_EQ THEN
        ASM_SIMP_TAC[RING_MUL_AC; RING_COFACTOR];
        ASM_SIMP_TAC[RING_DET_ADJUGATE_ROWS] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[RING_MUL_RZERO]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:K->bool`; `b:K->K->A`; `m':K->K->A`;
                 `a:K->K->A`] RING_SUM_TRACE_SIMILAR) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\j:K. ring_mul r (b i j)
      (ring_sum r s (\k. ring_mul r ((m:K->K->A) k i) ((a:K->K->A) j k))))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_MUL_SWAP o rand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r s (\k:K. if k = i then (m:K->K->A) i i else ring_0 r)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[RING_SUM_DELTA]; ALL_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO];
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REMOVE_THEN "sim" (MP_TAC o SPECL [`j:K`; `i:K`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[RING_MUL_SYM]]);;

(* If a m = diag(d) a with det a a unit, then m has the trace and the        *)
(* determinant of diag(d).                                                   *)
let RING_TRACE_DET_SIMILAR_DIAGONAL = prove
 (`!r s (a:K->K->A) m d.
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> a i j IN ring_carrier r /\ m i j IN ring_carrier r) /\
        (!i. i IN s ==> d i IN ring_carrier r) /\
        ring_unit r (ring_det r s a) /\
        (!i j. i IN s /\ j IN s
               ==> ring_sum r s (\k. ring_mul r (a i k) (m k j)) =
                   ring_mul r (d i) (a i j))
        ==> ring_sum r s (\i. m i i) = ring_sum r s d /\
            ring_det r s m = ring_product r s d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `s:K->bool`; `a:K->K->A`; `m:K->K->A`;
                   `\i j:K. if i = j then (d:K->A) i else ring_0 r`]
      RING_SUM_TRACE_SIMILAR_UNIT) THEN
    ASM_SIMP_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0];
      MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
      TRANS_TAC EQ_TRANS
       `ring_sum r s (\k:K. if k = i then ring_mul r (d i) ((a:K->K->A) i j)
                             else ring_0 r)` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL]; ALL_TAC] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_CASES_TAC `k:K = i` THEN
      ASM_SIMP_TAC[RING_MUL_LZERO]];
    SUBGOAL_THEN
     `ring_det r s (\i j. ring_sum r s (\k. ring_mul r ((a:K->K->A) i k)
                                                   (m k j))) =
      ring_det r s (\i j. ring_mul r (d i) (a i j))`
    MP_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_DET_MUL; RING_DET_ROWS_MUL] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `r:A ring` RING_MUL_LCANCEL) THEN
    EXISTS_TAC `ring_det r s (a:K->K->A)` THEN
    ASM_SIMP_TAC[RING_UNIT_IMP_REGULAR; RING_DET; RING_PRODUCT] THEN
    ASM_MESON_TAC[RING_MUL_SYM; RING_DET; RING_PRODUCT]]);;

(* ------------------------------------------------------------------------- *)
(* The Ryser formula for the permanent: inclusion-exclusion over the subsets *)
(* of the index set.                                                         *)
(* ------------------------------------------------------------------------- *)

let RING_SUM_ALTERNATING_SUBSETS = prove
 (`!(r:A ring) s u:K->bool.
        FINITE s
        ==> ring_sum r {t | t SUBSET s /\ u SUBSET t}
                     (\t. ring_pow r (ring_neg r (ring_1 r)) (CARD t)) =
            if u = s then ring_pow r (ring_neg r (ring_1 r)) (CARD s)
            else ring_0 r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(s:K->bool) SUBSET u` THENL
   [COND_CASES_TAC THENL
     [ASM_SIMP_TAC[SUBSET_ANTISYM_EQ; SING_GSPEC; RING_SUM_SING; RING_POW;
                   RING_NEG; RING_1];
      SUBGOAL_THEN `{t:K->bool | t SUBSET s /\ u SUBSET t} = {}`
       (fun th -> REWRITE_TAC[th; RING_SUM_CLAUSES]) THEN
      ASM SET_TAC[]];
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:K` STRIP_ASSUME_TAC o
      REWRITE_RULE[SUBSET; NOT_FORALL_THM; NOT_IMP]) THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]] THEN
  SUBGOAL_THEN `FINITE {t:K->bool | t SUBSET s /\ u SUBSET t}` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t:K->bool | t SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ABBREV_TAC `S = {t:K->bool | t SUBSET s /\ u SUBSET t}` THEN DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o ISPECL
   [`r:A ring`; `\t:K->bool. (a:K) IN t`;
    `\t:K->bool. ring_pow r (ring_neg r (ring_1 r):A) (CARD t)`;
    `\t:K->bool. ring_pow r (ring_neg r (ring_1 r):A) (CARD t)`] o
   MATCH_MP RING_SUM_CASES) THEN
  REWRITE_TAC[COND_ID] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_sum r {t | t IN S /\ (a:K) IN t}
      (\t. ring_pow r (ring_neg r (ring_1 r):A) (CARD t)) =
    ring_sum r {t | t IN S /\ ~(a IN t)}
      (\t. ring_neg r (ring_pow r (ring_neg r (ring_1 r)) (CARD t)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [`\t:K->bool. (a:K) INSERT t`; `\t:K->bool. t DELETE (a:K)`] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `t:K->bool` THEN STRIP_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `FINITE(t:K->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_CLAUSES; ring_pow; RING_MUL_LNEG; RING_MUL_LID;
                   RING_POW; RING_NEG; RING_1]];
    ASM_SIMP_TAC[RING_SUM_NEG; FINITE_RESTRICT; RING_POW; RING_NEG; RING_1;
                 RING_ADD_LNEG; RING_SUM]]);;

(* Ryser: expand prod_i sum_(j IN t) f i j as a sum over the maps s -> t     *)
(* (RING_SUM_PRODUCT_CARTESIAN_PRODUCT) and exchange the sums; a map         *)
(* mu : s -> s then comes with the alternating sum of (-1)^|t| over the t    *)
(* between its image and s, which vanishes unless mu is onto, i.e. a         *)
(* permutation (RING_SUM_ALTERNATING_SUBSETS).                               *)
let RING_SUM_PERMUTATIONS_RYSER = prove
 (`!r s (f:K->K->A).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_sum r {p | p permutes s}
              (\p. ring_product r s (\i. f i (p i))) =
            ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD s))
              (ring_sum r {t | t SUBSET s}
                 (\t. ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD t))
                        (ring_product r s (\i. ring_sum r t (\j. f i j)))))`,
  let lemma = prove
   (`!r s (g:(K->K)->A).
        FINITE s /\ (!mu. g mu IN ring_carrier r)
        ==> ring_sum r {t | t SUBSET s}
              (\t. ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD t))
                              (ring_sum r (cartesian_product s (\i. t)) g)) =
            ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD s))
              (ring_sum r {mu | mu IN cartesian_product s (\i. s) /\
                                IMAGE mu s = s} g)`,
    REPEAT STRIP_TAC THEN
    ABBREV_TAC `C = cartesian_product s (\i:K. (s:K->bool))` THEN
    SUBGOAL_THEN `FINITE(C:(K->K)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "C" THEN ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT] THEN
      DISJ2_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:K->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r {t | t SUBSET s}
        (\t. ring_sum r C
          (\mu:K->K. if IMAGE mu s SUBSET t
                     then ring_mul r (ring_pow r (ring_neg r (ring_1 r))
                                                 (CARD t)) ((g:(K->K)->A) mu)
                     else ring_0 r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:K->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `cartesian_product s (\i:K. t) =
        {mu:K->K | mu IN C /\ IMAGE mu s SUBSET t}`
      SUBST1_TAC THENL
       [EXPAND_TAC "C" THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CARTESIAN_PRODUCT; SUBSET;
                    FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
        REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN
        ASM_SIMP_TAC[RING_SUM_LMUL; FINITE_RESTRICT; RING_POW; RING_NEG;
                     RING_1]];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_POWERSET] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_POW; RING_NEG; RING_1;
                                       RING_0];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[RING_SUM_RMUL; FINITE_RESTRICT; FINITE_POWERSET; RING_POW;
                 RING_NEG; RING_1] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RING_SUM_ALTERNATING_SUBSETS] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO] THEN
    REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[RING_SUM_LMUL; FINITE_RESTRICT; RING_POW; RING_NEG; RING_1]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t SUBSET s
        ==> ring_product r s (\i. ring_sum r t (\j. (f:K->K->A) i j)) =
            ring_sum r (cartesian_product s (\i:K. t))
                     (\mu. ring_product r s (\i. f i (mu i)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`r:A ring`; `s:K->bool`; `\i:K. (t:K->bool)`; `f:K->K->A`]
      RING_SUM_PRODUCT_CARTESIAN_PRODUCT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD(s:K->bool)))
     (ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD s))
       (ring_sum r {mu | mu IN cartesian_product s (\i. s) /\ IMAGE mu s = s}
          (\mu. ring_product r s (\i. (f:K->K->A) i (mu i)))))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[RING_MUL_ASSOC; GSYM RING_MUL_POW; RING_POW; RING_NEG; RING_1;
             RING_SUM] THEN
    SIMP_TAC[RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG; RING_MUL_LID;
             RING_NEG; RING_1; RING_POW_ONE; RING_SUM] THEN
    MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [`RESTRICTION (s:K->bool):(K->K)->K->K`;
      `\mu:K->K x. if x IN s then mu x else x`] THEN
    REWRITE_TAC[IN_ELIM_THM; RESTRICTION_IN_CARTESIAN_PRODUCT;
                IN_CARTESIAN_PRODUCT] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `mu:K->K` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; RESTRICTION_UNIQUE] THEN
      ASM SET_TAC[];
      X_GEN_TAC `p:K->K` THEN DISCH_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [permutes]) THEN
      ASM_SIMP_TAC[PERMUTES_IN_IMAGE; IMAGE_RESTRICTION; SUBSET_REFL;
                   PERMUTES_IMAGE; FUN_EQ_THM; RESTRICTION] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC RING_PRODUCT_EQ THEN SIMP_TAC[]];
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `s:K->bool`;
                   `\mu:K->K. ring_product r s (\i. (f:K->K->A) i (mu i))`]
      lemma) THEN
    ASM_REWRITE_TAC[RING_PRODUCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Reindexing along an injective map of the index set.                       *)
(* ------------------------------------------------------------------------- *)

let RING_DET_REINDEX = prove
 (`!(r:B ring) (g:A->C) s (f:C->C->B).
        FINITE s /\ (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
        ==> ring_det r (IMAGE g s) f = ring_det r s (\i j. f (g i) (g j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g':C->A` o
    GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  SUBGOAL_THEN
   `(!y. y IN IMAGE (g:A->C) s ==> (g':C->A) y IN s /\ g(g' y) = y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ring_det] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\p:A->A y:C. if y IN IMAGE g s then (g:A->C)(p((g':C->A) y))
                           else y` THEN
  EXISTS_TAC `\q:C->C x:A. if x IN s then (g':C->A)(q((g:A->C) x)) else x` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `q:C->C` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!x:A. x IN s ==> (q:C->C)((g:A->C) x) IN IMAGE g s`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; FUN_IN_IMAGE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_INJECTIVE_RESTRICT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `g:A->C`) THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE; FUN_IN_IMAGE];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:C` THEN
      ASM_CASES_TAC `(y:C) IN IMAGE (g:A->C) s` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
        DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC[];
        ASM_MESON_TAC[permutes]]];
    X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_TRANSFER THEN EXISTS_TAC `p:A->A` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
      ASM_CASES_TAC `(x:A) IN s` THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
        ASM_MESON_TAC[permutes]];
      BINOP_TAC THENL
       [REWRITE_TAC[ring_sign] THEN
        MP_TAC(ISPECL
         [`g:A->C`; `s:A->bool`; `p:A->A`;
          `\y. if y IN IMAGE g s then (g:A->C)(p((g':C->A) y)) else y`]
         EVENPERM_TRANSFER) THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
        W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o
          lhand o snd) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC RING_PRODUCT_EQ THEN
        ASM_SIMP_TAC[o_THM; FUN_IN_IMAGE]]]]);;

(* ------------------------------------------------------------------------- *)
(* Two small consequences: singleton index set, scalar multiples.            *)
(* ------------------------------------------------------------------------- *)

let RING_DET_SING = prove
 (`!(r:B ring) (a:A) (f:A->A->B).
        f a a IN ring_carrier r ==> ring_det r {a} f = f a a`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
  REWRITE_TAC[FINITE_SING; IN_SING] THEN
  ANTS_TAC THENL [MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[RING_PRODUCT_SING]);;

let RING_DET_CMUL = prove
 (`!(r:B ring) s (f:A->A->B) c.
        FINITE s /\ c IN ring_carrier r /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> ring_det r s (\i j. ring_mul r c (f i j)) =
            ring_mul r (ring_pow r c (CARD s)) (ring_det r s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `\i:A. (c:B)`; `f:A->A->B`]
    RING_DET_ROWS_MUL) THEN
  ASM_SIMP_TAC[RING_PRODUCT_CONST]);;

(* ------------------------------------------------------------------------- *)
(* Block triangular arrays and Kronecker products: det of a block triangular *)
(* array over s UNION t is det_s * det_t (Laplace expansion along the rows   *)
(* of s), and the Kronecker product of a and b has determinant det(a)^|t|    *)
(* det(b)^|s| (RING_DET_MUL with the factors a (x) 1 and 1 (x) b); the case  *)
(* of the index set {t | t < m n} with the entries indexed by t MOD m and    *)
(* t DIV m.                                                                  *)
(* ------------------------------------------------------------------------- *)

let RING_DET_BLOCK_TRIANGULAR = prove
 (`!(r:B ring) s t (f:A->A->B).
        FINITE s /\ FINITE t /\ DISJOINT s t /\
        (!i j. i IN s UNION t /\ j IN s UNION t ==> f i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN t ==> f i j = ring_0 r)
        ==> ring_det r (s UNION t) f =
            ring_mul r (ring_det r s f) (ring_det r t f)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SIMP_TAC[UNION_EMPTY; RING_DET_EMPTY; RING_MUL_LID; RING_DET];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `f:A->A->B`] THEN
  REWRITE_TAC[DISJOINT_INSERT; INSERT_UNION_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i j. i IN a INSERT s /\ j IN a INSERT s
                      ==> (f:A->A->B) i j IN ring_carrier r`
  (LABEL_TAC "fs") THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(i:A) IN a INSERT s`; `(j:A) IN a INSERT s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `f:A->A->B`; `a:A`]
    RING_DET_LAPLACE_INSERT) THEN
  MP_TAC(ISPECL [`r:B ring`; `s UNION t:A->bool`; `f:A->A->B`; `a:A`]
    RING_DET_LAPLACE_INSERT) THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REMOVE_THEN "fs" (ASSUME_TAC o REWRITE_RULE[COMPONENT] o SPEC `a:A`) THEN
  REWRITE_TAC[GSYM INSERT_UNION_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_UNION o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; DISJOINT_INSERT] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_sum r t
     (\b. ring_mul r ((f:A->A->B) a b)
            (ring_mul r (ring_sign r (swap(a,b)))
               (ring_det r (s UNION t) (\i j. f i (swap(a,b) j))))) =
    ring_0 r`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IN_INSERT; RING_MUL_LZERO; RING_MUL; RING_SIGN; RING_DET];
    ALL_TAC] THEN
  SIMP_TAC[RING_ADD_RZERO; RING_SUM] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o rand o snd) THEN
  ASM_SIMP_TAC[RING_DET; RING_MUL; RING_SIGN; FINITE_INSERT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `b:A` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j. (j:A) IN t ==> swap(a,b) j = j` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(b:A) IN a INSERT s`; `DISJOINT (s:A->bool) t`; `~((a:A) IN t)`] THEN
    REWRITE_TAC[swap] THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
   [`t:A->bool`; `\i j. (f:A->A->B) i (swap(a,b) j)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(i:A) IN s UNION t`; `(j:A) IN s UNION t`; `(b:A) IN a INSERT s`] THEN
      REWRITE_TAC[swap] THEN SET_TAC[];
      ASM_SIMP_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `ring_det r t (\i j. (f:A->A->B) i (swap(a,b) j)) = ring_det r t f`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL; RING_SIGN; RING_DET]);;

let RING_DET_KRONECKER = prove
 (`!(r:C ring) s t (a:A->A->C) (b:B->B->C).
        FINITE s /\ FINITE t /\
        (!i j. i IN s /\ j IN s ==> a i j IN ring_carrier r) /\
        (!i j. i IN t /\ j IN t ==> b i j IN ring_carrier r)
        ==> ring_det r (s CROSS t)
              (\x y. ring_mul r (a (FST x) (FST y)) (b (SND x) (SND y))) =
            ring_mul r (ring_pow r (ring_det r s a) (CARD t))
                       (ring_pow r (ring_det r t b) (CARD s))`,
  let lemma = prove
   (`!(r:C ring) (s:A->bool) t (b:B->B->C).
        FINITE s /\ FINITE t /\
        (!i j. i IN t /\ j IN t ==> b i j IN ring_carrier r)
        ==> ring_det r (s CROSS t)
              (\x y. if FST x = FST y then b (SND x) (SND y) else ring_0 r) =
            ring_pow r (ring_det r t b) (CARD s)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[CROSS_EMPTY; RING_DET_EMPTY; CARD_CLAUSES; ring_pow] THEN
    MAP_EVERY X_GEN_TAC [`c:A`; `s:A->bool`] THEN
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[CARD_CLAUSES; ring_pow] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `((c:A) INSERT s) CROSS t = ({c} CROSS t) UNION (s CROSS (t:B->bool))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_UNION; IN_INSERT;
                  NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_BLOCK_TRIANGULAR o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_CROSS; FINITE_SING] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_UNION;
                  IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[RING_0];
      DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `{c:A} CROSS (t:B->bool) = IMAGE (\j. c,j) t`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_IMAGE; IN_SING;
                  PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_REINDEX o lhand o snd) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ANTS_TAC THENL
     [MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:C ring`; `(s:A->bool) CROSS (t:B->bool)`;
     `\x y:A#B. if SND x = SND y then (a:A->A->C) (FST x) (FST y)
                else ring_0 r`;
     `\x y:A#B. if FST x = FST y then (b:B->B->C) (SND x) (SND y)
                else ring_0 r`]
    RING_DET_MUL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(x:C) = x' /\ (y:C) = y' ==> x = y ==> x' = y'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`i:A`; `j:B`; `i':A`; `j':B`] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r ((s:A->bool) CROSS (t:B->bool))
        (\z. if z = (i',j) then ring_mul r ((a:A->A->C) i i') ((b:B->B->C) j j')
             else ring_0 r)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN
      MAP_EVERY X_GEN_TAC [`k:A`; `l:B`] THEN STRIP_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN
      ASM_CASES_TAC `k:A = i'` THEN ASM_CASES_TAC `l:B = j` THEN
      ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; RING_0] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[RING_SUM_DELTA; IN_CROSS; RING_MUL]];
    ALL_TAC] THEN
  BINOP_TAC THENL [ALL_TAC; ASM_SIMP_TAC[lemma]] THEN
  SUBGOAL_THEN
   `(s:A->bool) CROSS (t:B->bool) = IMAGE (\x:B#A. SND x,FST x) (t CROSS s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_IMAGE; EXISTS_PAIR_THM;
                PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:C ring`; `\x:B#A. SND x,FST x`;
                 `(t:B->bool) CROSS (s:A->bool)`;
                 `\x y:A#B. if SND x = SND y then (a:A->A->C) (FST x) (FST y)
                            else ring_0 r`] RING_DET_REINDEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_CROSS; FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:C ring`; `t:B->bool`; `s:A->bool`; `a:A->A->C`] lemma) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[FORALL_PAIR_THM]);;

let RING_DET_KRONECKER_MOD_DIV = prove
 (`!(r:A ring) m n a b.
        (!i j. i < m /\ j < m ==> a i j IN ring_carrier r) /\
        (!i j. i < n /\ j < n ==> b i j IN ring_carrier r)
        ==> ring_det r {t | t < m * n}
              (\t u. ring_mul r (a (t MOD m) (u MOD m))
                                (b (t DIV m) (u DIV m))) =
            ring_mul r (ring_pow r (ring_det r {i | i < m} a) n)
                       (ring_pow r (ring_det r {j | j < n} b) m)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; RING_DET_EMPTY;
                    ring_pow] THEN
    SIMP_TAC[RING_POW_ONE; RING_MUL_LID; RING_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t:num | t < m * n} =
    IMAGE (\x. FST x + m * SND x) ({i | i < m} CROSS {j | j < n})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
                IN_ELIM_THM] THEN
    X_GEN_TAC `t:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`t MOD m`; `t DIV m`] THEN
      ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ] THEN
      MP_TAC(SPECL [`t:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `m + m:num * j` THEN
      ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `m + m * j = m * (j + 1)`; LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_REINDEX o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT; FORALL_PAIR_THM; IN_CROSS;
             IN_ELIM_THM; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\t. t MOD m, t DIV m` (CONJUNCT2(CONJUNCT2 th))) THEN
      STRIP_ASSUME_TAC th) THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES;
                 PAIR_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `{i:num | i < m}`; `{j:num | j < n}`;
                 `a:num->num->A`; `b:num->num->A`] RING_DET_KRONECKER) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; CARD_NUMSEG_LT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Sylvester's determinant identity, also called the Weinstein-Aronszajn     *)
(* identity, for rectangular arrays p (rows s, columns t) and q (rows t,     *)
(* columns s): det(1 + p q) = det(1 + q p) (RING_DET_WEINSTEIN_ARONSZAJN).   *)
(* Over the index set IMAGE INL s UNION IMAGE INR t the block array [[1, p], *)
(* [-q, 1]] is both [[1, 0], [-q, 1]] [[1, p], [0, 1 + q p]] and [[1 + p q,  *)
(* p], [0, 1]] [[1, 0], [-q, 1]], so the identity follows from RING_DET_MUL  *)
(* and RING_DET_BLOCK_TRIANGULAR. This is not the Sylvester array of two     *)
(* polynomials (RING_DET_SYLVESTER).                                         *)
(* ------------------------------------------------------------------------- *)

let RING_SUM_DELTA_MUL = prove
 (`!(r:A ring) (s:K->bool) i w.
        i IN s /\ (!k. k IN s ==> w k IN ring_carrier r)
        ==> ring_sum r s
              (\k. ring_mul r (if i = k then ring_1 r else ring_0 r) (w k)) =
            w i /\
            ring_sum r s
              (\k. ring_mul r (w k) (if k = i then ring_1 r else ring_0 r)) =
            w i`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s (\k:K. if k = i then (w:K->A) i else ring_0 r)` THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[RING_SUM_DELTA]]) THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `k:K = i` THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_RID; RING_MUL_LZERO; RING_MUL_RZERO] THEN
  ASM_MESON_TAC[RING_MUL_LZERO; RING_MUL_RZERO]);;

let RING_DET_WEINSTEIN_ARONSZAJN = prove
 (`!(r:A ring) (s:K->bool) (t:L->bool) (p:K->L->A) (q:L->K->A).
        FINITE s /\ FINITE t /\
        (!i j. i IN s /\ j IN t ==> p i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN t ==> q j i IN ring_carrier r)
        ==> ring_det r s
             (\i i'. ring_add r (if i = i' then ring_1 r else ring_0 r)
                       (ring_sum r t (\j. ring_mul r (p i j) (q j i')))) =
            ring_det r t
             (\j j'. ring_add r (if j = j' then ring_1 r else ring_0 r)
                       (ring_sum r s (\i. ring_mul r (q j i) (p i j'))))`,
  let cond01 = prove
   (`!(r:A ring) b. (if b then ring_1 r else ring_0 r) IN ring_carrier r`,
    MESON_TAC[RING_0; RING_1]) in
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = IMAGE (INL:K->K+L) s UNION IMAGE (INR:L->K+L) t` THEN
  SUBGOAL_THEN
   `FINITE(IMAGE (INL:K->K+L) s) /\ FINITE(IMAGE (INR:L->K+L) t) /\
    DISJOINT (IMAGE (INL:K->K+L) s) (IMAGE (INR:L->K+L) t) /\
    FINITE(u:K+L->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[FINITE_IMAGE; FINITE_UNION] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[distinctness "sum"];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN (u:K+L->bool) <=>
        (?i. i IN s /\ x = INL i) \/ (?j. j IN t /\ x = INR j)`
  (LABEL_TAC "mem") THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:K+L->A.
        ring_sum r u f =
        ring_add r (ring_sum r s (\k. f(INL k))) (ring_sum r t (\m. f(INR m)))`
  (LABEL_TAC "sum") THENL
   [GEN_TAC THEN EXPAND_TAC "u" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[RING_SUM_IMAGE; injectivity "sum"; o_DEF];
    ALL_TAC] THEN
  ABBREV_TAC
   `blk = \(a:K->K->A) (b:K->L->A) (c:L->K->A) (d:L->L->A) (x:K+L) (y:K+L).
      if ?i. x = INL i then
        if ?i. y = INL i then a (OUTL x) (OUTL y) else b (OUTL x) (OUTR y)
      else if ?i. y = INL i then c (OUTR x) (OUTL y)
      else d (OUTR x) (OUTR y)` THEN
  SUBGOAL_THEN
   `!a b c d (i:K) (i':K) (j:L) (j':L).
      (blk:(K->K->A)->(K->L->A)->(L->K->A)->(L->L->A)->K+L->K+L->A)
       a b c d (INL i) (INL i') = (a:K->K->A) i i' /\
      blk a b c d (INL i) (INR j') = (b:K->L->A) i j' /\
      blk a b c d (INR j) (INL i') = (c:L->K->A) j i' /\
      blk a b c d (INR j) (INR j') = (d:L->L->A) j j'`
  (LABEL_TAC "blk") THENL
   [EXPAND_TAC "blk" THEN
    REWRITE_TAC[OUTL; OUTR; injectivity "sum"; distinctness "sum";
                GSYM(distinctness "sum")] THEN
    REWRITE_TAC[MESON[] `!a:K. ?x. a = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(P:A->bool) a b c d x y.
      x IN (u:K+L->bool) /\ y IN u /\
      (!i i'. i IN s /\ i' IN s ==> P((a:K->K->A) i i')) /\
      (!i j. i IN s /\ j IN t ==> P((b:K->L->A) i j)) /\
      (!i j. i IN s /\ j IN t ==> P((c:L->K->A) j i)) /\
      (!j j'. j IN t /\ j' IN t ==> P((d:L->L->A) j j'))
      ==> P((blk:(K->K->A)->(K->L->A)->(L->K->A)->(L->L->A)->K+L->K+L->A)
             a b c d x y)`
  (LABEL_TAC "prop") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ASSUME `!x. x IN (u:K+L->bool) <=>
        (?i. i IN s /\ x = INL i) \/ (?j. j IN t /\ x = INR j)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b c d a' b' c' d' x y.
      x IN (u:K+L->bool) /\ y IN u /\
      (!i i'. i IN s /\ i' IN s ==> (a:K->K->A) i i' = a' i i') /\
      (!i j. i IN s /\ j IN t ==> (b:K->L->A) i j = b' i j) /\
      (!i j. i IN s /\ j IN t ==> (c:L->K->A) j i = c' j i) /\
      (!j j'. j IN t /\ j' IN t ==> (d:L->L->A) j j' = d' j j')
      ==> (blk:(K->K->A)->(K->L->A)->(L->K->A)->(L->L->A)->K+L->K+L->A)
            a b c d x y = blk a' b' c' d' x y`
  (LABEL_TAC "cong") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ASSUME `!x. x IN (u:K+L->bool) <=>
        (?i. i IN s /\ x = INL i) \/ (?j. j IN t /\ x = INR j)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b c d a' b' c' d' x y.
      x IN (u:K+L->bool) /\ y IN u
      ==> ring_sum r u
            (\z. ring_mul r
              ((blk:(K->K->A)->(K->L->A)->(L->K->A)->(L->L->A)->K+L->K+L->A)
               a b c d x z) (blk a' b' c' d' z y)) =
          blk (\i i'. ring_add r
                 (ring_sum r s
                   (\k. ring_mul r ((a:K->K->A) i k) ((a':K->K->A) k i')))
                 (ring_sum r t
                   (\m. ring_mul r ((b:K->L->A) i m) ((c':L->K->A) m i'))))
              (\i j'. ring_add r
                 (ring_sum r s (\k. ring_mul r (a i k) ((b':K->L->A) k j')))
                 (ring_sum r t (\m. ring_mul r (b i m) ((d':L->L->A) m j'))))
              (\j i'. ring_add r
                 (ring_sum r s (\k. ring_mul r ((c:L->K->A) j k) (a' k i')))
                 (ring_sum r t (\m. ring_mul r ((d:L->L->A) j m) (c' m i'))))
              (\j j'. ring_add r
                 (ring_sum r s (\k. ring_mul r (c j k) (b' k j')))
                 (ring_sum r t (\m. ring_mul r (d j m) (d' m j'))))
              x y`
  (LABEL_TAC "mul") THENL
   [REPEAT GEN_TAC THEN REMOVE_THEN "sum" (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "mem" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "mem" (K ALL_TAC) THEN REMOVE_THEN "sum" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!a b c d.
      (!i i'. i IN s /\ i' IN s ==> (a:K->K->A) i i' IN ring_carrier r) /\
      (!i j. i IN s /\ j IN t ==> (b:K->L->A) i j IN ring_carrier r) /\
      (!i j. i IN s /\ j IN t ==> (c:L->K->A) j i IN ring_carrier r) /\
      (!j j'. j IN t /\ j' IN t ==> (d:L->L->A) j j' IN ring_carrier r) /\
      ((!i j. i IN s /\ j IN t ==> b i j = ring_0 r) \/
       (!i j. i IN s /\ j IN t ==> c j i = ring_0 r))
      ==> ring_det r (u:K+L->bool) (blk a b c d) =
          ring_mul r (ring_det r s a) (ring_det r t d)`
  (LABEL_TAC "tri") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       STRIP_ASSUME_TAC)))) THENL
     [MP_TAC(ISPECL [`r:A ring`; `IMAGE (INL:K->K+L) s`;
                     `IMAGE (INR:L->K+L) t`;
                     `(blk:(K->K->A)->(K->L->A)->(L->K->A)->(L->L->A)->
                       K+L->K+L->A) a b c d`]
        RING_DET_BLOCK_TRIANGULAR);
      MP_TAC(ISPECL [`r:A ring`; `IMAGE (INR:L->K+L) t`;
                     `IMAGE (INL:K->K+L) s`;
                     `(blk:(K->K->A)->(K->L->A)->(L->K->A)->(L->L->A)->
                       K+L->K+L->A) a b c d`]
        RING_DET_BLOCK_TRIANGULAR) THEN
      REWRITE_TAC[SET_RULE
       `IMAGE (INR:L->K+L) t UNION IMAGE INL s =
        IMAGE INL s UNION IMAGE INR t`] THEN
      ONCE_REWRITE_TAC[DISJOINT_SYM]] THEN
    (ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [CONJ_TAC THENL
        [REPEAT STRIP_TAC THEN
         USE_THEN "prop" (MATCH_MP_TAC o BETA_RULE o
           ISPEC `\v:A. v IN ring_carrier r`) THEN ASM_SIMP_TAC[];
         REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
         USE_THEN "blk" (fun th -> ASM_SIMP_TAC[th])];
       DISCH_THEN SUBST1_TAC] THEN
     ASM_SIMP_TAC[RING_DET_REINDEX; injectivity "sum"] THEN
     USE_THEN "blk" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ETA_AX]) THEN
    MATCH_MP_TAC RING_MUL_SYM THEN REWRITE_TAC[RING_DET];
    ALL_TAC] THEN
  ABBREV_TAC
   `ids = \i i':K. if i = i' then ring_1 r else ring_0 (r:A ring)` THEN
  ABBREV_TAC
   `idt = \j j':L. if j = j' then ring_1 r else ring_0 (r:A ring)` THEN
  ABBREV_TAC `nq = \(j:L) (i:K). ring_neg r ((q:L->K->A) j i)` THEN
  ABBREV_TAC `zst = \(i:K) (j:L). ring_0 (r:A ring)` THEN
  ABBREV_TAC `zts = \(j:L) (i:K). ring_0 (r:A ring)` THEN
  ABBREV_TAC
   `pq = \i i':K. ring_add r (if i = i' then ring_1 r else ring_0 r)
                   (ring_sum r t
                     (\j. ring_mul r ((p:K->L->A) i j) (q j i')))` THEN
  ABBREV_TAC
   `qp = \j j':L. ring_add r (if j = j' then ring_1 r else ring_0 r)
                   (ring_sum r s
                     (\i. ring_mul r ((q:L->K->A) j i) (p i j')))` THEN
  SUBGOAL_THEN
   `(!i i'. (ids:K->K->A) i i' IN ring_carrier r) /\
    (!j j'. (idt:L->L->A) j j' IN ring_carrier r) /\
    (!j i. j IN t /\ i IN s ==> (nq:L->K->A) j i IN ring_carrier r) /\
    (!i j. (zst:K->L->A) i j IN ring_carrier r) /\
    (!j i. (zts:L->K->A) j i IN ring_carrier r) /\
    (!i i'. (pq:K->K->A) i i' IN ring_carrier r) /\
    (!j j'. (qp:L->L->A) j j' IN ring_carrier r) /\
    ring_det r s ids = ring_1 r /\ ring_det r t idt = ring_1 r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ids"; "idt"; "nq"; "zst"; "zts"; "pq"; "qp"] THEN
    ASM_SIMP_TAC[cond01; RING_NEG; RING_0; RING_ADD; RING_SUM; RING_DET_I];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_det (r:A ring) (u:K+L->bool)
     (blk (ids:K->K->A) (p:K->L->A) (nq:L->K->A) (idt:L->L->A))` THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_det (r:A ring) (u:K+L->bool)
       (\x y. ring_sum r u
               (\z. ring_mul r
                     (blk (pq:K->K->A) (p:K->L->A) (zts:L->K->A)
                          (idt:L->L->A) x z)
                     (blk (ids:K->K->A) (zst:K->L->A) (nq:L->K->A)
                          idt z y)))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_MUL o rand o snd) THEN
      REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
        USE_THEN "prop" (MATCH_MP_TAC o BETA_RULE o
          ISPEC `\v:A. v IN ring_carrier r`) THEN ASM_SIMP_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "tri" (fun th ->
        MP_TAC(ISPECL [`pq:K->K->A`; `p:K->L->A`; `zts:L->K->A`;
                       `idt:L->L->A`] th) THEN
        MP_TAC(ISPECL [`ids:K->K->A`; `zst:K->L->A`; `nq:L->K->A`;
                       `idt:L->L->A`] th)) THEN
      MAP_EVERY EXPAND_TAC ["zts"; "zst"] THEN ASM_SIMP_TAC[] THEN
      SIMP_TAC[RING_0] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
      ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_RID; RING_DET; RING_1];
      ALL_TAC] THEN
    MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`x:K+L`; `y:K+L`] THEN
    STRIP_TAC THEN USE_THEN "mul" (fun th ->
      SIMP_TAC[th; ASSUME `(x:K+L) IN u`; ASSUME `(y:K+L) IN u`]) THEN
    CONV_TAC SYM_CONV THEN
    USE_THEN "cong" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ids"; "idt"; "nq"; "zst"; "zts"; "pq"; "qp"] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_SUM_DELTA_MUL; cond01; RING_MUL_LZERO; RING_MUL_RZERO;
                 RING_0; RING_SUM_0; RING_ADD_LZERO; RING_ADD_RZERO; RING_NEG;
                 RING_MUL; RING_SUM; RING_ADD] THEN
    SUBGOAL_THEN
     `ring_sum r t (\m. ring_mul r ((p:K->L->A) i m)
                                   (ring_neg r ((q:L->K->A) m i'))) =
      ring_neg r (ring_sum r t (\m. ring_mul r (p i m) (q m i')))`
    SUBST1_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_NEG o rand o snd) THEN
      ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[RING_MUL_RNEG];
      MATCH_MP_TAC(RING_RULE
       `d = ring_add r (ring_add r d x) (ring_neg r (x:A))`) THEN
      REWRITE_TAC[cond01; RING_SUM]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_det (r:A ring) (u:K+L->bool)
     (\x y. ring_sum r u
             (\z. ring_mul r
                   (blk (ids:K->K->A) (zst:K->L->A) (nq:L->K->A)
                        (idt:L->L->A) x z)
                   (blk ids (p:K->L->A) (zts:L->K->A) (qp:L->L->A) z y)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_MUL o lhand o snd) THEN
    REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
      USE_THEN "prop" (MATCH_MP_TAC o BETA_RULE o
        ISPEC `\v:A. v IN ring_carrier r`) THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "tri" (fun th ->
      MP_TAC(ISPECL [`ids:K->K->A`; `p:K->L->A`; `zts:L->K->A`;
                     `qp:L->L->A`] th) THEN
      MP_TAC(ISPECL [`ids:K->K->A`; `zst:K->L->A`; `nq:L->K->A`;
                     `idt:L->L->A`] th)) THEN
    MAP_EVERY EXPAND_TAC ["zts"; "zst"] THEN ASM_SIMP_TAC[] THEN
    SIMP_TAC[RING_0] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_DET; RING_1]] THEN
  MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`x:K+L`; `y:K+L`] THEN
  STRIP_TAC THEN USE_THEN "mul" (fun th ->
    SIMP_TAC[th; ASSUME `(x:K+L) IN u`; ASSUME `(y:K+L) IN u`]) THEN
  USE_THEN "cong" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["ids"; "idt"; "nq"; "zst"; "zts"; "pq"; "qp"] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_SUM_DELTA_MUL; cond01; RING_MUL_LZERO; RING_MUL_RZERO;
               RING_0; RING_SUM_0; RING_ADD_LZERO; RING_ADD_RZERO; RING_NEG;
               RING_MUL; RING_SUM; RING_ADD] THEN
  SUBGOAL_THEN
   `ring_sum r s (\k. ring_mul r (ring_neg r ((q:L->K->A) j k))
                                 ((p:K->L->A) k j')) =
    ring_neg r (ring_sum r s (\k. ring_mul r (q j k) (p k j')))`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_NEG o rand o snd) THEN
    ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[RING_MUL_LNEG];
    MATCH_MP_TAC(RING_RULE
     `d = ring_add r (ring_neg r x) (ring_add r d (x:A))`) THEN
    REWRITE_TAC[cond01; RING_SUM]]);;

(* ------------------------------------------------------------------------- *)
(* Triangular arrays indexed by a finite set of numbers.                     *)
(* ------------------------------------------------------------------------- *)

let RING_DET_LOWERTRIANGULAR = prove
 (`!(r:B ring) s (f:num->num->B).
        FINITE s /\
        (!i j. i IN s /\ j IN s /\ i < j ==> f i j = ring_0 r)
        ==> ring_det r s f = ring_product r s (\i. f i i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p | p permutes s}
      (\p. if p = I then ring_product r s (\i. (f:num->num->B) i i)
           else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:num->num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_SIGN_I; I_THM] THENL
     [SIMP_TAC[RING_MUL_LID; RING_PRODUCT]; ALL_TAC] THEN
    SUBGOAL_THEN `?i:num. i IN s /\ i < p i` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:num->num`; `s:num->bool`] PERMUTES_NUMSET_LE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[NOT_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `ring_product r s (\i. (f:num->num->B) i (p i)) = ring_0 r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_ZERO THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE];
      SIMP_TAC[RING_MUL_RZERO; RING_SIGN]];
    REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; PERMUTES_I; RING_PRODUCT]]);;

let RING_DET_UPPERTRIANGULAR = prove
 (`!(r:B ring) s (f:num->num->B).
        FINITE s /\
        (!i j. i IN s /\ j IN s /\ j < i ==> f i j = ring_0 r)
        ==> ring_det r s f = ring_product r s (\i. f i i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `s:num->bool`; `f:num->num->B`]
    RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`r:B ring`; `s:num->bool`; `\i j. (f:num->num->B) j i`]
    RING_DET_LOWERTRIANGULAR) THEN
  ASM_SIMP_TAC[]);;

(* Row operations by a lower triangular array: det(a b) = (prod a i i) det b *)

let RING_DET_LOWERTRIANGULAR_MUL = prove
 (`!(r:B ring) s (a:num->num->B) b.
        FINITE s /\
        (!i j. i IN s /\ j IN s ==> a i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s ==> b i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s /\ i < j ==> a i j = ring_0 r)
        ==> ring_det r s (\i j. ring_sum r s (\k. ring_mul r (a i k) (b k j))) =
            ring_mul r (ring_product r s (\i. a i i)) (ring_det r s b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_DET_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_DET_LOWERTRIANGULAR THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The triangular row change in blocks: rows i = l K + k + 1 (k < K, l < L), *)
(* row i a combination of the rows l K + t + 1, t <= k, of the same block.   *)
(* ------------------------------------------------------------------------- *)

let RING_SUM_SWAP_DELTA = prove
 (`!(r:B ring) s t (h:C->A) (u:C->B) (v:A->B).
        FINITE s /\ FINITE t /\
        (!x. x IN t ==> h x IN s /\ u x IN ring_carrier r) /\
        (!y. y IN s ==> v y IN ring_carrier r)
        ==> ring_sum r s
              (\y. ring_mul r
                     (ring_sum r t (\x. if y = h x then u x else ring_0 r))
                     (v y)) =
            ring_sum r t (\x. ring_mul r (u x) (v (h x)))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r s
      (\y. ring_sum r t
             (\x. if y = (h:C->A) x
                  then ring_mul r ((u:C->B) x) ((v:A->B) (h x))
                  else ring_0 r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `x:C` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL_LZERO];
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0; RING_MUL];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL]]);;

let RING_DET_TRIANGULAR_ROWS = prove
 (`!(r:B ring) K L (c:num->num->B) (g:num->num->num->B).
        (!k t. k < K /\ t <= k ==> c k t IN ring_carrier r) /\
        (!t l j. t < K /\ l < L /\ j IN 1..K * L
                 ==> g t l j IN ring_carrier r)
        ==> ring_det r (1..K * L)
              (\i j. ring_sum r (0..(i - 1) MOD K)
                       (\t. ring_mul r (c ((i - 1) MOD K) t)
                                       (g t ((i - 1) DIV K) j))) =
            ring_mul r
              (ring_product r (1..K * L)
                 (\i. c ((i - 1) MOD K) ((i - 1) MOD K)))
              (ring_det r (1..K * L)
                 (\i j. g ((i - 1) MOD K) ((i - 1) DIV K) j))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `K = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; NUMSEG_CLAUSES; ARITH_EQ; RING_DET_EMPTY;
                    RING_PRODUCT_CLAUSES] THEN
    SIMP_TAC[RING_MUL_LID; RING_1];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= K * L
        ==> (i - 1) DIV K * K + (i - 1) MOD K = i - 1 /\
            (i - 1) MOD K < K /\ (i - 1) DIV K < L`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[DIVISION_SIMP; MOD_LT_EQ; RDIV_LT_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`r:B ring`; `1..K * L`;
    `\i i'. ring_sum r (0..(i - 1) MOD K)
              (\t. if i' = (i - 1) DIV K * K + t + 1
                   then (c:num->num->B) ((i - 1) MOD K) t else ring_0 r)`;
    `\i' j. (g:num->num->num->B) ((i' - 1) MOD K) ((i' - 1) DIV K) j`]
   RING_DET_LOWERTRIANGULAR_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG; RING_SUM] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    (FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
      MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> TRANS_TAC EQ_TRANS (lhand(concl th)) THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[th]]) THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`r:B ring`; `1..K * L`; `0..(i - 1) MOD K`;
                   `\t. (i - 1) DIV K * K + t + 1`;
                   `(c:num->num->B) ((i - 1) MOD K)`;
                   `\i'. (g:num->num->num->B) ((i' - 1) MOD K)
                                              ((i' - 1) DIV K) j`]
      RING_SUM_SWAP_DELTA) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
       [X_GEN_TAC `t:num` THEN STRIP_TAC THEN CONJ_TAC THENL
         [ASM_ARITH_TAC;
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        X_GEN_TAC `y:num` THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `y:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_NUMSEG]];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `t:num < K` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(a + t + 1) - 1 = a + t`] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES];
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r (0..(i - 1) MOD K)
        (\t. if t = (i - 1) MOD K
             then (c:num->num->B) ((i - 1) MOD K) ((i - 1) MOD K)
             else ring_0 r)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = (i - 1) DIV K * K + t + 1 <=> t = (i - 1) MOD K`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RING_SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
      ASM_SIMP_TAC[LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* The characteristic polynomial det(X I - f) in poly_ring r (:1). Its       *)
(* degree is at most CARD s and its coefficient at CARD s is 1: each         *)
(* permutation term is a product of CARD s polynomials of degree at most 1,  *)
(* whose coefficient at CARD s is the product of their coefficients at 1     *)
(* (COEFF_RING_PRODUCT_LE), that is 1 for the identity and 0 otherwise.      *)
(* ------------------------------------------------------------------------- *)

let POLY_DEG_RING_PRODUCT_LE = prove
 (`!(r:B ring) (s:V->bool) (g:K->(V->num)->B) k.
        FINITE k /\ (!i. i IN k ==> g i IN ring_carrier(poly_ring r s))
        ==> poly_deg r (ring_product (poly_ring r s) k g) <=
            nsum k (\i. poly_deg r (g i))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[RING_PRODUCT_CLAUSES; NSUM_CLAUSES; POLY_RING_CLAUSES;
                POLY_DEG_1; LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `k:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC ih) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; NSUM_CLAUSES] THEN
  REWRITE_TAC[POLY_RING_CLAUSES] THEN
  TRANS_TAC LE_TRANS
   `poly_deg r ((g:K->(V->num)->B) a) +
    poly_deg r (ring_product (poly_ring r s) k g)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC POLY_DEG_MUL_LE THEN
  MP_TAC(ISPECL [`poly_ring (r:B ring) (s:V->bool)`; `k:K->bool`;
                 `g:K->(V->num)->B`] RING_PRODUCT) THEN
  UNDISCH_TAC `(g:K->(V->num)->B) a IN ring_carrier(poly_ring r s)` THEN
  REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM] THEN SIMP_TAC[]);;

let COEFF_POLY_MUL_LE = prove
 (`!r (p:(1->num)->A) q m n.
        ring_polynomial r p /\ ring_polynomial r q /\
        poly_deg r p <= m /\ poly_deg r q <= n
        ==> coeff (m + n) (poly_mul r p q) =
            ring_mul r (coeff m p) (coeff n q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COEFF_POLY_MUL] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r (0..m + n)
      (\a. if a = m then ring_mul r (coeff m p) (coeff n q)
           else ring_0 r):A` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `a:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_SUB2] THEN
    ASM_CASES_TAC `m:num < a` THENL
     [SUBGOAL_THEN `coeff a (p:(1->num)->A) = ring_0 r` SUBST1_TAC THENL
       [MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC RING_MUL_LZERO THEN ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT]];
      SUBGOAL_THEN `coeff ((m + n) - a) (q:(1->num)->A) = ring_0 r`
      SUBST1_TAC THENL
       [MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC RING_MUL_RZERO THEN ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT]]];
    REWRITE_TAC[RING_SUM_DELTA; IN_NUMSEG; LE_0; LE_ADD] THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_MUL]]);;

let COEFF_RING_PRODUCT_LE = prove
 (`!r (g:K->(1->num)->A) d s.
        FINITE s /\
        (!i. i IN s ==> ring_polynomial r (g i) /\ poly_deg r (g i) <= d i)
        ==> poly_deg r (ring_product (poly_ring r (:1)) s g) <= nsum s d /\
            coeff (nsum s d) (ring_product (poly_ring r (:1)) s g) =
            ring_product r s (\i. coeff (d i) (g i))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[RING_PRODUCT_CLAUSES; NSUM_CLAUSES; POLY_RING_CLAUSES;
                POLY_DEG_1; LE_REFL; COEFF_POLY_1];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `k:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC ih) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(g:K->(1->num)->A) a IN ring_carrier(poly_ring r (:1)) /\
    ring_polynomial r (ring_product (poly_ring r (:1)) k g)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT; GSYM RING_POLYNOMIAL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; NSUM_CLAUSES; COEFF_IN_CARRIER_ALT] THEN
  REWRITE_TAC[POLY_RING_CLAUSES] THEN CONJ_TAC THENL
   [TRANS_TAC LE_TRANS
     `poly_deg r ((g:K->(1->num)->A) a) +
      poly_deg r (ring_product (poly_ring r (:1)) k g)` THEN
    ASM_SIMP_TAC[POLY_DEG_MUL_LE; LE_ADD2];
    ASM_SIMP_TAC[COEFF_POLY_MUL_LE]]);;

let NSUM_LE_CARD_DELETE = prove
 (`!(g:A->num) s a.
        FINITE s /\ a IN s /\ g a = 0 /\ (!x. x IN s ==> g x <= 1)
        ==> nsum s g <= CARD s - 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:A->num`; `s:A->bool`; `a:A`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`s DELETE (a:A)`; `g:A->num`; `1`] NSUM_BOUND) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; CARD_DELETE; MULT_CLAUSES]);;

let ring_charpoly = new_definition
 `ring_charpoly (r:B ring) (s:A->bool) (f:A->A->B) =
        ring_det (poly_ring r (:1)) s
          (\i j. poly_sub r (if i = j then poly_var r one else poly_0 r)
                            (poly_const r (f i j)))`;;

let RING_CHARPOLY = prove
 (`!(r:B ring) s (f:A->A->B).
        ring_charpoly r s f IN ring_carrier(poly_ring r (:1))`,
  REWRITE_TAC[ring_charpoly; RING_DET]);;

let RING_CHARPOLY_EQ = prove
 (`!(r:B ring) s (f:A->A->B) g.
        (!i j. i IN s /\ j IN s ==> f i j = g i j)
        ==> ring_charpoly r s f = ring_charpoly r s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[]);;

let RING_CHARPOLY_TRANSP = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s ==> ring_charpoly r s (\i j. f j i) = ring_charpoly r s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  MP_TAC(ISPECL
   [`poly_ring (r:B ring) (:1)`; `s:A->bool`;
    `\i j. poly_sub r (if i = j then poly_var r one else poly_0 r)
                      (poly_const r ((f:A->A->B) i j))`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN
  ASM_CASES_TAC `i:A = j` THEN ASM_REWRITE_TAC[]);;

let RING_CHARPOLY_ENTRY = prove
 (`!(r:B ring) (f:A->A->B) i j.
        f i j IN ring_carrier r
        ==> poly_sub r (if i = j then poly_var r one else poly_0 r)
                       (poly_const r (f i j)) IN
            ring_carrier(poly_ring r (:1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM; SUBSET_UNIV] THEN
  MATCH_MP_TAC RING_POLYNOMIAL_SUB THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL_CONST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0]);;

let RING_CHARPOLY_EXTEND = prove
 (`!(r:B ring) (r':C ring) h s (f:A->A->B) x.
        ring_homomorphism(r,r') h /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        x IN ring_carrier r'
        ==> poly_extend (r,r') h (\v:1. x) (ring_charpoly r s f) =
            ring_det r' s (\i j. ring_sub r' (if i = j then x else ring_0 r')
                                             (h(f i j)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  MP_TAC(ISPECL
   [`poly_ring (r:B ring) (:1)`; `r':C ring`;
    `poly_extend (r:B ring,r':C ring) h (\v:1. x)`; `s:A->bool`;
    `\i j. poly_sub r (if i = j then poly_var r one else poly_0 r)
                      (poly_const r ((f:A->A->B) i j))`]
   RING_DET_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EXTEND; RING_CHARPOLY_ENTRY] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_SUB o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_POLYNOMIAL_CONST] THEN COND_CASES_TAC THEN
    REWRITE_TAC[RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[POLY_EXTEND_VAR; POLY_EXTEND_0; POLY_EXTEND_CONST]);;

let RING_CHARPOLY_HOMOMORPHISM = prove
 (`!(r:B ring) (r':C ring) h s (f:A->A->B).
        ring_homomorphism(r,r') h /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> h o ring_charpoly r s f = ring_charpoly r' s (\i j. h(f i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  MP_TAC(ISPECL
   [`poly_ring (r:B ring) (:1)`; `poly_ring (r':C ring) (:1)`;
    `\p:(1->num)->B. (h:B->C) o p`; `s:A->bool`;
    `\i j. poly_sub r (if i = j then poly_var r one else poly_0 r)
                      (poly_const r ((f:A->A->B) i j))`]
   RING_DET_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_RINGS; RING_CHARPOLY_ENTRY] THEN
  DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC RING_DET_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:B ring`; `r':C ring`; `h:B->C`;
                 `if (i:A) = j then poly_var (r:B ring) one else poly_0 r`;
                 `poly_const (r:B ring) ((f:A->A->B) i j):(1->num)->B`]
    POLY_COMPOSE_HOMOMORPHISM_SUB) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_POWERSERIES_CONST] THEN COND_CASES_TAC THEN
    REWRITE_TAC[RING_POWERSERIES_VAR; RING_POWERSERIES_0];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[POLY_COMPOSE_HOMOMORPHISM_CONST] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[POLY_COMPOSE_HOMOMORPHISM_VAR] THEN
  SUBGOAL_THEN `(h:B->C) o (poly_0 r:(1->num)->B) = poly_0 r'`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; POLY_0] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_0]);;

let RING_CHARPOLY_ID = prove
 (`!(r:B ring) (s:A->bool).
        FINITE s
        ==> ring_charpoly r s (\i j. if i = j then ring_1 r else ring_0 r) =
            poly_pow r (poly_sub r (poly_var r one) (poly_const r (ring_1 r)))
              (CARD s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLY_CONST_0; POLY_RING_CLAUSES] THEN
    SIMP_TAC[poly_sub; POLY_0; FUN_EQ_THM; RING_SUB_REFL; RING_0];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_CONST o lhand o snd) THEN
  ASM_SIMP_TAC[RING_CHARPOLY_ENTRY; RING_1; POLY_RING_CLAUSES] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  SIMP_TAC[IN_ELIM_THM; SUBSET_UNIV; RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
           RING_POLYNOMIAL_CONST; RING_1]);;

let RING_CHARPOLY_EVAL = prove
 (`!(r:B ring) s (f:A->A->B) z.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        z IN ring_carrier r
        ==> poly_eval r (ring_charpoly r s f) z =
            ring_det r s (\i j. ring_sub r (if i = j then z else ring_0 r)
                                           (f i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_eval; poly_evaluate] THEN
  ASM_SIMP_TAC[RING_CHARPOLY_EXTEND; RING_HOMOMORPHISM_I; I_THM]);;

let RING_CHARPOLY_DEG_COEFF = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> poly_deg r (ring_charpoly r s f) <= CARD s /\
            coeff (CARD s) (ring_charpoly r s f) = ring_1 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  ABBREV_TAC
   `M = \i j. poly_sub r (if i = j then poly_var r one else poly_0 r)
                         (poly_const r ((f:A->A->B) i j)):(1->num)->B` THEN
  REWRITE_TAC[ring_det] THEN
  MP_TAC(ISPECL [`r:B ring`; `poly_ring (r:B ring) (:1)`;
                 `poly_const r:B->(1->num)->B`] RING_HOMOMORPHISM_SIGN) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; POLY_RING_CLAUSES]) THEN
  SUBGOAL_THEN
   `!i j. i IN s /\ j IN s
          ==> ring_polynomial r ((M:A->A->(1->num)->B) i j) /\
              poly_deg r (M i j) <= 1 /\
              coeff 1 (M i j) = if i = j then ring_1 r else ring_0 r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0;
                 RING_POLYNOMIAL_CONST; POLY_DEG_SUB_CONST; POLY_DEG_VAR;
                 POLY_DEG_0; COEFF_POLY_SUB; COEFF_POLY_VAR; COEFF_POLY_CONST;
                 COEFF_POLY_0; ARITH_EQ; RING_SUB_RZERO; RING_SUB_REFL;
                 RING_0; RING_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p permutes s
        ==> ring_polynomial r
              (ring_product (poly_ring r (:1)) s
                 (\i. (M:A->A->(1->num)->B) i (p i))) /\
            poly_deg r (ring_product (poly_ring r (:1)) s (\i. M i (p i)))
            <= CARD s /\
            coeff (CARD s)
              (ring_product (poly_ring r (:1)) s (\i. M i (p i))) =
            if p = I then ring_1 r else ring_0 r`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:B ring`; `\i. (M:A->A->(1->num)->B) i ((p:A->A) i)`;
                   `\i:A. 1`; `s:A->bool`] COEFF_RING_PRODUCT_LE) THEN
    ASM_SIMP_TAC[PERMUTES_IN_IMAGE; NSUM_CONST; MULT_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT] THEN
    TRANS_TAC EQ_TRANS
     `ring_product r s
        (\i. if i = (p:A->A) i then ring_1 r else ring_0 (r:B ring))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC[PERMUTES_IN_IMAGE];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ_1 THEN ASM_REWRITE_TAC[I_THM];
      MATCH_MP_TAC RING_PRODUCT_ZERO] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
    REWRITE_TAC[I_THM; NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    UNDISCH_TAC `(p:A->A) permutes s` THEN REWRITE_TAC[permutes] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC POLY_DEG_RING_SUM_LE THEN
    ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_MUL; RING_POLYNOMIAL_CONST; RING_SIGN;
                 POLY_DEG_CMUL_LE];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_CONST; RING_SIGN] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p:A->A | p permutes s}
             (\p. if p = I then ring_1 r else ring_0 (r:B ring))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; PERMUTES_I; RING_1]] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_SIGN;
               RING_POLYNOMIAL_IMP_POWERSERIES] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[RING_SIGN_I; RING_MUL_LID; RING_MUL_RZERO; RING_SIGN; RING_1]);;

let RING_CHARPOLY_MONIC = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> monic r (ring_charpoly r s f) /\
            (~(ring_1 r = ring_0 r)
             ==> poly_deg r (ring_charpoly r s f) = CARD s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_CHARPOLY_DEG_COEFF) THEN
  SUBGOAL_THEN `ring_polynomial r (ring_charpoly r s (f:A->A->B))`
  ASSUME_TAC THENL
   [REWRITE_TAC[RING_POLYNOMIAL; RING_CHARPOLY]; ALL_TAC] THEN
  ASM_CASES_TAC `ring_1 r:B = ring_0 r` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONIC_IN_TRIVIAL_RING THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES; TRIVIAL_RING_10];
    SUBGOAL_THEN `poly_deg r (ring_charpoly r s (f:A->A->B)) = CARD s`
    (fun th -> REWRITE_TAC[th; monic]) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COEFF_NONZERO_LE_DEG THEN ASM_REWRITE_TAC[]]);;

let RING_CHARPOLY_EIGENVECTOR = prove
 (`!(r:B ring) s (f:A->A->B) c z.
        integral_domain r /\ FINITE s /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r) /\
        z IN ring_carrier r /\
        (!j. j IN s ==> c j IN ring_carrier r) /\
        (?j. j IN s /\ ~(c j = ring_0 r)) /\
        (!i. i IN s ==> ring_sum r s (\j. ring_mul r (f i j) (c j)) =
                        ring_mul r z (c i))
        ==> poly_eval r (ring_charpoly r s f) z = ring_0 r`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[RING_CHARPOLY_EVAL] THEN
  MATCH_MP_TAC RING_DET_DEPENDENT_COLUMNS THEN EXISTS_TAC `c:A->B` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_SUB; RING_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sub r (ring_sum r s (\j. if j = i then ring_mul r z ((c:A->B) i)
                                  else ring_0 r))
               (ring_sum r s (\j. ring_mul r ((f:A->A->B) i j) (c j)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_0];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `j:A = i` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r (ring_sub r a b) c =
        ring_sub r (ring_mul r a c) (ring_mul r b (c:B))`) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `~(i:A = j)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul r (ring_sub r (ring_0 r) b) c =
        ring_sub r (ring_0 r) (ring_mul r b (c:B))`) THEN
      ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL; RING_SUB_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The characteristic polynomial under reindexing and similarity: for        *)
(* P Q = 1 = Q P the array (Q M) P has the characteristic polynomial of M,   *)
(* since X I - (Q M) P = Q (X I - M) P over the polynomial ring.             *)
(* ------------------------------------------------------------------------- *)

let RING_CHARPOLY_REINDEX = prove
 (`!(r:B ring) (g:A->C) s (f:C->C->B).
        FINITE s /\ (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
        ==> ring_charpoly r (IMAGE g s) f =
            ring_charpoly r s (\i j. f (g i) (g j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_REINDEX o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_DET_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:A->C) i = g j <=> i = j` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let RING_CHARPOLY_SIMILAR = prove
 (`!(r:B ring) s (q:A->A->B) m p.
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> q i j IN ring_carrier r /\ m i j IN ring_carrier r /\
                   p i j IN ring_carrier r) /\
        (!i j. i IN s /\ j IN s
               ==> ring_sum r s (\k. ring_mul r (p i k) (q k j)) =
                   if i = j then ring_1 r else ring_0 r) /\
        (!i j. i IN s /\ j IN s
               ==> ring_sum r s (\k. ring_mul r (q i k) (p k j)) =
                   if i = j then ring_1 r else ring_0 r)
        ==> ring_charpoly r s
              (\i j. ring_sum r s
                      (\v. ring_mul r
                            (ring_sum r s (\u. ring_mul r (q i u) (m u v)))
                            (p v j))) =
            ring_charpoly r s m`,
  let homsum = prove
   (`!(r:B ring) (r':C ring) (c:B->C) (s:A->bool) a b.
        ring_homomorphism(r,r') c /\ FINITE s /\
        (!u. u IN s ==> a u IN ring_carrier r /\ b u IN ring_carrier r)
        ==> c(ring_sum r s (\u. ring_mul r (a u) (b u))) =
            ring_sum r' s (\u. ring_mul r' (c(a u)) (c(b u)))`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o ISPECL [`\u:A. ring_mul r ((a:A->B) u) (b u)`;
      `s:A->bool`] o MATCH_MP RING_HOMOMORPHISM_SUM) THEN
    ASM_SIMP_TAC[RING_MUL; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th])) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  ABBREV_TAC `P = poly_ring (r:B ring) (:1)` THEN
  ABBREV_TAC `X = poly_var (r:B ring) one` THEN
  SUBGOAL_THEN
   `ring_homomorphism(r,(P:((1->num)->B) ring)) (poly_const (r:B ring))`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `(X:(1->num)->B) IN ring_carrier P` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "X"] THEN
    REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM; SUBSET_UNIV;
                RING_POLYNOMIAL_VAR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_sub (r:B ring) = ring_sub (P:((1->num)->B) ring) /\
    poly_0 r = ring_0 P`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN ring_carrier r
        ==> poly_const r a IN ring_carrier (P:((1->num)->B) ring)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:((1->num)->B) ring`; `s:A->bool`;
                 `\i j. (poly_const r ((q:A->A->B) i j)):(1->num)->B`;
                 `\i j. ring_sub (P:((1->num)->B) ring)
                         (if i = j then X else ring_0 P)
                         (poly_const r ((m:A->A->B) i j))`;
                 `\i j. (poly_const r ((p:A->A->B) i j)):(1->num)->B`]
    RING_DET_SIMILAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUB THEN
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
     `(poly_const r
        (ring_sum r s
          (\k. ring_mul r ((p:A->A->B) i k) ((q:A->A->B) k j)))):
      (1->num)->B` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o ISPECL
       [`\k:A. ring_mul r ((p:A->A->B) i k) ((q:A->A->B) k j)`;
        `s:A->bool`] o MATCH_MP RING_HOMOMORPHISM_SUM) THEN
      ASM_SIMP_TAC[RING_MUL; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]);
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th;
                                        MATCH_MP RING_HOMOMORPHISM_1 th])];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN
  STRIP_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN
   `!u v. u IN s /\ v IN s
          ==> poly_const r ((q:A->A->B) i u) IN
              ring_carrier (P:((1->num)->B) ring) /\
              poly_const r ((m:A->A->B) u v) IN ring_carrier P /\
              poly_const r ((p:A->A->B) u v) IN ring_carrier P /\
              poly_const r (q u v) IN ring_carrier P`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (P:((1->num)->B) ring) s
     (\v. ring_mul P
           (ring_sub P (ring_mul P (poly_const r ((q:A->A->B) i v)) X)
              (poly_const r (ring_sum r s (\u. ring_mul r (q i u)
                                                         ((m:A->A->B) u v)))))
           (poly_const r ((p:A->A->B) v j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sum (P:((1->num)->B) ring) s
       (\u. ring_sub P
              (if u = v then ring_mul P (poly_const r ((q:A->A->B) i v)) X
               else ring_0 P)
              (ring_mul P (poly_const r (q i u))
                          (poly_const r ((m:A->A->B) u v))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      BETA_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_SUB_LDISTRIB; RING_0; RING_MUL_RZERO];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SUB o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[RING_MUL] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_MUL; RING_0];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ISPECL [`r:B ring`; `P:((1->num)->B) ring`;
                         `(poly_const (r:B ring)):B->(1->num)->B`] homsum) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (P:((1->num)->B) ring) s
     (\v. ring_sub P
           (ring_mul P X (ring_mul P (poly_const r ((q:A->A->B) i v))
                                     (poly_const r ((p:A->A->B) v j))))
           (ring_mul P (poly_const r (ring_sum r s
                          (\u. ring_mul r (q i u) ((m:A->A->B) u v))))
                       (poly_const r (p v j))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC(RING_RULE
     `ring_mul r (ring_sub r (ring_mul r a x) b) (c:A) =
      ring_sub r (ring_mul r x (ring_mul r a c)) (ring_mul r b c)`) THEN
    ASM_SIMP_TAC[RING_SUM; RING_MUL];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SUB o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; RING_SUM]; DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`r:B ring`; `P:((1->num)->B) ring`;
                   `(poly_const (r:B ring)):B->(1->num)->B`; `s:A->bool`;
                   `\v. (q:A->A->B) i v`; `\v. (p:A->A->B) v j`] homsum) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    COND_CASES_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th;
                                      MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO];
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ISPECL [`r:B ring`; `P:((1->num)->B) ring`;
                         `(poly_const (r:B ring)):B->(1->num)->B`] homsum) THEN
    ASM_SIMP_TAC[RING_SUM; RING_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* The constant coefficient and the coefficient at CARD s - 1 of the         *)
(* characteristic polynomial: (-1)^n det(f) and minus the trace of f. The    *)
(* second one uses the coefficient of degree CARD s - 1 of a product of      *)
(* polynomials X - c_i (COEFF_RING_PRODUCT_X_MINUS); the other permutations  *)
(* fix at most CARD s - 2 points and give terms of smaller degree.           *)
(* ------------------------------------------------------------------------- *)

let RING_CHARPOLY_COEFF_0 = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> coeff 0 (ring_charpoly r s f) =
            ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (CARD s))
                       (ring_det r s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:B ring`; `ring_charpoly r s (f:A->A->B)`]
    POLY_EVAL_AT_0) THEN
  REWRITE_TAC[RING_CHARPOLY] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[RING_CHARPOLY_EVAL; RING_0; COND_ID] THEN
  TRANS_TAC EQ_TRANS
   `ring_det r s
      (\i j. ring_mul r (ring_neg r (ring_1 r)) ((f:A->A->B) i j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN
    ASM_SIMP_TAC[RING_SUB_LZERO; RING_MUL_LNEG; RING_MUL_LID; RING_1];
    MATCH_MP_TAC RING_DET_CMUL THEN ASM_SIMP_TAC[RING_NEG; RING_1]]);;

let COEFF_RING_PRODUCT_X_MINUS = prove
 (`!(r:A ring) (c:K->A) s.
        FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> c i IN ring_carrier r)
        ==> coeff (CARD s - 1)
             (ring_product (poly_ring r (:1)) s
               (\i. poly_sub r (poly_var r one) (poly_const r (c i)))) =
            ring_neg r (ring_sum r s c)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `trivial_ring(r:A ring)` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [trivial_ring]) THEN
    MATCH_MP_TAC(SET_RULE `x IN s /\ y IN s ==> s = {z:A} ==> x = y`) THEN
    SIMP_TAC[RING_NEG; RING_SUM] THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN
    REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`;
    `\i:K. poly_sub r (poly_var r one) (poly_const r ((c:K->A) i))`;
    `s:K->bool`] COEFF_RING_PRODUCT_MONIC_SUBLEADING) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_X_MINUS_A; MONIC_X_MINUS_A; POLY_DEG_X_MINUS_A;
               ARITH_EQ] THEN
  MATCH_MP_TAC(MESON[]
   `a = a' /\ b = b' ==> coeff a p = b ==> coeff a' p = b'`) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN TRANS_TAC EQ_TRANS `nsum s (\i:K. 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[POLY_DEG_X_MINUS_A];
      ASM_SIMP_TAC[NSUM_CONST; MULT_CLAUSES]];
    TRANS_TAC EQ_TRANS `ring_sum r s (\i:K. ring_neg r ((c:K->A) i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN
      ASM_SIMP_TAC[POLY_DEG_X_MINUS_A; SUB_REFL; COEFF_POLY_SUB;
                   COEFF_POLY_VAR; COEFF_POLY_CONST; ARITH_EQ; RING_SUB_LZERO];
      ASM_SIMP_TAC[RING_SUM_NEG]]]);;

let RING_CHARPOLY_COEFF_TRACE = prove
 (`!(r:B ring) s (f:A->A->B).
        FINITE s /\ ~(s = {}) /\
        (!i j. i IN s /\ j IN s ==> f i j IN ring_carrier r)
        ==> coeff (CARD s - 1) (ring_charpoly r s f) =
            ring_neg r (ring_sum r s (\i. f i i))`,
  let lemma = prove
   (`!(p:A->A) s.
        FINITE s /\ p permutes s /\ ~(p = I)
        ==> nsum s (\i. if p i = i then 1 else 0) < CARD s - 1`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
    REWRITE_TAC[I_THM; NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    SUBGOAL_THEN `(a:A) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:A->A) a IN s DELETE a /\ ~(p(p a) = p a)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_DELETE; PERMUTES_IN_IMAGE; PERMUTES_INJECTIVE];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(CARD(s DELETE (a:A)) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0; FINITE_DELETE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\i:A. if (p:A->A) i = i then 1 else 0`;
                   `s DELETE (a:A)`; `(p:A->A) a`] NSUM_LE_CARD_DELETE) THEN
    MP_TAC(ISPECL [`\i:A. if (p:A->A) i = i then 1 else 0`;
                   `s:A->bool`; `a:A`] NSUM_DELETE) THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ANTS_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC; ARITH_TAC]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ring_charpoly] THEN
  ABBREV_TAC
   `M = \i j. poly_sub r (if i = j then poly_var r one else poly_0 r)
                         (poly_const r ((f:A->A->B) i j)):(1->num)->B` THEN
  REWRITE_TAC[ring_det] THEN
  MP_TAC(ISPECL [`r:B ring`; `poly_ring (r:B ring) (:1)`;
                 `poly_const r:B->(1->num)->B`] RING_HOMOMORPHISM_SIGN) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; POLY_RING_CLAUSES]) THEN
  SUBGOAL_THEN
   `!i j. i IN s /\ j IN s
          ==> ring_polynomial r ((M:A->A->(1->num)->B) i j) /\
              poly_deg r (M i j) <= (if j = i then 1 else 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0;
                 RING_POLYNOMIAL_CONST; POLY_DEG_SUB_CONST; POLY_DEG_VAR;
                 POLY_DEG_0] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p permutes s
        ==> ring_polynomial r
              (ring_product (poly_ring r (:1)) s
                 (\i. (M:A->A->(1->num)->B) i (p i))) /\
            coeff (CARD s - 1)
              (ring_product (poly_ring r (:1)) s (\i. M i (p i))) =
            if p = I then ring_neg r (ring_sum r s (\i. f i i))
            else ring_0 r`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
    CONJ_TAC THENL [REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "M" THEN
      REWRITE_TAC[I_THM] THEN MATCH_MP_TAC COEFF_RING_PRODUCT_X_MINUS THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC COEFF_ABOVE_DEG THEN
      REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `nsum s (\i. if (p:A->A) i = i then 1 else 0)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`r:B ring`; `\i. (M:A->A->(1->num)->B) i ((p:A->A) i)`;
                       `\i:A. if (p:A->A) i = i then 1 else 0`; `s:A->bool`]
          COEFF_RING_PRODUCT_LE) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[PERMUTES_IN_IMAGE]; SIMP_TAC[]];
        MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_CONST; RING_SIGN] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p:A->A | p permutes s}
      (\p. if p = I then ring_neg r (ring_sum r s (\i. (f:A->A->B) i i))
           else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_SIGN;
                 RING_POLYNOMIAL_IMP_POWERSERIES] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_SIGN_I; RING_MUL_LID; RING_MUL_RZERO; RING_SIGN;
                 RING_NEG; RING_SUM];
    SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; PERMUTES_I; RING_NEG; RING_SUM]]);;

(* For a 2 x 2 matrix the characteristic polynomial is monic of degree 2,    *)
(* with coefficient of X minus the trace and constant coefficient the        *)
(* determinant, so two such matrices have the same characteristic polynomial *)
(* iff they have the same trace and determinant (RING_CHARPOLY_EQ_CARD_2).   *)
let RING_CHARPOLY_EQ_CARD_2 = prove
 (`!(r:B ring) s (f:A->A->B) g.
        FINITE s /\ CARD s = 2 /\
        (!i j. i IN s /\ j IN s
               ==> f i j IN ring_carrier r /\ g i j IN ring_carrier r)
        ==> (ring_charpoly r s f = ring_charpoly r s g <=>
             ring_sum r s (\i. f i i) = ring_sum r s (\i. g i i) /\
             ring_det r s f = ring_det r s g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s:A->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_CLAUSES; ARITH_RULE `~(0 = 2)`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:A->A->B.
        (!i j. i IN s /\ j IN s ==> h i j IN ring_carrier r)
        ==> coeff 0 (ring_charpoly r s h) = ring_det r s h /\
            coeff 1 (ring_charpoly r s h) =
            ring_neg r (ring_sum r s (\i. h i i)) /\
            coeff 2 (ring_charpoly r s h) = ring_1 r /\
            !d. 2 < d ==> coeff d (ring_charpoly r s h) = ring_0 r`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `h:A->A->B`]
      RING_CHARPOLY_COEFF_TRACE) THEN
    MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `h:A->A->B`]
      RING_CHARPOLY_COEFF_0) THEN
    MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `h:A->A->B`]
      RING_CHARPOLY_DEG_COEFF) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[RING_DET; RING_RULE
       `ring_mul r (ring_pow r (ring_neg r (ring_1 r)) 2) (x:B) = x`];
      MATCH_MP_TAC COEFF_ABOVE_DEG THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`r:B ring`; `s:A->bool`; `h:A->A->B`]
          RING_CHARPOLY) THEN
        SIMP_TAC[POLY_RING; IN_ELIM_THM];
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `f:A->A->B` th) THEN MP_TAC(SPEC `g:A->A->B` th)) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM FUN_EQ_COEFF] THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(SPEC `0:num` th) THEN MP_TAC(SPEC `1:num` th)) THEN
    ASM_SIMP_TAC[RING_NEG_EQ; RING_SUM];
    STRIP_TAC THEN X_GEN_TAC `d:num` THEN
    SUBGOAL_THEN `(d:num) = 0 \/ d = 1 \/ d = 2 \/ 2 < d` STRIP_ASSUME_TAC THENL
     [ARITH_TAC; ASM_SIMP_TAC[]; ASM_SIMP_TAC[]; ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The coefficient of t in the determinant of a polynomial matrix with       *)
(* constant term the identity is the trace of the coefficients of t          *)
(* (COEFF_1_RING_DET).                                                       *)
(* ------------------------------------------------------------------------- *)

(* The coefficients of 1 and t of a product of univariate polynomials.     *)
let COEFF_0_1_RING_PRODUCT = prove
 (`!r (f:K->(1->num)->A) s.
        FINITE s /\ (!i. i IN s ==> ring_polynomial r (f i))
        ==> coeff 0 (ring_product (poly_ring r (:1)) s f) =
            ring_product r s (\i. coeff 0 (f i)) /\
            coeff 1 (ring_product (poly_ring r (:1)) s f) =
            ring_sum r s (\i. ring_mul r (coeff 1 (f i))
                                (ring_product r (s DELETE i)
                                   (\j. coeff 0 (f j))))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[RING_PRODUCT_CLAUSES; RING_SUM_CLAUSES; POLY_RING_CLAUSES;
                COEFF_POLY_1; ARITH_EQ];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC ih) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i d. i IN s ==> coeff d ((f:K->(1->num)->A) i) IN ring_carrier r) /\
    (!d. coeff d ((f:K->(1->num)->A) a) IN ring_carrier r) /\
    (f:K->(1->num)->A) a IN ring_carrier(poly_ring r (:1)) /\
    ring_polynomial r (ring_product (poly_ring r (:1)) s f)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT] THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT; GSYM RING_POLYNOMIAL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; RING_SUM_CLAUSES; FINITE_DELETE;
               RING_PRODUCT; RING_MUL; IN_INSERT] THEN
  REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_MUL] THEN
  REWRITE_TAC[NUMSEG_SING; RING_SUM_SING; num_CONV `1`;
              RING_SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[ARITH; SUB_0; SUB_REFL] THEN
  ASM_SIMP_TAC[RING_MUL; RING_SUM_SING; COEFF_IN_CARRIER_ALT; RING_PRODUCT;
               SET_RULE `~((a:K) IN s) ==> (a INSERT s) DELETE a = s`] THEN
  SUBGOAL_THEN
   `ring_sum r s (\i. ring_mul r (coeff 1 ((f:K->(1->num)->A) i))
                       (ring_product r ((a INSERT s) DELETE i)
                          (\j. coeff 0 (f j)))) =
    ring_sum r s (\i. ring_mul r (coeff 0 (f a))
                        (ring_mul r (coeff 1 (f i))
                           (ring_product r (s DELETE i)
                              (\j. coeff 0 (f j)))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a INSERT s) DELETE i = (a:K) INSERT (s DELETE i)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    ASM_SIMP_TAC[RING_MUL_AC; RING_PRODUCT];
    ASM_SIMP_TAC[RING_SUM_LMUL; RING_MUL; RING_PRODUCT] THEN
    MATCH_MP_TAC RING_ADD_SYM THEN
    ASM_SIMP_TAC[RING_MUL; RING_PRODUCT; RING_SUM]]);;

(* For a polynomial matrix a with a(0) = I, only the identity permutation   *)
(* contributes to the coefficient of t in det(a).                            *)
let COEFF_1_RING_PRODUCT_PERMUTES = prove
 (`!r s (a:K->K->(1->num)->A) p.
        FINITE s /\ p permutes s /\
        (!i j. i IN s /\ j IN s
               ==> ring_polynomial r (a i j) /\
                   coeff 0 (a i j) = if i = j then ring_1 r else ring_0 r)
        ==> coeff 1 (ring_product (poly_ring r (:1)) s (\i. a i (p i))) =
            if p = I then ring_sum r s (\i. coeff 1 (a i i)) else ring_0 r`,
  let lemma = prove
   (`!p s i:K. p permutes s /\ ~(p = I)
               ==> ?j. j IN s /\ ~(j = i) /\ ~(p j = j)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
    REWRITE_TAC[I_THM; NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `b:K`) THEN
    SUBGOAL_THEN `(b:K) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    ASM_CASES_TAC `b:K = i` THENL
     [EXISTS_TAC `(p:K->K) i` THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE; PERMUTES_INJECTIVE];
      EXISTS_TAC `b:K` THEN ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j d. i IN s /\ j IN s
            ==> coeff d ((a:K->K->(1->num)->A) i j) IN ring_carrier r`
  ASSUME_TAC THENL [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `\i. (a:K->K->(1->num)->A) i ((p:K->K) i)`;
                 `s:K->bool`] COEFF_0_1_RING_PRODUCT) THEN
  ASM_SIMP_TAC[PERMUTES_IN_IMAGE] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[I_THM] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_product r (s DELETE i)
        (\j. coeff 0 ((a:K->K->(1->num)->A) j j)) = ring_1 r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ_1 THEN ASM_SIMP_TAC[IN_DELETE];
      ASM_SIMP_TAC[RING_MUL_RID]];
    MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC `i:K` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:K->K`; `s:K->bool`; `i:K`] lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:K` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `ring_product r (s DELETE i)
        (\j. coeff 0 ((a:K->K->(1->num)->A) j ((p:K->K) j))) = ring_0 r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_ZERO THEN EXISTS_TAC `j:K` THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; PERMUTES_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[RING_MUL_RZERO; PERMUTES_IN_IMAGE]]]);;

(* For a square polynomial matrix a with a(0) = I, the coefficient of t in   *)
(* det(a) is the sum of the coefficients of t of the diagonal entries.       *)
let COEFF_1_RING_DET = prove
 (`!r s (a:K->K->(1->num)->A).
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> ring_polynomial r (a i j) /\
                   coeff 0 (a i j) = if i = j then ring_1 r else ring_0 r)
        ==> coeff 1 (ring_det (poly_ring r (:1)) s a) =
            ring_sum r s (\i. coeff 1 (a i i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  MP_TAC(GEN `p:K->K` (ISPECL [`r:A ring`; `poly_ring (r:A ring) (:1)`;
                 `poly_const r:A->(1->num)->A`; `p:K->K`]
    RING_HOMOMORPHISM_SIGN)) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; POLY_RING_CLAUSES]) THEN
  SUBGOAL_THEN
   `!p. p permutes s
        ==> ring_polynomial r
              (ring_product (poly_ring r (:1)) s
                 (\i. (a:K->K->(1->num)->A) i (p i)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_CONST; RING_SIGN] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {p:K->K | p permutes s}
      (\p. if p = I then ring_sum r s (\i. coeff 1 (a i i))
           else ring_0 (r:A ring))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:K->K` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_SIGN; RING_POLYNOMIAL_IMP_POWERSERIES;
                 COEFF_1_RING_PRODUCT_PERMUTES] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_SIGN_I; RING_MUL_LID; RING_MUL_RZERO; RING_SIGN;
                 RING_SUM];
    REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; PERMUTES_I; RING_SUM]]);;

(* ------------------------------------------------------------------------- *)
(* The Vandermonde determinant: det(x_i^j) = prod_(i<j) (x_j - x_i) over any *)
(* commutative ring.                                                         *)
(* ------------------------------------------------------------------------- *)

(* With p_i = prod_(t<i) (X - x_t), monic of degree i, the matrix          *)
(* (p_i(x_j)) is the product of the unitriangular coefficient matrix of the *)
(* p_i with the transposed Vandermonde matrix, and it is triangular since   *)
(* p_i(x_j) = 0 for j < i.                                                   *)
let RING_DET_VANDERMONDE = prove
 (`!(r:A ring) n x.
        (!i. i < n ==> x i IN ring_carrier r)
        ==> ring_det r {i | i < n} (\i j. ring_pow r (x i) j) =
            ring_product r {j | j < n}
              (\j. ring_product r {i | i < j} (\i. ring_sub r (x j) (x i)))`,
  let lemma = prove
   (`!(r:A ring) c.
        c IN ring_carrier r
        ==> ring_polynomial r (poly_sub r (poly_var r one) (poly_const r c)) /\
            poly_deg r (poly_sub r (poly_var r one) (poly_const r c)) <= 1 /\
            coeff 1 (poly_sub r (poly_var r one) (poly_const r c)) = ring_1 r`,
    SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
             POLY_DEG_SUB_CONST; POLY_DEG_VAR] THEN
    REPEAT STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COEFF_POLY_SUB; COEFF_POLY_VAR; COEFF_POLY_CONST; ARITH_EQ] THEN
    SIMP_TAC[RING_SUB_RZERO; RING_1]) in
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `p = \i. ring_product (poly_ring r (:1)) {t | t < i}
              (\t. poly_sub r (poly_var r one)
                              (poly_const r ((x:num->A) t)))` THEN
  SUBGOAL_THEN
   `!i. i < n ==> ring_polynomial r ((p:num->(1->num)->A) i) /\
                  poly_deg r (p i) <= i /\ coeff i (p i) = ring_1 r /\
                  !y. y IN ring_carrier r
                      ==> poly_eval r (p i) y =
                          ring_product r {t | t < i} (\t. ring_sub r y (x t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "p" THEN
    SUBGOAL_THEN `!t. t IN {t | t < i} ==> (x:num->A) t IN ring_carrier r`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LT_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`;
     `\t. poly_sub r (poly_var r one) (poly_const r ((x:num->A) t))`;
     `\t:num. 1`; `{t:num | t < i}`] COEFF_RING_PRODUCT_LE) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; NSUM_CONST; CARD_NUMSEG_LT; MULT_CLAUSES;
                 lemma; RING_PRODUCT_1] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_RING_PRODUCT o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; GSYM RING_POLYNOMIAL; lemma] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
                 POLY_EVAL_VAR; POLY_EVAL_CONST];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_det r {i | i < n} (\i j. ring_pow r ((x:num->A) j) i)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `{i:num | i < n}`;
                   `\i j. ring_pow r ((x:num->A) j) i`] RING_DET_TRANSP) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `{i:num | i < n}`;
                 `\i k. coeff k ((p:num->(1->num)->A) i)`;
                 `\k j. ring_pow r ((x:num->A) j) k`]
    RING_DET_LOWERTRIANGULAR_MUL) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_POW;
               COEFF_IN_CARRIER_ALT] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_MESON_TAC[LET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product r {i | i < n} (\i. coeff i ((p:num->(1->num)->A) i)) =
    ring_1 r`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ_1 THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SIMP_TAC[RING_MUL_LID; RING_DET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRANS_TAC EQ_TRANS
   `ring_det r {i | i < n}
      (\i j. poly_eval r ((p:num->(1->num)->A) i) ((x:num->A) j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[NUMSEG_LT; COND_RAND] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC POLY_EVAL_COEFF THEN ASM_SIMP_TAC[] THEN
    TRANS_TAC LE_TRANS `i:num` THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_UPPERTRIANGULAR o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RING_PRODUCT_ZERO THEN
    EXISTS_TAC `j:num` THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUB_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Free and projective extensions: coordinates, multiplication matrices,     *)
(* trace and norm. For rings k and l and h:A->B, free_basis (k,l) h n g says *)
(* that g 0, ..., g (n - 1) is a basis of l as a module over k via h. Then   *)
(* basis_coordinates (k,l) h n g x i is the i-th coordinate of x (ring_0 k   *)
(* for i >= n) and mul_matrix (k,l) h n g x is the matrix of multiplication  *)
(* by x.                                                                     *)
(* More generally projective_basis (k,l) h n e f says that the elements e 0, *)
(* ..., e (n - 1) of l and the additive maps f 0, ..., f (n - 1) from l to   *)
(* k, linear over k via h, form a dual basis: x = sum_i h(f i x) e i for     *)
(* every x in l. Then l is a finite projective module over k, a direct       *)
(* summand of k^n. The array A i j = f i (x e j) of x satisfies A(x) A(y) =  *)
(* A(x y), so E = A(1) is idempotent, and A + I - E acts as x on the image   *)
(* of E and as the identity on its complement.                               *)
(* The trace algebra_trace (k,l) h x and the norm algebra_norm (k,l) h x are *)
(* the trace of A and the determinant of A + I - E in a chosen finite        *)
(* projective basis when there is one, and ring_0 k and ring_1 k otherwise.  *)
(* They do not depend on the basis (ALGEBRA_TRACE_PROJECTIVE_BASIS,          *)
(* ALGEBRA_NORM_PROJECTIVE_BASIS). A free basis is a projective basis with   *)
(* the coordinates as the f i (FREE_BASIS_PROJECTIVE), and there they are    *)
(* the trace and the determinant of the matrix of multiplication             *)
(* (ALGEBRA_TRACE_FREE_BASIS, ALGEBRA_NORM_FREE_BASIS).                      *)
(* The predicates free_basis and projective_basis do not assert that h is a  *)
(* ring homomorphism; the algebra lemmas assume that separately. The default *)
(* trace 0 and norm 1 make the operations total; the matrix interpretation   *)
(* requires a finite projective basis, which over a field exists exactly     *)
(* when there is a finite free basis.                                        *)
(* ------------------------------------------------------------------------- *)

let free_basis = new_definition
 `free_basis (k:A ring,l:B ring) (h:A->B) n (g:num->B) <=>
  (!i. i < n ==> g i IN ring_carrier l) /\
  (!x. x IN ring_carrier l
       ==> ?c. (!i. i < n ==> c i IN ring_carrier k) /\
               x = ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i))) /\
  (!c. (!i. i < n ==> c i IN ring_carrier k) /\
       ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)) = ring_0 l
       ==> !i. i < n ==> c i = ring_0 k)`;;

let basis_coordinates = new_definition
 `basis_coordinates (k:A ring,l:B ring) (h:A->B) n (g:num->B) x =
        @c. (!i. i < n ==> c i IN ring_carrier k) /\
            (!i. ~(i < n) ==> c i = ring_0 k) /\
            ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)) = x`;;

let mul_matrix = new_definition
 `mul_matrix (k:A ring,l:B ring) (h:A->B) n (g:num->B) x i j =
        basis_coordinates (k,l) h n g (ring_mul l x (g j)) i`;;

let projective_basis = new_definition
 `projective_basis (k:A ring,l:B ring) (h:A->B) n (e:num->B) (f:num->B->A) <=>
  (!i. i < n ==> e i IN ring_carrier l) /\
  (!i x. i < n /\ x IN ring_carrier l ==> f i x IN ring_carrier k) /\
  (!i x y. i < n /\ x IN ring_carrier l /\ y IN ring_carrier l
           ==> f i (ring_add l x y) = ring_add k (f i x) (f i y)) /\
  (!i a x. i < n /\ a IN ring_carrier k /\ x IN ring_carrier l
           ==> f i (ring_mul l (h a) x) = ring_mul k a (f i x)) /\
  (!x. x IN ring_carrier l
       ==> ring_sum l {i | i < n} (\i. ring_mul l (h(f i x)) (e i)) = x)`;;

let algebra_trace = new_definition
 `algebra_trace (k:A ring,l:B ring) (h:A->B) x =
        if ?n e f. projective_basis (k,l) h n e f
        then @t. ?n e f. projective_basis (k,l) h n e f /\
                         t = ring_sum k {i | i < n}
                                      (\i. f i (ring_mul l x (e i)))
        else ring_0 k`;;

let algebra_norm = new_definition
 `algebra_norm (k:A ring,l:B ring) (h:A->B) x =
        if ?n e f. projective_basis (k,l) h n e f
        then @d. ?n e f. projective_basis (k,l) h n e f /\
                         d = ring_det k {i | i < n}
                              (\i j. ring_add k (f i (ring_mul l x (e j)))
                                      (ring_sub k
                                        (if i = j then ring_1 k else ring_0 k)
                                        (f i (e j))))
        else ring_1 k`;;

(* ------------------------------------------------------------------------- *)
(* Free bases and coordinates.                                               *)
(* ------------------------------------------------------------------------- *)

let FREE_BASIS_IN_CARRIER = prove
 (`!(h:A->B) k l n g.
        free_basis (k,l) h n g ==> !i. i < n ==> g i IN ring_carrier l`,
  SIMP_TAC[free_basis]);;

let FREE_BASIS_INDEPENDENT = prove
 (`!(h:A->B) k l n g c.
        free_basis (k,l) h n g /\
        (!i. i < n ==> c i IN ring_carrier k) /\
        ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)) = ring_0 l
        ==> !i. i < n ==> c i = ring_0 k`,
  REWRITE_TAC[free_basis] THEN MESON_TAC[]);;

let FREE_BASIS_MONOMORPHISM = prove
 (`!(h:A->B) k l n g.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ ~(n = 0)
        ==> ring_monomorphism(k,l) h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RING_MONOMORPHISM_ALT] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `\i:num. if i = 0 then x else ring_0 k:A`]
    FREE_BASIS_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
      ALL_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->B)(if i = 0 then x else ring_0 k) = ring_0 l`
    SUBST1_TAC THENL
     [COND_CASES_TAC THEN ASM_MESON_TAC[RING_HOMOMORPHISM_0];
      MATCH_MP_TAC RING_MUL_LZERO THEN
      ASM_MESON_TAC[FREE_BASIS_IN_CARRIER]];
    DISCH_THEN(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[LT_NZ]]);;

let FREE_BASIS_UNIQUE = prove
 (`!(h:A->B) k l n g c d.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        (!i. i < n ==> c i IN ring_carrier k) /\
        (!i. i < n ==> d i IN ring_carrier k) /\
        ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)) =
        ring_sum l {i | i < n} (\i. ring_mul l (h(d i)) (g i))
        ==> !i. i < n ==> c i = d i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `\i. ring_sub k ((c:num->A) i) (d i)`]
        FREE_BASIS_INDEPENDENT) THEN
  ASM_SIMP_TAC[RING_SUB; RING_SUB_EQ_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sub l
      (ring_sum l {i:num | i < n} (\i. ring_mul l (h((c:num->A) i)) (g i)))
      (ring_sum l {i:num | i < n} (\i. ring_mul l (h(d i)) ((g:num->B) i)))`
  THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_SUB_RDISTRIB];
    ASM_SIMP_TAC[RING_SUB_REFL; RING_SUM]]);;

(* The basis element g j as a combination with Kronecker coefficients.       *)
let FREE_BASIS_DELTA = prove
 (`!(h:A->B) k l n g j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ j < n
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l (h(if i = j then ring_1 k else ring_0 k))
                              (g i)) =
            g j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l {i | i < n} (\i. if i = j then (g:num->B) j else ring_0 l)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LZERO];
    ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM]]);;

let FREE_BASIS_HAS_SIZE = prove
 (`!(h:A->B) k l n g.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        FINITE(ring_carrier k)
        ==> ring_carrier l HAS_SIZE CARD(ring_carrier k) EXP n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_carrier l =
    IMAGE (\c. ring_sum l {i:num | i < n}
                 (\i. ring_mul l ((h:A->B)(c i)) (g i)))
          {c | (!i. i IN {i | i < n} ==> c i IN ring_carrier k) /\
               (!i. ~(i IN {i | i < n}) ==> c i = ARB)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RING_SUM] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:B` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [free_basis]) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. if i < n then (c:num->A) i else ARB` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_SIMP_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE_NUMSEG_LT;
                 GSYM FINITE_HAS_SIZE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:num->A`; `d:num->A`] THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                   `c:num->A`; `d:num->A`] FREE_BASIS_UNIQUE) THEN
    ASM_SIMP_TAC[]]);;

(* Free bases and principal quotients. If w is a free basis of s over r      *)
(* along h, then h(b) divides sum h(c_i) w_i in s iff b divides every c_i in *)
(* r (FREE_BASIS_RING_DIVIDES), so the cosets of the w_i are a free basis of *)
(* s/(h b) over r/(b) (FREE_BASIS_QUOTIENT_RING_PRINCIPAL).                  *)
let FREE_BASIS_RING_DIVIDES = prove
 (`!r (s:B ring) (h:A->B) n w b c.
        ring_homomorphism(r,s) h /\ free_basis (r,s) h n w /\
        b IN ring_carrier r /\ (!i. i < n ==> c i IN ring_carrier r)
        ==> (ring_divides s (h b)
              (ring_sum s {i | i < n} (\i. ring_mul s (h(c i)) (w i))) <=>
             !i. i < n ==> ring_divides r b (c i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN ring_carrier r ==> (h:A->B) x IN ring_carrier s`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ring_homomorphism(r,s) (h:A->B)` THEN
    SIMP_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  EQ_TAC THENL
   [REWRITE_TAC[ring_divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:B` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:B` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [free_basis]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num->A` (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    DISCH_THEN(fun th ->
     SUBGOAL_THEN
      `ring_sum s {i | i < n}
         (\i. ring_mul s ((h:A->B)(c i)) ((w:num->B) i)) =
       ring_sum s {i | i < n}
         (\i. ring_mul s (h(ring_mul r b ((d:num->A) i))) (w i))`
     ASSUME_TAC THENL
      [REWRITE_TAC[th] THEN
       W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
       ANTS_TAC THENL
        [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM];
         DISCH_THEN(SUBST1_TAC o SYM)] THEN
       MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
       X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
       ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
        (ASSUME `ring_homomorphism(r,s) (h:A->B)`)] THEN
       MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC[];
       ALL_TAC]) THEN
    MP_TAC(ISPECL [`h:A->B`; `r:A ring`; `s:B ring`; `n:num`; `w:num->B`;
                   `c:num->A`; `\i. ring_mul r b ((d:num->A) i)`]
      FREE_BASIS_UNIQUE) THEN
    ASM_SIMP_TAC[RING_MUL] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `(d:num->A) i` THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `d:num->A` o
      REWRITE_RULE[ring_divides; RIGHT_AND_EXISTS_THM;
                   RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    REWRITE_TAC[ring_divides; RING_SUM] THEN ASM_SIMP_TAC[] THEN
    EXISTS_TAC
     `ring_sum s {i | i < n}
        (\i. ring_mul s ((h:A->B)((d:num->A) i)) ((w:num->B) i))` THEN
    REWRITE_TAC[RING_SUM] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
     (ASSUME `ring_homomorphism(r,s) (h:A->B)`)] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC[]]);;

let FREE_BASIS_QUOTIENT_RING_PRINCIPAL = prove
 (`!r (s:B ring) (h:A->B) n w b.
        ring_homomorphism(r,s) h /\ free_basis (r,s) h n w /\
        b IN ring_carrier r
        ==> ?g. ring_homomorphism
                 (quotient_ring r (ideal_generated r {b}),
                  quotient_ring s (ideal_generated s {h b})) g /\
                (!a. a IN ring_carrier r
                     ==> g(ring_coset r (ideal_generated r {b}) a) =
                         ring_coset s (ideal_generated s {h b}) (h a)) /\
                free_basis
                 (quotient_ring r (ideal_generated r {b}),
                  quotient_ring s (ideal_generated s {h b})) g n
                 (ring_coset s (ideal_generated s {h b}) o w)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ib = ideal_generated r {b:A}` THEN
  ABBREV_TAC `jb = ideal_generated s {(h:A->B) b}` THEN
  SUBGOAL_THEN `ring_ideal r (ib:A->bool) /\ ring_ideal s (jb:B->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ib"; "jb"] THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ring_carrier r ==> (h:A->B) x IN ring_carrier s`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `(!x. x IN ring_carrier r ==> (x IN ib <=> ring_divides r b x)) /\
    (!y. y IN ring_carrier s
         ==> (y IN jb <=> ring_divides s ((h:A->B) b) y))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ib"; "jb"] THEN
    ASM_SIMP_TAC[IN_IDEAL_GENERATED_SING_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `h:A->B`; `ib:A->bool`;
                 `jb:B->bool`] QUOTIENT_RING_HOMOMORPHISM_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(x:A) IN ib` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[ring_divides] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
     (ASSUME `ring_homomorphism(r,s) (h:A->B)`); RING_MUL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:(A->bool)->(B->bool)` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ring_carrier(quotient_ring r ib) =
    {ring_coset r ib a | a | a IN ring_carrier(r:A ring)} /\
    ring_carrier(quotient_ring s jb) =
    {ring_coset s jb y | y | y IN ring_carrier(s:B ring)} /\
    ring_0(quotient_ring r ib) = ib /\ ring_0(quotient_ring s jb) = jb`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_0] THEN ASM_SIMP_TAC[QUOTIENT_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. (!k. k < n ==> c k IN ring_carrier r)
        ==> ring_sum (quotient_ring s jb) {k | k < n}
             (\k. ring_mul (quotient_ring s jb)
                   ((g:(A->bool)->(B->bool))(ring_coset r ib (c k)))
                   ((ring_coset s jb o (w:num->B)) k)) =
            ring_coset s jb
             (ring_sum s {k | k < n}
               (\k. ring_mul s ((h:A->B)(c k)) (w k)))`
  (LABEL_TAC "sumq") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\k. ring_mul s ((h:A->B)((c:num->A) k)) ((w:num->B) k)`;
      `{k:num | k < n}`]
     (MATCH_MP RING_HOMOMORPHISM_SUM (MATCH_MP RING_HOMOMORPHISM_RING_COSET
       (ASSUME `ring_ideal s (jb:B->bool)`)))) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(MATCH_MP RING_HOMOMORPHISM_MUL
     (MATCH_MP RING_HOMOMORPHISM_RING_COSET
       (ASSUME `ring_ideal s (jb:B->bool)`))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[free_basis] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[o_THM; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:B` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [free_basis]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\k. ring_coset r (ib:A->bool) ((d:num->A) k)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "sumq" (MP_TAC o SPEC `d:num->A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `cc:num->(A->bool)` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:num->A` o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN
   `ring_sum (quotient_ring s jb) {k | k < n}
     (\k. ring_mul (quotient_ring s jb) ((g:(A->bool)->(B->bool))(cc k))
                   ((ring_coset s jb o (w:num->B)) k)) =
    ring_coset s jb
     (ring_sum s {k | k < n}
       (\k. ring_mul s ((h:A->B)((d:num->A) k)) (w k)))`
  SUBST1_TAC THENL
   [USE_THEN "sumq" (MP_TAC o SPEC `d:num->A`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_COSET_EQ_IDEAL; RING_SUM] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `h:A->B`; `n:num`; `w:num->B`;
                 `b:A`; `d:num->A`] FREE_BASIS_RING_DIVIDES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_MESON_TAC[RING_COSET_EQ_IDEAL]);;

let FREE_BASIS_RING_SUM_IMAGE = prove
 (`!(h:A->B) l n (g:num->B) c.
        (!i j. i < n /\ j < n /\ g i = g j ==> i = j)
        ==> ring_sum l (IMAGE g {i | i < n}) (\x. ring_mul l (h(c x)) x) =
            ring_sum l {i | i < n} (\i. ring_mul l (h(c(g i))) (g i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `g:num->B`;
    `\x:B. ring_mul l ((h:A->B)(c x)) x`; `{i:num | i < n}`]
    RING_SUM_IMAGE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_DEF]);;

let BASIS_COORDINATES,BASIS_COORDINATES_OUTSIDE =
  let lemma = prove
   (`!(h:A->B) k l n g x.
        free_basis (k,l) h n g /\ x IN ring_carrier l
        ==> (!i. i < n ==> basis_coordinates (k,l) h n g x i IN
                           ring_carrier k) /\
            (!i. ~(i < n) ==> basis_coordinates (k,l) h n g x i = ring_0 k) /\
            ring_sum l {i | i < n}
              (\i. ring_mul l (h(basis_coordinates (k,l) h n g x i)) (g i)) =
            x`,
    REPEAT GEN_TAC THEN REWRITE_TAC[free_basis] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))
     ASSUME_TAC) THEN
    REWRITE_TAC[basis_coordinates] THEN CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. if i < n then (c:num->A) i else ring_0 k` THEN
    ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM]) in
  (prove
    (`!(h:A->B) k l n g x.
        free_basis (k,l) h n g /\ x IN ring_carrier l
        ==> (!i. basis_coordinates (k,l) h n g x i IN ring_carrier k) /\
            ring_sum l {i | i < n}
              (\i. ring_mul l (h(basis_coordinates (k,l) h n g x i)) (g i)) =
            x`,
     REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
     MESON_TAC[RING_0]),
   prove
    (`!(h:A->B) k l n g x i.
        free_basis (k,l) h n g /\ x IN ring_carrier l /\ ~(i < n)
        ==> basis_coordinates (k,l) h n g x i = ring_0 k`,
     MESON_TAC[lemma]));;

let BASIS_COORDINATES_IN_CARRIER = prove
 (`!(h:A->B) k l n g x i.
        free_basis (k,l) h n g /\ x IN ring_carrier l
        ==> basis_coordinates (k,l) h n g x i IN ring_carrier k`,
  MESON_TAC[BASIS_COORDINATES]);;

let BASIS_COORDINATES_EXPAND = prove
 (`!(h:A->B) k l n g x.
        free_basis (k,l) h n g /\ x IN ring_carrier l
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l (h(basis_coordinates (k,l) h n g x i)) (g i)) =
            x`,
  MESON_TAC[BASIS_COORDINATES]);;

let BASIS_COORDINATES_UNIQUE = prove
 (`!(h:A->B) k l n g x c.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        (!i. i < n ==> c i IN ring_carrier k) /\
        ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)) = x
        ==> !i. i < n ==> basis_coordinates (k,l) h n g x i = c i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  MATCH_MP_TAC FREE_BASIS_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `g:num->B`] THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER; BASIS_COORDINATES_EXPAND]);;

let BASIS_COORDINATES_EQ = prove
 (`!(h:A->B) k l n g x y.
        free_basis (k,l) h n g /\
        x IN ring_carrier l /\ y IN ring_carrier l
        ==> (basis_coordinates (k,l) h n g x =
             basis_coordinates (k,l) h n g y <=> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                                     `n:num`; `g:num->B`; t]
                               BASIS_COORDINATES_EXPAND)) [`x:B`; `y:B`] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let BASIS_COORDINATES_LINCOMB = prove
 (`!(h:A->B) k l n g c i.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        (!i. i < n ==> c i IN ring_carrier k) /\ i < n
        ==> basis_coordinates (k,l) h n g
              (ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i))) i =
            c i`,
  MESON_TAC[BASIS_COORDINATES_UNIQUE]);;

let BASIS_COORDINATES_BASIS = prove
 (`!(h:A->B) k l n g i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ j < n
        ==> basis_coordinates (k,l) h n g (g j) i =
            if i = j then ring_1 k else ring_0 k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_CASES_TAC `i:num < n` THENL
   [ALL_TAC;
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[BASIS_COORDINATES_OUTSIDE]] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
    `(g:num->B) j`; `\i:num. if i = j then ring_1 k else ring_0 (k:A ring)`]
    BASIS_COORDINATES_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[RING_0; RING_1]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l {i:num | i < n}
      (\i. if i = j then (g:num->B) j else ring_0 l)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LZERO];
    ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM]]);;

let BASIS_COORDINATES_ADD = prove
 (`!(h:A->B) k l n g x y i.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l /\ y IN ring_carrier l
        ==> basis_coordinates (k,l) h n g (ring_add l x y) i =
            ring_add k (basis_coordinates (k,l) h n g x i)
                       (basis_coordinates (k,l) h n g y i)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `i:num < n` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[BASIS_COORDINATES_OUTSIDE; RING_ADD; RING_ADD_LZERO;
                 RING_0]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
    `ring_add l x y:B`;
    `\i. ring_add k (basis_coordinates (k,l) (h:A->B) n g x i)
                    (basis_coordinates (k,l) h n g y i)`]
    BASIS_COORDINATES_UNIQUE) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  ASM_SIMP_TAC[RING_ADD; BASIS_COORDINATES_IN_CARRIER] THEN
  TRANS_TAC EQ_TRANS
   `ring_add l
     (ring_sum l {i:num | i < n}
       (\i. ring_mul l (h(basis_coordinates (k,l) (h:A->B) n g x i))
                       ((g:num->B) i)))
     (ring_sum l {i:num | i < n}
       (\i. ring_mul l (h(basis_coordinates (k,l) h n g y i)) (g i)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_ADD o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                   BASIS_COORDINATES_IN_CARRIER];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_ADD_RDISTRIB; BASIS_COORDINATES_IN_CARRIER];
    ASM_SIMP_TAC[BASIS_COORDINATES_EXPAND]]);;

let BASIS_COORDINATES_LMUL = prove
 (`!(h:A->B) k l n g a x i.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        a IN ring_carrier k /\ x IN ring_carrier l
        ==> basis_coordinates (k,l) h n g (ring_mul l (h a) x) i =
            ring_mul k a (basis_coordinates (k,l) h n g x i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ASM_CASES_TAC `i:num < n` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[BASIS_COORDINATES_OUTSIDE; RING_MUL; RING_MUL_RZERO]] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
    `ring_mul l ((h:A->B) a) x`;
    `\i. ring_mul k a (basis_coordinates (k,l) (h:A->B) n g x i)`]
    BASIS_COORDINATES_UNIQUE) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  ASM_SIMP_TAC[RING_MUL; BASIS_COORDINATES_IN_CARRIER] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul l ((h:A->B) a)
     (ring_sum l {i:num | i < n}
       (\i. ring_mul l (h(basis_coordinates (k,l) h n g x i))
                       ((g:num->B) i)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                   BASIS_COORDINATES_IN_CARRIER];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; BASIS_COORDINATES_IN_CARRIER];
    ASM_SIMP_TAC[BASIS_COORDINATES_EXPAND]]);;

let BASIS_COORDINATES_0 = prove
 (`!(h:A->B) k l n g i.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> basis_coordinates (k,l) h n g (ring_0 l) i = ring_0 k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `ring_0 k:A`; `ring_0 l:B`; `i:num`]
    BASIS_COORDINATES_LMUL) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
  ASM_SIMP_TAC[RING_0; RING_MUL_LZERO; BASIS_COORDINATES_IN_CARRIER]);;

let BASIS_COORDINATES_SUM = prove
 (`!(h:A->B) k l n g (s:K->bool) c y i.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ FINITE s /\
        (!j. j IN s ==> c j IN ring_carrier k /\ y j IN ring_carrier l)
        ==> basis_coordinates (k,l) h n g
              (ring_sum l s (\j. ring_mul l (h(c j)) (y j))) i =
            ring_sum k s
              (\j. ring_mul k (c j) (basis_coordinates (k,l) h n g (y j) i))`,
  REPLICATE_TAC 5 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `!a. a IN ring_carrier k ==> (h:A->B) a IN ring_carrier l`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; BASIS_COORDINATES_0] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`c:K->A`; `y:K->B`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN
  ASM_SIMP_TAC[RING_MUL; RING_SUM; BASIS_COORDINATES_ADD;
               BASIS_COORDINATES_LMUL; BASIS_COORDINATES_IN_CARRIER]);;

(* The coordinates of x y are the matrix of x applied to those of y.         *)

let BASIS_COORDINATES_MUL = prove
 (`!(h:A->B) k l n g x y i.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l /\ y IN ring_carrier l
        ==> basis_coordinates (k,l) h n g (ring_mul l x y) i =
            ring_sum k {j | j < n}
              (\j. ring_mul k (mul_matrix (k,l) h n g x i j)
                              (basis_coordinates (k,l) h n g y j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  SUBGOAL_THEN
   `ring_mul l x (y:B) =
    ring_sum l {j:num | j < n}
      (\j. ring_mul l ((h:A->B)(basis_coordinates (k,l) h n g y j))
                      (ring_mul l x ((g:num->B) j)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                   `y:B`] BASIS_COORDINATES_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                   BASIS_COORDINATES_IN_CARRIER];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL_AC; BASIS_COORDINATES_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`; `{j:num | j < n}`;
    `basis_coordinates (k,l) (h:A->B) n g y`;
    `\j. ring_mul l x ((g:num->B) j)`; `i:num`] BASIS_COORDINATES_SUM)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL;
                 BASIS_COORDINATES_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  MATCH_MP_TAC RING_MUL_SYM THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER; RING_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Linear combinations sum_i h(c i) g i of elements g i of l with            *)
(* coefficients c i in k: combinations of combinations                       *)
(* (EXTENSION_LINCOMB_SUM), sums and scalar multiples of the coefficients    *)
(* (EXTENSION_LINCOMB_ADD, EXTENSION_LINCOMB_LMUL) and products with an      *)
(* element of l (EXTENSION_MUL_LINCOMB, EXTENSION_LINCOMB_MUL).              *)
(* ------------------------------------------------------------------------- *)

(* A k-linear combination of k-linear combinations of the g i.               *)
let EXTENSION_LINCOMB_SUM = prove
 (`!(h:A->B) k l (s:K->bool) (t:L->bool) a b g.
        ring_homomorphism(k,l) h /\ FINITE s /\ FINITE t /\
        (!m. m IN s ==> a m IN ring_carrier k) /\
        (!m i. m IN s /\ i IN t ==> b m i IN ring_carrier k) /\
        (!i. i IN t ==> g i IN ring_carrier l)
        ==> ring_sum l s
             (\m. ring_mul l (h(a m))
                    (ring_sum l t (\i. ring_mul l (h(b m i)) (g i)))) =
            ring_sum l t
             (\i. ring_mul l (h(ring_sum k s (\m. ring_mul k (a m) (b m i))))
                             (g i))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  SUBGOAL_THEN
   `(!m. m IN s ==> (h:A->B)((a:K->A) m) IN ring_carrier l) /\
    (!m i. m IN s /\ i IN (t:L->bool)
           ==> ring_mul k ((a:K->A) m) (b m i) IN ring_carrier k /\
               (h:A->B)(b m i) IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l s (\m. ring_sum l t
      (\i. ring_mul l (h(ring_mul k ((a:K->A) m) (b m i))) ((g:L->B) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `m:K` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_MUL] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:L` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC];
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:L` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUM th]) THEN
    ASM_SIMP_TAC[GSYM RING_SUM_RMUL; RING_MUL; o_DEF]]);;

let EXTENSION_LINCOMB_ADD = prove
 (`!(h:A->B) k l (s:K->bool) c d g.
        ring_homomorphism(k,l) h /\ FINITE s /\
        (!i. i IN s ==> c i IN ring_carrier k) /\
        (!i. i IN s ==> d i IN ring_carrier k) /\
        (!i. i IN s ==> g i IN ring_carrier l)
        ==> ring_sum l s (\i. ring_mul l (h(ring_add k (c i) (d i))) (g i)) =
            ring_add l (ring_sum l s (\i. ring_mul l (h(c i)) (g i)))
                       (ring_sum l s (\i. ring_mul l (h(d i)) (g i)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_ADD o rand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB]);;

let EXTENSION_LINCOMB_LMUL = prove
 (`!(h:A->B) k l (s:K->bool) a c g.
        ring_homomorphism(k,l) h /\ FINITE s /\ a IN ring_carrier k /\
        (!i. i IN s ==> c i IN ring_carrier k) /\
        (!i. i IN s ==> g i IN ring_carrier l)
        ==> ring_sum l s (\i. ring_mul l (h(ring_mul k a (c i))) (g i)) =
            ring_mul l (h a) (ring_sum l s (\i. ring_mul l (h(c i)) (g i)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC]);;

let EXTENSION_MUL_LINCOMB = prove
 (`!(h:A->B) k l (s:K->bool) c y x.
        ring_homomorphism(k,l) h /\ FINITE s /\ x IN ring_carrier l /\
        (!i. i IN s ==> c i IN ring_carrier k) /\
        (!i. i IN s ==> y i IN ring_carrier l)
        ==> ring_mul l x (ring_sum l s (\i. ring_mul l (h(c i)) (y i))) =
            ring_sum l s (\i. ring_mul l (h(c i)) (ring_mul l x (y i)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL_AC]);;

let EXTENSION_LINCOMB_MUL = prove
 (`!(h:A->B) k l (s:K->bool) c y x.
        ring_homomorphism(k,l) h /\ FINITE s /\ x IN ring_carrier l /\
        (!i. i IN s ==> c i IN ring_carrier k) /\
        (!i. i IN s ==> y i IN ring_carrier l)
        ==> ring_mul l (ring_sum l s (\i. ring_mul l (h(c i)) (y i))) x =
            ring_sum l s (\i. ring_mul l (h(c i)) (ring_mul l (y i) x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Multiplication matrices.                                                  *)
(* ------------------------------------------------------------------------- *)

let MUL_MATRIX_IN_CARRIER = prove
 (`!(h:A->B) k l n g x i j.
        free_basis (k,l) h n g /\ x IN ring_carrier l /\ j < n
        ==> mul_matrix (k,l) h n g x i j IN ring_carrier k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  MATCH_MP_TAC BASIS_COORDINATES_IN_CARRIER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_MUL THEN ASM_MESON_TAC[FREE_BASIS_IN_CARRIER]);;

let MUL_MATRIX_EXPAND = prove
 (`!(h:A->B) k l n g x j.
        free_basis (k,l) h n g /\ x IN ring_carrier l /\ j < n
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l (h(mul_matrix (k,l) h n g x i j)) (g i)) =
            ring_mul l x (g j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_MUL THEN ASM_MESON_TAC[FREE_BASIS_IN_CARRIER]);;

let MUL_MATRIX_ADD = prove
 (`!(h:A->B) k l n g x y i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l /\ y IN ring_carrier l /\ j < n
        ==> mul_matrix (k,l) h n g (ring_add l x y) i j =
            ring_add k (mul_matrix (k,l) h n g x i j)
                       (mul_matrix (k,l) h n g y i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB; BASIS_COORDINATES_ADD; RING_MUL]);;

let MUL_MATRIX_LMUL = prove
 (`!(h:A->B) k l n g a x i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        a IN ring_carrier k /\ x IN ring_carrier l /\ j < n
        ==> mul_matrix (k,l) h n g (ring_mul l (h a) x) i j =
            ring_mul k a (mul_matrix (k,l) h n g x i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; BASIS_COORDINATES_LMUL; RING_MUL]);;

let MUL_MATRIX_SCALAR = prove
 (`!(h:A->B) k l n g a i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        a IN ring_carrier k /\ j < n
        ==> mul_matrix (k,l) h n g (h a) i j =
            if i = j then a else ring_0 k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_LMUL; BASIS_COORDINATES_BASIS] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO]);;

let MUL_MATRIX_1 = prove
 (`!(h:A->B) k l n g i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ j < n
        ==> mul_matrix (k,l) h n g (ring_1 l) i j =
            if i = j then ring_1 k else ring_0 k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_SIMP_TAC[RING_MUL_LID; BASIS_COORDINATES_BASIS]);;

let MUL_MATRIX_0 = prove
 (`!(h:A->B) k l n g i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ j < n
        ==> mul_matrix (k,l) h n g (ring_0 l) i j = ring_0 k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; BASIS_COORDINATES_0]);;

let MUL_MATRIX_MUL = prove
 (`!(h:A->B) k l n g x y i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l /\ y IN ring_carrier l /\ j < n
        ==> mul_matrix (k,l) h n g (ring_mul l x y) i j =
            ring_sum k {m | m < n}
              (\m. ring_mul k (mul_matrix (k,l) h n g x i m)
                              (mul_matrix (k,l) h n g y m j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  GEN_REWRITE_TAC LAND_CONV [mul_matrix] THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `x:B`; `ring_mul l y ((g:num->B) j)`; `i:num`]
    BASIS_COORDINATES_MUL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mul_matrix]);;

(* The matrix of a combination of elements, and matrices with entries in a   *)
(* subring.                                                                  *)
let MUL_MATRIX_RING_SUM = prove
 (`!(h:A->B) k l n g (s:K->bool) a y i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ FINITE s /\
        (!m. m IN s ==> a m IN ring_carrier k) /\
        (!m. m IN s ==> y m IN ring_carrier l) /\ i < n /\ j < n
        ==> mul_matrix (k,l) h n g
              (ring_sum l s (\m. ring_mul l (h(a m)) (y m))) i j =
            ring_sum k s
              (\m. ring_mul k (a m)
                     (mul_matrix (k,l) h n g (y m) i j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:K->bool`; `a:K->A`;
                 `y:K->B`; `(g:num->B) j`] EXTENSION_LINCOMB_MUL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`; `s:K->bool`;
    `a:K->A`; `\m. ring_mul l ((y:K->B) m) ((g:num->B) j)`; `i:num`]
   BASIS_COORDINATES_SUM)) THEN
  ASM_SIMP_TAC[RING_MUL]);;

let MUL_MATRIX_SUBRING = prove
 (`!(h:A->B) k l n g r x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        r subring_of k /\
        (!j. j < n
             ==> ?c. (!i. i < n ==> c i IN r) /\
                     ring_mul l x (g j) =
                     ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)))
        ==> !i j. i < n /\ j < n
                  ==> mul_matrix (k,l) h n g x i j IN r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i < n ==> (c:num->A) i IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBRING_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[mul_matrix; BASIS_COORDINATES_LINCOMB]);;

(* ------------------------------------------------------------------------- *)
(* Change of basis. For free bases g of size m and e of size n the arrays    *)
(* Q i u = coordinate i of g u in e and P v j = coordinate v of e j in g are *)
(* mutually inverse and the matrix of x in e is (Q M) P, M its matrix in g;  *)
(* so over a nontrivial ring m = n (FREE_BASES_SIZE_EQ), and the             *)
(* characteristic polynomial does not depend on the basis.                   *)
(* ------------------------------------------------------------------------- *)

let BASIS_COORDINATES_CHANGE_OF_BASIS = prove
 (`!(h:A->B) k l m n g g' y i.
        ring_homomorphism(k,l) h /\
        free_basis (k,l) h m g /\ free_basis (k,l) h n g' /\
        y IN ring_carrier l
        ==> basis_coordinates (k,l) h n g' y i =
            ring_sum k {p | p < m}
              (\p. ring_mul k (basis_coordinates (k,l) h n g' (g p) i)
                              (basis_coordinates (k,l) h m g y p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `g:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `g:num->B`;
                 `y:B`] BASIS_COORDINATES_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g':num->B`; `{p:num | p < m}`;
    `basis_coordinates (k,l) (h:A->B) m g y`; `g:num->B`; `i:num`]
    BASIS_COORDINATES_SUM)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; BASIS_COORDINATES_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER]);;

let BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE = prove
 (`!(h:A->B) k l m n g g' i j.
        ring_homomorphism(k,l) h /\
        free_basis (k,l) h m g /\ free_basis (k,l) h n g' /\ j < n
        ==> ring_sum k {p | p < m}
              (\p. ring_mul k (basis_coordinates (k,l) h n g' (g p) i)
                              (basis_coordinates (k,l) h m g (g' j) p)) =
            if i = j then ring_1 k else ring_0 k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `n:num`;
                 `g:num->B`; `g':num->B`; `(g':num->B) j`; `i:num`]
    BASIS_COORDINATES_CHANGE_OF_BASIS) THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_BASIS] THEN
  ASM_MESON_TAC[FREE_BASIS_IN_CARRIER]);;

let MUL_MATRIX_CHANGE_OF_BASIS = prove
 (`!(h:A->B) k l m n g g' x i j.
        ring_homomorphism(k,l) h /\
        free_basis (k,l) h m g /\ free_basis (k,l) h n g' /\
        x IN ring_carrier l /\ j < n
        ==> mul_matrix (k,l) h n g' x i j =
            ring_sum k {v | v < m}
              (\v. ring_mul k
                    (ring_sum k {u | u < m}
                      (\u. ring_mul k (basis_coordinates (k,l) h n g' (g u) i)
                                      (mul_matrix (k,l) h m g x u v)))
                    (basis_coordinates (k,l) h m g (g' j) v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `g:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g':num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  REWRITE_TAC[mul_matrix] THEN
  SUBGOAL_THEN
   `!v. basis_coordinates (k,l) (h:A->B) m g ((g':num->B) j) v IN
        ring_carrier k`
  ASSUME_TAC THENL [ASM_MESON_TAC[BASIS_COORDINATES_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l x ((g':num->B) j) =
    ring_sum l {v:num | v < m}
      (\v. ring_mul l ((h:A->B)(basis_coordinates (k,l) h m g (g' j) v))
                      (ring_mul l x ((g:num->B) v)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `g:num->B`;
                   `(g':num->B) j`] BASIS_COORDINATES_EXPAND) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                   BASIS_COORDINATES_IN_CARRIER];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL_AC; BASIS_COORDINATES_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g':num->B`; `{v:num | v < m}`;
    `basis_coordinates (k,l) (h:A->B) m g ((g':num->B) j)`;
    `\v. ring_mul l x ((g:num->B) v)`; `i:num`] BASIS_COORDINATES_SUM)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL;
                 BASIS_COORDINATES_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `n:num`;
                 `g:num->B`; `g':num->B`; `ring_mul l x ((g:num->B) v)`;
                 `i:num`] BASIS_COORDINATES_CHANGE_OF_BASIS) THEN
  ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC RING_MUL_SYM THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER; RING_SUM]);;

let FREE_BASES_SIZE_EQ = prove
 (`!(h:A->B) k l m n g g'.
        ring_homomorphism(k,l) h /\ ~trivial_ring k /\
        free_basis (k,l) h m g /\ free_basis (k,l) h n g'
        ==> m = n`,
  let lemma = prove
   (`!(h:A->B) k l m n g g'.
        ring_homomorphism(k,l) h /\ ~trivial_ring k /\
        free_basis (k,l) h m g /\ free_basis (k,l) h n g'
        ==> ~(m < n)`,
    REPEAT STRIP_TAC THEN UNDISCH_TAC `~trivial_ring(k:A ring)` THEN
    REWRITE_TAC[TRIVIAL_RING_10] THEN
    ABBREV_TAC
     `Q = \i p. if p < m then basis_coordinates (k,l) (h:A->B) n g'
                                ((g:num->B) p) i
                else ring_0 k` THEN
    ABBREV_TAC
     `P = \p j. if p < m then basis_coordinates (k,l) (h:A->B) m g
                                ((g':num->B) j) p
                else ring_0 k` THEN
    SUBGOAL_THEN
     `!i j. i < n /\ j < n
            ==> (Q:num->num->A) i j IN ring_carrier k /\
                (P:num->num->A) i j IN ring_carrier k`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN
      CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0] THEN
      MATCH_MP_TAC BASIS_COORDINATES_IN_CARRIER THEN
      ASM_MESON_TAC[FREE_BASIS_IN_CARRIER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`; `Q:num->num->A`;
                   `P:num->num->A`] RING_DET_MUL) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `ring_det k {i:num | i < n} (P:num->num->A) = ring_0 k`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_det k {i:num | i < n}
          (\i j. if i = m then ring_0 k else (P:num->num->A) i j)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "P" THEN REWRITE_TAC[LT_REFL];
        MATCH_MP_TAC RING_DET_ROW_0 THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]];
      ASM_SIMP_TAC[RING_MUL_RZERO; RING_DET] THEN
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    TRANS_TAC EQ_TRANS
     `ring_det k {i:num | i < n}
        (\i j. if i = j then ring_1 k else ring_0(k:A ring))` THEN
    CONJ_TAC THENL [SIMP_TAC[RING_DET_I; FINITE_NUMSEG_LT]; ALL_TAC] THEN
    MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `n:num`;
                   `g:num->B`; `g':num->B`; `i:num`; `j:num`]
      BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {p:num | p < n}
        (\p. if p < m then
                ring_mul k (basis_coordinates (k,l) (h:A->B) n g'
                              ((g:num->B) p) i)
                           (basis_coordinates (k,l) h m g
                              ((g':num->B) j) p)
             else ring_0 k)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[RING_MUL_LZERO; RING_0]]) in
  MESON_TAC[lemma; ARITH_RULE `m:num = n <=> ~(m < n) /\ ~(n < m)`]);;

let MUL_MATRIX_CHARPOLY_BASIS = prove
 (`!(h:A->B) k l m n g g' x.
        ring_homomorphism(k,l) h /\
        free_basis (k,l) h m g /\ free_basis (k,l) h n g' /\
        x IN ring_carrier l
        ==> ring_charpoly k {i | i < n} (mul_matrix (k,l) h n g' x) =
            ring_charpoly k {i | i < m} (mul_matrix (k,l) h m g x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `trivial_ring(k:A ring)` THENL
   [SUBGOAL_THEN `trivial_ring(poly_ring (k:A ring) (:1))` MP_TAC THENL
     [ASM_REWRITE_TAC[TRIVIAL_POLY_RING]; ALL_TAC] THEN
    REWRITE_TAC[trivial_ring] THEN MESON_TAC[RING_CHARPOLY; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `n:num = m` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[FREE_BASES_SIZE_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `g:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `g':num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL
   [`k:A ring`; `{i:num | i < m}`;
    `\i u. basis_coordinates (k,l) (h:A->B) m g' ((g:num->B) u) i`;
    `mul_matrix (k,l) (h:A->B) m g x`;
    `\v j. basis_coordinates (k,l) (h:A->B) m g ((g':num->B) j) v`]
   RING_CHARPOLY_SIMILAR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; BASIS_COORDINATES_IN_CARRIER;
                 MUL_MATRIX_IN_CARRIER] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `m:num`;
                     `g':num->B`; `g:num->B`; `i:num`; `j:num`]
        BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE);
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `m:num`;
                     `g:num->B`; `g':num->B`; `i:num`; `j:num`]
        BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[ring_charpoly] THEN MATCH_MP_TAC RING_DET_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MUL_MATRIX_CHANGE_OF_BASIS THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Projective bases: the dual basis lemma at the ring level. The functionals *)
(* f i are additive, k-linear and preserve finite linear combinations        *)
(* (PROJECTIVE_BASIS_ADD, _LMUL, _SUM). An additive map u from l to k that   *)
(* is linear over k via h is determined by its values on the e j             *)
(* (PROJECTIVE_BASIS_LINEAR). This gives the change between two projective   *)
(* bases and the product of the arrays of x and y (PROJECTIVE_BASIS_MUL,     *)
(* PROJECTIVE_BASIS_CHANGE). A free basis is a projective basis              *)
(* (FREE_BASIS_PROJECTIVE).                                                  *)
(* ------------------------------------------------------------------------- *)

let PROJECTIVE_BASIS_IN_CARRIER = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> (!i. i < n ==> e i IN ring_carrier l) /\
            (!i x. i < n /\ x IN ring_carrier l ==> f i x IN ring_carrier k)`,
  SIMP_TAC[projective_basis]);;

let PROJECTIVE_BASIS_EXPAND = prove
 (`!(h:A->B) k l n e f x.
        projective_basis (k,l) h n e f /\ x IN ring_carrier l
        ==> ring_sum l {i | i < n} (\i. ring_mul l (h(f i x)) (e i)) = x`,
  SIMP_TAC[projective_basis]);;

let PROJECTIVE_BASIS_ADD = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> !i x y. i < n /\ x IN ring_carrier l /\ y IN ring_carrier l
                    ==> f i (ring_add l x y) = ring_add k (f i x) (f i y)`,
  SIMP_TAC[projective_basis]);;

let PROJECTIVE_BASIS_LMUL = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> !i a x. i < n /\ a IN ring_carrier k /\ x IN ring_carrier l
                    ==> f i (ring_mul l (h a) x) = ring_mul k a (f i x)`,
  SIMP_TAC[projective_basis]);;

let PROJECTIVE_BASIS_0 = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> !i. i < n ==> f i (ring_0 l) = ring_0 k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_RZERO_UNIQUE THEN
  EXISTS_TAC `(f:num->B->A) i (ring_0 l)` THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[GSYM(MATCH_MP PROJECTIVE_BASIS_ADD th); RING_0;
                 RING_ADD_LZERO; MATCH_MP PROJECTIVE_BASIS_IN_CARRIER th]));;

let PROJECTIVE_BASIS_NEG = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> !i x. i < n /\ x IN ring_carrier l
                  ==> f i (ring_neg l x) = ring_neg k (f i x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RING_LNEG_UNIQUE THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[RING_NEG; MATCH_MP PROJECTIVE_BASIS_IN_CARRIER th;
                 GSYM(MATCH_MP PROJECTIVE_BASIS_ADD th);
                 MATCH_MP PROJECTIVE_BASIS_0 th; RING_ADD_RNEG]));;

let PROJECTIVE_BASIS_SUB = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> !i x y. i < n /\ x IN ring_carrier l /\ y IN ring_carrier l
                    ==> f i (ring_sub l x y) = ring_sub k (f i x) (f i y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sub] THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[RING_NEG; MATCH_MP PROJECTIVE_BASIS_ADD th;
                 MATCH_MP PROJECTIVE_BASIS_NEG th]));;

let PROJECTIVE_BASIS_SUM = prove
 (`!(h:A->B) k l n e f.
        ring_homomorphism(k,l) h /\ projective_basis (k,l) h n e f
        ==> !i (s:K->bool) c w.
                i < n /\ FINITE s /\
                (!m. m IN s ==> c m IN ring_carrier k /\ w m IN ring_carrier l)
                ==> f i (ring_sum l s (\m. ring_mul l (h(c m)) (w m))) =
                    ring_sum k s (\m. ring_mul k (c m) (f i (w m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!a. a IN ring_carrier k ==> (h:A->B) a IN ring_carrier l`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_SUM_CLAUSES;
    MATCH_MP PROJECTIVE_BASIS_0 th]) THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`c:K->A`; `w:K->B`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_MUL; RING_SUM;
    MATCH_MP PROJECTIVE_BASIS_ADD th; MATCH_MP PROJECTIVE_BASIS_LMUL th]));;

let PROJECTIVE_BASIS_RING_SUM = prove
 (`!(h:A->B) k l n e f.
        projective_basis (k,l) h n e f
        ==> !i (s:K->bool) y.
                i < n /\ FINITE s /\ (!m. m IN s ==> y m IN ring_carrier l)
                ==> f i (ring_sum l s y) = ring_sum k s (\m. f i (y m))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_SUM_CLAUSES;
    MATCH_MP PROJECTIVE_BASIS_0 th]) THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `y:K->B` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_SUM;
    MATCH_MP PROJECTIVE_BASIS_ADD th]));;

(* An additive map u from l to k, linear over k via h, is determined by its  *)
(* values on the basis.                                                      *)
let PROJECTIVE_BASIS_LINEAR = prove
 (`!(h:A->B) k l n e f (u:B->A) z.
        ring_homomorphism(k,l) h /\ projective_basis (k,l) h n e f /\
        (!x. x IN ring_carrier l ==> u x IN ring_carrier k) /\
        (!x y. x IN ring_carrier l /\ y IN ring_carrier l
               ==> u(ring_add l x y) = ring_add k (u x) (u y)) /\
        (!a x. a IN ring_carrier k /\ x IN ring_carrier l
               ==> u(ring_mul l (h a) x) = ring_mul k a (u x)) /\
        z IN ring_carrier l
        ==> u z = ring_sum k {j | j < n} (\j. ring_mul k (f j z) (u(e j)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN `(u:B->A)(ring_0 l) = ring_0 k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`ring_0 k:A`; `ring_0 l:B`]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
    ASM_SIMP_TAC[RING_0; RING_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:num->bool. FINITE s
        ==> !w. (!j. j IN s ==> w j IN ring_carrier l)
                ==> (u:B->A)(ring_sum l s w) = ring_sum k s (\j. u(w j))`
  (MP_TAC o SPEC `{j:num | j < n}`) THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; RING_SUM];
    REWRITE_TAC[FINITE_NUMSEG_LT]] THEN
  DISCH_THEN(MP_TAC o SPEC
   `\j. ring_mul l ((h:A->B)((f:num->B->A) j z)) (e j)`) THEN
  SUBGOAL_THEN `!j. j < n ==> (h:A->B)((f:num->B->A) j z) IN ring_carrier l`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                 `f:num->B->A`; `z:B`] PROJECTIVE_BASIS_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

(* The functionals of one basis on x z, and on z, through those of another.  *)
let PROJECTIVE_BASIS_MUL = prove
 (`!(h:A->B) k l m n e e' f f' x z i.
        ring_homomorphism(k,l) h /\
        projective_basis (k,l) h m e f /\ projective_basis (k,l) h n e' f' /\
        x IN ring_carrier l /\ z IN ring_carrier l /\ i < m
        ==> f i (ring_mul l x z) =
            ring_sum k {j | j < n}
              (\j. ring_mul k (f i (ring_mul l x (e' j))) (f' j z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f':num->B->A`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e':num->B`;
                 `f':num->B->A`; `\y. (f:num->B->A) i (ring_mul l x y)`;
                 `z:B`] PROJECTIVE_BASIS_LINEAR) THEN
  FIRST_ASSUM(fun th ->
    if rand(concl th) = `f:num->B->A`
    then ASSUME_TAC(MATCH_MP PROJECTIVE_BASIS_ADD th) THEN
         ASSUME_TAC(MATCH_MP PROJECTIVE_BASIS_LMUL th)
    else NO_TAC) THEN
  ASM_SIMP_TAC[RING_MUL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_MUL] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:A->B) a IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul l x (ring_mul l ((h:A->B) a) x') =
      ring_mul l (h a) (ring_mul l x x')`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r x (ring_mul r y z) = ring_mul r y (ring_mul r x (z:B))`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[RING_MUL]];
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_MUL]]);;

let PROJECTIVE_BASIS_CHANGE = prove
 (`!(h:A->B) k l m n e e' f f' z i.
        ring_homomorphism(k,l) h /\
        projective_basis (k,l) h m e f /\ projective_basis (k,l) h n e' f' /\
        z IN ring_carrier l /\ i < m
        ==> f i z =
            ring_sum k {j | j < n} (\j. ring_mul k (f i (e' j)) (f' j z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f':num->B->A`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e':num->B`;
                 `f':num->B->A`; `(f:num->B->A) i`; `z:B`]
    PROJECTIVE_BASIS_LINEAR) THEN
  FIRST_ASSUM(fun th ->
    if rand(concl th) = `f:num->B->A`
    then ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_ADD th;
                      MATCH_MP PROJECTIVE_BASIS_LMUL th]
    else NO_TAC) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[]);;

let FREE_BASIS_PROJECTIVE = prove
 (`!(h:A->B) k l n g.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> projective_basis (k,l) h n g
              (\i x. basis_coordinates (k,l) h n g x i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_SIMP_TAC[projective_basis; BASIS_COORDINATES_IN_CARRIER;
               BASIS_COORDINATES_ADD; BASIS_COORDINATES_LMUL;
               BASIS_COORDINATES_EXPAND]);;

(* ------------------------------------------------------------------------- *)
(* Trace and norm in an arbitrary projective basis, and their basic algebra. *)
(* Two projective bases (n,e,f) and (m,e',f') give the arrays P i j = f i    *)
(* (e' j) and B j k = f' j (y e k). By PROJECTIVE_BASIS_CHANGE and           *)
(* PROJECTIVE_BASIS_MUL, P B is the array of y in the first basis and B P    *)
(* the array of y in the second, so the traces agree. The array A + I - E of *)
(* x is I plus the array of x - 1 (ALGEBRA_NORM_PROJECTIVE_BASIS_ALT), so    *)
(* the norms agree by RING_DET_WEINSTEIN_ARONSZAJN. The identities that hold *)
(* for every ring homomorphism h hold in particular when l has no finite     *)
(* projective basis over k, by the choice of the defaults.                   *)
(* ------------------------------------------------------------------------- *)

let ALGEBRA_TRACE_PROJECTIVE_BASIS = prove
 (`!(h:A->B) k l n e f x.
        ring_homomorphism(k,l) h /\ projective_basis (k,l) h n e f /\
        x IN ring_carrier l
        ==> algebra_trace(k,l) h x =
            ring_sum k {i | i < n} (\i. f i (ring_mul l x (e i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m e' f'.
        projective_basis (k,l) (h:A->B) m e' f'
        ==> ring_sum k {i | i < m} (\i. f' i (ring_mul l x (e' i))) =
            ring_sum k {i | i < n}
              (\i. (f:num->B->A) i (ring_mul l x ((e:num->B) i)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
      check (fun th -> rand(concl th) = `f:num->B->A`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
      check (fun th -> rand(concl th) = `f':num->B->A`)) THEN
    SUBGOAL_THEN
     `(!j. j < n ==> ring_mul l x ((e:num->B) j) IN ring_carrier l) /\
      (!j. j < m ==> ring_mul l x ((e':num->B) j) IN ring_carrier l)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {i:num | i < m}
        (\i. ring_sum k {j:num | j < n}
               (\j. ring_mul k ((f':num->B->A) i (ring_mul l x (e j)))
                               ((f:num->B->A) j ((e':num->B) i))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `n:num`;
                     `e':num->B`; `e:num->B`; `f':num->B->A`; `f:num->B->A`;
                     `x:B`; `(e':num->B) i`; `i:num`]
        PROJECTIVE_BASIS_MUL) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `m:num`;
                   `e:num->B`; `e':num->B`; `f:num->B->A`; `f':num->B->A`;
                   `ring_mul l x ((e:num->B) j)`; `j:num`]
      PROJECTIVE_BASIS_CHANGE) THEN
    ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
    ASM_SIMP_TAC[RING_MUL];
    REWRITE_TAC[algebra_trace] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
    X_GEN_TAC `t:A` THEN ASM_MESON_TAC[]]);;

let ALGEBRA_NORM_PROJECTIVE_BASIS = prove
 (`!(h:A->B) k l n e f x.
        ring_homomorphism(k,l) h /\ projective_basis (k,l) h n e f /\
        x IN ring_carrier l
        ==> algebra_norm(k,l) h x =
            ring_det k {i | i < n}
              (\i j. ring_add k (f i (ring_mul l x (e j)))
                       (ring_sub k (if i = j then ring_1 k else ring_0 k)
                                   (f i (e j))))`,
  let lemma = prove
   (`!(h:A->B) k l n e f x.
        ring_homomorphism(k,l) h /\ projective_basis (k,l) h n e f /\
        x IN ring_carrier l
        ==> ring_det k {i | i < n}
              (\i j. ring_add k (f i (ring_mul l x (e j)))
                       (ring_sub k (if i = j then ring_1 k else ring_0 k)
                                   (f i (e j)))) =
            ring_det k {i | i < n}
              (\i j. ring_add k (if i = j then ring_1 k else ring_0 k)
                       (f i (ring_mul l (ring_sub l x (ring_1 l)) (e j))))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[RING_SUB_RDISTRIB; RING_MUL_LID; RING_1; RING_MUL;
                   MATCH_MP PROJECTIVE_BASIS_SUB th]) THEN
    MATCH_MP_TAC(RING_RULE
     `ring_add r a (ring_sub r d b) = ring_add r d (ring_sub r a (b:A))`) THEN
    ASM_SIMP_TAC[RING_MUL] THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1])
  in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m e' f'.
        projective_basis (k,l) (h:A->B) m e' f'
        ==> ring_det k {i | i < m}
              (\i j. ring_add k (f' i (ring_mul l x (e' j)))
                       (ring_sub k (if i = j then ring_1 k else ring_0 k)
                                   (f' i (e' j)))) =
            ring_det k {i | i < n}
              (\i j. ring_add k ((f:num->B->A) i (ring_mul l x (e j)))
                       (ring_sub k (if i = j then ring_1 k else ring_0 k)
                                   (f i ((e:num->B) j))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `e':num->B`;
                   `f':num->B->A`; `x:B`] lemma) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                   `f:num->B->A`; `x:B`] lemma) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ABBREV_TAC `y = ring_sub l x (ring_1 l:B)` THEN
    SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN ASM_SIMP_TAC[RING_SUB; RING_1]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
      check (fun th -> rand(concl th) = `f:num->B->A`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
      check (fun th -> rand(concl th) = `f':num->B->A`)) THEN
    SUBGOAL_THEN
     `(!j. j < n ==> ring_mul l y ((e:num->B) j) IN ring_carrier l) /\
      (!j. j < m ==> ring_mul l y ((e':num->B) j) IN ring_carrier l)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_det k {i | i < n}
        (\i j. ring_add k (if i = j then ring_1 k else ring_0 k)
                 ((f:num->B->A) i (ring_mul l y ((e:num->B) j)))) =
      ring_det k {i | i < n}
        (\i i'. ring_add k (if i = i' then ring_1 k else ring_0 k)
                  (ring_sum k {j | j < m}
                     (\j. ring_mul k (f i ((e':num->B) j))
                                     ((f':num->B->A) j
                                        (ring_mul l y (e i'))))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      AP_TERM_TAC THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `m:num`;
                     `e:num->B`; `e':num->B`; `f:num->B->A`; `f':num->B->A`;
                     `ring_mul l y ((e:num->B) j)`; `i:num`]
        PROJECTIVE_BASIS_CHANGE) THEN
      ASM_SIMP_TAC[RING_MUL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_det k {i | i < m}
        (\i j. ring_add k (if i = j then ring_1 k else ring_0 k)
                 ((f':num->B->A) i (ring_mul l y ((e':num->B) j)))) =
      ring_det k {j | j < m}
        (\j j'. ring_add k (if j = j' then ring_1 k else ring_0 k)
                  (ring_sum k {i | i < n}
                     (\i. ring_mul k (f' j (ring_mul l y ((e:num->B) i)))
                                     ((f:num->B->A) i (e' j')))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      AP_TERM_TAC THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `n:num`;
                     `e':num->B`; `e:num->B`; `f':num->B->A`; `f:num->B->A`;
                     `y:B`; `(e':num->B) j`; `i:num`]
        PROJECTIVE_BASIS_MUL) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_DET_WEINSTEIN_ARONSZAJN THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
    REWRITE_TAC[algebra_norm] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
    X_GEN_TAC `t:A` THEN ASM_MESON_TAC[]]);;

let ALGEBRA_NORM_PROJECTIVE_BASIS_ALT = prove
 (`!(h:A->B) k l n e f x.
        ring_homomorphism(k,l) h /\ projective_basis (k,l) h n e f /\
        x IN ring_carrier l
        ==> algebra_norm(k,l) h x =
            ring_det k {i | i < n}
              (\i j. ring_add k (if i = j then ring_1 k else ring_0 k)
                       (f i (ring_mul l (ring_sub l x (ring_1 l)) (e j))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                 `f:num->B->A`; `x:B`] ALGEBRA_NORM_PROJECTIVE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[RING_SUB_RDISTRIB; RING_MUL_LID; RING_1; RING_MUL;
                 MATCH_MP PROJECTIVE_BASIS_SUB th]) THEN
  MATCH_MP_TAC(RING_RULE
   `ring_add r a (ring_sub r d b) = ring_add r d (ring_sub r a (b:A))`) THEN
  ASM_SIMP_TAC[RING_MUL] THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1]);;

let ALGEBRA_TRACE_FREE_BASIS,ALGEBRA_NORM_FREE_BASIS = (CONJ_PAIR o prove)
 (`(!(h:A->B) k l n g x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l
        ==> algebra_trace(k,l) h x =
            ring_sum k {i | i < n} (\i. mul_matrix (k,l) h n g x i i)) /\
   (!(h:A->B) k l n g x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l
        ==> algebra_norm(k,l) h x =
            ring_det k {i | i < n} (mul_matrix (k,l) h n g x))`,
  REWRITE_TAC[AND_FORALL_THM;
              TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    FREE_BASIS_PROJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `\i x. basis_coordinates (k,l) (h:A->B) n g x i`; `x:B`]
    ALGEBRA_NORM_PROJECTIVE_BASIS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `\i x. basis_coordinates (k,l) (h:A->B) n g x i`; `x:B`]
    ALGEBRA_TRACE_PROJECTIVE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; mul_matrix];
    MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM; mul_matrix] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_mul l x ((g:num->B) j) IN ring_carrier l` ASSUME_TAC
    THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_BASIS] THEN
    REWRITE_TAC[MESON[RING_0; RING_1; RING_SUB_REFL]
     `ring_sub k (if p then ring_1 k else ring_0 k)
                 (if p then ring_1 k else ring_0 k) = ring_0 (k:A ring)`] THEN
    ASM_SIMP_TAC[RING_ADD_RZERO; BASIS_COORDINATES_IN_CARRIER]]);;

let ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS = prove
 (`!(h:A->B) k l x.
        ~(?n e f. projective_basis (k,l) h n e f)
        ==> algebra_trace(k,l) h x = ring_0 k /\
            algebra_norm(k,l) h x = ring_1 k`,
  SIMP_TAC[algebra_trace; algebra_norm]);;

let ALGEBRA_TRACE_NORM_IN_CARRIER = prove
 (`!(h:A->B) k l x.
        algebra_trace(k,l) h x IN ring_carrier k /\
        algebra_norm(k,l) h x IN ring_carrier k`,
  let lemma = prove
   (`!P (a:A) s. (!t. P t ==> t IN s) /\ P a ==> (@) P IN s`,
    MESON_TAC[SELECT_AX]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[algebra_trace; algebra_norm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
    (X_CHOOSE_TAC `f:num->B->A`))) THEN
  CONJ_TAC THEN MATCH_MP_TAC lemma THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN SIMP_TAC[RING_SUM; RING_DET] THEN
  ASM_MESON_TAC[]);;

let ALGEBRA_TRACE_ADD = prove
 (`!(h:A->B) k l x y.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l /\ y IN ring_carrier l
        ==> algebra_trace(k,l) h (ring_add l x y) =
            ring_add k (algebra_trace(k,l) h x) (algebra_trace(k,l) h y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?n e f. projective_basis (k,l) (h:A->B) n e f` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
      (X_CHOOSE_TAC `f:num->B->A`)));
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; RING_ADD_LZERO;
                 RING_0]] THEN
  ASM_SIMP_TAC[RING_ADD; ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`;
                                 `e:num->B`; `f:num->B->A`]
                           ALGEBRA_TRACE_PROJECTIVE_BASIS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  TRANS_TAC EQ_TRANS
   `ring_sum k {i:num | i < n}
      (\i. ring_add k ((f:num->B->A) i (ring_mul l x (e i)))
                      (f i (ring_mul l y ((e:num->B) i))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_MUL;
                   MATCH_MP PROJECTIVE_BASIS_ADD th]);
    MATCH_MP_TAC RING_SUM_ADD THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL]]);;

let ALGEBRA_TRACE_SCALAR = prove
 (`!(h:A->B) k l a x.
        ring_homomorphism(k,l) h /\ a IN ring_carrier k /\ x IN ring_carrier l
        ==> algebra_trace(k,l) h (ring_mul l (h a) x) =
            ring_mul k a (algebra_trace(k,l) h x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?n e f. projective_basis (k,l) (h:A->B) n e f` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
      (X_CHOOSE_TAC `f:num->B->A`)));
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; RING_MUL_RZERO]] THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL; ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`;
                                 `e:num->B`; `f:num->B->A`]
                           ALGEBRA_TRACE_PROJECTIVE_BASIS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  TRANS_TAC EQ_TRANS
   `ring_sum k {i:num | i < n}
      (\i. ring_mul k a ((f:num->B->A) i (ring_mul l x ((e:num->B) i))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL;
                   MATCH_MP PROJECTIVE_BASIS_LMUL th]);
    MATCH_MP_TAC RING_SUM_LMUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL]]);;

let ALGEBRA_NORM_MUL = prove
 (`!(h:A->B) k l x y.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l /\ y IN ring_carrier l
        ==> algebra_norm(k,l) h (ring_mul l x y) =
            ring_mul k (algebra_norm(k,l) h x) (algebra_norm(k,l) h y)`,
  let lemma = prove
   (`!(r:A ring) (s:K->bool) X Y i j.
        FINITE s /\ i IN s /\ j IN s /\
        (!a b. a IN s /\ b IN s
               ==> X a b IN ring_carrier r /\ Y a b IN ring_carrier r)
        ==> ring_sum r s
              (\m. ring_mul r
                    (ring_add r (if i = m then ring_1 r else ring_0 r) (X i m))
                    (ring_add r (if m = j then ring_1 r else ring_0 r)
                                (Y m j))) =
            ring_add r (if i = j then ring_1 r else ring_0 r)
              (ring_add r (Y i j)
                 (ring_add r (X i j)
                    (ring_sum r s (\m. ring_mul r (X i m) (Y m j)))))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!b. (if b then ring_1 r else ring_0 r) IN ring_carrier(r:A ring)`
    ASSUME_TAC THENL [MESON_TAC[RING_0; RING_1]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r s
       (\m:K. ring_add r
         (ring_add r
           (ring_mul r (if i = m then ring_1 r else ring_0 r)
                       (if m = j then ring_1 r else ring_0 r))
           (ring_mul r (if i = m then ring_1 r else ring_0 r)
                       ((Y:K->K->A) m j)))
         (ring_add r
           (ring_mul r ((X:K->K->A) i m)
                       (if m = j then ring_1 r else ring_0 r))
           (ring_mul r (X i m) (Y m j))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `m:K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC(RING_RULE
       `ring_mul r (ring_add r a b) (ring_add r c d) =
        ring_add r (ring_add r (ring_mul r a c) (ring_mul r a d))
                   (ring_add r (ring_mul r b c) (ring_mul r b (d:A)))`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT(W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_ADD o
             find_term (can (PART_MATCH (lhand o rand) RING_SUM_ADD)) o
             snd) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
             REPEAT((MATCH_MP_TAC RING_ADD ORELSE MATCH_MP_TAC RING_MUL) THEN
                    CONJ_TAC) THEN
             ASM_SIMP_TAC[];
             DISCH_THEN SUBST1_TAC]) THEN
    ASM_SIMP_TAC[RING_SUM_DELTA_MUL] THEN
    MATCH_MP_TAC(GSYM RING_ADD_ASSOC) THEN ASM_SIMP_TAC[RING_ADD; RING_SUM])
  in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?n e f. projective_basis (k,l) (h:A->B) n e f` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
      (X_CHOOSE_TAC `f:num->B->A`)));
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; RING_MUL_LID;
                 RING_1]] THEN
  ASM_SIMP_TAC[RING_MUL; ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`;
                                 `e:num->B`; `f:num->B->A`]
                           ALGEBRA_NORM_PROJECTIVE_BASIS_ALT] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `ring_sub l (ring_mul l x y) (ring_1 l) =
    ring_add l (ring_sub l y (ring_1 l))
      (ring_add l (ring_sub l x (ring_1 l))
         (ring_mul l (ring_sub l x (ring_1 l)) (ring_sub l y (ring_1 l:B))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_sub r (ring_mul r x y) (ring_1 r) =
      ring_add r (ring_sub r y (ring_1 r))
        (ring_add r (ring_sub r x (ring_1 r))
           (ring_mul r (ring_sub r x (ring_1 r))
                       (ring_sub r y (ring_1 r)))):B`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub l x (ring_1 l) IN ring_carrier l /\
    ring_sub l y (ring_1 l:B) IN ring_carrier l`
  MP_TAC THENL [ASM_SIMP_TAC[RING_SUB; RING_1]; ALL_TAC] THEN
  SPEC_TAC(`ring_sub l y (ring_1 l:B)`,`v:B`) THEN
  SPEC_TAC(`ring_sub l x (ring_1 l:B)`,`u:B`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!j. j < n ==> ring_mul l u ((e:num->B) j) IN ring_carrier l) /\
    (!j. j < n ==> ring_mul l v ((e:num->B) j) IN ring_carrier l) /\
    (!i j. i < n /\ j < n
           ==> (f:num->B->A) i (ring_mul l u (e j)) IN ring_carrier k /\
               f i (ring_mul l v (e j)) IN ring_carrier k)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_DET_MUL o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_ADD THEN ASM_SIMP_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`k:A ring`; `{m:num | m < n}`;
    `\a b. (f:num->B->A) a (ring_mul l u ((e:num->B) b))`;
    `\a b. (f:num->B->A) a (ring_mul l v ((e:num->B) b))`;
    `i:num`; `j:num`] lemma) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `n:num`;
                 `e:num->B`; `e:num->B`; `f:num->B->A`; `f:num->B->A`;
                 `u:B`; `ring_mul l v ((e:num->B) j)`; `i:num`]
    PROJECTIVE_BASIS_MUL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `ring_mul l u (ring_mul l v ((e:num->B) j)) IN ring_carrier l`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_MUL; RING_ADD; GSYM RING_MUL_ASSOC;
                 MATCH_MP PROJECTIVE_BASIS_ADD th]));;

let ALGEBRA_TRACE_NORM_BASE_FREE_BASIS = prove
 (`!(h:A->B) k l n g a.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        a IN ring_carrier k
        ==> algebra_trace(k,l) h (h a) = ring_mul k (ring_of_num k n) a /\
            algebra_norm(k,l) h (h a) = ring_pow k a n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
                 ALGEBRA_TRACE_FREE_BASIS;
               ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
                 ALGEBRA_NORM_FREE_BASIS] THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS `ring_sum k {i:num | i < n} (\i. a:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN
      ASM_SIMP_TAC[IN_ELIM_THM; MUL_MATRIX_SCALAR];
      ASM_SIMP_TAC[RING_SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]];
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MUL_MATRIX_SCALAR];
      DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS `ring_product k {i:num | i < n} (\i. a:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN
      ASM_SIMP_TAC[IN_ELIM_THM; MUL_MATRIX_SCALAR];
      ASM_SIMP_TAC[RING_PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]]]);;

let ALGEBRA_TRACE_0,ALGEBRA_NORM_1 = (CONJ_PAIR o prove)
 (`(!(h:A->B) k l.
        ring_homomorphism(k,l) h
        ==> algebra_trace(k,l) h (ring_0 l) = ring_0 k) /\
   (!(h:A->B) k l.
        ring_homomorphism(k,l) h
        ==> algebra_norm(k,l) h (ring_1 l) = ring_1 k)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_0 k:A`;
                   `ring_0 l:B`] ALGEBRA_TRACE_SCALAR) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
    ASM_SIMP_TAC[RING_0; RING_MUL_LZERO; ALGEBRA_TRACE_NORM_IN_CARRIER];
    ALL_TAC] THEN
  ASM_CASES_TAC `?n e f. projective_basis (k,l) (h:A->B) n e f` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
      (X_CHOOSE_TAC `f:num->B->A`)));
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS]] THEN
  ASM_SIMP_TAC[RING_1; ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`;
                               `e:num->B`; `f:num->B->A`]
                         ALGEBRA_NORM_PROJECTIVE_BASIS_ALT] THEN
  TRANS_TAC EQ_TRANS
   `ring_det k {i:num | i < n}
      (\i j. if i = j then ring_1 k else ring_0 (k:A ring))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[RING_SUB_REFL; RING_1; RING_MUL_LZERO;
                   MATCH_MP PROJECTIVE_BASIS_0 th]) THEN
    COND_CASES_TAC THEN SIMP_TAC[RING_ADD_RZERO; RING_0; RING_1];
    SIMP_TAC[RING_DET_I; FINITE_NUMSEG_LT]]);;

let ALGEBRA_TRACE_NEG = prove
 (`!(h:A->B) k l x.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l
        ==> algebra_trace(k,l) h (ring_neg l x) =
            ring_neg k (algebra_trace(k,l) h x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_neg l x = ring_mul l ((h:A->B)(ring_neg k (ring_1 k))) x`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_NEG th;
                                       MATCH_MP RING_HOMOMORPHISM_1 th;
                                       RING_1]) THEN
    ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL_LID; RING_1];
    ASM_SIMP_TAC[ALGEBRA_TRACE_SCALAR; RING_NEG; RING_1] THEN
    ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL_LID; RING_1;
                 ALGEBRA_TRACE_NORM_IN_CARRIER]]);;

let ALGEBRA_TRACE_SUB = prove
 (`!(h:A->B) k l x y.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l /\ y IN ring_carrier l
        ==> algebra_trace(k,l) h (ring_sub l x y) =
            ring_sub k (algebra_trace(k,l) h x) (algebra_trace(k,l) h y)`,
  SIMP_TAC[ring_sub; ALGEBRA_TRACE_ADD; ALGEBRA_TRACE_NEG; RING_NEG]);;

let ALGEBRA_NORM_POW = prove
 (`!(h:A->B) k l x n.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l
        ==> algebra_norm(k,l) h (ring_pow l x n) =
            ring_pow k (algebra_norm(k,l) h x) n`,
  REPLICATE_TAC 4 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  STRIP_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; ALGEBRA_NORM_1; ALGEBRA_NORM_MUL; RING_POW]);;

let ALGEBRA_TRACE_SUM = prove
 (`!(h:A->B) k l (s:K->bool) x.
        ring_homomorphism(k,l) h /\ FINITE s /\
        (!i. i IN s ==> x i IN ring_carrier l)
        ==> algebra_trace(k,l) h (ring_sum l s x) =
            ring_sum k s (\i. algebra_trace(k,l) h (x i))`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; ALGEBRA_TRACE_0; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_SUM; ALGEBRA_TRACE_ADD; ALGEBRA_TRACE_NORM_IN_CARRIER]);;

let ALGEBRA_NORM_PRODUCT = prove
 (`!(h:A->B) k l (s:K->bool) x.
        ring_homomorphism(k,l) h /\ FINITE s /\
        (!i. i IN s ==> x i IN ring_carrier l)
        ==> algebra_norm(k,l) h (ring_product l s x) =
            ring_product k s (\i. algebra_norm(k,l) h (x i))`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; ALGEBRA_NORM_1; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_PRODUCT; ALGEBRA_NORM_MUL; ALGEBRA_TRACE_NORM_IN_CARRIER]);;

(* Traces and norms in a subring r of k when the matrix has its entries in   *)
(* r.                                                                        *)
let ALGEBRA_TRACE_SUBRING = prove
 (`!(h:A->B) k l n g r x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        r subring_of k /\ x IN ring_carrier l /\
        (!j. j < n
             ==> ?c. (!i. i < n ==> c i IN r) /\
                     ring_mul l x (g j) =
                     ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)))
        ==> algebra_trace (k,l) h x IN r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `r:A->bool`; `x:B`] MUL_MATRIX_SUBRING) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `x:B`] ALGEBRA_TRACE_FREE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let ALGEBRA_NORM_SUBRING = prove
 (`!(h:A->B) k l n g r x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        r subring_of k /\ x IN ring_carrier l /\
        (!j. j < n
             ==> ?c. (!i. i < n ==> c i IN r) /\
                     ring_mul l x (g j) =
                     ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)))
        ==> algebra_norm (k,l) h x IN r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `r:A->bool`; `x:B`] MUL_MATRIX_SUBRING) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `x:B`] ALGEBRA_NORM_FREE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_DET_SUBRING THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

(* The trace of a linear combination (no basis needed).                      *)
let ALGEBRA_TRACE_RING_SUM = prove
 (`!(h:A->B) k l (s:K->bool) a y.
        ring_homomorphism(k,l) h /\ FINITE s /\
        (!m. m IN s ==> a m IN ring_carrier k) /\
        (!m. m IN s ==> y m IN ring_carrier l)
        ==> algebra_trace (k,l) h
              (ring_sum l s (\m. ring_mul l (h(a m)) (y m))) =
            ring_sum k s
              (\m. ring_mul k (a m) (algebra_trace (k,l) h (y m)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `s:K->bool`;
    `\m. ring_mul l ((h:A->B)((a:K->A) m)) ((y:K->B) m)`]
   ALGEBRA_TRACE_SUM)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_MUL; RING_HOMOMORPHISM_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[ALGEBRA_TRACE_SCALAR]);;

let ALGEBRA_TRACE_LINCOMB_MUL = prove
 (`!(h:A->B) k l (s:K->bool) c y x.
        ring_homomorphism(k,l) h /\ FINITE s /\
        (!p. p IN s ==> c p IN ring_carrier k) /\
        (!p. p IN s ==> y p IN ring_carrier l) /\ x IN ring_carrier l
        ==> algebra_trace (k,l) h
              (ring_mul l (ring_sum l s (\p. ring_mul l (h(c p)) (y p))) x) =
            ring_sum k s
              (\p. ring_mul k (c p)
                     (algebra_trace (k,l) h (ring_mul l (y p) x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:K->bool`; `c:K->A`;
                 `y:K->B`; `x:B`] EXTENSION_LINCOMB_MUL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `s:K->bool`;
    `c:K->A`; `\p. ring_mul l ((y:K->B) p) x`] ALGEBRA_TRACE_RING_SUM)) THEN
  ASM_SIMP_TAC[RING_MUL]);;

let ALGEBRA_TRACE_MUL_LINCOMB = prove
 (`!(h:A->B) k l (s:K->bool) c y x.
        ring_homomorphism(k,l) h /\ FINITE s /\
        (!p. p IN s ==> c p IN ring_carrier k) /\
        (!p. p IN s ==> y p IN ring_carrier l) /\ x IN ring_carrier l
        ==> algebra_trace (k,l) h
              (ring_mul l x (ring_sum l s (\p. ring_mul l (h(c p)) (y p)))) =
            ring_sum k s
              (\p. ring_mul k (c p)
                     (algebra_trace (k,l) h (ring_mul l x (y p))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:K->bool`; `c:K->A`;
                 `y:K->B`; `x:B`] EXTENSION_MUL_LINCOMB) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `s:K->bool`;
    `c:K->A`; `\p. ring_mul l x ((y:K->B) p)`] ALGEBRA_TRACE_RING_SUM)) THEN
  ASM_SIMP_TAC[RING_MUL]);;

(* The norm of h c - x is the characteristic polynomial of x at c.           *)
let ALGEBRA_NORM_SUB_CHARPOLY = prove
 (`!(h:A->B) k l n g c x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        c IN ring_carrier k /\ x IN ring_carrier l
        ==> algebra_norm (k,l) h (ring_sub l (h c) x) =
            poly_eval k
             (ring_charpoly k {i | i < n} (mul_matrix (k,l) h n g x)) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(h:A->B) c IN ring_carrier l /\
    h(ring_neg k (ring_1 k)) IN ring_carrier l /\
    ring_sub l (h c) x =
    ring_add l (h c) (ring_mul l (h(ring_neg k (ring_1 k))) x)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ q /\ (p ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_NEG; RING_1];
      FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_NEG th;
       MATCH_MP RING_HOMOMORPHISM_1 th; RING_1]) THEN
      DISCH_TAC THEN MATCH_MP_TAC(RING_RULE
       `ring_sub r c (x:A) =
        ring_add r c (ring_mul r (ring_neg r (ring_1 r)) x)`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `ring_sub l ((h:A->B) c) x`] ALGEBRA_NORM_FREE_BASIS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_SUB]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RING_CHARPOLY_EVAL; FINITE_NUMSEG_LT; IN_ELIM_THM;
               MUL_MATRIX_IN_CARRIER] THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MUL_MATRIX_ADD; MUL_MATRIX_LMUL; MUL_MATRIX_SCALAR; RING_MUL;
               RING_NEG; RING_1] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_add r a (ring_mul r (ring_neg r (ring_1 r)) b) =
    ring_sub r a (b:A)`) THEN
  ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0]);;

(* Two injective structure maps with the same image have the same free and   *)
(* projective bases, and the same trace and norm up to the two maps.         *)

let FREE_BASIS_EQ_IMAGE = prove
 (`!(h1:A->B) (h2:C->B) k1 k2 l n g.
        ring_monomorphism(k1,l) h1 /\ ring_monomorphism(k2,l) h2 /\
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2)
        ==> (free_basis (k1,l) h1 n g <=> free_basis (k2,l) h2 n g)`,
  let lemma = prove
   (`!(h1:A->B) (h2:C->B) k1 k2 l n g.
        ring_monomorphism(k1,l) h1 /\ ring_monomorphism(k2,l) h2 /\
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2) /\
        free_basis (k1,l) h1 n g
        ==> free_basis (k2,l) h2 n g`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
    SUBGOAL_THEN
     `ring_homomorphism(k1,l) (h1:A->B) /\ ring_homomorphism(k2,l) (h2:C->B)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!d. (!i. i < n ==> (d:num->C) i IN ring_carrier k2)
          ==> ?c. !i. i < n ==> c i IN ring_carrier k1 /\
                                (h1:A->B)(c i) = (h2:C->B)(d i)`
    (LABEL_TAC "dc") THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN
      DISCH_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[free_basis] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `?d. !i. i < n
                ==> (d:num->C) i IN ring_carrier k2 /\
                    (h2:C->B)(d i) =
                    (h1:A->B)(basis_coordinates (k1,l) h1 n g x i)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
        REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`h1:A->B`; `k1:A ring`; `l:B ring`; `n:num`;
                       `g:num->B`; `x:B`; `i:num`]
          BASIS_COORDINATES_IN_CARRIER) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `d:num->C` THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`h1:A->B`; `k1:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                     `x:B`] BASIS_COORDINATES_EXPAND) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
      X_GEN_TAC `d:num->C` THEN STRIP_TAC THEN
      REMOVE_THEN "dc" (MP_TAC o SPEC `d:num->C`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`h1:A->B`; `k1:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                     `c:num->A`] FREE_BASIS_INDEPENDENT) THEN
      ASM_SIMP_TAC[] THEN ANTS_TAC THENL
       [TRANS_TAC EQ_TRANS
         `ring_sum l {i:num | i < n}
            (\i. ring_mul l ((h2:C->B)(d i)) ((g:num->B) i))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
          ASM_REWRITE_TAC[]];
        DISCH_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k2:C ring`; `l:B ring`; `h2:C->B`; `(d:num->C) i`;
                     `ring_0 k2:C`] RING_MONOMORPHISM_INJECTIVE_EQ) THEN
      ASM_SIMP_TAC[RING_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
       `(h2:C->B)(d(i:num)) = (h1:A->B)(c i) /\ (c:num->A) i = ring_0 k1`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[RING_HOMOMORPHISM_0]]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`h1:A->B`; `h2:C->B`; `k1:A ring`; `k2:C ring`; `l:B ring`;
                   `n:num`; `g:num->B`] lemma);
    MP_TAC(ISPECL [`h2:C->B`; `h1:A->B`; `k2:C ring`; `k1:A ring`; `l:B ring`;
                   `n:num`; `g:num->B`] lemma)] THEN
  ASM_REWRITE_TAC[]);;

let PROJECTIVE_BASIS_EQ_IMAGE = prove
 (`!(h1:A->B) (h2:C->B) k1 k2 l n e f.
        ring_monomorphism(k1,l) h1 /\ ring_monomorphism(k2,l) h2 /\
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2) /\
        projective_basis (k1,l) h1 n e f
        ==> ?f'. projective_basis (k2,l) h2 n e f' /\
                 !i x. i < n /\ x IN ring_carrier l
                       ==> h2(f' i x) = h1(f i x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k1,l) (h1:A->B) /\ ring_homomorphism(k2,l) (h2:C->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!c d. c IN ring_carrier k2 /\ d IN ring_carrier k2 /\
          (h2:C->B) c = h2 d ==> c = d`
  ASSUME_TAC THENL [ASM_MESON_TAC[ring_monomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. b IN IMAGE (h1:A->B) (ring_carrier k1)
        ==> ?c. c IN ring_carrier k2 /\ (h2:C->B) c = b`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->C` o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  EXISTS_TAC `\i x. (g:B->C)((h1:A->B)((f:num->B->A) i x))` THEN
  SUBGOAL_THEN
   `!i x. i < n /\ x IN ring_carrier l
          ==> (g:B->C)((h1:A->B)((f:num->B->A) i x)) IN ring_carrier k2 /\
              (h2:C->B)(g(h1(f i x))) = h1(f i x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN
   `!c d. c IN ring_carrier k2 /\ d IN ring_carrier k2 /\
          (h2:C->B) c = h2 d ==> c = d`
   (fun th -> ASM_SIMP_TAC[projective_basis] THEN ASSUME_TAC th) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!c d. c IN ring_carrier k2 /\ d IN ring_carrier k2 /\
                        (h2:C->B) c = h2 d ==> c = d`)) THEN
    ASM_SIMP_TAC[RING_ADD] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD
                  (ASSUME `ring_homomorphism(k2,l) (h2:C->B)`)] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD
                  (ASSUME `ring_homomorphism(k1,l) (h1:A->B)`);
                 MATCH_MP PROJECTIVE_BASIS_ADD
                  (ASSUME `projective_basis (k1,l) (h1:A->B) n e f`)];
    MAP_EVERY X_GEN_TAC [`i:num`; `a:C`; `x:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?a'. a' IN ring_carrier k1 /\ (h1:A->B) a' = (h2:C->B) a`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h2:C->B) a IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!c d. c IN ring_carrier k2 /\ d IN ring_carrier k2 /\
                        (h2:C->B) c = h2 d ==> c = d`)) THEN
    ASM_SIMP_TAC[RING_MUL] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                  (ASSUME `ring_homomorphism(k2,l) (h2:C->B)`)] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(h1:A->B) a' = (h2:C->B) a`)) THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                  (ASSUME `ring_homomorphism(k1,l) (h1:A->B)`);
                 MATCH_MP PROJECTIVE_BASIS_LMUL
                  (ASSUME `projective_basis (k1,l) (h1:A->B) n e f`)];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h1:A->B`; `k1:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                   `f:num->B->A`; `x:B`] PROJECTIVE_BASIS_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]]);;

let ALGEBRA_TRACE_NORM_EQ_IMAGE = prove
 (`!(h1:A->B) (h2:C->B) k1 k2 l x.
        ring_monomorphism(k1,l) h1 /\ ring_monomorphism(k2,l) h2 /\
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2) /\
        x IN ring_carrier l
        ==> h1(algebra_trace(k1,l) h1 x) = h2(algebra_trace(k2,l) h2 x) /\
            h1(algebra_norm(k1,l) h1 x) = h2(algebra_norm(k2,l) h2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k1,l) (h1:A->B) /\ ring_homomorphism(k2,l) (h2:C->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  ASM_CASES_TAC `?n e f. projective_basis (k1,l) (h1:A->B) n e f` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
      (X_CHOOSE_TAC `f:num->B->A`)));
    SUBGOAL_THEN `~(?n e f. projective_basis (k2,l) (h2:C->B) n e f)`
    ASSUME_TAC THENL
     [REWRITE_TAC[NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `e:num->B`; `f:num->B->C`] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`h2:C->B`; `h1:A->B`; `k2:C ring`; `k1:A ring`;
                     `l:B ring`; `n:num`; `e:num->B`; `f:num->B->C`]
        PROJECTIVE_BASIS_EQ_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1]] THEN
  MP_TAC(ISPECL [`h1:A->B`; `h2:C->B`; `k1:A ring`; `k2:C ring`; `l:B ring`;
                 `n:num`; `e:num->B`; `f:num->B->A`]
    PROJECTIVE_BASIS_EQ_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':num->B->C` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f':num->B->C`)) THEN
  SUBGOAL_THEN `!j. j < n ==> ring_mul l x ((e:num->B) j) IN ring_carrier l`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < n /\ j < n
          ==> (f:num->B->A) i (ring_mul l x ((e:num->B) j)) IN
              ring_carrier k1 /\
              f i (e j) IN ring_carrier k1 /\
              (f':num->B->C) i (ring_mul l x (e j)) IN ring_carrier k2 /\
              f' i (e j) IN ring_carrier k2`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ISPECL [`h1:A->B`; `k1:A ring`; `l:B ring`; `n:num`;
                       `e:num->B`; `f:num->B->A`]
                 ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`h1:A->B`; `k1:A ring`; `l:B ring`; `n:num`;
                       `e:num->B`; `f:num->B->A`]
                 ALGEBRA_NORM_PROJECTIVE_BASIS;
               ISPECL [`h2:C->B`; `k2:C ring`; `l:B ring`; `n:num`;
                       `e:num->B`; `f':num->B->C`]
                 ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`h2:C->B`; `k2:C ring`; `l:B ring`; `n:num`;
                       `e:num->B`; `f':num->B->C`]
                 ALGEBRA_NORM_PROJECTIVE_BASIS] THEN
  SUBGOAL_THEN
   `(!b. (if b then ring_1 k1 else ring_0 k1) IN ring_carrier(k1:A ring)) /\
    (!b. (if b then ring_1 k2 else ring_0 k2) IN ring_carrier(k2:C ring))`
  STRIP_ASSUME_TAC THENL [MESON_TAC[RING_0; RING_1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:A ring`; `l:B ring`; `h1:A->B`; `{i:num | i < n}`;
    `\i j. ring_add k1 ((f:num->B->A) i (ring_mul l x ((e:num->B) j)))
             (ring_sub k1 (if i = j then ring_1 k1 else ring_0 k1)
                          (f i (e j)))`]
    RING_DET_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`k2:C ring`; `l:B ring`; `h2:C->B`; `{i:num | i < n}`;
    `\i j. ring_add k2 ((f':num->B->C) i (ring_mul l x ((e:num->B) j)))
             (ring_sub k2 (if i = j then ring_1 k2 else ring_0 k2)
                          (f' i (e j)))`]
    RING_DET_HOMOMORPHISM) THEN
  MP_TAC(ISPECL
   [`\i. (f:num->B->A) i (ring_mul l x ((e:num->B) i))`; `{i:num | i < n}`]
   (MATCH_MP RING_HOMOMORPHISM_SUM (ASSUME
     `ring_homomorphism(k1,l) (h1:A->B)`))) THEN
  MP_TAC(ISPECL
   [`\i. (f':num->B->C) i (ring_mul l x ((e:num->B) i))`; `{i:num | i < n}`]
   (MATCH_MP RING_HOMOMORPHISM_SUM (ASSUME
     `ring_homomorphism(k2,l) (h2:C->B)`))) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_ADD; RING_SUB; o_DEF] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
    MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM((fun th -> ASM_SIMP_TAC[RING_ADD; RING_SUB;
      MATCH_MP RING_HOMOMORPHISM_ADD th; MATCH_MP RING_HOMOMORPHISM_SUB th]) o
      check (fun th -> concl th = `ring_homomorphism(k1,l) (h1:A->B)`)) THEN
    FIRST_ASSUM((fun th -> ASM_SIMP_TAC[RING_ADD; RING_SUB;
      MATCH_MP RING_HOMOMORPHISM_ADD th; MATCH_MP RING_HOMOMORPHISM_SUB th]) o
      check (fun th -> concl th = `ring_homomorphism(k2,l) (h2:C->B)`)) THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[RING_HOMOMORPHISM_0;
                                      RING_HOMOMORPHISM_1]]);;

(* ------------------------------------------------------------------------- *)
(* Units. An element x of a finite projective extension is a unit exactly    *)
(* when its norm is (ALGEBRA_NORM_UNIT_PROJECTIVE). If the determinant of I  *)
(* + A(x - 1) is a unit, the adjugate solves (I + A(x - 1)) c = (f i 1);     *)
(* then c i = f i w for w = 1 - (x - 1) y, where y = sum_j h(c j) e j, so y  *)
(* = w and x y = 1. The basis is a null vector of h(I - E) from the left, so *)
(* h maps the norm of 0 to 0; hence the norm of 0 is 0 when h is injective   *)
(* (ALGEBRA_NORM_0_PROJECTIVE), and then the norm of an inverse is the       *)
(* inverse of the norm (ALGEBRA_NORM_INV). For non-injective h this can      *)
(* fail: for k = Z/6 and l = Z/2 the norm of 0 is 4.                         *)
(* ------------------------------------------------------------------------- *)

let ALGEBRA_NORM_UNIT_PROJECTIVE = prove
 (`!(h:A->B) k l x.
        ring_homomorphism(k,l) h /\ (?n e f. projective_basis (k,l) h n e f) /\
        x IN ring_carrier l
        ==> (ring_unit k (algebra_norm(k,l) h x) <=> ring_unit l x)`,
  let lemma = prove
   (`!(r:A ring) s (m:K->K->A) e.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> m i j IN ring_carrier r) /\
        (!i. i IN s ==> e i IN ring_carrier r) /\ ring_unit r (ring_det r s m)
        ==> ?c. (!j. j IN s ==> c j IN ring_carrier r) /\
                !i. i IN s
                    ==> ring_sum r s (\j. ring_mul r (m i j) (c j)) = e i`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?v. (!i. i IN s ==> (v:K->A) i IN ring_carrier r) /\
          (!i. i IN s ==> ring_mul r (ring_det r s m) (v i) = e i)`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `\i. ring_mul r (ring_inv r (ring_det r s (m:K->K->A)))
                                 ((e:K->A) i)` THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RING_MUL; RING_INV; RING_DET] THEN
      ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; RING_DET] THEN
      ASM_SIMP_TAC[RING_MUL_RINV; RING_MUL_LID];
      ALL_TAC] THEN
    EXISTS_TAC
     `\j. ring_sum r s
            (\i'. ring_mul r (ring_cofactor r s (m:K->K->A) i' j) (v i'))` THEN
    ASM_SIMP_TAC[RING_SUM] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r s
       (\i'. ring_mul r
              (ring_sum r s
                (\j. ring_mul r ((m:K->K->A) i j) (ring_cofactor r s m i' j)))
              ((v:K->A) i'))` THEN
    CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_sum r s (\j. ring_sum r s
          (\i'. ring_mul r ((m:K->K->A) i j)
                  (ring_mul r (ring_cofactor r s m i' j) ((v:K->A) i'))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_MUL; RING_COFACTOR];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[RING_MUL; RING_COFACTOR]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i':K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      ASM_SIMP_TAC[GSYM RING_SUM_RMUL; RING_MUL; RING_COFACTOR] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[RING_MUL_ASSOC; RING_COFACTOR];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r s (\i'. if i' = i then (e:K->A) i else ring_0 r)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[RING_SUM_DELTA]] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i':K` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_DET_ADJUGATE_ROWS] THEN
    ASM_CASES_TAC `i':K = i` THEN ASM_SIMP_TAC[RING_MUL_LZERO]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:num->B`
      (X_CHOOSE_TAC `f:num->B->A`))) ASSUME_TAC)) THEN
  EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[ring_unit; ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `algebra_norm(k,l) (h:A->B) y` THEN
    ASM_SIMP_TAC[GSYM ALGEBRA_NORM_MUL; ALGEBRA_TRACE_NORM_IN_CARRIER;
                 ALGEBRA_NORM_1]] THEN
  SUBGOAL_THEN `?u. u IN ring_carrier l /\ x = ring_add l u (ring_1 l:B)`
  (X_CHOOSE_THEN `u:B` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [EXISTS_TAC `ring_sub l x (ring_1 l:B)` THEN
    ASM_SIMP_TAC[RING_SUB; RING_1] THEN
    MATCH_MP_TAC(RING_RULE
     `x = ring_add r (ring_sub r x (ring_1 r)) (ring_1 r):B`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_sub l (ring_add l u (ring_1 l)) (ring_1 l):B = u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_sub r (ring_add r u (ring_1 r)) (ring_1 r):B = u`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                       `f:num->B->A`] ALGEBRA_NORM_PROJECTIVE_BASIS_ALT] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `(!j. j < n ==> ring_mul l u ((e:num->B) j) IN ring_carrier l) /\
    (!i j. i < n /\ j < n
           ==> (f:num->B->A) i (ring_mul l u (e j)) IN ring_carrier k) /\
    (!i. i < n ==> f i (ring_1 l) IN ring_carrier k) /\
    (!b. (if b then ring_1 k else ring_0 k) IN ring_carrier(k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; RING_1] THEN MESON_TAC[RING_0; RING_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`k:A ring`; `{i:num | i < n}`;
    `\i j. ring_add k (if i = j then ring_1 k else ring_0 k)
                      ((f:num->B->A) i (ring_mul l u ((e:num->B) j)))`;
    `\i. (f:num->B->A) i (ring_1 l)`] lemma) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  ABBREV_TAC
   `y = ring_sum l {j:num | j < n} (\j. ring_mul l ((h:A->B)(c j)) (e j))` THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < n ==> (h:A->B)((c:num->A) j) IN ring_carrier l`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> (c:num->A) i =
            (f:num->B->A) i (ring_sub l (ring_1 l) (ring_mul l u y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REMOVE_THEN "c" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!j. j < n
          ==> ring_mul k (if i = j then ring_1 k else ring_0 k) (c j)
              IN ring_carrier k /\
              ring_mul k ((f:num->B->A) i (ring_mul l u ((e:num->B) j)))
                         (c j) IN ring_carrier k`
    ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_sum k {j:num | j < n}
        (\j. ring_mul k
              (ring_add k (if i = j then ring_1 k else ring_0 k)
                          ((f:num->B->A) i (ring_mul l u ((e:num->B) j))))
              (c j)) =
      ring_add k (c i) (f i (ring_mul l u y))`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_sum k {j:num | j < n}
          (\j. ring_add k
                (ring_mul k (if i = j then ring_1 k else ring_0 k) (c j))
                (ring_mul k ((f:num->B->A) i (ring_mul l u ((e:num->B) j)))
                            (c j)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC RING_ADD_RDISTRIB THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_ADD o lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[REWRITE_RULE[IN_ELIM_THM]
                    (ISPECL [`k:A ring`; `{m:num | m < n}`]
                       RING_SUM_DELTA_MUL)] THEN
      AP_TERM_TAC THEN EXPAND_TAC "y" THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{j:num | j < n}`;
                     `c:num->A`; `e:num->B`; `u:B`] EXTENSION_MUL_LINCOMB) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`i:num`; `{j:num | j < n}`; `c:num->A`;
                     `\j. ring_mul l u ((e:num->B) j)`]
        (MATCH_MP PROJECTIVE_BASIS_SUM
          (CONJ (ASSUME `ring_homomorphism(k,l) (h:A->B)`)
                (ASSUME `projective_basis (k,l) (h:A->B) n e f`)))) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[RING_MUL; RING_1; MATCH_MP PROJECTIVE_BASIS_SUB th]) THEN
    MATCH_MP_TAC(RING_RULE
     `ring_add r a1 a2 = a3 ==> a1 = ring_sub r a3 (a2:A)`) THEN
    ASM_SIMP_TAC[RING_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `y = ring_sub l (ring_1 l) (ring_mul l u y):B` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                   `f:num->B->A`; `ring_sub l (ring_1 l) (ring_mul l u y):B`]
      PROJECTIVE_BASIS_EXPAND) THEN
    ASM_SIMP_TAC[RING_SUB; RING_1; RING_MUL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "y" THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[ring_unit] THEN ASM_SIMP_TAC[RING_ADD; RING_1] THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> lhs(concl th) = `y:B`)) THEN
  MATCH_MP_TAC(RING_RULE
   `y = ring_sub r (ring_1 r) (ring_mul r u y)
    ==> ring_mul r (ring_add r u (ring_1 r)) y = ring_1 r:B`) THEN
  ASM_REWRITE_TAC[]);;

let ALGEBRA_NORM_UNIT = prove
 (`!(h:A->B) k l x.
        ring_homomorphism(k,l) h /\ (?n g. free_basis (k,l) h n g) /\
        x IN ring_carrier l
        ==> (ring_unit k (algebra_norm(k,l) h x) <=> ring_unit l x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRA_NORM_UNIT_PROJECTIVE THEN
  ASM_MESON_TAC[FREE_BASIS_PROJECTIVE]);;

let ALGEBRA_NORM_0_FREE_BASIS = prove
 (`!(h:A->B) k l n g.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\ 0 < n
        ==> algebra_norm (k,l) h (ring_0 l) = ring_0 k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `ring_0 l:B`] ALGEBRA_NORM_FREE_BASIS) THEN
  ASM_REWRITE_TAC[RING_0] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_det k {i | i < n}
      (\i j. if i = 0 then ring_0 k
             else mul_matrix (k,l) (h:A->B) n g (ring_0 l) i j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; MUL_MATRIX_0; COND_ID];
    MATCH_MP_TAC RING_DET_ROW_0 THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]]);;

let ALGEBRA_NORM_0 = prove
 (`!(h:A->B) k l.
        ring_homomorphism(k,l) h /\ (?n g. free_basis (k,l) h n g) /\
        ~trivial_ring l
        ==> algebra_norm(k,l) h (ring_0 l) = ring_0 k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `g:num->B`)) ASSUME_TAC)) THEN
  MATCH_MP_TAC ALGEBRA_NORM_0_FREE_BASIS THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `g:num->B`] THEN
  ASM_REWRITE_TAC[LT_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~trivial_ring(l:B ring)` THEN
  REWRITE_TAC[TRIVIAL_RING_SUBSET; SUBSET; IN_SING] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `0:num`; `g:num->B`;
                 `y:B`] BASIS_COORDINATES_EXPAND) THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
  MESON_TAC[]);;

let ALGEBRA_NORM_0_PROJECTIVE = prove
 (`!(h:A->B) k l.
        ring_monomorphism(k,l) h /\ (?n e f. projective_basis (k,l) h n e f)
        ==> algebra_norm(k,l) h (ring_0 l) = ring_0 k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
    (X_CHOOSE_THEN `e:num->B` (X_CHOOSE_TAC `f:num->B->A`)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`;
                 `algebra_norm(k,l) (h:A->B) (ring_0 l)`; `ring_0 k:A`]
    RING_MONOMORPHISM_INJECTIVE_EQ) THEN
  ASM_REWRITE_TAC[RING_0; ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                 `f:num->B->A`; `ring_0 l:B`]
    ALGEBRA_NORM_PROJECTIVE_BASIS) THEN
  ASM_REWRITE_TAC[RING_0] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i j. i < n /\ j < n
          ==> (f:num->B->A) i (e j) IN ring_carrier k /\
              ring_add k (f i (ring_mul l (ring_0 l) ((e:num->B) j)))
                (ring_sub k (if i = j then ring_1 k else ring_0 k)
                            (f i (e j))) =
              ring_sub k (if i = j then ring_1 k else ring_0 k) (f i (e j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[RING_MUL_LZERO] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_0 th]) THEN
    MATCH_MP_TAC RING_ADD_LZERO THEN
    MATCH_MP_TAC RING_SUB THEN ASM_SIMP_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `(h:A->B)(ring_det k {i:num | i < n}
      (\i j. ring_sub k (if i = j then ring_1 k else ring_0 k)
                        ((f:num->B->A) i ((e:num->B) j))))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `{i:num | i < n}`;
                 `\i j. ring_sub k (if i = j then ring_1 k else ring_0 k)
                                 ((f:num->B->A) i ((e:num->B) j))`]
    RING_DET_HOMOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_SUB THEN ASM_SIMP_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC
   `d = ring_det l {i:num | i < n}
         (\i j. (h:A->B)(ring_sub k (if i = j then ring_1 k else ring_0 k)
                                    ((f:num->B->A) i ((e:num->B) j))))` THEN
  SUBGOAL_THEN
   `!i j. i < n /\ j < n
          ==> (h:A->B)(ring_sub k (if i = j then ring_1 k else ring_0 k)
                                  ((f:num->B->A) i ((e:num->B) j))) =
              ring_sub l (if i = j then ring_1 l else ring_0 l)
                         (h(f i (e j))) /\
              h(f i (e j)) IN ring_carrier l`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; RING_1;
      MATCH_MP RING_HOMOMORPHISM_SUB
       (ASSUME `ring_homomorphism(k,l) (h:A->B)`);
      MATCH_MP RING_HOMOMORPHISM_0 (ASSUME `ring_homomorphism(k,l) (h:A->B)`);
      MATCH_MP RING_HOMOMORPHISM_1 (ASSUME `ring_homomorphism(k,l) (h:A->B)`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < n ==> ring_mul l ((e:num->B) m) d = ring_0 l`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN EXPAND_TAC "d" THEN
    MATCH_MP_TAC RING_DET_DEPENDENT_ROWS_MUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUB THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sub l
        (ring_sum l {i:num | i < n}
           (\i. ring_mul l ((e:num->B) i)
                  (if i = j then ring_1 l else ring_0 l)))
        (ring_sum l {i:num | i < n}
           (\i. ring_mul l ((h:A->B)((f:num->B->A) i (e j))) (e i)))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul r x (ring_sub r d y) =
        ring_sub r (ring_mul r x d) (ring_mul r y (x:B))`) THEN
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REWRITE_RULE[IN_ELIM_THM]
                  (ISPECL [`l:B ring`; `{m:num | m < n}`] RING_SUM_DELTA_MUL);
                 PROJECTIVE_BASIS_EXPAND] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                   `f:num->B->A`; `(e:num->B) j`] PROJECTIVE_BASIS_EXPAND) THEN
    ASM_SIMP_TAC[RING_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[RING_DET]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `ring_mul l (d:B) (ring_1 l)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                 `f:num->B->A`; `ring_1 l:B`] PROJECTIVE_BASIS_EXPAND) THEN
  ASM_REWRITE_TAC[RING_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `!i. i < n ==> (h:A->B)((f:num->B->A) i (ring_1 l)) IN
                              ring_carrier l`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_SUM_LMUL; FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_mul l ((h:A->B)((f:num->B->A) i (ring_1 l)))
               (ring_mul l ((e:num->B) i) d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_mul r d (ring_mul r a x) = ring_mul r a (ring_mul r (x:B) d)`) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[RING_MUL_RZERO]]);;

let ALGEBRA_NORM_INV = prove
 (`!(h:A->B) k l x.
        ring_monomorphism(k,l) h /\ x IN ring_carrier l
        ==> algebra_norm(k,l) h (ring_inv l x) =
            ring_inv k (algebra_norm(k,l) h x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `ring_unit l (x:B)` THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER; GSYM ALGEBRA_NORM_MUL;
                 RING_INV; RING_MUL_RINV; ALGEBRA_NORM_1];
    ALL_TAC] THEN
  ASM_CASES_TAC `?n e f. projective_basis (k,l) (h:A->B) n e f` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; RING_INV_1]] THEN
  SUBGOAL_THEN `ring_inv l x:B = ring_0 l` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[ring_inv]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_inv k (algebra_norm(k,l) (h:A->B) x) = ring_0 k`
  SUBST1_TAC THENL
   [REWRITE_TAC[ring_inv] THEN ASM_MESON_TAC[ALGEBRA_NORM_UNIT_PROJECTIVE];
    MATCH_MP_TAC ALGEBRA_NORM_0_PROJECTIVE THEN ASM_REWRITE_TAC[]]);;

(* Over fields the norm vanishes only at 0.                                  *)
let ALGEBRA_NORM_EQ_0_FREE_BASIS = prove
 (`!(h:A->B) k l n g x.
        field k /\ field l /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ 0 < n /\ x IN ring_carrier l
        ==> (algebra_norm (k,l) h x = ring_0 k <=> x = ring_0 l)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ALGEBRA_NORM_0_FREE_BASIS THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `g:num->B`] THEN ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `ring_inv l x:B`]
    ALGEBRA_NORM_MUL) THEN
  ASM_SIMP_TAC[FIELD_MUL_RINV; RING_INV; ALGEBRA_NORM_1] THEN
  ASM_CASES_TAC `algebra_norm (k,l) (h:A->B) x = ring_0 k` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; ALGEBRA_TRACE_NORM_IN_CARRIER;
               FIELD_NONTRIVIAL]);;

(* ------------------------------------------------------------------------- *)
(* Base change: coordinates, matrices, traces and norms commute with         *)
(* homomorphisms u of the base rings and f of the algebras compatible with   *)
(* the structure maps, when the image f o g of the basis is again a free     *)
(* basis. For projective bases (n,e,f) and (n,v o e,f') the compatibility f' *)
(* i (v y) = u(f i y) of the functionals is assumed instead                  *)
(* (ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE_PROJECTIVE).                        *)
(* ------------------------------------------------------------------------- *)

let BASIS_COORDINATES_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (h':C->D) (u:A->C) (f:B->D) k l k' l' n g y i.
        ring_homomorphism(k,l) h /\ ring_homomorphism(k',l') h' /\
        ring_homomorphism(k,k') u /\ ring_homomorphism(l,l') f /\
        (!a. a IN ring_carrier k ==> f(h a) = h'(u a)) /\
        free_basis (k,l) h n g /\ free_basis (k',l') h' n (f o g) /\
        y IN ring_carrier l
        ==> basis_coordinates (k',l') h' n (f o g) (f y) i =
            u(basis_coordinates (k,l) h n g y i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:B->D) y IN ring_carrier l'` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_CASES_TAC `i:num < n` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[BASIS_COORDINATES_OUTSIDE] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_0]] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `y:B`] BASIS_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = basis_coordinates (k,l) (h:A->B) n g y` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. (h:A->B)((c:num->A) i) IN ring_carrier l /\
        (u:A->C)(c i) IN ring_carrier k'`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':C->D`; `k':C ring`; `l':D ring`; `n:num`;
    `(f:B->D) o (g:num->B)`; `(f:B->D) y`; `(u:A->C) o (c:num->A)`]
    BASIS_COORDINATES_UNIQUE) THEN
  ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) o
    check (fun th -> is_eq(concl th) && rand(concl th) = `y:B`)) THEN
  FIRST_ASSUM((fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
   (MATCH_MP RING_HOMOMORPHISM_SUM th) o rand o snd)) o
    check (fun th -> concl th = `ring_homomorphism(l,l') (f:B->D)`)) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; o_DEF] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM((fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) o
    check (fun th -> concl th = `ring_homomorphism(l,l') (f:B->D)`)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MUL_MATRIX_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (h':C->D) (u:A->C) (f:B->D) k l k' l' n g x i j.
        ring_homomorphism(k,l) h /\ ring_homomorphism(k',l') h' /\
        ring_homomorphism(k,k') u /\ ring_homomorphism(l,l') f /\
        (!a. a IN ring_carrier k ==> f(h a) = h'(u a)) /\
        free_basis (k,l) h n g /\ free_basis (k',l') h' n (f o g) /\
        x IN ring_carrier l /\ j < n
        ==> mul_matrix (k',l') h' n (f o g) (f x) i j =
            u(mul_matrix (k,l) h n g x i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix; o_THM] THEN
  SUBGOAL_THEN `(g:num->B) j IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[FREE_BASIS_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l' ((f:B->D) x) (f((g:num->B) j)) = f(ring_mul l x (g j))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC BASIS_COORDINATES_HOMOMORPHIC_IMAGE THEN
    ASM_SIMP_TAC[RING_MUL]]);;

let ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE_PROJECTIVE = prove
 (`!(h:A->B) (h':C->D) (u:A->C) (v:B->D) k l k' l' n e f f' x.
        ring_homomorphism(k,l) h /\ ring_homomorphism(k',l') h' /\
        ring_homomorphism(k,k') u /\ ring_homomorphism(l,l') v /\
        projective_basis (k,l) h n e f /\
        projective_basis (k',l') h' n (v o e) f' /\
        (!i y. i < n /\ y IN ring_carrier l ==> f' i (v y) = u(f i y)) /\
        x IN ring_carrier l
        ==> algebra_trace(k',l') h' (v x) = u(algebra_trace(k,l) h x) /\
            algebra_norm(k',l') h' (v x) = u(algebra_norm(k,l) h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:B->D) x IN ring_carrier l'` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f:num->B->A`)) THEN
  SUBGOAL_THEN
   `(!j. j < n ==> ring_mul l x ((e:num->B) j) IN ring_carrier l) /\
    (!i j. i < n /\ j < n
           ==> (f:num->B->A) i (ring_mul l x (e j)) IN ring_carrier k /\
               f i (e j) IN ring_carrier k) /\
    (!j. j < n ==> ring_mul l' ((v:B->D) x) (v((e:num->B) j)) =
                   v(ring_mul l x (e j)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MUL] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL o
      check (fun th -> concl th = `ring_homomorphism(l,l') (v:B->D)`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`;
                       `e:num->B`; `f:num->B->A`]
                 ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`;
                       `e:num->B`; `f:num->B->A`]
                 ALGEBRA_NORM_PROJECTIVE_BASIS;
               ISPECL [`h':C->D`; `k':C ring`; `l':D ring`; `n:num`;
                       `(v:B->D) o (e:num->B)`; `f':num->D->C`]
                 ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`h':C->D`; `k':C ring`; `l':D ring`; `n:num`;
                       `(v:B->D) o (e:num->B)`; `f':num->D->C`]
                 ALGEBRA_NORM_PROJECTIVE_BASIS] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`k:A ring`; `k':C ring`; `u:A->C`; `{i:num | i < n}`;
    `\i j. ring_add k ((f:num->B->A) i (ring_mul l x ((e:num->B) j)))
             (ring_sub k (if i = j then ring_1 k else ring_0 k)
                         (f i (e j)))`]
    RING_DET_HOMOMORPHISM) THEN
  MP_TAC(ISPECL
   [`\i. (f:num->B->A) i (ring_mul l x ((e:num->B) i))`; `{i:num | i < n}`]
   (MATCH_MP RING_HOMOMORPHISM_SUM (ASSUME
     `ring_homomorphism(k,k') (u:A->C)`))) THEN
  SUBGOAL_THEN
   `!b. (if b then ring_1 k else ring_0 k) IN ring_carrier(k:A ring)`
  ASSUME_TAC THENL [MESON_TAC[RING_0; RING_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_ADD; RING_SUB; o_DEF] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
    MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RING_ADD; RING_SUB;
      MATCH_MP RING_HOMOMORPHISM_ADD
       (ASSUME `ring_homomorphism(k,k') (u:A->C)`);
      MATCH_MP RING_HOMOMORPHISM_SUB
       (ASSUME `ring_homomorphism(k,k') (u:A->C)`)] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[RING_HOMOMORPHISM_0;
                                      RING_HOMOMORPHISM_1]]);;

let ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (h':C->D) (u:A->C) (f:B->D) k l k' l' n g x.
        ring_homomorphism(k,l) h /\ ring_homomorphism(k',l') h' /\
        ring_homomorphism(k,k') u /\ ring_homomorphism(l,l') f /\
        (!a. a IN ring_carrier k ==> f(h a) = h'(u a)) /\
        free_basis (k,l) h n g /\ free_basis (k',l') h' n (f o g) /\
        x IN ring_carrier l
        ==> algebra_trace(k',l') h' (f x) = u(algebra_trace(k,l) h x) /\
            algebra_norm(k',l') h' (f x) = u(algebra_norm(k,l) h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE_PROJECTIVE THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `g:num->B`;
    `\i z. basis_coordinates (k,l) (h:A->B) n g z i`;
    `\i z. basis_coordinates (k',l') (h':C->D) n ((f:B->D) o g) z i`] THEN
  ASM_SIMP_TAC[FREE_BASIS_PROJECTIVE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BASIS_COORDINATES_HOMOMORPHIC_IMAGE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cayley-Hamilton for multiplication matrices: x is a root of the           *)
(* characteristic polynomial of its matrix in a free basis (any commutative  *)
(* rings). The basis g is a null vector of x I - M from the left, so the     *)
(* adjugate gives det(x I - M) g m = 0 for all m, and 1 is a combination     *)
(* of the g m.                                                               *)
(* ------------------------------------------------------------------------- *)

let MUL_MATRIX_CHARPOLY_ROOT = prove
 (`!(h:A->B) k l n g x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l
        ==> poly_extend (k,l) h (\v. x)
             (ring_charpoly k {i | i < n} (mul_matrix (k,l) h n g x)) =
            ring_0 l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_CHARPOLY_EXTEND o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MUL_MATRIX_IN_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC
   `q = \i j. ring_sub l (if i = j then x else ring_0 l)
                         ((h:A->B)(mul_matrix (k,l) h n g x i j))` THEN
  SUBGOAL_THEN `!i j. j < n ==> (q:num->num->B) i j IN ring_carrier l`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUB THEN
    ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
    ALL_TAC] THEN
  ABBREV_TAC `d = ring_det l {i:num | i < n} (q:num->num->B)` THEN
  SUBGOAL_THEN `(d:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[RING_DET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n
        ==> ring_sum l {i:num | i < n}
              (\i. ring_mul l ((q:num->num->B) i j) ((g:num->B) i)) =
            ring_0 l`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "q" THEN
    TRANS_TAC EQ_TRANS
     `ring_sub l
       (ring_sum l {i:num | i < n}
         (\i. ring_mul l (if i = j then x else ring_0 l) ((g:num->B) i)))
       (ring_sum l {i:num | i < n}
         (\i. ring_mul l ((h:A->B)(mul_matrix (k,l) h n g x i j)) (g i)))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL;
                     MUL_MATRIX_IN_CARRIER] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN
        ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC RING_SUB_RDISTRIB THEN
      ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MUL_MATRIX_EXPAND] THEN
    TRANS_TAC EQ_TRANS `ring_sub l (ring_mul l x ((g:num->B) j))
                                   (ring_mul l x (g j))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[RING_SUB_REFL; RING_MUL]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l {i:num | i < n}
        (\i. if i = j then ring_mul l x ((g:num->B) j) else ring_0 l)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num = j` THEN ASM_SIMP_TAC[RING_MUL_LZERO];
      ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; RING_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < n ==> ring_mul l d ((g:num->B) m) = ring_0 l`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `ring_mul l ((g:num->B) m) d` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[]; EXPAND_TAC "d"] THEN
    MATCH_MP_TAC RING_DET_DEPENDENT_ROWS_MUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
     [SYM(MATCH_MP th (ASSUME `j:num < n`))]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `ring_1 l:B`] BASIS_COORDINATES_EXPAND) THEN
  ASM_REWRITE_TAC[RING_1] THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `ring_mul l (d:B) (ring_1 l)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
    check (fun th -> is_eq(concl th) && rand(concl th) = `ring_1 l:B`)) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL;
                 BASIS_COORDINATES_IN_CARRIER; RING_1];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_mul l ((h:A->B)(basis_coordinates (k,l) h n g (ring_1 l) m))
               (ring_mul l d ((g:num->B) m))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_AC; BASIS_COORDINATES_IN_CARRIER; RING_1];
    ASM_SIMP_TAC[RING_MUL_RZERO; BASIS_COORDINATES_IN_CARRIER; RING_1]]);;

(* ------------------------------------------------------------------------- *)
(* Towers of free extensions. For free bases b of l over k (via f, size p)   *)
(* and c of m over l (via g, size q), the products g(b i) c j, indexed by    *)
(* t = i + p * j < p * q, form a free basis of m over k (FREE_BASIS_TRANS),  *)
(* the coordinates in it are iterated coordinates, and the matrix of g y,    *)
(* y in l, is the Kronecker product of the matrix of y with the identity of  *)
(* size q (MUL_MATRIX_TRANS).                                                *)
(* ------------------------------------------------------------------------- *)

let RING_SUM_MOD_DIV = prove
 (`!(r:A ring) m n (f:num->num->A).
        (!i j. i < m /\ j < n ==> f i j IN ring_carrier r)
        ==> ring_sum r {t | t < m * n} (\t. f (t MOD m) (t DIV m)) =
            ring_sum r {j | j < n} (\j. ring_sum r {i | i < m} (\i. f i j))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:num = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC;
                    RING_SUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t:num | t < m * n} =
    IMAGE (\x. SND x + m * FST x) ({j:num | j < n} CROSS {i:num | i < m})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
                IN_ELIM_THM] THEN
    X_GEN_TAC `t:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`t DIV m`; `t MOD m`] THEN
      ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ] THEN
      MP_TAC(SPECL [`t:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `i:num`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `m + m * j:num` THEN
      ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `m + m * j:num = m * (j + 1)`;
                  LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\t. t MOD m, t DIV m` (CONJUNCT2(CONJUNCT2 th))) THEN
      STRIP_ASSUME_TAC th) THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES;
                 PAIR_EQ] THEN
    MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`r:A ring`; `{j:num | j < n}`;
    `\j:num. {i:num | i < m}`; `\j i. (f:num->num->A) i j`]
    RING_SUM_SUM_PRODUCT)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM CROSS] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; o_THM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

let FREE_BASIS_TRANS,BASIS_COORDINATES_TRANS =
  let lemma0 = prove
   (`!(f:A->B) (g:B->C) k l m p q b c a.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        (!i. i < p ==> b i IN ring_carrier l) /\
        (!j. j < q ==> c j IN ring_carrier m) /\
        (!t. t < p * q ==> a t IN ring_carrier k)
        ==> ring_sum m {t | t < p * q}
              (\t. ring_mul m ((g o f) (a t))
                     (ring_mul m (g(b(t MOD p))) (c(t DIV p)))) =
            ring_sum m {j | j < q}
              (\j. ring_mul m
                    (g(ring_sum l {i | i < p}
                         (\i. ring_mul l (f(a(i + p * j))) (b i))))
                    (c j))`,
    REPEAT STRIP_TAC THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o
      REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
      GEN_REWRITE_RULE I [ring_homomorphism] o
      check (fun th -> rand(concl th) = t))) [`f:A->B`; `g:B->C`] THEN
    SUBGOAL_THEN
     `!i j. i < p /\ j < q ==> (a:num->A)(i + p * j) IN ring_carrier k`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      TRANS_TAC LTE_TRANS `p + p * j:num` THEN
      ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `p + p * j:num = p * (j + 1)`;
                  LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!i j. i < p /\ j < q
             ==> (f:A->B)((a:num->A)(i + p * j)) IN ring_carrier l) /\
      (!i j. i < p /\ j < q
             ==> (g:B->C)((f:A->B)((a:num->A)(i + p * j))) IN
                 ring_carrier m) /\
      (!i. i < p ==> (g:B->C)((b:num->B) i) IN ring_carrier m)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `p:num = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC;
                      RING_SUM_CLAUSES] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[RING_MUL_LZERO];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum m {t | t < p * q}
        (\t. ring_mul m (((g:B->C) o (f:A->B))
                          ((a:num->A)(t MOD p + p * t DIV p)))
                        (ring_mul m (g((b:num->B)(t MOD p)))
                                    ((c:num->C)(t DIV p))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `t MOD p + p * t DIV p = t` (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`t:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`m:C ring`; `p:num`; `q:num`;
      `\i j. ring_mul m (((g:B->C) o (f:A->B)) ((a:num->A)(i + p * j)))
                        (ring_mul m (g((b:num->B) i)) ((c:num->C) j))`]
     RING_SUM_MOD_DIV)) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      REPEAT(MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\i. ring_mul l ((f:A->B)((a:num->A)(i + p * j))) ((b:num->B) i)`;
      `{i:num | i < p}`]
     (MATCH_MP RING_HOMOMORPHISM_SUM
       (ASSUME `ring_homomorphism(l,m) (g:B->C)`))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; o_THM];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL]) in
  let lemma1 = prove
   (`!(f:A->B) (g:B->C) k l m p q b c w.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (l,m) g q c /\
        w IN ring_carrier m
        ==> ring_sum m {t | t < p * q}
              (\t. ring_mul m
                    ((g o f) (basis_coordinates (k,l) f p b
                               (basis_coordinates (l,m) g q c w (t DIV p))
                               (t MOD p)))
                    (ring_mul m (g(b(t MOD p))) (c(t DIV p)))) = w`,
    REPEAT STRIP_TAC THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o
      MATCH_MP FREE_BASIS_IN_CARRIER o
      check (fun th -> rand(concl th) = t))) [`b:num->B`; `c:num->C`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) lemma0 o lhand o snd) THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `q:num`; `c:num->C`;
                   `w:C`] BASIS_COORDINATES_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `p:num`; `b:num->B`;
                   `basis_coordinates (l,m) (g:B->C) q c w j`]
      BASIS_COORDINATES_EXPAND) THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]) in
  let FREE_BASIS_TRANS = prove
   (`!(f:A->B) (g:B->C) k l m p q b c.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (l,m) g q c
        ==> free_basis (k,m) (g o f) (p * q)
             (\t. ring_mul m (g(b(t MOD p))) (c(t DIV p)))`,
    REPEAT STRIP_TAC THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o
      MATCH_MP FREE_BASIS_IN_CARRIER o
      check (fun th -> rand(concl th) = t))) [`b:num->B`; `c:num->C`] THEN
    REWRITE_TAC[free_basis] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC RING_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
        EXISTS_TAC `l:B ring` THEN ASM_SIMP_TAC[MOD_LT_EQ];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ]];
      X_GEN_TAC `w:C` THEN DISCH_TAC THEN
      EXISTS_TAC
       `\t. basis_coordinates (k,l) (f:A->B) p b
              (basis_coordinates (l,m) (g:B->C) q c w (t DIV p)) (t MOD p)` THEN
      ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `a:num->A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                     `p:num`; `q:num`; `b:num->B`; `c:num->C`; `a:num->A`]
        lemma0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `!i j. i < p /\ j < q ==> (a:num->A)(i + p * j) IN ring_carrier k`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        TRANS_TAC LTE_TRANS `p + p * j:num` THEN
        ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
        REWRITE_TAC[ARITH_RULE `p + p * j:num = p * (j + 1)`;
                    LE_MULT_LCANCEL] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!j. j < q
            ==> ring_sum l {i:num | i < p}
                  (\i. ring_mul l ((f:A->B)(a(i + p * j))) ((b:num->B) i)) =
                ring_0 l`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `q:num`; `c:num->C`;
          `\j. ring_sum l {i:num | i < p}
                 (\i. ring_mul l ((f:A->B)((a:num->A)(i + p * j)))
                                 ((b:num->B) i))`] FREE_BASIS_INDEPENDENT) THEN
        ASM_REWRITE_TAC[RING_SUM] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          is_eq(concl th) && is_comb(lhand(concl th)))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`t:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      ONCE_REWRITE_TAC[ARITH_RULE
       `t DIV p * p + t MOD p = t MOD p + p * t DIV p`] THEN
      MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `p:num`; `b:num->B`;
                     `\i. (a:num->A)(i + p * t DIV p)`]
        FREE_BASIS_INDEPENDENT) THEN
      ASM_SIMP_TAC[RDIV_LT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]) in
  FREE_BASIS_TRANS,
  prove
   (`!(f:A->B) (g:B->C) k l m p q b c w t.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (l,m) g q c /\
        w IN ring_carrier m /\ t < p * q
        ==> basis_coordinates (k,m) (g o f) (p * q)
              (\t. ring_mul m (g(b(t MOD p))) (c(t DIV p))) w t =
            basis_coordinates (k,l) f p b
              (basis_coordinates (l,m) g q c w (t DIV p)) (t MOD p)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`;
      `p * q:num`; `\t. ring_mul m ((g:B->C)((b:num->B)(t MOD p)))
                                  ((c:num->C)(t DIV p))`;
      `w:C`;
      `\t. basis_coordinates (k,l) (f:A->B) p b
              (basis_coordinates (l,m) (g:B->C) q c w (t DIV p)) (t MOD p)`]
     BASIS_COORDINATES_UNIQUE)) THEN
    ANTS_TAC THENL
     [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FREE_BASIS_TRANS THEN EXISTS_TAC `l:B ring` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER];
      MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[]]);;

let MUL_MATRIX_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m p q b c y t u.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (l,m) g q c /\
        y IN ring_carrier l /\ t < p * q /\ u < p * q
        ==> mul_matrix (k,m) (g o f) (p * q)
              (\t. ring_mul m (g(b(t MOD p))) (c(t DIV p))) (g y) t u =
            ring_mul k (mul_matrix (k,l) f p b y (t MOD p) (u MOD p))
                       (if t DIV p = u DIV p then ring_1 k else ring_0 k)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = t))) [`b:num->B`; `c:num->C`] THEN
  SUBGOAL_THEN `~(p:num = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t MOD p < p /\ u MOD p < p /\ t DIV p < q /\ u DIV p < q`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:B->C) y IN ring_carrier m /\
    ring_mul l y ((b:num->B)(u MOD p)) IN ring_carrier l /\
    (g:B->C)((b:num->B)(u MOD p)) IN ring_carrier m /\
    (g:B->C)(ring_mul l y ((b:num->B)(u MOD p))) IN ring_carrier m`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MUL]; ALL_TAC] THEN
  REWRITE_TAC[mul_matrix] THEN
  SUBGOAL_THEN
   `ring_mul m ((g:B->C) y)
      (ring_mul m (g((b:num->B)(u MOD p))) ((c:num->C)(u DIV p))) =
    ring_mul m (g(ring_mul l y (b(u MOD p)))) (c(u DIV p))`
  SUBST1_TAC THENL
   [FIRST_ASSUM((fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) o
     check (fun th -> concl th = `ring_homomorphism(l,m) (g:B->C)`)) THEN
    MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
    `p:num`; `q:num`; `b:num->B`; `c:num->C`;
    `ring_mul m ((g:B->C)(ring_mul l y ((b:num->B)(u MOD p))))
                ((c:num->C)(u DIV p))`; `t:num`] BASIS_COORDINATES_TRANS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[BASIS_COORDINATES_LMUL; BASIS_COORDINATES_BASIS] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO; BASIS_COORDINATES_0;
               BASIS_COORDINATES_IN_CARRIER]);;

let ALGEBRA_TRACE_NORM_INTERMEDIATE_FREE_BASIS = prove
 (`!(f:A->B) (g:B->C) k l m p q b c y.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (l,m) g q c /\
        y IN ring_carrier l
        ==> algebra_trace(k,m) (g o f) (g y) =
            ring_mul k (ring_of_num k q) (algebra_trace(k,l) f y) /\
            algebra_norm(k,m) (g o f) (g y) =
            ring_pow k (algebra_norm(k,l) f y) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,m) ((g:B->C) o (f:A->B)) /\
    free_basis (k,m) (g o f) (p * q)
      (\t. ring_mul m (g((b:num->B)(t MOD p))) ((c:num->C)(t DIV p))) /\
    g y IN ring_carrier m`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FREE_BASIS_TRANS THEN EXISTS_TAC `l:B ring` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `p:num`; `b:num->B`]
                 ALGEBRA_TRACE_FREE_BASIS;
               ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `p:num`; `b:num->B`]
                 ALGEBRA_NORM_FREE_BASIS;
               ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`;
                       `p * q:num`;
                       `\t. ring_mul m ((g:B->C)((b:num->B)(t MOD p)))
                                       ((c:num->C)(t DIV p))`]
                 ALGEBRA_TRACE_FREE_BASIS;
               ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`;
                       `p * q:num`;
                       `\t. ring_mul m ((g:B->C)((b:num->B)(t MOD p)))
                                       ((c:num->C)(t DIV p))`]
                 ALGEBRA_NORM_FREE_BASIS] THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_sum k {t:num | t < p * q}
        (\t. mul_matrix (k,l) (f:A->B) p b y (t MOD p) (t MOD p))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MUL_MATRIX_TRANS] THEN
      MATCH_MP_TAC RING_MUL_RID THEN MATCH_MP_TAC MUL_MATRIX_IN_CARRIER THEN
      ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`k:A ring`; `p:num`; `q:num`;
      `\i j:num. mul_matrix (k,l) (f:A->B) p b y i i`] RING_SUM_MOD_DIV)) THEN
    ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[RING_SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; RING_SUM];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_det k {t:num | t < p * q}
      (\t u. ring_mul k
              (mul_matrix (k,l) (f:A->B) p b y (t MOD p) (u MOD p))
              (if t DIV p = u DIV p then ring_1 k else ring_0 k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MUL_MATRIX_TRANS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`; `q:num`;
                 `mul_matrix (k,l) (f:A->B) p b y`;
                 `\i j:num. if i = j then ring_1 k else ring_0(k:A ring)`]
    RING_DET_KRONECKER_MOD_DIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[RING_DET_I; FINITE_NUMSEG_LT; RING_POW_ONE] THEN
  MATCH_MP_TAC RING_MUL_RID THEN SIMP_TAC[RING_POW; RING_DET]);;

let MUL_MATRIX_CHARPOLY_INTERMEDIATE =
  let lemma = prove
   (`!p t u. ~(p = 0)
             ==> (t = u <=> t MOD p = u MOD p /\ t DIV p = u DIV p)`,
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`t:num`; `p:num`] DIVISION) THEN
    MP_TAC(SPECL [`u:num`; `p:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]) in
  prove
 (`!(f:A->B) (g:B->C) k l m p q b c y.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (l,m) g q c /\
        y IN ring_carrier l
        ==> ring_charpoly k {t | t < p * q}
              (mul_matrix (k,m) (g o f) (p * q)
                (\t. ring_mul m (g(b(t MOD p))) (c(t DIV p))) (g y)) =
            poly_pow k (ring_charpoly k {i | i < p} (mul_matrix (k,l) f p b y))
                     q`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p:num = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; ring_charpoly;
                    RING_DET_EMPTY] THEN
    SUBGOAL_THEN
     `poly_pow k (ring_1(poly_ring k (:1))) q =
      ring_pow (poly_ring (k:A ring) (:1)) (ring_1(poly_ring k (:1))) q`
    SUBST1_TAC THENL [REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
    REWRITE_TAC[RING_POW_ONE];
    ALL_TAC] THEN
  REWRITE_TAC[ring_charpoly] THEN
  TRANS_TAC EQ_TRANS
   `ring_det (poly_ring k (:1)) {t:num | t < p * q}
     (\t u. ring_mul (poly_ring k (:1))
             (poly_sub k (if t MOD p = u MOD p then poly_var k one
                          else poly_0 k)
               (poly_const k
                 (mul_matrix (k,l) (f:A->B) p b y (t MOD p) (u MOD p))))
             (if t DIV p = u DIV p then ring_1(poly_ring k (:1))
              else ring_0(poly_ring k (:1))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:num`; `u:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MUL_MATRIX_TRANS] THEN
    SUBGOAL_THEN
     `mul_matrix (k,l) (f:A->B) p b y (t MOD p) (u MOD p) IN ring_carrier k`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MUL_MATRIX_IN_CARRIER THEN ASM_REWRITE_TAC[MOD_LT_EQ];
      ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `t:num`; `u:num`] lemma) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `t DIV p = u DIV p` THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO; POLY_CONST_0] THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_MUL_RID THEN
      MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_CONST;
                   RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0];
      MATCH_MP_TAC(MESON[]
       `(a:(1->num)->A) = poly_0 k /\ b = poly_0 k ==> a = b`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES));
                    GSYM(el 5 (CONJUNCTS POLY_RING_CLAUSES))] THEN
        MATCH_MP_TAC RING_SUB_REFL THEN REWRITE_TAC[RING_0];
        MATCH_MP_TAC(CONJUNCT1 POLY_MUL_0) THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_CONST;
                     RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0]]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`poly_ring (k:A ring) (:1)`; `p:num`; `q:num`;
    `\i j:num. poly_sub k (if i = j then poly_var k one else poly_0 k)
                (poly_const k (mul_matrix (k,l) (f:A->B) p b y i j))`;
    `\i j:num. if i = j then ring_1(poly_ring (k:A ring) (:1))
               else ring_0(poly_ring k (:1))`] RING_DET_KRONECKER_MOD_DIV)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1] THEN
    ASM_SIMP_TAC[POLY_RING_CLAUSES; IN_ELIM_THM; SUBSET_UNIV;
                 RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_CONST;
                 RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0;
                 MUL_MATRIX_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[RING_DET_I; FINITE_NUMSEG_LT; RING_POW_ONE] THEN
  SIMP_TAC[RING_MUL_RID; RING_POW; RING_DET] THEN
  REWRITE_TAC[POLY_RING_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Towers of projective extensions. For projective bases (p,b,u) of l over k *)
(* (via f) and (q,c,w) of m over l (via g), the products g(b i) c j with the *)
(* functionals u i o w j, indexed by t = i + p * j < p * q, form a           *)
(* projective basis of m over k (PROJECTIVE_BASIS_TRANS), and the trace of m *)
(* over k is the trace over k of the trace of m over l                       *)
(* (ALGEBRA_TRACE_TOWER_PROJECTIVE).                                         *)
(* ------------------------------------------------------------------------- *)

let PROJECTIVE_BASIS_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m p q b c u w.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        projective_basis (k,l) f p b u /\ projective_basis (l,m) g q c w
        ==> projective_basis (k,m) (g o f) (p * q)
              (\t. ring_mul m (g(b(t MOD p))) (c(t DIV p)))
              (\t z. u (t MOD p) (w (t DIV p) z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `u:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `w:num->C->B`)) THEN
  SUBGOAL_THEN `!t. t < p * q ==> t MOD p < p /\ t DIV p < q` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
    ASM_SIMP_TAC[MULT_CLAUSES; CONJUNCT1 LT; MOD_LT_EQ; RDIV_LT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!a. a IN ring_carrier k ==> (f:A->B) a IN ring_carrier l) /\
    (!a. a IN ring_carrier l ==> (g:B->C) a IN ring_carrier m)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i < p ==> (g:B->C)((b:num->B) i) IN ring_carrier m)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[projective_basis; o_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_MUL];
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_ADD
                  (ASSUME `projective_basis (l,m) (g:B->C) q c w`)] THEN
    ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_ADD
                  (ASSUME `projective_basis (k,l) (f:A->B) p b u`)];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_LMUL
                  (ASSUME `projective_basis (l,m) (g:B->C) q c w`)] THEN
    ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_LMUL
                  (ASSUME `projective_basis (k,l) (f:A->B) p b u`)];
    X_GEN_TAC `z:C` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(!j. j < q ==> (w:num->C->B) j z IN ring_carrier l) /\
    (!i j. i < p /\ j < q ==> (u:num->B->A) i (w j z) IN ring_carrier k)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < p /\ j < q
          ==> (f:A->B)((u:num->B->A) i ((w:num->C->B) j z)) IN
              ring_carrier l /\
              ring_mul m ((g:B->C)((b:num->B) i)) ((c:num->C) j) IN
              ring_carrier m`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < p /\ j < q
          ==> (g:B->C)((f:A->B)((u:num->B->A) i ((w:num->C->B) j z))) IN
              ring_carrier m /\
              ring_mul l (f(u i (w j z))) ((b:num->B) i) IN ring_carrier l`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < p /\ j < q
          ==> (g:B->C)(ring_mul l ((f:A->B)((u:num->B->A) i
                                     ((w:num->C->B) j z))) ((b:num->B) i)) IN
              ring_carrier m`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `p:num`; `q:num`;
    `\i j. ring_mul m ((g:B->C)((f:A->B)((u:num->B->A) i
                                   ((w:num->C->B) j z))))
                      (ring_mul m (g((b:num->B) i)) ((c:num->C) j))`]
    RING_SUM_MOD_DIV) THEN
  ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `q:num`; `c:num->C`;
                 `w:num->C->B`; `z:C`] PROJECTIVE_BASIS_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `p:num`; `b:num->B`;
                 `u:num->B->A`; `(w:num->C->B) j z`]
    PROJECTIVE_BASIS_EXPAND) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
    [SYM th]) THEN
  MP_TAC(ISPECL
   [`\i. ring_mul l ((f:A->B)((u:num->B->A) i ((w:num->C->B) j z)))
                    ((b:num->B) i)`; `{i:num | i < p}`]
   (MATCH_MP RING_HOMOMORPHISM_SUM (ASSUME
     `ring_homomorphism(l,m) (g:B->C)`))) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; o_DEF] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                (ASSUME `ring_homomorphism(l,m) (g:B->C)`); RING_MUL] THEN
  MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC[]);;

let ALGEBRA_TRACE_TOWER_PROJECTIVE = prove
 (`!(f:A->B) (g:B->C) k l m z.
        ring_homomorphism(k,l) f /\ ring_homomorphism(l,m) g /\
        (?p b u. projective_basis (k,l) f p b u) /\
        (?q c w. projective_basis (l,m) g q c w) /\
        z IN ring_carrier m
        ==> algebra_trace(k,m) (g o f) z =
            algebra_trace(k,l) f (algebra_trace(l,m) g z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `b:num->B`
       (X_CHOOSE_TAC `u:num->B->A`)))
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `c:num->C`
         (X_CHOOSE_TAC `w:num->C->B`))) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `ring_homomorphism(k,m) ((g:B->C) o (f:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `p:num`; `q:num`; `b:num->B`; `c:num->C`; `u:num->B->A`;
                 `w:num->C->B`] PROJECTIVE_BASIS_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `u:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `w:num->C->B`)) THEN
  SUBGOAL_THEN
   `(!i. i < p ==> (g:B->C)((b:num->B) i) IN ring_carrier m) /\
    (!j. j < q ==> ring_mul m z ((c:num->C) j) IN ring_carrier m) /\
    algebra_trace(l,m) g z IN ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. j < q ==> (w:num->C->B) j (ring_mul m z ((c:num->C) j)) IN
                   ring_carrier l) /\
    (!i j. i < p /\ j < q
           ==> ring_mul m z (ring_mul m ((g:B->C)((b:num->B) i)) (c j)) IN
               ring_carrier m)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. i < p /\ j < q
           ==> ring_mul l ((b:num->B) i)
                 ((w:num->C->B) j (ring_mul m z ((c:num->C) j))) IN
               ring_carrier l) /\
    (!i j. i < p /\ j < q
           ==> w j (ring_mul m z (ring_mul m ((g:B->C)(b i)) (c j))) IN
               ring_carrier l)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. i < p /\ j < q
           ==> (u:num->B->A) i
                 (ring_mul l ((b:num->B) i)
                    ((w:num->C->B) j (ring_mul m z ((c:num->C) j)))) IN
               ring_carrier k) /\
    (!i j. i < p /\ j < q
           ==> u i (w j (ring_mul m z (ring_mul m ((g:B->C)(b i)) (c j)))) IN
               ring_carrier k)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`; `p * q:num`;
                 `\t. ring_mul m ((g:B->C)((b:num->B)(t MOD p)))
                                 ((c:num->C)(t DIV p))`;
                 `\t z. (u:num->B->A) (t MOD p) ((w:num->C->B) (t DIV p) z)`;
                 `z:C`] ALGEBRA_TRACE_PROJECTIVE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `p:num`; `b:num->B`;
                       `u:num->B->A`] ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `q:num`; `c:num->C`;
                       `w:num->C->B`] ALGEBRA_TRACE_PROJECTIVE_BASIS] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`; `q:num`;
    `\i j. (u:num->B->A) i ((w:num->C->B) j
             (ring_mul m z (ring_mul m ((g:B->C)((b:num->B) i))
                                      ((c:num->C) j))))`]
    RING_SUM_MOD_DIV) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum k {j:num | j < q}
      (\j. ring_sum k {i:num | i < p}
         (\i. (u:num->B->A) i
                (ring_mul l ((b:num->B) i)
                   ((w:num->C->B) j (ring_mul m z ((c:num->C) j))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `ring_mul m z (ring_mul m ((g:B->C)((b:num->B) i)) ((c:num->C) j)) =
      ring_mul m (g(b i)) (ring_mul m z (c j))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r z (ring_mul r y x) = ring_mul r y (ring_mul r z (x:C))`) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_LMUL
                    (ASSUME `projective_basis (l,m) (g:B->C) q c w`)]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`i:num`; `{j:num | j < q}`;
    `\j. ring_mul l ((b:num->B) i)
                    ((w:num->C->B) j (ring_mul m z ((c:num->C) j)))`]
    (MATCH_MP PROJECTIVE_BASIS_RING_SUM
      (ASSUME `projective_basis (k,l) (f:A->B) p b u`))) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[RING_SUM_LMUL; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Products of algebras. Finite projective bases of l1 and l2 over k give    *)
(* one of prod_ring l1 l2 over k via a |-> (h1 a,h2 a), with the functionals *)
(* of l1 on the first component followed by those of l2 on the second        *)
(* (PROJECTIVE_BASIS_PROD_RING). The array of (x1,x2) is block diagonal, so  *)
(* its trace is the sum and its norm the product of those of x1 and x2       *)
(* (ALGEBRA_TRACE_NORM_PROD_RING).                                           *)
(* ------------------------------------------------------------------------- *)

let PROJECTIVE_BASIS_PROD_RING = prove
 (`!(h1:A->B) (h2:A->C) k l1 l2 n1 n2 e1 e2 f1 f2.
        ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
        projective_basis (k,l1) h1 n1 e1 f1 /\
        projective_basis (k,l2) h2 n2 e2 f2
        ==> projective_basis (k,prod_ring l1 l2) (\a. h1 a,h2 a) (n1 + n2)
              (\i. if i < n1 then e1 i,ring_0 l2 else ring_0 l1,e2(i - n1))
              (\i x. if i < n1 then f1 i (FST x) else f2 (i - n1) (SND x))`,
  let lemma = prove
   (`!(r:A ring) (r':B ring) (s:K->bool) (f:K->A) (g:K->B).
        FINITE s /\
        (!i. i IN s ==> f i IN ring_carrier r /\ g i IN ring_carrier r')
        ==> ring_sum (prod_ring r r') s (\i. f i,g i) =
            ring_sum r s f,ring_sum r' s g`,
    GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[RING_SUM_CLAUSES; PROD_RING; FORALL_IN_INSERT; IN_CROSS] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f1:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f2:num->C->A`)) THEN
  SUBGOAL_THEN `!i:num. i < n1 + n2 /\ ~(i < n1) ==> i - n1 < n2`
  ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[projective_basis; PROD_RING; FORALL_PAIR_THM; IN_CROSS] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; IN_CROSS];
    REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_ADD
                  (ASSUME `projective_basis (k,l1) (h1:A->B) n1 e1 f1`);
                 MATCH_MP PROJECTIVE_BASIS_ADD
                  (ASSUME `projective_basis (k,l2) (h2:A->C) n2 e2 f2`)];
    REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[MATCH_MP PROJECTIVE_BASIS_LMUL
                  (ASSUME `projective_basis (k,l1) (h1:A->B) n1 e1 f1`);
                 MATCH_MP PROJECTIVE_BASIS_LMUL
                  (ASSUME `projective_basis (k,l2) (h2:A->C) n2 e2 f2`)];
    MAP_EVERY X_GEN_TAC [`x1:B`; `x2:C`] THEN STRIP_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (prod_ring l1 l2) {i:num | i < n1 + n2}
      (\i. (if i < n1 then ring_mul l1 ((h1:A->B)((f1:num->B->A) i x1))
                                    ((e1:num->B) i)
            else ring_0 l1),
           (if ~(i < n1)
            then ring_mul l2 ((h2:A->C)((f2:num->C->A) (i - n1) x2))
                             ((e2:num->C) (i - n1))
            else ring_0 l2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[PAIR_EQ] THEN MATCH_MP_TAC RING_MUL_RZERO THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[RING_0] THEN MATCH_MP_TAC RING_MUL THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET; PAIR_EQ] THEN
  SUBGOAL_THEN
   `{i:num | i IN {i | i < n1 + n2} /\ i < n1} = {i | i < n1} /\
    {i:num | i IN {i | i < n1 + n2} /\ ~(i < n1)} =
    IMAGE (\j. j + n1) {j | j < n2}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN CONJ_TAC THEN
    GEN_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    EQ_TAC THENL [DISCH_TAC THEN EXISTS_TAC `x - n1:num`; STRIP_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[RING_SUM_IMAGE; EQ_ADD_RCANCEL; o_DEF; ADD_SUB] THEN
  MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`; `e1:num->B`;
                 `f1:num->B->A`; `x1:B`] PROJECTIVE_BASIS_EXPAND) THEN
  MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`; `e2:num->C`;
                 `f2:num->C->A`; `x2:C`] PROJECTIVE_BASIS_EXPAND) THEN
  ASM_SIMP_TAC[]);;

let ALGEBRA_TRACE_NORM_PROD_RING = prove
 (`!(h1:A->B) (h2:A->C) k l1 l2 x1 x2.
        ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
        (?n e f. projective_basis (k,l1) h1 n e f) /\
        (?n e f. projective_basis (k,l2) h2 n e f) /\
        x1 IN ring_carrier l1 /\ x2 IN ring_carrier l2
        ==> algebra_trace(k,prod_ring l1 l2) (\a. h1 a,h2 a) (x1,x2) =
            ring_add k (algebra_trace(k,l1) h1 x1)
                       (algebra_trace(k,l2) h2 x2) /\
            algebra_norm(k,prod_ring l1 l2) (\a. h1 a,h2 a) (x1,x2) =
            ring_mul k (algebra_norm(k,l1) h1 x1)
                       (algebra_norm(k,l2) h2 x2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `e1:num->B`
       (X_CHOOSE_TAC `f1:num->B->A`)))
     (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `e2:num->C`
         (X_CHOOSE_TAC `f2:num->C->A`))) STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`h1:A->B`; `h2:A->C`; `k:A ring`; `l1:B ring`; `l2:C ring`;
                 `n1:num`; `n2:num`; `e1:num->B`; `e2:num->C`;
                 `f1:num->B->A`; `f2:num->C->A`]
    PROJECTIVE_BASIS_PROD_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,prod_ring l1 l2) (\a. (h1:A->B) a,(h2:A->C) a)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[RING_HOMOMORPHISM_PAIRED]; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:B,x2:C) IN ring_carrier(prod_ring l1 l2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PROD_RING; IN_CROSS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\a. (h1:A->B) a,(h2:A->C) a`; `k:A ring`;
    `prod_ring (l1:B ring) (l2:C ring)`; `n1 + n2:num`;
    `\i. if i < n1 then (e1:num->B) i,ring_0 l2
         else ring_0 l1,(e2:num->C)(i - n1)`;
    `\i x. if i < n1 then (f1:num->B->A) i (FST x)
           else (f2:num->C->A) (i - n1) (SND x)`;
    `x1:B,x2:C`] ALGEBRA_NORM_PROJECTIVE_BASIS) THEN
  MP_TAC(ISPECL [`\a. (h1:A->B) a,(h2:A->C) a`; `k:A ring`;
    `prod_ring (l1:B ring) (l2:C ring)`; `n1 + n2:num`;
    `\i. if i < n1 then (e1:num->B) i,ring_0 l2
         else ring_0 l1,(e2:num->C)(i - n1)`;
    `\i x. if i < n1 then (f1:num->B->A) i (FST x)
           else (f2:num->C->A) (i - n1) (SND x)`;
    `x1:B,x2:C`] ALGEBRA_TRACE_PROJECTIVE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`;
                       `e1:num->B`; `f1:num->B->A`]
                 ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`;
                       `e1:num->B`; `f1:num->B->A`]
                 ALGEBRA_NORM_PROJECTIVE_BASIS;
               ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`;
                       `e2:num->C`; `f2:num->C->A`]
                 ALGEBRA_TRACE_PROJECTIVE_BASIS;
               ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`;
                       `e2:num->C`; `f2:num->C->A`]
                 ALGEBRA_NORM_PROJECTIVE_BASIS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f1:num->B->A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER o
    check (fun th -> rand(concl th) = `f2:num->C->A`)) THEN
  SUBGOAL_THEN
   `(!i. i < n1 ==> (f1:num->B->A) i (ring_0 l1) = ring_0 k) /\
    (!i. i < n2 ==> (f2:num->C->A) i (ring_0 l2) = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PROJECTIVE_BASIS_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{i:num | i < n1 + n2} =
    {i | i < n1} UNION IMAGE (\j. j + n1) {j | j < n2} /\
    DISJOINT {i:num | i < n1} (IMAGE (\j. j + n1) {j | j < n2})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; DISJOINT; IN_UNION; IN_INTER; IN_IMAGE;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN GEN_TAC THENL
     [EQ_TAC THENL
       [DISCH_TAC THEN ASM_CASES_TAC `x:num < n1` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `x - n1:num` THEN ASM_ARITH_TAC;
        STRIP_TAC THEN ASM_ARITH_TAC];
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i < n1 ==> ring_mul l1 x1 ((e1:num->B) i) IN ring_carrier l1) /\
    (!j. j < n2 ==> ring_mul l2 x2 ((e2:num->C) j) IN ring_carrier l2)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_UNION o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[RING_SUM_IMAGE; EQ_ADD_RCANCEL; o_DEF; ADD_SUB] THEN
    BINOP_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; ARITH_RULE `~(j + n1 < n1:num)`] THEN
    ASM_SIMP_TAC[PROD_RING; RING_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. (if b then ring_1 k else ring_0 k) IN ring_carrier(k:A ring)`
  ASSUME_TAC THENL [MESON_TAC[RING_0; RING_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. i < n1 /\ j < n1
           ==> (f1:num->B->A) i ((e1:num->B) j) IN ring_carrier k /\
               f1 i (ring_mul l1 x1 (e1 j)) IN ring_carrier k) /\
    (!i j. i < n2 /\ j < n2
           ==> (f2:num->C->A) i ((e2:num->C) j) IN ring_carrier k /\
               f2 i (ring_mul l2 x2 (e2 j)) IN ring_carrier k) /\
    (!i. i < n1 + n2 /\ ~(i < n1) ==> i - n1 < n2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_BLOCK_TRIANGULAR o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM(ASSUME `{i:num | i < n1 + n2} =
                  {i | i < n1} UNION IMAGE (\j. j + n1) {j | j < n2}`)] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
                IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `i:num < n1` THEN ASM_CASES_TAC `j:num < n1` THEN
      ASM_SIMP_TAC[PROD_RING; RING_MUL_RZERO; RING_ADD; RING_SUB; RING_0] THEN
      MATCH_MP_TAC RING_ADD THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC RING_SUB THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `~(j + n1 < n1:num)`; PROD_RING;
                   RING_MUL_RZERO; ARITH_RULE `i:num < n1 ==> ~(i = j + n1)`;
                   RING_SUB_REFL; RING_ADD_LZERO; RING_0]];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN SIMP_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[PROD_RING];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_REINDEX o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_NUMSEG_LT; EQ_ADD_RCANCEL]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_DET_EQ THEN
  SIMP_TAC[IN_ELIM_THM; ARITH_RULE `~(j + n1 < n1:num)`; ADD_SUB;
           EQ_ADD_RCANCEL] THEN
  ASM_SIMP_TAC[PROD_RING; RING_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* The discriminant of a free basis g of size n: the determinant of the      *)
(* trace form, the array of the traces algebra_trace (k,l) h (g i * g j) for *)
(* i, j < n. It commutes with base change                                    *)
(* (BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE) and changes by det(C)^2 under a    *)
(* change of basis C (BASIS_DISCRIMINANT_CHANGE_OF_BASIS). Over a field it   *)
(* vanishes exactly when the trace form is degenerate                        *)
(* (BASIS_DISCRIMINANT_EQ_0; over a domain a degenerate trace form gives 0:  *)
(* BASIS_DISCRIMINANT_DEGENERATE), so it is nonzero for a field l when n is  *)
(* nonzero in k (BASIS_DISCRIMINANT_NONZERO); it clears the denominators of  *)
(* the coordinates (BASIS_DISCRIMINANT_TIMES_COORD, by Cramer).              *)
(* ------------------------------------------------------------------------- *)

let basis_discriminant = new_definition
 `basis_discriminant (k:A ring,l:B ring) (h:A->B) n (g:num->B) =
  ring_det k {i | i < n}
    (\i j. algebra_trace (k,l) h (ring_mul l (g i) (g j)))`;;

(* The discriminant commutes with homomorphisms u of the base rings and f of *)
(* the algebras compatible with the structure maps, when the image f o g of  *)
(* the basis is again a free basis.                                          *)
let BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (h':C->D) (u:A->C) (f:B->D) k l k' l' n g.
        ring_homomorphism(k,l) h /\ ring_homomorphism(k',l') h' /\
        ring_homomorphism(k,k') u /\ ring_homomorphism(l,l') f /\
        (!a. a IN ring_carrier k ==> f(h a) = h'(u a)) /\
        free_basis (k,l) h n g /\ free_basis (k',l') h' n (f o g)
        ==> basis_discriminant (k',l') h' n (f o g) =
            u(basis_discriminant (k,l) h n g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[basis_discriminant] THEN
  MP_TAC(ISPECL [`k:A ring`; `k':C ring`; `u:A->C`; `{i:num | i < n}`;
    `\i j. algebra_trace (k,l) (h:A->B) (ring_mul l ((g:num->B) i) (g j))`]
    RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_mul l' ((f:B->D)((g:num->B) i)) (f(g j)) = f(ring_mul l (g i) (g j))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`h:A->B`; `h':C->D`; `u:A->C`; `f:B->D`; `k:A ring`;
                   `l:B ring`; `k':C ring`; `l':D ring`; `n:num`; `g:num->B`;
                   `ring_mul l ((g:num->B) i) (g j)`]
      ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_MUL]]);;

let BASIS_DISCRIMINANT_CHANGE_OF_BASIS = prove
 (`!(h:A->B) k l n g g' (C:num->num->A).
        ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ free_basis (k,l) h n g' /\
        (!i j. i < n /\ j < n ==> C i j IN ring_carrier k) /\
        (!i. i < n ==> g' i = ring_sum l {j | j < n}
                                (\j. ring_mul l (h(C i j)) (g j)))
        ==> basis_discriminant (k,l) h n g' =
            ring_mul k (ring_pow k (ring_det k {i | i < n} C) 2)
                       (basis_discriminant (k,l) h n g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g':num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[basis_discriminant] THEN
  ABBREV_TAC
   `P = \p q. algebra_trace (k,l) (h:A->B)
                (ring_mul l ((g:num->B) p) (g q))` THEN
  SUBGOAL_THEN `!p q. (P:num->num->A) p q IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_det k {i | i < n}
      (\i j. ring_sum k {p | p < n}
               (\p. ring_mul k ((C:num->num->A) i p)
                      (ring_sum k {q | q < n}
                         (\q. ring_mul k ((P:num->num->A) p q) (C j q)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    UNDISCH_THEN
     `!i. i < n ==> (g':num->B) i =
                    ring_sum l {j | j < n}
                      (\j. ring_mul l ((h:A->B)((C:num->num->A) i j))
                                      ((g:num->B) j))`
     (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)] THEN
                ASSUME_TAC th) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ALGEBRA_TRACE_LINCOMB_MUL o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ALGEBRA_TRACE_MUL_LINCOMB o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_MUL_SYM THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`; `C:num->num->A`;
    `\p j. ring_sum k {q | q < n}
             (\q. ring_mul k ((P:num->num->A) p q) ((C:num->num->A) j q))`]
    RING_DET_MUL) THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`; `P:num->num->A`;
                 `\q j. (C:num->num->A) j q`] RING_DET_MUL) THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`; `C:num->num->A`]
    RING_DET_TRANSP) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUM] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul (r:A ring) c (ring_mul r d c) =
    ring_mul r (ring_pow r c 2) d`) THEN
  REWRITE_TAC[RING_DET]);;

let TRACE_FORM_NONDEGENERATE = prove
 (`!(h:A->B) k l n g x.
        field l /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ ~(ring_of_num k n = ring_0 k) /\
        x IN ring_carrier l /\ ~(x = ring_0 l)
        ==> ?y. y IN ring_carrier l /\
                ~(algebra_trace (k,l) h (ring_mul l x y) = ring_0 k)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `ring_inv l x:B` THEN
  ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_1) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `ring_1 k:A`] ALGEBRA_TRACE_NORM_BASE_FREE_BASIS) THEN
  ASM_SIMP_TAC[RING_1; RING_MUL_RID; RING_OF_NUM]);;

(* Conversely, over a domain a degenerate trace form (a nonzero x with       *)
(* Tr(x y) = 0 for all y) gives discriminant zero.                           *)
let BASIS_DISCRIMINANT_DEGENERATE = prove
 (`!(h:A->B) k l n g x.
        integral_domain k /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ x IN ring_carrier l /\ ~(x = ring_0 l) /\
        (!y. y IN ring_carrier l
             ==> algebra_trace (k,l) h (ring_mul l x y) = ring_0 k)
        ==> basis_discriminant (k,l) h n g = ring_0 k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `x:B`] BASIS_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = basis_coordinates (k,l) (h:A->B) n g x` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[basis_discriminant] THEN
  MATCH_MP_TAC RING_DET_DEPENDENT_ROWS THEN EXISTS_TAC `c:num->A` THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM;
               ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`] THEN
    DISCH_TAC THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_LZERO];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:num->B) j`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC ALGEBRA_TRACE_LINCOMB_MUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]]);;

let BASIS_DISCRIMINANT_EQ_0 = prove
 (`!(h:A->B) k l n g.
        field k /\ ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> (basis_discriminant (k,l) h n g = ring_0 k <=>
             ?x. x IN ring_carrier l /\ ~(x = ring_0 l) /\
                 !y. y IN ring_carrier l
                     ==> algebra_trace (k,l) h (ring_mul l x y) =
                         ring_0 k)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN MATCH_MP_TAC BASIS_DISCRIMINANT_DEGENERATE THEN
    EXISTS_TAC `x:B` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  REWRITE_TAC[basis_discriminant] THEN
  ASM_SIMP_TAC[RING_DET_EQ_0_ROWS; FINITE_NUMSEG_LT; IN_ELIM_THM;
               ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `ring_sum l {i | i < n} (\i. ring_mul l ((h:A->B)(c i)) ((g:num->B) i))` THEN
  REWRITE_TAC[RING_SUM] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                   `c:num->A`] FREE_BASIS_INDEPENDENT) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n
        ==> algebra_trace (k,l) h
             (ring_mul l (ring_sum l {i | i < n}
                           (\i. ring_mul l ((h:A->B)(c i)) ((g:num->B) i)))
                         (g j)) = ring_0 k`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM(MATCH_MP th
     (ASSUME `j:num < n`))]) THEN
    MATCH_MP_TAC ALGEBRA_TRACE_LINCOMB_MUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `y:B`] BASIS_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM(CONJUNCT2 th)] THEN
                       ASSUME_TAC(CONJUNCT1 th)) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ALGEBRA_TRACE_MUL_LINCOMB o
    lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUM] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_RZERO]);;

let BASIS_DISCRIMINANT_NONZERO = prove
 (`!(h:A->B) k l n g.
        field k /\ field l /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ ~(ring_of_num k n = ring_0 k)
        ==> ~(basis_discriminant (k,l) h n g = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    BASIS_DISCRIMINANT_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `x:B`] TRACE_FORM_NONDEGENERATE) THEN
  ASM_MESON_TAC[]);;

let BASIS_DISCRIMINANT_TIMES_COORD = prove
 (`!(h:A->B) k l n g r x.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        r subring_of k /\ x IN ring_carrier l /\
        (!i j. i < n /\ j < n
               ==> algebra_trace (k,l) h (ring_mul l (g i) (g j)) IN r) /\
        (!j. j < n ==> algebra_trace (k,l) h (ring_mul l (g j) x) IN r)
        ==> !m. m < n
                ==> ring_mul k (basis_discriminant (k,l) h n g)
                               (basis_coordinates (k,l) h n g x m) IN r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  REWRITE_TAC[basis_discriminant] THEN
  ABBREV_TAC
   `P = \i j. algebra_trace (k,l) (h:A->B)
                (ring_mul l ((g:num->B) i) (g j))` THEN
  ABBREV_TAC `c = basis_coordinates (k,l) (h:A->B) n g x` THEN
  SUBGOAL_THEN
   `(!i j. (P:num->num->A) i j IN ring_carrier k) /\
    (!i. i < n ==> (c:num->A) i IN ring_carrier k) /\
    (!i j. ring_cofactor k {i | i < n} (P:num->num->A) i j IN ring_carrier k)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "c"] THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER; BASIS_COORDINATES_IN_CARRIER;
                 RING_COFACTOR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n
        ==> algebra_trace (k,l) h (ring_mul l ((g:num->B) j) x) =
            ring_sum k {i | i < n} (\i. ring_mul k ((c:num->A) i)
                                                 ((P:num->num->A) j i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "c"] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                   `x:B`] BASIS_COORDINATES_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
                          [SYM th]) THEN
    MATCH_MP_TAC ALGEBRA_TRACE_MUL_LINCOMB THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; BASIS_COORDINATES_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul k (ring_det k {i | i < n} P) ((c:num->A) m) =
    ring_sum k {j | j < n}
      (\j. ring_mul k (ring_cofactor k {i | i < n} P j m)
             (algebra_trace (k,l) (h:A->B)
                (ring_mul l ((g:num->B) j) x)))`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[ring_cofactor] THEN MATCH_MP_TAC RING_DET_SUBRING THEN
    EXPAND_TAC "P" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[IN_SUBRING_0; IN_SUBRING_1]] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum k {i | i < n}
      (\i. ring_mul k ((c:num->A) i)
             (ring_sum k {j | j < n}
                (\j. ring_mul k (ring_cofactor k {i | i < n} P j m)
                                ((P:num->num->A) j i))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_DET_ADJUGATE_COLUMNS; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {i | i < n}
        (\i. if i = m then ring_mul k ((c:num->A) m)
                             (ring_det k {i | i < n} P)
             else ring_0 k)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; RING_MUL; RING_DET] THEN
      MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_DET];
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = m` THEN ASM_SIMP_TAC[RING_MUL_RZERO]];
    MP_TAC(BETA_RULE(ISPECL
     [`k:A ring`; `{i:num | i < n}`; `{j:num | j < n}`; `c:num->A`;
      `\j. ring_cofactor k {i | i < n} (P:num->num->A) j m`;
      `\i j. (P:num->num->A) j i`] RING_SUM_MUL_SWAP)) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Nilpotent elements have trace zero over a domain                          *)
(* (ALGEBRA_TRACE_NILPOTENT): for x nilpotent, 1 + t x is a unit of l[t], so *)
(* the determinant of the coefficientwise matrix of 1 + t x is a unit of     *)
(* k[t] (RING_UNIT_MUL_MATRIX_POLY), hence a constant, and its coefficient   *)
(* of t is the trace of the matrix of x (COEFF_1_RING_DET). So a nonzero     *)
(* nilpotent element makes the discriminant zero                             *)
(* (BASIS_DISCRIMINANT_NILPOTENT).                                           *)
(* ------------------------------------------------------------------------- *)

(* Multiplication matrices applied coefficientwise to polynomials over l.    *)
let RING_POLYNOMIAL_MUL_MATRIX = prove
 (`!(h:A->B) k l n g p i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        ring_polynomial l (p:(1->num)->B) /\ i < n /\ j < n
        ==> ring_polynomial k
             ((\y. mul_matrix (k,l) h n g y i j) o p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_POLYNOMIAL_COEFF; COEFF_COMPOSE] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    FINITE_SUBSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[MUL_MATRIX_0]);;

let MUL_MATRIX_POLY_MUL = prove
 (`!(h:A->B) k l n g p q i j.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        ring_polynomial l (p:(1->num)->B) /\ ring_polynomial l q /\
        i < n /\ j < n
        ==> (\y. mul_matrix (k,l) h n g y i j) o poly_mul l p q =
            ring_sum (poly_ring k (:1)) {m | m < n}
              (\m. poly_mul k
                     ((\y. mul_matrix (k,l) h n g y i m) o p)
                     ((\y. mul_matrix (k,l) h n g y m j) o q))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FUN_EQ_COEFF] THEN
  X_GEN_TAC `d:num` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
  SUBGOAL_THEN
   `(!e. coeff e (p:(1->num)->B) IN ring_carrier l) /\
    (!e. coeff e (q:(1->num)->B) IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_MUL_MATRIX] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COEFF_COMPOSE; COEFF_POLY_MUL] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `0..d`; `\a:num. ring_1(k:A ring)`;
                 `\a. ring_mul l (coeff a (p:(1->num)->B))
                                 (coeff (d - a) (q:(1->num)->B))`;
                 `i:num`; `j:num`] MUL_MATRIX_RING_SUM) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; RING_1; RING_MUL; RING_MUL_LID;
               MUL_MATRIX_IN_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[MUL_MATRIX_MUL] THEN
  W(MP_TAC o BETA_RULE o PART_MATCH (lhand o rand) RING_SUM_SWAP o
    lhand o snd) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL;
               MUL_MATRIX_IN_CARRIER]);;

(* Coefficientwise multiplication matrices of a unit of l[t] have a          *)
(* determinant that is a unit of k[t].                                       *)
let RING_UNIT_MUL_MATRIX_POLY = prove
 (`!(h:A->B) k l n g p.
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        ring_unit (poly_ring l (:1)) p
        ==> ring_unit (poly_ring k (:1))
             (ring_det (poly_ring k (:1)) {i | i < n}
               (\i j. (\y. mul_matrix (k,l) h n g y i j) o p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_unit] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:(1->num)->B` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  REWRITE_TAC[RING_DET] THEN
  EXISTS_TAC `ring_det (poly_ring k (:1)) {i | i < n}
       (\i j. (\y. mul_matrix (k,l) (h:A->B) n g y i j) o q)` THEN
  REWRITE_TAC[RING_DET] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_DET_MUL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                 RING_POLYNOMIAL_MUL_MATRIX];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  TRANS_TAC EQ_TRANS
   `ring_det (poly_ring k (:1)) {i:num | i < n}
      (\i j. if i = j then ring_1 (poly_ring k (:1))
             else ring_0 (poly_ring (k:A ring) (:1)))` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[RING_DET_I; FINITE_NUMSEG_LT]] THEN
  MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[POLY_RING_CLAUSES]) THEN
  REWRITE_TAC[POLY_RING_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM MUL_MATRIX_POLY_MUL] THEN
  REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_COMPOSE; COEFF_POLY_1] THEN
  X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d:num = 0` THEN ASM_CASES_TAC `i:num = j` THEN
  ASM_SIMP_TAC[COEFF_POLY_1; COEFF_POLY_0; MUL_MATRIX_1;
               MUL_MATRIX_0]);;

let ALGEBRA_TRACE_NILPOTENT = prove
 (`!(h:A->B) k l n g x.
        integral_domain k /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ ring_nilpotent l x
        ==> algebra_trace (k,l) h x = ring_0 k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_NILPOTENT_IN_CARRIER) THEN
  ABBREV_TAC `z = ring_mul (poly_ring l (:1)) (poly_var l one)
                           (poly_const l (x:B))` THEN
  SUBGOAL_THEN `ring_nilpotent (poly_ring l (:1)) (z:(1->num)->B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC RING_NILPOTENT_LMUL THEN
    REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR] THEN
    MATCH_MP_TAC RING_NILPOTENT_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 RING_UNIT_NILPOTENT_CLAUSES_1)) THEN
  ABBREV_TAC `P = ring_add (poly_ring l (:1)) (ring_1(poly_ring l (:1)))
                           (z:(1->num)->B)` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_unit]) THEN
  REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `coeff 0 (P:(1->num)->B) = ring_1 l /\ coeff 1 P = x`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "z"] THEN REWRITE_TAC[POLY_RING_CLAUSES] THEN
    ASM_SIMP_TAC[COEFF_POLY_ADD; COEFF_POLY_1; COEFF_POLY_VAR_MUL;
                 COEFF_POLY_CONST; RING_POLYNOMIAL_IMP_POWERSERIES;
                 RING_POLYNOMIAL_CONST; ARITH; RING_ADD_RZERO;
                 RING_ADD_LZERO; RING_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `P:(1->num)->B`] RING_UNIT_MUL_MATRIX_POLY) THEN
  ASM_SIMP_TAC[RING_UNIT_POLY_DOMAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A`
   (MP_TAC o AP_TERM `coeff 1:((1->num)->A)->A` o CONJUNCT2)) THEN
  REWRITE_TAC[COEFF_POLY_CONST; ARITH_EQ] THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`;
    `\i j. (\y. mul_matrix (k,l) (h:A->B) n g y i j) o
           (P:(1->num)->B)`] COEFF_1_RING_DET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; COEFF_COMPOSE;
                 RING_POLYNOMIAL_MUL_MATRIX;
                 MUL_MATRIX_1];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                 `x:B`] ALGEBRA_TRACE_FREE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[COEFF_COMPOSE]);;

let BASIS_DISCRIMINANT_NILPOTENT = prove
 (`!(h:A->B) k l n g x.
        integral_domain k /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n g /\ ring_nilpotent l x /\ ~(x = ring_0 l)
        ==> basis_discriminant (k,l) h n g = ring_0 k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BASIS_DISCRIMINANT_DEGENERATE THEN
  EXISTS_TAC `x:B` THEN ASM_SIMP_TAC[RING_NILPOTENT_IN_CARRIER] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRA_TRACE_NILPOTENT THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `g:num->B`] THEN
  ASM_SIMP_TAC[RING_NILPOTENT_RMUL]);;

(* ------------------------------------------------------------------------- *)
(* Resultants and discriminants of univariate polynomials over any ring.     *)
(* ------------------------------------------------------------------------- *)

(* Sylvester matrix of p, q with (actual) degrees m, n: rows i < n carry the *)
(* coefficients of p from the top, shifted right by i; rows n + i carry      *)
(* those of q, shifted right by i. For two constants, including two zero     *)
(* polynomials, this is the empty determinant 1.                             *)
let poly_resultant = new_definition
 `poly_resultant (r:A ring) p q =
        ring_det r {i | i < poly_deg r p + poly_deg r q}
         (\i j. if i < poly_deg r q
                then if i <= j /\ j <= i + poly_deg r p
                     then coeff ((poly_deg r p + i) - j) p else ring_0 r
                else if i - poly_deg r q <= j /\ j <= i
                     then coeff (i - j) q else ring_0 r)`;;

(* The discriminant: (-1)^(n(n-1)/2) times the determinant of the Sylvester  *)
(* matrix of p and its derivative with the formal degrees n and n - 1, its   *)
(* first column (lc p times e_0 + n e_(n-1) for n >= 2) divided by lc p. No  *)
(* division is needed, so it is defined over any ring. Every constant,       *)
(* including the zero polynomial, has discriminant 1.                        *)
let poly_discriminant = new_definition
 `poly_discriminant (r:A ring) p =
        ring_mul r
         (ring_pow r (ring_neg r (ring_1 r))
            ((poly_deg r p * (poly_deg r p - 1)) DIV 2))
         (ring_det r {i | i < 2 * poly_deg r p - 1}
           (\i j. if j = 0
                  then if i = 0 then ring_1 r
                       else if i = poly_deg r p - 1
                       then ring_of_num r (poly_deg r p) else ring_0 r
                  else if i < poly_deg r p - 1
                  then if i <= j /\ j <= i + poly_deg r p
                       then coeff ((poly_deg r p + i) - j) p else ring_0 r
                  else if i - (poly_deg r p - 1) <= j /\ j <= i
                  then coeff (i - j) (poly_deriv r p) else ring_0 r))`;;

(* ------------------------------------------------------------------------- *)
(* Determinants of coefficient arrays of families of polynomials: for f(i),  *)
(* i < N, the array with entry (i,j) the coefficient of X^(N-1-j) in f(i). A *)
(* combination of a family b(k) with coordinates a(i,k) gives the product of *)
(* the determinants (RING_DET_COEFF_RING_SUM); for b(k) monic of degree      *)
(* N-1-k the second factor is 1 (RING_DET_COEFF_MONIC_REV,                   *)
(* RING_DET_COEFF_BASIS). Over a field the determinant vanishes iff a        *)
(* nontrivial combination of the f(i) is zero (RING_DET_COEFF_EQ_0).         *)
(* ------------------------------------------------------------------------- *)

let RING_DET_COEFF_RING_SUM = prove
 (`!(r:A ring) N (a:num->num->A) (b:num->(1->num)->A) (d:num->num).
        (!i k. i < N /\ k < N ==> a i k IN ring_carrier r) /\
        (!k. k < N ==> b k IN ring_carrier(poly_ring r (:1)))
        ==> ring_det r {i | i < N}
              (\i j. coeff (d j)
                      (ring_sum (poly_ring r (:1)) {k | k < N}
                         (\k. poly_mul r (poly_const r (a i k)) (b k)))) =
            ring_mul r (ring_det r {i | i < N} a)
                       (ring_det r {i | i < N} (\k j. coeff (d j) (b k)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k < N ==> ring_polynomial r ((b:num->(1->num)->A) k)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `{i:num | i < N}`; `a:num->num->A`;
                 `\k j. coeff ((d:num->num) j) ((b:num->(1->num)->A) k)`]
    RING_DET_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_POLYNOMIAL_IMP_POWERSERIES]);;

let RING_DET_COEFF_MONIC_REV = prove
 (`!(r:A ring) N (b:num->(1->num)->A).
        (!k. k < N
             ==> b k IN ring_carrier(poly_ring r (:1)) /\
                 poly_deg r (b k) <= (N - 1) - k /\
                 coeff ((N - 1) - k) (b k) = ring_1 r)
        ==> ring_det r {i | i < N} (\k j. coeff ((N - 1) - j) (b k)) =
            ring_1 r`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_UPPERTRIANGULAR o
    lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ_1 THEN
    ASM_SIMP_TAC[IN_ELIM_THM]]);;

let RING_DET_COEFF_BASIS = prove
 (`!(r:A ring) N (g:num->(1->num)->A) (a:num->num->A) (b:num->(1->num)->A).
        (!i k. i < N /\ k < N ==> a i k IN ring_carrier r) /\
        (!k. k < N
             ==> b k IN ring_carrier(poly_ring r (:1)) /\
                 poly_deg r (b k) <= (N - 1) - k /\
                 coeff ((N - 1) - k) (b k) = ring_1 r) /\
        (!i. i < N
             ==> g i = ring_sum (poly_ring r (:1)) {k | k < N}
                         (\k. poly_mul r (poly_const r (a i k)) (b k)))
        ==> ring_det r {i | i < N} (\i j. coeff ((N - 1) - j) (g i)) =
            ring_det r {i | i < N} a`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_det r {i | i < N}
      (\i j. coeff ((N - 1) - j)
               (ring_sum (poly_ring r (:1)) {k | k < N}
                  (\k. poly_mul r (poly_const r ((a:num->num->A) i k))
                                  ((b:num->(1->num)->A) k))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `N:num`; `a:num->num->A`;
                 `b:num->(1->num)->A`; `\j. (N - 1) - j`]
    RING_DET_COEFF_RING_SUM) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `N:num`; `b:num->(1->num)->A`]
    RING_DET_COEFF_MONIC_REV) THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_DET]);;

(* Subtracting c times the next row from the rows n, ..., N - 2 does not     *)
(* change the determinant (an upper unitriangular row operation).            *)
let RING_DET_ROW_OPERATIONS_SUCC = prove
 (`!(r:A ring) N n c (m:num->num->A).
        c IN ring_carrier r /\
        (!i j. i < N /\ j < N ==> m i j IN ring_carrier r)
        ==> ring_det r {i | i < N}
              (\i j. if n <= i /\ i + 1 < N
                     then ring_sub r (m i j) (ring_mul r c (m (i + 1) j))
                     else m i j) =
            ring_det r {i | i < N} m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `{i:num | i < N}`;
    `\i k. if k = i then ring_1 r
           else if n <= i /\ i + 1 < N /\ k = i + 1 then ring_neg r c
           else ring_0 (r:A ring)`; `m:num->num->A`] RING_DET_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0; RING_1; RING_NEG];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_UPPERTRIANGULAR o
    lhand o rand o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RING_PRODUCT_1]] THEN
  SIMP_TAC[RING_MUL_LID; RING_DET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:num->num->A) i j IN ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(m:num->num->A) (i + 1) j IN ring_carrier r`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r {k | k < N}
        (\k. ring_add r (if k = i then (m:num->num->A) i j else ring_0 r)
                        (if k = i + 1
                         then ring_neg r (ring_mul r c (m (i + 1) j))
                         else ring_0 r))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_ADD o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0; RING_NEG; RING_MUL];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; RING_NEG; RING_MUL] THEN
      REWRITE_TAC[ring_sub];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      ASM_CASES_TAC `k:num = i` THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i = i + 1)`; RING_ADD_RZERO; RING_MUL_LID] THEN
      ASM_CASES_TAC `k = i + 1` THEN
      ASM_SIMP_TAC[RING_ADD_LZERO; RING_MUL_LZERO; RING_MUL_LNEG; RING_NEG;
                   RING_MUL; RING_0]];
    SUBGOAL_THEN `!k. ~(n <= i /\ i + 1 < N /\ k = i + 1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r {k | k < N}
        (\k. if k = i then (m:num->num->A) i j else ring_0 r)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      ASM_CASES_TAC `k:num = i` THEN ASM_SIMP_TAC[RING_MUL_LID] THEN
      ASM_SIMP_TAC[RING_MUL_LZERO]]]);;

(* The family (X - c) h(i) + e(i), i <= N, with e(i) = 0 for i < N: in the   *)
(* basis (X - c) X^(N-1-k), k < N, and 1 its coordinate array is block       *)
(* triangular with corner e(N).                                              *)
let RING_DET_COEFF_X_MINUS = prove
 (`!(r:A ring) N c (h:num->(1->num)->A) (e:num->A).
        c IN ring_carrier r /\
        (!i. i <= N
             ==> h i IN ring_carrier(poly_ring r (:1)) /\
                 (poly_deg r (h i) < N \/ h i = poly_0 r) /\
                 e i IN ring_carrier r) /\
        (!i. i < N ==> e i = ring_0 r)
        ==> ring_det r {i | i < N + 1}
              (\i j. coeff (N - j)
                       (poly_add r (poly_const r (e i))
                         (poly_mul r
                            (poly_sub r (poly_var r one) (poly_const r c))
                            (h i)))) =
            ring_mul r
              (ring_det r {i | i < N} (\i j. coeff ((N - 1) - j) (h i)))
              (e N)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "h") (LABEL_TAC "e"))) THEN
  ABBREV_TAC `xc = poly_sub r (poly_var r one) (poly_const r (c:A))` THEN
  SUBGOAL_THEN
   `xc IN ring_carrier(poly_ring r (:1)) /\ ring_polynomial r (xc:(1->num)->A)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "xc" THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER; RING_POLYNOMIAL_X_MINUS_A];
    ALL_TAC] THEN
  SUBGOAL_THEN `{k:num | k <= N} = N INSERT {k | k < N}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`r:A ring`; `N + 1`;
    `\i. poly_add r (poly_const r ((e:num->A) i))
                    (poly_mul r (xc:(1->num)->A) ((h:num->(1->num)->A) i))`;
    `\i k. if k < N then coeff ((N - 1) - k) ((h:num->(1->num)->A) i)
           else (e:num->A) i`;
    `\k. if k < N
         then poly_mul r (xc:(1->num)->A)
                (poly_pow r (poly_var r one) ((N - 1) - k))
         else poly_1 r`]
   RING_DET_COEFF_BASIS) THEN
  REWRITE_TAC[ADD_SUB; ARITH_RULE `i < N + 1 <=> i <= N`] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `k:num`] THEN STRIP_TAC THEN
      USE_THEN "h" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THEN SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_MUL;
                     RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR] THEN
        CONJ_TAC THENL
         [W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o
            lhand o snd) THEN
          ASM_SIMP_TAC[RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR] THEN
          MATCH_MP_TAC(ARITH_RULE
           `a <= 1 /\ b <= (N - 1) - k /\ k < N
            ==> x <= a + b ==> x <= N - k`) THEN
          ASM_REWRITE_TAC[POLY_DEG_VAR_POW] THEN CONJ_TAC THENL
           [EXPAND_TAC "xc" THEN
            ASM_SIMP_TAC[POLY_DEG_SUB_CONST; RING_POLYNOMIAL_VAR] THEN
            REWRITE_TAC[POLY_DEG_VAR] THEN ARITH_TAC;
            ARITH_TAC];
          ASM_SIMP_TAC[COEFF_POLY_MUL_VARPOW; RING_POLYNOMIAL_IMP_POWERSERIES;
                       ARITH_RULE `k < N ==> ~(N - k < (N - 1) - k)`;
                       ARITH_RULE `k < N ==> (N - k) - ((N - 1) - k) = 1`] THEN
          EXPAND_TAC "xc" THEN
          REWRITE_TAC[COEFF_POLY_SUB; COEFF_POLY_VAR; COEFF_POLY_CONST] THEN
          REWRITE_TAC[ARITH_EQ] THEN SIMP_TAC[RING_SUB_RZERO; RING_1]];
        SUBGOAL_THEN `k:num = N` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[SUB_REFL; COEFF_POLY_1; POLY_DEG_1; LE_REFL] THEN
        REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_1]];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "h" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`r:A ring`; `(h:num->(1->num)->A) i`; `N:num`]
      POLY_EXPAND_REV) THEN
    ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL;
                 GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_MUL;
                 RING_POLYNOMIAL_CONST; RING_POLYNOMIAL_1] THEN
    ASM_SIMP_TAC[POLY_MUL_RID; RING_POLYNOMIAL_IMP_POWERSERIES;
                 RING_POLYNOMIAL_CONST] THEN
    REWRITE_TAC[POLY_CLAUSES] THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC RING_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST] THEN
        ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT];
        MATCH_MP_TAC RING_POW THEN
        REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS(ISPEC `poly_ring (r:A ring) (:1)`
      RING_MUL_AC))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST] THEN
      ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT];
      MATCH_MP_TAC RING_POW THEN
      REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{i:num | i <= N} = {i | i < N} UNION {N}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_BLOCK_TRIANGULAR o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_SING; DISJOINT; EXTENSION;
                IN_INTER; IN_SING; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNION] THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      USE_THEN "h" (MP_TAC o SPEC `i:num`) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      COND_CASES_TAC THEN SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[LT_REFL] THEN USE_THEN "e" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN SIMP_TAC[IN_ELIM_THM];
    USE_THEN "h" (MP_TAC o SPEC `N:num`) THEN
    SIMP_TAC[RING_DET_SING; LT_REFL; LE_REFL]]);;

let RING_DET_COEFF_EQ_0 = prove
 (`!(k:A ring) N (f:num->(1->num)->A).
        field k /\
        (!i. i < N
             ==> f i IN ring_carrier(poly_ring k (:1)) /\ poly_deg k (f i) < N)
        ==> (ring_det k {i | i < N} (\i j. coeff ((N - 1) - j) (f i)) =
             ring_0 k <=>
             ?c. (!i. i < N ==> c i IN ring_carrier k) /\
                 (?i. i < N /\ ~(c i = ring_0 k)) /\
                 ring_sum (poly_ring k (:1)) {i | i < N}
                   (\i. poly_mul k (poly_const k (c i)) (f i)) = poly_0 k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_EQ_0_ROWS o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; COEFF_IN_CARRIER_ALT] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (c <=> d)) ==> (a /\ b /\ c <=> a /\ b /\ d)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!d. coeff d (ring_sum (poly_ring k (:1)) {i | i < N}
                  (\i. poly_mul k (poly_const k (c i)) (f i))) =
        ring_sum k {i | i < N}
          (\i. ring_mul k ((c:num->A) i) (coeff d ((f:num->(1->num)->A) i)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_POLYNOMIAL_MUL;
                 RING_POLYNOMIAL_CONST] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; COEFF_POLY_LMUL;
                 RING_POLYNOMIAL_IMP_POWERSERIES];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_COEFF] THEN
  ASM_REWRITE_TAC[COEFF_POLY_0] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `d:num` THEN ASM_CASES_TAC `d:num < N` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(N - 1) - d`) THEN
      ASM_SIMP_TAC[ARITH_RULE `d < N ==> (N - 1) - d < N`;
                   ARITH_RULE `d < N ==> (N - 1) - ((N - 1) - d) = d`];
      MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `coeff d ((f:num->(1->num)->A) a) = ring_0 k`
      SUBST1_TAC THENL
       [USE_THEN "f" (MP_TAC o SPEC `a:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ASM_SIMP_TAC[RING_MUL_RZERO]]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Sylvester determinant with formal degrees m and n: the array of       *)
(* poly_resultant with m and n in place of the degrees of p and q, for deg p *)
(* <= m and deg q <= n. It is the coefficient array of the family X^(n-1-i)  *)
(* p (i < n), X^(m+n-1-i) q (n <= i < m + n) (RING_DET_SYLVESTER).           *)
(* Multiplying p by X - c multiplies it by q(c) (RING_DET_SYLVESTER_X_MINUS: *)
(* one row operation on the q rows, then RING_DET_COEFF_X_MINUS), which      *)
(* gives the product formula for p split with m roots and any formal degree  *)
(* n of q (RING_DET_SYLVESTER_ROOTS). Over a field, for deg p = m and p      *)
(* nonzero, the determinant vanishes iff p and q are not coprime             *)
(* (RING_DET_SYLVESTER_EQ_0). The formal degrees are needed for the          *)
(* discriminant: the derivative of p has the formal degree deg p - 1 even    *)
(* when its degree is smaller.                                               *)
(* ------------------------------------------------------------------------- *)

let RING_DET_SYLVESTER = prove
 (`!(r:A ring) m n p q.
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        poly_deg r p <= m /\ poly_deg r q <= n
        ==> ring_det r {i | i < m + n}
             (\i j. if i < n
                    then if i <= j /\ j <= i + m
                         then coeff ((m + i) - j) p else ring_0 r
                    else if i - n <= j /\ j <= i
                         then coeff (i - j) q else ring_0 r) =
            ring_det r {i | i < m + n}
             (\i j. coeff (((m + n) - 1) - j)
                     (if i < n
                      then poly_mul r
                             (poly_pow r (poly_var r one) ((n - 1) - i)) p
                      else poly_mul r
                             (poly_pow r (poly_var r one) (((m + n) - 1) - i))
                             q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[COEFF_POLY_VARPOW_MUL; RING_POLYNOMIAL_IMP_POWERSERIES] THENL
   [MP_TAC(ARITH_RULE
     `i < n /\ j < m + n
      ==> ((m + n) - 1) - j + j + 1 = m + n /\ (n - 1) - i + i + 1 = n`) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`((m + n) - 1) - j`,`a:num`) THEN
    SPEC_TAC(`(n - 1) - i`,`b:num`) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:num < b <=> m + i < j) /\ a - b = (m + i) - j`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(m:num) + i < j` THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MP_TAC(ARITH_RULE
     `i < m + n /\ j < m + n
      ==> ((m + n) - 1) - j + j + 1 = m + n /\
          ((m + n) - 1) - i + i + 1 = m + n`) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`((m + n) - 1) - j`,`a:num`) THEN
    SPEC_TAC(`((m + n) - 1) - i`,`b:num`) THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(a:num < b <=> i < j) /\ a - b = i - j`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i:num < j` THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* A combination of the rows of the Sylvester array is u p + v q, with u and *)
(* v given by the coordinates.                                               *)
let RING_SUM_SYLVESTER_ROWS = prove
 (`!(r:A ring) m n p q (c:num->A).
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        (!i. i < m + n ==> c i IN ring_carrier r)
        ==> ring_sum (poly_ring r (:1)) {i | i < m + n}
              (\i. poly_mul r (poly_const r (c i))
                    (if i < n
                     then poly_mul r (poly_pow r (poly_var r one) ((n - 1) - i))
                                     p
                     else poly_mul r
                            (poly_pow r (poly_var r one) (((m + n) - 1) - i))
                            q)) =
            poly_add r
             (poly_mul r
               (ring_sum (poly_ring r (:1)) {i | i < n}
                  (\i. poly_mul r (poly_const r (c i))
                         (poly_pow r (poly_var r one) ((n - 1) - i))))
               p)
             (poly_mul r
               (ring_sum (poly_ring r (:1)) {i | i < m}
                  (\i. poly_mul r (poly_const r (c(n + i)))
                         (poly_pow r (poly_var r one) ((m - 1) - i))))
               q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i < m + n
         ==> poly_const r ((c:num->A) i) IN ring_carrier(poly_ring r (:1))) /\
    poly_var r one IN ring_carrier(poly_ring (r:A ring) (:1))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST;
                 RING_POLYNOMIAL_VAR];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_CLAUSES] THEN
  SUBGOAL_THEN
   `{i | i < m + n} = {i | i < n} UNION IMAGE (\i:num. n + i) {i | i < m}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `i:num < n` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `i - n:num` THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    MESON_TAC[ARITH_RULE `~(n + i:num < n)`];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_sum (poly_ring r (:1)) {i | i < n}
        (\i. ring_mul (poly_ring r (:1))
               (ring_mul (poly_ring r (:1)) (poly_const r ((c:num->A) i))
                  (ring_pow (poly_ring r (:1)) (poly_var r one) ((n - 1) - i)))
               p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RING_MUL_ASSOC THEN
      ASM_SIMP_TAC[RING_POW; ARITH_RULE `i:num < n ==> i < m + n`];
      MATCH_MP_TAC RING_SUM_RMUL THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW;
                   ARITH_RULE `i:num < n ==> i < m + n`]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF; ARITH_RULE `~(n + i:num < n)`] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (poly_ring r (:1)) {i | i < m}
      (\i. ring_mul (poly_ring r (:1))
             (ring_mul (poly_ring r (:1)) (poly_const r ((c:num->A) (n + i)))
                (ring_pow (poly_ring r (:1)) (poly_var r one) ((m - 1) - i)))
             q)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE
     `i < m ==> ((m + n) - 1) - (n + i) = (m - 1) - i`] THEN
    MATCH_MP_TAC RING_MUL_ASSOC THEN
    ASM_SIMP_TAC[RING_POW; ARITH_RULE `i:num < m ==> n + i < m + n`];
    MATCH_MP_TAC RING_SUM_RMUL THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW;
                 ARITH_RULE `i:num < m ==> n + i < m + n`]]);;

let RING_DET_SYLVESTER_X_MINUS = prove
 (`!(r:A ring) m n p q c.
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        poly_deg r p <= m /\ poly_deg r q <= n /\ c IN ring_carrier r
        ==> ring_det r {i | i < (m + 1) + n}
             (\i j. if i < n
                    then if i <= j /\ j <= i + m + 1
                         then coeff (((m + 1) + i) - j)
                                (poly_mul r
                                   (poly_sub r (poly_var r one)
                                               (poly_const r c)) p)
                         else ring_0 r
                    else if i - n <= j /\ j <= i
                         then coeff (i - j) q else ring_0 r) =
            ring_mul r (poly_eval r q c)
             (ring_det r {i | i < m + n}
               (\i j. if i < n
                      then if i <= j /\ j <= i + m
                           then coeff ((m + i) - j) p else ring_0 r
                      else if i - n <= j /\ j <= i
                           then coeff (i - j) q else ring_0 r))`,
  let lemA = RING_RULE
   `ring_mul (r:B ring) y (ring_mul r x p) =
    ring_add r (ring_0 r) (ring_mul r x (ring_mul r y p))`
  and lemB = RING_RULE
   `ring_sub (r:B ring) (ring_mul r (ring_mul r x y) z)
                        (ring_mul r c (ring_mul r y z)) =
    ring_add r (ring_0 r) (ring_mul r (ring_sub r x c) (ring_mul r y z))`
  and lemC = RING_RULE `ring_add (r:B ring) a (ring_sub r q a) = q` in
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `xc = poly_sub r (poly_var r one) (poly_const r (c:A))` THEN
  SUBGOAL_THEN
   `xc IN ring_carrier(poly_ring r (:1)) /\
    ring_polynomial r (xc:(1->num)->A) /\
    ring_polynomial r (p:(1->num)->A) /\ ring_polynomial r (q:(1->num)->A) /\
    poly_var r one IN ring_carrier(poly_ring (r:A ring) (:1))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "xc" THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER; RING_POLYNOMIAL_X_MINUS_A] THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
    REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `m + 1`; `n:num`;
                 `poly_mul r (xc:(1->num)->A) p`; `q:(1->num)->A`]
    RING_DET_SYLVESTER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_MUL] THEN
    EXPAND_TAC "xc" THEN ASM_SIMP_TAC[POLY_DEG_MUL_X_MINUS_A] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `m:num`; `n:num`; `p:(1->num)->A`;
                 `q:(1->num)->A`] RING_DET_SYLVESTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `((m + 1) + n) - 1 = m + n /\ (m + 1) + n = (m + n) + 1`] THEN
  ABBREV_TAC `N:num = m + n` THEN
  SUBGOAL_THEN `n:num <= N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `c:A`; `q:(1->num)->A`]
    POLY_DIVIDES_X_MINUS_A) THEN
  ASM_REWRITE_TAC[ring_divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':(1->num)->A`
   (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o REWRITE_RULE[POLY_RING_CLAUSES]))
   o last o CONJUNCTS) THEN
  SUBGOAL_THEN `poly_deg r (q':(1->num)->A) < N \/ q' = poly_0 r`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `q':(1->num)->A = poly_0 r` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `c:A`; `q':(1->num)->A`]
      POLY_DEG_MUL_X_MINUS_A) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
    UNDISCH_TAC
     `poly_sub r q (poly_const r (poly_eval r q c)) =
      poly_mul r xc (q':(1->num)->A)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[POLY_DEG_SUB_CONST; POLY_EVAL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `N + 1`; `n:num`; `c:A`;
   `\i j. coeff (N - j)
           (if i < n
            then poly_mul r (poly_pow r (poly_var r one) ((n - 1) - i))
                   (poly_mul r xc (p:(1->num)->A))
            else poly_mul r (poly_pow r (poly_var r one) (N - i)) q)`]
   RING_DET_ROW_OPERATIONS_SUCC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_MUL; RING_POLYNOMIAL_POW;
                 RING_POLYNOMIAL_VAR];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`r:A ring`; `N:num`; `c:A`;
   `\i. if i < N
        then if i < n
             then poly_mul (r:A ring)
                    (poly_pow r (poly_var r one) ((n - 1) - i))
                    (p:(1->num)->A)
             else poly_mul r (poly_pow r (poly_var r one) ((N - 1) - i))
                    (q:(1->num)->A)
        else (q':(1->num)->A)`;
   `\i. if i = N:num then poly_eval r (q:(1->num)->A) c
        else ring_0 (r:A ring)`]
   RING_DET_COEFF_X_MINUS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num < N` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `~(i:num = N)` (fun th -> REWRITE_TAC[th; RING_0]) THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        COND_CASES_TAC THEN
        ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_MUL;
                     RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                     POLY_DEG_VARPOW_MUL] THEN
        DISJ1_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `i:num = N` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[POLY_EVAL]]];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(fun (_,w) -> let t = rand(rand w) in
     MP_TAC(ISPECL [`r:A ring`; lhand t; rand t] RING_MUL_SYM)) THEN
  ANTS_TAC THENL [REWRITE_TAC[POLY_EVAL; RING_DET]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `y = w /\ z = x ==> x = ring_mul (r:A ring) y c ==> z = ring_mul r w c`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC RING_DET_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `i < N + 1 <=> i <= N`] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num < n` THENL
   [SUBGOAL_THEN `i:num < N /\ ~(i = N) /\ ~(n <= i)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[POLY_CONST_0]] THEN
    AP_TERM_TAC THEN REWRITE_TAC[POLY_CLAUSES] THEN
    MATCH_MP_TAC lemA THEN ASM_SIMP_TAC[RING_POW] THEN
    ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = N` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[LT_REFL; ARITH_RULE `~(N + 1 <= N)`; SUB_REFL] THEN
    ASM_SIMP_TAC[ARITH_RULE `n:num <= N ==> ~(N < n)`] THEN
    SUBST1_TAC(SYM(ASSUME
     `poly_sub r q (poly_const r (poly_eval r q c)) =
      poly_mul r xc (q':(1->num)->A)`)) THEN
    AP_TERM_TAC THEN REWRITE_TAC[POLY_POW] THEN
    SIMP_TAC[POLY_MUL_LID; RING_POLYNOMIAL_IMP_POWERSERIES;
             ASSUME `ring_polynomial r (q:(1->num)->A)`] THEN
    REWRITE_TAC[POLY_CLAUSES] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC lemC THEN ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    REWRITE_TAC[RING_POLYNOMIAL_CONST; POLY_EVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `n <= i /\ i + 1 <= N /\ i < N /\ ~(i + 1 < n)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_CONST_0; ARITH_RULE `N - (i + 1) = (N - 1) - i`;
               ARITH_RULE `i < N ==> N - i = SUC((N - 1) - i)`] THEN
  SUBGOAL_THEN
   `poly_add r (poly_0 r)
      (poly_mul r xc (poly_mul r (poly_pow r (poly_var r one) ((N - 1) - i))
                        (q:(1->num)->A))) =
    poly_sub r
      (poly_mul r (poly_pow r (poly_var r one) (SUC((N - 1) - i))) q)
      (poly_mul r (poly_const r c)
         (poly_mul r (poly_pow r (poly_var r one) ((N - 1) - i)) q))`
  SUBST1_TAC THENL
   [EXPAND_TAC "xc" THEN REWRITE_TAC[POLY_POW; POLY_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC lemB THEN
    ASM_SIMP_TAC[RING_POW] THEN
    ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[COEFF_POLY_SUB] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC COEFF_POLY_LMUL THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR]);;

let POLY_DEG_RING_PRODUCT_X_MINUS_LE = prove
 (`!(r:A ring) (x:K->A) s.
        FINITE s /\ (!i. i IN s ==> x i IN ring_carrier r)
        ==> poly_deg r (ring_product (poly_ring r (:1)) s
                         (\i. poly_sub r (poly_var r one)
                                         (poly_const r (x i)))) <= CARD s`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_RING_PRODUCT_LE o
    lhand o snd) THEN
  ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
  TRANS_TAC LE_TRANS `nsum s (\i:K. 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN
    ASM_SIMP_TAC[POLY_DEG_SUB_CONST; RING_POLYNOMIAL_VAR; POLY_DEG_VAR] THEN
    ARITH_TAC;
    ASM_SIMP_TAC[NSUM_CONST; MULT_CLAUSES; LE_REFL]]);;

let RING_DET_SYLVESTER_ROOTS = prove
 (`!(r:A ring) m n p q a (x:num->A).
        q IN ring_carrier(poly_ring r (:1)) /\ poly_deg r q <= n /\
        a IN ring_carrier r /\ (!i. i < m ==> x i IN ring_carrier r) /\
        p = ring_mul (poly_ring r (:1)) (poly_const r a)
              (ring_product (poly_ring r (:1)) {i | i < m}
                 (\i. poly_sub r (poly_var r one) (poly_const r (x i))))
        ==> ring_det r {i | i < m + n}
             (\i j. if i < n
                    then if i <= j /\ j <= i + m
                         then coeff ((m + i) - j) p else ring_0 r
                    else if i - n <= j /\ j <= i
                         then coeff (i - j) q else ring_0 r) =
            ring_mul r (ring_pow r a n)
              (ring_product r {i | i < m} (\i. poly_eval r q (x i)))`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; RING_PRODUCT_CLAUSES] THEN
    SUBGOAL_THEN
     `poly_const r (a:A) IN ring_carrier(poly_ring r (:1))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST];
      ASM_SIMP_TAC[RING_MUL_RID; RING_POW]] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS `ring_product r {i | i < n} (\i:num. a:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN
      SIMP_TAC[IN_ELIM_THM; LE_REFL; SUB_REFL; COEFF_POLY_CONST];
      ASM_SIMP_TAC[RING_PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
  SUBGOAL_THEN
   `(!i. i < m ==> (x:num->A) i IN ring_carrier r) /\ x m IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!i. i < m + 1 ==> (x:num->A) i IN ring_carrier r` THEN
    MESON_TAC[ARITH_RULE `i < m ==> i < m + 1`; ARITH_RULE `m < m + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `{i | i < m + 1} = m INSERT {i | i < m}` SUBST_ALL_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `p' = ring_mul (poly_ring r (:1)) (poly_const r a)
          (ring_product (poly_ring r (:1)) {i | i < m}
             (\i. poly_sub r (poly_var r one)
                             (poly_const r ((x:num->A) i))))` THEN
  SUBGOAL_THEN
   `p' IN ring_carrier(poly_ring r (:1)) /\ poly_deg r (p':(1->num)->A) <= m`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[RING_PRODUCT] THEN
      ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST];
      REWRITE_TAC[POLY_RING_CLAUSES] THEN MATCH_MP_TAC POLY_DEG_CMUL_LE THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_RING_PRODUCT_X_MINUS_LE o
        lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p = ring_mul (poly_ring r (:1))
          (poly_sub r (poly_var r one) (poly_const r ((x:num->A) m))) p'`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER] THEN
    EXPAND_TAC "p'" THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS(ISPEC `poly_ring (r:A ring) (:1)`
      RING_MUL_AC))) THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER; RING_PRODUCT] THEN
    ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_RING_CLAUSES] THEN
  MP_TAC(ISPECL [`r:A ring`; `m:num`; `n:num`; `p':(1->num)->A`;
                 `q:(1->num)->A`; `(x:num->A) m`]
    RING_DET_SYLVESTER_X_MINUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`n:num`; `p':(1->num)->A`; `q:(1->num)->A`; `a:A`; `x:num->A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  REWRITE_TAC[POLY_EVAL] THEN
  MATCH_MP_TAC(el 2 (CONJUNCTS(ISPEC `r:A ring` RING_MUL_AC))) THEN
  ASM_SIMP_TAC[POLY_EVAL; RING_POW; RING_MUL; RING_PRODUCT]);;

let RING_DET_SYLVESTER_EQ_0 = prove
 (`!(k:A ring) m n p q.
        field k /\
        p IN ring_carrier(poly_ring k (:1)) /\
        q IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\ poly_deg k p = m /\ poly_deg k q <= n
        ==> (ring_det k {i | i < m + n}
              (\i j. if i < n
                     then if i <= j /\ j <= i + m
                          then coeff ((m + i) - j) p else ring_0 k
                     else if i - n <= j /\ j <= i
                          then coeff (i - j) q else ring_0 k) = ring_0 k <=>
             ~ring_coprime (poly_ring k (:1)) (p,q))`,
  let lemma = RING_RULE
   `ring_add (r:A ring) (ring_mul r u p) (ring_mul r v q) = ring_0 r
    ==> ring_mul r v q = ring_mul r p (ring_neg r u)`
  and lemma' = RING_RULE
   `ring_add (r:A ring) (ring_mul r q1 (ring_mul r d p1))
                        (ring_mul r (ring_neg r p1) (ring_mul r d q1)) =
    ring_0 r` in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`k:A ring`; `m:num`; `n:num`; `p:(1->num)->A`;
                 `q:(1->num)->A`] RING_DET_SYLVESTER) THEN
  ASM_SIMP_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_COEFF_EQ_0 o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_MUL; RING_POLYNOMIAL_POW;
                 RING_POLYNOMIAL_VAR; POLY_DEG_VARPOW_MUL] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:num->A` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC))) THEN
    MP_TAC(ISPECL [`k:A ring`; `m:num`; `n:num`; `p:(1->num)->A`;
                   `q:(1->num)->A`; `c:num->A`] RING_SUM_SYLVESTER_ROWS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ABBREV_TAC
     `u = ring_sum (poly_ring k (:1)) {i | i < n}
           (\i. poly_mul k (poly_const k ((c:num->A) i))
                  (poly_pow k (poly_var k one) ((n - 1) - i)))` THEN
    ABBREV_TAC
     `v = ring_sum (poly_ring k (:1)) {i | i < m}
           (\i. poly_mul k (poly_const k ((c:num->A) (n + i)))
                  (poly_pow k (poly_var k one) ((m - 1) - i)))` THEN
    SUBGOAL_THEN
     `u IN ring_carrier(poly_ring k (:1)) /\
      v IN ring_carrier(poly_ring k (:1)) /\
      (poly_deg k (v:(1->num)->A) < m \/ v = poly_0 k)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN REWRITE_TAC[RING_SUM] THEN
      MATCH_MP_TAC POLY_DEG_RING_SUM_VARPOW_REV THEN
      ASM_SIMP_TAC[ARITH_RULE `i:num < m ==> n + i < m + n`];
      ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "uv") THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_divides (poly_ring k (:1)) p (v:(1->num)->A)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_COPRIME_DIVPROD_RIGHT THEN
      EXISTS_TAC `q:(1->num)->A` THEN
      ASM_SIMP_TAC[PID_IMP_UFD; PID_POLY_RING] THEN
      ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ring_divides] THEN ASM_SIMP_TAC[RING_MUL] THEN
      EXISTS_TAC `ring_neg (poly_ring k (:1)) (u:(1->num)->A)` THEN
      ASM_SIMP_TAC[RING_NEG] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] lemma) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[POLY_RING_CLAUSES] THEN USE_THEN "uv" ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `v:(1->num)->A = poly_0 k` ASSUME_TAC THENL
     [ASM_CASES_TAC `v:(1->num)->A = poly_0 k` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:A ring`; `(:1)`; `p:(1->num)->A`; `v:(1->num)->A`]
        POLY_DEG_DIVIDES_LE) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `u:(1->num)->A = poly_0 k` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `u:(1->num)->A`;
                     `p:(1->num)->A`] INTEGRAL_DOMAIN_MUL_EQ_0) THEN
      ASM_REWRITE_TAC[INTEGRAL_DOMAIN_POLY_RING; POLY_RING_CLAUSES] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "uv"
       (MP_TAC o REWRITE_RULE[ASSUME `v:(1->num)->A = poly_0 k`]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
      SIMP_TAC[POLY_MUL_0; POLY_ADD_RZERO; RING_POLYNOMIAL_IMP_POWERSERIES;
               RING_POLYNOMIAL_MUL; ASSUME `ring_polynomial k (u:(1->num)->A)`;
               ASSUME `ring_polynomial k (p:(1->num)->A)`;
               ASSUME `ring_polynomial k (q:(1->num)->A)`];
      ALL_TAC] THEN
    UNDISCH_TAC `~((c:num->A) i = ring_0 k)` THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num < n` THENL
     [MP_TAC(ISPECL [`k:A ring`; `c:num->A`; `n:num`; `(n - 1) - i`]
        COEFF_RING_SUM_VARPOW_REV) THEN
      ASM_SIMP_TAC[ARITH_RULE `i:num < n ==> i < m + n`;
                   ARITH_RULE `i < n ==> (n - 1) - i < n`;
                   ARITH_RULE `i < n ==> (n - 1) - ((n - 1) - i) = i`] THEN
      ASM_REWRITE_TAC[COEFF_POLY_0] THEN MESON_TAC[];
      MP_TAC(ISPECL [`k:A ring`; `\i. (c:num->A)(n + i)`; `m:num`;
                     `(m - 1) - (i - n)`] COEFF_RING_SUM_VARPOW_REV) THEN
      REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `i:num < m ==> n + i < m + n`;
                   ARITH_RULE `~(i < n) /\ i < m + n ==> (m - 1) - (i - n) < m`;
                   ARITH_RULE `~(i < n) /\ i < m + n
                               ==> n + (m - 1) - ((m - 1) - (i - n)) = i`] THEN
      ASM_REWRITE_TAC[COEFF_POLY_0] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[ring_coprime] THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(1->num)->A` MP_TAC) THEN
  REWRITE_TAC[ring_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `p1:(1->num)->A` STRIP_ASSUME_TAC)))
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
       (X_CHOOSE_THEN `q1:(1->num)->A` STRIP_ASSUME_TAC))))
   ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  SUBGOAL_THEN
   `~(d:(1->num)->A = poly_0 k) /\ ~(p1:(1->num)->A = poly_0 k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~(p:(1->num)->A = poly_0 k)` THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN
    ASM_SIMP_TAC[POLY_MUL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(poly_deg k (d:(1->num)->A) = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `(:1)`; `d:(1->num)->A`] POLY_DEG_EQ_0_UNIT) THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg k (p1:(1->num)->A) < m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `d:(1->num)->A`; `p1:(1->num)->A`]
      POLY_DEG_MUL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p = ring_mul (poly_ring k (:1)) d (p1:(1->num)->A)` THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg k (q1:(1->num)->A) < n \/ q1 = poly_0 k`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `q1:(1->num)->A = poly_0 k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `d:(1->num)->A`; `q1:(1->num)->A`]
      POLY_DEG_MUL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `q = ring_mul (poly_ring k (:1)) d (q1:(1->num)->A)` THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\i. if i < n then coeff ((n - 1) - i) (q1:(1->num)->A)
                  else coeff (((m + n) - 1) - i) (poly_neg k p1)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ring_sum (poly_ring k (:1)) {i | i < n}
      (\i. poly_mul k
            (poly_const k (if i < n then coeff ((n - 1) - i) q1
                           else coeff (((m + n) - 1) - i) (poly_neg k p1)))
            (poly_pow k (poly_var k one) ((n - 1) - i))) = q1 /\
    ring_sum (poly_ring k (:1)) {i | i < m}
      (\i. poly_mul k
            (poly_const k (if n + i < n then coeff ((n - 1) - (n + i)) q1
                           else coeff (((m + n) - 1) - (n + i))
                                      (poly_neg k p1)))
            (poly_pow k (poly_var k one) ((m - 1) - i))) =
    poly_neg k (p1:(1->num)->A)`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v")) THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `q1:(1->num)->A`; `n:num`]
        POLY_EXPAND_REV) THEN
      ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
      MP_TAC(ISPECL [`k:A ring`; `poly_neg k (p1:(1->num)->A)`; `m:num`]
        POLY_EXPAND_REV) THEN
      ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_NEG; POLY_DEG_NEG] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN
      SIMP_TAC[IN_ELIM_THM; ARITH_RULE `~(n + i:num < n)`] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `((m + n) - 1) - (n + i) = (m - 1) - i` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REFL_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `m:num`; `n:num`; `p:(1->num)->A`;
                 `q:(1->num)->A`;
                 `\i. if i < n then coeff ((n - 1) - i) (q1:(1->num)->A)
                      else coeff (((m + n) - 1) - i) (poly_neg k p1)`]
    RING_SUM_SYLVESTER_ROWS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL_NEG];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL_NEG];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(LABEL_TAC "zero" o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `p1:(1->num)->A`]
      RING_NEG_EQ_0) THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES; GSYM RING_POLYNOMIAL] THEN
    REMOVE_THEN "v" (SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC RAND_CONV [CONJUNCT1(CONJUNCT2 POLY_CLAUSES)] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REMOVE_THEN "zero" (MP_TAC o SPEC `n + i:num`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n + i < m + n:num <=> i < m`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[POLY_CONST_0; POLY_RING_CLAUSES] THEN
    SIMP_TAC[POLY_MUL_0; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR];
    REWRITE_TAC[POLY_CLAUSES] THEN MATCH_MP_TAC lemma' THEN
    ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL]]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of the resultant: carrier, homomorphisms preserving the  *)
(* degrees, symmetry, constant arguments.                                    *)
(* ------------------------------------------------------------------------- *)

let POLY_RESULTANT_IN_CARRIER = prove
 (`!(r:A ring) p q. poly_resultant r p q IN ring_carrier r`,
  REWRITE_TAC[poly_resultant; RING_DET]);;

let POLY_RESULTANT_HOMOMORPHISM = prove
 (`!(f:A->B) r r' p q.
        ring_homomorphism(r,r') f /\
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        poly_deg r' (f o p) = poly_deg r p /\
        poly_deg r' (f o q) = poly_deg r q
        ==> f(poly_resultant r p q) = poly_resultant r' (f o p) (f o q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_resultant] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_HOMOMORPHISM o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; COEFF_IN_CARRIER_ALT];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[COEFF_COMPOSE]));;

let POLY_RESULTANT_SYM = prove
 (`!(r:A ring) p q.
        poly_resultant r q p =
        ring_mul r
          (ring_pow r (ring_neg r (ring_1 r)) (poly_deg r p * poly_deg r q))
          (poly_resultant r p q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_resultant] THEN
  ABBREV_TAC `m = poly_deg r (p:(1->num)->A)` THEN
  ABBREV_TAC `n = poly_deg r (q:(1->num)->A)` THEN
  SUBGOAL_THEN
   `ring_pow r (ring_neg r (ring_1 r)) (m * n) =
    ring_sign (r:A ring) (\i. if i < m + n then (i + n) MOD (m + n) else i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ring_sign; EVENPERM_CYCLIC_N] THEN
    SIMP_TAC[RING_POW_NEG; RING_1; RING_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD; EVEN_MULT; ADD_EQ_0] THEN
    MESON_TAC[EVEN];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_DET_PERMUTE_ROWS o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; PERMUTES_CYCLIC_N] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBST1_TAC(ARITH_RULE `n + m:num = m + n`) THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `i:num < m` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i:num < m ==> i + n < m + n`] THEN
    REWRITE_TAC[ARITH_RULE `~(i + n:num < n)`; ADD_SUB] THEN
    REWRITE_TAC[ARITH_RULE `n + i:num = i + n`];
    SUBGOAL_THEN `(i + n) MOD (m + n) = i - m` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `~(i:num < m) /\ i < m + n ==> i - m < n`] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i:num < m) ==> i - m + m = i /\
                                              m + i - m = i`]]]);;

let POLY_RESULTANT_LCONST = prove
 (`!(r:A ring) a q.
        a IN ring_carrier r /\ q IN ring_carrier(poly_ring r (:1))
        ==> poly_resultant r (poly_const r a) q = ring_pow r a (poly_deg r q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_resultant; POLY_DEG_CONST] THEN
  MP_TAC(ISPECL [`r:A ring`; `0`; `poly_deg r (q:(1->num)->A)`;
                 `poly_const r (a:A):(1->num)->A`; `q:(1->num)->A`; `a:A`;
                 `\i:num. a:A`] RING_DET_SYLVESTER_ROOTS) THEN
  ASM_REWRITE_TAC[LE_REFL; LT; EMPTY_GSPEC; RING_PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN `poly_const r (a:A) IN ring_carrier(poly_ring r (:1))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_CONST]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_POW]);;

let POLY_RESULTANT_RCONST = prove
 (`!(r:A ring) p b.
        p IN ring_carrier(poly_ring r (:1)) /\ b IN ring_carrier r
        ==> poly_resultant r p (poly_const r b) = ring_pow r b (poly_deg r p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[poly_resultant; POLY_DEG_CONST; ADD_CLAUSES; LT; SUB_0] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LE_REFL; SUB_REFL; COEFF_POLY_CONST] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* The resultant of a split polynomial: a^deg(q) times the product of the    *)
(* values of q at the roots; linear factors.                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_RESULTANT_ROOTS = prove
 (`!(r:A ring) p q a (x:num->A).
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\
        (!i. i < poly_deg r p ==> x i IN ring_carrier r) /\
        p = ring_mul (poly_ring r (:1)) (poly_const r a)
              (ring_product (poly_ring r (:1)) {i | i < poly_deg r p}
                 (\i. poly_sub r (poly_var r one) (poly_const r (x i))))
        ==> poly_resultant r p q =
            ring_mul r (ring_pow r a (poly_deg r q))
              (ring_product r {i | i < poly_deg r p}
                 (\i. poly_eval r q (x i)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_resultant] THEN
  MATCH_MP_TAC RING_DET_SYLVESTER_ROOTS THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[LE_REFL]);;

let POLY_RESULTANT_X_MINUS_MUL = prove
 (`!(r:A ring) c p q.
        c IN ring_carrier r /\
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\ ~(p = poly_0 r)
        ==> poly_resultant r
              (poly_mul r (poly_sub r (poly_var r one) (poly_const r c)) p) q =
            ring_mul r (poly_eval r q c) (poly_resultant r p q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_resultant] THEN
  ASM_SIMP_TAC[POLY_DEG_MUL_X_MINUS_A; RING_POLYNOMIAL] THEN
  MATCH_MP_TAC RING_DET_SYLVESTER_X_MINUS THEN
  ASM_REWRITE_TAC[LE_REFL]);;

let POLY_RESULTANT_X_MINUS = prove
 (`!(r:A ring) c q.
        c IN ring_carrier r /\ q IN ring_carrier(poly_ring r (:1))
        ==> poly_resultant r (poly_sub r (poly_var r one) (poly_const r c)) q =
            poly_eval r q c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `trivial_ring(r:A ring)` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [trivial_ring]) THEN
    MP_TAC(ISPECL [`r:A ring`; `q:(1->num)->A`; `c:A`] POLY_EVAL) THEN
    MP_TAC(ISPECL [`r:A ring`;
                   `poly_sub r (poly_var r one) (poly_const r (c:A))`;
                   `q:(1->num)->A`] POLY_RESULTANT_IN_CARRIER) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `c:A`; `poly_1 r:(1->num)->A`; `q:(1->num)->A`]
    POLY_RESULTANT_X_MINUS_MUL) THEN
  ASM_SIMP_TAC[POLY_MUL_RID; RING_POLYNOMIAL_IMP_POWERSERIES;
               RING_POLYNOMIAL_X_MINUS_A] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_1] THEN
    ASM_REWRITE_TAC[GSYM POLY_CONST_1; POLY_CONST_EQ_0; GSYM TRIVIAL_RING_10];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_1 r:A`; `q:(1->num)->A`]
    POLY_RESULTANT_LCONST) THEN
  ASM_REWRITE_TAC[POLY_CONST_1; RING_1; RING_POW_ONE] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[RING_MUL_RID; POLY_EVAL]);;

(* ------------------------------------------------------------------------- *)
(* The resultant is a combination u p + v q with deg u < deg q and deg v <   *)
(* deg p (the cofactors of the last column). Over a field, unless both p     *)
(* and q are zero, it vanishes iff p and q are not coprime.                  *)
(* ------------------------------------------------------------------------- *)

let POLY_RESULTANT_COMBINATION = prove
 (`!(r:A ring) p q.
        p IN ring_carrier(poly_ring r (:1)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        ~(poly_deg r p = 0 /\ poly_deg r q = 0)
        ==> ?u v. u IN ring_carrier(poly_ring r (:1)) /\
                  v IN ring_carrier(poly_ring r (:1)) /\
                  (poly_deg r u < poly_deg r q \/ u = poly_0 r) /\
                  (poly_deg r v < poly_deg r p \/ v = poly_0 r) /\
                  poly_add r (poly_mul r u p) (poly_mul r v q) =
                  poly_const r (poly_resultant r p q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[poly_resultant] THEN
  MP_TAC(ISPECL [`r:A ring`; `poly_deg r (p:(1->num)->A)`;
                 `poly_deg r (q:(1->num)->A)`; `p:(1->num)->A`;
                 `q:(1->num)->A`] RING_DET_SYLVESTER) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `m = poly_deg r (p:(1->num)->A)` THEN
  ABBREV_TAC `n = poly_deg r (q:(1->num)->A)` THEN
  ABBREV_TAC
   `f = \i. if i < n
            then poly_mul r (poly_pow r (poly_var r one) ((n - 1) - i))
                   (p:(1->num)->A)
            else poly_mul r (poly_pow r (poly_var r one) (((m + n) - 1) - i))
                   q` THEN
  SUBGOAL_THEN
   `!i. ring_polynomial r ((f:num->(1->num)->A) i) /\
        (i < m + n ==> poly_deg r (f i) < m + n)`
  (LABEL_TAC "f") THENL
   [X_GEN_TAC `i:num` THEN EXPAND_TAC "f" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_MUL; RING_POLYNOMIAL_POW;
                 RING_POLYNOMIAL_VAR; POLY_DEG_VARPOW_MUL] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `c = \i. ring_cofactor r {i | i < m + n}
              (\i j. coeff (((m + n) - 1) - j) ((f:num->(1->num)->A) i))
              i ((m + n) - 1)` THEN
  SUBGOAL_THEN `!i. (c:num->A) i IN ring_carrier r` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[RING_COFACTOR]; ALL_TAC] THEN
  EXISTS_TAC
   `ring_sum (poly_ring r (:1)) {i | i < n}
      (\i. poly_mul r (poly_const r ((c:num->A) i))
             (poly_pow r (poly_var r one) ((n - 1) - i)))` THEN
  EXISTS_TAC
   `ring_sum (poly_ring r (:1)) {i | i < m}
      (\i. poly_mul r (poly_const r ((c:num->A) (n + i)))
             (poly_pow r (poly_var r one) ((m - 1) - i)))` THEN
  ASM_SIMP_TAC[RING_SUM; POLY_DEG_RING_SUM_VARPOW_REV] THEN
  MP_TAC(ISPECL [`r:A ring`; `m:num`; `n:num`; `p:(1->num)->A`;
                 `q:(1->num)->A`; `c:num->A`] RING_SUM_SYLVESTER_ROWS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!i. (if i < n
         then poly_mul r (poly_pow r (poly_var r one) ((n - 1) - i))
                (p:(1->num)->A)
         else poly_mul r (poly_pow r (poly_var r one) (((m + n) - 1) - i))
                q) = f i`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_POLY_CONST] THEN X_GEN_TAC `d:num` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_POLYNOMIAL_IMP_POWERSERIES] THEN
  ASM_CASES_TAC `d:num < m + n` THENL
   [MP_TAC(ISPECL
     [`r:A ring`; `{i:num | i < m + n}`;
      `\i j. coeff (((m + n) - 1) - j) ((f:num->(1->num)->A) i)`;
      `(m + n) - 1`; `((m + n) - 1) - d`] RING_DET_ADJUGATE_COLUMNS) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; COEFF_IN_CARRIER_ALT;
                 ARITH_RULE `~(m = 0 /\ n = 0) ==> (m + n) - 1 < m + n`;
                 ARITH_RULE `d < m + n ==> ((m + n) - 1) - d < m + n`;
                 ARITH_RULE
                  `d < m + n ==> ((m + n) - 1) - (((m + n) - 1) - d) = d`;
                 ARITH_RULE `d < m + n ==> ((m + n) - 1 = ((m + n) - 1) - d <=>
                                            d = 0)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[];
    SUBGOAL_THEN `~(d = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `coeff d ((f:num->(1->num)->A) a) = ring_0 r` SUBST1_TAC THENL
     [MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_SIMP_TAC[] THEN
      REMOVE_THEN "f" (MP_TAC o SPEC `a:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[RING_MUL_RZERO]]]);;

let POLY_RESULTANT_EQ_0 = prove
 (`!(k:A ring) p q.
        field k /\
        p IN ring_carrier(poly_ring k (:1)) /\
        q IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k /\ q = poly_0 k)
        ==> (poly_resultant k p q = ring_0 k <=>
             ~ring_coprime (poly_ring k (:1)) (p,q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `p:(1->num)->A = poly_0 k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    REWRITE_TAC[poly_resultant; POLY_DEG_0] THEN
    MP_TAC(ISPECL [`k:A ring`; `0`; `poly_deg k (q:(1->num)->A)`;
                   `poly_0 k:(1->num)->A`; `q:(1->num)->A`; `ring_0 k:A`;
                   `\i:num. ring_0 k:A`] RING_DET_SYLVESTER_ROOTS) THEN
    ASM_REWRITE_TAC[LE_REFL; RING_0; LT; EMPTY_GSPEC; RING_PRODUCT_CLAUSES] THEN
    REWRITE_TAC[POLY_CONST_0; POLY_RING_CLAUSES] THEN
    SIMP_TAC[POLY_MUL_0; RING_POLYNOMIAL_1; RING_MUL_RID; RING_POW; RING_0] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RING_POW_ZERO] THEN
    MP_TAC(ISPECL [`k:A ring`; `(:1)`; `q:(1->num)->A`] POLY_DEG_EQ_0_UNIT) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
    REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2 POLY_CLAUSES))] THEN
    ASM_REWRITE_TAC[REWRITE_RULE[POLY_RING_CLAUSES]
     (ISPEC `poly_ring (k:A ring) (:1)` (CONJUNCT1 RING_COPRIME_0))] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  REWRITE_TAC[poly_resultant] THEN
  MATCH_MP_TAC RING_DET_SYLVESTER_EQ_0 THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of the discriminant. Its determinant times the leading   *)
(* coefficient is the Sylvester determinant of p and its derivative with the *)
(* formal degrees n and n - 1 (POLY_DISCRIMINANT_SYLVESTER), hence the       *)
(* resultant when the derivative has degree n - 1                            *)
(* (POLY_DISCRIMINANT_RESULTANT); under a scaling that preserves the degree  *)
(* it is homogeneous of degree 2n - 2 (POLY_DISCRIMINANT_CMUL).              *)
(* ------------------------------------------------------------------------- *)

let POLY_DISCRIMINANT_IN_CARRIER = prove
 (`!(r:A ring) p. poly_discriminant r p IN ring_carrier r`,
  SIMP_TAC[poly_discriminant; RING_MUL; RING_POW; RING_NEG; RING_1;
           RING_DET]);;

let POLY_DISCRIMINANT_HOMOMORPHISM = prove
 (`!(f:A->B) r r' p.
        ring_homomorphism(r,r') f /\ p IN ring_carrier(poly_ring r (:1)) /\
        poly_deg r' (f o p) = poly_deg r p
        ==> f(poly_discriminant r p) = poly_discriminant r' (f o p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_discriminant] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
   [RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1; RING_HOMOMORPHISM_NEG;
    RING_HOMOMORPHISM_POW; RING_HOMOMORPHISM_MUL;
    RING_HOMOMORPHISM_RING_OF_NUM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[RING_POW; RING_NEG; RING_1; RING_DET] THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_HOMOMORPHISM o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; RING_1; RING_OF_NUM; COEFF_IN_CARRIER_ALT;
                 RING_POLYNOMIAL_POLY_DERIV];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `f:A->B`; `p:(1->num)->A`]
    POLY_DERIV_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[COEFF_COMPOSE]));;

let POLY_DISCRIMINANT_SYLVESTER = prove
 (`!(r:A ring) p.
        p IN ring_carrier(poly_ring r (:1)) /\ 1 <= poly_deg r p
        ==> ring_mul r (coeff (poly_deg r p) p) (poly_discriminant r p) =
            ring_mul r
             (ring_pow r (ring_neg r (ring_1 r))
                ((poly_deg r p * (poly_deg r p - 1)) DIV 2))
             (ring_det r {i | i < poly_deg r p + (poly_deg r p - 1)}
               (\i j. if i < poly_deg r p - 1
                      then if i <= j /\ j <= i + poly_deg r p
                           then coeff ((poly_deg r p + i) - j) p else ring_0 r
                      else if i - (poly_deg r p - 1) <= j /\ j <= i
                           then coeff (i - j) (poly_deriv r p)
                           else ring_0 r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[poly_discriminant] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  ABBREV_TAC `n = poly_deg r (p:(1->num)->A)` THEN
  SUBGOAL_THEN `n + (n - 1) = 2 * n - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`r:A ring`; `{i:num | i < 2 * n - 1}`;
    `\j:num. if j = 0 then coeff n (p:(1->num)->A) else ring_1 r`;
    `\i j. if j = 0
           then if i = 0 then ring_1 r
                else if i = n - 1 then ring_of_num r n else ring_0 r
           else if i < n - 1
           then if i <= j /\ j <= i + n
                then coeff ((n + i) - j) p else ring_0 (r:A ring)
           else if i - (n - 1) <= j /\ j <= i
           then coeff (i - j) (poly_deriv r p) else ring_0 r`]
   RING_DET_COLUMNS_MUL) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; RING_1; RING_OF_NUM; COEFF_IN_CARRIER_ALT;
                 RING_POLYNOMIAL_POLY_DERIV];
    ALL_TAC] THEN
  REWRITE_TAC[RING_PRODUCT_DELTA; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 0 < 2 * n - 1`; COEFF_IN_CARRIER_ALT] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
   `y = ring_mul (r:A ring) x a
    ==> ring_mul r a (ring_mul r s x) = ring_mul r s y`)) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_DET; RING_POW; RING_NEG; RING_1; COEFF_IN_CARRIER_ALT];
    FIRST_X_ASSUM(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_DET_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_0; COEFF_IN_CARRIER_ALT;
                 RING_POLYNOMIAL_POLY_DERIV]] THEN
  REWRITE_TAC[LE_0; LE_REFL; ADD_CLAUSES; SUB_0; ARITH_RULE `i <= 0 <=> i = 0`;
              ARITH_RULE `i - m <= 0 <=> i <= m`] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES; LE_0] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LID; COEFF_IN_CARRIER_ALT; COEFF_POLY_DERIV] THEN
    SUBGOAL_THEN `n = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH; RING_OF_NUM_1] THEN
    ASM_SIMP_TAC[RING_MUL_LID; COEFF_IN_CARRIER_ALT];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `~(i = n - 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[RING_MUL_LZERO; COEFF_IN_CARRIER_ALT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `i = n - 1` THEN ASM_REWRITE_TAC[LE_REFL] THENL
   [ASM_SIMP_TAC[COEFF_POLY_DERIV; ARITH_RULE `1 <= n ==> n - 1 + 1 = n`];
    SUBGOAL_THEN `~(i <= n - 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[RING_MUL_LZERO; COEFF_IN_CARRIER_ALT]]]);;

let POLY_DISCRIMINANT_RESULTANT = prove
 (`!(r:A ring) p.
        p IN ring_carrier(poly_ring r (:1)) /\ 1 <= poly_deg r p /\
        poly_deg r (poly_deriv r p) = poly_deg r p - 1
        ==> ring_mul r (coeff (poly_deg r p) p) (poly_discriminant r p) =
            ring_mul r
             (ring_pow r (ring_neg r (ring_1 r))
                ((poly_deg r p * (poly_deg r p - 1)) DIV 2))
             (poly_resultant r p (poly_deriv r p))`,
  SIMP_TAC[POLY_DISCRIMINANT_SYLVESTER] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[poly_resultant]);;

let POLY_DISCRIMINANT_CMUL = prove
 (`!(r:A ring) c p.
        c IN ring_carrier r /\ p IN ring_carrier(poly_ring r (:1)) /\
        poly_deg r (poly_mul r (poly_const r c) p) = poly_deg r p
        ==> poly_discriminant r (poly_mul r (poly_const r c) p) =
            ring_mul r (ring_pow r c (2 * poly_deg r p - 2))
                       (poly_discriminant r p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_discriminant] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  ABBREV_TAC `n = poly_deg r (p:(1->num)->A)` THEN
  MP_TAC(ISPECL
   [`r:A ring`; `{i:num | i < 2 * n - 1}`;
    `\j:num. if j = 0 then ring_1 r else (c:A)`;
    `\i j. if j = 0
           then if i = 0 then ring_1 r
                else if i = n - 1 then ring_of_num r n else ring_0 r
           else if i < n - 1
           then if i <= j /\ j <= i + n
                then coeff ((n + i) - j) p else ring_0 (r:A ring)
           else if i - (n - 1) <= j /\ j <= i
           then coeff (i - j) (poly_deriv r p) else ring_0 r`]
   RING_DET_COLUMNS_MUL) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; RING_1; RING_OF_NUM; COEFF_IN_CARRIER_ALT;
                 RING_POLYNOMIAL_POLY_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product r {j | j < 2 * n - 1} (\j. if j = 0 then ring_1 r else c) =
    ring_pow r (c:A) (2 * n - 2)`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_product r ({j | j < 2 * n - 1} DELETE 0)
        (\j. if j = 0 then ring_1 r else (c:A))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_SUPERSET THEN SET_TAC[]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_product r ({j | j < 2 * n - 1} DELETE 0) (\j. c:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN SIMP_TAC[IN_DELETE];
      ASM_SIMP_TAC[RING_PRODUCT_CONST; FINITE_DELETE; FINITE_NUMSEG_LT] THEN
      AP_TERM_TAC THEN
      SIMP_TAC[CARD_DELETE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
      ARITH_TAC];
    DISCH_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
   `y = ring_mul (r:A ring) x d
    ==> ring_mul r s y = ring_mul r d (ring_mul r s x)`)) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_DET; RING_POW; RING_NEG; RING_1]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    SIMP_TAC[RING_MUL_RID; RING_0; RING_1; RING_OF_NUM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_DERIV_CMUL; RING_POLYNOMIAL_IMP_POWERSERIES] THEN
  ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_POLYNOMIAL_IMP_POWERSERIES;
               RING_POLYNOMIAL_POLY_DERIV] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_SYM; COEFF_IN_CARRIER_ALT;
               RING_POLYNOMIAL_POLY_DERIV]);;

(* ------------------------------------------------------------------------- *)
(* The discriminant of a split polynomial a prod_(i<n) (X - x(i)) is         *)
(* a^(2n-2) prod_(i<j) (x(i) - x(j))^2, over any ring: the derivative at     *)
(* x(i) is the product of the x(i) - x(j), j <> i, and the product of all    *)
(* these differences is (-1)^(n(n-1)/2) times the product of the squares.    *)
(* ------------------------------------------------------------------------- *)

let POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS = prove
 (`!(r:A ring) (x:K->A) s i.
        FINITE s /\ (!j. j IN s ==> x j IN ring_carrier r) /\ i IN s
        ==> poly_eval r
             (poly_deriv r
               (ring_product (poly_ring r (:1)) s
                  (\j. poly_sub r (poly_var r one) (poly_const r (x j)))))
             (x i) =
            ring_product r (s DELETE i) (\j. ring_sub r (x i) (x j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`poly_ring (r:A ring) (:1)`;
    `\j. poly_sub r (poly_var r one) (poly_const r ((x:K->A) j))`;
    `s:K->bool`; `i:K`] RING_PRODUCT_DELETE) THEN
  ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC
   `q = ring_product (poly_ring r (:1)) (s DELETE i)
          (\j. poly_sub r (poly_var r one) (poly_const r ((x:K->A) j)))` THEN
  SUBGOAL_THEN `ring_polynomial r (q:(1->num)->A)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:K->A) i IN ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[POLY_RING_CLAUSES] THEN
  ASM_SIMP_TAC[POLY_DERIV_MUL; RING_POLYNOMIAL_IMP_POWERSERIES;
               RING_POLYNOMIAL_X_MINUS_A] THEN
  ASM_SIMP_TAC[POLY_DERIV_SUB; RING_POWERSERIES_VAR; RING_POWERSERIES_CONST;
               POLY_DERIV_VAR; POLY_DERIV_CONST] THEN
  ASM_SIMP_TAC[POLY_EVAL_ADD; POLY_EVAL_MUL; POLY_EVAL_SUB; RING_POLYNOMIAL_MUL;
               RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_CONST; RING_POLYNOMIAL_0;
               RING_POLYNOMIAL_X_MINUS_A; RING_POLYNOMIAL_POLY_DERIV; RING_1;
               RING_POLYNOMIAL_VAR; POLY_EVAL_CONST; POLY_EVAL_0;
               POLY_EVAL_VAR; RING_SUB_REFL; RING_0] THEN
  ASM_SIMP_TAC[RING_SUB_RZERO; RING_MUL_LZERO; RING_MUL_LID; POLY_EVAL; RING_1;
               RING_ADD_RZERO; RING_MUL] THEN
  EXPAND_TAC "q" THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_RING_PRODUCT o
    lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; POLY_X_MINUS_A_IN_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
  ASM_SIMP_TAC[IN_DELETE; POLY_EVAL_SUB; RING_POLYNOMIAL_VAR;
               RING_POLYNOMIAL_CONST; POLY_EVAL_VAR; POLY_EVAL_CONST]);;

let RING_PRODUCT_DIFFERENCES = prove
 (`!(r:A ring) (x:num->A) n.
        (!i. i < n ==> x i IN ring_carrier r)
        ==> ring_product r {i | i < n}
              (\i. ring_product r ({j | j < n} DELETE i)
                                 (\j. ring_sub r (x i) (x j))) =
            ring_mul r
             (ring_pow r (ring_neg r (ring_1 r)) ((n * (n - 1)) DIV 2))
             (ring_product r {(i,j) | i < j /\ j < n}
                (\(i,j). ring_pow r (ring_sub r (x i) (x j)) 2))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; RING_PRODUCT_CLAUSES] THEN
    REWRITE_TAC[SET_RULE `{(i:num,j:num) | F} = {}`; RING_PRODUCT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ring_pow] THEN
    SIMP_TAC[RING_MUL_LID; RING_1];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LT]; DISCH_TAC] THEN
  REWRITE_TAC[ADD1] THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
  SUBGOAL_THEN
   `(!i. i < n ==> (x:num->A) i IN ring_carrier r) /\ x n IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!i. i < n + 1 ==> (x:num->A) i IN ring_carrier r` THEN
    MESON_TAC[ARITH_RULE `i < n ==> i < n + 1`; ARITH_RULE `n < n + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{i | i < n + 1} = n INSERT {i | i < n} /\
    {(i,j) | i < j /\ j < n + 1} =
    {(i,j) | i < j /\ j < n} UNION IMAGE (\i. (i,n)) {i | i < n}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_UNION; IN_ELIM_PAIR_THM;
                IN_IMAGE; PAIR_EQ; IN_ELIM_THM; IN_INSERT] THEN
    CONJ_TAC THENL
     [ARITH_TAC;
      MESON_TAC[ARITH_RULE
       `a < b /\ b < n + 1 <=> a < b /\ b < n \/ a < n /\ b = n`]];
    ALL_TAC] THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  SIMP_TAC[RING_PRODUCT] THEN
  SUBGOAL_THEN
   `(n INSERT {j | j < n:num}) DELETE n = {j | j < n} /\
    (!i. i < n ==> (n INSERT {j | j < n}) DELETE i =
                   n INSERT ({j | j < n} DELETE i))`
  (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; IN_DELETE] THEN
    CONJ_TAC THENL [ARITH_TAC; REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r (ring_product r {j | j < n} (\j. ring_sub r (x n) (x j)))
      (ring_product r {i | i < n}
         (\i. ring_mul r (ring_sub r ((x:num->A) i) (x n))
                (ring_product r ({j | j < n} DELETE i)
                   (\j. ring_sub r (x i) (x j)))))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG_LT;
             IN_DELETE; IN_ELIM_THM; LT_REFL] THEN
    ASM_SIMP_TAC[RING_SUB];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_MUL o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUB; RING_PRODUCT] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ring_product r {j | j < n} (\j. ring_sub r ((x:num->A) n) (x j)) =
    ring_mul r (ring_pow r (ring_neg r (ring_1 r)) n)
               (ring_product r {i | i < n} (\i. ring_sub r (x i) (x n)))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_product r {j | j < n}
        (\j. ring_mul r (ring_neg r (ring_1 r))
                        (ring_sub r ((x:num->A) j) (x n)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_sub (r:A ring) a b =
        ring_mul r (ring_neg r (ring_1 r)) (ring_sub r b a)`)) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[RING_PRODUCT_MUL; FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUB;
                   RING_NEG; RING_1; RING_PRODUCT_CONST; CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {(i,j) | i < j /\ j < n} /\
    DISJOINT {(i,j) | i < j /\ j < n} (IMAGE (\i:num. (i,n)) {i | i < n})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{i:num | i < n} CROSS {j:num | j < n}` THEN
      SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
                  IN_ELIM_THM] THEN
      ARITH_TAC;
      REWRITE_TAC[DISJOINT; EXTENSION; FORALL_PAIR_THM; IN_INTER;
                  IN_ELIM_PAIR_THM; IN_IMAGE; PAIR_EQ; NOT_IN_EMPTY;
                  IN_ELIM_THM] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRODUCT_UNION; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o
    rand o rand o rand o snd) THEN
  ANTS_TAC THENL [SIMP_TAC[PAIR_EQ]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[RING_PRODUCT_POW; FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUB] THEN
  SUBGOAL_THEN `((n + 1) * ((n + 1) - 1)) DIV 2 = (n * (n - 1)) DIV 2 + n`
  SUBST1_TAC THENL
   [REWRITE_TAC[ADD_SUB] THEN
    SUBGOAL_THEN `(n + 1) * n = n * 2 + n * (n - 1)` SUBST1_TAC THENL
     [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUC_SUB1; ARITH] THEN
      ARITH_TAC;
      SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `u = ring_pow (r:A ring) (ring_neg r (ring_1 r)) ((n * (n - 1)) DIV 2)` THEN
  ABBREV_TAC `v = ring_pow (r:A ring) (ring_neg r (ring_1 r)) n` THEN
  ABBREV_TAC
   `y = ring_product r {i | i < n} (\i. ring_sub r ((x:num->A) i) (x n))` THEN
  ABBREV_TAC
   `z = ring_product r {(i,j) | i < j /\ j < n}
          (\(i,j). ring_pow r (ring_sub r ((x:num->A) i) (x j)) 2)` THEN
  SUBGOAL_THEN
   `u IN ring_carrier r /\ v IN ring_carrier r /\ y IN ring_carrier r /\
    (z:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"; "y"; "z"] THEN
    SIMP_TAC[RING_POW; RING_NEG; RING_1; RING_PRODUCT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_POW_ADD; RING_NEG; RING_1] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul (r:A ring) (ring_mul r v y) (ring_mul r y (ring_mul r u z)) =
    ring_mul r (ring_mul r u v) (ring_mul r z (ring_pow r y 2))`) THEN
  ASM_REWRITE_TAC[]);;

(* The square of the ordered product is the signed product of all           *)
(* differences, as used in the discriminant of a power basis.                *)
let RING_PRODUCT_DIFFERENCES_SQUARE = prove
 (`!(r:A ring) x n.
        (!i. i < n ==> x i IN ring_carrier r)
        ==> ring_pow r (ring_product r {j | j < n}
                          (\j. ring_product r {i | i < j}
                                 (\i. ring_sub r (x j) (x i)))) 2 =
            ring_mul r
              (ring_pow r (ring_neg r (ring_1 r)) ((n * (n - 1)) DIV 2))
              (ring_product r {i | i < n}
                 (\i. ring_product r ({j | j < n} DELETE i)
                        (\j. ring_sub r (x i) (x j))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_PRODUCT_DIFFERENCES] THEN
  SIMP_TAC[RING_MUL_ASSOC; RING_POW; RING_NEG; RING_1; RING_PRODUCT;
           GSYM RING_POW_ADD; GSYM MULT_2; RING_POW_MUL;
           RING_RULE `ring_pow r (ring_neg r (ring_1 r)) 2 = ring_1 r:A`;
           RING_POW_ONE; RING_MUL_LID] THEN
  REWRITE_TAC[RING_PRODUCT_PAIRS_LT] THEN
  TRANS_TAC EQ_TRANS
   `ring_product r {j | j < n}
      (\j. ring_pow r (ring_product r {i | i < j}
                         (\i. ring_sub r ((x:num->A) j) (x i))) 2)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_POW THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; RING_PRODUCT];
    MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_product r {i | i < j}
      (\i. ring_pow r (ring_sub r ((x:num->A) j) (x i)) 2)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_POW THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_SUB THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_pow r (ring_sub r a b) 2 =
      ring_pow r (ring_sub r b (a:A)) 2`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let POLY_DISCRIMINANT_ROOTS = prove
 (`!(r:A ring) p a (x:num->A).
        p IN ring_carrier(poly_ring r (:1)) /\ a IN ring_carrier r /\
        (!i. i < poly_deg r p ==> x i IN ring_carrier r) /\
        p = ring_mul (poly_ring r (:1)) (poly_const r a)
              (ring_product (poly_ring r (:1)) {i | i < poly_deg r p}
                 (\i. poly_sub r (poly_var r one) (poly_const r (x i))))
        ==> poly_discriminant r p =
            ring_mul r (ring_pow r a (2 * poly_deg r p - 2))
              (ring_product r {(i,j) | i < j /\ j < poly_deg r p}
                 (\(i,j). ring_pow r (ring_sub r (x i) (x j)) 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `trivial_ring(r:A ring)` THENL
   [FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [trivial_ring]) THEN
    MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`]
      POLY_DISCRIMINANT_IN_CARRIER) THEN
    SUBGOAL_THEN
     `ring_mul r (ring_pow r a (2 * poly_deg r (p:(1->num)->A) - 2))
        (ring_product r {(i,j) | i < j /\ j < poly_deg r p}
           (\(i,j). ring_pow r (ring_sub r ((x:num->A) i) (x j)) 2)) IN
      ring_carrier r`
    MP_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC[RING_POW; RING_PRODUCT];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `ring_carrier r = {ring_0(r:A ring)}`; IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = poly_deg r (p:(1->num)->A)` THEN
  ABBREV_TAC
   `p0 = ring_product (poly_ring r (:1)) {i | i < n}
          (\i. poly_sub r (poly_var r one) (poly_const r ((x:num->A) i)))` THEN
  SUBGOAL_THEN
   `p0 IN ring_carrier(poly_ring r (:1)) /\ ring_polynomial r p0 /\
    monic r (p0:(1->num)->A) /\ poly_deg r p0 = n`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN REWRITE_TAC[RING_PRODUCT; RING_POLYNOMIAL] THEN
    SUBGOAL_THEN
     `!i. i IN {i | i < n}
          ==> ring_polynomial r
                (poly_sub r (poly_var r one) (poly_const r ((x:num->A) i))) /\
              monic r (poly_sub r (poly_var r one) (poly_const r (x i))) /\
              poly_deg r (poly_sub r (poly_var r one) (poly_const r (x i))) = 1`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL_X_MINUS_A; MONIC_X_MINUS_A;
                   POLY_DEG_X_MINUS_A];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MONIC_POLY_PRODUCT; POLY_DEG_PRODUCT_MONIC;
                 FINITE_NUMSEG_LT] THEN
    TRANS_TAC EQ_TRANS `nsum {i | i < n} (\i:num. 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[];
      SIMP_TAC[NSUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; MULT_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `coeff n (p0:(1->num)->A) = ring_1 r` ASSUME_TAC THENL
   [ASM_MESON_TAC[monic]; ALL_TAC] THEN
  SUBGOAL_THEN `p = poly_mul r (poly_const r a) (p0:(1->num)->A)` ASSUME_TAC
  THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[POLY_RING_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `p0:(1->num)->A`]
    POLY_DISCRIMINANT_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[poly_discriminant] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LT; EMPTY_GSPEC; SET_RULE `{(i:num,j:num) | F} = {}`;
                RING_DET_EMPTY; RING_PRODUCT_CLAUSES; ring_pow] THEN
    SIMP_TAC[RING_MUL_LID; RING_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p0:(1->num)->A`] POLY_DISCRIMINANT_SYLVESTER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[RING_MUL_LID; POLY_DISCRIMINANT_IN_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `n - 1`; `p0:(1->num)->A`;
                 `poly_deriv r (p0:(1->num)->A)`; `ring_1 (r:A ring)`;
                 `x:num->A`] RING_DET_SYLVESTER_ROOTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLY_DERIV_IN_CARRIER; RING_1] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `p0:(1->num)->A`] POLY_DEG_DERIV_LE) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[POLY_CONST_1; POLY_RING_CLAUSES] THEN
      ASM_SIMP_TAC[POLY_MUL_LID; RING_POLYNOMIAL_IMP_POWERSERIES]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[RING_POW_ONE] THEN
  SIMP_TAC[RING_MUL_LID; RING_PRODUCT] THEN
  SUBGOAL_THEN
   `ring_product r {i | i < n} (\i. poly_eval r (poly_deriv r p0) (x i)) =
    ring_product r {i | i < n}
      (\i. ring_product r ({j | j < n} DELETE i)
             (\j. ring_sub r ((x:num->A) i) (x j)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "p0" THEN
    MATCH_MP_TAC POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRODUCT_DIFFERENCES] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
   `ring_mul (r:A ring) u u = ring_1 r
    ==> ring_mul r u (ring_mul r u z) = z`)) THEN
  REWRITE_TAC[RING_PRODUCT] THEN
  SIMP_TAC[GSYM RING_MUL_POW; RING_NEG; RING_1; RING_POW] THEN
  SIMP_TAC[RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG; RING_1; RING_MUL_LID;
           RING_NEG_NEG; RING_POW_ONE]);;

(* The discriminant of a * prod_(i<n) (X - x_i) is the square of a^(n-1)     *)
(* times the Vandermonde determinant det(x_i^j), whose value is the product  *)
(* of the x_j - x_i for i < j (RING_DET_VANDERMONDE).                        *)
let POLY_DISCRIMINANT_VANDERMONDE = prove
 (`!(r:A ring) p a (x:num->A).
        p IN ring_carrier(poly_ring r (:1)) /\ a IN ring_carrier r /\
        (!i. i < poly_deg r p ==> x i IN ring_carrier r) /\
        p = ring_mul (poly_ring r (:1)) (poly_const r a)
              (ring_product (poly_ring r (:1)) {i | i < poly_deg r p}
                 (\i. poly_sub r (poly_var r one) (poly_const r (x i))))
        ==> poly_discriminant r p =
            ring_pow r
             (ring_mul r (ring_pow r a (poly_deg r p - 1))
               (ring_det r {i | i < poly_deg r p} (\i j. ring_pow r (x i) j)))
             2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP POLY_DISCRIMINANT_ROOTS) THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  ABBREV_TAC `n = poly_deg r (p:(1->num)->A)` THEN
  ASM_SIMP_TAC[RING_DET_VANDERMONDE; RING_PRODUCT_PAIRS_LT] THEN
  SUBGOAL_THEN
   `!j. j < n
        ==> ring_product r {i | i < j}
              (\i. ring_pow r (ring_sub r ((x:num->A) i) (x j)) 2) =
            ring_pow r (ring_product r {i | i < j}
                          (\i. ring_sub r (x j) (x i))) 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!i. i < j ==> (x:num->A) i IN ring_carrier r` ASSUME_TAC
    THENL [ASM_MESON_TAC[LT_TRANS]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_PRODUCT_POW o rand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_SUB] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_RULE
     `ring_pow (r:A ring) (ring_sub r a b) 2 = ring_pow r (ring_sub r b a) 2`];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r (ring_pow r a (2 * n - 2))
      (ring_product r {j | j < n}
        (\j. ring_pow r (ring_product r {i | i < j}
                          (\i. ring_sub r ((x:num->A) j) (x i))) 2))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_POW o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_PRODUCT] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_MUL_POW; RING_POW; RING_PRODUCT; RING_POW_POW] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Over a field the discriminant of a polynomial of positive degree vanishes *)
(* iff the polynomial is not separable, i.e. not coprime to its derivative.  *)
(* ------------------------------------------------------------------------- *)

let POLY_DISCRIMINANT_EQ_0 = prove
 (`!(k:A ring) p.
        field k /\ p IN ring_carrier(poly_ring k (:1)) /\ 1 <= poly_deg k p
        ==> (poly_discriminant k p = ring_0 k <=> ~poly_separable k p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p:(1->num)->A = poly_0 k)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[POLY_DEG_0]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN `~(coeff (poly_deg k p) (p:(1->num)->A) = ring_0 k)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_TOP_EQ_0; RING_POLYNOMIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`] POLY_DISCRIMINANT_SYLVESTER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `coeff (poly_deg k p) (p:(1->num)->A)`;
                 `poly_discriminant k (p:(1->num)->A)`]
    INTEGRAL_DOMAIN_MUL_EQ_0) THEN
  ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL;
               POLY_DISCRIMINANT_IN_CARRIER] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_DOMAIN_MUL_EQ_0 o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_POW; RING_NEG; RING_1; RING_DET] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_POW_EQ_0; RING_NEG; RING_1; RING_NEG_EQ_0] THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL] THEN REWRITE_TAC[poly_separable] THEN
  MATCH_MP_TAC RING_DET_SYLVESTER_EQ_0 THEN
  ASM_SIMP_TAC[POLY_DERIV_IN_CARRIER; POLY_DEG_DERIV_LE; RING_POLYNOMIAL]);;

