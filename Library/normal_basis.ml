(* ========================================================================= *)
(* The normal basis theorem.                                                 *)
(*                                                                           *)
(* For a finite Galois extension (k,l) h with Galois group G, some element x *)
(* of l has its conjugates f x, f IN G, as a basis of l over k (Lang,        *)
(* Algebra, VI 13.1): every y in l is a unique combination of the f x with   *)
(* coefficients in k (NORMAL_BASIS_THEOREM). Equivalently the f x are        *)
(* distinct and form a ring_basis (NORMAL_BASIS_RING_BASIS), and every       *)
(* enumeration of G gives a free basis (NORMAL_BASIS_FREE_BASIS, with        *)
(* free_basis of Library/ring_det.ml). For finite fields with q = |k|        *)
(* elements: some x has x, x^q, ..., x^(q^(n-1)) as a free basis, n = [l:k]  *)
(* (FINITE_FIELD_NORMAL_BASIS).                                              *)
(*                                                                           *)
(* Criteria for a normal element x of a finite Galois extension: the f x are *)
(* independent over k iff they are a basis (NORMAL_BASIS_INDEPENDENT) iff    *)
(* the determinant of the array (inverse f o g) x, f, g IN G, is nonzero     *)
(* (NORMAL_BASIS_DETERMINANT; the direction from the determinant needs only  *)
(* a finite extension: NORMAL_BASIS_DET_INDEPENDENT).                        *)
(*                                                                           *)
(* The cyclic vector theorem (CYCLIC_VECTOR_EXISTS of                        *)
(* Library/fieldtheory.ml: if t^d is a k-combination of 1, t, ..., t^(d-1)   *)
(* and these d maps are independent over k, then z, t z, ..., t^(d-1) z are  *)
(* independent for some z) gives the case of cyclic Galois groups.           *)
(*                                                                           *)
(* Routes. Cyclic Galois groups, in particular all finite fields: a          *)
(* generator s of G has s^n = 1, n = [l:k], and 1, s, ..., s^(n-1) are       *)
(* independent over l by Dedekind (GALOIS_GROUP_INDEPENDENT), so the cyclic  *)
(* vector theorem applies (NORMAL_BASIS_CYCLIC). Infinite base fields, an    *)
(* argument in one variable: for a primitive element a let Q_p(X) be the     *)
(* product of the X - r a over r IN G, r <> p, and P(X) the determinant of   *)
(* the Q_(inverse f o g)(X), f, g IN G. At X = a the array is diagonal with  *)
(* nonzero entries, so P is a nonzero polynomial with finitely many roots,   *)
(* and some b = h(c) is not a root. Since G fixes b, f maps w = Q_1(b) to    *)
(* Q_f(b), so the determinant of the (inverse f o g) w is P(b), which is     *)
(* nonzero (NORMAL_BASIS_INFINITE).                                          *)
(*                                                                           *)
(* Uses: Library/galois.ml (galois_group, galois_extension, Dedekind         *)
(* independence, Galois groups of finite fields), Library/fieldtheory.ml     *)
(* (PRIMITIVE_ELEMENT_THEOREM, ring_basis, FREE_BASIS_FIELD,                 *)
(* CYCLIC_VECTOR_EXISTS), Library/ring_det.ml (determinants, free_basis),    *)
(* Library/ringtheory.ml (polynomials).                                      *)
(* ========================================================================= *)

needs "Library/galois.ml";;

(* ------------------------------------------------------------------------- *)
(* Normal elements. For a finite Galois extension the conjugates f x,        *)
(* f IN G, are [l:k] = |G| many, so they form a basis as soon as they are    *)
(* independent over k (then they are distinct). They are independent         *)
(* exactly when the determinant of the (inverse f o g) x is nonzero: a       *)
(* dependency over k gives a column dependency, and conversely a row         *)
(* dependency e gives the combination of the inverse f with coefficients     *)
(* e(f), which vanishes on the span of the f x, so on l, against Dedekind.   *)
(* ------------------------------------------------------------------------- *)

let NORMAL_BASIS_INDEPENDENT = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        x IN ring_carrier l /\
        (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                  ==> c f IN ring_carrier k) /\
             ring_sum l (group_carrier(galois_group(k,l) h))
               (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
             ==> !f. f IN group_carrier(galois_group(k,l) h)
                     ==> c f = ring_0 k)
        ==> (!f g. f IN group_carrier(galois_group(k,l) h) /\
                   g IN group_carrier(galois_group(k,l) h) /\ f x = g x
                   ==> f = g) /\
            ring_basis (k,l) h
              (IMAGE (\f. f x) (group_carrier(galois_group(k,l) h))) /\
            (!y. y IN ring_carrier l
                 ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                              ==> c f IN ring_carrier k) /\
                         y = ring_sum l (group_carrier(galois_group(k,l) h))
                               (\f. ring_mul l (h(c f)) (f x)))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ind")))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_NEG) THEN
  SUBGOAL_THEN
   `FINITE(G:(B->B)->bool) /\ CARD G = extension_degree(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
    ASM_MESON_TAC[GALOIS_EXTENSION_EQ_CARD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
    (!c. c IN ring_carrier k ==> (h:A->B) c IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[GALOIS_GROUP_IN_CARRIER] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g. f IN G /\ g IN G /\ (f:B->B) x = g x ==> f = g`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "ind" (MP_TAC o SPEC
     `\u:B->B. if u = f then ring_1 k
               else if u = g then ring_neg k (ring_1 k) else ring_0 k:A`) THEN
    REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      SIMP_TAC[RING_1; RING_NEG; RING_0];
      ALL_TAC;
      DISCH_THEN(MP_TAC o SPEC `f:B->B`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[FIELD_NONTRIVIAL]] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l G
        (\u. ring_add l (if u = f then (f:B->B) x else ring_0 l)
                        (if u = g then ring_neg l (g x) else ring_0 l))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `u:B->B` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      ASM_CASES_TAC `u:B->B = f` THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[RING_MUL_LID; RING_ADD_RZERO; RING_1];
        ALL_TAC] THEN
      ASM_CASES_TAC `u:B->B = g` THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[RING_1; RING_MUL_LNEG; RING_MUL_LID;
                     RING_ADD_LZERO; RING_NEG];
        ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_LZERO; RING_0]];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_ADD o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0; RING_NEG];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[RING_SUM_DELTA] THEN
    ASM_SIMP_TAC[RING_ADD_RNEG; RING_NEG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ring_independent (k,l) (h:A->B) (IMAGE (\f:B->B. f x) G)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_INDEPENDENT_FINITE; FINITE_IMAGE] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
    X_GEN_TAC `c:B->A` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN STRIP_TAC THEN
    USE_THEN "ind" (MP_TAC o BETA_RULE o SPEC `\f:B->B. (c:B->A)(f x)`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `ring_sum l (IMAGE (\f:B->B. f x) G) (\y. ring_mul l (h((c:B->A) y)) y) =
      ring_0 l` THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o
      lhand o lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_basis (k,l) (h:A->B) (IMAGE (\f:B->B. f x) G)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_MATROID_BASIS] THEN
    MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN
    ASM_SIMP_TAC[RING_MATROID_INDEPENDENT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_EXTENSION_RING_MATROID]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\f:B->B. f x`; `G:(B->B)->bool`] CARD_IMAGE_INJ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `matroid_finite_dimensional (ring_matroid (k,l) (h:A->B))`
    MP_TAC THENL
     [ASM_MESON_TAC[FINITE_EXTENSION_RING_MATROID]; ALL_TAC] THEN
    SIMP_TAC[extension_degree; LE_REFL];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `ring_basis (k,l) (h:A->B) (IMAGE (\f:B->B. f x) G)`) THEN
  REWRITE_TAC[ring_basis; ring_spanning] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `IMAGE (\f:B->B. f x) G`] RING_SPAN_FINITE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; FORALL_IN_IMAGE];
    DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:B` o GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:B->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\f:B->B. (c:B->A)(f x)` THEN ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF]);;

let NORMAL_BASIS_DET_INDEPENDENT = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l /\
        ~(ring_det l (group_carrier(galois_group(k,l) h))
                     (\f g. (inverse f o g) x) = ring_0 l)
        ==> !c. (!f. f IN group_carrier(galois_group(k,l) h)
                     ==> c f IN ring_carrier k) /\
                ring_sum l (group_carrier(galois_group(k,l) h))
                  (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                ==> !f. f IN group_carrier(galois_group(k,l) h)
                        ==> c f = ring_0 k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  SUBGOAL_THEN `FINITE(group_carrier(galois_group(k,l) (h:A->B)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_GALOIS_GROUP]; ALL_TAC] THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  SUBGOAL_THEN
   `(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
    (!f. f IN G ==> inverse f IN G) /\
    (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
    (!f c. f IN G /\ c IN ring_carrier k ==> f((h:A->B) c) = h c) /\
    (!c. c IN ring_carrier k ==> h c IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    REWRITE_TAC[GALOIS_GROUP_IN_CARRIER; GALOIS_GROUP_INVERSE;
                GALOIS_GROUP_RING_HOMOMORPHISM; GALOIS_GROUP_FIXES] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `c:(B->B)->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  UNDISCH_TAC
   `~(ring_det l G (\f g:B->B. (inverse f o g) (x:B)) = ring_0 l)` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RING_DET_DEPENDENT_COLUMNS THEN
  EXISTS_TAC `\f:B->B. (h:A->B)(c f)` THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; o_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `g:B->B` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((c:(B->B)->A) g = ring_0 k)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    UNDISCH_TAC `(h:A->B)(ring_0 k) = ring_0 l` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
      [ring_monomorphism]) THEN
    ASM_SIMP_TAC[RING_0];
    ALL_TAC] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (inverse f:B->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `inverse f (ring_sum l G (\g:B->B. ring_mul l ((h:A->B)(c g)) (g (x:B)))):B`
  THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\g:B->B. ring_mul l ((h:A->B)(c g)) (g (x:B))`; `G:(B->B)->bool`]
     (MATCH_MP RING_HOMOMORPHISM_SUM
       (ASSUME `ring_homomorphism(l,l) (inverse f:B->B)`))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `u:B->B` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
     (ASSUME `ring_homomorphism(l,l) (inverse f:B->B)`)] THEN
    MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
    USE_THEN "sum" SUBST1_TAC THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]]);;

let NORMAL_BASIS_DETERMINANT = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        x IN ring_carrier l
        ==> ((!c. (!f. f IN group_carrier(galois_group(k,l) h)
                       ==> c f IN ring_carrier k) /\
                  ring_sum l (group_carrier(galois_group(k,l) h))
                    (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                  ==> !f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f = ring_0 k) <=>
             ~(ring_det l (group_carrier(galois_group(k,l) h))
                          (\f g. (inverse f o g) x) = ring_0 l))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[NORMAL_BASIS_DET_INDEPENDENT]] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    NORMAL_BASIS_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "span" o CONJUNCT2 o CONJUNCT2) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `FINITE(group_carrier(galois_group(k,l) (h:A->B)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_GALOIS_GROUP]; ALL_TAC] THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  SUBGOAL_THEN
   `(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
    (!f g. f IN G /\ g IN G ==> f o g IN G) /\
    (!f. f IN G ==> inverse f IN G) /\
    (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
    (!f c. f IN G /\ c IN ring_carrier k ==> f((h:A->B) c) = h c) /\
    (!f. f IN G ==> inverse(inverse f) = f) /\
    (!c. c IN ring_carrier k ==> h c IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    REWRITE_TAC[GALOIS_GROUP_IN_CARRIER; GALOIS_GROUP_INVERSE;
                GALOIS_GROUP_RING_HOMOMORPHISM; GALOIS_GROUP_FIXES;
                GALOIS_GROUP_COMPOSE] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; PERMUTES_INVERSE_INVERSE;
                  GALOIS_GROUP_PERMUTES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l`
  (LABEL_TAC "gin") THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_DET_EQ_0_ROWS; FIELD_IMP_INTEGRAL_DOMAIN; o_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e:(B->B)->B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s0:B->B` STRIP_ASSUME_TAC) (LABEL_TAC "rows"))) THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier l
        ==> ring_sum l G (\s. ring_mul l ((e:(B->B)->B) s) (inverse s y)) =
            ring_0 l`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "span" (MP_TAC o SPEC `y:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(B->B)->A`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l G
        (\s. ring_sum l G
               (\t:B->B. ring_mul l ((h:A->B)(c t))
                   (ring_mul l ((e:(B->B)->B) s) (inverse s (t (x:B))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `s:B->B` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `ring_homomorphism(l,l) (inverse s:B->B)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL
       [`\f:B->B. ring_mul l ((h:A->B)(c f)) (f (x:B))`; `G:(B->B)->bool`]
       (MATCH_MP RING_HOMOMORPHISM_SUM
         (ASSUME `ring_homomorphism(l,l) (inverse s:B->B)`))) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
        TRY(USE_THEN "gin" MATCH_MP_TAC) THEN ASM_SIMP_TAC[RING_MUL];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:B->B` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM] THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
        (ASSUME `ring_homomorphism(l,l) (inverse s:B->B)`)] THEN
      SUBGOAL_THEN
       `(h:A->B)(c(t:B->B)) IN ring_carrier l /\
        (e:(B->B)->B) s IN ring_carrier l /\
        inverse s (t(x:B)) IN ring_carrier l`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SPEC_TAC(`(h:A->B)(c(t:B->B))`,`u:B`) THEN
      SPEC_TAC(`(e:(B->B)->B) s`,`v:B`) THEN
      SPEC_TAC(`inverse (s:B->B) (t(x:B))`,`z:B`) THEN
      RING_TAC;
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      REPEAT(MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
      TRY(USE_THEN "gin" MATCH_MP_TAC) THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC `t:B->B` THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      REPEAT(MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
      TRY(USE_THEN "gin" MATCH_MP_TAC) THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "rows" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(t:B->B) IN G`)]) THEN
    MATCH_MP_TAC RING_MUL_RZERO THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `\f:B->B. (e:(B->B)->B) (inverse f)`]
    GALOIS_GROUP_INDEPENDENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
      [SYM(MATCH_MP th (ASSUME `(y:B) IN ring_carrier l`))]) THEN
    MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [`inverse:(B->B)->(B->B)`; `inverse:(B->B)->(B->B)`] THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `inverse s0:B->B`) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The two cases of the proof: cyclic Galois groups (any base field, in      *)
(* particular finite fields, through the cyclic vector theorem) and infinite *)
(* base fields (through the determinant of a polynomial array).              *)
(* ------------------------------------------------------------------------- *)

let NORMAL_BASIS_CYCLIC = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        cyclic_group(galois_group(k,l) h)
        ==> ?x. x IN ring_carrier l /\
                (!y. y IN ring_carrier l
                     ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                                  ==> c f IN ring_carrier k) /\
                             y = ring_sum l (group_carrier(galois_group(k,l) h))
                                   (\f. ring_mul l (h(c f)) (f x))) /\
                (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f IN ring_carrier k) /\
                     ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                     ==> !f. f IN group_carrier(galois_group(k,l) h)
                             ==> c f = ring_0 k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s:B->B` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [cyclic_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
  SUBGOAL_THEN
   `!c. c IN ring_carrier k ==> (h:A->B) c IN ring_carrier l`
  (LABEL_TAC "hin") THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(group_carrier(galois_group(k,l) (h:A->B)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_GALOIS_GROUP]; ALL_TAC] THEN
  ABBREV_TAC `n = CARD(group_carrier(galois_group(k,l) (h:A->B)))` THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `I:B->B` THEN REWRITE_TAC[GALOIS_GROUP_I];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `s:B->B`]
    FINITE_CYCLIC_GROUP_POWERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "img") (LABEL_TAC "pw")) THEN
  SUBGOAL_THEN
   `!i y. ITER i (s:B->B) y = group_pow (galois_group(k,l) (h:A->B)) s i y`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; group_pow; GALOIS_GROUP; I_THM;
                                    o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. group_pow (galois_group(k,l) (h:A->B)) s i IN
        group_carrier(galois_group(k,l) h)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GROUP_POW]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i y. y IN ring_carrier l
          ==> group_pow (galois_group(k,l) (h:A->B)) s i y IN ring_carrier l`
  ASSUME_TAC THENL [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < n /\ j < n /\
          group_pow (galois_group(k,l) (h:A->B)) s i =
          group_pow (galois_group(k,l) h) s j
          ==> i = j`
  (LABEL_TAC "inj") THENL
   [USE_THEN "pw" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[CONG_IMP_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `group_pow (galois_group(k,l) (h:A->B)) s n = I`
  ASSUME_TAC THENL
   [USE_THEN "pw" (MP_TAC o SPECL [`n:num`; `0`]) THEN
    REWRITE_TAC[NUMBER_RULE `(n == 0) (mod n)`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[group_pow; GALOIS_GROUP];
    REMOVE_THEN "pw" (K ALL_TAC)] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->B`; `n:num`;
                 `\i. if i = 0 then ring_1 k else ring_0 k:A`]
    CYCLIC_VECTOR_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER];
      ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM; RING_HOMOMORPHISM_ADD];
      MP_TAC(ISPECL [`h:A->B`; `s:B->B`; `k:A ring`; `l:B ring`]
        GALOIS_GROUP_RING_HOMOMORPHISM) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
      REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_MESON_TAC[GALOIS_GROUP_FIXES];
      GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN ASM_REWRITE_TAC[I_THM] THEN
      CONV_TAC SYM_CONV THEN
      TRANS_TAC EQ_TRANS
       `ring_sum l {i | i < n} (\i. if i = 0 then y else ring_0 l):B` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[group_pow; GALOIS_GROUP; I_THM] THEN
        ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LZERO];
        ASM_REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; LT_NZ]];
      X_GEN_TAC `c:num->A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cin") (LABEL_TAC "zero")) THEN
      SUBGOAL_THEN
       `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
            ==> (@i. i < n /\ group_pow (galois_group(k,l) h) s i = f) < n /\
                group_pow (galois_group(k,l) h) s
                  (@i. i < n /\ group_pow (galois_group(k,l) h) s i = f) = f`
      (LABEL_TAC "sel") THENL
       [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN CONV_TAC SELECT_CONV THEN
        UNDISCH_TAC `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))` THEN
        USE_THEN "img"
         (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. i < n
            ==> (@j. j < n /\ group_pow (galois_group(k,l) (h:A->B)) s j =
                              group_pow (galois_group(k,l) h) s i) = i`
      (LABEL_TAC "selid") THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        USE_THEN "sel" (MP_TAC o SPEC
          `group_pow (galois_group(k,l) (h:A->B)) s i`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
        `\f. (h:A->B)(c(@i. i < n /\
                         group_pow (galois_group(k,l) (h:A->B)) s i = f))`]
        GALOIS_GROUP_INDEPENDENT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
          USE_THEN "hin" MATCH_MP_TAC THEN USE_THEN "cin" MATCH_MP_TAC THEN
          USE_THEN "sel" (MP_TAC o SPEC `f:B->B`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
          ALL_TAC] THEN
        X_GEN_TAC `y:B` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `s:B->B`; `l:B ring`]
          RING_SUM_CYCLIC_GROUP) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "zero" (MP_TAC o SPEC `y:B`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
        DISCH_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
        `group_pow (galois_group(k,l) (h:A->B)) s i`) THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(h:A->B)(ring_0 k) = ring_0 l` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
        [ring_monomorphism]) THEN
      ASM_SIMP_TAC[RING_0]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:B`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "z"))) THEN
  SUBGOAL_THEN
   `!c. (!f. f IN group_carrier(galois_group(k,l) (h:A->B))
             ==> c f IN ring_carrier k) /\
        ring_sum l (group_carrier(galois_group(k,l) h))
          (\f. ring_mul l (h(c f)) (f z)) = ring_0 l
        ==> !f. f IN group_carrier(galois_group(k,l) h) ==> c f = ring_0 k`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:(B->B)->A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `s:B->B`; `l:B ring`]
      RING_SUM_CYCLIC_GROUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_TAC THEN
    USE_THEN "z" (MP_TAC o SPEC
      `\i. (c:(B->B)->A)(group_pow (galois_group(k,l) (h:A->B)) s i)`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM];
    ALL_TAC] THEN
  EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `z:B`]
    NORMAL_BASIS_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let NORMAL_BASIS_INFINITE = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        INFINITE(ring_carrier k)
        ==> ?x. x IN ring_carrier l /\
                (!y. y IN ring_carrier l
                     ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                                  ==> c f IN ring_carrier k) /\
                             y = ring_sum l (group_carrier(galois_group(k,l) h))
                                   (\f. ring_mul l (h(c f)) (f x))) /\
                (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f IN ring_carrier k) /\
                     ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                     ==> !f. f IN group_carrier(galois_group(k,l) h)
                             ==> c f = ring_0 k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `integral_domain(l:B ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    PRIMITIVE_ELEMENT_THEOREM) THEN
  ASM_SIMP_TAC[GALOIS_IMP_SEPARABLE_EXTENSION] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(group_carrier(galois_group(k,l) (h:A->B)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_GALOIS_GROUP]; ALL_TAC] THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  SUBGOAL_THEN
   `(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
    (!f g. f IN G /\ g IN G ==> f o g IN G) /\
    (!f. f IN G ==> inverse f IN G) /\
    (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
    (!f c. f IN G /\ c IN ring_carrier k ==> f((h:A->B) c) = h c) /\
    (!f. f IN G ==> f permutes ring_carrier l) /\
    I IN G /\
    (!c. c IN ring_carrier k ==> h c IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    REWRITE_TAC[GALOIS_GROUP_IN_CARRIER; GALOIS_GROUP_INVERSE; GALOIS_GROUP_I;
                GALOIS_GROUP_RING_HOMOMORPHISM; GALOIS_GROUP_FIXES;
                GALOIS_GROUP_COMPOSE; GALOIS_GROUP_PERMUTES] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g. f IN G /\ g IN G /\ (f:B->B) a = g a ==> f = g`
  (LABEL_TAC "pinj") THENL
   [MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC PERMUTES_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`f:B->B`; `g:B->B`; `l:B ring`; `l:B ring`;
                   `(a:B) INSERT IMAGE (h:A->B) (ring_carrier k)`]
      RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g. f IN G /\ g IN G ==> (inverse f o g = I <=> (f:B->B) = g)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:B->B`; `ring_carrier l:B->bool`] PERMUTES_INVERSES_o) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `(o) (f:B->B):(B->B)->(B->B)`) THEN
      ASM_REWRITE_TAC[o_ASSOC; I_O_ID] THEN MESON_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `Q = \p:B->B. ring_product (poly_ring l (:1)) (G DELETE p)
                  (\r:B->B. poly_sub l (poly_var l one)
                                      (poly_const l (r a)))` THEN
  SUBGOAL_THEN
   `!p:B->B. (Q:(B->B)->(1->num)->B) p IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[RING_PRODUCT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p y. y IN ring_carrier l
          ==> poly_eval l ((Q:(B->B)->(1->num)->B) p) y =
              ring_product l (G DELETE p) (\r. ring_sub l y (r a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_RING_PRODUCT o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_DELETE; POLY_CLAUSES; RING_SUB; POLY_VAR_UNIV;
                   POLY_CONST; IN_DELETE];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `r:B->B` THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
                 POLY_EVAL_VAR; POLY_EVAL_CONST];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = ring_det (poly_ring l (:1)) G
          (\p q:B->B. (Q:(B->B)->(1->num)->B) (inverse p o q))` THEN
  SUBGOAL_THEN `(P:(1->num)->B) IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC[RING_DET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier l
        ==> poly_eval l (P:(1->num)->B) y =
            ring_det l G (\p q. ring_product l (G DELETE (inverse p o q))
                                  (\r. ring_sub l y (r a)))`
  (LABEL_TAC "Peval") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    MP_TAC(ISPECL [`poly_ring l (:1):((1->num)->B)ring`; `l:B ring`;
                   `\p:(1->num)->B. poly_eval l p y`; `G:(B->B)->bool`;
                   `\p q:B->B. (Q:(B->B)->(1->num)->B) (inverse p o q)`]
      RING_DET_HOMOMORPHISM) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EVAL] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(poly_eval l (P:(1->num)->B) a = ring_0 l)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o rand o
      snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`p:B->B`; `q:B->B`] THEN
      STRIP_TAC THEN MATCH_MP_TAC RING_PRODUCT_ZERO THEN
      EXISTS_TAC `I:B->B` THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; I_THM; RING_SUB_REFL] THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; NOT_EXISTS_THM] THEN
    X_GEN_TAC `p:B->B` THEN
    ASM_CASES_TAC `(p:B->B) IN G` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inverse (p:B->B) o p = I` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; FINITE_DELETE; NOT_EXISTS_THM;
                 IN_DELETE; RING_SUB_EQ_0] THEN
    X_GEN_TAC `r:B->B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r:B->B) a = I a` ASSUME_TAC THENL
     [REWRITE_TAC[I_THM] THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_eq(concl th) && rand(concl th) = `ring_0 l:B`)) THEN
      ASM_SIMP_TAC[RING_SUB_EQ_0];
      ALL_TAC] THEN
    UNDISCH_TAC `~(r = (I:B->B))` THEN REWRITE_TAC[] THEN
    USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P = ring_0(poly_ring l (:1)):(1->num)->B)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(poly_eval l (P:(1->num)->B) a = ring_0 l)` THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES; POLY_EVAL_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `P:(1->num)->B`] POLY_ROOT_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `?c. c IN ring_carrier k /\
        ~(poly_eval l (P:(1->num)->B) ((h:A->B) c) = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
    SUBGOAL_THEN `INFINITE(IMAGE (h:A->B) (ring_carrier k))` MP_TAC THENL
     [MATCH_MP_TAC INFINITE_IMAGE THEN ASM_MESON_TAC[ring_monomorphism];
      ALL_TAC] THEN
    REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{y | y IN ring_carrier l /\
           poly_eval l (P:(1->num)->B) y = ring_0 l}` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `w = ring_product l (G DELETE I)
          (\r:B->B. ring_sub l ((h:A->B) c) (r a))` THEN
  SUBGOAL_THEN `(w:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[RING_PRODUCT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN G
        ==> (p:B->B) w =
            ring_product l (G DELETE p) (\r. ring_sub l ((h:A->B) c) (r a))`
  (LABEL_TAC "conj") THENL
   [X_GEN_TAC `p:B->B` THEN DISCH_TAC THEN EXPAND_TAC "w" THEN
    SUBGOAL_THEN `ring_homomorphism(l,l) (p:B->B)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\r:B->B. ring_sub l ((h:A->B) c) (r a)`; `G DELETE (I:B->B)`]
     (MATCH_MP RING_HOMOMORPHISM_PRODUCT
       (ASSUME `ring_homomorphism(l,l) (p:B->B)`))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; RING_SUB];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_PRODUCT_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [`\r:B->B. (p:B->B) o r`; `\r:B->B. inverse (p:B->B) o r`] THEN
    SUBGOAL_THEN `(p:B->B) o inverse p = I /\ inverse p o p = I`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_INVERSES_o]; ALL_TAC] THEN
    REWRITE_TAC[IN_DELETE; o_ASSOC] THEN ASM_REWRITE_TAC[I_O_ID] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `q:B->B` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `q:B->B` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `(o) (inverse p:B->B):(B->B)->(B->B)`) THEN
      ASM_REWRITE_TAC[o_ASSOC; I_O_ID];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB
      (ASSUME `ring_homomorphism(l,l) (p:B->B)`)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_det l G (\f g:B->B. (inverse f o g) w) =
    poly_eval l (P:(1->num)->B) ((h:A->B) c)`
  ASSUME_TAC THENL
   [USE_THEN "Peval" (MP_TAC o SPEC `(h:A->B) c`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_DET_EQ THEN
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    USE_THEN "conj" (MP_TAC o SPEC `inverse (f:B->B) o (g:B->B)`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. (!f:B->B. f IN G ==> d f IN ring_carrier k) /\
        ring_sum l G (\f:B->B. ring_mul l ((h:A->B)(d f)) (f (w:B))) =
        ring_0 l
        ==> !f. f IN G ==> d f = ring_0 k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `w:B`]
      NORMAL_BASIS_DET_INDEPENDENT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `w:B`]
    NORMAL_BASIS_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The normal basis theorem and its forms with ring_basis and free_basis;    *)
(* for finite fields the Galois group is generated by the Frobenius map, so  *)
(* the powers x^(q^i), i < [l:k], of a normal element form a free basis.     *)
(* ------------------------------------------------------------------------- *)

let NORMAL_BASIS_THEOREM = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                (!y. y IN ring_carrier l
                     ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                                  ==> c f IN ring_carrier k) /\
                             y = ring_sum l (group_carrier(galois_group(k,l) h))
                                   (\f. ring_mul l (h(c f)) (f x))) /\
                (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f IN ring_carrier k) /\
                     ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                     ==> !f. f IN group_carrier(galois_group(k,l) h)
                             ==> c f = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `FINITE(ring_carrier(k:A ring))` THENL
   [MATCH_MP_TAC NORMAL_BASIS_CYCLIC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CYCLIC_GALOIS_GROUP_FINITE_FIELD THEN
    ASM_MESON_TAC[FINITE_FINITE_FIELD_EXTENSION];
    MATCH_MP_TAC NORMAL_BASIS_INFINITE THEN ASM_REWRITE_TAC[INFINITE]]);;

let NORMAL_BASIS_RING_BASIS = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                ring_basis (k,l) h
                  (IMAGE (\f. f x) (group_carrier(galois_group(k,l) h))) /\
                !f g. f IN group_carrier(galois_group(k,l) h) /\
                      g IN group_carrier(galois_group(k,l) h) /\
                      f x = g x
                      ==> f = g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] NORMAL_BASIS_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    NORMAL_BASIS_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let NORMAL_BASIS_FREE_BASIS = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                !n e. BIJ e {i | i < n} (group_carrier(galois_group(k,l) h))
                      ==> free_basis (k,l) h n (\i. e i x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] NORMAL_BASIS_RING_BASIS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `e:num->B->B`] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[FREE_BASIS_FIELD] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [BIJ]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJ]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SURJ]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (\i. (e:num->B->B) i x) {i | i < n} =
      IMAGE (\f. f x) (group_carrier(galois_group(k,l) (h:A->B)))`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let FINITE_FIELD_NORMAL_BASIS = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> ?x. x IN ring_carrier l /\
                free_basis (k,l) h (extension_degree(k,l) h)
                  (\i. ring_pow l x (CARD(ring_carrier k) EXP i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    FINITE_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_GROUP_FINITE_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `s = \x. if x IN ring_carrier l
            then ring_pow l x (CARD(ring_carrier k:A->bool)) else x:B` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] NORMAL_BASIS_FREE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`extension_degree(k,l) (h:A->B)`;
    `group_pow (galois_group(k,l) (h:A->B)) s`]) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `s:B->B`]
      FINITE_CYCLIC_GROUP_POWERS) THEN
    ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BIJ; INJ; SURJ; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[CONG_IMP_EQ];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[GALOIS_GROUP_POW_RING_POW] THEN
    ASM_REWRITE_TAC[]]);;
