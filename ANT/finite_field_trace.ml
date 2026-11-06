(* ========================================================================= *)
(* Traces of finite fields and separability of free algebras over a finite   *)
(* field.                                                                    *)
(*                                                                           *)
(* The trace of a finite field l over a subfield k (algebra_trace of         *)
(* Library/ring_det.ml) is not identically zero                              *)
(* (ALGEBRA_TRACE_FINITE_FIELD_NONZERO: finite fields are perfect, so the    *)
(* extension is separable and its trace is onto, ALGEBRA_TRACE_SURJECTIVE of *)
(* Library/fieldtheory.ml; the trace as the Frobenius orbit sum is           *)
(* ALGEBRA_TRACE_NORM_FINITE_FIELD of Library/galois.ml). A reduced finite   *)
(* algebra l over a finite field splits as l/m x l/j with m maximal, and the *)
(* trace splits accordingly (ALGEBRA_TRACE_CHINESE_REMAINDER), so it is not  *)
(* identically zero on an ideal j with l = m + j and m INTER j = {0}         *)
(* (ALGEBRA_TRACE_COMAXIMAL_NONZERO), and for a ring r with r/(P INTER Q)    *)
(* free over a finite field, P maximal and P + Q = r, some element of Q has  *)
(* a nonzero trace in r/(P INTER Q)                                          *)
(* (ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO); hence its trace form is       *)
(* nondegenerate (TRACE_FORM_NONDEGENERATE_FINITE), and a free algebra over  *)
(* a finite field has zero discriminant iff it has a nonzero nilpotent       *)
(* element (BASIS_DISCRIMINANT_EQ_0_FINITE).                                 *)
(*                                                                           *)
(* Helpers: the splitting of a finite reduced ring at a maximal ideal        *)
(* (FINITE_REDUCED_RING_SPLIT); from earlier files |l| = |k|^n for a free    *)
(* algebra (FREE_BASIS_HAS_SIZE of Library/ring_det.ml), the Chinese         *)
(* remainder isomorphism for two ideals with zero intersection               *)
(* (RING_ISOMORPHISM_PROD_QUOTIENT_RING) and solving x y = w modulo a        *)
(* maximal ideal with y in a comaximal ideal (MAXIMAL_IDEAL_COMAXIMAL_MUL).  *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (nilpotents, quotient rings),                 *)
(* Library/fieldtheory.ml (perfect fields, separable extensions,             *)
(* ALGEBRA_TRACE_SURJECTIVE), Library/ring_det.ml (FREE_BASIS_HAS_SIZE,      *)
(* BASIS_DISCRIMINANT_EQ_0, BASIS_DISCRIMINANT_NILPOTENT),                   *)
(* ANT/ideal_arith.ml (ideal_product, RING_ISOMORPHISM_PROD_QUOTIENT_RING,   *)
(* MAXIMAL_IDEAL_COMAXIMAL_MUL), ANT/trace_form.ml (products, isomorphic     *)
(* images and existence of free bases).                                      *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/trace_form.ml";;

(* ------------------------------------------------------------------------- *)
(* Finite fields and their extensions.                                       *)
(* ------------------------------------------------------------------------- *)

let ALGEBRA_TRACE_FINITE_FIELD_NONZERO = prove
 (`!k:A ring l:B ring h n g.
        field k /\ field l /\ FINITE(ring_carrier l) /\
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> ?x. x IN ring_carrier l /\
                ~(algebra_trace (k,l) h x = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field_extension(k,l) (h:A->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[field_extension; FIELD_RING_HOMOMORPHISM_MONOMORPHISM;
                 FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `finite_extension(k,l) (h:A->B) /\ FINITE(ring_carrier(k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FREE_BASIS_IMP_FINITE_EXTENSION;
                  FINITE_RING_MONOMORPHIC_PREIMAGE; field_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    ALGEBRA_TRACE_SURJECTIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN
    ASM_SIMP_TAC[FINITE_FIELD_IMP_PERFECT; FINITE_IMP_ALGEBRAIC_EXTENSION];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ring_1 k:A` o
    REWRITE_RULE[EXTENSION; IN_IMAGE]) THEN
  REWRITE_TAC[RING_1] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[FIELD_NONTRIVIAL]);;

(* ------------------------------------------------------------------------- *)
(* Free algebras over a finite field: discriminant and nilpotents.           *)
(* ------------------------------------------------------------------------- *)

let ALGEBRA_TRACE_CHINESE_REMAINDER = prove
 (`!k:A ring l:B ring h n g j1 j2 n1 g1 n2 g2 z.
        field k /\ ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        ring_ideal l j1 /\ ring_ideal l j2 /\
        ring_setadd l j1 j2 = ring_carrier l /\ j1 INTER j2 = {ring_0 l} /\
        free_basis (k,quotient_ring l j1) (ring_coset l j1 o h) n1 g1 /\
        free_basis (k,quotient_ring l j2) (ring_coset l j2 o h) n2 g2 /\
        z IN ring_carrier l
        ==> algebra_trace (k,l) h z =
            ring_add k
             (algebra_trace (k,quotient_ring l j1) (ring_coset l j1 o h)
                (ring_coset l j1 z))
             (algebra_trace (k,quotient_ring l j2) (ring_coset l j2 o h)
                (ring_coset l j2 z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `j1:B->bool`; `j2:B->bool`]
    RING_ISOMORPHISM_PROD_QUOTIENT_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `f = \x:B. ring_coset l j1 x,ring_coset l j2 x` THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,quotient_ring l j1) (ring_coset l j1 o (h:A->B)) /\
    ring_homomorphism(k,quotient_ring l j2) (ring_coset l j2 o h)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `l:B ring` THEN ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:B->(B->bool)#(B->bool)) o (h:A->B) =
    (\a. (ring_coset l j1 o h) a,(ring_coset l j2 o h) a)`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `quotient_ring l (j1:B->bool)`;
                 `quotient_ring l (j2:B->bool)`; `ring_coset l j1 o (h:A->B)`;
                 `ring_coset l j2 o (h:A->B)`; `n1:num`; `n2:num`;
                 `g1:num->B->bool`; `g2:num->B->bool`]
                FREE_BASIS_PROD_RING) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`;
                 `prod_ring (quotient_ring l j1) (quotient_ring (l:B ring) j2)`;
                 `h:A->B`; `f:B->(B->bool)#(B->bool)`; `n:num`; `g:num->B`]
                FREE_BASIS_ISOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism
     (k,prod_ring (quotient_ring l j1) (quotient_ring l j2))
     (\a. (ring_coset l j1 o (h:A->B)) a,(ring_coset l j2 o h) a)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_HOMOMORPHISM_PAIRED; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `n:num = n1 + n2` SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS
     `extension_degree
       (k:A ring,prod_ring (quotient_ring l j1) (quotient_ring l j2))
       (\a. (ring_coset l j1 o (h:A->B)) a,(ring_coset l j2 o h) a)` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC FREE_BASIS_EXTENSION_DEGREE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN ACCEPT_TAC th);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`;
                 `prod_ring (quotient_ring l j1) (quotient_ring (l:B ring) j2)`;
                 `h:A->B`; `f:B->(B->bool)#(B->bool)`; `n1 + n2:num`;
                 `g:num->B`; `z:B`] ALGEBRA_TRACE_ISOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "f" THEN BETA_TAC THEN MATCH_MP_TAC ALGEBRA_TRACE_PROD_RING THEN
  MAP_EVERY EXISTS_TAC
   [`n1:num`; `n2:num`; `g1:num->B->bool`; `g2:num->B->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC `l:B ring` THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET]);;

(* A free algebra l over a finite field k split as l/m x l/j, m maximal: on  *)
(* j the trace is that of the finite field l/m, which is not identically     *)
(* zero.                                                                     *)
let ALGEBRA_TRACE_COMAXIMAL_NONZERO = prove
 (`!k:A ring l:B ring h n g m j.
        field k /\ FINITE(ring_carrier k) /\
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        maximal_ideal l m /\ ring_ideal l j /\
        ring_setadd l m j = ring_carrier l /\ m INTER j = {ring_0 l}
        ==> ?y. y IN j /\ ~(algebra_trace (k,l) h y = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `FINITE(ring_carrier(l:B ring))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FREE_BASIS_HAS_SIZE; HAS_SIZE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:B->bool.
        ring_ideal l i
        ==> FINITE(ring_carrier(quotient_ring l i)) /\
            ring_homomorphism(k,quotient_ring l i)
                             (ring_coset l i o (h:A->B)) /\
            ?n' g'. free_basis (k,quotient_ring l i) (ring_coset l i o h) n' g'`
  (fun th -> MP_TAC(SPEC `m:B->bool` th) THEN MP_TAC(SPEC `j:B->bool` th))
  THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT
     `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; SIMPLE_IMAGE; FINITE_IMAGE];
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET];
      STRIP_TAC THEN EXISTS_TAC
       `extension_degree (k,quotient_ring l i) (ring_coset l i o (h:A->B))` THEN
      MATCH_MP_TAC FREE_BASIS_EXISTS THEN
      EXISTS_TAC `ring_carrier(quotient_ring l (i:B->bool))` THEN
      ASM_REWRITE_TAC[ring_spanning; RING_SPAN_SELF; SUBSET_REFL]];
    ASM_REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`n2:num`; `g2:num->B->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n1:num`; `g1:num->B->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `quotient_ring l (m:B->bool)`;
                 `ring_coset l m o (h:A->B)`; `n1:num`; `g1:num->B->bool`]
                ALGEBRA_TRACE_FINITE_FIELD_NONZERO) THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING; QUOTIENT_RING_CARRIER; SIMPLE_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:B->bool`; `j:B->bool`; `ring_1 l:B`; `w:B`]
    MAXIMAL_IDEAL_COMAXIMAL_MUL) THEN
  ASM_REWRITE_TAC[RING_1] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MAXIMAL_IMP_PROPER_IDEAL; PROPER_IDEAL]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `n:num`; `g:num->B`;
                 `m:B->bool`; `j:B->bool`; `n1:num`; `g1:num->B->bool`;
                 `n2:num`; `g2:num->B->bool`; `y:B`]
                ALGEBRA_TRACE_CHINESE_REMAINDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_coset l m y = ring_coset l m (w:B) /\
    ring_coset l j y = ring_0(quotient_ring l (j:B->bool))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[RING_COSET_EQ; QUOTIENT_RING_0; RING_COSET_EQ_IDEAL] THEN
    ASM_MESON_TAC[RING_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `algebra_trace (k,quotient_ring l j) (ring_coset l j o (h:A->B))
                    (ring_0(quotient_ring l j)) = ring_0 k`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ALGEBRA_TRACE_0];
    ASM_SIMP_TAC[RING_ADD_RZERO; ALGEBRA_TRACE_NORM_IN_CARRIER]]);;

(* With r/(P INTER Q) free over a finite field, P maximal and P + Q = r,     *)
(* some element of Q has a nonzero trace (r/(P INTER Q) = r/P x r/Q and the  *)
(* trace of the finite field r/P is not zero).                               *)
let ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO = prove
 (`!(f:K ring) (r:A ring) g n G P Q.
        field f /\ FINITE(ring_carrier f) /\
        ring_homomorphism(f,quotient_ring r (P INTER Q)) g /\
        free_basis (f,quotient_ring r (P INTER Q)) g n G /\
        maximal_ideal r P /\ ring_ideal r Q /\
        ring_setadd r P Q = ring_carrier r
        ==> ?x. x IN Q /\
                ~(algebra_trace (f,quotient_ring r (P INTER Q)) g
                    (ring_coset r (P INTER Q) x) = ring_0 f)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = (P:A->bool) INTER Q` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool) /\ j SUBSET P /\ j SUBSET Q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN ASM_SIMP_TAC[RING_IDEAL_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ring_ideal r i /\ j SUBSET i
        ==> {x | x IN ring_carrier r /\
                 ring_coset r j x IN IMAGE (ring_coset r j) i} = (i:A->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_sub r x u IN (i:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_COSET_EQ; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `x = ring_add r (ring_sub r x u) (u:A)` SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `x = ring_add (r:A ring) (ring_sub r x u) u`) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[IN_RING_IDEAL_ADD]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_EPIMORPHISM_RING_COSET o
    check (fun th -> concl th = `ring_ideal r (j:A->bool)`)) THEN
  SUBGOAL_THEN
   `ring_ideal (quotient_ring r j) (IMAGE (ring_coset r j) (P:A->bool)) /\
    ring_ideal (quotient_ring r j) (IMAGE (ring_coset r j) (Q:A->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_EPIMORPHIC_IMAGE THEN
    EXISTS_TAC `r:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:K ring`; `quotient_ring r (j:A->bool)`;
                 `g:K->(A->bool)`; `n:num`; `G:num->(A->bool)`;
                 `IMAGE (ring_coset r j) (P:A->bool)`;
                 `IMAGE (ring_coset r j) (Q:A->bool)`]
    ALGEBRA_TRACE_COMAXIMAL_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `quotient_ring r (j:A->bool)`;
                     `ring_coset r (j:A->bool)`; `P:A->bool`;
                     `IMAGE (ring_coset r j) (P:A->bool)`]
        MAXIMAL_IDEAL_CORRESPONDENCE) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC] THEN
    ASM_SIMP_TAC[MAXIMAL_IDEAL_COMAXIMAL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ring_setadd r P Q = ring_carrier(r:A ring)` THEN
      ASM_SIMP_TAC[MAXIMAL_IDEAL_COMAXIMAL] THEN
      REWRITE_TAC[CONTRAPOS_THM; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      ASM_SIMP_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:A->bool` THEN
    REWRITE_TAC[IN_INTER; IN_SING] THEN
    ASM_SIMP_TAC[QUOTIENT_RING_0] THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:A) IN Q` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `Q:A->bool`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
          GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
          EXISTS_TAC `y:A` THEN ASM_MESON_TAC[]];
        UNDISCH_THEN `z = ring_coset r j (x:A)` SUBST1_TAC THEN
        SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
         [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
          ASM_SIMP_TAC[RING_COSET_EQ_IDEAL] THEN EXPAND_TAC "j" THEN
          ASM_REWRITE_TAC[IN_INTER]]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THEN
      EXISTS_TAC `ring_0 r:A` THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_0] THEN CONV_TAC SYM_CONV THEN
      ASM_SIMP_TAC[RING_COSET_EQ_IDEAL; RING_0; IN_RING_IDEAL_0]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FINITE_REDUCED_RING_SPLIT = prove
 (`!l:B ring x.
        FINITE(ring_carrier l) /\
        (!z. ring_nilpotent l z ==> z = ring_0 l) /\
        x IN ring_carrier l /\ ~(x = ring_0 l)
        ==> ?m j. maximal_ideal l m /\ ~(x IN m) /\ ring_ideal l j /\
                  ring_setadd l m j = ring_carrier l /\
                  m INTER j = {ring_0 l}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(fun red ->
    SUBGOAL_THEN `!z:B. z IN INTERS {p | prime_ideal l p} ==> z = ring_0 l`
    (LABEL_TAC "nil") THENL
     [MP_TAC(ISPEC `l:B ring` RING_NILRADICAL) THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC[trivial_ring; IN_SING]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[radical; IN_ELIM_THM; IN_SING] THEN
      MESON_TAC[red; ring_nilpotent];
      ALL_TAC]) THEN
  SUBGOAL_THEN `!p. prime_ideal l p ==> maximal_ideal (l:B ring) p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[GSYM(MATCH_MP FIELD_QUOTIENT_RING th)]) THEN
    MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_QUOTIENT_RING; QUOTIENT_RING_CARRIER;
                 SIMPLE_IMAGE; FINITE_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. prime_ideal l p /\ ~((x:B) IN p)` STRIP_ASSUME_TAC THENL
   [USE_THEN "nil" (MP_TAC o SPEC `x:B`) THEN
    REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = {q | maximal_ideal l q /\ ~(q = (p:B->bool))}` THEN
  SUBGOAL_THEN
   `FINITE(s:(B->bool)->bool) /\
    !q. q IN s ==> ring_ideal l q /\ ring_setadd l p q = ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t:B->bool | t SUBSET ring_carrier l}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET; SUBSET; IN_ELIM_THM;
                   MAXIMAL_IDEAL_IMP_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `q:B->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MAXIMAL_IMP_RING_IDEAL; MAXIMAL_IDEAL_COMAXIMAL] THEN
    ASM_MESON_TAC[maximal_ideal; PSUBSET; PRIME_IMP_PROPER_IDEAL];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:B->bool`; `ideal_product l s (\q:B->bool. q)`] THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_PRODUCT; COMAXIMAL_IDEAL_PRODUCT;
               PRIME_IMP_RING_IDEAL] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:B` THEN
  REWRITE_TAC[IN_INTER; IN_SING] THEN EQ_TAC THENL
   [STRIP_TAC THEN USE_THEN "nil" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN X_GEN_TAC `q:B->bool` THEN
    DISCH_TAC THEN ASM_CASES_TAC `q:B->bool = p` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:B ring`; `s:(B->bool)->bool`; `\q:B->bool. q`;
                   `q:B->bool`] IDEAL_PRODUCT_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_0; RING_IDEAL_IDEAL_PRODUCT;
                 PRIME_IMP_RING_IDEAL]]);;

(* For x <> 0 in a reduced l choose a maximal ideal m not containing x and   *)
(* an ideal j with l = l/m x l/j, an element t of the finite field l/m with  *)
(* nonzero trace, and y in j with x y = t modulo m; then Tr(x y) = Tr(t) +   *)
(* Tr(0).                                                                    *)
let TRACE_FORM_NONDEGENERATE_FINITE = prove
 (`!k:A ring l:B ring h n g x.
        field k /\ FINITE(ring_carrier k) /\
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        (!z. ring_nilpotent l z ==> z = ring_0 l) /\
        x IN ring_carrier l /\ ~(x = ring_0 l)
        ==> ?y. y IN ring_carrier l /\
                ~(algebra_trace (k,l) h (ring_mul l x y) = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(ring_carrier(l:B ring))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FREE_BASIS_HAS_SIZE; HAS_SIZE]; ALL_TAC] THEN
  UNDISCH_TAC `!z:B. ring_nilpotent l z ==> z = ring_0 l` THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP FINITE_REDUCED_RING_SPLIT
   (CONJ (ASSUME `FINITE(ring_carrier(l:B ring))`) (CONJ th
     (CONJ (ASSUME `(x:B) IN ring_carrier l`)
           (ASSUME `~(x:B = ring_0 l)`)))))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:B->bool`; `j:B->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN
   `!i:B->bool.
        ring_ideal l i
        ==> FINITE(ring_carrier(quotient_ring l i)) /\
            ring_homomorphism(k,quotient_ring l i)
                             (ring_coset l i o (h:A->B)) /\
            ?n' g'. free_basis (k,quotient_ring l i) (ring_coset l i o h) n' g'`
  (fun th -> MP_TAC(SPEC `m:B->bool` th) THEN MP_TAC(SPEC `j:B->bool` th))
  THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT
     `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; SIMPLE_IMAGE; FINITE_IMAGE];
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET];
      STRIP_TAC THEN EXISTS_TAC
       `extension_degree (k,quotient_ring l i) (ring_coset l i o (h:A->B))` THEN
      MATCH_MP_TAC FREE_BASIS_EXISTS THEN
      EXISTS_TAC `ring_carrier(quotient_ring l (i:B->bool))` THEN
      ASM_REWRITE_TAC[ring_spanning; RING_SPAN_SELF; SUBSET_REFL]];
    ASM_REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`n2:num`; `g2:num->B->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n1:num`; `g1:num->B->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `quotient_ring l (m:B->bool)`;
                 `ring_coset l m o (h:A->B)`; `n1:num`; `g1:num->B->bool`]
                ALGEBRA_TRACE_FINITE_FIELD_NONZERO) THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING; QUOTIENT_RING_CARRIER; SIMPLE_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:B->bool`; `j:B->bool`; `x:B`; `w:B`]
    MAXIMAL_IDEAL_COMAXIMAL_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `n:num`; `g:num->B`;
                 `m:B->bool`; `j:B->bool`; `n1:num`; `g1:num->B->bool`;
                 `n2:num`; `g2:num->B->bool`; `ring_mul l x y:B`]
                ALGEBRA_TRACE_CHINESE_REMAINDER) THEN
  ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_coset l m (ring_mul l x y) = ring_coset l m (w:B) /\
    ring_coset l j (ring_mul l x y) = ring_0(quotient_ring l (j:B->bool))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[RING_COSET_EQ; QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_MUL;
                 IN_RING_IDEAL_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `algebra_trace (k,quotient_ring l j) (ring_coset l j o (h:A->B))
                    (ring_0(quotient_ring l j)) = ring_0 k`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ALGEBRA_TRACE_0];
    ASM_SIMP_TAC[RING_ADD_RZERO; ALGEBRA_TRACE_NORM_IN_CARRIER]]);;

let BASIS_DISCRIMINANT_EQ_0_FINITE = prove
 (`!k:A ring l:B ring h n g.
        field k /\ FINITE(ring_carrier k) /\
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> (basis_discriminant (k,l) h n g = ring_0 k <=>
             ?x. ring_nilpotent l x /\ ~(x = ring_0 l))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_SIMP_TAC[BASIS_DISCRIMINANT_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM NOT_IMP; GSYM NOT_FORALL_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `n:num`; `g:num->B`;
                   `x:B`] TRACE_FORM_NONDEGENERATE_FINITE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC BASIS_DISCRIMINANT_NILPOTENT THEN
    EXISTS_TAC `x:B` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]]);;
