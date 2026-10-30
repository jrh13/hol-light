(* ========================================================================= *)
(* Galois theory.                                                            *)
(*                                                                           *)
(* Galois groups and extensions, fixed fields, the theorem of Artin, the     *)
(* fundamental theorem of Galois theory, natural irrationalities, Galois     *)
(* groups of polynomials (discriminants, the alternating group criterion,    *)
(* cubics) and of finite fields, Hilbert 90, Kummer and Artin-Schreier       *)
(* extensions, radical extensions and radical elements, cyclotomic           *)
(* extensions, solvable towers, and solvability by radicals: in              *)
(* characteristic zero a polynomial is solvable by radicals if and only if   *)
(* its Galois group is solvable.                                             *)
(* ========================================================================= *)

needs "Library/fieldtheory.ml";;
needs "Library/symmetric_group.ml";;

(* ------------------------------------------------------------------------- *)
(* The Galois group of a field extension (k,l) h: the automorphisms of l     *)
(* fixing the image of k pointwise, as a subgroup of the symmetric group on  *)
(* the carrier of l (so its elements are the identity outside the carrier).  *)
(* ------------------------------------------------------------------------- *)

let galois_group = new_definition
 `galois_group (k:A ring,l:B ring) (h:A->B) =
    subgroup_generated (symmetric_group (ring_carrier l))
      {f | ring_automorphism l f /\ !x. x IN ring_carrier k ==> f(h x) = h x}`;;

let GALOIS_GROUP = prove
 (`(!(h:A->B) k l.
        group_carrier(galois_group(k,l) h) =
        {f | f permutes ring_carrier l /\ ring_automorphism l f /\
             !x. x IN ring_carrier k ==> f(h x) = h x}) /\
   (!(h:A->B) k l. group_id(galois_group(k,l) h) = I) /\
   (!(h:A->B) k l. group_inv(galois_group(k,l) h) = inverse) /\
   (!(h:A->B) k l. group_mul(galois_group(k,l) h) = (o))`,
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[galois_group; SUBGROUP_GENERATED; SYMMETRIC_GROUP]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[galois_group] THEN
  ONCE_REWRITE_TAC[SUBGROUP_GENERATED_RESTRICT] THEN
  REWRITE_TAC[SYMMETRIC_GROUP; INTER; IN_ELIM_THM] THEN
  MATCH_MP_TAC CARRIER_SUBGROUP_GENERATED_SUBGROUP THEN
  REWRITE_TAC[subgroup_of; SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[PERMUTES_I; RING_AUTOMORPHISM_I; I_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE] THEN CONJ_TAC THENL
     [REWRITE_TAC[ring_automorphism] THEN
      MATCH_MP_TAC RING_ISOMORPHISM_INVERSE THEN
      EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[GSYM ring_automorphism];
      ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PERMUTES_COMPOSE; RING_AUTOMORPHISM_COMPOSE; o_THM]]);;

let IN_GALOIS_GROUP = prove
 (`!(h:A->B) f k l.
        f IN group_carrier(galois_group(k,l) h) <=>
        f permutes ring_carrier l /\ ring_automorphism l f /\
        !x. x IN ring_carrier k ==> f(h x) = h x`,
  REWRITE_TAC[GALOIS_GROUP; IN_ELIM_THM]);;

let GALOIS_GROUP_SUBGROUP = prove
 (`!(h:A->B) k l.
        group_carrier(galois_group(k,l) h) subgroup_of
        symmetric_group(ring_carrier l)`,
  REWRITE_TAC[galois_group; SUBGROUP_SUBGROUP_GENERATED]);;

let SUBGROUP_GENERATED_GALOIS_GROUP = prove
 (`!(h:A->B) k l.
        subgroup_generated (symmetric_group(ring_carrier l))
                           (group_carrier(galois_group(k,l) h)) =
        galois_group(k,l) h`,
  REWRITE_TAC[galois_group; SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED]);;

let GALOIS_GROUP_INVERSE = prove
 (`!(h:A->B) f k l.
        f IN group_carrier(galois_group(k,l) h)
        ==> inverse f IN group_carrier(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f:B->B`] GROUP_INV) THEN
  ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))]);;

let GALOIS_GROUP_COMPOSE = prove
 (`!(h:A->B) f g k l.
        f IN group_carrier(galois_group(k,l) h) /\
        g IN group_carrier(galois_group(k,l) h)
        ==> f o g IN group_carrier(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f:B->B`; `g:B->B`]
    GROUP_MUL) THEN
  ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))]);;

let GALOIS_GROUP_PERMUTES = prove
 (`!(h:A->B) f k l.
        f IN group_carrier(galois_group(k,l) h) ==> f permutes ring_carrier l`,
  SIMP_TAC[IN_GALOIS_GROUP]);;

let GALOIS_GROUP_RING_AUTOMORPHISM = prove
 (`!(h:A->B) f k l.
        f IN group_carrier(galois_group(k,l) h) ==> ring_automorphism l f`,
  SIMP_TAC[IN_GALOIS_GROUP]);;

let GALOIS_GROUP_RING_HOMOMORPHISM = prove
 (`!(h:A->B) f k l.
        f IN group_carrier(galois_group(k,l) h) ==> ring_homomorphism(l,l) f`,
  SIMP_TAC[IN_GALOIS_GROUP; ring_automorphism;
           RING_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let GALOIS_GROUP_FIXES = prove
 (`!(h:A->B) f k l x.
        f IN group_carrier(galois_group(k,l) h) /\ x IN ring_carrier k
        ==> f(h x) = h x`,
  SIMP_TAC[IN_GALOIS_GROUP]);;

let GALOIS_GROUP_IN_CARRIER = prove
 (`!(h:A->B) f k l x.
        f IN group_carrier(galois_group(k,l) h) /\ x IN ring_carrier l
        ==> f x IN ring_carrier l`,
  MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE]);;

let GALOIS_GROUP_IMAGE_INVERSE = prove
 (`!(h:A->B) f k l s.
        f IN group_carrier(galois_group(k,l) h) /\ IMAGE f s = s
        ==> IMAGE (inverse f) s = s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:B. x) s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[IMAGE_ID]]);;

let GALOIS_GROUP_RING_MONOMORPHISM = prove
 (`!(h:A->B) f k l.
        f IN group_carrier(galois_group(k,l) h) ==> ring_monomorphism(l,l) f`,
  MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM; ring_automorphism;
            RING_ISOMORPHISM_IMP_MONOMORPHISM]);;

let GALOIS_GROUP_I = prove
 (`!(h:A->B) k l. I IN group_carrier(galois_group(k,l) h)`,
  MESON_TAC[GROUP_ID; GALOIS_GROUP]);;

let GALOIS_GROUP_ACTION = prove
 (`(!(h:A->B) k l.
        group_action (galois_group(k,l) h) (ring_carrier l) (\f x. f x)) /\
   (!(h:A->B) k l. group_action (galois_group(k,l) h) (:B->bool) IMAGE)`,
  REWRITE_TAC[group_action; CONJUNCT2 GALOIS_GROUP; IN_UNIV] THEN
  REWRITE_TAC[I_THM; o_THM; IMAGE_I; IMAGE_o] THEN
  MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE]);;

let GALOIS_GROUP_POLY_EVAL = prove
 (`!(h:A->B) f k l p x.
        ring_homomorphism(k,l) h /\ f IN group_carrier(galois_group(k,l) h) /\
        p IN ring_carrier(poly_ring k (:1)) /\ x IN ring_carrier l
        ==> poly_eval l (h o p) (f x) = f(poly_eval l (h o p) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `x:B`; `f:B->B`;
                 `(h:A->B) o (p:(1->num)->A)`]
    POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM;
                  IN_RING_POLYNOMIAL_CARRIER_COMPOSE];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `m:1->num` THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`;
                 `(p:(1->num)->A) m`] GALOIS_GROUP_FIXES) THEN
  ASM_MESON_TAC[IN_POLY_RING_CARRIER; ring_polynomial; ring_powerseries]);;

(* A permutation of l that agrees on each finite set with an element of the  *)
(* Galois group is in the Galois group.                                      *)

let GALOIS_GROUP_LOCAL = prove
 (`!(h:A->B) k l f.
        f permutes ring_carrier l /\
        (!s. FINITE s
             ==> ?g. g IN group_carrier(galois_group(k,l) h) /\
                     !x. x IN s ==> g x = f x)
        ==> f IN group_carrier(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_GALOIS_GROUP; ring_automorphism; RING_ISOMORPHISM] THEN
  ASM_SIMP_TAC[PERMUTES_IMAGE] THEN
  REWRITE_TAC[ring_homomorphism] THEN
  ASM_SIMP_TAC[PERMUTES_IMAGE; SUBSET_REFL] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `{ring_0 l:B}`) THEN
    REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM; RING_HOMOMORPHISM_0];
    FIRST_ASSUM(MP_TAC o SPEC `{ring_1 l:B}`) THEN
    REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM; RING_HOMOMORPHISM_1];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `{x:B,ring_neg l x}`) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `g:B->B`] RING_HOMOMORPHISM_NEG) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `{x:B,y,ring_add l x y}`) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `g:B->B`] RING_HOMOMORPHISM_ADD) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `{x:B,y,ring_mul l x y}`) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `g:B->B`] RING_HOMOMORPHISM_MUL) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM];
    ASM_MESON_TAC[PERMUTES_INJECTIVE];
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `{(h:A->B) a}`) THEN
    REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[GALOIS_GROUP_FIXES]]);;

let GALOIS_GROUP_ANTIMONO = prove
 (`!(h:A->B) (h':C->B) k k' l.
        IMAGE h (ring_carrier k) SUBSET IMAGE h' (ring_carrier k')
        ==> group_carrier(galois_group(k',l) h') SUBSET
            group_carrier(galois_group(k,l) h)`,
  REWRITE_TAC[SUBSET; IN_GALOIS_GROUP; FORALL_IN_IMAGE; IN_IMAGE] THEN
  MESON_TAC[]);;

(* The Galois group depends on the base only through the image of k (compare *)
(* EXTENSION_DEGREE_EQ_IMAGE and FINITE_EXTENSION_EQ_IMAGE).                 *)

let GALOIS_GROUP_EQ_IMAGE = prove
 (`!(h:A->B) (h':C->B) k k' l.
        IMAGE h (ring_carrier k) = IMAGE h' (ring_carrier k')
        ==> galois_group(k,l) h = galois_group(k',l) h'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[galois_group] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `f:B->B` THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\u:B->bool. !y. y IN u ==> (f:B->B) y = y`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE]);;

let TRIVIAL_GALOIS_GROUP = prove
 (`!(h:A->B) k l.
        ring_carrier l SUBSET IMAGE h (ring_carrier k)
        ==> trivial_group(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[trivial_group; GALOIS_GROUP; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `f:B->B` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PERMUTES_I; RING_AUTOMORPHISM_I; I_THM] THEN
  MATCH_MP_TAC PERMUTES_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
  ASM_REWRITE_TAC[PERMUTES_I; I_THM] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Galois groups and extensions of homomorphisms. For algebraic l over k and *)
(* a monomorphism j from l into m, f |-> j o f (restricted to the carrier of *)
(* l) is a bijection from the Galois group onto the extensions of j o h to l *)
(* with image inside j(l); for normal l this is all of them. Hence the       *)
(* Galois group of a finite extension has at most separable_degree elements, *)
(* with equality exactly for normal extensions, and for normal extensions it *)
(* acts transitively on the roots of each minimal polynomial.                *)
(* ------------------------------------------------------------------------- *)

let GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_GEN = prove
 (`!(h:A->B) (j:B->C) k l m.
        algebraic_extension(k,l) h /\ ring_monomorphism(l,m) j
        ==> BIJ (\f. RESTRICTION (ring_carrier l) (j o f))
                (group_carrier(galois_group(k,l) h))
                {g | g IN ring_homomorphism_extensions (k,l,m) (h,j o h) /\
                     IMAGE g (ring_carrier l) SUBSET IMAGE j (ring_carrier l)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN
   `ring_homomorphism(k:A ring,l:B ring) h /\
    ring_homomorphism(l:B ring,m:C ring) j`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ring_monomorphism]; ALL_TAC] THEN
  REWRITE_TAC[BIJ; INJ; SURJ; IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ r ==> (p /\ q) /\ (p /\ r)`) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `f:B->B` THEN REWRITE_TAC[IN_GALOIS_GROUP] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
      ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `l:B ring` THEN
      ASM_MESON_TAC[ring_automorphism; RING_ISOMORPHISM_IMP_HOMOMORPHISM];
      SIMP_TAC[IMAGE_RESTRICTION; SUBSET_REFL; IMAGE_o] THEN
      ASM_SIMP_TAC[PERMUTES_IMAGE; SUBSET_REFL]];
    MAP_EVERY X_GEN_TAC [`f1:B->B`; `f2:B->B`] THEN
    REWRITE_TAC[IN_GALOIS_GROUP] THEN STRIP_TAC THEN
    MATCH_MP_TAC PERMUTES_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `x:B`) THEN
    ASM_REWRITE_TAC[RESTRICTION; o_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism] o
      check (fun th ->
        concl th = `ring_monomorphism(l:B ring,m:C ring) j`)) THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    X_GEN_TAC `g:B->C` THEN
    REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM; o_THM] THEN
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`g:B->C`; `j:B->C`; `l:B ring`; `l:B ring`; `m:C ring`]
    RING_HOMOMORPHISM_MONOMORPHISM_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:B->B` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `f = \x. if x IN ring_carrier l then (e:B->B) x else x` THEN
  SUBGOAL_THEN `!x. x IN ring_carrier l ==> (f:B->B) x = e x` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC `e:B->B` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ring_carrier k ==> (f:B->B)((h:A->B) x) = h x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->B) x IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism] o
      check (fun th ->
        concl th = `ring_monomorphism(l:B ring,m:C ring) j`)) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_automorphism l (f:B->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[IN_GALOIS_GROUP] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `ring_automorphism l (e:B->B)` MP_TAC THENL
     [MATCH_MP_TAC RING_AUTOMORPHISM_EQ THEN EXISTS_TAC `f:B->B` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[ring_automorphism; RING_ISOMORPHISM] THEN STRIP_TAC] THEN
    EXPAND_TAC "f" THEN ASM_REWRITE_TAC[RESTRICT_PERMUTES_EQ];
    MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_SIMP_TAC[RESTRICTION_IN_EXTENSIONAL; RESTRICTION; o_THM]]);;

let GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS = prove
 (`!(h:A->B) k l.
        algebraic_extension(k,l) h
        ==> BIJ (RESTRICTION (ring_carrier l))
                (group_carrier(galois_group(k,l) h))
                (ring_homomorphism_extensions(k,l,l) (h,h))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `l:B ring`; `l:B ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_GEN) THEN
  ASM_REWRITE_TAC[RING_MONOMORPHISM_I; I_O_ID; IMAGE_I; ETA_AX] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `g:B->B` THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
  EQ_TAC THEN SIMP_TAC[] THEN SIMP_TAC[ring_homomorphism]);;

let GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_NORMAL = prove
 (`!(h:A->B) (j:B->C) k l m.
        normal_extension(k,l) h /\ integral_domain m /\
        ring_homomorphism(l,m) j
        ==> BIJ (\f. RESTRICTION (ring_carrier l) (j o f))
                (group_carrier(galois_group(k,l) h))
                (ring_homomorphism_extensions (k,l,m) (h,j o h))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_GEN) THEN
  ASM_SIMP_TAC[NORMAL_IMP_ALGEBRAIC_EXTENSION;
               FIELD_RING_HOMOMORPHISM_MONOMORPHISM;
               INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `g:B->C` THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM; o_THM] THEN
  EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(s:C->bool) = t ==> s SUBSET t`) THEN
  MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `m:C ring`] THEN
  ASM_REWRITE_TAC[]);;

let CARD_GALOIS_GROUP_LE = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> FINITE(group_carrier(galois_group(k,l) h)) /\
            CARD(group_carrier(galois_group(k,l) h)) <=
            extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS) THEN
  ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION] THEN
  REWRITE_TAC[BIJ; INJ; SURJ] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `h:A->B`; `k:A ring`; `l:B ring`; `l:B ring`]
    CARD_RING_HOMOMORPHISM_EXTENSIONS_LE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
               RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  SUBGOAL_THEN
   `ring_homomorphism_extensions (k,l,l) (h,h) =
    IMAGE (RESTRICTION (ring_carrier l))
          (group_carrier(galois_group(k:A ring,l:B ring) h))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`RESTRICTION (ring_carrier l):(B->B)->(B->B)`;
                 `group_carrier(galois_group(k:A ring,l:B ring) h)`]
    FINITE_IMAGE_INJ_EQ) THEN
  MP_TAC(ISPECL [`RESTRICTION (ring_carrier l):(B->B)->(B->B)`;
                 `group_carrier(galois_group(k:A ring,l:B ring) h)`]
    CARD_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let FINITE_GALOIS_GROUP = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h ==> FINITE(group_carrier(galois_group(k,l) h))`,
  SIMP_TAC[CARD_GALOIS_GROUP_LE]);;

let CARD_GALOIS_GROUP_LE_SEPARABLE_DEGREE,
    NORMAL_EXTENSION_EQ_CARD_GALOIS_GROUP = (CONJ_PAIR o prove)
 (`(!(h:A->B) k l.
        finite_extension(k,l) h
        ==> CARD(group_carrier(galois_group(k,l) h)) <=
            separable_degree(k,l) h) /\
   (!(h:A->B) k l.
        finite_extension(k,l) h
        ==> (normal_extension(k,l) h <=>
             CARD(group_carrier(galois_group(k,l) h)) =
             separable_degree(k,l) h))`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(B#num) ring`
   (X_CHOOSE_THEN `j:B->B#num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM o
    check (fun th ->
      concl th = `field_extension(l:B ring,m) (j:B->B#num)`)) THEN
  SUBGOAL_THEN `ring_homomorphism(k:A ring,m) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `k:A ring`; `l:B ring`;
                 `m:(B#num) ring`] HAS_SIZE_SEPARABLE_DEGREE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `m:(B#num) ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_GEN) THEN
  ASM_REWRITE_TAC[BIJ; INJ; SURJ] THEN
  ABBREV_TAC
   `S = {g | g IN ring_homomorphism_extensions (k:A ring,l:B ring,m)
                    (h:A->B,(j:B->B#num) o h) /\
             IMAGE g (ring_carrier l) SUBSET IMAGE j (ring_carrier l)}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `S SUBSET ring_homomorphism_extensions (k:A ring,l:B ring,m)
                (h:A->B,(j:B->B#num) o h)`
  ASSUME_TAC THENL [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(S:(B->B#num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(group_carrier(galois_group(k:A ring,l:B ring) h)) =
    CARD(S:(B->B#num)->bool)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `FINITE(S:(B->B#num)->bool)` THEN
    SUBGOAL_THEN
     `S = IMAGE (\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f))
                (group_carrier(galois_group(k:A ring,l:B ring) h))`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f)`;
                   `group_carrier(galois_group(k:A ring,l:B ring) h)`]
      FINITE_IMAGE_INJ_EQ) THEN
    MP_TAC(ISPECL [`\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f)`;
                   `group_carrier(galois_group(k:A ring,l:B ring) h)`]
      CARD_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSET] THEN
  SUBGOAL_THEN
   `CARD(S:(B->B#num)->bool) =
    CARD(ring_homomorphism_extensions (k:A ring,l:B ring,m)
           (h:A->B,(j:B->B#num) o h)) <=>
    S = ring_homomorphism_extensions (k,l,m) (h,j o h)`
  SUBST1_TAC THENL
   [EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "S" THEN
  REWRITE_TAC[SET_RULE
   `{x:B->B#num | x IN s /\ P x} = s <=> !x. x IN s ==> P x`] THEN
  EQ_TAC THENL
   [REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM; o_THM] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:(B#num)->bool) = t ==> s SUBSET t`) THEN
    MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `m:(B#num) ring`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
                 ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
                 RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `m:(B#num) ring`] NORMAL_EXTENSION_EQ_EMBEDDINGS) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC `g:B->B#num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `RESTRICTION (ring_carrier l) (g:B->B#num) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
      ASM_SIMP_TAC[o_THM; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
    `RESTRICTION (ring_carrier l) (g:B->B#num) IN S`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:B->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o AP_TERM `\u:B->B#num. IMAGE u (ring_carrier l)`))) THEN
  SIMP_TAC[IMAGE_RESTRICTION; SUBSET_REFL; IMAGE_o] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IMAGE]);;

let GALOIS_GROUP_ORBIT = prove
 (`!(h:A->B) k l x.
        normal_extension(k,l) h /\ x IN ring_carrier l
        ==> {f x | f IN group_carrier(galois_group(k,l) h)} =
            {y | y IN ring_carrier l /\
                 poly_eval l (h o minimal_polynomial(k,l) h x) y = ring_0 l}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `h:A->B`; `RESTRICTION (ring_carrier l) (f:B->B)`;
                   `k:A ring`; `l:B ring`; `l:B ring`; `x:B`]
      RING_HOMOMORPHISM_EXTENSIONS_ROOT) THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM; GALOIS_GROUP_FIXES];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(B#num) ring`
   (X_CHOOSE_THEN `j:B->B#num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM o
    check (fun th ->
      concl th = `field_extension(l:B ring,m) (j:B->B#num)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th ->
      concl th = `ring_monomorphism(l:B ring,m) (j:B->B#num)`)) THEN
  SUBGOAL_THEN `ring_homomorphism(k:A ring,m) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:A->B) o minimal_polynomial(k,l) h x IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:(B#num) ring`; `h:A->B`;
                 `(j:B->B#num) o (h:A->B)`; `x:B`; `(j:B->B#num) y`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_IN_CARRIER] THEN
    REWRITE_TAC[GSYM o_ASSOC] THEN
    MP_TAC(ISPECL [`l:B ring`; `m:(B#num) ring`; `y:B`; `j:B->B#num`;
                   `(h:A->B) o minimal_polynomial(k,l) h x`]
      POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `e:B->B#num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `m:(B#num) ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_NORMAL) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
               ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
  REWRITE_TAC[BIJ; SURJ] THEN
  DISCH_THEN(MP_TAC o SPEC `RESTRICTION (ring_carrier l) (e:B->B#num)` o
             CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:B->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o C AP_THM `x:B`))) THEN
  ASM_REWRITE_TAC[RESTRICTION; o_THM] THEN DISCH_TAC THEN
  EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism] o
      check (fun th ->
        concl th = `ring_monomorphism(l:B ring,m) (j:B->B#num)`)) THEN
  ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE]);;

let GALOIS_GROUP_ORBIT_FINITE = prove
 (`!(h:A->B) k l x.
        algebraic_extension(k,l) h /\ x IN ring_carrier l
        ==> FINITE {f x | f IN group_carrier(galois_group(k,l) h)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:A->B) o minimal_polynomial(k,l) h x IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{y | y IN ring_carrier l /\
                   poly_eval l ((h:A->B) o minimal_polynomial(k,l) h x) y =
                   ring_0 l}` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o minimal_polynomial(k,l) h x`]
      POLY_ROOT_BOUND) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; POLY_RING_CLAUSES] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL;
                  MINIMAL_POLYNOMIAL_IN_CARRIER; MINIMAL_POLYNOMIAL_NONZERO];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`;
                 `minimal_polynomial(k,l) (h:A->B) x`; `x:B`]
    GALOIS_GROUP_POLY_EVAL) THEN
  ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `l:B ring`; `l:B ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
  ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Galois extensions: normal and separable. A finite extension is Galois     *)
(* exactly when its Galois group has [l:k] elements, and exactly when it is  *)
(* the splitting extension of a separable polynomial.                        *)
(* ------------------------------------------------------------------------- *)

let galois_extension = new_definition
 `galois_extension (k:A ring,l:B ring) (h:A->B) <=>
        normal_extension (k,l) h /\ separable_extension (k,l) h`;;

let GALOIS_IMP_NORMAL_EXTENSION = prove
 (`!(h:A->B) k l. galois_extension(k,l) h ==> normal_extension(k,l) h`,
  SIMP_TAC[galois_extension]);;

let GALOIS_IMP_SEPARABLE_EXTENSION = prove
 (`!(h:A->B) k l. galois_extension(k,l) h ==> separable_extension(k,l) h`,
  SIMP_TAC[galois_extension]);;

let GALOIS_IMP_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l. galois_extension(k,l) h ==> algebraic_extension(k,l) h`,
  SIMP_TAC[galois_extension; NORMAL_IMP_ALGEBRAIC_EXTENSION]);;

let GALOIS_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l. galois_extension(k,l) h ==> field_extension(k,l) h`,
  SIMP_TAC[galois_extension; NORMAL_IMP_FIELD_EXTENSION]);;

let GALOIS_EXTENSION_REFL = prove
 (`!k:A ring. galois_extension(k,k) I <=> field k`,
  REWRITE_TAC[galois_extension; NORMAL_EXTENSION_REFL;
              SEPARABLE_EXTENSION_REFL]);;

let GALOIS_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism(k,l) f
        ==> galois_extension(k,l) f`,
  SIMP_TAC[galois_extension; NORMAL_EXTENSION_ISOMORPHISM;
           SEPARABLE_EXTENSION_ISOMORPHISM]);;

let GALOIS_EXTENSION_EQ_CARD = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> (galois_extension(k,l) h <=>
             CARD(group_carrier(galois_group(k,l) h)) =
             extension_degree(k,l) h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[galois_extension] THEN
  ASM_SIMP_TAC[NORMAL_EXTENSION_EQ_CARD_GALOIS_GROUP;
               GSYM SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    CARD_GALOIS_GROUP_LE_SEPARABLE_DEGREE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SEPARABLE_DEGREE_LE_EXTENSION_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let GALOIS_EXTENSION_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension(k,l) f /\ field_extension(l,m) g /\
        galois_extension(k,m) (g o f)
        ==> galois_extension(l,m) g`,
  REWRITE_TAC[galois_extension] THEN
  MESON_TAC[NORMAL_EXTENSION_INTERMEDIATE; SEPARABLE_EXTENSION_INTERMEDIATE]);;

let GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h <=>
        ?p. poly_separable k p /\ splitting_extension(k,l) h p`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[galois_extension] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      PRIMITIVE_ELEMENT_THEOREM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` (CONJUNCTS_THEN2 ASSUME_TAC
      (ASSUME_TAC o AP_TERM `ring_carrier:B ring->B->bool`))) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) a` ASSUME_TAC THENL
     [ASM_MESON_TAC[algebraic_extension; NORMAL_IMP_ALGEBRAIC_EXTENSION];
      ALL_TAC] THEN
    EXISTS_TAC `minimal_polynomial(k,l) (h:A->B) a` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[separable_extension; separable_element]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      MINIMAL_POLYNOMIAL) THEN
    ASM_REWRITE_TAC[splitting_extension] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `l:B ring`; `l:B ring`;
                   `a:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
     [SYM(check (fun th -> rand(concl th) = `ring_carrier(l:B ring)`) th)]) THEN
    TRANS_TAC SUBSET_TRANS
     `ring_carrier(subring_generated l
       (IMAGE (h:A->B) (ring_carrier k) UNION
        {x | x IN ring_carrier l /\
             poly_eval l (h o minimal_polynomial (k,l) h a) x =
             ring_0 l}))` THEN
    REWRITE_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC SUBRING_GENERATED_MONO THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o (p:(1->num)->A)) x = ring_0 l}` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  REWRITE_TAC[galois_extension] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SPLITTING_IMP_FINITE_EXTENSION];
    ASM_MESON_TAC[SPLITTING_EXTENSION_IMP_NORMAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) o (p:(1->num)->A) IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(R:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
      POLY_ROOT_BOUND) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; POLY_RING_CLAUSES] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN R ==> algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[algebraic_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN R ==> separable_element(k,l) (h:A->B) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:B) IN R` THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[separable_element] THEN MATCH_MP_TAC POLY_SEPARABLE_DIVISOR THEN
    EXISTS_TAC `p:(1->num)->A` THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER; MINIMAL_POLYNOMIAL_DIVIDES] THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    ASM_REWRITE_TAC[GSYM poly_eval];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `R:B->bool`]
    SEPARABLE_EXTENSION_GENERATED_BY_SEPARABLE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION R) = l`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[SUBRING_EQ_SUBFIELD_GENERATED; FIELD_ALGEBRAIC_EXTENSION]);;

(* ------------------------------------------------------------------------- *)
(* Fixed fields. The fixed field of a set G of maps is the set of elements   *)
(* of l fixed by all of them; for endomorphisms of a field it is a subfield, *)
(* used as a ring through subfield_generated l (fixed_field l G) with I.     *)
(* ------------------------------------------------------------------------- *)

let fixed_field = new_definition
 `fixed_field (l:B ring) (G:(B->B)->bool) =
        {x | x IN ring_carrier l /\ !f. f IN G ==> f x = x}`;;

let IN_FIXED_FIELD = prove
 (`!(l:B ring) G x.
        x IN fixed_field l G <=>
        x IN ring_carrier l /\ !f. f IN G ==> f x = x`,
  REWRITE_TAC[fixed_field; IN_ELIM_THM]);;

let FIXED_FIELD_SUBSET = prove
 (`!(l:B ring) G. fixed_field l G SUBSET ring_carrier l`,
  SIMP_TAC[fixed_field; SUBSET; IN_ELIM_THM]);;

let SUBFIELD_OF_FIXED_FIELD = prove
 (`!(l:B ring) G.
        field l /\ (!f. f IN G ==> ring_endomorphism l f)
        ==> fixed_field l G subfield_of l`,
  REWRITE_TAC[fixed_field] THEN MATCH_ACCEPT_TAC SUBFIELD_OF_COMMON_FIXPOINTS);;

let FIXED_FIELD_ANTIMONO = prove
 (`!(l:B ring) G H. G SUBSET H ==> fixed_field l H SUBSET fixed_field l G`,
  REWRITE_TAC[fixed_field] THEN SET_TAC[]);;

let FIXED_FIELD_EMPTY = prove
 (`!l:B ring. fixed_field l {} = ring_carrier l`,
  REWRITE_TAC[fixed_field; NOT_IN_EMPTY] THEN SET_TAC[]);;

let FIXED_FIELD_UNION = prove
 (`!(l:B ring) G H.
        fixed_field l (G UNION H) = fixed_field l G INTER fixed_field l H`,
  REWRITE_TAC[fixed_field] THEN SET_TAC[]);;

let IMAGE_SUBSET_FIXED_FIELD_GALOIS_GROUP = prove
 (`!(h:A->B) k l.
        ring_homomorphism(k,l) h
        ==> IMAGE h (ring_carrier k) SUBSET
            fixed_field l (group_carrier(galois_group(k,l) h))`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_FIXED_FIELD] THEN
  MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; GALOIS_GROUP_FIXES]);;

let FIXED_FIELD_GALOIS_SUBSET = prove
 (`!(h:A->B) k l H.
        field_extension(k,l) h /\ H SUBSET group_carrier(galois_group(k,l) h)
        ==> fixed_field l H subfield_of l /\
            IMAGE h (ring_carrier k) SUBSET fixed_field l H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN
    ASM_MESON_TAC[SUBSET; GALOIS_GROUP_RING_HOMOMORPHISM;
                  ring_endomorphism];
    TRANS_TAC SUBSET_TRANS
     `fixed_field l (group_carrier(galois_group(k,l) (h:A->B)))` THEN
    ASM_SIMP_TAC[FIXED_FIELD_ANTIMONO;
                 IMAGE_SUBSET_FIXED_FIELD_GALOIS_GROUP;
                 RING_MONOMORPHISM_IMP_HOMOMORPHISM]]);;

let SUBSET_GALOIS_GROUP_FIXED_FIELD = prove
 (`!(l:B ring) G.
        field l /\
        (!f. f IN G ==> f permutes ring_carrier l /\ ring_automorphism l f)
        ==> G SUBSET
            group_carrier
             (galois_group(subfield_generated l (fixed_field l G),l) I)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated l (fixed_field l G)) =
    fixed_field (l:B ring) G`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
    MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN
    ASM_MESON_TAC[RING_AUTOMORPHISM_IMP_ENDOMORPHISM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUBSET; IN_GALOIS_GROUP; I_THM; IN_FIXED_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Artin: a finite group G of automorphisms of a field l is the Galois group *)
(* of l over its fixed field, of degree CARD G. The proof follows Lang       *)
(* (Algebra, VI 1.8): the polynomial with simple roots the G-orbit of an     *)
(* element a has its coefficients in the fixed field, so a is separable over *)
(* the fixed field with split minimal polynomial of degree at most CARD G.   *)
(* The same argument for the full Galois group of an algebraic extension     *)
(* characterizes Galois extensions by their fixed field.                     *)
(* ------------------------------------------------------------------------- *)

let RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD = prove
 (`!(l:B ring) G s.
        (!f. f IN G ==> ring_automorphism l f /\ IMAGE f s = s) /\
        FINITE s /\ s SUBSET ring_carrier l
        ==> !m. ring_product (poly_ring l (:1)) s
                  (\b. poly_sub l (poly_var l one) (poly_const l b)) m
                IN fixed_field l G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = ring_product (poly_ring l (:1)) s
     (\b. poly_sub l (poly_var l one) (poly_const (l:B ring) b))` THEN
  SUBGOAL_THEN `P IN ring_carrier(poly_ring (l:B ring) (:1))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[RING_PRODUCT]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:B->B. f IN G ==> f o P = (P:(1->num)->B)` ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ring_automorphism; RING_ISOMORPHISM_IMP_HOMOMORPHISM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`; `(:1)`]
      RING_HOMOMORPHISM_POLY_RINGS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPECL
     [`\b. poly_sub l (poly_var l one) (poly_const (l:B ring) b)`;
      `s:B->bool`] o MATCH_MP RING_HOMOMORPHISM_PRODUCT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "P" THEN
    TRANS_TAC EQ_TRANS
     `ring_product (poly_ring l (:1)) s
        (\b. poly_sub l (poly_var l one)
                        (poly_const (l:B ring) ((f:B->B) b)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `b:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(b:B) IN ring_carrier l` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`;
                     `poly_var (l:B ring) (one:1)`;
                     `poly_const (l:B ring) (b:B):(1->num)->B`]
        POLY_COMPOSE_HOMOMORPHISM_SUB) THEN
      ASM_REWRITE_TAC[RING_POWERSERIES_VAR; RING_POWERSERIES_CONST] THEN
      DISCH_THEN SUBST1_TAC THEN BINOP_TAC THENL
       [MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_VAR;
        MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_CONST] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`poly_ring (l:B ring) (:1)`; `f:B->B`;
                   `\b. poly_sub l (poly_var l one) (poly_const (l:B ring) b)`;
                   `s:B->bool`] RING_PRODUCT_IMAGE) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B`) THEN
      ASM_REWRITE_TAC[ring_automorphism; RING_ISOMORPHISM] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B`) THEN ASM_SIMP_TAC[o_DEF];
    ALL_TAC] THEN
  X_GEN_TAC `m:1->num` THEN REWRITE_TAC[IN_FIXED_FIELD] THEN CONJ_TAC THENL
   [UNDISCH_TAC `P IN ring_carrier(poly_ring (l:B ring) (:1))` THEN
    SIMP_TAC[IN_POLY_RING_CARRIER; ring_polynomial; ring_powerseries];
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `m:1->num` o C MATCH_MP
      (ASSUME `(f:B->B) IN G`)) THEN
    REWRITE_TAC[o_THM]]);;

let MINIMAL_POLYNOMIAL_FINITE_ORBIT = prove
 (`!(h:A->B) k l G a.
        field_extension(k,l) h /\
        G subgroup_of symmetric_group(ring_carrier l) /\
        (!f. f IN G ==> ring_automorphism l f) /\
        fixed_field l G SUBSET IMAGE h (ring_carrier k) /\
        a IN ring_carrier l /\ FINITE {f a | f IN G}
        ==> algebraic_over(k,l) h a /\ separable_element(k,l) h a /\
            poly_splits_over(k,l) h (minimal_polynomial(k,l) h a) /\
            poly_deg k (minimal_polynomial(k,l) h a) <= CARD {f a | f IN G}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `t = {(f:B->B) a | f IN G}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[subgroup_of; SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM] o
    check (fun th -> is_binary "subgroup_of" (concl th))) THEN
  SUBGOAL_THEN `(t:B->bool) SUBSET ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:B) IN t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `I:B->B` THEN ASM_REWRITE_TAC[I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:B->B. f IN G ==> IMAGE f t = t` ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:B` THEN EQ_TAC THENL
     [ASM_MESON_TAC[o_THM];
      DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `inverse (f:B->B) (y:B)` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[PERMUTES_INVERSES];
        EXISTS_TAC `inverse (f:B->B) o (g:B->B)` THEN
        ASM_SIMP_TAC[o_THM]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `G:(B->B)->bool`; `t:B->bool`]
    RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `t:B->bool`] RING_PRODUCT_X_MINUS_A) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  ABBREV_TAC `P = ring_product (poly_ring l (:1)) t
     (\b. poly_sub l (poly_var l one) (poly_const (l:B ring) b))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `(:1)`; `P:(1->num)->B`]
    POLY_RING_MONOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ring_polynomial k (q:(1->num)->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `~((q:(1->num)->A) = poly_0 k)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `q:(1->num)->A`]
      POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MONIC_IMP_NONZERO THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING] THEN ASM_MESON_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg k (q:(1->num)->A) = CARD(t:B->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `q:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_splits_over (k,l) (h:A->B) q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[poly_splits_over]; ALL_TAC] THEN
  SUBGOAL_THEN `poly_separable k (q:(1->num)->A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `q:(1->num)->A`]
      POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_extend (k,l) (h:A->B) (\v:1. a) q = ring_0 l`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval] THEN
    MP_TAC(ASSUME `{x | x IN ring_carrier l /\
                        poly_eval l (P:(1->num)->B) x = ring_0 l} = t`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:B`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) a` ASSUME_TAC THENL
   [REWRITE_TAC[algebraic_over] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `q:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (poly_ring k (:1)) (minimal_polynomial (k,l) (h:A->B) a) q`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_DIVIDES]; ALL_TAC] THEN
  ASM_REWRITE_TAC[separable_element] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLY_SEPARABLE_DIVISOR THEN EXISTS_TAC `q:(1->num)->A` THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
    REWRITE_TAC[poly_splits_over] THEN MATCH_MP_TAC POLY_SPLITS_DIVISOR THEN
    EXISTS_TAC `P:(1->num)->B` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONIC_IMP_NONZERO THEN
      ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING] THEN
      ASM_MESON_TAC[RING_POLYNOMIAL];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(h:A->B) o (q:(1->num)->A) = P`)) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_DIVIDES_HOMOMORPHIC_IMAGE o CONJ
       (ISPEC `(:1)` (MATCH_MP RING_HOMOMORPHISM_POLY_RINGS
         (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`))) o
       check (fun th -> concl th = `ring_divides (poly_ring k (:1))
               (minimal_polynomial (k,l) (h:A->B) a) q`)) THEN
      REWRITE_TAC[]];
    TRANS_TAC LE_TRANS `poly_deg k (q:(1->num)->A)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MINIMAL_POLYNOMIAL_DEG_LE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[LE_REFL]]]);;

let ARTIN_FIXED_FIELD = prove
 (`!(l:B ring) G.
        field l /\ FINITE G /\ G subgroup_of symmetric_group(ring_carrier l) /\
        (!f. f IN G ==> ring_automorphism l f)
        ==> finite_extension(subfield_generated l (fixed_field l G),l) I /\
            galois_extension(subfield_generated l (fixed_field l G),l) I /\
            extension_degree(subfield_generated l (fixed_field l G),l) I =
            CARD G /\
            group_carrier
             (galois_group(subfield_generated l (fixed_field l G),l) I) = G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f:B->B. f IN G ==> f permutes ring_carrier l` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [subgroup_of] o
      check (fun th -> is_binary "subgroup_of" (concl th))) THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `G SUBSET
    group_carrier(galois_group(subfield_generated l (fixed_field l G),l)
                               (I:B->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_GALOIS_GROUP_FIXED_FIELD THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `fixed_field l (G:(B->B)->bool) subfield_of l` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN
    ASM_MESON_TAC[RING_AUTOMORPHISM_IMP_ENDOMORPHISM];
    ALL_TAC] THEN
  ABBREV_TAC `K = subfield_generated l (fixed_field l (G:(B->B)->bool))` THEN
  SUBGOAL_THEN `ring_carrier K = fixed_field l (G:(B->B)->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(K,l) (I:B->B)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:B. a IN ring_carrier l
          ==> algebraic_over(K,l) I a /\ separable_element(K,l) I a /\
              poly_splits_over(K,l) I (minimal_polynomial(K,l) I a) /\
              poly_deg K (minimal_polynomial(K,l) I a) <= CARD(G:(B->B)->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `G:(B->B)->bool`; `a:B`]
      MINIMAL_POLYNOMIAL_FINITE_ORBIT) THEN
    ASM_REWRITE_TAC[IMAGE_I; SUBSET_REFL] THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LE_TRANS `CARD(IMAGE (\f:B->B. f a) G)` THEN
    ASM_SIMP_TAC[CARD_IMAGE_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_extension(K,l) (I:B->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[algebraic_extension]; ALL_TAC] THEN
  SUBGOAL_THEN `separable_extension(K,l) (I:B->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[separable_extension]; ALL_TAC] THEN
  SUBGOAL_THEN `normal_extension(K,l) (I:B->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `CARD(G:(B->B)->bool)`]
    SEPARABLE_EXTENSION_BOUNDED_DEGREE) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`] CARD_GALOIS_GROUP_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `CARD(G:(B->B)->bool) <= CARD(group_carrier(galois_group(K,l) (I:B->B)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `extension_degree(K,l) (I:B->B) = CARD(G:(B->B)->bool)`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[galois_extension] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GALOIS_EXTENSION_EQ_FIXED_FIELD = prove
 (`!(h:A->B) k l.
        algebraic_extension(k,l) h
        ==> (galois_extension(k,l) h <=>
             fixed_field l (group_carrier(galois_group(k,l) h)) =
             IMAGE h (ring_carrier k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC[IMAGE_SUBSET_FIXED_FIELD_GALOIS_GROUP] THEN
    REWRITE_TAC[SUBSET; IN_FIXED_FIELD] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM MINIMAL_POLYNOMIAL_DEG_EQ_1] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      GALOIS_GROUP_ORBIT) THEN
    ASM_SIMP_TAC[GALOIS_IMP_NORMAL_EXTENSION] THEN
    SUBGOAL_THEN
     `{f x | f IN group_carrier(galois_group(k:A ring,l) (h:A->B))} = {x:B}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      ASM_MESON_TAC[GROUP_ID; GALOIS_GROUP; I_THM];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `minimal_polynomial(k,l) (h:A->B) x`]
      POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT_EQ) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER; MINIMAL_POLYNOMIAL_NONZERO;
                 CARD_SING] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT;
                    GALOIS_IMP_NORMAL_EXTENSION];
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE)] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[GALOIS_IMP_SEPARABLE_EXTENSION; separable_extension;
                    separable_element];
      ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN ring_carrier l
        ==> separable_element(k,l) (h:A->B) a /\
            poly_splits_over(k,l) h (minimal_polynomial(k,l) h a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `group_carrier(galois_group(k:A ring,l:B ring) h)`; `a:B`]
      MINIMAL_POLYNOMIAL_FINITE_ORBIT) THEN
    ASM_REWRITE_TAC[GALOIS_GROUP_SUBGROUP; SUBSET_REFL] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM]; ALL_TAC] THEN
    MATCH_MP_TAC GALOIS_GROUP_ORBIT_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[galois_extension; NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT;
               separable_extension]);;

let FIXED_FIELD_GALOIS_GROUP = prove
 (`!(h:A->B) k l.
        galois_extension(k,l) h
        ==> fixed_field l (group_carrier(galois_group(k,l) h)) =
            IMAGE h (ring_carrier k)`,
  MESON_TAC[GALOIS_EXTENSION_EQ_FIXED_FIELD; GALOIS_IMP_ALGEBRAIC_EXTENSION]);;

(* ------------------------------------------------------------------------- *)
(* Elements of the Galois group are determined by their values on            *)
(* generators, and the Galois group depends on the extension only up to      *)
(* isomorphism; in particular all splitting extensions of a polynomial have  *)
(* isomorphic Galois groups.                                                 *)
(* ------------------------------------------------------------------------- *)

let GALOIS_GROUP_EQ_ON_GENERATORS = prove
 (`!(h:A->B) f g k l s.
        field l /\
        subfield_generated l (IMAGE h (ring_carrier k) UNION s) = l /\
        f IN group_carrier(galois_group(k,l) h) /\
        g IN group_carrier(galois_group(k,l) h) /\
        (!x. x IN s ==> f x = g x)
        ==> f = g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:B->B`; `g:B->B`; `l:B ring`; `l:B ring`;
                 `IMAGE (h:A->B) (ring_carrier k) UNION s`]
    RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM; GALOIS_GROUP_FIXES];
    DISCH_TAC] THEN
  MATCH_MP_TAC PERMUTES_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
  ASM_MESON_TAC[GALOIS_GROUP_PERMUTES]);;

let ISOMORPHIC_GALOIS_GROUPS = prove
 (`!(h:A->B) (h':A->C) (f:B->C) k l l'.
        ring_homomorphism(k,l) h /\ ring_isomorphism(l,l') f /\
        (!x. x IN ring_carrier k ==> f(h x) = h' x)
        ==> galois_group(k,l) h isomorphic_group galois_group(k,l') h'`,
  let lemma = prove
   (`!(h:A->B) (h':A->C) (f:B->C) f' k l l' s.
        ring_isomorphisms(l,l') (f,f') /\
        (!x. x IN ring_carrier k ==> h x IN ring_carrier l /\ f(h x) = h' x) /\
        s IN group_carrier(galois_group(k,l) h)
        ==> (\y. if y IN ring_carrier l' then f(s(f' y)) else y) IN
            group_carrier(galois_group(k,l') h')`,
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_GALOIS_GROUP] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_isomorphisms]) THEN
    SUBGOAL_THEN `ring_automorphism l' ((f:B->C) o (s:B->B) o (f':C->B))`
    ASSUME_TAC THENL
     [REWRITE_TAC[ring_automorphism] THEN
      MATCH_MP_TAC RING_ISOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_ISOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
        ASM_REWRITE_TAC[GSYM ring_automorphism] THEN
        ASM_MESON_TAC[ring_isomorphism; RING_ISOMORPHISMS_SYM];
        ASM_MESON_TAC[ring_isomorphism]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[RESTRICT_PERMUTES_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_automorphism]) THEN
      REWRITE_TAC[RING_ISOMORPHISM; o_DEF] THEN MESON_TAC[];
      MATCH_MP_TAC RING_AUTOMORPHISM_EQ THEN
      EXISTS_TAC `(f:B->C) o (s:B->B) o (f':C->B)` THEN
      ASM_SIMP_TAC[o_THM];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (is_forall o concl) o
        check (fun th -> free_in `h':A->C` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]]) in
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `f':C->B` o GEN_REWRITE_RULE I
   [ring_isomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_isomorphisms]) THEN
  SUBGOAL_THEN `!x. x IN ring_carrier k ==> (h:A->B) x IN ring_carrier l`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  EXISTS_TAC `\s y. if y IN ring_carrier l' then (f:B->C)(s((f':C->B) y))
                    else y` THEN
  EXISTS_TAC `\t x. if x IN ring_carrier l then (f':C->B)(t((f:B->C) x))
                    else x` THEN
  REWRITE_TAC[GROUP_ISOMORPHISMS; GROUP_HOMOMORPHISM; SUBSET;
              FORALL_IN_IMAGE] THEN
  REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:B->B` THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `l:B ring`] THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:B->B`; `t:B->B`] THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:C` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:B->B)((f':C->B) y) IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE;
                    RING_HOMOMORPHISM_IN_CARRIER];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:B->C)((t:B->B)((f':C->B) y)) IN ring_carrier l'`
      (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    X_GEN_TAC `s:B->B` THEN DISCH_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:B` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(f:B->C) x IN ring_carrier l'`
        (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE];
      ASM_MESON_TAC[permutes]];
    X_GEN_TAC `t:C->C` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`h':A->C`; `l':C ring`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[RING_ISOMORPHISMS_SYM] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:C` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(f':C->B) y IN ring_carrier l`
        (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE];
      ASM_MESON_TAC[permutes]]]);;

let ISOMORPHIC_GALOIS_GROUPS_SPLITTING = prove
 (`!(h:A->B) (h':A->C) k l l' p.
        splitting_extension(k,l) h p /\ splitting_extension(k,l') h' p
        ==> galois_group(k,l) h isomorphic_group galois_group(k,l') h'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `h':A->C`; `k:A ring`; `l:B ring`; `l':C ring`;
                 `p:(1->num)->A`] SPLITTING_EXTENSION_UNIQUE_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:B->C` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC ISOMORPHIC_GALOIS_GROUPS THEN EXISTS_TAC `f:B->C` THEN
  ASM_MESON_TAC[SPLITTING_IMP_FIELD_EXTENSION;
                FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

(* A Galois extension stays Galois, with isomorphic Galois group, when l is  *)
(* replaced by its image under a homomorphism into a field.                  *)

let GALOIS_EXTENSION_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (j:B->C) k l m.
        galois_extension(k,l) h /\ field m /\ ring_homomorphism(l,m) j
        ==> galois_extension
             (k,subfield_generated m (IMAGE j (ring_carrier l))) (j o h) /\
            galois_group(k,l) h isomorphic_group
            galois_group(k,subfield_generated m (IMAGE j (ring_carrier l)))
                        (j o h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`j:B->C`; `l:B ring`; `m:C ring`]
    RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = IMAGE (j:B->C) (ring_carrier l)` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[galois_extension] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:A->B`; `(j:B->C) o (h:A->B)`; `I:A->A`; `j:B->C`;
                     `k:A ring`; `l:B ring`; `k:A ring`;
                     `subfield_generated m (s:C->bool)`]
        NORMAL_EXTENSION_ISOMORPHIC_IMAGE) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[RING_ISOMORPHISM_I; I_THM; o_THM;
                   GALOIS_IMP_NORMAL_EXTENSION];
      MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`;
                     `subfield_generated m (s:C->bool)`]
        SEPARABLE_EXTENSION_TRANS_EQ) THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_ISOMORPHISM; GALOIS_IMP_SEPARABLE_EXTENSION;
                   SEPARABLE_EXTENSION_ISOMORPHISM]];
    MATCH_MP_TAC ISOMORPHIC_GALOIS_GROUPS THEN EXISTS_TAC `j:B->C` THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; o_THM]]);;

(* ------------------------------------------------------------------------- *)
(* The Galois correspondence. An intermediate field of an extension (k,l) h  *)
(* is a subfield s of l containing the image of k, used as a ring through    *)
(* subfield_generated l s with the inclusion I; its Galois group             *)
(* galois_group(subfield_generated l s,l) I is a subgroup of                 *)
(* galois_group(k,l) h. For a Galois extension the fixed field of the Galois *)
(* group of l over s is s, and for a finite extension the Galois group of l  *)
(* over the fixed field of a subgroup H is H (Artin). So for finite Galois   *)
(* extensions s and H are in an inclusion-reversing bijection, with degrees  *)
(* and indices matching.                                                     *)
(* ------------------------------------------------------------------------- *)

let SUBGROUP_OF_GALOIS_GROUP = prove
 (`!(h:A->B) k l G.
        G subgroup_of galois_group(k,l) h <=>
        G subgroup_of symmetric_group(ring_carrier l) /\
        G SUBSET group_carrier(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [galois_group] THEN
  REWRITE_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_EQ; GSYM galois_group]);;

let IN_GALOIS_GROUP_INTERMEDIATE = prove
 (`!(h:A->B) f k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> (f IN group_carrier(galois_group(subfield_generated l s,l) I) <=>
             f IN group_carrier(galois_group(k,l) h) /\
             !x. x IN s ==> f x = x)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[IN_GALOIS_GROUP; CARRIER_SUBFIELD_GENERATED_SUBFIELD; I_THM] THEN
  EQ_TAC THEN SIMP_TAC[] THEN ASM SET_TAC[]);;

let GALOIS_GROUP_INTERMEDIATE_SUBGROUP = prove
 (`!(h:A->B) k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> group_carrier(galois_group(subfield_generated l s,l) I)
            subgroup_of galois_group(k,l) h`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBGROUP_OF_GALOIS_GROUP; GALOIS_GROUP_SUBGROUP; SUBSET] THEN
  X_GEN_TAC `f:B->B` THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    IN_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_SIMP_TAC[]);;

let GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED = prove
 (`!(h:A->B) k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> subgroup_generated (galois_group(k,l) h)
              (group_carrier(galois_group(subfield_generated l s,l) I)) =
            galois_group(subfield_generated l s,l) I`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUPS_EQ] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               GALOIS_GROUP_INTERMEDIATE_SUBGROUP] THEN
  REWRITE_TAC[SUBGROUP_GENERATED; GALOIS_GROUP]);;

let GALOIS_EXTENSION_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s.
        galois_extension(k,l) h /\ IMAGE h (ring_carrier k) SUBSET s
        ==> galois_extension(subfield_generated l s,l) I`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_EXTENSION_INTERMEDIATE THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN
  ASM_REWRITE_TAC[I_O_ID] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
               FIELD_EXTENSION_SUBFIELD_GENERATED]);;

let FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE = prove
 (`!(h:A->B) k l s.
        galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> fixed_field l
             (group_carrier(galois_group(subfield_generated l s,l) I)) = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (s:B->bool)`; `l:B ring`]
    FIXED_FIELD_GALOIS_GROUP) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[GALOIS_EXTENSION_SUBFIELD_GENERATED];
    ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD]]);;

let GALOIS_GROUP_FIXED_FIELD = prove
 (`!(h:A->B) k l H.
        finite_extension(k,l) h /\ H subgroup_of galois_group(k,l) h
        ==> fixed_field l H subfield_of l /\
            IMAGE h (ring_carrier k) SUBSET fixed_field l H /\
            group_carrier
             (galois_group(subfield_generated l (fixed_field l H),l) I) = H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [SUBGROUP_OF_GALOIS_GROUP]) THEN
  SUBGOAL_THEN `!f:B->B. f IN H ==> ring_automorphism l f` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; GALOIS_GROUP_RING_AUTOMORPHISM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN
    ASM_MESON_TAC[RING_AUTOMORPHISM_IMP_ENDOMORPHISM];
    TRANS_TAC SUBSET_TRANS
     `fixed_field l (group_carrier(galois_group(k:A ring,l:B ring) h))` THEN
    ASM_SIMP_TAC[FIXED_FIELD_ANTIMONO; IMAGE_SUBSET_FIXED_FIELD_GALOIS_GROUP;
                 RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    MP_TAC(ISPECL [`l:B ring`; `H:(B->B)->bool`] ARTIN_FIXED_FIELD) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `group_carrier(galois_group(k:A ring,l:B ring) h)` THEN
    ASM_SIMP_TAC[CARD_GALOIS_GROUP_LE]]);;

let GALOIS_CORRESPONDENCE = prove
 (`!(h:A->B) k l.
     finite_extension(k,l) h /\ galois_extension(k,l) h
     ==> (!H. H subgroup_of galois_group(k,l) h
              ==> fixed_field l H subfield_of l /\
                  IMAGE h (ring_carrier k) SUBSET fixed_field l H /\
                  group_carrier(galois_group
                    (subfield_generated l (fixed_field l H),l) I) = H) /\
         (!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
              ==> group_carrier(galois_group(subfield_generated l s,l) I)
                  subgroup_of galois_group(k,l) h /\
                  fixed_field l
                    (group_carrier(galois_group(subfield_generated l s,l) I)) =
                  s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC GALOIS_GROUP_FIXED_FIELD THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[GALOIS_GROUP_INTERMEDIATE_SUBGROUP] THEN
    MATCH_MP_TAC FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[]]);;

let GALOIS_GROUP_ANTIMONO_EQ = prove
 (`!(h:A->B) k l s t.
        galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        t subfield_of l /\ IMAGE h (ring_carrier k) SUBSET t
        ==> (group_carrier(galois_group(subfield_generated l t,l) I) SUBSET
             group_carrier(galois_group(subfield_generated l s,l) I) <=>
             s SUBSET t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `t:B->bool`]
      FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
      GEN_REWRITE_TAC BINOP_CONV [SYM th1; SYM th2])) THEN
    MATCH_MP_TAC FIXED_FIELD_ANTIMONO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC GALOIS_GROUP_ANTIMONO THEN
    ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD]]);;

let FIXED_FIELD_ANTIMONO_EQ = prove
 (`!(h:A->B) k l G H.
        finite_extension(k,l) h /\
        G subgroup_of galois_group(k,l) h /\ H subgroup_of galois_group(k,l) h
        ==> (fixed_field l H SUBSET fixed_field l G <=> G SUBSET H)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[FIXED_FIELD_ANTIMONO] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `G:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `H:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rand(concl th) = `H:(B->B)->bool`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rand(concl th) = `G:(B->B)->bool`)) THEN
  MATCH_MP_TAC GALOIS_GROUP_ANTIMONO THEN
  ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD]);;

let GALOIS_CORRESPONDENCE_DEGREE = prove
 (`!(h:A->B) k l s.
     finite_extension(k,l) h /\ galois_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
     ==> extension_degree(subfield_generated l s,l) I =
         CARD(group_carrier(galois_group(subfield_generated l s,l) I)) /\
         extension_degree(k,subfield_generated l s) h *
         CARD(group_carrier(galois_group(subfield_generated l s,l) I)) =
         CARD(group_carrier(galois_group(k,l) h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_EXTENSION_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (s:B->bool)`; `l:B ring`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `l:B ring`]
    EXTENSION_DEGREE_TOWER_LAW) THEN
  ASM_SIMP_TAC[I_O_ID; FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
               FIELD_EXTENSION_SUBFIELD_GENERATED]);;

let GALOIS_CORRESPONDENCE_INDEX = prove
 (`!(h:A->B) k l s.
     finite_extension(k,l) h /\ galois_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
     ==> CARD {right_coset (galois_group(k,l) h)
                (group_carrier(galois_group(subfield_generated l s,l) I)) x |
               x | x IN group_carrier(galois_group(k,l) h)} =
         extension_degree(k,subfield_generated l s) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_CORRESPONDENCE_DEGREE) THEN
  MP_TAC(ISPECL
   [`galois_group(k:A ring,l:B ring) h`;
    `group_carrier(galois_group(subfield_generated l (s:B->bool),l) I)`]
   LAGRANGE_THEOREM_RIGHT) THEN
  ASM_SIMP_TAC[CARD_GALOIS_GROUP_LE; GALOIS_GROUP_INTERMEDIATE_SUBGROUP] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(CARD(group_carrier
        (galois_group(subfield_generated l s,l) (I:B->B))) = 0)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhs(concl th) =
      `extension_degree(subfield_generated l s,l) (I:B->B)`)) THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_0; FIELD_EXTENSION_SUBFIELD_GENERATED];
    MATCH_MP_TAC(MESON[EQ_MULT_RCANCEL]
     `!a b c n:num. a * n = c /\ b * n = c /\ ~(n = 0) ==> a = b`) THEN
    MAP_EVERY EXISTS_TAC
     [`CARD(group_carrier(galois_group(k:A ring,l:B ring) h))`;
      `CARD(group_carrier
         (galois_group(subfield_generated l s,l) (I:B->B)))`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Normal intermediate fields. For a normal extension l over k every         *)
(* homomorphism from an intermediate field into l fixing the image of k      *)
(* extends to an element of the Galois group. An intermediate field s is     *)
(* normal over k exactly when it is mapped into itself by the Galois group,  *)
(* and for a Galois extension exactly when the Galois group of l over s is a *)
(* normal subgroup. Restriction to a normal intermediate field s is then an  *)
(* epimorphism onto the Galois group of s over k with kernel the Galois      *)
(* group of l over s, whence the quotient theorem.                           *)
(* ------------------------------------------------------------------------- *)

(* The extension goes through an algebraic closure m of l: extend j o g from *)
(* s to l, then the extension comes from the Galois group since l is normal  *)
(* (GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_NORMAL).                   *)
let GALOIS_GROUP_EXTEND_HOMOMORPHISM = prove
 (`!(h:A->B) g k l s.
     normal_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
     ring_homomorphism(subfield_generated l s,l) g /\
     (!x. x IN ring_carrier k ==> g(h x) = h x)
     ==> ?f. f IN group_carrier(galois_group(k,l) h) /\
             !x. x IN s ==> f x = g x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `S = subfield_generated l (s:B->bool)` THEN
  SUBGOAL_THEN `ring_carrier S = (s:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension(k,S) (h:A->B) /\ field_extension(S,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
                 FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_extension(S,l) (I:B->B)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `S:B ring`; `l:B ring`]
      ALGEBRAIC_EXTENSION_TRANS_EQ) THEN
    ASM_SIMP_TAC[I_O_ID];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(B#num) ring`
   (X_CHOOSE_THEN `j:B->B#num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION o
    check (fun th ->
      concl th = `algebraic_extension(l:B ring,m) (j:B->B#num)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM o
    check (fun th ->
      concl th = `field_extension(l:B ring,m) (j:B->B#num)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th ->
      concl th = `ring_monomorphism(l:B ring,m) (j:B->B#num)`)) THEN
  MP_TAC(ISPECL [`S:B ring`; `l:B ring`; `m:(B#num) ring`; `I:B->B`;
                 `(j:B->B#num) o (g:B->B)`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[I_THM; o_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:B->B#num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `m:(B#num) ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_NORMAL) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
               ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
  REWRITE_TAC[BIJ; SURJ] THEN
  DISCH_THEN(MP_TAC o SPEC `RESTRICTION (ring_carrier l) (e:B->B#num)` o
             CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->B) x IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (h:A->B) (ring_carrier k) SUBSET s` THEN
      UNDISCH_TAC `(x:A) IN ring_carrier k` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:B->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBFIELD_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `x:B`) THEN
  ASM_REWRITE_TAC[RESTRICTION; o_THM] THEN
  SUBGOAL_THEN `(e:B->B#num) x = j((g:B->B) x)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [ring_monomorphism] o
    check (fun th ->
      concl th = `ring_monomorphism(l:B ring,m) (j:B->B#num)`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE];
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]]);;

let GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE = prove
 (`!(h:A->B) f k l s.
        field l /\ s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        normal_extension(k,subfield_generated l s) h /\
        f IN group_carrier(galois_group(k,l) h)
        ==> IMAGE f s = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `l:B ring`]
    NORMAL_EXTENSION_IMAGES_EQ) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; IMAGE_I;
               FIELD_IMP_INTEGRAL_DOMAIN; I_THM;
               RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[GALOIS_GROUP_FIXES; GALOIS_GROUP_RING_HOMOMORPHISM;
                RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED]);;

(* A stable intermediate field contains all roots of the minimal polynomials *)
(* of its elements (GALOIS_GROUP_ORBIT), so these split over it.             *)
let NORMAL_EXTENSION_EQ_GALOIS_STABLE = prove
 (`!(h:A->B) k l s.
        normal_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> (normal_extension(k,subfield_generated l s) h <=>
             !f. f IN group_carrier(galois_group(k,l) h)
                 ==> IMAGE f s SUBSET s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:B->bool) = t ==> s SUBSET t`) THEN
    MATCH_MP_TAC GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `S = subfield_generated l (s:B->bool)` THEN
  SUBGOAL_THEN `ring_carrier S = (s:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension(k,S) (h:A->B) /\ field_extension(S,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
                 FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  REWRITE_TAC[NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `S:B ring`; `l:B ring`]
      ALGEBRAIC_EXTENSION_TRANS_EQ) THEN
    ASM_SIMP_TAC[I_O_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBFIELD_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    GALOIS_GROUP_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `S:B ring`; `l:B ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_MONOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[I_O_ID; I_THM; FIELD_EXTENSION_IMP_HOMOMORPHISM;
               FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `q = minimal_polynomial (k,l) (h:A->B) x` THEN
  REWRITE_TAC[poly_splits_over] THEN
  MATCH_MP_TAC POLY_SPLITS_MONOMORPHIC_PREIMAGE THEN
  MAP_EVERY EXISTS_TAC [`l:B ring`; `I:B->B`] THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM; I_O_ID; IMAGE_I] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT;
                  poly_splits_over];
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    EXPAND_TAC "q" THEN ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:B` o
      GEN_REWRITE_RULE I [EXTENSION] o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:B->B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B`) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[]]);;

let GALOIS_GROUP_INTERMEDIATE_NORMAL_SUBGROUP = prove
 (`!(h:A->B) k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        (!f. f IN group_carrier(galois_group(k,l) h) ==> IMAGE f s SUBSET s)
        ==> group_carrier(galois_group(subfield_generated l s,l) I)
            normal_subgroup_of galois_group(k,l) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION] THEN
  ASM_SIMP_TAC[GALOIS_GROUP_INTERMEDIATE_SUBGROUP] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:B->B` THEN
  MP_TAC(ISPECL [`h:A->B`; `t:B->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    IN_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`;
                 `group_conjugation (galois_group(k,l) (h:A->B)) f t`;
                 `k:A ring`; `l:B ring`; `s:B->bool`]
    IN_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION] THEN
  REWRITE_TAC[group_conjugation; CONJUNCT2(CONJUNCT2 GALOIS_GROUP)] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `inverse (f:B->B) y IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `inverse(f:B->B)`) THEN
    ASM_SIMP_TAC[GALOIS_GROUP_INVERSE; SUBSET; FORALL_IN_IMAGE];
    ASM_SIMP_TAC[]] THEN
  ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_INVERSES]);;

let GALOIS_CORRESPONDENCE_NORMAL = prove
 (`!(h:A->B) k l s.
     galois_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
     ==> (normal_extension(k,subfield_generated l s) h <=>
          group_carrier(galois_group(subfield_generated l s,l) I)
          normal_subgroup_of galois_group(k,l) h) /\
         (normal_extension(k,subfield_generated l s) h <=>
          !f. f IN group_carrier(galois_group(k,l) h) ==> IMAGE f s SUBSET s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_NORMAL_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    NORMAL_EXTENSION_EQ_GALOIS_STABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  EQ_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_INTERMEDIATE_NORMAL_SUBGROUP]; ALL_TAC] THEN
  REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[IN_FIXED_FIELD] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; SUBFIELD_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `t:B->B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inverse(f:B->B)`) THEN
  ASM_SIMP_TAC[GALOIS_GROUP_INVERSE] THEN
  DISCH_THEN(MP_TAC o SPEC `t:B->B`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`;
                 `group_conjugation (galois_group(k,l) (h:A->B))
                    (inverse f) t`;
                 `k:A ring`; `l:B ring`; `s:B->bool`]
    IN_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[group_conjugation; CONJUNCT2(CONJUNCT2 GALOIS_GROUP)] THEN
  ASM_SIMP_TAC[o_THM; MATCH_MP PERMUTES_INVERSE_INVERSE
   (ASSUME `(f:B->B) permutes ring_carrier l`)] THEN
  DISCH_THEN(MP_TAC o AP_TERM `f:B->B`) THEN
  ASM_MESON_TAC[PERMUTES_INVERSES]);;

let GALOIS_GROUP_RESTRICT = prove
 (`!(h:A->B) f k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        f IN group_carrier(galois_group(k,l) h) /\ IMAGE f s = s
        ==> (\x. if x IN s then f x else x) IN
            group_carrier(galois_group(k,subfield_generated l s) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  ABBREV_TAC `S = subfield_generated l (s:B->bool)` THEN
  SUBGOAL_THEN `ring_carrier S = (s:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(S,S) (f:B->B)` ASSUME_TAC THENL
   [SUBGOAL_THEN `S = subring_generated l (s:B->bool)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
    THENL
     [EXPAND_TAC "S" THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SUBRING_EQ_SUBFIELD_GENERATED THEN
      ASM_MESON_TAC[subfield_of];
      MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN EXPAND_TAC "S" THEN
      ASM_SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_GALOIS_GROUP; RESTRICT_PERMUTES_EQ] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PERMUTES_INJECTIVE];
    REWRITE_TAC[ring_automorphism; RING_ISOMORPHISM] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC `f:B->B` THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `IMAGE (f:B->B) s = s` THEN SET_TAC[];
      ASM_MESON_TAC[PERMUTES_INJECTIVE]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->B) x IN s` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `IMAGE (h:A->B) (ring_carrier k) SUBSET s` THEN
      UNDISCH_TAC `(x:A) IN ring_carrier k` THEN SET_TAC[];
      ASM_MESON_TAC[GALOIS_GROUP_FIXES]]]);;

let GALOIS_GROUP_RESTRICTION_HOMOMORPHISM = prove
 (`!(h:A->B) k l s.
     field l /\ s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
     normal_extension(k,subfield_generated l s) h
     ==> group_homomorphism
           (galois_group(k,l) h,galois_group(k,subfield_generated l s) h)
           (\f x. if x IN s then f x else x) /\
         group_kernel
           (galois_group(k,l) h,galois_group(k,subfield_generated l s) h)
           (\f x. if x IN s then f x else x) =
         group_carrier(galois_group(subfield_generated l s,l) I)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:B->B. f IN group_carrier(galois_group(k,l) (h:A->B))
             ==> IMAGE f s = s /\
                 (\x. if x IN s then f x else x) IN
                 group_carrier(galois_group(k,subfield_generated l s) h)`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE THEN
      MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`] THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC GALOIS_GROUP_RESTRICT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC RESTRICT_COMPOSE THEN
    EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; SUBFIELD_OF_IMP_SUBSET];
    REWRITE_TAC[group_kernel; CONJUNCT1(CONJUNCT2 GALOIS_GROUP)] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `f:B->B` THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      IN_GALOIS_GROUP_INTERMEDIATE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; I_THM] THEN MESON_TAC[]]);;

let GALOIS_GROUP_RESTRICTION = prove
 (`!(h:A->B) k l s.
     normal_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
     normal_extension(k,subfield_generated l s) h
     ==> group_epimorphism
           (galois_group(k,l) h,galois_group(k,subfield_generated l s) h)
           (\f x. if x IN s then f x else x) /\
         group_kernel
           (galois_group(k,l) h,galois_group(k,subfield_generated l s) h)
           (\f x. if x IN s then f x else x) =
         group_carrier(galois_group(subfield_generated l s,l) I)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_FIELD_EXTENSION o
    check (fun th -> concl th = `normal_extension(k:A ring,l:B ring) h`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[group_epimorphism] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
     [group_homomorphism] o
     check (fun th -> is_binary "group_homomorphism" (concl th)));
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `t:B->B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `t:B->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_GROUP_EXTEND_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBST1_TAC(SYM(CONJUNCT1(ISPEC `t:B->B` I_O_ID))) THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `subfield_generated l (s:B->bool)` THEN
      REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
      ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM];
      ASM_MESON_TAC[GALOIS_GROUP_FIXES]];
    MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES o
    check (fun th -> concl th =
      `t IN group_carrier
             (galois_group(k,subfield_generated l s) (h:A->B))`)) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  REWRITE_TAC[permutes; FUN_EQ_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `x:B` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* For any field extension l, an intermediate field s normal over k is       *)
(* mapped onto itself by the Galois group, and restriction to s is a         *)
(* homomorphism, an epimorphism when l is normal                             *)
(* (GALOIS_GROUP_RESTRICTION_NORMAL).                                        *)

let GALOIS_GROUP_RESTRICTION_NORMAL = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ s subfield_of l /\
        normal_extension(k,subfield_generated l s) h
        ==> (!f. f IN group_carrier(galois_group(k,l) h) ==> IMAGE f s = s) /\
            group_homomorphism
             (galois_group(k,l) h,galois_group(k,subfield_generated l s) h)
             (\f x. if x IN s then f x else x) /\
            (normal_extension(k,l) h
             ==> group_epimorphism
                  (galois_group(k,l) h,galois_group(k,subfield_generated l s) h)
                  (\f x. if x IN s then f x else x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier k) SUBSET s` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION) THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    ASM_SIMP_TAC[field_extension; ring_monomorphism; ring_homomorphism;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE];
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
                  GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
                  GALOIS_GROUP_RESTRICTION) THEN
    ASM_SIMP_TAC[]]);;

let GALOIS_GROUP_QUOTIENT = prove
 (`!(h:A->B) k l s.
     normal_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
     normal_extension(k,subfield_generated l s) h
     ==> quotient_group (galois_group(k,l) h)
           (group_carrier(galois_group(subfield_generated l s,l) I))
         isomorphic_group galois_group(k,subfield_generated l s) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_GROUP_RESTRICTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_ACCEPT_TAC FIRST_GROUP_EPIMORPHISM_THEOREM);;

(* For a Galois extension, an intermediate field s whose Galois group is a   *)
(* normal subgroup is a Galois extension of k, with Galois group the         *)
(* quotient.                                                                 *)

let GALOIS_EXTENSION_NORMAL_SUBGROUP = prove
 (`!(h:A->B) k l s.
     galois_extension(k,l) h /\
     s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
     group_carrier(galois_group(subfield_generated l s,l) I)
     normal_subgroup_of galois_group(k,l) h
     ==> galois_extension(k,subfield_generated l s) h /\
         quotient_group (galois_group(k,l) h)
           (group_carrier(galois_group(subfield_generated l s,l) I))
         isomorphic_group galois_group(k,subfield_generated l s) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `normal_extension(k,subfield_generated l s) (h:A->B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      GALOIS_CORRESPONDENCE_NORMAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GALOIS_GROUP_QUOTIENT; GALOIS_IMP_NORMAL_EXTENSION] THEN
  ASM_REWRITE_TAC[galois_extension] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `l:B ring`]
    SEPARABLE_EXTENSION_SUBFIELD) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[I_O_ID; GALOIS_IMP_SEPARABLE_EXTENSION;
               FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
               FIELD_EXTENSION_SUBFIELD_GENERATED]);;

(* ------------------------------------------------------------------------- *)
(* The fundamental theorem of Galois theory for a finite Galois extension,   *)
(* collecting the correspondence, the order reversal in both directions, the *)
(* degrees and indices, normality and the quotient theorem.                  *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_GALOIS_THEORY = prove
 (`!(h:A->B) k l.
     finite_extension(k,l) h /\ galois_extension(k,l) h
     ==> (!H. H subgroup_of galois_group(k,l) h
              ==> fixed_field l H subfield_of l /\
                  IMAGE h (ring_carrier k) SUBSET fixed_field l H /\
                  group_carrier(galois_group
                    (subfield_generated l (fixed_field l H),l) I) = H) /\
         (!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
              ==> group_carrier(galois_group(subfield_generated l s,l) I)
                  subgroup_of galois_group(k,l) h /\
                  fixed_field l
                    (group_carrier(galois_group(subfield_generated l s,l) I)) =
                  s) /\
         (!s t. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
                t subfield_of l /\ IMAGE h (ring_carrier k) SUBSET t
                ==> (group_carrier
                      (galois_group(subfield_generated l t,l) I) SUBSET
                     group_carrier
                      (galois_group(subfield_generated l s,l) I) <=>
                     s SUBSET t)) /\
         (!G H. G subgroup_of galois_group(k,l) h /\
                H subgroup_of galois_group(k,l) h
                ==> (fixed_field l H SUBSET fixed_field l G <=> G SUBSET H)) /\
         (!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
              ==> extension_degree(subfield_generated l s,l) I =
                  CARD(group_carrier
                        (galois_group(subfield_generated l s,l) I)) /\
                  extension_degree(k,subfield_generated l s) h *
                  CARD(group_carrier
                        (galois_group(subfield_generated l s,l) I)) =
                  CARD(group_carrier(galois_group(k,l) h)) /\
                  CARD {right_coset (galois_group(k,l) h)
                         (group_carrier
                           (galois_group(subfield_generated l s,l) I)) x |
                        x | x IN group_carrier(galois_group(k,l) h)} =
                  extension_degree(k,subfield_generated l s) h) /\
         (!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
              ==> (normal_extension(k,subfield_generated l s) h <=>
                   group_carrier(galois_group(subfield_generated l s,l) I)
                   normal_subgroup_of galois_group(k,l) h)) /\
         (!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
              normal_extension(k,subfield_generated l s) h
              ==> quotient_group (galois_group(k,l) h)
                    (group_carrier(galois_group(subfield_generated l s,l) I))
                  isomorphic_group galois_group(k,subfield_generated l s) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_NORMAL_EXTENSION) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC GALOIS_GROUP_FIXED_FIELD THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[GALOIS_GROUP_INTERMEDIATE_SUBGROUP] THEN
    MATCH_MP_TAC FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC GALOIS_GROUP_ANTIMONO_EQ THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FIXED_FIELD_ANTIMONO_EQ THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      GALOIS_CORRESPONDENCE_INDEX) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      GALOIS_CORRESPONDENCE_DEGREE) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      GALOIS_CORRESPONDENCE_NORMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    MATCH_MP_TAC GALOIS_GROUP_QUOTIENT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The lattice of intermediate fields and conjugation. The Galois group of l *)
(* over the subfield generated by any set s consists of the automorphisms of *)
(* l fixing s pointwise, so the Galois group over the compositum of two      *)
(* subfields is the intersection of their Galois groups. For a finite Galois *)
(* extension the Galois group over the intersection of two intermediate      *)
(* fields is the subgroup generated by their Galois groups, and for a finite *)
(* extension the fixed field of the intersection of two subgroups of the     *)
(* Galois group is the compositum of their fixed fields: the Galois          *)
(* correspondence is a lattice anti-isomorphism. Conjugating a set of maps   *)
(* by a permutation f of l maps its fixed field by f, and the Galois group   *)
(* over the image of s under an automorphism f is the conjugate by f of the  *)
(* Galois group over s.                                                      *)
(* ------------------------------------------------------------------------- *)

let IN_GALOIS_GROUP_SUBFIELD_GENERATED = prove
 (`!(l:B ring) s f.
        field l
        ==> (f IN group_carrier(galois_group(subfield_generated l s,l) I) <=>
             f permutes ring_carrier l /\ ring_automorphism l f /\
             !x. x IN s ==> f x = x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_GALOIS_GROUP; I_THM] THEN
  ASM_CASES_TAC `(f:B->B) permutes ring_carrier l` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ring_automorphism l (f:B->B)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:B) IN ring_carrier l` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[permutes]];
    SUBGOAL_THEN
     `ring_carrier(subfield_generated l (s:B->bool)) SUBSET
      {x | x IN ring_carrier l /\ (f:B->B) x = x}`
    MP_TAC THENL
     [ASM_SIMP_TAC[SUBFIELD_GENERATED_MINIMAL_EQ; SUBFIELD_OF_FIXPOINTS;
                   RING_AUTOMORPHISM_IMP_ENDOMORPHISM] THEN
      ASM SET_TAC[];
      SET_TAC[]]]);;

let GALOIS_GROUP_COMPOSITUM = prove
 (`!(l:B ring) s t.
        field l
        ==> group_carrier(galois_group(subfield_generated l (s UNION t),l) I) =
            group_carrier(galois_group(subfield_generated l s,l) I) INTER
            group_carrier(galois_group(subfield_generated l t,l) I)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER] THEN
  ASM_SIMP_TAC[IN_GALOIS_GROUP_SUBFIELD_GENERATED; IN_UNION] THEN
  MESON_TAC[]);;

let FIXED_FIELD_SUBGROUP_GENERATED = prove
 (`!(h:A->B) k l G.
        G SUBSET group_carrier(galois_group(k,l) h)
        ==> fixed_field l
              (group_carrier(subgroup_generated (galois_group(k,l) h) G)) =
            fixed_field l G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIXED_FIELD_ANTIMONO THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_FIXED_FIELD] THEN X_GEN_TAC `a:B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `group_carrier(subgroup_generated (galois_group(k,l) (h:A->B)) G) SUBSET
    {f | f IN group_carrier(galois_group(k,l) h) /\ f a = a}`
  MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[subgroup_of; SUBSET; IN_ELIM_THM; CONJUNCT2 GALOIS_GROUP] THEN
  SIMP_TAC[I_THM] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h` GROUP_ID) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)];
    X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GALOIS_GROUP_INVERSE] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP PERMUTES_INVERSES o
      MATCH_MP GALOIS_GROUP_PERMUTES) THEN
    DISCH_THEN(MP_TAC o SPEC `a:B`) THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GALOIS_GROUP_COMPOSE; o_THM]]);;

(* For a Galois extension the fixed field of a set of generators of the      *)
(* Galois group is the image of k, and l is generated over the image of k by *)
(* a set s exactly when the identity is the only element of the Galois group *)
(* fixing s pointwise (no finiteness is needed: the fixed field of the       *)
(* Galois group over an intermediate field is that field). For a finite      *)
(* Galois group generated by g, an element a generates l over the image of k *)
(* exactly when the powers g^j that fix a are those with j a multiple of the *)
(* order of the group.                                                       *)

let FIXED_FIELD_GALOIS_GROUP_GENERATORS = prove
 (`!(h:A->B) k l G.
        galois_extension(k,l) h /\
        G SUBSET group_carrier(galois_group(k,l) h) /\
        subgroup_generated (galois_group(k,l) h) G = galois_group(k,l) h
        ==> fixed_field l G = IMAGE h (ring_carrier k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `G:(B->B)->bool`]
    FIXED_FIELD_SUBGROUP_GENERATED) THEN
  ASM_SIMP_TAC[FIXED_FIELD_GALOIS_GROUP] THEN MESON_TAC[]);;

let GALOIS_EXTENSION_GENERATORS_EQ = prove
 (`!(h:A->B) k l s.
        galois_extension(k,l) h
        ==> (subfield_generated l (IMAGE h (ring_carrier k) UNION s) = l <=>
             !f. f IN group_carrier(galois_group(k,l) h) /\
                 (!x. x IN s ==> f x = x)
                 ==> f = I)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`] THEN
    ASM_REWRITE_TAC[I_THM] THEN
    MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h` GROUP_ID) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`;
    `ring_carrier(subfield_generated l
       (IMAGE (h:A->B) (ring_carrier k) UNION s))`]
   FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; ASSUME `field(l:B ring)`] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k) UNION s`]
      SUBFIELD_GENERATED_SUBSET_CARRIER) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_homomorphism] o
      MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_FIXED_FIELD] THEN X_GEN_TAC `x:B` THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `f:B->B` THEN
  SIMP_TAC[IN_GALOIS_GROUP_SUBFIELD_GENERATED; ASSUME `field(l:B ring)`;
           IN_UNION] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `f = (I:B->B)` (fun th -> REWRITE_TAC[th; I_THM]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_GALOIS_GROUP] THEN
  ASM_MESON_TAC[FUN_IN_IMAGE]);;

let GALOIS_EXTENSION_SIMPLE_EQ = prove
 (`!(h:A->B) k l a.
        galois_extension(k,l) h
        ==> (subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l <=>
             !f. f IN group_carrier(galois_group(k,l) h) /\ f a = a ==> f = I)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `(a:B) INSERT s = s UNION {a}`] THEN
  ASM_SIMP_TAC[GALOIS_EXTENSION_GENERATORS_EQ; IN_SING; FORALL_UNWIND_THM2]);;

let GALOIS_EXTENSION_SIMPLE_CYCLIC_EQ = prove
 (`!(h:A->B) g k l a.
        galois_extension(k,l) h /\
        FINITE(group_carrier(galois_group(k,l) h)) /\
        g IN group_carrier(galois_group(k,l) h) /\
        subgroup_generated (galois_group(k,l) h) {g} = galois_group(k,l) h
        ==> (subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l <=>
             !j. group_pow (galois_group(k,l) h) g j a = a
                 ==> CARD(group_carrier(galois_group(k,l) h)) divides j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GALOIS_EXTENSION_SIMPLE_EQ] THEN
  SUBGOAL_THEN
   `!j. group_pow (galois_group(k,l) (h:A->B)) g j = I <=>
        CARD(group_carrier(galois_group(k,l) h)) divides j`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `g:B->B`]
      SUBGROUP_GENERATED_ELEMENT_ORDER) THEN
    MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `g:B->B`; `j:num`]
      GROUP_POW_EQ_ID) THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GROUP_POW];
    X_GEN_TAC `f:B->B` THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `g:B->B`]
    FINITE_CYCLIC_SUBGROUP_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `f:B->B` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (SUBST_ALL_TAC o CONJUNCT2)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let GALOIS_GROUP_INTER = prove
 (`!(h:A->B) k l s t.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\ IMAGE h (ring_carrier k) SUBSET t
        ==> group_carrier(galois_group(subfield_generated l (s INTER t),l) I) =
            group_carrier(subgroup_generated (galois_group(k,l) h)
              (group_carrier(galois_group(subfield_generated l s,l) I) UNION
               group_carrier(galois_group(subfield_generated l t,l) I)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `t:B->bool`]
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC
   `K = group_carrier(subgroup_generated (galois_group(k,l) (h:A->B))
          (group_carrier(galois_group(subfield_generated l s,l) I) UNION
           group_carrier(galois_group(subfield_generated l t,l) I)))` THEN
  SUBGOAL_THEN `fixed_field l (K:(B->B)->bool) = s INTER t` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) FIXED_FIELD_SUBGROUP_GENERATED o
      lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN ASM_MESON_TAC[subgroup_of];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[FIXED_FIELD_UNION] THEN BINOP_TAC THEN
    MATCH_MP_TAC FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `K:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED];
    ASM_SIMP_TAC[]]);;

let FIXED_FIELD_INTER = prove
 (`!(h:A->B) k l G H.
        finite_extension(k,l) h /\
        G subgroup_of galois_group(k,l) h /\ H subgroup_of galois_group(k,l) h
        ==> fixed_field l (G INTER H) =
            ring_carrier(subfield_generated l
              (fixed_field l G UNION fixed_field l H))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `G:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `H:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `galois_extension(subfield_generated l (fixed_field l G),l) (I:B->B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:B ring`; `G:(B->B)->bool`] ARTIN_FIXED_FIELD) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MP_TAC(GEN_REWRITE_RULE I [SUBGROUP_OF_GALOIS_GROUP]
     (ASSUME `G subgroup_of galois_group(k,l) (h:A->B)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k:A ring,l:B ring) h)` THEN
      ASM_SIMP_TAC[CARD_GALOIS_GROUP_LE];
      ASM_MESON_TAC[SUBSET; GALOIS_GROUP_RING_AUTOMORPHISM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`I:B->B`; `subfield_generated l (fixed_field l (G:(B->B)->bool))`;
    `l:B ring`;
    `ring_carrier(subfield_generated l
       (fixed_field l G UNION fixed_field l (H:(B->B)->bool)))`]
   FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; IMAGE_I;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `fixed_field l G UNION fixed_field l (H:(B->B)->bool)` THEN
    REWRITE_TAC[SUBSET_UNION] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET THEN
    REWRITE_TAC[UNION_SUBSET; FIXED_FIELD_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[GALOIS_GROUP_COMPOSITUM]);;

let FIXED_FIELD_CONJUGATE = prove
 (`!(l:B ring) f H.
        f permutes ring_carrier l
        ==> fixed_field l (IMAGE (\g. f o g o inverse f) H) =
            IMAGE f (fixed_field l H)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  REWRITE_TAC[EXTENSION; IN_FIXED_FIELD; IN_IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `inverse (f:B->B) x` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; PERMUTES_INVERSE]; ALL_TAC] THEN
    X_GEN_TAC `g:B->B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:B->B`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `inverse(f:B->B)`) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE]]);;

let GALOIS_GROUP_CONJUGATE = prove
 (`!(h:A->B) k l f s.
        f IN group_carrier(galois_group(k,l) h) /\ s subfield_of l
        ==> group_carrier(galois_group(subfield_generated l (IMAGE f s),l) I) =
            IMAGE (\g. f o g o inverse f)
              (group_carrier(galois_group(subfield_generated l s,l) I))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  SUBGOAL_THEN
   `inverse(f:B->B) permutes ring_carrier l /\ ring_automorphism l (inverse f)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_INVERSE; GALOIS_GROUP_PERMUTES;
                  GALOIS_GROUP_RING_AUTOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:B->B) s subfield_of l` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN EXISTS_TAC `l:B ring` THEN
    ASM_MESON_TAC[ring_automorphism; RING_ISOMORPHISM_IMP_MONOMORPHISM];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `g:B->B` THEN
  GEN_REWRITE_TAC RAND_CONV [IN_IMAGE] THEN
  ASM_SIMP_TAC[IN_GALOIS_GROUP; I_THM; CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               FORALL_IN_IMAGE] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `inverse(f:B->B) o g o f` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PERMUTES_COMPOSE];
      ASM_MESON_TAC[RING_AUTOMORPHISM_COMPOSE];
      ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g':B->B` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PERMUTES_COMPOSE];
      ASM_MESON_TAC[RING_AUTOMORPHISM_COMPOSE];
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Natural irrationalities and composita of Galois extensions. If s is       *)
(* finite and Galois over the image of k and t is any intermediate field,    *)
(* then the compositum of s and t, the subfield generated by s UNION t, is   *)
(* finite and Galois over t, and restriction to s is an isomorphism from its *)
(* Galois group over t onto the Galois group of s over s INTER t (Lang,      *)
(* Algebra, VI 1.12; for normal s restriction is still a monomorphism). So   *)
(* the degree of the compositum over t divides the degree of s over k        *)
(* (VI 1.13), and when s INTER t is the image of k restriction is an         *)
(* isomorphism onto the Galois group of s over k. The compositum of two      *)
(* finite Galois extensions s and t is finite Galois, and the pair of        *)
(* restrictions embeds its Galois group into the product of the Galois       *)
(* groups of s and t, an isomorphism when s INTER t is the image of k        *)
(* (VI 1.14).                                                                *)
(* ------------------------------------------------------------------------- *)

(* The lift of s to t is the splitting extension over t of a separable       *)
(* polynomial with splitting extension s (SPLITTING_EXTENSION_LIFT).         *)
(* Restriction is well defined since s is normal over the image of k, and    *)
(* injective since the compositum is generated over t by s. Its image has    *)
(* fixed field s INTER t, since an element of s fixed by the whole Galois    *)
(* group of the compositum over t lies in t, so by the Galois correspondence *)
(* for s it is the Galois group of s over s INTER t.                         *)

let GALOIS_EXTENSION_LIFT = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET t /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h
        ==> finite_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I /\
            galois_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`]
    GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING] THEN
  EXISTS_TAC `(h:A->B) o (p:(1->num)->A)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SPLITTING_EXTENSION_LIFT THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC POLY_SEPARABLE_MONOMORPHIC_IMAGE THEN
  EXISTS_TAC `k:A ring` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  ASM_MESON_TAC[SPLITTING_EXTENSION_IN_POLY_RING;
                FIELD_EXTENSION_IMP_HOMOMORPHISM;
                FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
                FIELD_EXTENSION_TRANS; FIELD_EXTENSION_SUBFIELD_GENERATED;
                FINITE_IMP_FIELD_EXTENSION; I_O_ID]);;

let GALOIS_COMPOSITUM_MONOMORPHISM = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\
        IMAGE h (ring_carrier k) SUBSET t /\
        normal_extension(k,subfield_generated l s) h
        ==> group_monomorphism
              (galois_group
                (subfield_generated l t,subfield_generated l (s UNION t)) I,
               galois_group
                (subfield_generated l (s INTER t),subfield_generated l s) I)
              (\f x. if x IN s then f x else x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(s:B->bool) SUBSET ring_carrier(subfield_generated l (s UNION t)) /\
    (t:B->bool) SUBSET ring_carrier(subfield_generated l (s UNION t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `field(subfield_generated l (s UNION t:B->bool))` ASSUME_TAC
  THENL [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:B->bool) subfield_of subfield_generated l (s UNION t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(subfield_generated l t,
                                        subfield_generated l (s UNION t))
                                       (I:B->B))
        ==> f IN group_carrier
                  (galois_group(k,subfield_generated l (s UNION t))
                               (h:A->B)) /\
            IMAGE f s = s`
  (LABEL_TAC "res") THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                     `subfield_generated l (t:B->bool)`;
                     `subfield_generated l (s UNION t:B->bool)`]
        GALOIS_GROUP_ANTIMONO) THEN
      ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
      ASM SET_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE THEN
      MAP_EVERY EXISTS_TAC
       [`h:A->B`; `k:A ring`; `subfield_generated l (s UNION t:B->bool)`] THEN
      ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN]];
    ALL_TAC] THEN
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM; SUBSET;
              FORALL_IN_IMAGE] THEN
  REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_THEN(fun th ->
      ASSUME_TAC th THEN USE_THEN "res" (STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`;
                   `subfield_generated l (s UNION t:B->bool)`; `s:B->bool`]
      GALOIS_GROUP_RESTRICT) THEN
    ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN; IN_GALOIS_GROUP] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; SUBFIELD_OF_INTER;
                 IN_INTER; I_THM] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`I:B->B`; `f:B->B`; `subfield_generated l (t:B->bool)`;
                   `subfield_generated l (s UNION t:B->bool)`; `x:B`]
      GALOIS_GROUP_FIXES) THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; I_THM];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC RESTRICT_COMPOSE THEN
    EXISTS_TAC `ring_carrier(subfield_generated l (s UNION t:B->bool))` THEN
    ASM_MESON_TAC[GALOIS_GROUP_PERMUTES];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `I:B->B` GALOIS_GROUP_EQ_ON_GENERATORS) THEN
    MAP_EVERY EXISTS_TAC
     [`subfield_generated l (t:B->bool)`;
      `subfield_generated l (s UNION t:B->bool)`; `s:B->bool`] THEN
    ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `t UNION s:B->bool = s UNION t` SUBST1_TAC THENL
       [SET_TAC[]; ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN; UNION_SUBSET]];
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C AP_THM `x:B` o
        check (fun th -> is_eq(concl th) && is_abs(lhs(concl th)))) THEN
      ASM_REWRITE_TAC[]]]);;

let GALOIS_COMPOSITUM = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\
        IMAGE h (ring_carrier k) SUBSET t /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h
        ==> finite_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I /\
            galois_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I /\
            group_isomorphism
              (galois_group
                (subfield_generated l t,subfield_generated l (s UNION t)) I,
               galois_group
                (subfield_generated l (s INTER t),subfield_generated l s) I)
              (\f x. if x IN s then f x else x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_EXTENSION_LIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_COMPOSITUM_MONOMORPHISM) THEN
  ASM_SIMP_TAC[GALOIS_IMP_NORMAL_EXTENSION] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  ASM_REWRITE_TAC[group_epimorphism] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
   [group_monomorphism]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `H = IMAGE (\f x. if x IN s then f x else x)
          (group_carrier(galois_group(subfield_generated l t,
                                      subfield_generated l (s UNION t))
                                     (I:B->B)))` THEN
  SUBGOAL_THEN
   `H subgroup_of galois_group(subfield_generated l (s INTER t),
                               subfield_generated l s) (I:B->B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC
     `galois_group(subfield_generated l t,subfield_generated l (s UNION t))
                  (I:B->B)` THEN
    ASM_REWRITE_TAC[CARRIER_SUBGROUP_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `finite_extension(subfield_generated l (s INTER t),subfield_generated l s)
                    (I:B->B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
                   `s INTER t:B->bool`]
      FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[SUBSET_INTER; SUBFIELD_GENERATED_IDEMPOT_GEN; INTER_SUBSET;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (s INTER t:B->bool)`;
                 `subfield_generated l (s:B->bool)`; `H:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC LAND_CONV [SYM(CONJUNCT2(CONJUNCT2 th))]) THEN
  SUBGOAL_THEN `fixed_field (subfield_generated l s) H = s INTER (t:B->bool)`
  SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN
    REWRITE_TAC[EXTENSION; IN_FIXED_FIELD; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; IN_INTER] THEN
    X_GEN_TAC `x:B` THEN ASM_CASES_TAC `(x:B) IN s` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (t:B->bool)`;
                   `subfield_generated l (s UNION t:B->bool)`]
      FIXED_FIELD_GALOIS_GROUP) THEN
    ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_FIXED_FIELD] THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier(subfield_generated l (s UNION t))`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    UNDISCH_TAC `(x:B) IN s` THEN
    MP_TAC(ISPECL [`l:B ring`; `s:B->bool`] SUBFIELD_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN; INTER_SUBSET;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD]]);;

let GALOIS_COMPOSITUM_DEGREE = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\
        IMAGE h (ring_carrier k) SUBSET t /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h
        ==> extension_degree
              (subfield_generated l t,subfield_generated l (s UNION t)) I =
            extension_degree
              (subfield_generated l (s INTER t),subfield_generated l s) I /\
            extension_degree
              (subfield_generated l t,subfield_generated l (s UNION t)) I
            divides extension_degree(k,subfield_generated l s) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_COMPOSITUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `finite_extension(k,subfield_generated l (s INTER t)) (h:A->B) /\
    finite_extension(subfield_generated l (s INTER t),subfield_generated l s)
                    (I:B->B) /\
    galois_extension(subfield_generated l (s INTER t),subfield_generated l s)
                    (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
                   `s INTER t:B->bool`]
      FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
                   `s INTER t:B->bool`]
      GALOIS_EXTENSION_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[SUBSET_INTER; SUBFIELD_GENERATED_IDEMPOT_GEN; INTER_SUBSET;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `extension_degree(k,subfield_generated l s) (h:A->B) =
    extension_degree(k,subfield_generated l (s INTER t)) h *
    extension_degree(subfield_generated l (s INTER t),subfield_generated l s)
                    (I:B->B)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (s INTER t:B->bool)`;
                   `subfield_generated l (s:B->bool)`]
      EXTENSION_DEGREE_TOWER_LAW) THEN
    ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION; I_O_ID];
    MATCH_MP_TAC(MESON[DIVIDES_LMUL; DIVIDES_REFL]
     `!a b c:num. a = b ==> a = b /\ a divides c * b`)] THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (t:B->bool)`;
                 `subfield_generated l (s UNION t:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (s INTER t:B->bool)`;
                 `subfield_generated l (s:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_CARD_EQ o
    MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC) THEN
  ASM_SIMP_TAC[CARD_EQ_CARD; FINITE_GALOIS_GROUP]);;

let GALOIS_COMPOSITUM_DISJOINT = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h /\
        s INTER t = IMAGE h (ring_carrier k)
        ==> group_isomorphism
              (galois_group
                (subfield_generated l t,subfield_generated l (s UNION t)) I,
               galois_group(k,subfield_generated l s) h)
              (\f x. if x IN s then f x else x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_COMPOSITUM) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(r <=> s) ==> p /\ q /\ r ==> s`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC GALOIS_GROUP_EQ_IMAGE THEN
  ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               SUBFIELD_OF_INTER]);;

(* The compositum of s and t is normal over the image of k                   *)
(* (NORMAL_EXTENSION_COMPOSITUM), separable by the tower through t, and      *)
(* finite by the tower law. The pair of restrictions is injective since      *)
(* s UNION t generates the compositum, and when s INTER t is the image of k  *)
(* both groups have [s:k][t:k] elements.                                     *)

let GALOIS_EXTENSION_COMPOSITUM = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h /\
        finite_extension(k,subfield_generated l t) h /\
        galois_extension(k,subfield_generated l t) h
        ==> finite_extension(k,subfield_generated l (s UNION t)) h /\
            galois_extension(k,subfield_generated l (s UNION t)) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. u subfield_of l /\ finite_extension(k,subfield_generated l u) h
        ==> IMAGE (h:A->B) (ring_carrier k) SUBSET u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_homomorphism] o
      MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
      MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_EXTENSION_LIFT) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `field_extension(k,subfield_generated l t) (h:A->B) /\
    field_extension(subfield_generated l t,subfield_generated l (s UNION t))
                   (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(CONJUNCT1(ISPEC `h:A->B` I_O_ID))) THEN
    MATCH_MP_TAC FINITE_EXTENSION_TRANS THEN
    EXISTS_TAC `subfield_generated l (t:B->bool)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[galois_extension]] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `h:A->B`; `I:B->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (s:B->bool)`;
                   `subfield_generated l (t:B->bool)`; `l:B ring`]
      NORMAL_EXTENSION_COMPOSITUM) THEN
    ASM_SIMP_TAC[GALOIS_IMP_NORMAL_EXTENSION; IMAGE_I; I_O_ID;
                 FIELD_EXTENSION_SUBFIELD_GENERATED;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (t:B->bool)`;
                   `subfield_generated l (s UNION t:B->bool)`]
      SEPARABLE_EXTENSION_TRANS_EQ) THEN
    ASM_SIMP_TAC[GALOIS_IMP_SEPARABLE_EXTENSION; I_O_ID]]);;

let GALOIS_COMPOSITUM_PROD_GROUP_MONOMORPHISM = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\
        IMAGE h (ring_carrier k) SUBSET t /\
        normal_extension(k,subfield_generated l s) h /\
        normal_extension(k,subfield_generated l t) h
        ==> group_monomorphism
              (galois_group(k,subfield_generated l (s UNION t)) h,
               prod_group (galois_group(k,subfield_generated l s) h)
                          (galois_group(k,subfield_generated l t) h))
              (\f. (\x. if x IN s then f x else x),
                   (\x. if x IN t then f x else x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(s:B->bool) SUBSET ring_carrier(subfield_generated l (s UNION t)) /\
    (t:B->bool) SUBSET ring_carrier(subfield_generated l (s UNION t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `field(subfield_generated l (s UNION t:B->bool))` ASSUME_TAC
  THENL [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED]; ALL_TAC] THEN
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM_PAIRED] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`;
                   `subfield_generated l (s UNION t:B->bool)`; `s:B->bool`]
      GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
    ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN; SUBFIELD_OF_SUBFIELD_GENERATED;
                 SUBSET_UNION];
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`;
                   `subfield_generated l (s UNION t:B->bool)`; `t:B->bool`]
      GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
    ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN; SUBFIELD_OF_SUBFIELD_GENERATED;
                 SUBSET_UNION];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC
     [`h:A->B`; `k:A ring`; `subfield_generated l (s UNION t:B->bool)`;
      `s UNION t:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `IMAGE (h:A->B) (ring_carrier k) UNION s UNION t = s UNION t`
      SUBST1_TAC THENL
       [ASM SET_TAC[];
        ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN; UNION_SUBSET]];
      X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o C AP_THM `x:B` o
          check (fun th -> is_eq(concl th) &&
                           free_in `s:B->bool` (concl th)));
        FIRST_X_ASSUM(MP_TAC o C AP_THM `x:B` o
          check (fun th -> is_eq(concl th) &&
                           free_in `t:B->bool` (concl th)))] THEN
      ASM_REWRITE_TAC[]]]);;

let GALOIS_COMPOSITUM_PROD_GROUP = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h /\
        finite_extension(k,subfield_generated l t) h /\
        galois_extension(k,subfield_generated l t) h /\
        s INTER t = IMAGE h (ring_carrier k)
        ==> group_isomorphism
              (galois_group(k,subfield_generated l (s UNION t)) h,
               prod_group (galois_group(k,subfield_generated l s) h)
                          (galois_group(k,subfield_generated l t) h))
              (\f. (\x. if x IN s then f x else x),
                   (\x. if x IN t then f x else x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) (ring_carrier k) SUBSET s /\
    IMAGE (h:A->B) (ring_carrier k) SUBSET t`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_EXTENSION_COMPOSITUM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_COMPOSITUM_DEGREE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_EXTENSION_LIFT) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_COMPOSITUM_PROD_GROUP_MONOMORPHISM) THEN
  ASM_SIMP_TAC[GALOIS_IMP_NORMAL_EXTENSION] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE o snd) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[FINITE_GALOIS_GROUP; CONJUNCT1 PROD_GROUP; FINITE_CROSS;
               CARD_CROSS] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (t:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`;
                 `subfield_generated l (s UNION t:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (t:B->bool)`;
                 `subfield_generated l (s UNION t:B->bool)`]
    EXTENSION_DEGREE_TOWER_LAW) THEN
  ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION; I_O_ID] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`I:B->B`; `h:A->B`; `subfield_generated l (s INTER t:B->bool)`;
                 `k:A ring`; `subfield_generated l (s:B->bool)`]
    EXTENSION_DEGREE_EQ_IMAGE) THEN
  ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               SUBFIELD_OF_INTER] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Finite Galois subextensions. finite_galois_subfields (k,l) h is the set   *)
(* of subfields e of l containing the image of k with e finite and Galois    *)
(* over k. For a Galois extension each x in l lies in one                    *)
(* (FINITE_GALOIS_SUBFIELDS_ELEMENT: the field generated by the roots of the *)
(* minimal polynomial of x, which splits in l by normality and is separable, *)
(* by GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING), any two lie in a third       *)
(* (FINITE_GALOIS_SUBFIELDS_UPPER_BOUND, the compositum, by                  *)
(* GALOIS_EXTENSION_COMPOSITUM), so do finitely many                         *)
(* (FINITE_GALOIS_SUBFIELDS_UPPER_BOUNDS), and every finite subset of l lies *)
(* in one (FINITE_GALOIS_SUBFIELDS_FINITE). Two elements of the Galois group *)
(* have the same restriction to e iff they agree on a finite set             *)
(* (FINITE_GALOIS_SUBFIELD_RESTRICTION_EQ, through                           *)
(* GALOIS_GROUP_EQ_ON_GENERATORS; a field extension is enough). This is the  *)
(* directed system of infinite Galois theory.                                *)
(* ------------------------------------------------------------------------- *)

let finite_galois_subfields = new_definition
 `finite_galois_subfields (k:A ring,l:B ring) (h:A->B) =
        {e | e subfield_of l /\ IMAGE h (ring_carrier k) SUBSET e /\
             finite_extension(k,subfield_generated l e) h /\
             galois_extension(k,subfield_generated l e) h}`;;

let IN_FINITE_GALOIS_SUBFIELDS = prove
 (`!(h:A->B) k l e.
        e IN finite_galois_subfields(k,l) h <=>
        e subfield_of l /\ IMAGE h (ring_carrier k) SUBSET e /\
        finite_extension(k,subfield_generated l e) h /\
        galois_extension(k,subfield_generated l e) h`,
  REWRITE_TAC[finite_galois_subfields; IN_ELIM_THM]);;

let FINITE_GALOIS_SUBFIELDS_ELEMENT = prove
 (`!(h:A->B) k l x.
        galois_extension(k,l) h /\ x IN ring_carrier l
        ==> ?e. e IN finite_galois_subfields(k,l) h /\ x IN e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_FINITE_GALOIS_SUBFIELDS] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_NORMAL_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_SEPARABLE_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
                MINIMAL_POLYNOMIAL) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[GALOIS_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `poly_eval l ((h:A->B) o minimal_polynomial(k,l) h x) x = ring_0 l`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(x:B) IN {f x | f IN group_carrier(galois_group(k,l) (h:A->B))}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `I:B->B` THEN
      REWRITE_TAC[GALOIS_GROUP_I; I_THM];
      ASM_SIMP_TAC[GALOIS_GROUP_ORBIT] THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_splits_over (k,l) (h:A->B) (minimal_polynomial(k,l) h x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `normal_extension(k,l) (h:A->B)` THEN
    REWRITE_TAC[normal_extension] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `t = IMAGE (h:A->B) (ring_carrier k) UNION
        {y | y IN ring_carrier l /\
             poly_eval l (h o minimal_polynomial(k,l) h x) y = ring_0 l}` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `minimal_polynomial(k,l) (h:A->B) x`]
                SPLITTING_EXTENSION_GENERATED_BY_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `finite_extension(k,subfield_generated l t) (h:A->B) /\
    galois_extension(k,subfield_generated l t) h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING] THEN
    EXISTS_TAC `minimal_polynomial(k,l) (h:A->B) x` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `separable_extension(k,l) (h:A->B)` THEN
    REWRITE_TAC[separable_extension; separable_element] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:B->bool) SUBSET ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ring_monomorphism(k:A ring,l:B ring) h` THEN
      SIMP_TAC[ring_monomorphism; ring_homomorphism];
      SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `ring_carrier(subfield_generated l (t:B->bool))` THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
               SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[]]);;

let FINITE_GALOIS_SUBFIELDS_UPPER_BOUND = prove
 (`!(h:A->B) k l e1 e2.
        field l /\
        e1 IN finite_galois_subfields(k,l) h /\
        e2 IN finite_galois_subfields(k,l) h
        ==> ?e. e IN finite_galois_subfields(k,l) h /\
                e1 SUBSET e /\ e2 SUBSET e`,
  REWRITE_TAC[IN_FINITE_GALOIS_SUBFIELDS] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `e1:B->bool`; `e2:B->bool`]
                GALOIS_EXTENSION_COMPOSITUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_carrier(subfield_generated l (e1 UNION e2:B->bool))` THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
               SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  SUBGOAL_THEN
   `(e1 UNION e2:B->bool) SUBSET
    ring_carrier(subfield_generated l (e1 UNION e2))`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
    ASM_SIMP_TAC[UNION_SUBSET; SUBFIELD_OF_IMP_SUBSET];
    ASM SET_TAC[]]);;

let FINITE_GALOIS_SUBFIELDS_UPPER_BOUNDS = prove
 (`!(h:A->B) k l c.
        field l /\ FINITE c /\ ~(c = {}) /\
        c SUBSET finite_galois_subfields(k,l) h
        ==> ?e. e IN finite_galois_subfields(k,l) h /\
                !e'. e' IN c ==> e' SUBSET e`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; INSERT_SUBSET; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`e1:B->bool`; `c:(B->bool)->bool`] THEN
  ASM_CASES_TAC `c:(B->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:B->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `e1:B->bool`; `e2:B->bool`]
                FINITE_GALOIS_SUBFIELDS_UPPER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let FINITE_GALOIS_SUBFIELDS_FINITE = prove
 (`!(h:A->B) k l s.
        galois_extension(k,l) h /\ FINITE s /\ s SUBSET ring_carrier l
        ==> ?e. e IN finite_galois_subfields(k,l) h /\ s SUBSET e`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_1 l:B`]
                  FINITE_GALOIS_SUBFIELDS_ELEMENT) THEN
    ASM_REWRITE_TAC[RING_1; EMPTY_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `s:B->bool`] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:B->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
                FINITE_GALOIS_SUBFIELDS_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:B->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `e1:B->bool`; `e2:B->bool`]
                FINITE_GALOIS_SUBFIELDS_UPPER_BOUND) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[GALOIS_IMP_FIELD_EXTENSION; field_extension];
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]]);;

let FINITE_GALOIS_SUBFIELD_RESTRICTION_EQ = prove
 (`!(h:A->B) k l e.
        field_extension(k,l) h /\ e IN finite_galois_subfields(k,l) h
        ==> ?b. FINITE b /\ b SUBSET e /\
                !f g. f IN group_carrier(galois_group(k,l) h) /\
                      g IN group_carrier(galois_group(k,l) h)
                      ==> ((\x. if x IN e then f x else x) =
                           (\x. if x IN e then g x else x) <=>
                           !x. x IN b ==> f x = g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_FINITE_GALOIS_SUBFIELDS]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_FINITELY_GENERATED_EXTENSION) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o last o CONJUNCTS)
  THEN EXISTS_TAC `b:B->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `e:B->bool`]
                GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[GALOIS_IMP_NORMAL_EXTENSION] THEN
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT1) THEN
  MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(fun th -> X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      MP_TAC(AP_THM th `x:B`)) THEN
    SUBGOAL_THEN `(x:B) IN e` (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `\x. if x IN e then (f:B->B) x else x`;
                 `\x. if x IN e then (g:B->B) x else x`; `k:A ring`;
                 `subfield_generated l (e:B->bool)`; `b:B->bool`]
                GALOIS_GROUP_EQ_ON_GENERATORS) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN e` (fun th -> REWRITE_TAC[th]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Galois group of a polynomial. For a normal extension the Galois group *)
(* acts transitively on the roots in l of an irreducible polynomial. For a   *)
(* splitting extension of p it acts faithfully on the roots of p, so it      *)
(* embeds in their symmetric group. If p is irreducible, the number of roots *)
(* is a prime and some element moves exactly two roots, then the image is a  *)
(* transitive subgroup containing a transposition, hence the whole symmetric *)
(* group.                                                                    *)
(* ------------------------------------------------------------------------- *)

let GALOIS_GROUP_TRANSITIVE_ON_ROOTS = prove
 (`!(h:A->B) k l p a b.
     normal_extension(k,l) h /\ ring_irreducible(poly_ring k (:1)) p /\
     a IN ring_carrier l /\ poly_eval l (h o p) a = ring_0 l /\
     b IN ring_carrier l /\ poly_eval l (h o p) b = ring_0 l
     ==> ?f. f IN group_carrier(galois_group(k,l) h) /\ f a = b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    GALOIS_GROUP_ORBIT) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`; `a:B`]
    MINIMAL_POLYNOMIAL_ROOTS_IRREDUCIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `b:B`) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let GALOIS_GROUP_IMAGE_ROOTS = prove
 (`!(h:A->B) f k l p.
        ring_homomorphism(k,l) h /\ f IN group_carrier(galois_group(k,l) h) /\
        p IN ring_carrier(poly_ring k (:1))
        ==> IMAGE f {x | x IN ring_carrier l /\
                         poly_eval l (h o p) x = ring_0 l} =
            {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier(galois_group(k,l) (h:A->B))
        ==> IMAGE g {x | x IN ring_carrier l /\
                         poly_eval l (h o p) x = ring_0 l} SUBSET
            {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:B->B` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`;
                   `p:(1->num)->A`; `x:B`] GALOIS_GROUP_POLY_EVAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE;
                  RING_HOMOMORPHISM_0; GALOIS_GROUP_RING_HOMOMORPHISM];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inverse(f:B->B)`) THEN
  ASM_SIMP_TAC[GALOIS_GROUP_INVERSE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
  ASM_MESON_TAC[PERMUTES_INVERSES]);;

let GALOIS_GROUP_ACTION_ON_ROOTS = prove
 (`!(h:A->B) k l p.
     splitting_extension(k,l) h p
     ==> group_monomorphism
          (galois_group(k,l) h,
           symmetric_group
            {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l})
          (\f x. if x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l
                 then f x else x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> IMAGE f {x | x IN ring_carrier l /\
                         poly_eval l (h o p) x = ring_0 l} =
            {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_IMAGE_ROOTS THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `l:B ring`)) THEN
  SUBGOAL_THEN
   `(\f x. if x IN ring_carrier l /\ poly_eval l ((h:A->B) o p) x = ring_0 l
           then (f:B->B) x else x) =
    (\f x. if x IN {x | x IN ring_carrier l /\
                        poly_eval l (h o p) x = ring_0 l}
           then f x else x)`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o p) x = ring_0 l}` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(R:B->bool) SUBSET ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM; SYMMETRIC_GROUP;
              CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RESTRICT_PERMUTES_EQ] THEN
    ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_INJECTIVE];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC RESTRICT_COMPOSE THEN
    EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_MESON_TAC[GALOIS_GROUP_PERMUTES];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `R:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `x:B`) THEN ASM_REWRITE_TAC[]]);;

let GALOIS_GROUP_ACTION_ON_ROOTS_TRANSITIVE = prove
 (`!(h:A->B) k l p.
     splitting_extension(k,l) h p /\ ring_irreducible(poly_ring k (:1)) p
     ==> !a b. a IN ring_carrier l /\ poly_eval l (h o p) a = ring_0 l /\
               b IN ring_carrier l /\ poly_eval l (h o p) b = ring_0 l
               ==> ?g. g IN group_image
                             (galois_group(k,l) h,
                              symmetric_group
                               {x | x IN ring_carrier l /\
                                    poly_eval l (h o p) x = ring_0 l})
                             (\f x. if x IN ring_carrier l /\
                                       poly_eval l (h o p) x = ring_0 l
                                    then f x else x) /\
                       g a = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IMP_NORMAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                 `a:B`; `b:B`] GALOIS_GROUP_TRANSITIVE_ON_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:B->B` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[group_image; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[]);;

let GALOIS_GROUP_CARD_ROOTS_DIVIDES = prove
 (`!(h:A->B) k l p.
     splitting_extension(k,l) h p /\ ring_irreducible(poly_ring k (:1)) p
     ==> CARD {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
         divides CARD(group_carrier(galois_group(k,l) h))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_IMP_FINITE_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IMP_NORMAL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
    POLY_SPLITS_HAS_ROOT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[poly_splits_over]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IRREDUCIBLE_IMP_POLY_DEG_NZ THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC)] THEN
  ASSUME_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    (CONJUNCT1 GALOIS_GROUP_ACTION)) THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `ring_carrier l:B->bool`;
                 `\(f:B->B) (x:B). f x`; `a:B`] ORBIT_STABILIZER_MUL) THEN
  ASM_SIMP_TAC[CARD_GALOIS_GROUP_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DIVIDES_RMUL THEN
  MATCH_MP_TAC(MESON[DIVIDES_REFL]
   `(s:B->bool) = t ==> CARD s divides CARD t`) THEN
  REWRITE_TAC[EXTENSION; IN_GROUP_ORBIT; IN_ELIM_THM] THEN
  X_GEN_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                   `a:B`; `y:B`] GALOIS_GROUP_TRANSITIVE_ON_ROOTS) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`;
                   `p:(1->num)->A`; `a:B`] GALOIS_GROUP_POLY_EVAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_0; GALOIS_GROUP_RING_HOMOMORPHISM]]);;

let GALOIS_GROUP_PRIME_TRANSPOSITION_EXPLICIT = prove
 (`!(h:A->B) f k l p.
     splitting_extension(k,l) h p /\ ring_irreducible(poly_ring k (:1)) p /\
     prime(CARD {x | x IN ring_carrier l /\
                     poly_eval l (h o p) x = ring_0 l}) /\
     f IN group_carrier(galois_group(k,l) h) /\
     {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l /\
          ~(f x = x)} HAS_SIZE 2
     ==> group_isomorphism
          (galois_group(k,l) h,
           symmetric_group
            {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l})
          (\g x. if x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l
                 then g x else x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_ROOT_BOUND_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_ACTION_ON_ROOTS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_ACTION_ON_ROOTS_TRANSITIVE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_binary "HAS_SIZE" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_comb(concl th) && rator(concl th) = `prime`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  SUBGOAL_THEN
   `!P. {x | x IN ring_carrier l /\ poly_eval l ((h:A->B) o p) x = ring_0 l /\
             P x} =
        {x | x IN {x | x IN ring_carrier l /\
                       poly_eval l ((h:A->B) o p) x = ring_0 l} /\ P x}`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN ring_carrier l /\ poly_eval l ((h:A->B) o p) a = ring_0 l /\
          b IN ring_carrier l /\ poly_eval l (h o p) b = ring_0 l <=>
          a IN {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l} /\
          b IN {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\f x. if x IN ring_carrier l /\ poly_eval l ((h:A->B) o p) x = ring_0 l
           then (f:B->B) x else x) =
    (\f x. if x IN {x | x IN ring_carrier l /\
                        poly_eval l (h o p) x = ring_0 l}
           then f x else x)`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o p) x = ring_0 l}` THEN
  ABBREV_TAC `rho = \g x. if x IN R then (g:B->B) x else x` THEN
  DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(a:B) IN R /\ ~(f a = a) /\ (b:B) IN R /\ ~(f b = b) /\
    !x. x IN R /\ ~(x = a) /\ ~(x = b) ==> f x = x`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `a:B` th) THEN MP_TAC(SPEC `b:B` th) THEN MP_TAC th) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC TRANSITIVE_TRANSPOSITION_SYMMETRIC_ISOMORPHISM THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(rho:(B->B)->B->B) f permutes R` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
     [group_homomorphism] o CONJUNCT1 o GEN_REWRITE_RULE I
     [group_monomorphism]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SYMMETRIC_GROUP; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho:(B->B)->B->B) f = swap(a,b)` (SUBST1_TAC o SYM) THENL
   [MP_TAC(ISPECL [`(rho:(B->B)->B->B) f`; `a:B`; `b:B`]
      PERMUTES_DOUBLETON) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q \/ r) ==> r`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_SUPERSET THEN EXISTS_TAC `R:B->bool` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      EXPAND_TAC "rho" THEN ASM_SIMP_TAC[];
      EXPAND_TAC "rho" THEN REWRITE_TAC[FUN_EQ_THM; I_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `a:B`) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[group_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[]]);;

let GALOIS_GROUP_PRIME_TRANSPOSITION = prove
 (`!(h:A->B) f k l p.
     splitting_extension(k,l) h p /\ ring_irreducible(poly_ring k (:1)) p /\
     prime(CARD {x | x IN ring_carrier l /\
                     poly_eval l (h o p) x = ring_0 l}) /\
     f IN group_carrier(galois_group(k,l) h) /\
     {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l /\
          ~(f x = x)} HAS_SIZE 2
     ==> galois_group(k,l) h isomorphic_group
         symmetric_group
           {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}`,
  REWRITE_TAC[isomorphic_group] THEN
  MESON_TAC[GALOIS_GROUP_PRIME_TRANSPOSITION_EXPLICIT]);;

(* ------------------------------------------------------------------------- *)
(* Discriminants and the alternating group. Let p be a separable polynomial  *)
(* of degree n with leading coefficient c, and number the roots of h o p in  *)
(* a splitting extension l as x_0, ..., x_(n-1). Then                        *)
(* d = h(c)^(n-1) det(x_i^j), that is h(c)^(n-1) times the product of the    *)
(* x_j - x_i for i < j, is a nonzero square root of h(disc p), and each      *)
(* element f of the Galois group maps d to its product with the sign of the  *)
(* permutation of the roots induced by f. So if 2 is not 0 in k, the Galois  *)
(* group acts on the roots by even permutations if and only if the           *)
(* discriminant of p is a square in k. The Galois group of an irreducible    *)
(* separable cubic has order 3 if its discriminant is a square in k, and     *)
(* order 6 if not.                                                           *)
(* ------------------------------------------------------------------------- *)

(* An element f of the Galois group permutes the rows of a determinant with  *)
(* entries u^e(v), indexed by the roots u, v of p, for any exponents e: it   *)
(* multiplies the determinant by the sign of the permutation of the roots    *)
(* that f induces.                                                           *)

let GALOIS_GROUP_VANDERMONDE_ROOTS = prove
 (`!(h:A->B) f k l p (e:B->num).
        ring_homomorphism(k,l) h /\ f IN group_carrier(galois_group(k,l) h) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        FINITE {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
        ==> f(ring_det l
               {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
               (\u v. ring_pow l u (e v))) =
            ring_mul l
             (ring_sign l
               (\x. if x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l
                    then f x else x))
             (ring_det l
               {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
               (\u v. ring_pow l u (e v)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\x. if x IN ring_carrier l /\ poly_eval l ((h:A->B) o p) x = ring_0 l
         then (f:B->B) x else x) =
    (\x. if x IN {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
         then f x else x)`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o (p:(1->num)->A)) x = ring_0 l}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(R:B->bool) SUBSET ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_IMAGE_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`; `R:B->bool`;
                 `\u v. ring_pow (l:B ring) u ((e:B->num) v)`]
    RING_DET_HOMOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_POW THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `R:B->bool`;
                 `\u v. ring_pow (l:B ring) u ((e:B->num) v)`;
                 `\x. if x IN R then (f:B->B) x else x`]
    RING_DET_PERMUTE_ROWS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RESTRICT_PERMUTES_EQ] THEN
    ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_INJECTIVE];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_DET_EQ THEN
  MAP_EVERY X_GEN_TAC [`u:B`; `v:B`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP RING_HOMOMORPHISM_POW) THEN
  ASM SET_TAC[]);;

(* The square root of the discriminant: with an enumeration z of the roots   *)
(* and its inverse e, det(z_i^j) is the determinant above, nonzero since the *)
(* roots are distinct (POLY_DISCRIMINANT_VANDERMONDE).                       *)

let GALOIS_GROUP_DISCRIMINANT_SQUARE_ROOT = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p /\ poly_separable k p
        ==> ?d. d IN ring_carrier l /\ ~(d = ring_0 l) /\
                ring_pow l d 2 = h(poly_discriminant k p) /\
                !f. f IN group_carrier(galois_group(k,l) h)
                    ==> f d =
                        ring_mul l
                         (ring_sign l
                           (\x. if x IN ring_carrier l /\
                                   poly_eval l (h o p) x = ring_0 l
                                then f x else x))
                         d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `integral_domain(l:B ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) o (p:(1->num)->A) IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = poly_deg k (p:(1->num)->A)` THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o (p:(1->num)->A)) x = ring_0 l}` THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
    POLY_DEG_MONOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_ROOT_BOUND_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(R:B->bool) SUBSET ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?(z:num->B) (e:B->num).
        IMAGE z {i | i < n} = R /\ !i. i IN {i | i < n} ==> e(z i) = i`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:B->bool`; `n:num`] HAS_SIZE_INDEX) THEN
    ASM_REWRITE_TAC[HAS_SIZE; EXISTS_UNIQUE_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:num->B` THEN STRIP_TAC THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM INJECTIVE_ON_LEFT_INVERSE] THEN
    REWRITE_TAC[IN_ELIM_THM; EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> (z:num->B) i IN ring_carrier l` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `a = (h:A->B)(coeff n (p:(1->num)->A))` THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier l /\ ~(a = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SUBGOAL_THEN `coeff n (p:(1->num)->A) IN ring_carrier k /\
                  ~(coeff n p = ring_0 k)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_THEN `poly_deg k (p:(1->num)->A) = n` (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT] THEN
      MATCH_MP_TAC POLY_TOP_NONZERO THEN
      ASM_REWRITE_TAC[CONJUNCT2 POLY_RING_CLAUSES];
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`;
                     `coeff n (p:(1->num)->A)`] RING_MONOMORPHISM_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`; `a:B`; `z:num->B`]
    POLY_DISCRIMINANT_VANDERMONDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
      POLY_ROOT_COUNT_IMP_PRODUCT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `coeff n ((h:A->B) o (p:(1->num)->A)) = a` SUBST1_TAC THENL
     [EXPAND_TAC "a" THEN REWRITE_TAC[coeff; o_THM]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJUNCT2 POLY_RING_CLAUSES] THEN
    AP_TERM_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      aconv (concl th) `IMAGE (z:num->B) {i | i < n} = R`)) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
      EXISTS_TAC `e:B->num` THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ABBREV_TAC
   `V = ring_det l {i | i < n} (\i j. ring_pow l ((z:num->B) i) j)` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_DISCRIMINANT_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(V:B = ring_0 l)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> rand(concl th) = `V:B`)) THEN
    ASM_SIMP_TAC[RING_DET_VANDERMONDE; INTEGRAL_DOMAIN_PRODUCT_EQ_0;
                 FINITE_NUMSEG_LT; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`; NOT_EXISTS_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_SUB_EQ_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `e:B->num`) THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[RING_DET]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_det l R (\u v. ring_pow l u ((e:B->num) v)) = V`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      aconv (concl th) `IMAGE (z:num->B) {i | i < n} = R`)) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_REINDEX o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG_LT; INJECTIVE_ON_LEFT_INVERSE] THEN
      EXISTS_TAC `e:B->num` THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ring_mul l (ring_pow l a (n - 1)) V:B` THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW; INTEGRAL_DOMAIN_MUL_EQ_0;
               INTEGRAL_DOMAIN_POW_EQ_0] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`;
                 `p:(1->num)->A`; `e:B->num`]
    GALOIS_GROUP_VANDERMONDE_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->B) a = a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC GALOIS_GROUP_FIXES THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `l:B ring`] THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`] RING_HOMOMORPHISM_MUL) THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`] RING_HOMOMORPHISM_POW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[RING_POW] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul (r:B ring) x (ring_mul r s v) =
    ring_mul r s (ring_mul r x v)`) THEN
  ASM_SIMP_TAC[RING_SIGN; RING_POW]);;

(* If 2 is not 0 then d is not -d, so d is fixed by f exactly when f acts on *)
(* the roots by an even permutation; and d lies in the image of k, the fixed *)
(* field of the Galois group, exactly when disc p is a square in k.          *)

let GALOIS_GROUP_EVEN_EQ_DISCRIMINANT_SQUARE = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p /\ poly_separable k p /\
        ~(ring_of_num k 2 = ring_0 k)
        ==> ((!f. f IN group_carrier(galois_group(k,l) h)
                  ==> evenperm
                       (\x. if x IN ring_carrier l /\
                               poly_eval l (h o p) x = ring_0 l
                            then f x else x)) <=>
             ?d. d IN ring_carrier k /\
                 ring_pow k d 2 = poly_discriminant k p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_DISCRIMINANT_SQUARE_ROOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:B` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `integral_domain(l:B ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
  SUBGOAL_THEN `galois_extension(k,l) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `(d:B) IN IMAGE (h:A->B) (ring_carrier k)` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      REWRITE_TAC[GSYM(MATCH_MP FIXED_FIELD_GALOIS_GROUP th)]) THEN
    ASM_REWRITE_TAC[IN_FIXED_FIELD] THEN
    MATCH_MP_TAC(MESON[]
     `(!f:B->B. P f ==> (Q f <=> R f))
      ==> ((!f. P f ==> Q f) <=> (!f. P f ==> R f))`) THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o C MATCH_MP
     (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
    REWRITE_TAC[ring_sign] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LNEG; RING_1] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_mul l (ring_of_num l 2) (d:B) = ring_0 l` MP_TAC THENL
     [UNDISCH_TAC `ring_neg l d = (d:B)` THEN
      ASM_SIMP_TAC[GSYM RING_ADD_EQ_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[RING_RULE
       `ring_mul (r:B ring) (ring_of_num r 2) x = ring_add r x x`];
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_OF_NUM] THEN
      FIRST_ASSUM(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)]) THEN
      ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_OF_NUM]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism]) THEN
    ASM_SIMP_TAC[RING_POW; POLY_DISCRIMINANT_IN_CARRIER] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    UNDISCH_THEN `(d:B) = h(e:A)` (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:A->B) e IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `d:B`; `(h:A->B) e`]
      INTEGRAL_DOMAIN_SQUARE_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `ring_pow k (e:A) 2 = poly_discriminant k p`
     (SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    STRIP_TAC THENL
     [EXISTS_TAC `e:A` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `ring_neg k e:A` THEN
      ASM_SIMP_TAC[RING_NEG] THEN ASM_MESON_TAC[RING_HOMOMORPHISM_NEG]]]);;

(* For an irreducible separable cubic the order of the Galois group is a     *)
(* multiple of 3 (it acts transitively on the 3 roots) and divides 3! = 6.   *)
(* In the group of order 3 every element has order dividing 3, hence acts    *)
(* evenly; the group of order 6 maps onto all permutations of the roots, so  *)
(* it contains a transposition.                                              *)

let GALOIS_GROUP_CUBIC = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p /\ ring_irreducible(poly_ring k (:1)) p /\
        poly_separable k p /\ poly_deg k p = 3 /\
        ~(ring_of_num k 2 = ring_0 k)
        ==> (CARD(group_carrier(galois_group(k,l) h)) = 3 <=>
             ?d. d IN ring_carrier k /\
                 ring_pow k d 2 = poly_discriminant k p) /\
            (CARD(group_carrier(galois_group(k,l) h)) = 6 <=>
             ~(?d. d IN ring_carrier k /\
                   ring_pow k d 2 = poly_discriminant k p))`,
  let lemma = prove
   (`!c. c divides FACT 3 /\ 3 divides c ==> c = 3 \/ c = 6`,
    REWRITE_TAC[FACT; num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    GEN_TAC THEN ASM_CASES_TAC `c < 7` THENL
     [POP_ASSUM MP_TAC THEN SPEC_TAC(`c:num`,`c:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE o CONJUNCT1) THEN
      ASM_ARITH_TAC]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_EVEN_EQ_DISCRIMINANT_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  SUBGOAL_THEN `finite_extension(k,l) (h:A->B) /\ galois_extension(k,l) h`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] FINITE_GALOIS_GROUP) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_ACTION_ON_ROOTS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    GALOIS_GROUP_CARD_ROOTS_DIVIDES) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_ROOT_BOUND_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!f:B->B. (\x. if x IN ring_carrier l /\
                     poly_eval l ((h:A->B) o p) x = ring_0 l
                  then f x else x) =
             (\x. if x IN {x | x IN ring_carrier l /\
                               poly_eval l (h o p) x = ring_0 l}
                  then f x else x)`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o (p:(1->num)->A)) x = ring_0 l}` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
   [group_monomorphism]) THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> (\x. if x IN R then f x else x) permutes R`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
     [group_homomorphism]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SYMMETRIC_GROUP; IN_ELIM_THM] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(group_carrier(galois_group(k,l) (h:A->B))) = 3 \/
    CARD(group_carrier(galois_group(k,l) h)) = 6`
  MP_TAC THENL
   [MATCH_MP_TAC lemma THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      GALOIS_EXTENSION_EQ_CARD) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
      SPLITTING_EXTENSION_DEGREE_DIVIDES_FACT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC
     `CARD(R:B->bool) divides
      CARD(group_carrier(galois_group(k,l) (h:A->B)))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th ->
    ASSUME_TAC th THEN REWRITE_TAC[th])) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `f:B->B`]
      GROUP_POW_GROUP_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `symmetric_group(R:B->bool)`;
                   `\f x. if x IN R then (f:B->B) x else x`]
      GROUP_HOMOMORPHISM_POW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`f:B->B`; `3`]) THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP); I_THM; COND_ID] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\x. if x IN R then (f:B->B) x else x`; `R:B->bool`; `3`]
      EVENPERM_GROUP_POW) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PERMUTATION_PERMUTES] THEN EXISTS_TAC `R:B->bool` THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EVENPERM_ID; ARITH]];
    SUBGOAL_THEN `?a b:B. a IN R /\ b IN R /\ ~(a = b)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(HAS_SIZE_CONV `(R:B->bool) HAS_SIZE 3`) THEN
      ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:B`; `a':B`] THEN ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\f x. if x IN R then (f:B->B) x else x)
            (group_carrier(galois_group(k,l) (h:A->B))) =
      group_carrier(symmetric_group R)`
    MP_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET_EQ THEN
      ASM_SIMP_TAC[FINITE_SYMMETRIC_GROUP; CARD_SYMMETRIC_GROUP] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o
          GEN_REWRITE_RULE I [group_homomorphism]);
        W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o
              GEN_REWRITE_RULE I [group_monomorphism]);
            FIRST_ASSUM ACCEPT_TAC];
          DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[FACT; num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
        CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; SYMMETRIC_GROUP; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `swap(a:B,b)`) THEN
    ASM_SIMP_TAC[PERMUTES_SWAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:B->B` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `f:B->B` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[EVENPERM_SWAP]]);;

(* ------------------------------------------------------------------------- *)
(* Galois groups of finite fields. A finite field l is a finite Galois       *)
(* extension of each subfield k, being the splitting extension of the        *)
(* separable polynomial X^|l| - X. The Frobenius map x |-> x^q, q the number *)
(* of elements of k (the identity outside the carrier of l), is in the       *)
(* Galois group, and its order is [l:k], since its d-th power, the map       *)
(* x |-> x^(q^d), fixes at most q^d elements. Hence the Galois group is      *)
(* cyclic of order [l:k], generated by the Frobenius map. For each divisor d *)
(* of [l:k] the fixed field of the d-th power of the Frobenius map, the set  *)
(* of solutions of x^(q^d) = x, is an intermediate field of degree d, and it *)
(* is the only one of that degree; there are none of other degrees.          *)
(* ------------------------------------------------------------------------- *)

let FINITE_FIELD_GALOIS_EXTENSION = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> finite_extension(k,l) h /\ galois_extension(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    FINITE_FIELD_SPLITTING_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Powers in the Galois group are compositions, so the powers of a power map *)
(* are power maps; no hypotheses are needed.                                 *)
let GALOIS_GROUP_POW_RING_POW = prove
 (`!(h:A->B) k l n j.
        group_pow (galois_group(k,l) h)
                  (\x. if x IN ring_carrier l then ring_pow l x n else x) j =
        (\x. if x IN ring_carrier l then ring_pow l x (n EXP j) else x)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`j:num`,`j:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[group_pow; GALOIS_GROUP] THEN
  REWRITE_TAC[FUN_EQ_THM; I_THM; o_THM; EXP] THEN X_GEN_TAC `x:B` THEN
  ASM_CASES_TAC `(x:B) IN ring_carrier l` THEN
  ASM_SIMP_TAC[RING_POW_1; RING_POW; RING_POW_POW; MULT_SYM]);;

(* If the d-th power of the Frobenius map is the identity, all |k|^[l:k]     *)
(* elements of l satisfy x^(q^d) = x, so [l:k] <= d                          *)
(* (RING_POW_FIXPOINTS_BOUND).                                               *)
let GALOIS_GROUP_FROBENIUS = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> (\x. if x IN ring_carrier l
                 then ring_pow l x (CARD(ring_carrier k)) else x)
            IN group_carrier(galois_group(k,l) h) /\
            group_element_order (galois_group(k,l) h)
             (\x. if x IN ring_carrier l
                  then ring_pow l x (CARD(ring_carrier k)) else x) =
            extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `FINITE(ring_carrier(k:A ring))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_RING_MONOMORPHIC_PREIMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `finite_extension(k,l) (h:A->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_EQ_FIELD_EXTENSION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] CARD_GALOIS_GROUP_LE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] CARD_EXTENSION_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `q = CARD(ring_carrier(k:A ring))` THEN
  ABBREV_TAC `n = extension_degree(k,l) (h:A->B)` THEN
  ABBREV_TAC `f = \x. if x IN ring_carrier l then ring_pow l x q else x:B` THEN
  SUBGOAL_THEN `2 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[FINITE_FIELD_CARD_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `f IN group_carrier(galois_group(k,l) (h:A->B))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `1`]
      RING_ENDOMORPHISM_POW_CARD) THEN
    ASM_REWRITE_TAC[EXP_1] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_automorphism l (\x:B. ring_pow l x q)` MP_TAC THENL
     [REWRITE_TAC[ring_automorphism] THEN
      ASM_SIMP_TAC[RING_ISOMORPHISM_EQ_MONOMORPHISM_FINITE] THEN
      MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; GSYM ring_endomorphism];
      DISCH_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[IN_GALOIS_GROUP] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ring_automorphism l (\x:B. ring_pow l x q)` THEN
      REWRITE_TAC[ring_automorphism; RING_ISOMORPHISM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[RESTRICT_PERMUTES_EQ];
      MATCH_MP_TAC RING_AUTOMORPHISM_EQ THEN
      EXISTS_TAC `\x:B. ring_pow l x q` THEN ASM_SIMP_TAC[];
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = group_element_order (galois_group(k,l) (h:A->B)) f` THEN
  SUBGOAL_THEN `~(d = 0) /\ d <= n` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `f:B->B`]
      GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
    SUBGOAL_THEN `~(group_carrier(galois_group(k,l) (h:A->B)) = {})`
    MP_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[GSYM CARD_EQ_0]] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `d divides CARD(group_carrier(galois_group(k,l) (h:A->B)))` THEN
      ASM_REWRITE_TAC[DIVIDES_ZERO];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:B. x IN ring_carrier l ==> ring_pow l x (q EXP d) = x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `f:B->B`; `d:num`]
      GROUP_POW_EQ_ID) THEN
    ASM_REWRITE_TAC[DIVIDES_REFL] THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[GALOIS_GROUP_POW_RING_POW; GALOIS_GROUP] THEN
    REWRITE_TAC[FUN_EQ_THM; I_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `q EXP d`] RING_POW_FIXPOINTS_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    TRANS_TAC LE_TRANS `q EXP 1` THEN
    ASM_REWRITE_TAC[EXP_1; LE_EXP] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `q EXP n <= q EXP d` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> lhs(concl th) = `CARD(ring_carrier(l:B ring))`)) THEN
    TRANS_TAC LE_TRANS
     `CARD {x:B | x IN ring_carrier l /\ ring_pow l x (q EXP d) = x}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]);;

let GALOIS_GROUP_FINITE_FIELD = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> (\x. if x IN ring_carrier l
                 then ring_pow l x (CARD(ring_carrier k)) else x)
            IN group_carrier(galois_group(k,l) h) /\
            subgroup_generated (galois_group(k,l) h)
              {\x. if x IN ring_carrier l
                   then ring_pow l x (CARD(ring_carrier k)) else x} =
            galois_group(k,l) h /\
            CARD(group_carrier(galois_group(k,l) h)) = extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    FINITE_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] CARD_GALOIS_GROUP_LE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] GALOIS_GROUP_FROBENIUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER]);;

let CYCLIC_GALOIS_GROUP_FINITE_FIELD = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> cyclic_group(galois_group(k,l) h)`,
  REWRITE_TAC[CYCLIC_GROUP_ALT] THEN MESON_TAC[GALOIS_GROUP_FINITE_FIELD]);;

(* The fixed field of the subgroup generated by the d-th power of the        *)
(* Frobenius map, of order [l:k] / d, has degree d over k; by                *)
(* FINITE_FIELD_INTERMEDIATE_FIELD_EXPLICIT it is the set of solutions of    *)
(* x^(q^d) = x.                                                              *)
let FINITE_FIELD_INTERMEDIATE_FIELD_DIVISOR = prove
 (`!(h:A->B) k l d.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\
        d divides extension_degree(k,l) h
        ==> {x | x IN ring_carrier l /\
                 ring_pow l x (CARD(ring_carrier k) EXP d) = x} subfield_of l /\
            IMAGE h (ring_carrier k) SUBSET
            {x | x IN ring_carrier l /\
                 ring_pow l x (CARD(ring_carrier k) EXP d) = x} /\
            extension_degree
             (k,subfield_generated l
                 {x | x IN ring_carrier l /\
                      ring_pow l x (CARD(ring_carrier k) EXP d) = x}) h = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    FINITE_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_GROUP_FINITE_FIELD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] GALOIS_GROUP_FROBENIUS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] EXTENSION_DEGREE_EQ_0) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] CARD_GALOIS_GROUP_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = extension_degree(k,l) (h:A->B)` THEN
  ABBREV_TAC
   `f = \x. if x IN ring_carrier l
            then ring_pow l x (CARD(ring_carrier(k:A ring))) else x:B` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(d = 0) /\ d * (n DIV d) = n /\ ~(n DIV d = 0)`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
    ASM_CASES_TAC `d:num = 0` THENL
     [UNDISCH_TAC `(d:num) divides n` THEN ASM_REWRITE_TAC[DIVIDES_ZERO];
      ASM_SIMP_TAC[DIV_EQ_0; NOT_LT]] THEN
    MP_TAC(SPECL [`d:num`; `n:num`] DIVIDES_LE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `H = group_carrier(subgroup_generated (galois_group(k,l) (h:A->B))
                       {group_pow (galois_group(k,l) h) f d})` THEN
  SUBGOAL_THEN `CARD(H:(B->B)->bool) = n DIV d` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `f:B->B`; `d:num`]
      GROUP_ELEMENT_ORDER_POW) THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`;
                   `group_pow (galois_group(k,l) (h:A->B)) f d`]
      CARD_CYCLIC_SUBGROUP_ORDER) THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`;
                   `group_pow (galois_group(k,l) (h:A->B)) f d`]
      FINITE_CYCLIC_SUBGROUP_ORDER) THEN
    ASM_SIMP_TAC[GROUP_POW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `H:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "H" THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `fixed_field l (H:(B->B)->bool)`]
    GALOIS_CORRESPONDENCE_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[EQ_MULT_RCANCEL]
   `!a b c m:num. a * c = m ==> b * c = m /\ ~(c = 0) ==> a = b`)) THEN
  DISCH_THEN(MP_TAC o SPEC `d:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `fixed_field l (H:(B->B)->bool)`]
    FINITE_FIELD_INTERMEDIATE_FIELD_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

let FINITE_FIELD_INTERMEDIATE_FIELDS = prove
 (`!(h:A->B) k l d.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> (d divides extension_degree(k,l) h <=>
             ?!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
                  extension_degree(k,subfield_generated l s) h = d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `d:num`]
        FINITE_FIELD_INTERMEDIATE_FIELD_DIVISOR) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`s:B->bool`; `t:B->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `t:B->bool`]
        FINITE_FIELD_INTERMEDIATE_FIELD_EXPLICIT) THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
        FINITE_FIELD_INTERMEDIATE_FIELD_EXPLICIT) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `s:B->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    REWRITE_TAC[divides] THEN
    EXISTS_TAC `extension_degree(subfield_generated l (s:B->bool),l) I` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (s:B->bool)`; `l:B ring`]
      EXTENSION_DEGREE_TOWER_LAW) THEN
    ASM_SIMP_TAC[I_O_ID; FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
                 FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC[field_extension]]);;

(* ------------------------------------------------------------------------- *)
(* Hilbert 90. The norm and the trace of a finite Galois extension are       *)
(* written as the product and the sum over the Galois group G: they lie in   *)
(* the fixed field of G (for a Galois extension, in the image of the base),  *)
(* are multiplicative and additive, and do not change when x is replaced by  *)
(* f(x) for f in G. By the independence of the elements of G, due to         *)
(* Dedekind, some element has sum 1 over G. Every multiplicative 1-cocycle c *)
(* of G (c(f o g) = c(f) * f(c(g)), c(f) nonzero) is a coboundary f(b) / b,  *)
(* and every additive one (c(f o g) = c(f) + f(c(g))) is f(b) - b (Noether). *)
(* For G generated by g, x has product 1 over G exactly when x = y / g(y),   *)
(* and sum 0 exactly when x = y - g(y). The Galois hypothesis is not needed  *)
(* in these results: they hold for the Galois group of any finite extension. *)
(* ------------------------------------------------------------------------- *)

(* Sums and products over a group are invariant under left and right         *)
(* translations; products and sums over the Galois group of the images of    *)
(* x lie in the fixed field, so in the image of k for a Galois extension.    *)

let RING_SUM_GROUP_TRANSLATION = prove
 (`!G (r:B ring) (u:A->B) a.
        a IN group_carrier G
        ==> ring_sum r (group_carrier G) (\x. u(group_mul G a x)) =
            ring_sum r (group_carrier G) u /\
            ring_sum r (group_carrier G) (\x. u(group_mul G x a)) =
            ring_sum r (group_carrier G) u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THENL
   [MAP_EVERY EXISTS_TAC
     [`group_mul G (a:A)`; `group_mul G (group_inv G a:A)`];
    MAP_EVERY EXISTS_TAC
     [`\x. group_mul G x (a:A)`; `\x. group_mul G x (group_inv G a:A)`]] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN REPEAT STRIP_TAC THEN GROUP_TAC);;

let RING_PRODUCT_GROUP_TRANSLATION = prove
 (`!G (r:B ring) (u:A->B) a.
        a IN group_carrier G
        ==> ring_product r (group_carrier G) (\x. u(group_mul G a x)) =
            ring_product r (group_carrier G) u /\
            ring_product r (group_carrier G) (\x. u(group_mul G x a)) =
            ring_product r (group_carrier G) u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC RING_PRODUCT_EQ_GENERAL_INVERSES THENL
   [MAP_EVERY EXISTS_TAC
     [`group_mul G (a:A)`; `group_mul G (group_inv G a:A)`];
    MAP_EVERY EXISTS_TAC
     [`\x. group_mul G x (a:A)`; `\x. group_mul G x (group_inv G a:A)`]] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN REPEAT STRIP_TAC THEN GROUP_TAC);;

let RING_SUM_CYCLIC_GROUP = prove
 (`!G (a:A) (r:B ring) u.
        FINITE(group_carrier G) /\ a IN group_carrier G /\
        subgroup_generated G {a} = G
        ==> ring_sum r (group_carrier G) u =
            ring_sum r {i | i < CARD(group_carrier G)}
                       (\i. u(group_pow G a i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_CYCLIC_GROUP_POWERS) THEN
  ABBREV_TAC `n = CARD(group_carrier(G:A group))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:B ring`; `group_pow G (a:A)`; `u:A->B`; `{i:num | i < n}`]
    RING_SUM_IMAGE) THEN
  REWRITE_TAC[o_DEF; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[CONG_IMP_EQ]);;

let RING_PRODUCT_CYCLIC_GROUP = prove
 (`!G (a:A) (r:B ring) u.
        FINITE(group_carrier G) /\ a IN group_carrier G /\
        subgroup_generated G {a} = G
        ==> ring_product r (group_carrier G) u =
            ring_product r {i | i < CARD(group_carrier G)}
                           (\i. u(group_pow G a i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_CYCLIC_GROUP_POWERS) THEN
  ABBREV_TAC `n = CARD(group_carrier(G:A group))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:B ring`; `group_pow G (a:A)`; `u:A->B`; `{i:num | i < n}`]
    RING_PRODUCT_IMAGE) THEN
  REWRITE_TAC[o_DEF; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[CONG_IMP_EQ]);;

let GALOIS_PRODUCT_IN_FIXED_FIELD = prove
 (`!(h:A->B) k l x.
        x IN ring_carrier l
        ==> ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x) IN
            fixed_field l (group_carrier(galois_group(k,l) h)) /\
            ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f x) IN
            fixed_field l (group_carrier(galois_group(k,l) h))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IN_FIXED_FIELD; RING_PRODUCT; RING_SUM; AND_FORALL_THM] THEN
  X_GEN_TAC `g:B->B` THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> (f:B->B) x IN ring_carrier l`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_MONOMORPHISM) THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP RING_MONOMORPHISM_PRODUCT th;
                 MATCH_MP RING_MONOMORPHISM_SUM th]) THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`; `\f:B->B. f x`;
                 `g:B->B`] RING_PRODUCT_GROUP_TRANSLATION) THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`; `\f:B->B. f x`;
                 `g:B->B`] RING_SUM_GROUP_TRANSLATION) THEN
  ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP)); o_DEF] THEN
  SIMP_TAC[]);;

let GALOIS_PRODUCT_IN_BASE = prove
 (`!(h:A->B) k l x.
        galois_extension(k,l) h /\ x IN ring_carrier l
        ==> ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x) IN
            IMAGE h (ring_carrier k) /\
            ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f x) IN
            IMAGE h (ring_carrier k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FIXED_FIELD_GALOIS_GROUP) THEN
  ASM_SIMP_TAC[GALOIS_PRODUCT_IN_FIXED_FIELD]);;

(* The product and the sum over the Galois group are unchanged when x is     *)
(* replaced by f(x) for f in the group. For a finite extension the product   *)
(* is multiplicative and vanishes only at 0, the sum is additive, and at an  *)
(* element of the image of k they are its power and its multiple by the      *)
(* order of the group.                                                       *)

let GALOIS_PRODUCT_CONJUGATE = prove
 (`!(h:A->B) f k l x.
        f IN group_carrier(galois_group(k,l) h)
        ==> ring_product l (group_carrier(galois_group(k,l) h)) (\g. g(f x)) =
            ring_product l (group_carrier(galois_group(k,l) h)) (\g. g x) /\
            ring_sum l (group_carrier(galois_group(k,l) h)) (\g. g(f x)) =
            ring_sum l (group_carrier(galois_group(k,l) h)) (\g. g x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`; `\g:B->B. g x`;
                 `f:B->B`] RING_PRODUCT_GROUP_TRANSLATION) THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`; `\g:B->B. g x`;
                 `f:B->B`] RING_SUM_GROUP_TRANSLATION) THEN
  ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP)); o_DEF] THEN
  SIMP_TAC[]);;

let GALOIS_PRODUCT_MUL = prove
 (`!(h:A->B) k l x y.
        finite_extension(k,l) h /\ x IN ring_carrier l /\ y IN ring_carrier l
        ==> ring_product l (group_carrier(galois_group(k,l) h))
                           (\f. f(ring_mul l x y)) =
            ring_mul l
             (ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x))
             (ring_product l (group_carrier(galois_group(k,l) h)) (\f. f y))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_product l (group_carrier(galois_group(k,l) (h:A->B)))
                 (\f. ring_mul l ((f:B->B) x) (f y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
      (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM th)]);
    MATCH_MP_TAC RING_PRODUCT_MUL THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; GALOIS_GROUP_IN_CARRIER]]);;

let GALOIS_SUM_ADD = prove
 (`!(h:A->B) k l x y.
        finite_extension(k,l) h /\ x IN ring_carrier l /\ y IN ring_carrier l
        ==> ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. f(ring_add l x y)) =
            ring_add l
             (ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f x))
             (ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f y))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l (group_carrier(galois_group(k,l) (h:A->B)))
             (\f. ring_add l ((f:B->B) x) (f y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD
      (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM th)]);
    MATCH_MP_TAC RING_SUM_ADD THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; GALOIS_GROUP_IN_CARRIER]]);;

let GALOIS_PRODUCT_EQ_0 = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l
        ==> (ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x) =
             ring_0 l <=> x = ring_0 l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `integral_domain(l:B ring) /\
    FINITE(group_carrier(galois_group(k,l) (h:A->B)))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  field_extension; FIELD_IMP_INTEGRAL_DOMAIN];
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0]] THEN
  EQ_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; GALOIS_GROUP_RING_MONOMORPHISM];
    DISCH_TAC THEN EXISTS_TAC `I:B->B` THEN
    ASM_REWRITE_TAC[GALOIS_GROUP_I; I_THM]]);;

let GALOIS_PRODUCT_BASE = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier k
        ==> ring_product l (group_carrier(galois_group(k,l) h)) (\f. f(h x)) =
            ring_pow l (h x) (CARD(group_carrier(galois_group(k,l) h))) /\
            ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f(h x)) =
            ring_mul l
             (ring_of_num l (CARD(group_carrier(galois_group(k,l) h)))) (h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(h:A->B) x IN ring_carrier l /\
    FINITE(group_carrier(galois_group(k,l) h)) /\
    !f. f IN group_carrier(galois_group(k,l) h) ==> f(h x) = h x`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  FIELD_EXTENSION_IMP_SUBSET; GALOIS_GROUP_FIXES; SUBSET;
                  FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `\f:B->B. f((h:A->B) x)`; `\f:B->B. (h:A->B) x`;
                 `group_carrier(galois_group(k,l) (h:A->B))`]
    RING_PRODUCT_EQ) THEN
  MP_TAC(ISPECL [`l:B ring`; `\f:B->B. f((h:A->B) x)`; `\f:B->B. (h:A->B) x`;
                 `group_carrier(galois_group(k,l) (h:A->B))`]
    RING_SUM_EQ) THEN
  ASM_SIMP_TAC[RING_PRODUCT_CONST; RING_SUM_CONST]);;

(* For a finite Galois extension the norm and the trace are the product and  *)
(* the sum over the Galois group.                                            *)

let ALGEBRA_TRACE_NORM_GALOIS = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        x IN ring_carrier l
        ==> h(algebra_norm(k,l) h x) =
            ring_product l (group_carrier(galois_group(k,l) h)) (\s. s x) /\
            h(algebra_trace(k,l) h x) =
            ring_sum l (group_carrier(galois_group(k,l) h)) (\s. s x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:(B#num)ring`; `j:B->B#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> rand(concl th) = `j:B->B#num`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `k:A ring`; `l:B ring`;
                 `n:(B#num)ring`; `x:B`]
    ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GALOIS_IMP_SEPARABLE_EXTENSION] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `n:(B#num)ring`]
    GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS_NORMAL) THEN
  ASM_SIMP_TAC[GALOIS_IMP_NORMAL_EXTENSION; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  ABBREV_TAC `Gal = group_carrier(galois_group(k,l) (h:A->B))` THEN
  ABBREV_TAC `E = ring_homomorphism_extensions (k,l,n)
                    (h:A->B,(j:B->B#num) o h)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `E = IMAGE (\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f))
              Gal /\
    (!f f'. f IN Gal /\ f' IN Gal /\
            RESTRICTION (ring_carrier l) ((j:B->B#num) o f) =
            RESTRICTION (ring_carrier l) (j o f')
            ==> f = f')`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `BIJ (\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f))
          Gal E` THEN
    REWRITE_TAC[BIJ; INJ; SURJ] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Gal:(B->B)->bool) /\
                (!s:B->B. s IN Gal ==> s x IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Gal" THEN ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
    ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product n E (\s:B->B#num. s x) =
    (j:B->B#num) (ring_product l Gal (\s:B->B. s x)) /\
    ring_sum n E (\s:B->B#num. s x) =
    (j:B->B#num) (ring_sum l Gal (\s:B->B. s x))`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME
     `E = IMAGE (\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f))
                Gal`) THEN
    MP_TAC(ISPECL [`n:(B#num)ring`;
      `\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f)`;
      `\s:B->B#num. s x`; `Gal:(B->B)->bool`] RING_PRODUCT_IMAGE) THEN
    MP_TAC(ISPECL [`n:(B#num)ring`;
      `\f:B->B. RESTRICTION (ring_carrier l) ((j:B->B#num) o f)`;
      `\s:B->B#num. s x`; `Gal:(B->B)->bool`] RING_SUM_IMAGE) THEN
    REPEAT(ANTS_TAC THENL
     [REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[o_DEF] THEN
    (let th = ASSUME `ring_homomorphism(l,n) (j:B->B#num)` in
     ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_PRODUCT th;
                  MATCH_MP RING_HOMOMORPHISM_SUM th]) THEN
    REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ; MATCH_MP_TAC RING_SUM_EQ] THEN
    ASM_SIMP_TAC[RESTRICTION; o_THM];
    ALL_TAC] THEN
  UNDISCH_THEN
   `!f f':B->B. f IN Gal /\ f' IN Gal /\
                RESTRICTION (ring_carrier l) ((j:B->B#num) o f) =
                RESTRICTION (ring_carrier l) (j o f')
                ==> f = f'`
   (K ALL_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_TRACE_NORM_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(CONJUNCT2(REWRITE_RULE[ring_monomorphism]
   (ASSUME `ring_monomorphism(l,n) (j:B->B#num)`))) THEN
  ASM_REWRITE_TAC[RING_PRODUCT; RING_SUM] THEN
  MATCH_MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_IN_CARRIER) THEN
  ASM_REWRITE_TAC[]);;

(* For finite fields the Galois group is cyclic of order [l:k], generated by *)
(* the Frobenius map x |-> x^q, q the number of elements of k                *)
(* (GALOIS_GROUP_FINITE_FIELD), so the norm and the trace are the product    *)
(* and the sum of the x^(q^i) for i < [l:k].                                 *)

let ALGEBRA_TRACE_NORM_FINITE_FIELD = prove
 (`!(h:A->B) k l x.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\ x IN ring_carrier l
        ==> h(algebra_norm(k,l) h x) =
            ring_product l {i | i < extension_degree(k,l) h}
                         (\i. ring_pow l x (CARD(ring_carrier k) EXP i)) /\
            h(algebra_trace(k,l) h x) =
            ring_sum l {i | i < extension_degree(k,l) h}
                     (\i. ring_pow l x (CARD(ring_carrier k) EXP i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    FINITE_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_TRACE_NORM_GALOIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_GROUP_FINITE_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `g = \y. if y IN ring_carrier l
            then ring_pow l y (CARD(ring_carrier(k:A ring))) else y:B` THEN
  STRIP_TAC THEN
  UNDISCH_THEN
   `CARD(group_carrier(galois_group(k,l) (h:A->B))) = extension_degree(k,l) h`
   (SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `g:B->B`; `l:B ring`;
                 `\s:B->B. s x`] RING_PRODUCT_CYCLIC_GROUP) THEN
  MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `g:B->B`; `l:B ring`;
                 `\s:B->B. s x`] RING_SUM_CYCLIC_GROUP) THEN
  ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[GALOIS_GROUP_POW_RING_POW] THEN
  ASM_REWRITE_TAC[]);;

(* The elements of the Galois group of a finite extension are linearly       *)
(* independent over l (Dedekind), so some element has sum 1 over the group.  *)

let GALOIS_GROUP_INDEPENDENT = prove
 (`!(h:A->B) k l c.
        finite_extension(k,l) h /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> c f IN ring_carrier l) /\
        (!x. x IN ring_carrier l
             ==> ring_sum l (group_carrier(galois_group(k,l) h))
                   (\f. ring_mul l (c f) (f x)) = ring_0 l)
        ==> !f. f IN group_carrier(galois_group(k,l) h) ==> c f = ring_0 l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`;
                 `group_carrier(galois_group(k,l) (h:A->B))`;
                 `c:(B->B)->B`] RING_HOMOMORPHISMS_INDEPENDENT_SET) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION; field_extension;
                  FIELD_IMP_INTEGRAL_DOMAIN];
    ASM_MESON_TAC[FINITE_GALOIS_GROUP];
    REWRITE_TAC[GALOIS_GROUP_RING_HOMOMORPHISM];
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(MESON[]
     `~(!x:B. P x ==> (f:B->B) x = g x) ==> ?x. P x /\ ~(f x = g x)`) THEN
    ASM_MESON_TAC[PERMUTES_EQ; GALOIS_GROUP_PERMUTES]]);;

let GALOIS_SUM_EQ_1_EXISTS = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f x) =
                ring_1 l`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `field(l:B ring) /\ FINITE(G:(B->B)->bool) /\
    (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
    (!f x. f IN G /\ x IN ring_carrier l ==> (f:B->B) x IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    REWRITE_TAC[GALOIS_GROUP_IN_CARRIER; GALOIS_GROUP_RING_HOMOMORPHISM] THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  field_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x. x IN ring_carrier l /\ ~(ring_sum l G (\f. (f:B->B) x) = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `\f:B->B. ring_1(l:B ring)`] GALOIS_GROUP_INDEPENDENT) THEN
    ASM_REWRITE_TAC[RING_1] THEN
    SUBGOAL_THEN
     `!x. x IN ring_carrier l
          ==> ring_sum l G (\f. ring_mul l (ring_1 l) ((f:B->B) x)) =
              ring_sum l G (\f. f x)`
     (fun th -> SIMP_TAC[th])
    THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
      ASM_SIMP_TAC[RING_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q /\ (~p ==> r) ==> (r ==> q) ==> p`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[FIELD_NONTRIVIAL; GALOIS_GROUP_I]; MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `t = ring_sum l G (\f. (f:B->B) x)` THEN
  SUBGOAL_THEN
   `(t:B) IN ring_carrier l /\ !f. f IN G ==> (f:B->B) t = t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      GALOIS_PRODUCT_IN_FIXED_FIELD) THEN
    ASM_REWRITE_TAC[IN_FIXED_FIELD] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ring_mul l x (ring_inv l t):B` THEN
  ASM_SIMP_TAC[RING_MUL; RING_INV] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l G (\f. ring_mul l ((f:B->B) x) (ring_inv l t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
      MATCH_MP FIELD_HOMOMORPHISM_INV (CONJ (ASSUME `field(l:B ring)`) th);
      RING_INV]);
    MP_TAC(ISPECL [`l:B ring`; `\f:B->B. f x`; `ring_inv l t:B`;
                   `G:(B->B)->bool`] RING_SUM_RMUL) THEN
    ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV]]);;

(* Hilbert 90 in the form of Noether: multiplicative and additive 1-cocycles *)
(* of the Galois group of a finite extension are coboundaries. The cocycle   *)
(* c is twisted into an element b = sum over f of c(f) * f(x) (with x chosen *)
(* by Dedekind so that b is nonzero, resp. with x of sum 1), and then        *)
(* g(b) = b / c(g), resp. g(b) = b - c(g), for each g in the group.          *)

let HILBERT_90 = prove
 (`!(h:A->B) k l c.
        finite_extension(k,l) h /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> c f IN ring_carrier l /\ ~(c f = ring_0 l)) /\
        (!f g. f IN group_carrier(galois_group(k,l) h) /\
               g IN group_carrier(galois_group(k,l) h)
               ==> c(f o g) = ring_mul l (c f) (f(c g)))
        ==> ?b. b IN ring_carrier l /\ ~(b = ring_0 l) /\
                !f. f IN group_carrier(galois_group(k,l) h)
                    ==> c f = ring_div l (f b) b`,
  let lemma = prove
   (`!f a b c:A.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        c IN ring_carrier f /\ ~(b = ring_0 f) /\ ring_mul f c a = b
        ==> c = ring_div f (ring_inv f a) (ring_inv f b)`,
    FIELD_TAC) in
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `field(l:B ring) /\ FINITE(G:(B->B)->bool) /\
    (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
    (!f x. f IN G /\ x IN ring_carrier l ==> (f:B->B) x IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    REWRITE_TAC[GALOIS_GROUP_IN_CARRIER; GALOIS_GROUP_RING_HOMOMORPHISM] THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  field_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x. x IN ring_carrier l /\
        ~(ring_sum l G (\f. ring_mul l (c f) ((f:B->B) x)) = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `c:(B->B)->B`]
      GALOIS_GROUP_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GALOIS_GROUP_I];
    ALL_TAC] THEN
  ABBREV_TAC `b = ring_sum l G (\f. ring_mul l (c f) ((f:B->B) x))` THEN
  SUBGOAL_THEN `(b:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN `!g. g IN G ==> ring_mul l (c g) ((g:B->B) b) = b`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:B->B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(l,l) (g:B->B)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:B->B) b = ring_sum l G (\f. ring_mul l (g(c f)) (g((f:B->B) x)))`
    SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN
      FIRST_ASSUM(MP_TAC o ISPECL
       [`\f:B->B. ring_mul l (c f) (f x)`; `G:(B->B)->bool`] o
       MATCH_MP RING_HOMOMORPHISM_SUM) THEN
      ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM] THEN
      FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]);
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l G
        (\f. ring_mul l (c g) (ring_mul l ((g:B->B)(c f)) (g(f x))))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_LMUL THEN
      ASM_SIMP_TAC[RING_MUL];
      ALL_TAC] THEN
    EXPAND_TAC "b" THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`;
                   `\f:B->B. ring_mul l (c f) (f x)`; `g:B->B`]
        RING_SUM_GROUP_TRANSLATION) THEN
    ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ring_inv l b:B` THEN
  ASM_SIMP_TAC[RING_INV; FIELD_INV_EQ_0] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`] FIELD_HOMOMORPHISM_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MATCH_MP_TAC lemma THEN ASM_SIMP_TAC[]);;

let HILBERT_90_ADDITIVE = prove
 (`!(h:A->B) k l c.
        finite_extension(k,l) h /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> c f IN ring_carrier l) /\
        (!f g. f IN group_carrier(galois_group(k,l) h) /\
               g IN group_carrier(galois_group(k,l) h)
               ==> c(f o g) = ring_add l (c f) (f(c g)))
        ==> ?b. b IN ring_carrier l /\
                !f. f IN group_carrier(galois_group(k,l) h)
                    ==> c f = ring_sub l (f b) b`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `field(l:B ring) /\ FINITE(G:(B->B)->bool) /\
    (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
    (!f x. f IN G /\ x IN ring_carrier l ==> (f:B->B) x IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    REWRITE_TAC[GALOIS_GROUP_IN_CARRIER; GALOIS_GROUP_RING_HOMOMORPHISM] THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  field_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] GALOIS_SUM_EQ_1_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `b = ring_sum l G (\f. ring_mul l (c f) ((f:B->B) t))` THEN
  SUBGOAL_THEN `(b:B) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN `!g. g IN G ==> ring_add l (c g) ((g:B->B) b) = b`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:B->B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(l,l) (g:B->B)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:B->B) b = ring_sum l G (\f. ring_mul l (g(c f)) (g((f:B->B) t)))`
    SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN
      FIRST_ASSUM(MP_TAC o ISPECL
       [`\f:B->B. ring_mul l (c f) (f t)`; `G:(B->B)->bool`] o
       MATCH_MP RING_HOMOMORPHISM_SUM) THEN
      ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM] THEN
      FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `c(g:B->B) = ring_sum l G (\f. ring_mul l (c g) (g((f:B->B) t)))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`; `\f:B->B. (g:B->B)(f t)`; `(c:(B->B)->B) g`;
                     `G:(B->B)->bool`] RING_SUM_LMUL) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`;
                     `\f:B->B. f t`; `g:B->B`]
        RING_SUM_GROUP_TRANSLATION) THEN
      ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP)); o_THM] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_SIMP_TAC[RING_MUL_RID];
      ALL_TAC] THEN
    W(fun (asl,w) ->
      MP_TAC(PART_MATCH (rand o rand) RING_SUM_ADD (lhand w))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    EXPAND_TAC "b" THEN
    MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `l:B ring`;
                   `\f:B->B. ring_mul l (c f) (f t)`; `g:B->B`]
        RING_SUM_GROUP_TRANSLATION) THEN
    ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_RDISTRIB THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ring_neg l b:B` THEN ASM_SIMP_TAC[RING_NEG] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_NEG th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(RING_RULE
   `!r a x y:B.
        a IN ring_carrier r /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_add r a y = x
            ==> a = ring_sub r (ring_neg r y) (ring_neg r x)`) THEN
  ASM_SIMP_TAC[]);;

(* The cyclic forms. For the Galois group generated by g, with n elements,   *)
(* the partial products p(m) = x * g(x) * ... * g^(m-1)(x) satisfy           *)
(* p(i + j) = p(i) * g^i(p(j)); when the product of x over the group is 1,   *)
(* p(n) = 1 and p is periodic, so c(g^m) = p(m) is a well-defined cocycle    *)
(* with c(g) = x, and HILBERT_90 gives x = y / g(y). Similarly for the sums. *)
(* The converse directions hold for any g in the group.                      *)

let HILBERT_90_CYCLIC = prove
 (`!(h:A->B) k l g x.
        finite_extension(k,l) h /\
        g IN group_carrier(galois_group(k,l) h) /\
        subgroup_generated (galois_group(k,l) h) {g} = galois_group(k,l) h /\
        x IN ring_carrier l /\
        ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x) =
        ring_1 l
        ==> ?y. y IN ring_carrier l /\ ~(y = ring_0 l) /\
                x = ring_div l y (g y)`,
  let lemma = prove
   (`!f a b:A.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        ~(b = ring_0 f)
        ==> ring_div f (ring_inv f b) (ring_inv f a) = ring_div f a b`,
    FIELD_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `field(l:B ring) /\ FINITE(group_carrier(galois_group(k,l) (h:A->B))) /\
    group_id(galois_group(k,l) h) = I /\ group_mul(galois_group(k,l) h) = (o) /\
    (!f. f IN group_carrier(galois_group(k,l) h)
         ==> ring_monomorphism(l,l) f) /\
    (!f x. f IN group_carrier(galois_group(k,l) h) /\ x IN ring_carrier l
           ==> f x IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT2 GALOIS_GROUP; GALOIS_GROUP_IN_CARRIER;
                GALOIS_GROUP_RING_MONOMORPHISM] THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  field_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:B = ring_0 l)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      GALOIS_PRODUCT_EQ_0) THEN
    ASM_SIMP_TAC[FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  ABBREV_TAC `G = galois_group(k,l) (h:A->B)` THEN
  MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`]
    SUBGROUP_GENERATED_ELEMENT_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = CARD(group_carrier G:(B->B)->bool)` THEN
  ABBREV_TAC `e = group_pow G (g:B->B)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(!i y. y IN ring_carrier l ==> (e:num->B->B) i y IN ring_carrier l) /\
    (!i y z. y IN ring_carrier l /\ z IN ring_carrier l
             ==> e i (ring_mul l y z) = ring_mul l (e i y) (e i z)) /\
    (!i. e i (ring_1 l) = ring_1 l) /\
    (!i y. y IN ring_carrier l ==> (e i y = ring_0 l <=> y = ring_0 l)) /\
    (!i j y. e(i + j) y = e i (e j y)) /\ (!y. e 0 y = y) /\ e 1 = g`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!i. ring_monomorphism(l,l) ((e:num->B->B) i)` ASSUME_TAC
    THENL [EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW];
      GEN_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o
        MATCH_MP RING_HOMOMORPHISM_MUL o
        MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o SPEC `i:num`);
      GEN_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o
        MATCH_MP RING_HOMOMORPHISM_1 o
        MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o SPEC `i:num`);
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MONOMORPHISM_EQ_0 THEN
      ASM_REWRITE_TAC[ETA_AX];
      EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW_ADD; o_THM];
      EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW_0; I_THM];
      EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW_1]];
    ALL_TAC] THEN
  ABBREV_TAC `p = \j. ring_product l {i | i < j} (\i. (e:num->B->B) i x)` THEN
  SUBGOAL_THEN
   `(!j. (p:num->B) j IN ring_carrier l /\ ~(p j = ring_0 l)) /\
    p 0 = ring_1 l /\ p n = ring_1 l /\
    (!j. p(SUC j) = ring_mul l ((e:num->B->B) j x) (p j))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    ASM_SIMP_TAC[RING_PRODUCT; NUMSEG_CLAUSES_LT; RING_PRODUCT_CLAUSES;
                 FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL;
                 FIELD_IMP_INTEGRAL_DOMAIN; INTEGRAL_DOMAIN_PRODUCT_EQ_0] THEN
    MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`; `l:B ring`; `\f:B->B. f x`]
      RING_PRODUCT_CYCLIC_GROUP) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. (p:num->B)(i + j) = ring_mul l (p i) ((e:num->B->B) i (p j))`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[ADD_CLAUSES; RING_MUL_RID] THEN
    MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(SPEC_ALL RING_MUL_AC))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`; `p:num->B`] GROUP_POW_PERIODIC) THEN
  ASM_SIMP_TAC[RING_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:(B->B)->B`) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `c:(B->B)->B`]
    HILBERT_90) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`] FINITE_CYCLIC_GROUP_POWERS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:num->B->B) i o e j = e(i + j)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:B->B`) THEN
  SUBGOAL_THEN `(c:(B->B)->B) g = x` SUBST1_TAC THENL
   [UNDISCH_TAC `(e:num->B->B) 1 = g` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[ONE] THEN ASM_SIMP_TAC[RING_MUL_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `ring_inv l b:B` THEN
  ASM_SIMP_TAC[RING_INV; FIELD_INV_EQ_0] THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (g:B->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_IMP_HOMOMORPHISM THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `g:B->B`] FIELD_HOMOMORPHISM_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC lemma THEN ASM_SIMP_TAC[]);;

let HILBERT_90_ADDITIVE_CYCLIC = prove
 (`!(h:A->B) k l g x.
        finite_extension(k,l) h /\
        g IN group_carrier(galois_group(k,l) h) /\
        subgroup_generated (galois_group(k,l) h) {g} = galois_group(k,l) h /\
        x IN ring_carrier l /\
        ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f x) = ring_0 l
        ==> ?y. y IN ring_carrier l /\ x = ring_sub l y (g y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `field(l:B ring) /\ FINITE(group_carrier(galois_group(k,l) (h:A->B))) /\
    group_id(galois_group(k,l) h) = I /\ group_mul(galois_group(k,l) h) = (o) /\
    (!f. f IN group_carrier(galois_group(k,l) h)
         ==> ring_monomorphism(l,l) f) /\
    (!f x. f IN group_carrier(galois_group(k,l) h) /\ x IN ring_carrier l
           ==> f x IN ring_carrier l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT2 GALOIS_GROUP; GALOIS_GROUP_IN_CARRIER;
                GALOIS_GROUP_RING_MONOMORPHISM] THEN
    ASM_MESON_TAC[FINITE_GALOIS_GROUP; FINITE_IMP_FIELD_EXTENSION;
                  field_extension];
    ALL_TAC] THEN
  ABBREV_TAC `G = galois_group(k,l) (h:A->B)` THEN
  MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`]
    SUBGROUP_GENERATED_ELEMENT_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = CARD(group_carrier G:(B->B)->bool)` THEN
  ABBREV_TAC `e = group_pow G (g:B->B)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(!i y. y IN ring_carrier l ==> (e:num->B->B) i y IN ring_carrier l) /\
    (!i y z. y IN ring_carrier l /\ z IN ring_carrier l
             ==> e i (ring_add l y z) = ring_add l (e i y) (e i z)) /\
    (!i. e i (ring_0 l) = ring_0 l) /\
    (!i j y. e(i + j) y = e i (e j y)) /\ (!y. e 0 y = y) /\ e 1 = g`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!i. ring_monomorphism(l,l) ((e:num->B->B) i)` ASSUME_TAC
    THENL [EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW];
      GEN_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o
        MATCH_MP RING_HOMOMORPHISM_ADD o
        MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o SPEC `i:num`);
      GEN_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o
        MATCH_MP RING_HOMOMORPHISM_0 o
        MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o SPEC `i:num`);
      EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW_ADD; o_THM];
      EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW_0; I_THM];
      EXPAND_TAC "e" THEN ASM_SIMP_TAC[GROUP_POW_1]];
    ALL_TAC] THEN
  ABBREV_TAC `s = \j. ring_sum l {i | i < j} (\i. (e:num->B->B) i x)` THEN
  SUBGOAL_THEN
   `(!j. (s:num->B) j IN ring_carrier l) /\ s 0 = ring_0 l /\
    s n = ring_0 l /\ (!j. s(SUC j) = ring_add l ((e:num->B->B) j x) (s j))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    ASM_SIMP_TAC[RING_SUM; NUMSEG_CLAUSES_LT; RING_SUM_CLAUSES;
                 FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`; `l:B ring`; `\f:B->B. f x`]
      RING_SUM_CYCLIC_GROUP) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. (s:num->B)(i + j) = ring_add l (s i) ((e:num->B->B) i (s j))`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[ADD_CLAUSES; RING_ADD_RZERO] THEN
    MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(SPEC_ALL RING_ADD_AC))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`; `s:num->B`] GROUP_POW_PERIODIC) THEN
  ASM_SIMP_TAC[RING_ADD_RZERO] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:(B->B)->B`) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `c:(B->B)->B`]
    HILBERT_90_ADDITIVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`G:(B->B)group`; `g:B->B`] FINITE_CYCLIC_GROUP_POWERS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:num->B->B) i o e j = e(i + j)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:B->B`) THEN
  SUBGOAL_THEN `(c:(B->B)->B) g = x` SUBST1_TAC THENL
   [UNDISCH_TAC `(e:num->B->B) 1 = g` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[ONE] THEN ASM_SIMP_TAC[RING_ADD_RZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `ring_neg l b:B` THEN ASM_SIMP_TAC[RING_NEG] THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (g:B->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_IMP_HOMOMORPHISM THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_NEG th]) THEN
  MATCH_MP_TAC(RING_RULE
   `!r x y:B.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_sub r x y = ring_sub r (ring_neg r y) (ring_neg r x)`) THEN
  ASM_SIMP_TAC[]);;

let HILBERT_90_CYCLIC_EQ = prove
 (`!(h:A->B) k l g x.
        finite_extension(k,l) h /\
        g IN group_carrier(galois_group(k,l) h) /\
        subgroup_generated (galois_group(k,l) h) {g} = galois_group(k,l) h /\
        x IN ring_carrier l
        ==> (ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x) =
             ring_1 l <=>
             ?y. y IN ring_carrier l /\ ~(y = ring_0 l) /\
                 x = ring_div l y (g y))`,
  let lemma = prove
   (`!f a b:A.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        ~(b = ring_0 f) /\ ring_mul f a b = b
        ==> a = ring_1 f`,
    FIELD_TAC) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[HILBERT_90_CYCLIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `field(l:B ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION; field_extension]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:B->B) y IN ring_carrier l /\ ~(g y = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER; RING_MONOMORPHISM_EQ_0;
                  GALOIS_GROUP_RING_MONOMORPHISM];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  EXISTS_TAC
   `ring_product l (group_carrier(galois_group(k,l) (h:A->B))) (\f. f y)` THEN
  ASM_SIMP_TAC[RING_PRODUCT; GALOIS_PRODUCT_EQ_0] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `(g:B->B) y`]
    GALOIS_PRODUCT_MUL) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `y:B`]
    GALOIS_PRODUCT_CONJUGATE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[ring_div; GSYM RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV;
               RING_MUL_RID]);;

let HILBERT_90_ADDITIVE_CYCLIC_EQ = prove
 (`!(h:A->B) k l g x.
        finite_extension(k,l) h /\
        g IN group_carrier(galois_group(k,l) h) /\
        subgroup_generated (galois_group(k,l) h) {g} = galois_group(k,l) h /\
        x IN ring_carrier l
        ==> (ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f x) =
             ring_0 l <=>
             ?y. y IN ring_carrier l /\ x = ring_sub l y (g y))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[HILBERT_90_ADDITIVE_CYCLIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `(g:B->B) y IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_sub l y ((g:B->B) y)`;
                 `(g:B->B) y`] GALOIS_SUM_ADD) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `y:B`]
    GALOIS_PRODUCT_CONJUGATE) THEN
  ASM_SIMP_TAC[RING_SUB; RING_RULE
   `!r a b:B. a IN ring_carrier r /\ b IN ring_carrier r
              ==> ring_add r (ring_sub r a b) b = a`] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(RING_RULE
   `!r a b:B. a IN ring_carrier r /\ b IN ring_carrier r
              ==> b = ring_add r a b ==> a = ring_0 r`) THEN
  REWRITE_TAC[RING_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Radical extensions. The extension (k,l) h is radical when l is generated  *)
(* over the image of k by finitely many elements a(0), ..., a(n-1) such that *)
(* a positive power of each a(i) lies in the subfield generated by the image *)
(* of k and the earlier a(j). Radical extensions are finite. They are closed *)
(* under towers and homomorphic images, a radical extension is radical over  *)
(* each intermediate field, and inside a field the compositum of finitely    *)
(* many radical subextensions is radical.                                    *)
(* ------------------------------------------------------------------------- *)

let radical_extension = new_definition
 `radical_extension (k:A ring,l:B ring) (h:A->B) <=>
        field_extension (k,l) h /\
        ?n (a:num->B) (m:num->num).
          (!i. i < n
               ==> ~(m i = 0) /\ a i IN ring_carrier l /\
                   ring_pow l (a i) (m i) IN
                   ring_carrier(subfield_generated l
                     (IMAGE h (ring_carrier k) UNION IMAGE a {j | j < i}))) /\
          subfield_generated l
            (IMAGE h (ring_carrier k) UNION IMAGE a {i | i < n}) = l`;;

let RADICAL_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l. radical_extension(k,l) h ==> field_extension(k,l) h`,
  SIMP_TAC[radical_extension]);;

let RADICAL_EXTENSION_EQ = prove
 (`!(f:A->B) f' k l.
        radical_extension(k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> radical_extension(k,l) f'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (f':A->B) (ring_carrier k) = IMAGE f (ring_carrier k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:A. x IN s ==> (f':A->B) x = f x) ==> IMAGE f' s = IMAGE f s`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIELD_EXTENSION_EQ THEN EXISTS_TAC `f:A->B` THEN
    ASM_REWRITE_TAC[]]);;

let RADICAL_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> radical_extension (k,l) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[radical_extension] THEN
  MAP_EVERY EXISTS_TAC [`0`; `(\i. ring_0 l):num->B`; `(\i. 1):num->num`] THEN
  REWRITE_TAC[LT; EMPTY_GSPEC; IMAGE_CLAUSES; UNION_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN
  SIMP_TAC[RING_ISOMORPHISM; SUBFIELD_GENERATED_RING_CARRIER]);;

let RADICAL_EXTENSION_REFL = prove
 (`!k:A ring. radical_extension(k,k) I <=> field k`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[RADICAL_IMP_FIELD_EXTENSION; FIELD_EXTENSION_REFL];
    DISCH_TAC THEN MATCH_MP_TAC RADICAL_EXTENSION_ISOMORPHISM THEN
    ASM_REWRITE_TAC[RING_ISOMORPHISM_I]]);;

let RADICAL_EXTENSION_IMP_FINITE = prove
 (`!(h:A->B) k l. radical_extension(k,l) h ==> finite_extension(k,l) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `a:num->B`
     (X_CHOOSE_THEN `m:num->num` STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[finitely_generated_extension] THEN
    EXISTS_TAC `IMAGE (a:num->B) {i | i < n}` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> algebraic_over(k,l) (h:A->B) ((a:num->B) i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `(a:num->B) i`;
                   `(m:num->num) i`] ALGEBRAIC_OVER_POW_EQ) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `IMAGE (a:num->B) {j | j < i}`]
      ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[LT_TRANS]; DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[algebraic_extension] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `IMAGE (a:num->B) {i | i < n}`]
    ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM]);;

let RADICAL_EXTENSION_SIMPLE = prove
 (`!(h:A->B) k l a n.
     field_extension(k,l) h /\ a IN ring_carrier l /\ ~(n = 0) /\
     ring_pow l a n IN IMAGE h (ring_carrier k) /\
     subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l
     ==> radical_extension(k,l) h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[radical_extension] THEN
  MAP_EVERY EXISTS_TAC [`1`; `(\i. a):num->B`; `(\i. n):num->num`] THEN
  REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`; SING_GSPEC; FORALL_UNWIND_THM2;
              LT; EMPTY_GSPEC; IMAGE_CLAUSES; UNION_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_SUBSET];
    ASM_REWRITE_TAC[SET_RULE `s UNION {a:B} = a INSERT s`]]);;

(* Two sequences of radical generators can be concatenated when the base set *)
(* of the second lies in the subfield generated by the first.                *)

let RADICAL_GENERATORS_APPEND = prove
 (`!(l:B ring) s t n (p:num) (a:num->B) b (m:num->num) m'.
        (!i. i < n
             ==> ~(m i = 0) /\ a i IN ring_carrier l /\
                 ring_pow l (a i) (m i) IN
                 ring_carrier(subfield_generated l
                   (s UNION IMAGE a {j | j < i}))) /\
        (!i. i < p
             ==> ~(m' i = 0) /\ b i IN ring_carrier l /\
                 ring_pow l (b i) (m' i) IN
                 ring_carrier(subfield_generated l
                   (t UNION IMAGE b {j | j < i}))) /\
        t SUBSET
        ring_carrier(subfield_generated l (s UNION IMAGE a {j | j < n}))
        ==> ?q c m''.
              (!i. i < q:num
                   ==> ~(m'' i = 0) /\ c i IN ring_carrier l /\
                       ring_pow l (c i) (m'' i) IN
                       ring_carrier(subfield_generated l
                         (s UNION IMAGE c {j | j < i}))) /\
              IMAGE c {i | i < q} =
              IMAGE a {i | i < n} UNION IMAGE b {i | i < p}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a")
   (CONJUNCTS_THEN2 (LABEL_TAC "b") ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`n + p:num`; `\i. if i < n then (a:num->B) i else b(i - n)`;
    `\i. if i < n then (m:num->num) i else m'(i - n)`] THEN
  SUBGOAL_THEN
   `!i. i <= n
        ==> IMAGE (\i. if i < n then (a:num->B) i else b(i - n)) {j | j < i} =
            IMAGE a {j | j < i}`
  (LABEL_TAC "lo") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x:num. x IN s ==> (f:num->B) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. IMAGE (\i. if i < n then (a:num->B) i else b(i - n)) {j | j < n + i} =
        IMAGE a {j | j < n} UNION IMAGE b {j | j < i}`
  (LABEL_TAC "hi") THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:B` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `j:num`
       (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      COND_CASES_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `j - n:num` THEN REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `j:num`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THENL
       [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        EXISTS_TAC `n + j:num` THEN
        REWRITE_TAC[ARITH_RULE `~(n + j < n:num)`; ADD_SUB2] THEN
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < n:num` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "lo" (fun th -> REWRITE_TAC[MATCH_MP th
      (MATCH_MP LT_IMP_LE (ASSUME `i < n:num`))]) THEN
    REMOVE_THEN "a" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[NOT_LT; LE_EXISTS] o
    check (fun th -> concl th = `~(i < n:num)`)) THEN
  ASM_REWRITE_TAC[ADD_SUB2] THEN
  REMOVE_THEN "b" (MP_TAC o SPEC `d:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `(y:B) IN s0 ==> s0 SUBSET t0 ==> y IN t0`)) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `ring_carrier(subfield_generated l
     (ring_carrier(subfield_generated l (s UNION IMAGE (a:num->B) {j | j < n}))
      UNION IMAGE (b:num->B) {j | j < d}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
    MATCH_MP_TAC(SET_RULE
     `t SUBSET u ==> t UNION v SUBSET u UNION v:B->bool`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SUBFIELD_GENERATED_UNION_LEFT; UNION_ASSOC; SUBSET_REFL]]);;

let RADICAL_EXTENSION_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m.
     radical_extension(k,l) f /\ radical_extension(l,m) g
     ==> radical_extension(k,m) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `a:num->B`
       (X_CHOOSE_THEN `ma:num->num`
         (CONJUNCTS_THEN2 (LABEL_TAC "a") ASSUME_TAC)))))
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `b:num->C`
       (X_CHOOSE_THEN `mb:num->num`
         (CONJUNCTS_THEN2 (LABEL_TAC "b") ASSUME_TAC)))))) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    check (fun th -> concl th = `field_extension(l:B ring,m:C ring) g`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `!i. i <= n:num
        ==> ring_carrier(subfield_generated m
              (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION
               IMAGE (g o a) {j | j < i})) =
            IMAGE g (ring_carrier(subfield_generated l
              (IMAGE f (ring_carrier k) UNION IMAGE a {j | j < i})))`
  (LABEL_TAC "im") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_o; GSYM IMAGE_UNION] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; UNION_SUBSET] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      USE_THEN "a" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated m
      (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION
       IMAGE (g o (a:num->B)) {j | j < n})) =
    IMAGE g (ring_carrier l)`
  ASSUME_TAC THENL
   [USE_THEN "im" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k)`;
                 `IMAGE (g:B->C) (ring_carrier l)`; `n:num`; `p:num`;
                 `(g:B->C) o (a:num->B)`; `b:num->C`; `ma:num->num`;
                 `mb:num->num`] RADICAL_GENERATORS_APPEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "a" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `i < n:num`)) THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `g:B->C`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(a:num->B) i IN ring_carrier l`))]) THEN
    USE_THEN "im" (fun th -> REWRITE_TAC[MATCH_MP th
      (MATCH_MP LT_IMP_LE (ASSUME `i < n:num`))]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `c:num->C`
    (X_CHOOSE_THEN `mc:num->num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`q:num`; `c:num->C`; `mc:num->num`] THEN
  ASM_REWRITE_TAC[GSYM UNION_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM SUBFIELD_GENERATED_UNION_LEFT] THEN
  ASM_REWRITE_TAC[]);;

let RADICAL_EXTENSION_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m.
     field_extension(k,l) f /\ field_extension(l,m) g /\
     radical_extension(k,m) (g o f)
     ==> radical_extension(l,m) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
     (X_CHOOSE_THEN `a:num->C` (X_CHOOSE_THEN `ma:num->num`
       STRIP_ASSUME_TAC)))))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `a:num->C`; `ma:num->num`] THEN
  SUBGOAL_THEN
   `!t. IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION t SUBSET
        IMAGE g (ring_carrier l) UNION t`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> s UNION u SUBSET t UNION u:C->bool`) THEN
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl) o
      check (free_in `ma:num->num` o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(y:C) IN s0 ==> s0 SUBSET t0 ==> y IN t0`)) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ring_carrier(subfield_generated m
      (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION
       IMAGE (a:num->C) {i | i < n}))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM_REWRITE_TAC[]]]);;

let RADICAL_EXTENSION_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (j:B->C) k l m.
     radical_extension(k,l) h /\ field m /\ ring_homomorphism(l,m) j
     ==> radical_extension
           (k,subfield_generated m (IMAGE j (ring_carrier l))) (j o h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RADICAL_EXTENSION_TRANS THEN
  EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RADICAL_EXTENSION_ISOMORPHISM THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP RADICAL_IMP_FIELD_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ring_monomorphism(l:B ring,m:C ring) j` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (j:B->C) (ring_carrier l) subfield_of m` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF];
    ALL_TAC] THEN
  REWRITE_TAC[RING_ISOMORPHISM] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
    MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[field_extension; SUBSET_REFL];
    ASM_MESON_TAC[ring_monomorphism]]);;

let RADICAL_EXTENSION_HOMOMORPHIC_IMAGE_GEN = prove
 (`!(h:A->B) (g:A->C) (e:B->C) k l m.
        radical_extension(k,l) h /\ field m /\ ring_homomorphism(l,m) e /\
        (!x. x IN ring_carrier k ==> e(h x) = g x)
        ==> IMAGE e (ring_carrier l) subfield_of m /\
            radical_extension(k,subfield_generated m (IMAGE e (ring_carrier l)))
                             g`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    EXISTS_TAC `l:B ring` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
      MATCH_MP RADICAL_IMP_FIELD_EXTENSION) THEN
    ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    MATCH_MP_TAC RADICAL_EXTENSION_EQ THEN
    EXISTS_TAC `(e:B->C) o (h:A->B)` THEN
    ASM_SIMP_TAC[RADICAL_EXTENSION_HOMOMORPHIC_IMAGE; o_THM]]);;

let RADICAL_EXTENSION_BASE = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> radical_extension(k,subfield_generated l (IMAGE h (ring_carrier k)))
                             h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`I:A->A`; `h:A->B`; `k:A ring`; `k:A ring`; `l:B ring`]
    RADICAL_EXTENSION_HOMOMORPHIC_IMAGE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_SIMP_TAC[RADICAL_EXTENSION_REFL; I_O_ID;
               RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

(* An intermediate field s of a field extension (k,l) h is radical over k    *)
(* exactly when s is generated in l over the image of k by a sequence of     *)
(* radical generators. Hence composita of radical subextensions of a field   *)
(* are radical.                                                              *)

let RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ s subfield_of l
        ==> (radical_extension(k,subfield_generated l s) h <=>
             IMAGE h (ring_carrier k) SUBSET s /\
             ?n:num a m.
               (!i. i < n
                    ==> ~(m i = 0) /\ a i IN ring_carrier l /\
                        ring_pow l (a i) (m i) IN
                        ring_carrier(subfield_generated l
                          (IMAGE h (ring_carrier k) UNION
                           IMAGE a {j | j < i}))) /\
               ring_carrier(subfield_generated l
                 (IMAGE h (ring_carrier k) UNION IMAGE a {i | i < n})) = s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[radical_extension; CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               RING_POW_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC(TAUT
   `(p <=> p') /\ (p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`) THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET) THEN
      ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
      MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!n (a:num->B).
      (!i. i < n ==> a i IN s)
      ==> !i. i <= n
              ==> subfield_generated (subfield_generated l s)
                    (IMAGE (h:A->B) (ring_carrier k) UNION
                     IMAGE a {j | j < i}) =
                  subfield_generated l
                    (IMAGE h (ring_carrier k) UNION IMAGE a {j | j < i})`
  (LABEL_TAC "sg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; UNION_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. subfield_generated l t = subfield_generated l s <=>
        ring_carrier(subfield_generated l t) = (s:B->bool)`
  (LABEL_TAC "eq") THENL
   [GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED]];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `a:num->B`
    (X_CHOOSE_THEN `m:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "a")
      ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `a:num->B`; `m:num->num`] THENL
   [SUBGOAL_THEN `!i. i < n ==> (a:num->B) i IN s` ASSUME_TAC THENL
     [USE_THEN "a" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
    USE_THEN "sg" (MP_TAC o SPECL [`n:num`; `a:num->B`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "sgn")] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "a" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `i < n:num`)) THEN
      USE_THEN "sgn" (MP_TAC o C MATCH_MP
        (MATCH_MP LT_IMP_LE (ASSUME `i < n:num`))) THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                           REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!x:B s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `s:B->bool` THEN ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET];
      USE_THEN "sgn" (MP_TAC o C MATCH_MP (SPEC `n:num` LE_REFL)) THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      REMOVE_THEN "eq" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `!i. i < n ==> (a:num->B) i IN s` ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN CONJ_TAC THENL
       [USE_THEN "a" (fun th -> MESON_TAC[th; ASSUME `i < n:num`]);
        REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN DISJ2_TAC THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "sg" (MP_TAC o SPECL [`n:num`; `a:num->B`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "sgn")] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "a" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `i < n:num`)) THEN
      USE_THEN "sgn" (MP_TAC o C MATCH_MP
        (MATCH_MP LT_IMP_LE (ASSUME `i < n:num`))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
      USE_THEN "sgn" (MP_TAC o C MATCH_MP (SPEC `n:num` LE_REFL)) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

let RADICAL_EXTENSION_COMPOSITUM = prove
 (`!(h:A->B) k l s t.
     field l /\ s subfield_of l /\ t subfield_of l /\
     radical_extension(k,subfield_generated l s) h /\
     radical_extension(k,subfield_generated l t) h
     ==> radical_extension(k,subfield_generated l (s UNION t)) h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field_extension(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (s:B->bool)`; `l:B ring`]
      FIELD_EXTENSION_TRANS) THEN
    ASM_SIMP_TAC[RADICAL_IMP_FIELD_EXTENSION;
                 FIELD_EXTENSION_SUBFIELD_GENERATED; I_O_ID];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `ring_carrier(subfield_generated l (s UNION t:B->bool))`]
    RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `t:B->bool`]
    RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
    (X_CHOOSE_THEN `a:num->B` (X_CHOOSE_THEN `ma:num->num`
      STRIP_ASSUME_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num`
    (X_CHOOSE_THEN `b:num->B` (X_CHOOSE_THEN `mb:num->num`
      STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:B->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s UNION t:B->bool` THEN REWRITE_TAC[SUBSET_UNION] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET THEN
    ASM_SIMP_TAC[UNION_SUBSET; SUBFIELD_OF_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k)`;
                 `IMAGE (h:A->B) (ring_carrier k)`; `n:num`; `p:num`;
                 `a:num->B`; `b:num->B`; `ma:num->num`; `mb:num->num`]
    RADICAL_GENERATORS_APPEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `c:num->B`
    (X_CHOOSE_THEN `mc:num->num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`q:num`; `c:num->B`; `mc:num->num`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `t:B->bool`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `s:B->bool`)) THEN
  REWRITE_TAC[SUBFIELD_GENERATED_UNION] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let RADICAL_EXTENSION_UNIONS = prove
 (`!(h:A->B) k l f.
        field_extension(k,l) h /\ FINITE f /\
        (!s. s IN f
             ==> s subfield_of l /\
                 radical_extension(k,subfield_generated l s) h)
        ==> radical_extension
              (k,subfield_generated l (IMAGE h (ring_carrier k) UNION UNIONS f))
              h`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[UNIONS_0; UNION_EMPTY; RADICAL_EXTENSION_BASE] THEN
  MAP_EVERY X_GEN_TAC [`s:B->bool`; `f:(B->bool)->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) (ring_carrier k) UNION UNIONS (s INSERT f) =
    s UNION (IMAGE h (ring_carrier k) UNION UNIONS f)`
  SUBST1_TAC THENL [REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUBFIELD_GENERATED_UNION_RIGHT] THEN
  MATCH_MP_TAC RADICAL_EXTENSION_COMPOSITUM THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
               SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED]);;

(* ------------------------------------------------------------------------- *)
(* Radical elements. An element x of l is radical over k when it lies in a   *)
(* subfield of l that is radical over k, that is, x can be expressed by      *)
(* radicals over the image of k inside l. Finitely many radical elements lie *)
(* in one radical subextension, so the radical elements form a subfield of l *)
(* containing the image of k, closed under roots and mapped to radical       *)
(* elements by homomorphisms. An extension generated by finitely many of its *)
(* radical elements is radical, and a finite extension is radical exactly    *)
(* when all of its elements are radical.                                     *)
(* ------------------------------------------------------------------------- *)

(* The radical tower must lie inside the specified ambient field l. For     *)
(* solvability by radicals with auxiliary roots in a larger field, use an    *)
(* algebraically closed ambient field, as in GALOIS_SOLVABLE_EQ_RADICAL.      *)
let radical_element = new_definition
 `radical_element (k:A ring,l:B ring) (h:A->B) x <=>
        ?s. s subfield_of l /\ x IN s /\
            radical_extension (k,subfield_generated l s) h`;;

let RADICAL_ELEMENT_IN_CARRIER = prove
 (`!(h:A->B) k l x. radical_element(k,l) h x ==> x IN ring_carrier l`,
  REWRITE_TAC[radical_element] THEN
  MESON_TAC[SUBFIELD_OF_IMP_SUBSET; SUBSET]);;

let RADICAL_ELEMENT_BASE = prove
 (`!(h:A->B) k l x.
     field_extension(k,l) h /\ x IN ring_carrier k
     ==> radical_element(k,l) h (h x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[radical_element] THEN
  EXISTS_TAC
   `ring_carrier(subfield_generated l (IMAGE (h:A->B) (ring_carrier k)))` THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED;
               RADICAL_EXTENSION_BASE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_SUBFIELD_GENERATED THEN
    ASM_MESON_TAC[field_extension];
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_SUBSET; FUN_IN_IMAGE]]);;

let RADICAL_ELEMENT_NEG = prove
 (`!(h:A->B) k l x.
     radical_element(k,l) h x ==> radical_element(k,l) h (ring_neg l x)`,
  REWRITE_TAC[radical_element] THEN MESON_TAC[IN_SUBFIELD_NEG]);;

let RADICAL_ELEMENT_INV = prove
 (`!(h:A->B) k l x.
     radical_element(k,l) h x ==> radical_element(k,l) h (ring_inv l x)`,
  REWRITE_TAC[radical_element] THEN MESON_TAC[IN_SUBFIELD_INV]);;

let RADICAL_ELEMENT_POW = prove
 (`!(h:A->B) k l x n.
     radical_element(k,l) h x ==> radical_element(k,l) h (ring_pow l x n)`,
  REWRITE_TAC[radical_element] THEN MESON_TAC[IN_SUBFIELD_POW]);;

let RADICAL_ELEMENTS_COMMON_RADICAL_EXTENSION = prove
 (`!(h:A->B) k l b.
        field_extension(k,l) h /\ FINITE b /\
        (!x. x IN b ==> radical_element(k,l) h x)
        ==> ?s. s subfield_of l /\ b SUBSET s /\
                radical_extension(k,subfield_generated l s) h`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC
     `ring_carrier(subfield_generated l (IMAGE (h:A->B) (ring_carrier k)))` THEN
    ASM_SIMP_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED; EMPTY_SUBSET;
                 RADICAL_EXTENSION_BASE; SUBFIELD_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `b:B->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT; INSERT_SUBSET] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:B->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:B->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [radical_element]) THEN
  EXISTS_TAC `ring_carrier(subfield_generated l (v UNION u:B->bool))` THEN
  SUBGOAL_THEN
   `(v UNION u:B->bool) SUBSET ring_carrier(subfield_generated l (v UNION u))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET THEN
    ASM_SIMP_TAC[UNION_SUBSET; SUBFIELD_OF_IMP_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
               SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED;
               RADICAL_EXTENSION_COMPOSITUM] THEN
  ASM SET_TAC[]);;

let RADICAL_ELEMENT_PAIR = prove
 (`!(h:A->B) k l x y.
     field_extension(k,l) h /\
     radical_element(k,l) h x /\ radical_element(k,l) h y
     ==> ?s. s subfield_of l /\ x IN s /\ y IN s /\
             radical_extension(k,subfield_generated l s) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{x:B,y}`]
    RADICAL_ELEMENTS_COMMON_RADICAL_EXTENSION) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                  NOT_IN_EMPTY; INSERT_SUBSET; EMPTY_SUBSET; GSYM CONJ_ASSOC]);;

let RADICAL_ELEMENT_ADD = prove
 (`!(h:A->B) k l x y.
     field_extension(k,l) h /\
     radical_element(k,l) h x /\ radical_element(k,l) h y
     ==> radical_element(k,l) h (ring_add l x y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RADICAL_ELEMENT_PAIR) THEN
  REWRITE_TAC[radical_element] THEN MESON_TAC[IN_SUBFIELD_ADD]);;

let RADICAL_ELEMENT_SUB = prove
 (`!(h:A->B) k l x y.
     field_extension(k,l) h /\
     radical_element(k,l) h x /\ radical_element(k,l) h y
     ==> radical_element(k,l) h (ring_sub l x y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RADICAL_ELEMENT_PAIR) THEN
  REWRITE_TAC[radical_element] THEN MESON_TAC[IN_SUBFIELD_SUB]);;

let RADICAL_ELEMENT_MUL = prove
 (`!(h:A->B) k l x y.
     field_extension(k,l) h /\
     radical_element(k,l) h x /\ radical_element(k,l) h y
     ==> radical_element(k,l) h (ring_mul l x y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RADICAL_ELEMENT_PAIR) THEN
  REWRITE_TAC[radical_element] THEN MESON_TAC[IN_SUBFIELD_MUL]);;

let RADICAL_ELEMENT_DIV = prove
 (`!(h:A->B) k l x y.
     field_extension(k,l) h /\
     radical_element(k,l) h x /\ radical_element(k,l) h y
     ==> radical_element(k,l) h (ring_div l x y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RADICAL_ELEMENT_PAIR) THEN
  REWRITE_TAC[radical_element; ring_div] THEN
  MESON_TAC[IN_SUBFIELD_MUL; IN_SUBFIELD_INV]);;

let RADICAL_ELEMENT_ROOT = prove
 (`!(h:A->B) k l x n.
     field_extension(k,l) h /\ x IN ring_carrier l /\ ~(n = 0) /\
     radical_element(k,l) h (ring_pow l x n)
     ==> radical_element(k,l) h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_element] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:B->bool`
     STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num`
    (X_CHOOSE_THEN `a:num->B` (X_CHOOSE_THEN `ma:num->num`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k)`;
                 `s:B->bool`; `p:num`; `1`; `a:num->B`; `(\i. x):num->B`;
                 `ma:num->num`; `(\i. n):num->num`]
    RADICAL_GENERATORS_APPEND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL; ARITH_RULE `i < 1 <=> i = 0`;
                 FORALL_UNWIND_THM2; LT; EMPTY_GSPEC; IMAGE_CLAUSES;
                 UNION_EMPTY; CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`; SING_GSPEC; IMAGE_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `c:num->B`
    (X_CHOOSE_THEN `mc:num->num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `ring_carrier(subfield_generated l
    (IMAGE (h:A->B) (ring_carrier k) UNION IMAGE c {i | i < q:num}))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED];
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_UNION; IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
     `ring_carrier(subfield_generated l
       (IMAGE (h:A->B) (ring_carrier k) UNION IMAGE c {i | i < q:num}))`]
    RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED]; DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[SUBSET_UNION; FIELD_EXTENSION_IMP_SUBSET];
    MAP_EVERY EXISTS_TAC [`q:num`; `c:num->B`; `mc:num->num`] THEN
    ASM_REWRITE_TAC[]]);;

let SUBFIELD_OF_RADICAL_ELEMENTS = prove
 (`!(h:A->B) k l.
     field_extension(k,l) h
     ==> {x | radical_element(k,l) h x} subfield_of l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[subring_of; IN_ELIM_THM; SUBSET] THEN
  ASM_SIMP_TAC[RADICAL_ELEMENT_ADD; RADICAL_ELEMENT_MUL;
               RADICAL_ELEMENT_NEG; RADICAL_ELEMENT_INV] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[RADICAL_ELEMENT_IN_CARRIER];
    SUBST1_TAC(SYM(MATCH_MP RING_HOMOMORPHISM_0
      (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`)));
    SUBST1_TAC(SYM(MATCH_MP RING_HOMOMORPHISM_1
      (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`)))] THEN
  MATCH_MP_TAC RADICAL_ELEMENT_BASE THEN ASM_REWRITE_TAC[RING_0; RING_1]);;

let RADICAL_ELEMENT_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (j:B->C) k l m x.
     field m /\ ring_homomorphism(l,m) j /\ radical_element(k,l) h x
     ==> radical_element(k,m) (j o h) (j x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_element] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `s:B->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (j:B->C) s` THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->C) o (h:A->B)`; `j:B->C`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `m:C ring`]
    RADICAL_EXTENSION_HOMOMORPHIC_IMAGE_GEN) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED; o_THM;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD; FUN_IN_IMAGE]);;

let RADICAL_EXTENSION_GENERATED_BY_RADICAL_ELEMENTS = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ FINITE s /\
        (!x. x IN s ==> radical_element(k,l) h x) /\
        subfield_generated l (IMAGE h (ring_carrier k) UNION s) = l
        ==> radical_extension(k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    RADICAL_ELEMENTS_COMMON_RADICAL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `subfield_generated l (t:B->bool) = l`
   (fun th -> SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_EQ; CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
    check (fun th -> is_eq(concl th) && rand(concl th) = `l:B ring`)) THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET o
    MATCH_MP RADICAL_IMP_FIELD_EXTENSION) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD]);;

let RADICAL_EXTENSION_EQ_RADICAL_ELEMENTS = prove
 (`!(h:A->B) k l.
     radical_extension(k,l) h <=>
     finite_extension(k,l) h /\
     !x. x IN ring_carrier l ==> radical_element(k,l) h x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[RADICAL_EXTENSION_IMP_FINITE] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN REWRITE_TAC[radical_element] THEN
    EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER; CARRIER_SUBFIELD_OF] THEN
    ASM_MESON_TAC[RADICAL_IMP_FIELD_EXTENSION; field_extension];
    STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_FINITELY_GENERATED_EXTENSION) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC RADICAL_EXTENSION_GENERATED_BY_RADICAL_ELEMENTS THEN
  EXISTS_TAC `b:B->bool` THEN ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The normal closure of a radical extension. For l radical over k and an    *)
(* embedding j of l into an algebraically closed field m, the normal closure *)
(* N of l inside m given by FINITE_EXTENSION_NORMAL_CLOSURE is radical over  *)
(* k: it is generated by finitely many elements of images e(l) of l under    *)
(* embeddings over k, and each e(l) is a radical subextension of N. Hence a  *)
(* radical element of an algebraically closed field lies in a subfield that  *)
(* is both radical and normal over k.                                        *)
(* ------------------------------------------------------------------------- *)

let RADICAL_EXTENSION_NORMAL_CLOSURE = prove
 (`!(h:A->B) (j:B->C) k l m.
     radical_extension(k,l) h /\
     algebraically_closed_field m /\ ring_homomorphism(l,m) j
     ==> ?s. s subfield_of m /\ IMAGE j (ring_carrier l) SUBSET s /\
             radical_extension(k,subfield_generated m s) (j o h) /\
             normal_extension(k,subfield_generated m s) (j o h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    FINITE_EXTENSION_NORMAL_CLOSURE) THEN
  ASM_SIMP_TAC[RADICAL_EXTENSION_IMP_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:C->bool` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "s") (CONJUNCTS_THEN2 (LABEL_TAC "e")
     STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  ABBREV_TAC
   `N = subfield_generated m
          (IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k) UNION s)` THEN
  EXISTS_TAC `ring_carrier N:C->bool` THEN
  SUBGOAL_THEN `subfield_generated m (ring_carrier N) = N:C ring`
  SUBST1_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "N" THEN ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED];
    USE_THEN "e" (MP_TAC o SPEC `j:B->C`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC RADICAL_EXTENSION_GENERATED_BY_RADICAL_ELEMENTS THEN
  EXISTS_TAC `s:C->bool` THEN
  ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:C` THEN DISCH_TAC THEN
    USE_THEN "s" (MP_TAC o C MATCH_MP (ASSUME `(x:C) IN s`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:B->C` STRIP_ASSUME_TAC) THEN
    USE_THEN "e" (MP_TAC o SPEC `e:B->C`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `(j:B->C) o (h:A->B)`; `e:B->C`;
                   `k:A ring`; `l:B ring`; `m:C ring`]
      RADICAL_EXTENSION_HOMOMORPHIC_IMAGE_GEN) THEN
    ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[radical_element] THEN
    EXISTS_TAC `IMAGE (e:B->C) (ring_carrier l)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "N" THEN REWRITE_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`m:C ring`; `IMAGE (e:B->C) (ring_carrier l)`;
                     `IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k) UNION s`]
        SUBFIELD_GENERATED_IDEMPOT_GEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    EXPAND_TAC "N" THEN REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT]]);;

let RADICAL_ELEMENT_NORMAL_CLOSURE = prove
 (`!(h:A->B) k l x.
     algebraically_closed_field l /\ radical_element(k,l) h x
     ==> ?s. s subfield_of l /\ x IN s /\
             radical_extension(k,subfield_generated l s) h /\
             normal_extension(k,subfield_generated l s) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical_element] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (t:B->bool)`; `l:B ring`]
    RADICAL_EXTENSION_NORMAL_CLOSURE) THEN
  ASM_SIMP_TAC[I_O_ID; IMAGE_I; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:B->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cyclotomic and Kummer extensions. An extension generated over the image   *)
(* of k by deg p distinct roots of a polynomial p over k is finite and       *)
(* Galois (p splits and is separable). Its Galois group is abelian when its  *)
(* elements commute on a set of generators, in particular when l is          *)
(* generated over the image of k by an element z of finite order (they send  *)
(* z to powers of z) or by an element a which they multiply by elements of   *)
(* the image of k. Adjoining a root of unity z gives an extension of the     *)
(* first kind for X^d - 1, d the order of z, whose roots are the d powers of *)
(* z: it is abelian Galois in any characteristic. Adjoining an n-th root a   *)
(* of an element of k, when k has n distinct n-th roots of unity, gives one  *)
(* for X^n - a^n (for X when a = 0), whose roots are the products of a with  *)
(* the roots of unity, so the elements of the Galois group multiply a by     *)
(* roots of unity: again abelian Galois. Both are also stated for an         *)
(* intermediate field s of l and the subfield generated by s and the new     *)
(* element, the form used in towers.                                         *)
(* ------------------------------------------------------------------------- *)

let GALOIS_EXTENSION_DISTINCT_ROOTS = prove
 (`!(h:A->B) k l p s.
        field_extension(k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k) /\
        s HAS_SIZE poly_deg k p /\
        (!x. x IN s
             ==> x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l) /\
        subfield_generated l (IMAGE h (ring_carrier k) UNION s) = l
        ==> finite_extension(k,l) h /\ galois_extension(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                 `s:B->bool`] POLY_SPLITS_OVER_DISTINCT_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GALOIS_EXTENSION_EQ_SEPARABLE_SPLITTING] THEN
  EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[splitting_extension]);;

let ABELIAN_GALOIS_GROUP_ON_GENERATORS = prove
 (`!(h:A->B) k l s.
        field l /\
        subfield_generated l (IMAGE h (ring_carrier k) UNION s) = l /\
        (!f g x. f IN group_carrier(galois_group(k,l) h) /\
                 g IN group_carrier(galois_group(k,l) h) /\ x IN s
                 ==> f(g x) = g(f x))
        ==> abelian_group(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[abelian_group; CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
  MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
  MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`] THEN
  ASM_SIMP_TAC[GALOIS_GROUP_COMPOSE; o_THM]);;

let ABELIAN_GALOIS_GROUP_ROOT_OF_UNITY = prove
 (`!(h:A->B) k l z.
        field l /\ z IN ring_carrier l /\ ~(ring_order l z = 0) /\
        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l
        ==> abelian_group(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ABELIAN_GALOIS_GROUP_ON_GENERATORS THEN
  EXISTS_TAC `{z:B}` THEN
  ASM_REWRITE_TAC[SET_RULE `(s:B->bool) UNION {a} = a INSERT s`; IN_SING] THEN
  MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`; `x:B`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(l,l) (f:B->B) /\ ring_homomorphism(l,l) (g:B->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `f:B->B`; `z:B`]
    RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
  MP_TAC(ISPECL [`l:B ring`; `g:B->B`; `z:B`]
    RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; ring_endomorphism] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`);
               MATCH_MP RING_HOMOMORPHISM_POW
                (ASSUME `ring_homomorphism(l,l) (g:B->B)`)] THEN
  ASM_SIMP_TAC[RING_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC);;

let ABELIAN_GALOIS_GROUP_RADICAL = prove
 (`!(h:A->B) k l a.
        field_extension(k,l) h /\ a IN ring_carrier l /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> ?c. c IN ring_carrier k /\ f a = ring_mul l (h c) a)
        ==> abelian_group(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MATCH_MP_TAC ABELIAN_GALOIS_GROUP_ON_GENERATORS THEN
  EXISTS_TAC `{a:B}` THEN
  ASM_REWRITE_TAC[SET_RULE `(s:B->bool) UNION {a} = a INSERT s`; IN_SING] THEN
  MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`; `x:B`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `f:B->B`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:B->B`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `v:A`]
    GALOIS_GROUP_FIXES) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `w:A`]
    GALOIS_GROUP_FIXES) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `v:A`]
    RING_HOMOMORPHISM_IN_CARRIER) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `w:A`]
    RING_HOMOMORPHISM_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(l,l) (f:B->B) /\ ring_homomorphism(l,l) (g:B->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`);
               MATCH_MP RING_HOMOMORPHISM_MUL
                (ASSUME `ring_homomorphism(l,l) (g:B->B)`)] THEN
  MATCH_MP_TAC(last(CONJUNCTS(ISPEC `l:B ring` RING_MUL_AC))) THEN
  ASM_SIMP_TAC[]);;

let CYCLOTOMIC_EXTENSION_ABELIAN = prove
 (`!(h:A->B) k l z n.
        field_extension(k,l) h /\ ~(n = 0) /\
        z IN ring_carrier l /\ ring_pow l z n = ring_1 l /\
        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l
        ==> finite_extension(k,l) h /\ galois_extension(k,l) h /\
            abelian_group(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `d = ring_order l (z:B)` THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `z:B`; `n:num`] RING_POW_EQ_1) THEN
    ASM_REWRITE_TAC[DIVIDES_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow l (z:B) d = ring_1 l` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC RING_POW_RING_ORDER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC ABELIAN_GALOIS_GROUP_ROOT_OF_UNITY THEN
    EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC
   `p = poly_sub k (poly_pow k (poly_var k one) d) (poly_const k (ring_1 k))
        :(1->num)->A` THEN
  ABBREV_TAC `s = {x:B | x IN ring_carrier l /\ ring_pow l x d = ring_1 l}` THEN
  SUBGOAL_THEN
   `p IN ring_carrier(poly_ring k (:1)) /\ poly_deg k p = d /\
    ~(p:(1->num)->A = poly_0 k)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    MP_TAC(ISPECL [`k:A ring`; `d:num`; `ring_1 k:A`]
      POLY_VAR_POW_SUB_CONST) THEN
    ASM_SIMP_TAC[RING_1; FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:B->bool) HAS_SIZE poly_deg k (p:(1->num)->A)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    MP_TAC(ISPECL [`l:B ring`; `z:B`; `d:num`] ROOTS_OF_UNITY_RING_ORDER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:B. x IN s
          ==> x IN ring_carrier l /\
              poly_eval l ((h:A->B) o p) x = ring_0 l`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN EXPAND_TAC "p" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[POLY_EVAL_VAR_POW_SUB_CONST; RING_1] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_SUB_REFL; RING_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s) = l`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
    TRANS_TAC SUBSET_TRANS
     `ring_carrier(subfield_generated l
        ((z:B) INSERT IMAGE (h:A->B) (ring_carrier k)))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
      MATCH_MP_TAC(SET_RULE
       `(z:B) IN s ==> z INSERT t SUBSET t UNION s`) THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                 `s:B->bool`] GALOIS_EXTENSION_DISTINCT_ROOTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]);;

let KUMMER_EXTENSION_ABELIAN = prove
 (`!(h:A->B) k l a n.
        field_extension(k,l) h /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n /\
        a IN ring_carrier l /\ ring_pow l a n IN IMAGE h (ring_carrier k) /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l
        ==> finite_extension(k,l) h /\ galois_extension(k,l) h /\
            abelian_group(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ring_pow l (a:B) n IN IMAGE (h:A->B) (ring_carrier k)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `!x:A. x IN ring_carrier k ==> (h:A->B) x IN ring_carrier l`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B)(ring_1 k) = ring_1 l /\ h(ring_0 k) = ring_0 l`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_1; RING_HOMOMORPHISM_0]; ALL_TAC] THEN
  ABBREV_TAC `u = {x:A | x IN ring_carrier k /\ ring_pow k x n = ring_1 k}` THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(u:A->bool) HAS_SIZE n` THEN EXPAND_TAC "u" THEN
    MATCH_ACCEPT_TAC ROOTS_OF_UNITY_HAS_SIZE_NONZERO;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p s. p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k) /\
          s HAS_SIZE poly_deg k p /\
          (!x. x IN s
               ==> x IN ring_carrier l /\
                   poly_eval l ((h:A->B) o p) x = ring_0 l) /\
          (a:B) IN s /\
          (!x. x IN s ==> ?v. v IN ring_carrier k /\ x = ring_mul l (h v) a)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `a = ring_0 (l:B ring)` THENL
     [EXISTS_TAC
       `poly_sub k (poly_pow k (poly_var k one) 1) (poly_const k (ring_0 k))
        :(1->num)->A` THEN
      EXISTS_TAC `{a:B}` THEN
      MP_TAC(ISPECL [`k:A ring`; `1`; `ring_0 k:A`] POLY_VAR_POW_SUB_CONST) THEN
      ASM_SIMP_TAC[FIELD_NONTRIVIAL; RING_0; ARITH_EQ] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2; HAS_SIZE; FINITE_SING;
                      CARD_SING] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[RING_0; POLY_EVAL_VAR_POW_SUB_CONST; RING_POW_1;
                     RING_SUB_REFL];
        EXISTS_TAC `ring_1 k:A` THEN ASM_SIMP_TAC[RING_1; RING_MUL_RZERO]];
      ALL_TAC] THEN
    EXISTS_TAC
     `poly_sub k (poly_pow k (poly_var k one) n) (poly_const k c)
      :(1->num)->A` THEN
    EXISTS_TAC `IMAGE (\x. ring_mul l ((h:A->B) x) a) u` THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `c:A`] POLY_VAR_POW_SUB_CONST) THEN
    ASM_SIMP_TAC[FIELD_NONTRIVIAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [ring_monomorphism]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_RCANCEL THEN
      MAP_EVERY EXISTS_TAC [`l:B ring`; `a:B`] THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
      EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[RING_MUL; POLY_EVAL_VAR_POW_SUB_CONST] THEN
      ASM_SIMP_TAC[RING_MUL_POW] THEN
      SUBGOAL_THEN `ring_pow l ((h:A->B) x) n = ring_1 l` SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
          (ASSUME `ring_homomorphism(k,l) (h:A->B)`))];
        ALL_TAC] THEN
      ASM_SIMP_TAC[RING_MUL_LID; RING_SUB_REFL];
      EXISTS_TAC `ring_1 k:A` THEN EXPAND_TAC "u" THEN
      ASM_SIMP_TAC[IN_ELIM_THM; RING_1; RING_POW_ONE; RING_MUL_LID];
      EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s) = l`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
    TRANS_TAC SUBSET_TRANS
     `ring_carrier(subfield_generated l
        ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k)))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
      MATCH_MP_TAC(SET_RULE
       `(a:B) IN s ==> a INSERT t SUBSET t UNION s`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                 `s:B->bool`] POLY_SPLITS_OVER_DISTINCT_ROOTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                 `s:B->bool`] GALOIS_EXTENSION_DISTINCT_ROOTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC ABELIAN_GALOIS_GROUP_RADICAL THEN
  EXISTS_TAC `a:B` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:B->B) a IN s` MP_TAC THENL
   [ALL_TAC;
    MESON_TAC[ASSUME `!x:B. x IN s
                        ==> ?v. v IN ring_carrier k /\
                                x = ring_mul l ((h:A->B) v) a`]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `s:B->bool`)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`;
                 `p:(1->num)->A`; `a:B`] GALOIS_GROUP_POLY_EVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `poly_eval l ((h:A->B) o p) a = ring_0 l` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
  MATCH_MP_TAC GALOIS_GROUP_RING_HOMOMORPHISM THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[]);;

let CYCLOTOMIC_EXTENSION_ABELIAN_INTERMEDIATE = prove
 (`!(l:B ring) s z n.
        field l /\ s subfield_of l /\ ~(n = 0) /\
        z IN ring_carrier l /\ ring_pow l z n = ring_1 l
        ==> finite_extension
             (subfield_generated l s,subfield_generated l (z INSERT s)) I /\
            galois_extension
             (subfield_generated l s,subfield_generated l (z INSERT s)) I /\
            abelian_group
             (galois_group
               (subfield_generated l s,subfield_generated l (z INSERT s)) I)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CYCLOTOMIC_EXTENSION_ABELIAN THEN
  MAP_EVERY EXISTS_TAC [`z:B`; `n:num`] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; IMAGE_I;
               SUBFIELD_GENERATED_IDEMPOT; RING_POW_SUBFIELD_GENERATED;
               el 2 (CONJUNCTS SUBFIELD_GENERATED);
               SUBFIELD_GENERATED_INC_GEN; IN_INSERT] THEN
  MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; IMAGE_I;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  SET_TAC[]);;

let KUMMER_EXTENSION_ABELIAN_INTERMEDIATE = prove
 (`!(l:B ring) s a n.
        field l /\ s subfield_of l /\
        {x | x IN s /\ ring_pow l x n = ring_1 l} HAS_SIZE n /\
        a IN ring_carrier l /\ ring_pow l a n IN s
        ==> finite_extension
             (subfield_generated l s,subfield_generated l (a INSERT s)) I /\
            galois_extension
             (subfield_generated l s,subfield_generated l (a INSERT s)) I /\
            abelian_group
             (galois_group
               (subfield_generated l s,subfield_generated l (a INSERT s)) I)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC KUMMER_EXTENSION_ABELIAN THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `n:num`] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; IMAGE_I;
               SUBFIELD_GENERATED_IDEMPOT; RING_POW_SUBFIELD_GENERATED;
               el 2 (CONJUNCTS SUBFIELD_GENERATED);
               SUBFIELD_GENERATED_INC_GEN; IN_INSERT] THEN
  MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; IMAGE_I;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  SET_TAC[]);;

(* If a^n lies in the image of k and k has n distinct n-th roots of unity,   *)
(* every element of the Galois group multiplies a by the image of an n-th    *)
(* root of unity of k. When the elements of the Galois group multiply a      *)
(* generator a in this way, f |-> f(a) / a embeds the Galois group in the    *)
(* finite group of n-th roots of unity of l, so the Galois group is cyclic   *)
(* of order dividing n. Hence Kummer extensions have cyclic Galois groups,   *)
(* also in the intermediate form used in towers.                             *)

let GALOIS_GROUP_KUMMER_ROOT_OF_UNITY = prove
 (`!(h:A->B) f k l a n.
        field_extension(k,l) h /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n /\
        a IN ring_carrier l /\ ring_pow l a n IN IMAGE h (ring_carrier k) /\
        f IN group_carrier(galois_group(k,l) h)
        ==> ?c. c IN ring_carrier k /\ ring_pow k c n = ring_1 k /\
                f a = ring_mul l (h c) a`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `u = {x:A | x IN ring_carrier k /\ ring_pow k x n = ring_1 k}` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(u:A->bool) HAS_SIZE n` THEN EXPAND_TAC "u" THEN
    MATCH_ACCEPT_TAC ROOTS_OF_UNITY_HAS_SIZE_NONZERO;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:B->B)(ring_0 l) = ring_0 l /\ (h:A->B)(ring_1 k) = ring_1 l`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1]; ALL_TAC] THEN
  ASM_CASES_TAC `a = ring_0(l:B ring)` THENL
   [EXISTS_TAC `ring_1 k:A` THEN
    ASM_REWRITE_TAC[RING_1; RING_POW_ONE] THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; RING_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->B) a IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->B)(ring_pow l a n) = ring_pow l a n` ASSUME_TAC THENL
   [UNDISCH_TAC `ring_pow l (a:B) n IN IMAGE (h:A->B) (ring_carrier k)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `c0:A`]
      GALOIS_GROUP_FIXES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b. b IN ring_carrier l /\ ring_pow l b n = ring_1 l /\
        (f:B->B) a = ring_mul l b a`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `ring_mul l ((f:B->B) a) (ring_inv l a)` THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; RING_MUL_POW; RING_POW_INV] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
        (ASSUME `ring_homomorphism(l,l) (f:B->B)`))] THEN
      MATCH_MP_TAC FIELD_MUL_RINV THEN
      ASM_SIMP_TAC[RING_POW; INTEGRAL_DOMAIN_POW_EQ_0;
                   FIELD_IMP_INTEGRAL_DOMAIN];
      ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV;
                   RING_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) u = {x | x IN ring_carrier l /\ ring_pow l x n = ring_1 l}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:B ring`; `n:num`] ROOTS_OF_UNITY_BOUND) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; LE_1] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (h:A->B) u HAS_SIZE n` MP_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[ring_monomorphism];
      REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (h:A->B) u SUBSET
      {x | x IN ring_carrier l /\ ring_pow l x n = ring_1 l}`
    ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
        (ASSUME `ring_homomorphism(k,l) (h:A->B)`))] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (h:A->B) u`;
                   `{x:B | x IN ring_carrier l /\ ring_pow l x n = ring_1 l}`]
      CARD_SUBSET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:B) IN IMAGE (h:A->B) u` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Powers of an element f of the Galois group that multiplies a by an        *)
(* element c fixed by f, or adds c to a: the n-th power multiplies a by c^n, *)
(* or adds n c.                                                              *)

let GALOIS_GROUP_POW_MUL_FIXED = prove
 (`!(h:A->B) f k l a c n.
        f IN group_carrier(galois_group(k,l) h) /\
        a IN ring_carrier l /\ c IN ring_carrier l /\
        f c = c /\ f a = ring_mul l c a
        ==> group_pow (galois_group(k,l) h) f n a =
            ring_mul l (ring_pow l c n) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_pow; CONJUNCT1(CONJUNCT2 GALOIS_GROUP);
                  CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP)); o_THM;
                  I_THM] THENL
   [ASM_SIMP_TAC[ring_pow; RING_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`); RING_POW] THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
  ASM_SIMP_TAC[ring_pow; RING_POW; RING_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
  ASM_SIMP_TAC[RING_POW]);;

let GALOIS_GROUP_POW_ADD_FIXED = prove
 (`!(h:A->B) f k l a c n.
        f IN group_carrier(galois_group(k,l) h) /\
        a IN ring_carrier l /\ c IN ring_carrier l /\
        f c = c /\ f a = ring_add l a c
        ==> group_pow (galois_group(k,l) h) f n a =
            ring_add l a (ring_mul l (ring_of_num l n) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_pow; CONJUNCT1(CONJUNCT2 GALOIS_GROUP);
                  CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP)); o_THM;
                  I_THM] THENL
   [ASM_SIMP_TAC[RING_OF_NUM_0; RING_MUL_LZERO; RING_ADD_RZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`);
               MATCH_MP RING_HOMOMORPHISM_MUL
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`);
               MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM
                (ASSUME `ring_homomorphism(l,l) (f:B->B)`);
               RING_OF_NUM; RING_MUL] THEN
  REWRITE_TAC[ADD1; RING_OF_NUM_ADD; RING_OF_NUM_1] THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_OF_NUM; RING_1; RING_MUL_LID] THEN
  ASM_SIMP_TAC[RING_ADD_AC; RING_MUL; RING_OF_NUM]);;

let CYCLIC_GALOIS_GROUP_RADICAL = prove
 (`!(h:A->B) k l a n.
        field_extension(k,l) h /\ a IN ring_carrier l /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
        ~(n = 0) /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> ?c. c IN ring_carrier k /\ ring_pow k c n = ring_1 k /\
                     f a = ring_mul l (h c) a)
        ==> cyclic_group(galois_group(k,l) h) /\
            CARD(group_carrier(galois_group(k,l) h)) divides n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "roots"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `integral_domain(l:B ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN ring_carrier k ==> (h:A->B) x IN ring_carrier l`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `(I:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h` GROUP_ID) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)];
    ALL_TAC] THEN
  ASM_CASES_TAC `a = ring_0(l:B ring)` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `a = ring_0(l:B ring)`)) THEN
    SUBGOAL_THEN `trivial_group(galois_group(k:A ring,l:B ring) h)`
    ASSUME_TAC THENL
     [REWRITE_TAC[trivial_group; CONJUNCT1(CONJUNCT2 GALOIS_GROUP)] THEN
      REWRITE_TAC[EXTENSION; IN_SING] THEN X_GEN_TAC `f:B->B` THEN
      EQ_TAC THENL
       [DISCH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
      MAP_EVERY EXISTS_TAC
       [`h:A->B`; `k:A ring`; `l:B ring`; `{ring_0 l:B}`] THEN
      ASM_REWRITE_TAC[SET_RULE `(s:B->bool) UNION {a} = a INSERT s`;
                      IN_SING; FORALL_UNWIND_THM2; I_THM] THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
      MATCH_MP_TAC GALOIS_GROUP_RING_HOMOMORPHISM THEN
      MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[TRIVIAL_IMP_CYCLIC_GROUP] THEN
      FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [trivial_group]) THEN
      REWRITE_TAC[CARD_SING; DIVIDES_1]];
    ALL_TAC] THEN
  ABBREV_TAC
   `S = {x | (?c. c IN ring_carrier k /\ ring_pow k c n = ring_1 k /\
                  x = (h:A->B) c) /\
             ?f. f IN group_carrier(galois_group(k,l) h) /\
                 f a = ring_mul l x a}` THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> x IN ring_carrier l /\ ring_pow l x n = ring_1 l /\
            !f. f IN group_carrier(galois_group(k,l) (h:A->B)) ==> f x = x`
  (LABEL_TAC "Sprop") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `c:A` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))
     (K ALL_TAC)) THEN
    ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
      (ASSUME `ring_homomorphism(k,l) (h:A->B)`))] THEN
    REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1
      (ASSUME `ring_homomorphism(k,l) (h:A->B)`)] THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `c:A`]
      GALOIS_GROUP_FIXES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_multsys l (S:B->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[ring_multsys] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SUBSET];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [EXISTS_TAC `ring_1 k:A` THEN
        REWRITE_TAC[RING_1; RING_POW_ONE; MATCH_MP RING_HOMOMORPHISM_1
          (ASSUME `ring_homomorphism(k,l) (h:A->B)`)];
        EXISTS_TAC `I:B->B` THEN ASM_SIMP_TAC[I_THM; RING_MUL_LID]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC)
                      (X_CHOOSE_THEN `f:B->B` STRIP_ASSUME_TAC))
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC)
                      (X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC))) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `ring_mul k c d:A` THEN
      ASM_SIMP_TAC[RING_MUL; RING_MUL_POW; RING_MUL_LID; RING_1] THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
        (ASSUME `ring_homomorphism(k,l) (h:A->B)`)];
      EXISTS_TAC `(f:B->B) o (g:B->B)` THEN
      ASM_SIMP_TAC[GALOIS_GROUP_COMPOSE] THEN ASM_REWRITE_TAC[o_THM] THEN
      ASSUME_TAC(MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
       (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
      MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `d:A`]
        GALOIS_GROUP_FIXES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
        (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
      ASM_SIMP_TAC[RING_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `S:B->bool`] FINITE_RING_MULTSYS_CYCLIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:B | x IN ring_carrier l /\ ring_pow l x n = ring_1 l}` THEN
      ASM_SIMP_TAC[ROOTS_OF_UNITY_BOUND; LE_1] THEN
      ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
      DISCH_THEN(fun th -> USE_THEN "Sprop" (MP_TAC o C MATCH_MP th)) THEN
      ASM_REWRITE_TAC[RING_POW_ZERO] THEN
      ASM_MESON_TAC[FIELD_NONTRIVIAL]];
    DISCH_THEN(X_CHOOSE_THEN `w:B`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen")))] THEN
  SUBGOAL_THEN
   `?f0. f0 IN group_carrier(galois_group(k,l) (h:A->B)) /\
         f0 a = ring_mul l w a`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:B) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. group_pow (galois_group(k,l) (h:A->B)) f0 m IN
        group_carrier(galois_group(k,l) h) /\
        group_pow (galois_group(k,l) h) f0 m a =
        ring_mul l (ring_pow l w m) a`
  (LABEL_TAC "pow") THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC GROUP_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GALOIS_GROUP_POW_MUL_FIXED THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "Sprop" (MP_TAC o C MATCH_MP (ASSUME `(w:B) IN S`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
          g IN group_carrier(galois_group(k,l) h) /\ f a = g a
          ==> f = g`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `{a:B}`] THEN
    ASM_REWRITE_TAC[SET_RULE `(s:B->bool) UNION {a} = a INSERT s`; IN_SING;
                    FORALL_UNWIND_THM2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> ?m. f = group_pow (galois_group(k,l) h) f0 m`
  (LABEL_TAC "every") THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    USE_THEN "roots" (MP_TAC o C MATCH_MP
     (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:A->B) c IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `c:A` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "gen" (MP_TAC o C MATCH_MP (ASSUME `(h:A->B) c IN S`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subgroup_generated (galois_group(k,l) (h:A->B)) {f0} =
    galois_group(k,l) h`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBGROUP_GENERATED_EQ] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    USE_THEN "every" (X_CHOOSE_THEN `m:num` SUBST1_TAC o C MATCH_MP
      (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
    MATCH_MP_TAC IN_SUBGROUP_POW THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_pow (galois_group(k,l) (h:A->B)) f0 n =
    group_id(galois_group(k,l) h)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[I_THM] THEN
    USE_THEN "Sprop" (MP_TAC o C MATCH_MP (ASSUME `(w:B) IN S`)) THEN
    SIMP_TAC[RING_MUL_LID; ASSUME `(a:B) IN ring_carrier l`];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cyclic_group] THEN EXISTS_TAC `f0:B->B` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f0:B->B`]
    CARD_CYCLIC_SUBGROUP_ORDER) THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f0:B->B`]
    FINITE_CYCLIC_SUBGROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f0:B->B`; `n:num`]
    GROUP_POW_EQ_ID) THEN
  ASM_REWRITE_TAC[]);;

let KUMMER_EXTENSION_CYCLIC = prove
 (`!(h:A->B) k l a n.
        field_extension(k,l) h /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n /\
        a IN ring_carrier l /\ ring_pow l a n IN IMAGE h (ring_carrier k) /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l
        ==> cyclic_group(galois_group(k,l) h) /\
            CARD(group_carrier(galois_group(k,l) h)) divides n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CYCLIC_GALOIS_GROUP_RADICAL THEN EXISTS_TAC `a:B` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ROOTS_OF_UNITY_HAS_SIZE_NONZERO];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_KUMMER_ROOT_OF_UNITY THEN
    ASM_REWRITE_TAC[]]);;

let KUMMER_EXTENSION_CYCLIC_INTERMEDIATE = prove
 (`!(l:B ring) s a n.
        field l /\ s subfield_of l /\
        {x | x IN s /\ ring_pow l x n = ring_1 l} HAS_SIZE n /\
        a IN ring_carrier l /\ ring_pow l a n IN s
        ==> cyclic_group
             (galois_group
               (subfield_generated l s,subfield_generated l (a INSERT s)) I) /\
            CARD(group_carrier
                  (galois_group
                    (subfield_generated l s,subfield_generated l (a INSERT s))
                    I)) divides n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC KUMMER_EXTENSION_CYCLIC THEN
  EXISTS_TAC `a:B` THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; IMAGE_I;
               SUBFIELD_GENERATED_IDEMPOT; RING_POW_SUBFIELD_GENERATED;
               el 2 (CONJUNCTS SUBFIELD_GENERATED);
               SUBFIELD_GENERATED_INC_GEN; IN_INSERT] THEN
  MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; IMAGE_I;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  SET_TAC[]);;

(* Kummer theory: if k has n distinct n-th roots of unity, every cyclic      *)
(* Galois extension of degree n is generated by an n-th root of an element   *)
(* of k. For a generator g of the Galois group and a root of unity z of      *)
(* order n in k, the norm of the inverse of h(z) is 1, so by Hilbert 90 it   *)
(* is y / g(y) for some nonzero y; then g(y) = h(z) y and g^j(y) = h(z)^j y, *)
(* so only the identity in the Galois group fixes y, which therefore         *)
(* generates l, and y^n is fixed by g, so it lies in the image of k.         *)
(* Together with KUMMER_EXTENSION_CYCLIC: the extensions generated by an     *)
(* n-th root of an element of k are exactly the finite cyclic Galois         *)
(* extensions of degree dividing n.                                          *)

let KUMMER_CYCLIC_EXTENSION = prove
 (`!(h:A->B) k l n.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        cyclic_group(galois_group(k,l) h) /\
        CARD(group_carrier(galois_group(k,l) h)) = n /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n
        ==> ?a. a IN ring_carrier l /\
                ring_pow l a n IN IMAGE h (ring_carrier k) /\
                subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP CARD_GALOIS_GROUP_LE) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ROOTS_OF_UNITY_HAS_SIZE_NONZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`] ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(h:A->B) z IN ring_carrier l /\ ring_order l (h z) = n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[RING_ORDER_MONOMORPHIC_IMAGE]];
    ALL_TAC] THEN
  ABBREV_TAC `u = (h:A->B) z` THEN
  SUBGOAL_THEN `ring_pow l (u:B) n = ring_1 l /\ ~(u = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`; `u:B`] RING_POW_RING_ORDER) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(n = 0)` THEN
      UNDISCH_TAC `ring_order l (u:B) = n` THEN
      ASM_SIMP_TAC[RING_ORDER_0; TRIVIAL_RING_10; FIELD_NONTRIVIAL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [cyclic_group]) THEN
  ASSUME_TAC(MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
   (ASSUME `(g:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  ASSUME_TAC(MATCH_MP GALOIS_GROUP_PERMUTES
   (ASSUME `(g:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `g:B->B`;
                 `ring_inv l u:B`] HILBERT_90_CYCLIC) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_INV] THEN
    TRANS_TAC EQ_TRANS
     `ring_product l (group_carrier(galois_group(k,l) (h:A->B)))
                     (\f. ring_inv l u)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `f:B->B` THEN
      DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `z:A`]
        GALOIS_GROUP_FIXES) THEN
      MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`]
        FIELD_HOMOMORPHISM_INV) THEN
      ASM_SIMP_TAC[MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
       (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)];
      ASM_SIMP_TAC[RING_PRODUCT_CONST; RING_INV; RING_POW_INV; RING_INV_1]];
    REWRITE_TAC[ring_div] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(g:B->B) y IN ring_carrier l /\ ~((g:B->B) y = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
      SUBST1_TAC(SYM(MATCH_MP RING_HOMOMORPHISM_0
       (ASSUME `ring_homomorphism(l,l) (g:B->B)`))) THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:B->B) y = ring_mul l u y` ASSUME_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `!r u v w x y:A.
        u IN ring_carrier r /\ v IN ring_carrier r /\ w IN ring_carrier r /\
        x IN ring_carrier r /\ y IN ring_carrier r /\
        ring_mul r u v = ring_1 r /\ ring_mul r w x = ring_1 r /\
        v = ring_mul r y w
        ==> x = ring_mul r u y`) THEN
    MAP_EVERY EXISTS_TAC [`ring_inv l u:B`; `ring_inv l ((g:B->B) y)`] THEN
    ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV; FIELD_MUL_LINV];
    ALL_TAC] THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{g:B->B}`]
      FIXED_FIELD_GALOIS_GROUP_GENERATORS) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_FIXED_FIELD; IN_SING; FORALL_UNWIND_THM2] THEN
    ASM_SIMP_TAC[RING_POW; MATCH_MP RING_HOMOMORPHISM_POW
      (ASSUME `ring_homomorphism(l,l) (g:B->B)`)] THEN
    ASM_SIMP_TAC[RING_MUL_POW; RING_POW; RING_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `y:B`]
    GALOIS_EXTENSION_SIMPLE_CYCLIC_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC `j:num` THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `z:A`]
    GALOIS_GROUP_FIXES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `y:B`; `u:B`;
                 `j:num`] GALOIS_GROUP_POW_MUL_FIXED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_SELF; FIELD_IMP_INTEGRAL_DOMAIN;
               RING_POW; RING_POW_EQ_1]);;

let KUMMER_CYCLIC_EXTENSION_EQ = prove
 (`!(h:A->B) k l n.
        field_extension(k,l) h /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n
        ==> (finite_extension(k,l) h /\ galois_extension(k,l) h /\
             cyclic_group(galois_group(k,l) h) /\
             CARD(group_carrier(galois_group(k,l) h)) divides n <=>
             ?a. a IN ring_carrier l /\
                 ring_pow l a n IN IMAGE h (ring_carrier k) /\
                 subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC;
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `n:num`]
      KUMMER_EXTENSION_ABELIAN) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `n:num`]
      KUMMER_EXTENSION_CYCLIC) THEN
    ASM_SIMP_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `CARD(group_carrier(galois_group(k,l) (h:A->B)))`]
    KUMMER_CYCLIC_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ROOTS_OF_UNITY_HAS_SIZE_DIVISOR THEN
    EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `CARD(group_carrier(galois_group(k,l) (h:A->B))) divides n` THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  ASM_SIMP_TAC[GSYM RING_POW_POW] THEN
  UNDISCH_TAC
   `ring_pow l (a:B) (CARD(group_carrier(galois_group(k,l) (h:A->B)))) IN
    IMAGE h (ring_carrier k)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_pow k (c:A) m` THEN ASM_SIMP_TAC[RING_POW] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_POW o
    MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Artin-Schreier extensions. In characteristic p, adjoining a root a of     *)
(* X^p - X - c with c in k gives a finite Galois extension, since the roots  *)
(* of X^p - X - c are the p distinct elements a + j, j in the prime field.   *)
(* The Galois group moves a by elements of the prime field, so               *)
(* f |-> f(a) - a embeds it in the prime field, and an element that moves a  *)
(* has order p: the Galois group is cyclic of order 1 or p, and of order p   *)
(* when a is not in the image of k. Conversely a cyclic Galois extension of  *)
(* degree p is generated by such a root: the trace of -1 is -p = 0, so by    *)
(* the additive form of Hilbert 90 there is y with g(y) = y + 1 for a        *)
(* generator g, and then y^p - y is fixed by g. Hence, as in the Kummer      *)
(* case, the extensions generated by a root of some X^p - X - c are exactly  *)
(* the finite cyclic Galois extensions of degree dividing p.                 *)
(* ------------------------------------------------------------------------- *)

let GALOIS_EXTENSION_ARTIN_SCHREIER = prove
 (`!(h:A->B) k l a p.
        field_extension(k,l) h /\ prime p /\ ring_char k = p /\
        a IN ring_carrier l /\
        ring_sub l (ring_pow l a p) a IN IMAGE h (ring_carrier k) /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l
        ==> finite_extension(k,l) h /\ galois_extension(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `ring_char(l:B ring) = p` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  UNDISCH_TAC
   `ring_sub l (ring_pow l a p) a IN IMAGE (h:A->B) (ring_carrier k)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` (STRIP_ASSUME_TAC o GSYM)) THEN
  ABBREV_TAC
   `q = poly_sub k (poly_sub k (poly_pow k (poly_var k one) p)
                               (poly_var k one))
                   (poly_const k c):(1->num)->A` THEN
  SUBGOAL_THEN
   `(q:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\ poly_deg k q = p`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `p:num`] POLY_VAR_POW_SUB_VAR) THEN
    ASM_SIMP_TAC[FIELD_NONTRIVIAL; PRIME_GE_2] THEN
    REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN STRIP_TAC THEN
    EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_CONST;
                 POLY_DEG_SUB_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q:(1->num)->A = poly_0 k)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `poly_deg (k:A ring):((1->num)->A)->num`) THEN
    ASM_REWRITE_TAC[POLY_DEG_0] THEN ASM_SIMP_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier l
        ==> poly_eval l ((h:A->B) o q) x =
            ring_sub l (ring_sub l (ring_pow l x p) x) (h c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[poly_eval] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[GSYM(MATCH_MP POLY_EXTEND_EVALUATE th)]) THEN
    ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_VAR;
                 POLY_EXTEND_CONST; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  ABBREV_TAC
   `s = IMAGE (\j. ring_add l (a:B) (ring_of_num l j)) {j | j < p}` THEN
  SUBGOAL_THEN `(s:B->bool) HAS_SIZE poly_deg k (q:(1->num)->A)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    ASM_SIMP_TAC[RING_ADD_LCANCEL; RING_OF_NUM; RING_OF_NUM_EQ] THEN
    MESON_TAC[CONG_IMP_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:B. x IN s
          ==> x IN ring_carrier l /\
              poly_eval l ((h:A->B) o q) x = ring_0 l`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_ADD; RING_OF_NUM] THEN
    SUBGOAL_THEN
     `ring_pow l (ring_of_num l j) p = ring_of_num (l:B ring) j`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `l:B ring` FROBENIUS_FIXED) THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
      DISCH_THEN(MP_TAC o SPEC `ring_of_num l j:B` o
        REWRITE_RULE[EXTENSION]) THEN
      REWRITE_TAC[IN_ELIM_THM; RING_OF_NUM] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `&j:int` THEN
      REWRITE_TAC[IN_UNIV; RING_OF_INT_OF_NUM];
      ALL_TAC] THEN
    MP_TAC(ISPEC `l:B ring` RING_ENDOMORPHISM_FROBENIUS) THEN
    ASM_REWRITE_TAC[ring_endomorphism] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:B`; `ring_of_num l j:B`] o
      MATCH_MP RING_HOMOMORPHISM_ADD) THEN
    ASM_SIMP_TAC[RING_OF_NUM] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(RING_RULE
     `!r a b q:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  q IN ring_carrier r
                  ==> ring_sub r (ring_sub r (ring_add r q b) (ring_add r a b))
                                 (ring_sub r q a) = ring_0 r`) THEN
    ASM_SIMP_TAC[RING_POW; RING_OF_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s) = l`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
    TRANS_TAC SUBSET_TRANS
     `ring_carrier(subfield_generated l
        ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k)))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
      MATCH_MP_TAC(SET_RULE
       `(a:B) IN s ==> a INSERT t SUBSET t UNION s`) THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `0` THEN
      ASM_SIMP_TAC[RING_OF_NUM_0; RING_ADD_RZERO; PRIME_IMP_NZ; LE_1]];
    ALL_TAC] THEN
  MATCH_MP_TAC GALOIS_EXTENSION_DISTINCT_ROOTS THEN
  MAP_EVERY EXISTS_TAC [`q:(1->num)->A`; `s:B->bool`] THEN
  ASM_REWRITE_TAC[]);;

let GALOIS_GROUP_ARTIN_SCHREIER = prove
 (`!(h:A->B) f k l a p.
        field_extension(k,l) h /\ prime p /\ ring_char k = p /\
        a IN ring_carrier l /\
        ring_sub l (ring_pow l a p) a IN IMAGE h (ring_carrier k) /\
        f IN group_carrier(galois_group(k,l) h)
        ==> ?n. f a = ring_add l a (ring_of_int l n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `ring_char(l:B ring) = p` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
   (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  SUBGOAL_THEN `(f:B->B) a IN ring_carrier l` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub l (ring_pow l ((f:B->B) a) p) (f a) =
    ring_sub l (ring_pow l a p) a`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_POW; GSYM(MATCH_MP RING_HOMOMORPHISM_POW
      (ASSUME `ring_homomorphism(l,l) (f:B->B)`))] THEN
    ASM_SIMP_TAC[RING_POW; GSYM(MATCH_MP RING_HOMOMORPHISM_SUB
      (ASSUME `ring_homomorphism(l,l) (f:B->B)`))] THEN
    UNDISCH_TAC
     `ring_sub l (ring_pow l a p) a IN IMAGE (h:A->B) (ring_carrier k)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GALOIS_GROUP_FIXES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub l ((f:B->B) a) a IN {ring_of_int l n | n IN (:int)}`
  MP_TAC THENL
   [MP_TAC(ISPEC `l:B ring` FROBENIUS_FIXED) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_SUB] THEN
    MP_TAC(ISPEC `l:B ring` RING_ENDOMORPHISM_FROBENIUS) THEN
    ASM_REWRITE_TAC[ring_endomorphism] THEN
    DISCH_THEN(MP_TAC o SPECL [`(f:B->B) a`; `a:B`] o
      MATCH_MP RING_HOMOMORPHISM_SUB) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(RING_RULE
     `!r x y u v:A. x IN ring_carrier r /\ y IN ring_carrier r /\
                    u IN ring_carrier r /\ v IN ring_carrier r /\
                    ring_sub r u x = ring_sub r v y
                    ==> ring_sub r u v = ring_sub r x y`) THEN
    ASM_SIMP_TAC[RING_POW];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `n:int` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(RING_RULE
     `!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
                ==> x = ring_add r y (ring_sub r x y)`) THEN
    ASM_REWRITE_TAC[]]);;

let CYCLIC_GALOIS_GROUP_TRANSLATION = prove
 (`!(h:A->B) k l a p.
        field_extension(k,l) h /\ prime p /\ ring_char k = p /\
        a IN ring_carrier l /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> ?n. f a = ring_add l a (ring_of_int l n))
        ==> cyclic_group(galois_group(k,l) h) /\
            CARD(group_carrier(galois_group(k,l) h)) divides p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "trans")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `ring_char(l:B ring) = p` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `(I:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h` GROUP_ID) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
          g IN group_carrier(galois_group(k,l) h) /\
          ring_sub l (f a) a = ring_sub l (g a) a
          ==> f = g`
  (LABEL_TAC "inj") THENL
   [MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `{a:B}`] THEN
    ASM_REWRITE_TAC[SET_RULE `(s:B->bool) UNION {a} = a INSERT s`; IN_SING;
                    FORALL_UNWIND_THM2] THEN
    MATCH_MP_TAC(RING_RULE
     `!r x y z:A. x IN ring_carrier r /\ y IN ring_carrier r /\
                  z IN ring_carrier r /\ ring_sub r x z = ring_sub r y z
                  ==> x = y`) THEN
    MAP_EVERY EXISTS_TAC [`l:B ring`; `a:B`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "trans" (fun th ->
      X_CHOOSE_THEN `m:int` SUBST1_TAC (MATCH_MP th (ASSUME
        `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
      X_CHOOSE_THEN `n:int` SUBST1_TAC (MATCH_MP th (ASSUME
        `(g:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`))) THEN
    ASM_SIMP_TAC[RING_ADD; RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\f. ring_sub l ((f:B->B) a) a)
          (group_carrier(galois_group(k,l) (h:A->B))) SUBSET
    {ring_of_int l n | n IN (:int)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    USE_THEN "trans" (X_CHOOSE_THEN `n:int` SUBST1_TAC o C MATCH_MP
     (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
    EXISTS_TAC `n:int` THEN
    MATCH_MP_TAC(RING_RULE
     `!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
                ==> ring_sub r (ring_add r x y) x = y`) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` HAS_SIZE_PRIME_SUBRING) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ; HAS_SIZE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE(group_carrier(galois_group(k,l) (h:A->B))) /\
    CARD(group_carrier(galois_group(k,l) h)) <= p`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\f. ring_sub l ((f:B->B) a) a`;
                   `group_carrier(galois_group(k,l) (h:A->B))`]
      CARD_IMAGE_INJ) THEN
    MP_TAC(ISPECL [`\f. ring_sub l ((f:B->B) a) a`;
                   `group_carrier(galois_group(k,l) (h:A->B))`]
      FINITE_IMAGE_INJ_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`IMAGE (\f. ring_sub l ((f:B->B) a) a)
             (group_carrier(galois_group(k,l) (h:A->B)))`;
      `{ring_of_int l n | n IN (:int)}:B->bool`] CARD_SUBSET) THEN
    MP_TAC(ISPECL
     [`IMAGE (\f. ring_sub l ((f:B->B) a) a)
             (group_carrier(galois_group(k,l) (h:A->B)))`;
      `{ring_of_int l n | n IN (:int)}:B->bool`] FINITE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(group_carrier(galois_group(k,l) (h:A->B))) = 1 \/
    CARD(group_carrier(galois_group(k,l) h)) = p`
  MP_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[DIVIDES_1; DIVIDES_REFL] THEN
    MATCH_MP_TAC PRIME_ORDER_IMP_CYCLIC_GROUP THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B)) ==> f = I`
  THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `group_carrier(galois_group(k,l) (h:A->B)) = {I}`
    SUBST1_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[CARD_SING]];
    DISJ2_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f0:B->B` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  USE_THEN "trans" (X_CHOOSE_TAC `n0:int` o C MATCH_MP
   (ASSUME `(f0:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `f0:B->B`; `k:A ring`; `l:B ring`; `a:B`;
                 `ring_of_int l n0:B`; `p:num`] GALOIS_GROUP_POW_ADD_FIXED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INT; MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
     (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
       (ASSUME `(f0:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`))];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_of_num l p = ring_0(l:B ring)` SUBST1_TAC THENL
   [UNDISCH_TAC `ring_char(l:B ring) = p` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_OF_NUM_CHAR];
    ALL_TAC] THEN
  SIMP_TAC[RING_MUL_LZERO; RING_OF_INT; RING_ADD_RZERO;
           ASSUME `(a:B) IN ring_carrier l`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `group_element_order (galois_group(k,l) (h:A->B)) f0 = p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f0:B->B`; `p:num`]
      GROUP_ELEMENT_ORDER_UNIQUE_PRIME) THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 GALOIS_GROUP)] THEN
    DISCH_THEN SUBST1_TAC THEN
    REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[GROUP_POW; I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(group_carrier(galois_group(k,l) (h:A->B))) = 0)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`galois_group(k:A ring,l:B ring) h`; `f0:B->B`]
    GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let ARTIN_SCHREIER_CYCLIC = prove
 (`!(h:A->B) k l a p.
        field_extension(k,l) h /\ prime p /\ ring_char k = p /\
        a IN ring_carrier l /\ ~(a IN IMAGE h (ring_carrier k)) /\
        ring_sub l (ring_pow l a p) a IN IMAGE h (ring_carrier k) /\
        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l
        ==> finite_extension(k,l) h /\ galois_extension(k,l) h /\
            cyclic_group(galois_group(k,l) h) /\
            CARD(group_carrier(galois_group(k,l) h)) = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `p:num`]
    GALOIS_EXTENSION_ARTIN_SCHREIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CARD_GALOIS_GROUP_LE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `p:num`]
    CYCLIC_GALOIS_GROUP_TRANSLATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `a:B`; `p:num`]
      GALOIS_GROUP_ARTIN_SCHREIER) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `~(CARD(group_carrier(galois_group(k,l) (h:A->B))) = 1)`
  MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h`
      TRIVIAL_GROUP_HAS_SIZE_1) THEN
    ASM_REWRITE_TAC[trivial_group; CONJUNCT1(CONJUNCT2 GALOIS_GROUP);
                    HAS_SIZE] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~((a:B) IN IMAGE (h:A->B) (ring_carrier k))` THEN
    REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FIXED_FIELD_GALOIS_GROUP) THEN
    ASM_REWRITE_TAC[IN_FIXED_FIELD; IN_SING; FORALL_UNWIND_THM2; I_THM];
    UNDISCH_TAC
     `CARD(group_carrier(galois_group(k,l) (h:A->B))) divides p` THEN
    UNDISCH_TAC `prime p` THEN REWRITE_TAC[prime] THEN MESON_TAC[]]);;

let ARTIN_SCHREIER_EXTENSION = prove
 (`!(h:A->B) k l p.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        prime p /\ ring_char k = p /\
        CARD(group_carrier(galois_group(k,l) h)) = p
        ==> ?a. a IN ring_carrier l /\
                ring_sub l (ring_pow l a p) a IN IMAGE h (ring_carrier k) /\
                subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP CARD_GALOIS_GROUP_LE) THEN
  SUBGOAL_THEN `ring_char(l:B ring) = p` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h`
    PRIME_ORDER_IMP_CYCLIC_GROUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->B` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [cyclic_group]) THEN
  ASSUME_TAC(MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
   (ASSUME `(g:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `g:B->B`;
                 `ring_neg l (ring_1 l):B`] HILBERT_90_ADDITIVE_CYCLIC) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_NEG; RING_1] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l (group_carrier(galois_group(k,l) (h:A->B)))
                 (\f. ring_neg l (ring_1 l))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B` THEN
      DISCH_THEN(MP_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
      DISCH_THEN(fun th -> SIMP_TAC[RING_1; MATCH_MP RING_HOMOMORPHISM_NEG th;
                                    MATCH_MP RING_HOMOMORPHISM_1 th]);
      ASM_SIMP_TAC[RING_SUM_CONST; RING_NEG; RING_1] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `ring_char(l:B ring)`)) THEN
      SIMP_TAC[RING_OF_NUM_CHAR; RING_MUL_LZERO; RING_NEG; RING_1]];
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(g:B->B) y = ring_add l y (ring_1 l)` ASSUME_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r /\
                ring_neg r (ring_1 r) = ring_sub r y x
                ==> x = ring_add r y (ring_1 r)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{g:B->B}`]
      FIXED_FIELD_GALOIS_GROUP_GENERATORS) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_FIXED_FIELD; IN_SING; FORALL_UNWIND_THM2] THEN
    ASM_SIMP_TAC[RING_POW; RING_SUB] THEN
    ASM_SIMP_TAC[RING_POW; MATCH_MP RING_HOMOMORPHISM_SUB
      (ASSUME `ring_homomorphism(l,l) (g:B->B)`)] THEN
    ASM_SIMP_TAC[RING_POW; MATCH_MP RING_HOMOMORPHISM_POW
      (ASSUME `ring_homomorphism(l,l) (g:B->B)`)] THEN
    MP_TAC(ISPEC `l:B ring` RING_ENDOMORPHISM_FROBENIUS) THEN
    ASM_REWRITE_TAC[ring_endomorphism] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:B`; `ring_1 l:B`] o
      MATCH_MP RING_HOMOMORPHISM_ADD) THEN
    ASM_SIMP_TAC[RING_1; RING_POW_ONE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(RING_RULE
     `!r y q:A. y IN ring_carrier r /\ q IN ring_carrier r
                ==> ring_sub r (ring_add r q (ring_1 r))
                               (ring_add r y (ring_1 r)) =
                    ring_sub r q y`) THEN
    ASM_SIMP_TAC[RING_POW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `y:B`]
    GALOIS_EXTENSION_SIMPLE_CYCLIC_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC `j:num` THEN
  MP_TAC(ISPECL [`h:A->B`; `g:B->B`; `k:A ring`; `l:B ring`; `y:B`;
                 `ring_1 l:B`; `j:num`] GALOIS_GROUP_POW_ADD_FIXED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_1; MATCH_MP RING_HOMOMORPHISM_1
      (ASSUME `ring_homomorphism(l,l) (g:B->B)`)];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_OF_NUM] THEN
  SUBGOAL_THEN
   `ring_add l (y:B) (ring_of_num l j) = y <=> ring_of_num l j = ring_0 l`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `!r y c:A. y IN ring_carrier r /\ c IN ring_carrier r
                ==> (ring_add r y c = y <=> c = ring_0 r)`) THEN
    ASM_REWRITE_TAC[RING_OF_NUM];
    UNDISCH_TAC `ring_char(l:B ring) = p` THEN
    REWRITE_TAC[RING_CHAR_UNIQUE] THEN SIMP_TAC[]]);;

let ARTIN_SCHREIER_EXTENSION_EQ = prove
 (`!(h:A->B) k l p.
        field_extension(k,l) h /\ prime p /\ ring_char k = p
        ==> (finite_extension(k,l) h /\ galois_extension(k,l) h /\
             cyclic_group(galois_group(k,l) h) /\
             CARD(group_carrier(galois_group(k,l) h)) divides p <=>
             ?a. a IN ring_carrier l /\
                 ring_sub l (ring_pow l a p) a IN IMAGE h (ring_carrier k) /\
                 subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC;
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `p:num`]
      GALOIS_EXTENSION_ARTIN_SCHREIER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CYCLIC_GALOIS_GROUP_TRANSLATION THEN
    EXISTS_TAC `a:B` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `a:B`; `p:num`]
      GALOIS_GROUP_ARTIN_SCHREIER) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `CARD(group_carrier(galois_group(k,l) (h:A->B))) = 1 \/
    CARD(group_carrier(galois_group(k,l) h)) = p`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `CARD(group_carrier(galois_group(k,l) (h:A->B))) divides p` THEN
    UNDISCH_TAC `prime p` THEN REWRITE_TAC[prime] THEN MESON_TAC[];
    ALL_TAC;
    MATCH_MP_TAC ARTIN_SCHREIER_EXTENSION THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CARD_GALOIS_GROUP_LE) THEN
  MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h`
    TRIVIAL_GROUP_HAS_SIZE_1) THEN
  ASM_REWRITE_TAC[trivial_group; CONJUNCT1(CONJUNCT2 GALOIS_GROUP);
                  HAS_SIZE] THEN
  DISCH_TAC THEN EXISTS_TAC `ring_0 l:B` THEN
  ASM_SIMP_TAC[GALOIS_EXTENSION_SIMPLE_EQ; IN_SING; RING_0] THEN
  ASM_SIMP_TAC[RING_POW_ZERO; PRIME_IMP_NZ; RING_SUB_REFL; RING_0] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `ring_0 k:A` THEN
  REWRITE_TAC[RING_0] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
  ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Solvable towers. The Galois group of l over the subfield generated by the *)
(* image of k is the Galois group of l over k. A chain of intermediate       *)
(* fields from the image of k to l in which each step is normal with abelian *)
(* Galois group gives a chain of Galois groups as in the definition of       *)
(* solvable_group: each is normal in the previous one, as the kernel of the  *)
(* restriction to the next step, with quotient embedded in the abelian       *)
(* Galois group of the step. Nothing is assumed about l over k except that l *)
(* is a field. In particular the Galois group is solvable when l is          *)
(* generated over the image of k by an element z of finite order followed by *)
(* finitely many elements each of which has a power, with exponent dividing  *)
(* the order of z, in the subfield generated by the earlier ones: a          *)
(* cyclotomic step followed by Kummer steps, in any characteristic. Finally  *)
(* a normal extension that embeds over k into a normal extension with        *)
(* solvable Galois group has a solvable Galois group, an epimorphic image    *)
(* under restriction.                                                        *)
(* ------------------------------------------------------------------------- *)

let GALOIS_GROUP_SUBFIELD_GENERATED_IMAGE = prove
 (`!(h:A->B) k l.
        field l
        ==> galois_group(subfield_generated l (IMAGE h (ring_carrier k)),l) I =
            galois_group(k,l) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUPS_EQ; GALOIS_GROUP] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; I_THM] THEN X_GEN_TAC `f:B->B` THEN
  ASM_CASES_TAC `(f:B->B) permutes ring_carrier l` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ring_automorphism l (f:B->B)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(h:A->B) x IN ring_carrier l` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM SET_TAC[];
      ASM_MESON_TAC[permutes]];
    SUBGOAL_THEN
     `ring_carrier(subfield_generated l (IMAGE (h:A->B) (ring_carrier k)))
      SUBSET {x | x IN ring_carrier l /\ (f:B->B) x = x}`
    MP_TAC THENL
     [ASM_SIMP_TAC[SUBFIELD_GENERATED_MINIMAL_EQ; SUBFIELD_OF_FIXPOINTS;
                   RING_AUTOMORPHISM_IMP_ENDOMORPHISM] THEN
      ASM SET_TAC[];
      SET_TAC[]]]);;

let SOLVABLE_GALOIS_TOWER = prove
 (`!(h:A->B) k l n (s:num->B->bool).
        field l /\
        s 0 = IMAGE h (ring_carrier k) /\ s n = ring_carrier l /\
        (!i. i < n
             ==> s i subfield_of l /\ s i SUBSET s(SUC i) /\
                 normal_extension
                  (subfield_generated l (s i),subfield_generated l (s(SUC i)))
                  I /\
                 abelian_group
                  (galois_group
                    (subfield_generated l (s i),
                     subfield_generated l (s(SUC i))) I))
        ==> solvable_group(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tower")))) THEN
  SUBGOAL_THEN
   `!i. i <= n
        ==> (s:num->B->bool) i subfield_of l /\
            IMAGE (h:A->B) (ring_carrier k) SUBSET s i`
  (LABEL_TAC "sub") THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[SUBSET_REFL]] THEN
      ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_TAC `(s:num->B->bool) n = ring_carrier l` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF];
        USE_THEN "tower" (MP_TAC o SPEC `0`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(fun ih -> DISCH_TAC THEN MP_TAC ih) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "tower" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_CASES_TAC `SUC i = n` THENL
     [ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF];
      USE_THEN "tower" (MP_TAC o SPEC `SUC i`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[solvable_group] THEN EXISTS_TAC `n:num` THEN
  EXISTS_TAC
   `\i. group_carrier
         (galois_group(subfield_generated l ((s:num->B->bool) i),l) I)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[GALOIS_GROUP_SUBFIELD_GENERATED_IMAGE];
    ASM_REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER] THEN
    MP_TAC(ISPECL [`I:B->B`; `l:B ring`; `l:B ring`] TRIVIAL_GALOIS_GROUP) THEN
    REWRITE_TAC[IMAGE_I; SUBSET_REFL; trivial_group; GALOIS_GROUP];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "tower" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "sub" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "sub" (MP_TAC o SPEC `SUC i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `(s:num->B->bool) i`]
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated l ((s:num->B->bool) i)) = s i`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l ((s:num->B->bool) i)`;
                 `l:B ring`; `(s:num->B->bool)(SUC i)`]
    GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[NORMAL_SUBGROUP_GROUP_KERNEL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_ABELIANNESS o
    MATCH_MP FIRST_GROUP_ISOMORPHISM_THEOREM) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ABELIAN_SUBGROUP_GENERATED THEN
  ASM_REWRITE_TAC[]);;

let SOLVABLE_GALOIS_RADICAL_TOWER = prove
 (`!(h:A->B) k l z n (a:num->B) (m:num->num).
        field_extension(k,l) h /\
        z IN ring_carrier l /\ ~(ring_order l z = 0) /\
        (!i. i < n
             ==> m i divides ring_order l z /\ a i IN ring_carrier l /\
                 ring_pow l (a i) (m i) IN
                 ring_carrier(subfield_generated l
                   (z INSERT IMAGE h (ring_carrier k) UNION
                    IMAGE a {j | j < i}))) /\
        subfield_generated l
          (z INSERT IMAGE h (ring_carrier k) UNION IMAGE a {i | i < n}) = l
        ==> solvable_group(galois_group(k,l) h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "a")
     ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier k) subfield_of l` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN EXISTS_TAC `k:A ring` THEN
    ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t:num->B->bool.
      !i. t i = ring_carrier(subfield_generated l
                  (z INSERT IMAGE (h:A->B) (ring_carrier k) UNION
                   IMAGE (a:num->B) {j | j < i}))`
  (X_CHOOSE_THEN `t:num->B->bool` (LABEL_TAC "tdef")) THENL
   [EXISTS_TAC
     `\i. ring_carrier(subfield_generated l
            ((z:B) INSERT IMAGE (h:A->B) (ring_carrier k) UNION
             IMAGE (a:num->B) {j | j < i}))` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (t:num->B->bool) i subfield_of l /\ z IN t i /\
        IMAGE (h:A->B) (ring_carrier k) SUBSET t i /\ t i SUBSET t(SUC i) /\
        subfield_generated l (t(SUC i)) =
        subfield_generated l ((a:num->B) i INSERT t i)`
  (LABEL_TAC "t") THENL
   [X_GEN_TAC `i:num` THEN USE_THEN "tdef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
                 SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED;
                 SUBFIELD_GENERATED_INSERT] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      ASM_REWRITE_TAC[IN_INSERT; IN_UNION];
      MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET] THEN SET_TAC[];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
      REWRITE_TAC[IN_ELIM_THM; LT] THEN SET_TAC[];
      AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNION; IN_IMAGE; IN_ELIM_THM;
                  LT] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subfield_generated l ((t:num->B->bool) 0) =
    subfield_generated l (z INSERT IMAGE (h:A->B) (ring_carrier k)) /\
    t n = ring_carrier l /\
    !i. i < n ==> ring_pow l ((a:num->B) i) ((m:num->num) i) IN t i`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "tdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED; LT; EMPTY_GSPEC;
                IMAGE_CLAUSES; UNION_EMPTY] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && rand(concl th) = `l:B ring`)) THEN
      REFL_TAC;
      USE_THEN "a" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  REMOVE_THEN "tdef" (K ALL_TAC) THEN
  MATCH_MP_TAC SOLVABLE_GALOIS_TOWER THEN
  MAP_EVERY EXISTS_TAC
   [`SUC n`;
    `\i. if i = 0 then IMAGE (h:A->B) (ring_carrier k)
         else (t:num->B->bool)(i - 1)`] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[NOT_SUC; SUC_SUB1; LT_SUC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "t" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k)`; `z:B`;
                   `ring_order l (z:B)`]
      CYCLOTOMIC_EXTENSION_ABELIAN_INTERMEDIATE) THEN
    ASM_SIMP_TAC[RING_POW_RING_ORDER] THEN
    MESON_TAC[GALOIS_IMP_NORMAL_EXTENSION];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  USE_THEN "t" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "a" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `i < n:num`)) THEN
  MP_TAC(ISPECL [`l:B ring`; `(t:num->B->bool) i`; `(a:num->B) i`;
                 `(m:num->num) i`]
    KUMMER_EXTENSION_ABELIAN_INTERMEDIATE) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[GALOIS_IMP_NORMAL_EXTENSION]] THEN
  USE_THEN "t" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`l:B ring`; `(t:num->B->bool) i`; `z:B`;
                 `ring_order l (z:B)`; `(m:num->num) i`]
    ROOTS_OF_UNITY_RING_ORDER_DIVISOR) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; SUBFIELD_IMP_SUBRING_OF]);;

let SOLVABLE_GALOIS_SUBEXTENSION = prove
 (`!(h:A->B) (g:A->C) (j:B->C) k l m.
        normal_extension(k,l) h /\ normal_extension(k,m) g /\
        ring_homomorphism(l,m) j /\
        (!x. x IN ring_carrier k ==> j(h x) = g x) /\
        solvable_group(galois_group(k,m) g)
        ==> solvable_group(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP NORMAL_IMP_FIELD_EXTENSION o
    check (fun th -> concl th = t)))
   [`normal_extension(k:A ring,l:B ring) h`;
    `normal_extension(k:A ring,m:C ring) g`] THEN
  SUBGOAL_THEN `ring_monomorphism(l:B ring,m:C ring) j` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  ABBREV_TAC `t = IMAGE (j:B->C) (ring_carrier l)` THEN
  SUBGOAL_THEN `(t:C->bool) subfield_of m` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:A->C) (ring_carrier k) SUBSET t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o C MATCH_MP
     (ASSUME `(x:A) IN ring_carrier k`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; ring_monomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_isomorphism(l,subfield_generated m t) (j:B->C)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_ISOMORPHISM; CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
      MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_REWRITE_TAC[field_extension; SUBSET_REFL];
      ASM_MESON_TAC[ring_monomorphism]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `j:B->C`; `k:A ring`; `l:B ring`;
                 `subfield_generated m (t:C->bool)`]
    ISOMORPHIC_GALOIS_GROUPS) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_SOLVABILITY) THEN
  MATCH_MP_TAC(ISPEC `galois_group(k:A ring,m:C ring) g`
    SOLVABLE_GROUP_EPIMORPHIC_IMAGE) THEN
  EXISTS_TAC `\(f:C->C) x. if x IN t then f x else x` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:A->C`; `k:A ring`; `m:C ring`; `t:C->bool`]
    GALOIS_GROUP_RESTRICTION) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `I:A->A`; `j:B->C`; `k:A ring`;
                 `l:B ring`; `k:A ring`; `subfield_generated m (t:C->bool)`]
    NORMAL_EXTENSION_ISOMORPHIC_IMAGE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RING_ISOMORPHISM_I; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* Galois groups of radical extensions. A radical subextension s of a field  *)
(* l comes with an n <> 0 such that adjoining to s any element of l of order *)
(* n gives an extension with solvable Galois group over k (the exponents of  *)
(* the radicals divide n). In characteristic zero an algebraically closed    *)
(* field has elements of every order n <> 0, and for a normal radical        *)
(* extension l the field obtained by adjoining such an element to an image   *)
(* of l is again normal, as the compositum of l with a cyclotomic extension; *)
(* so normal radical extensions have solvable Galois groups. With the normal *)
(* closure, the same holds for normal extensions that embed into radical     *)
(* extensions, and for the splitting extension of an irreducible polynomial  *)
(* with a root expressible by radicals in some extension field.              *)
(* ------------------------------------------------------------------------- *)

let SOLVABLE_GALOIS_RADICAL_ROOT_OF_UNITY = prove
 (`!(h:A->B) k l s.
        field l /\ s subfield_of l /\
        radical_extension(k,subfield_generated l s) h
        ==> ?n. ~(n = 0) /\
                !z. z IN ring_carrier l /\ ring_order l z = n
                    ==> solvable_group
                          (galois_group(k,subfield_generated l (z INSERT s))
                                       h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field_extension(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (s:B->bool)`; `l:B ring`]
      FIELD_EXTENSION_TRANS) THEN
    ASM_SIMP_TAC[RADICAL_IMP_FIELD_EXTENSION;
                 FIELD_EXTENSION_SUBFIELD_GENERATED; I_O_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    RADICAL_EXTENSION_INTO_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num`
    (X_CHOOSE_THEN `a:num->B` (X_CHOOSE_THEN `m:num->num`
      (CONJUNCTS_THEN2 (LABEL_TAC "a") (LABEL_TAC "s")))))) THEN
  SUBGOAL_THEN
   `!q. q <= p ==> ?n. ~(n = 0) /\ !i. i < q ==> (m:num->num) i divides n`
  (MP_TAC o SPEC `p:num`) THENL
   [INDUCT_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC `1` THEN REWRITE_TAC[LT; ARITH_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "a" (MP_TAC o SPEC `q:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    EXISTS_TAC `n * (m:num->num) q` THEN ASM_REWRITE_TAC[MULT_EQ_0; LT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL];
    REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < p ==> (a:num->B) i IN s` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "s" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN CONJ_TAC THENL
     [USE_THEN "a" (fun th -> ASM_MESON_TAC[th]);
      REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= p
        ==> subfield_generated (subfield_generated l (z INSERT s))
              ((z:B) INSERT IMAGE (h:A->B) (ring_carrier k) UNION
               IMAGE (a:num->B) {j | j < i}) =
            subfield_generated l
              (z INSERT IMAGE h (ring_carrier k) UNION IMAGE a {j | j < i})`
  (LABEL_TAC "idem") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(z:B) INSERT s` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET THEN
      ASM_SIMP_TAC[INSERT_SUBSET; SUBFIELD_OF_IMP_SUBSET]] THEN
    MATCH_MP_TAC(SET_RULE
     `!z:B s t u. t SUBSET s /\ u SUBSET s ==> z INSERT t UNION u SUBSET
                                               z INSERT s`) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[LTE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN ring_carrier(subfield_generated l (z INSERT s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MATCH_MP_TAC SOLVABLE_GALOIS_RADICAL_TOWER THEN
  MAP_EVERY EXISTS_TAC [`z:B`; `p:num`; `a:num->B`; `m:num->num`] THEN
  USE_THEN "idem" (fun th ->
    REWRITE_TAC[MATCH_MP th (SPEC `p:num` LE_REFL)]) THEN
  ASM_SIMP_TAC[RING_ORDER_SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "idem" (fun th -> REWRITE_TAC[MATCH_MP th
      (MATCH_MP LT_IMP_LE (ASSUME `i < p:num`))]) THEN
    USE_THEN "a" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `i < p:num`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_SIMP_TAC[IN_INSERT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(y:B) IN s0 ==> s0 SUBSET t0 ==> y IN t0`)) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC[];
    USE_THEN "s" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBFIELD_GENERATED_INSERT; INSERT_UNION_EQ]]);;

let RADICAL_NORMAL_EXTENSION_SOLVABLE = prove
 (`!(h:A->B) k l.
        ring_char k = 0 /\ radical_extension(k,l) h /\ normal_extension(k,l) h
        ==> solvable_group(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RADICAL_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `om:(B#num)ring` (X_CHOOSE_THEN `j:B->B#num`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM o
    check (fun th -> concl th = `field_extension(l:B ring,om:(B#num)ring) j`))
  THEN
  SUBGOAL_THEN
   `field_extension(k:A ring,om:(B#num)ring) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `j:B->B#num`;
                 `k:A ring`; `l:B ring`; `om:(B#num)ring`]
    RADICAL_EXTENSION_HOMOMORPHIC_IMAGE_GEN) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; o_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `om:(B#num)ring`;
                 `IMAGE (j:B->B#num) (ring_carrier l)`]
    SOLVABLE_GALOIS_RADICAL_ROOT_OF_UNITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`om:(B#num)ring`; `n:num`]
    ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `ring_char(om:(B#num)ring) = 0`
     (fun th -> ASM_REWRITE_TAC[th; DIVIDES_ZERO]) THEN
    ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE];
    DISCH_THEN(X_CHOOSE_THEN `z:B#num` STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `j:B->B#num`;
                 `k:A ring`; `l:B ring`;
                 `subfield_generated om
                    ((z:B#num) INSERT IMAGE (j:B->B#num) (ring_carrier l))`]
    SOLVABLE_GALOIS_SUBEXTENSION) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[o_THM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
    MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
  ABBREV_TAC
   `c = subfield_generated om
          ((z:B#num) INSERT IMAGE ((j:B->B#num) o (h:A->B)) (ring_carrier k))`
  THEN
  SUBGOAL_THEN
   `normal_extension(k:A ring,c:(B#num)ring) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GALOIS_IMP_NORMAL_EXTENSION THEN
    MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `c:(B#num)ring`;
                   `z:B#num`; `n:num`] CYCLOTOMIC_EXTENSION_ABELIAN) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    EXPAND_TAC "c" THEN
    REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT; RING_POW_SUBFIELD_GENERATED;
                CONJUNCT2 SUBFIELD_GENERATED] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      ASM_REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `ring_order om (z:B#num) = n`)) THEN
      MATCH_MP_TAC RING_POW_RING_ORDER THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `j:B->B#num`;
                 `I:(B#num)->(B#num)`; `k:A ring`; `l:B ring`;
                 `c:(B#num)ring`; `om:(B#num)ring`]
    NORMAL_EXTENSION_COMPOSITUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM; I_THM] THEN EXPAND_TAC "c" THEN
    REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN EXPAND_TAC "c" THEN
  REWRITE_TAC[IMAGE_I; SUBFIELD_GENERATED_UNION_RIGHT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE
   `!z:B#num s t. t SUBSET s ==> s UNION (z INSERT t) = z INSERT s`) THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN
  ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET]);;

let RADICAL_EXTENSION_SOLVABLE = prove
 (`!(h:A->B) (g:A->C) (j:B->C) k l m.
        ring_char k = 0 /\ normal_extension(k,l) h /\
        radical_extension(k,m) g /\
        ring_homomorphism(l,m) j /\ (!x. x IN ring_carrier k ==> j(h x) = g x)
        ==> solvable_group(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP RADICAL_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP NORMAL_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `field_extension(l:B ring,m:C ring) j` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[field_extension] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m:C ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `om:(C#num)ring` (X_CHOOSE_THEN `i:C->C#num`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`g:A->C`; `i:C->C#num`; `k:A ring`; `m:C ring`;
                 `om:(C#num)ring`] RADICAL_EXTENSION_NORMAL_CLOSURE) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(C#num)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `(i:C->C#num) o (g:A->C)`;
                 `(i:C->C#num) o (j:B->C)`; `k:A ring`; `l:B ring`;
                 `subfield_generated om (s:(C#num)->bool)`]
    SOLVABLE_GALOIS_SUBEXTENSION) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RADICAL_NORMAL_EXTENSION_SOLVABLE; o_THM] THEN
  MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
  MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN EXISTS_TAC `m:C ring` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (i:C->C#num) (ring_carrier m)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC FIELD_EXTENSION_IMP_SUBSET THEN ASM_REWRITE_TAC[]]);;

let RADICAL_ROOT_SOLVABLE = prove
 (`!(h:A->B) (g:A->C) k l m p x.
        ring_char k = 0 /\ splitting_extension(k,l) h p /\
        ring_irreducible(poly_ring k (:1)) p /\
        field_extension(k,m) g /\ radical_element(k,m) g x /\
        poly_eval m (g o p) x = ring_0 m
        ==> solvable_group(galois_group(k,l) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    check (fun th -> concl th = `field_extension(k:A ring,m:C ring) g`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th = `ring_monomorphism(k:A ring,m:C ring) g`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RADICAL_ELEMENT_IN_CARRIER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IN_POLY_RING) THEN
  MP_TAC(ISPEC `m:C ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `om:(C#num)ring` (X_CHOOSE_THEN `i:C->C#num`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`g:A->C`; `i:C->C#num`; `k:A ring`; `m:C ring`;
                 `om:(C#num)ring`; `x:C`]
    RADICAL_ELEMENT_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(i:C->C#num) o (g:A->C)`; `k:A ring`; `om:(C#num)ring`;
                 `(i:C->C#num) x`] RADICAL_ELEMENT_NORMAL_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(C#num)->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `n = subfield_generated om (s:(C#num)->bool)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `ring_carrier n = (s:(C#num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `(i:C->C#num) o (g:A->C)`; `k:A ring`; `l:B ring`;
                 `n:(C#num)ring`; `p:(1->num)->A`]
    SPLITTING_EXTENSION_EXTEND_HOMOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:B->C#num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`h:A->B`; `(i:C->C#num) o (g:A->C)`; `e:B->C#num`;
                   `k:A ring`; `l:B ring`; `n:(C#num)ring`]
      RADICAL_EXTENSION_SOLVABLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[SPLITTING_EXTENSION_IMP_NORMAL]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [normal_extension] o check (fun th ->
      concl th = `normal_extension(k:A ring,n:(C#num)ring)
                                  ((i:C->C#num) o (g:A->C))`)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `(i:C->C#num) x` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:(C#num)ring`; `om:(C#num)ring`; `(i:C->C#num) x`;
                 `I:(C#num)->(C#num)`;
                 `((i:C->C#num) o (g:A->C)) o (p:(1->num)->A)`]
    POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:A ring` THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]];
    REWRITE_TAC[I_THM; I_O_ID] THEN DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MP_TAC(ISPECL [`m:C ring`; `om:(C#num)ring`; `x:C`; `i:C->C#num`;
                 `(g:A->C) o (p:(1->num)->A)`] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_0]]);;

(* ------------------------------------------------------------------------- *)
(* Polynomials with no root expressible by radicals. In characteristic zero  *)
(* an irreducible polynomial whose Galois group is not solvable has no root  *)
(* expressible by radicals in any extension field. This applies when the     *)
(* degree is a prime at least 5 and some element of the Galois group moves   *)
(* exactly two roots, for then the Galois group is the symmetric group on    *)
(* the roots. In the last form the Galois group element is an automorphism   *)
(* of a field in which the polynomial splits, for example complex            *)
(* conjugation when the field is that of the complex numbers.                *)
(* ------------------------------------------------------------------------- *)

let NOT_SOLVABLE_IMP_NO_RADICAL_ROOT = prove
 (`!(h:A->B) (g:A->C) k l m p.
        ring_char k = 0 /\ splitting_extension(k,l) h p /\
        ring_irreducible(poly_ring k (:1)) p /\
        ~solvable_group(galois_group(k,l) h) /\ field_extension(k,m) g
        ==> ~(?x. radical_element(k,m) g x /\
                  poly_eval m (g o p) x = ring_0 m)`,
  MESON_TAC[RADICAL_ROOT_SOLVABLE]);;

let PRIME_TRANSPOSITION_NO_RADICAL_ROOT = prove
 (`!(h:A->B) (g:A->C) f k l m p.
        ring_char k = 0 /\ splitting_extension(k,l) h p /\
        ring_irreducible(poly_ring k (:1)) p /\
        prime(poly_deg k p) /\ 5 <= poly_deg k p /\
        f IN group_carrier(galois_group(k,l) h) /\
        {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l /\
             ~(f x = x)} HAS_SIZE 2 /\
        field_extension(k,m) g
        ==> ~(?x. radical_element(k,m) g x /\
                  poly_eval m (g o p) x = ring_0 m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `p:(1->num)->A`] NOT_SOLVABLE_IMP_NO_RADICAL_ROOT) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IN_POLY_RING) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_NONZERO) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_SPLITS) THEN
  SUBGOAL_THEN
   `FINITE {x | x IN ring_carrier l /\
                poly_eval l ((h:A->B) o p) x = ring_0 l} /\
    CARD {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l} =
    poly_deg k (p:(1->num)->A)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
        POLY_ROOT_BOUND_EXTENSION) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE THEN
      ASM_SIMP_TAC[PERFECT_FIELD_CHAR_0] THEN
      ASM_MESON_TAC[field_extension]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`;
                 `p:(1->num)->A`] GALOIS_GROUP_PRIME_TRANSPOSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_SOLVABILITY) THEN
  MATCH_MP_TAC NOT_SOLVABLE_SYMMETRIC_GROUP THEN ASM_REWRITE_TAC[]);;

let PRIME_TRANSPOSITION_NO_RADICAL_ROOT_SPLITS = prove
 (`!(g:A->B) f k m p.
        ring_char k = 0 /\ field_extension(k,m) g /\
        ring_irreducible(poly_ring k (:1)) p /\ poly_splits_over(k,m) g p /\
        prime(poly_deg k p) /\ 5 <= poly_deg k p /\
        f IN group_carrier(galois_group(k,m) g) /\
        {x | x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m /\
             ~(f x = x)} HAS_SIZE 2
        ==> ~(?x. radical_element(k,m) g x /\
                  poly_eval m (g o p) x = ring_0 m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  SUBGOAL_THEN `~((p:(1->num)->A) = poly_0 k)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_irreducible]) THEN
    REWRITE_TAC[POLY_RING_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->B`; `k:A ring`; `m:B ring`; `p:(1->num)->A`]
    SPLITTING_EXTENSION_GENERATED_BY_ROOTS) THEN
  ONCE_REWRITE_TAC[GSYM SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated m
      (IMAGE (g:A->B) (ring_carrier k) UNION
       {x | x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m}))
    subfield_of m /\
    IMAGE (g:A->B) (ring_carrier k) SUBSET
    ring_carrier(subfield_generated m
      (IMAGE (g:A->B) (ring_carrier k) UNION
       {x | x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m})) /\
    (!x. x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m
         ==> x IN ring_carrier(subfield_generated m
                (IMAGE (g:A->B) (ring_carrier k) UNION
                 {x | x IN ring_carrier m /\
                      poly_eval m (g o p) x = ring_0 m})))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_SUBSET; SUBSET_UNION];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC
   `s = ring_carrier(subfield_generated m
          (IMAGE (g:A->B) (ring_carrier k) UNION
           {x | x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m}))` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBFIELD_OF_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`g:A->B`; `g:A->B`; `\x. if x IN s then (f:B->B) x else x`;
                 `k:A ring`; `subfield_generated m (s:B->bool)`; `m:B ring`;
                 `p:(1->num)->A`] PRIME_TRANSPOSITION_NO_RADICAL_ROOT) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GALOIS_GROUP_RESTRICT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE THEN
    ASM_MESON_TAC[SPLITTING_EXTENSION_IMP_NORMAL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `!t u:B->bool. t HAS_SIZE 2 ==> u = t ==> u HAS_SIZE 2`)) THEN
  SUBGOAL_THEN `ring_homomorphism(k,subfield_generated m s) (g:A->B)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SPLITTING_IMP_FIELD_EXTENSION;
                  FIELD_EXTENSION_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               CONJUNCT2 SUBFIELD_GENERATED] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN
  ASM_CASES_TAC `(x:B) IN s` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier m` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`m:B ring`; `s:B->bool`; `(g:A->B) o (p:(1->num)->A)`;
                 `x:B`] POLY_EVAL_SUBFIELD_GENERATED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Solvable Galois groups and radicals: the converse of Abel-Ruffini. If k   *)
(* has n distinct n-th roots of unity, a finite Galois extension of k whose  *)
(* degree divides n and whose Galois group is solvable is radical: a chain   *)
(* of subgroups with cyclic quotients gives a chain of intermediate fields,  *)
(* each a Kummer extension of the previous one. In general one adjoins to an *)
(* image of l a root of unity z of order N, a multiple of [l:k]: by natural  *)
(* irrationalities the result is finite Galois over the field generated by   *)
(* the image of k and z, with a solvable Galois group of order dividing N,   *)
(* and that field is radical over k. So when the characteristic of k does    *)
(* not divide [l:k], every element of a finite Galois extension with         *)
(* solvable Galois group is expressible by radicals in each algebraically    *)
(* closed field into which l embeds. In characteristic zero this gives the   *)
(* iff forms: a finite normal extension has a solvable Galois group exactly  *)
(* when all of its elements are expressible by radicals, and the splitting   *)
(* extension of a polynomial has a solvable Galois group exactly when all    *)
(* roots of the polynomial in an algebraically closed field are expressible  *)
(* by radicals, or for an irreducible polynomial, some root.                 *)
(* ------------------------------------------------------------------------- *)

(* One step of a tower: if k has n distinct n-th roots of unity and n is a   *)
(* multiple of [l:k], the fixed field of a normal subgroup H of the Galois   *)
(* group with cyclic quotient is generated over k by an n-th root of an      *)
(* element of k. Finiteness is implied: [l:k] divides n, which is nonzero.   *)

let RADICAL_EXTENSION_CYCLIC_QUOTIENT = prove
 (`!(h:A->B) k l n H.
     galois_extension(k,l) h /\
     extension_degree(k,l) h divides n /\
     {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n /\
     H normal_subgroup_of galois_group(k,l) h /\
     cyclic_group(quotient_group (galois_group(k,l) h) H)
     ==> radical_extension(k,subfield_generated l (fixed_field l H)) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ROOTS_OF_UNITY_HAS_SIZE_NONZERO) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `finite_extension(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0; DIVIDES_ZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `H:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP] THEN
  ABBREV_TAC `s = fixed_field (l:B ring) H` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `H:(B->B)->bool`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    GALOIS_EXTENSION_NORMAL_SUBGROUP) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
                 `n:num`] KUMMER_CYCLIC_EXTENSION_EQ) THEN
  ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP ISOMORPHIC_GROUP_CYCLICITY) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`]
      GALOIS_EXTENSION_EQ_CARD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC DIVIDES_TRANS THEN
    EXISTS_TAC `extension_degree(k:A ring,l:B ring) h` THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_SUBFIELD_GENERATED_DIVIDES];
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RADICAL_EXTENSION_SIMPLE THEN
    MAP_EVERY EXISTS_TAC [`a:B`; `n:num`] THEN
    ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION]]);;

(* The converse of Abel-Ruffini over a field with enough roots of unity. The *)
(* chain c(0), ..., c(r) of SOLVABLE_GROUP_CYCLIC_CHAIN gives the fixed      *)
(* fields F(i) of the c(i), with F(0) the image of k and F(r) = l; F(i+1) is *)
(* the fixed field of the normal subgroup c(i+1), with cyclic quotient, of   *)
(* the Galois group c(i) of l over F(i), whose roots of unity include those  *)
(* of k. As above, finiteness follows from [l:k] dividing n.                 *)

let SOLVABLE_IMP_RADICAL_EXTENSION = prove
 (`!(h:A->B) k l n.
        galois_extension(k,l) h /\
        solvable_group(galois_group(k,l) h) /\
        extension_degree(k,l) h divides n /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n
        ==> radical_extension(k,l) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ROOTS_OF_UNITY_HAS_SIZE_NONZERO) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `finite_extension(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0; DIVIDES_ZERO]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN
   `!s. s subfield_of l /\ IMAGE (h:A->B) (ring_carrier k) SUBSET s
        ==> {x | x IN s /\ ring_pow l x n = ring_1 l} HAS_SIZE n`
  (LABEL_TAC "roots") THENL
   [MP_TAC(ISPECL [`k:A ring`; `n:num`] ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `s:B->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `z:A`]
      RING_ORDER_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `s:B->bool`; `(h:A->B) z`; `n:num`; `n:num`]
      ROOTS_OF_UNITY_RING_ORDER_DIVISOR) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; SUBFIELD_IMP_SUBRING_OF;
                 DIVIDES_REFL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `galois_group(k:A ring,l:B ring) h`
    SOLVABLE_GROUP_CYCLIC_CHAIN) THEN
  ASM_SIMP_TAC[FINITE_GALOIS_GROUP; CONJUNCT1(CONJUNCT2 GALOIS_GROUP)] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` (X_CHOOSE_THEN `c:num->(B->B)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "c"))))) THEN
  SUBGOAL_THEN
   `!i. i <= r
        ==> (c:num->(B->B)->bool) i subgroup_of galois_group(k,l) (h:A->B)`
  (LABEL_TAC "sub") THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[CARRIER_SUBGROUP_OF]; ALL_TAC] THEN
    DISCH_TAC THEN USE_THEN "c" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP;
              SUBGROUP_OF_SUBGROUP_GENERATED_REV];
    ALL_TAC] THEN
  SUBGOAL_THEN `fixed_field (l:B ring) {I} = ring_carrier l` ASSUME_TAC THENL
   [REWRITE_TAC[fixed_field; IN_SING; FORALL_UNWIND_THM2; I_THM] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= r
        ==> radical_extension
             (k,subfield_generated l (fixed_field l ((c:num->(B->B)->bool) i)))
             (h:A->B)`
  (MP_TAC o SPEC `r:num`) THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[LE_REFL; SUBFIELD_GENERATED_RING_CARRIER]] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    ASM_SIMP_TAC[FIXED_FIELD_GALOIS_GROUP; RADICAL_EXTENSION_BASE];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l
                   (fixed_field l ((c:num->(B->B)->bool) i))`;
                 `subfield_generated l
                   (fixed_field l ((c:num->(B->B)->bool) (SUC i)))`]
    RADICAL_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  USE_THEN "sub" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `(c:num->(B->B)->bool) i`] GALOIS_GROUP_FIXED_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = fixed_field l ((c:num->(B->B)->bool) i)` THEN STRIP_TAC THEN
  USE_THEN "c" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `u:B->bool`]
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RADICAL_EXTENSION_CYCLIC_QUOTIENT THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `u:B->bool`]
      GALOIS_EXTENSION_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC DIVIDES_TRANS THEN
    EXISTS_TAC `extension_degree(k:A ring,l:B ring) h` THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_SUBFIELD_GENERATED_DIVIDES];
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD;
                 RING_POW_SUBFIELD_GENERATED; CONJUNCT2 SUBFIELD_GENERATED]]);;

(* Natural irrationalities for solvable groups: if s is finite Galois over   *)
(* the image of k with solvable Galois group, then for any intermediate      *)
(* field t the compositum of s and t is finite Galois over t with solvable   *)
(* Galois group, and its degree over t divides [s:k] (its Galois group is    *)
(* isomorphic to a subgroup of that of s over k).                            *)

let GALOIS_COMPOSITUM_SOLVABLE = prove
 (`!(h:A->B) k l s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\
        IMAGE h (ring_carrier k) SUBSET t /\
        finite_extension(k,subfield_generated l s) h /\
        galois_extension(k,subfield_generated l s) h /\
        solvable_group(galois_group(k,subfield_generated l s) h)
        ==> finite_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I /\
            galois_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I /\
            solvable_group
              (galois_group
                (subfield_generated l t,subfield_generated l (s UNION t)) I) /\
            extension_degree
              (subfield_generated l t,subfield_generated l (s UNION t)) I
            divides extension_degree(k,subfield_generated l s) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `t:B->bool`]
    GALOIS_COMPOSITUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(s INTER t:B->bool) subfield_of subfield_generated l s /\
    IMAGE (h:A->B) (ring_carrier k) SUBSET s INTER t /\
    subfield_generated (subfield_generated l s) (s INTER t) =
    subfield_generated l (s INTER t)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ; SUBFIELD_OF_INTER;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD; SUBSET_INTER;
                 INTER_SUBSET] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
                 `s INTER t:B->bool`]
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
                 `s INTER t:B->bool`]
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_SOLVABILITY o
      MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SOLVABLE_GROUP_SUBGROUP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (t:B->bool)`;
                 `subfield_generated l (s UNION t:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  SUBGOAL_THEN
   `CARD(group_carrier
          (galois_group
            (subfield_generated l t,subfield_generated l (s UNION t)) I)) =
    CARD(group_carrier
          (galois_group
            (subfield_generated l (s INTER t),subfield_generated l s)
            (I:B->B)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k,subfield_generated l s)
                                            (h:A->B))` THEN
      ASM_SIMP_TAC[FINITE_GALOIS_GROUP; SUBGROUP_OF_IMP_SUBSET];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP CARD_EQ_GROUP_ISOMORPHIC_IMAGE)];
    MATCH_MP_TAC LAGRANGE_THEOREM THEN
    ASM_SIMP_TAC[FINITE_GALOIS_GROUP]]);;

(* Adjoining a root of unity to the image of k gives a radical extension.    *)

let RADICAL_EXTENSION_ROOT_OF_UNITY = prove
 (`!(h:A->B) k l z n.
        field_extension(k,l) h /\ z IN ring_carrier l /\ ~(n = 0) /\
        ring_pow l z n = ring_1 l
        ==> radical_extension
             (k,subfield_generated l (z INSERT IMAGE h (ring_carrier k))) h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RADICAL_EXTENSION_SIMPLE THEN
  MAP_EVERY EXISTS_TAC [`z:B`; `n:num`] THEN
  ASM_REWRITE_TAC[RING_POW_SUBFIELD_GENERATED; SUBFIELD_GENERATED_IDEMPOT] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_INSERT];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `ring_1 k:A` THEN
    REWRITE_TAC[RING_1] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN
    MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* Adjoining a root of unity: if l is Galois over k with solvable Galois     *)
(* group, j embeds l into a field m and z in m has finite order a multiple   *)
(* of [l:k] (so l is finite over k), then the subfield of m generated by z   *)
(* and the image of l is radical over k. No assumption on the characteristic *)
(* is needed here.                                                           *)

let SOLVABLE_IMP_RADICAL_ROOT_OF_UNITY = prove
 (`!(h:A->B) (j:B->C) k l m z.
        galois_extension(k,l) h /\
        solvable_group(galois_group(k,l) h) /\
        field m /\ ring_homomorphism(l,m) j /\
        z IN ring_carrier m /\ ~(ring_order m z = 0) /\
        extension_degree(k,l) h divides ring_order m z
        ==> radical_extension
             (k,subfield_generated m (z INSERT IMAGE j (ring_carrier l)))
             (j o h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `finite_extension(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0; DIVIDES_ZERO]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `field_extension(k:A ring,m:C ring) ((j:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[field_extension] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k) SUBSET
    IMAGE j (ring_carrier l) /\
    ring_carrier(subfield_generated m
     (z INSERT IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k))) subfield_of m /\
    IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k) SUBSET
    ring_carrier(subfield_generated m
     (z INSERT IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k))) /\
    (z:C) IN ring_carrier(subfield_generated m
     (z INSERT IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC FIELD_EXTENSION_IMP_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_SUBSET] THEN SET_TAC[];
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    GALOIS_EXTENSION_HOMOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    FINITE_EXTENSION_HOMOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`j:B->C`; `l:B ring`; `m:C ring`]
    RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_SOLVABILITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `N = ring_order (m:C ring) z` THEN
  ABBREV_TAC `s = IMAGE (j:B->C) (ring_carrier l)` THEN
  ABBREV_TAC
   `t = ring_carrier(subfield_generated m
          (z INSERT IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k)))` THEN
  MP_TAC(ISPECL [`(j:B->C) o (h:A->B)`; `k:A ring`; `m:C ring`; `s:C->bool`;
                 `t:C->bool`] GALOIS_COMPOSITUM_SOLVABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `subfield_generated m (s UNION t) = subfield_generated m ((z:C) INSERT s)`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[SUBFIELD_GENERATED_UNION_RIGHT] THEN
    AP_TERM_TAC THEN UNDISCH_TAC
     `IMAGE ((j:B->C) o (h:A->B)) (ring_carrier k) SUBSET s` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:C->C`; `subfield_generated m (t:C->bool)`;
                 `subfield_generated m ((z:C) INSERT s)`; `N:num`]
    SOLVABLE_IMP_RADICAL_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `extension_degree(k:A ring,l:B ring) h` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD;
                   RING_POW_SUBFIELD_GENERATED;
                   CONJUNCT2 SUBFIELD_GENERATED] THEN
      MP_TAC(ISPECL [`m:C ring`; `t:C->bool`; `z:C`; `N:num`; `N:num`]
        ROOTS_OF_UNITY_RING_ORDER_DIVISOR) THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; SUBFIELD_IMP_SUBRING_OF;
                   DIVIDES_REFL]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `radical_extension(k,subfield_generated m t) ((j:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC RADICAL_EXTENSION_ROOT_OF_UNITY THEN
    EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "N" THEN MATCH_MP_TAC RING_POW_RING_ORDER THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(j:B->C) o (h:A->B)`; `I:C->C`; `k:A ring`;
                 `subfield_generated m (t:C->bool)`;
                 `subfield_generated m ((z:C) INSERT s)`]
    RADICAL_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[I_O_ID]);;

(* The converse of Abel-Ruffini: if the characteristic of k does not divide  *)
(* [l:k], every element of a finite Galois extension l of k with solvable    *)
(* Galois group is expressible by radicals over k in any algebraically       *)
(* closed field m into which l embeds (m has an element of order [l:k]).     *)
(* No finiteness hypothesis is needed: the condition forces [l:k] <> 0.      *)

let SOLVABLE_IMP_RADICAL = prove
 (`!(h:A->B) (j:B->C) k l m.
        galois_extension(k,l) h /\
        ~(ring_char k divides extension_degree(k,l) h) /\
        solvable_group(galois_group(k,l) h) /\
        algebraically_closed_field m /\ ring_homomorphism(l,m) j
        ==> !x. x IN ring_carrier l ==> radical_element(k,m) (j o h) (j x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_monomorphism(l:B ring,m:C ring) j` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `extension_degree(k:A ring,l:B ring) h`]
    ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `m:C ring`; `(j:B->C) o (h:A->B)`]
      RING_CHAR_MONOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
      EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `z:C` STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `z:C`] SOLVABLE_IMP_RADICAL_ROOT_OF_UNITY) THEN
  ASM_REWRITE_TAC[DIVIDES_REFL] THEN ANTS_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(ring_char(k:A ring) divides extension_degree(k,l) (h:A->B))` THEN
    ASM_REWRITE_TAC[DIVIDES_0];
    DISCH_TAC] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN REWRITE_TAC[radical_element] THEN
  EXISTS_TAC
   `ring_carrier(subfield_generated m (z INSERT IMAGE (j:B->C)
                                                 (ring_carrier l)))` THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
               SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
  ASM_SIMP_TAC[IN_INSERT; FUN_IN_IMAGE] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
  EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[]);;

(* In characteristic zero, for a finite normal extension: the Galois group   *)
(* is solvable exactly when every element is expressible by radicals in an   *)
(* algebraically closed field into which l embeds. For the converse          *)
(* direction finitely many generators of l lie in one radical subextension   *)
(* of m.                                                                     *)

let GALOIS_SOLVABLE_EQ_RADICAL = prove
 (`!(h:A->B) (j:B->C) k l m.
        ring_char k = 0 /\ finite_extension(k,l) h /\ normal_extension(k,l) h /\
        algebraically_closed_field m /\ ring_homomorphism(l,m) j
        ==> (solvable_group(galois_group(k,l) h) <=>
             !x. x IN ring_carrier l ==> radical_element(k,m) (j o h) (j x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `field_extension(l:B ring,m:C ring) j` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[field_extension] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC SOLVABLE_IMP_RADICAL THEN
    ASM_REWRITE_TAC[DIVIDES_ZERO; galois_extension] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN
      ASM_SIMP_TAC[NORMAL_IMP_ALGEBRAIC_EXTENSION];
      ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_0]];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_FINITELY_GENERATED_EXTENSION) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `field_extension(k:A ring,m:C ring) ((j:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(j:B->C) o (h:A->B)`; `k:A ring`; `m:C ring`;
                 `IMAGE (j:B->C) b`]
    RADICAL_ELEMENTS_COMMON_RADICAL_EXTENSION) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [ASM SET_TAC[]; DISCH_THEN(X_CHOOSE_THEN `s:C->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->C) o (h:A->B)`; `j:B->C`; `k:A ring`;
                 `l:B ring`; `subfield_generated m (s:C->bool)`]
    RADICAL_EXTENSION_SOLVABLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
  MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ring_carrier(l:B ring) =
    ring_carrier(subfield_generated l
      (IMAGE (h:A->B) (ring_carrier k) UNION b))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`;
                 `IMAGE (h:A->B) (ring_carrier k) UNION b`]
    SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_EXTENSION_IMP_MONOMORPHISM;
                 UNION_SUBSET; FIELD_EXTENSION_IMP_SUBSET];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
  ASM_REWRITE_TAC[IMAGE_UNION; UNION_SUBSET; GSYM IMAGE_o] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET o
    MATCH_MP RADICAL_IMP_FIELD_EXTENSION) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD]);;

(* The polynomial forms in characteristic zero: the splitting extension of p *)
(* has a solvable Galois group exactly when all roots of p in an             *)
(* algebraically closed field m are expressible by radicals (the roots       *)
(* generate a splitting extension of p inside m), and for irreducible p      *)
(* exactly when some root is.                                                *)

let SOLVABLE_BY_RADICALS_EQ = prove
 (`!(h:A->B) (g:A->C) k l m p.
        ring_char k = 0 /\ splitting_extension(k,l) h p /\
        algebraically_closed_field m /\ field_extension(k,m) g
        ==> (solvable_group(galois_group(k,l) h) <=>
             !x. x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m
                 ==> radical_element(k,m) g x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IN_POLY_RING) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_NONZERO) THEN
  ABBREV_TAC
   `r = {x | x IN ring_carrier m /\
             poly_eval m ((g:A->C) o (p:(1->num)->A)) x = ring_0 m}` THEN
  SUBGOAL_THEN
   `splitting_extension
     (k,subfield_generated m (IMAGE (g:A->C) (ring_carrier k) UNION r)) g p`
  ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC SPLITTING_EXTENSION_GENERATED_BY_ROOTS THEN
    ASM_REWRITE_TAC[poly_splits_over] THEN
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`;
                 `subfield_generated m
                    (IMAGE (g:A->C) (ring_carrier k) UNION r)`;
                 `p:(1->num)->A`] ISOMORPHIC_GALOIS_GROUPS_SPLITTING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_SOLVABILITY) THEN
  MP_TAC(ISPECL [`g:A->C`; `I:C->C`; `k:A ring`;
                 `subfield_generated m
                    (IMAGE (g:A->C) (ring_carrier k) UNION r)`;
                 `m:C ring`] GALOIS_SOLVABLE_EQ_RADICAL) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_O_ID; I_THM] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SPLITTING_IMP_FINITE_EXTENSION;
                  SPLITTING_EXTENSION_IMP_NORMAL];
    DISCH_THEN SUBST1_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:C` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    EXPAND_TAC "r" THEN ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `{x | radical_element(k,m) (g:A->C) x}`;
                 `IMAGE (g:A->C) (ring_carrier k) UNION r`]
    SUBFIELD_GENERATED_MINIMAL) THEN
  ASM_SIMP_TAC[SUBFIELD_OF_RADICAL_ELEMENTS] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RADICAL_ELEMENT_BASE] THEN EXPAND_TAC "r" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM]]);;

let SOLVABLE_BY_RADICALS_IRREDUCIBLE_EQ = prove
 (`!(h:A->B) (g:A->C) k l m p.
        ring_char k = 0 /\ splitting_extension(k,l) h p /\
        ring_irreducible(poly_ring k (:1)) p /\
        algebraically_closed_field m /\ field_extension(k,m) g
        ==> (solvable_group(galois_group(k,l) h) <=>
             ?x. x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m /\
                 radical_element(k,m) g x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:C` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                   `p:(1->num)->A`; `x:C`] RADICAL_ROOT_SOLVABLE) THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `p:(1->num)->A`] SOLVABLE_BY_RADICALS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(?x:C. P x /\ R x) ==> (!x. P x /\ R x ==> Q x)
    ==> (?x. P x /\ R x /\ Q x)`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IN_POLY_RING) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `m:C ring`; `g:A->C`; `p:(1->num)->A`]
    POLY_DEG_MONOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL; IRREDUCIBLE_IMP_POLY_DEG_NZ]);;
