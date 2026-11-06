(* ========================================================================= *)
(* The cyclotomic character.                                                 *)
(*                                                                           *)
(*   cyclotomic_character k n f = the unit c mod n with f x = x^c for every  *)
(*                                n-th root of unity x of k                  *)
(*                                                                           *)
(* For an integral domain k containing an element z of order n (ring_order k *)
(* z = n, n nonzero) and a ring automorphism f of k, cyclotomic_character k  *)
(* n f is a unit of the integers mod n with f x = x^c for all n-th roots of  *)
(* unity x (CYCLOTOMIC_CHARACTER), the only one with f z = z^c               *)
(* (CYCLOTOMIC_CHARACTER_UNIQUE), and for m dividing n the character mod m   *)
(* is its reduction mod m (CYCLOTOMIC_CHARACTER_DIVIDES), so the characters  *)
(* for the powers of a prime form a compatible family. On every Galois group *)
(* galois_group(k,l) h with l containing z it is a homomorphism into         *)
(* unit_group(integer_mod_ring n) (CYCLOTOMIC_CHARACTER_HOMOMORPHISM),       *)
(* continuous for the Krull topology of Multivariate/infinite_galois.ml and  *)
(* the discrete topology on the units (CYCLOTOMIC_CHARACTER_CONTINUOUS),     *)
(* with kernel, for l a field, the Galois group of l over k(z)               *)
(* (CYCLOTOMIC_CHARACTER_KERNEL). For l normal over k it is onto iff         *)
(* [k(z):k] = phi(n) (CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ), in particular    *)
(* for k the prime field of characteristic 0                                 *)
(* (CYCLOTOMIC_CHARACTER_EPIMORPHISM, by the irreducibility of the           *)
(* cyclotomic polynomials over Q), and for Q-bar it is a continuous          *)
(* epimorphism for every n (ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER).         *)
(*                                                                           *)
(* Routes. An automorphism maps z to a power z^j with j a unit mod n         *)
(* (RING_ENDOMORPHISM_ROOT_OF_UNITY applied to f and its inverse), and the   *)
(* n-th roots of unity are the powers of z (ROOTS_OF_UNITY_RING_ORDER);      *)
(* powers of z depend only on the exponent mod n (RING_POW_EQ_GEN).          *)
(* Surjectivity: restriction maps Gal(l/k) onto Gal(k(z)/k)                  *)
(* (GALOIS_GROUP_RESTRICTION, k(z) being Galois over k by                    *)
(* CYCLOTOMIC_EXTENSION_ABELIAN), and the monomorphism of Gal(k(z)/k) into   *)
(* modmul_group n of Library/cyclotomic.ml (CYCLOTOMIC_GALOIS_GROUP_MODMUL)  *)
(* is an isomorphism iff [k(z):k] = phi(n)                                   *)
(* (CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM), modmul_group n being        *)
(* isomorphic to the unit group (GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP); over  *)
(* Q, k(z) is the number field Q(z) of degree phi(n)                         *)
(* (CYCLOTOMIC_FIELD_DEGREE).                                                *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml,                      *)
(* Library/ring_groups.ml (unit_group), Library/galois.ml,                   *)
(* Library/cyclotomic.ml, Multivariate/metric.ml (pointwise_topology),       *)
(* ANT/numfield.ml, ANT/cyclotomic_field.ml and ANT/cyclotomic_galois.ml     *)
(* (UNIT_GROUP_INTEGER_MOD_RING, GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP).       *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_groups.ml";;
needs "Library/galois.ml";;
needs "Library/cyclotomic.ml";;
needs "ANT/numfield.ml";;
needs "ANT/cyclotomic_field.ml";;
needs "ANT/cyclotomic_galois.ml";;
needs "Multivariate/metric.ml";;

(* ------------------------------------------------------------------------- *)
(* The cyclotomic character of a ring automorphism, defined by the Hilbert   *)
(* choice operator over the units mod n; the conditions make it well         *)
(* defined. Its reduction mod a divisor m of n is the character mod m, an    *)
(* element of order m being a power of z.                                    *)
(* ------------------------------------------------------------------------- *)

let cyclotomic_character = new_definition
 `cyclotomic_character (k:A ring) n (f:A->A) =
        @c. c IN group_carrier(unit_group(integer_mod_ring n)) /\
            !x. x IN ring_carrier k /\ ring_pow k x n = ring_1 k
                ==> f x = ring_pow k x (num_of_int c)`;;

let CYCLOTOMIC_CHARACTER = prove
 (`!(k:A ring) n z f.
        integral_domain k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ ring_automorphism k f
        ==> cyclotomic_character k n f IN
            group_carrier(unit_group(integer_mod_ring n)) /\
            !x. x IN ring_carrier k /\ ring_pow k x n = ring_1 k
                ==> f x = ring_pow k x
                  (num_of_int(cyclotomic_character k n f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cyclotomic_character] THEN CONV_TAC SELECT_CONV THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_automorphism]) THEN
  REWRITE_TAC[ring_isomorphism; ring_isomorphisms; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:A->A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `f:A->A`; `z:A`]
    RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->A`; `z:A`]
    RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
  ASM_REWRITE_TAC[ring_endomorphism] THEN
  DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
  SUBGOAL_THEN `coprime(j:num,n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `ring_pow k (z:A) (j * i) = ring_pow k z 1` MP_TAC THENL
     [ASM_SIMP_TAC[RING_POW_1; GSYM RING_POW_POW] THEN
      UNDISCH_TAC `(f:A->A) z = ring_pow k z j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
        (ASSUME `ring_homomorphism(k,k) (f:A->A)`))] THEN
      UNDISCH_TAC `(g:A->A) z = ring_pow k z i` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[RING_POW_EQ_GEN] THEN CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  EXISTS_TAC `&(j MOD n):int` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[UNIT_GROUP_INTEGER_MOD_RING] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `j MOD n` THEN
    ASM_SIMP_TAC[MOD_LT_EQ; COPRIME_LMOD];
    ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`] ROOTS_OF_UNITY_RING_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A` o GEN_REWRITE_RULE I [EXTENSION] o
    CONJUNCT1) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW
    (ASSUME `ring_homomorphism(k,k) (f:A->A)`)] THEN
  ASM_SIMP_TAC[RING_POW_POW; RING_POW_EQ_GEN] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MULT_SYM]);;

let CYCLOTOMIC_CHARACTER_UNIQUE = prove
 (`!(k:A ring) n z f c.
        integral_domain k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ ring_automorphism k f /\
        c IN group_carrier(unit_group(integer_mod_ring n))
        ==> (cyclotomic_character k n f = c <=>
             f z = ring_pow k z (num_of_int c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `z:A`; `f:A->A`]
    CYCLOTOMIC_CHARACTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:A`)) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`] RING_POW_RING_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THENL [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_POW_EQ_GEN] THEN
  MAP_EVERY UNDISCH_TAC
   [`c IN group_carrier(unit_group(integer_mod_ring n))`;
    `cyclotomic_character (k:A ring) n f IN
     group_carrier(unit_group(integer_mod_ring n))`] THEN
  ASM_SIMP_TAC[UNIT_GROUP_INTEGER_MOD_RING; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[CONG] THEN ASM_SIMP_TAC[MOD_LT]);;

let CYCLOTOMIC_CHARACTER_DIVIDES = prove
 (`!(k:A ring) m n z f.
        integral_domain k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ m divides n /\ ring_automorphism k f
        ==> cyclotomic_character k m f = cyclotomic_character k n f rem &m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `0 divides (n:num)` THEN ASM_REWRITE_TAC[DIVIDES_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n DIV m = 0) /\ n DIV m divides n /\ n DIV (n DIV m) = m`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [divides] o
      check (fun th -> concl th = `(m:num) divides n`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN
    CONJ_TAC THENL [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow k (ring_pow k (z:A) (n DIV m)) n = ring_1 k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `z:A`] RING_POW_RING_ORDER) THEN
    ASM_SIMP_TAC[RING_POW_POW] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[GSYM RING_POW_POW; RING_POW_ONE];
    ALL_TAC] THEN
  ABBREV_TAC `w = ring_pow k (z:A) (n DIV m)` THEN
  SUBGOAL_THEN `(w:A) IN ring_carrier k /\ ring_order k w = m`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[RING_POW; RING_ORDER_POW]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `z:A`; `f:A->A`]
    CYCLOTOMIC_CHARACTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o SPEC `w:A`)) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`cyclotomic_character (k:A ring) n f`,`c:int`) THEN
  X_GEN_TAC `c:int` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[UNIT_GROUP_INTEGER_MOD_RING; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NUM_OF_INT_OF_NUM]) THEN
  REWRITE_TAC[INT_OF_NUM_REM] THEN
  MP_TAC(ISPECL [`k:A ring`; `m:num`; `w:A`; `f:A->A`; `&(a MOD m):int`]
    CYCLOTOMIC_CHARACTER_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[UNIT_GROUP_INTEGER_MOD_RING; IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `a MOD m` THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
    REWRITE_TAC[COPRIME_LMOD] THEN
    UNDISCH_TAC `coprime(a:num,n)` THEN UNDISCH_TAC `(m:num) divides n` THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `a:num`] RING_POW_MOD_ORDER) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The character on Galois groups: a homomorphism, continuous since its      *)
(* fibres are the sets {f | f z = z^c}, open in the pointwise topology, with *)
(* kernel the automorphisms fixing z, that is the Galois group over k(z).    *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_CHARACTER_HOMOMORPHISM = prove
 (`!(h:A->B) k l n z.
        integral_domain l /\ z IN ring_carrier l /\ ring_order l z = n /\
        ~(n = 0)
        ==> group_homomorphism
             (galois_group(k,l) h,unit_group(integer_mod_ring n))
             (cyclotomic_character l n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `f:B->B`]
      CYCLOTOMIC_CHARACTER) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
  REWRITE_TAC[GALOIS_GROUP; UNIT_GROUP] THEN
  SUBGOAL_THEN
   `ring_automorphism l (f:B->B) /\ ring_automorphism l (g:B->B) /\
    ring_automorphism l (f o g) /\ ring_homomorphism(l,l) f`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM; GALOIS_GROUP_COMPOSE;
                  GALOIS_GROUP_RING_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `z:B`] RING_POW_RING_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `f:B->B`]
    CYCLOTOMIC_CHARACTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:B`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `g:B->B`]
    CYCLOTOMIC_CHARACTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:B`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `(f:B->B) o (g:B->B)`;
                 `ring_mul (integer_mod_ring n)
                   (cyclotomic_character (l:B ring) n (f:B->B))
                   (cyclotomic_character (l:B ring) n (g:B->B))`]
    CYCLOTOMIC_CHARACTER_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`unit_group(integer_mod_ring n)`;
                   `cyclotomic_character (l:B ring) n f`;
                   `cyclotomic_character (l:B ring) n g`] GROUP_MUL) THEN
    ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 UNIT_GROUP))];
    DISCH_THEN SUBST1_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(f:B->B) z = ring_pow l z (num_of_int(cyclotomic_character l n f))`;
    `(g:B->B) z = ring_pow l z (num_of_int(cyclotomic_character l n g))`;
    `cyclotomic_character (l:B ring) n f IN
     group_carrier(unit_group(integer_mod_ring n))`;
    `cyclotomic_character (l:B ring) n g IN
     group_carrier(unit_group(integer_mod_ring n))`] THEN
  SPEC_TAC(`cyclotomic_character (l:B ring) n (f:B->B)`,`c:int`) THEN
  SPEC_TAC(`cyclotomic_character (l:B ring) n (g:B->B)`,`d:int`) THEN
  ASM_SIMP_TAC[UNIT_GROUP_INTEGER_MOD_RING; IN_IMAGE; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:int`; `c:int`] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; INTEGER_MOD_RING; INT_OF_NUM_MUL;
              INT_OF_NUM_REM] THEN
  DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW
    (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RING_POW_POW; RING_POW_EQ_GEN] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let CYCLOTOMIC_CHARACTER_KERNEL = prove
 (`!(h:A->B) k l n z.
        field l /\ z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0)
        ==> group_kernel
             (galois_group(k,l) h,unit_group(integer_mod_ring n))
             (cyclotomic_character l n) =
            group_carrier
             (galois_group
               (subfield_generated l (z INSERT IMAGE h (ring_carrier k)),l)
               I)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
  ASM_SIMP_TAC[IN_GALOIS_GROUP_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[group_kernel; IN_ELIM_THM; UNIT_GROUP; FORALL_IN_INSERT;
              FORALL_IN_IMAGE; IN_GALOIS_GROUP] THEN
  MATCH_MP_TAC(TAUT
   `(p /\ q ==> (r <=> s)) ==> ((p /\ q /\ t) /\ r <=> p /\ q /\ s /\ t)`) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `f:B->B`;
                 `ring_1(integer_mod_ring n)`] CYCLOTOMIC_CHARACTER_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    MP_TAC(ISPEC `unit_group(integer_mod_ring n)` GROUP_ID) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 UNIT_GROUP)];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INTEGER_MOD_RING; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  MP_TAC(ISPECL [`l:B ring`; `z:B`; `1:num`] RING_POW_MOD_ORDER) THEN
  ASM_SIMP_TAC[RING_POW_1]);;

let CYCLOTOMIC_CHARACTER_CONTINUOUS = prove
 (`!(h:A->B) k l n z.
        integral_domain l /\ z IN ring_carrier l /\ ring_order l z = n /\
        ~(n = 0)
        ==> continuous_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              discrete_topology(group_carrier(unit_group(integer_mod_ring n))))
             (cyclotomic_character l n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES] THEN
  REWRITE_TAC[TOPSPACE_POINTWISE_TOPOLOGY] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `f:B->B`]
      CYCLOTOMIC_CHARACTER) THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM];
    ALL_TAC] THEN
  X_GEN_TAC `c:int` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
         cyclotomic_character l n f = c} =
    {f | f IN group_carrier(galois_group(k,l) h) /\
         f z = ring_pow l z (num_of_int c)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CYCLOTOMIC_CHARACTER_UNIQUE THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM];
    REWRITE_TAC[OPEN_IN_POINTWISE_TOPOLOGY_POINT]]);;

(* ------------------------------------------------------------------------- *)
(* Surjectivity. For l normal over k the character factors through the       *)
(* restriction onto Gal(k(z)/k), whose image in the units mod n is all of    *)
(* them iff [k(z):k] = phi(n); over Q this is the irreducibility of the      *)
(* cyclotomic polynomials, and for Q-bar every n has a primitive n-th root   *)
(* of unity (ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY).            *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ = prove
 (`!(h:A->B) k l n z.
        normal_extension(k,l) h /\ z IN ring_carrier l /\
        ring_order l z = n /\ ~(n = 0)
        ==> (group_epimorphism
              (galois_group(k,l) h,unit_group(integer_mod_ring n))
              (cyclotomic_character l n) <=>
             extension_degree
              (k,subfield_generated l (z INSERT IMAGE h (ring_carrier k))) h =
             phi n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `(z INSERT IMAGE (h:A->B) (ring_carrier k)) SUBSET
    ring_carrier(subfield_generated l (z INSERT IMAGE h (ring_carrier k)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:B) IN z INSERT IMAGE (h:A->B) (ring_carrier k)` THEN
    REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN STRIP_TAC THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension
     (k,subfield_generated l (z INSERT IMAGE h (ring_carrier k))) (h:A->B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_order (subfield_generated l (z INSERT IMAGE h (ring_carrier k))) z =
    n /\
    subfield_generated
     (subfield_generated l (z INSERT IMAGE h (ring_carrier k)))
     (z INSERT IMAGE (h:A->B) (ring_carrier k)) =
    subfield_generated l (z INSERT IMAGE h (ring_carrier k)) /\
    field(subfield_generated l (z INSERT IMAGE h (ring_carrier k))) /\
    ring_pow (subfield_generated l (z INSERT IMAGE h (ring_carrier k))) =
    ring_pow l /\
    ring_carrier(subfield_generated l (z INSERT IMAGE h (ring_carrier k)))
    subfield_of l /\
    subfield_generated l
     (ring_carrier(subfield_generated l (z INSERT IMAGE h (ring_carrier k)))) =
    subfield_generated l (z INSERT IMAGE h (ring_carrier k))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED;
                 SUBFIELD_SUBFIELD_GENERATED;
                 SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ring_order l (z:B)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC RING_ORDER_SUBFIELD_GENERATED THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `m = subfield_generated l (z INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  SUBGOAL_THEN `(z:B) IN ring_carrier m` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier k) SUBSET ring_carrier m`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow m (z:B) n = ring_1 m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN
    UNDISCH_TAC `ring_order l (z:B) = n` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[RING_POW_RING_ORDER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_epimorphism (galois_group(k,l) h,galois_group(k,m) (h:A->B))
     (\f x. if x IN ring_carrier m then f x else x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_carrier m:B->bool`]
                  GALOIS_GROUP_RESTRICTION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC GALOIS_IMP_NORMAL_EXTENSION THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `m:B ring`; `z:B`; `n:num`]
      CYCLOTOMIC_EXTENSION_ABELIAN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) h)
        ==> (\x. if x IN ring_carrier m then f x else x) IN
            group_carrier(galois_group(k,m) (h:A->B)) /\
            (\x. if x IN ring_carrier m then f x else x) z = f z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT1 o
      REWRITE_RULE[group_epimorphism; group_homomorphism; SUBSET;
                   FORALL_IN_IMAGE] o
      check (fun th -> is_binary "group_epimorphism" (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN group_carrier(modmul_group n) /\
          b IN group_carrier(modmul_group n) /\ (a == b) (mod n)
          ==> a = b`
  (LABEL_TAC "res") THENL
   [REWRITE_TAC[MODMUL_GROUP] THEN COND_CASES_TAC THEN
    REWRITE_TAC[IN_SING; IN_ELIM_THM] THEN MESON_TAC[CONG_IMP_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPEC `n:num` GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP) THEN
  ASM_REWRITE_TAC[GROUP_ISOMORPHISM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a. ring_pow l (z:B) (num_of_int(&a rem &n)) = ring_pow l z a`
  ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`l:B ring`; `z:B`] RING_POW_MOD_ORDER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral_domain(l:B ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `m:B ring`; `z:B`; `n:num`]
    CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `m:B ring`; `z:B`; `n:num`]
      CYCLOTOMIC_GALOIS_GROUP_MODMUL) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(B->B)->num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
    ASM_REWRITE_TAC[group_epimorphism] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GROUP_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(ACCEPT_TAC o CONJUNCT1 o
        GEN_REWRITE_RULE I [group_homomorphism]);
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&b rem &n IN group_carrier(unit_group(integer_mod_ring n))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        rhs(concl th) = `group_carrier(unit_group(integer_mod_ring n))`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `group_epimorphism
       (galois_group(k,l) (h:A->B),unit_group(integer_mod_ring n))
       (cyclotomic_character l n)` THEN
    REWRITE_TAC[group_epimorphism; EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE o SPEC `&b rem &n:int` o
      CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:B->B`
     (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(f:B->B) z = ring_pow l z b` ASSUME_TAC THENL
     [FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM o
        check (fun th -> concl th =
          `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
      MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `f:B->B`; `&b rem &n:int`]
        CYCLOTOMIC_CHARACTER_UNIQUE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ring_carrier(m:B ring)`)) (concl th) &&
      is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `g = \x. if x IN ring_carrier m then (f:B->B) x else x` THEN
    STRIP_TAC THEN EXISTS_TAC `g:B->B` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "res" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `group_monomorphism (galois_group(k,m) (h:A->B),
                                       modmul_group n) e` THEN
      REWRITE_TAC[group_monomorphism; group_homomorphism; SUBSET;
                  FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `z:B`] RING_POW_EQ_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `(g:B->B) z = ring_pow l z (e g)` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `g:B->B` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `e:(B->B)->num`)) (concl th) &&
        is_imp(snd(dest_forall(concl th))))) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "g" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(B->B)->num` (CONJUNCTS_THEN2 MP_TAC
    ASSUME_TAC)) THEN
  REWRITE_TAC[GROUP_ISOMORPHISM] THEN STRIP_TAC THEN
  REWRITE_TAC[GROUP_EPIMORPHISM_ALT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CYCLOTOMIC_CHARACTER_HOMOMORPHISM THEN
    EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[group_image; SUBSET; IN_IMAGE] THEN
  X_GEN_TAC `c:int` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?b. b IN group_carrier(modmul_group n) /\ &b rem &n = c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c IN group_carrier(unit_group(integer_mod_ring n))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) &&
      rhs(concl th) = `group_carrier(unit_group(integer_mod_ring n))`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. g IN group_carrier(galois_group(k,m) (h:A->B)) /\
        (e:(B->B)->num) g = b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `b IN group_carrier(modmul_group n)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) &&
      rhs(concl th) = `group_carrier(modmul_group n)`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
        (\x. if x IN ring_carrier m then f x else x) = g`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `group_epimorphism (galois_group(k,l) h,galois_group(k,m) (h:A->B))
       (\f x. if x IN ring_carrier m then f x else x)` THEN
    REWRITE_TAC[group_epimorphism; EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `g:B->B` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `f:B->B` THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM o
    check (fun th -> concl th =
      `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`; `z:B`; `f:B->B`; `c:int`]
    CYCLOTOMIC_CHARACTER_UNIQUE) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(f:B->B) z = g z` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `g:B->B`)) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:B->B) z = ring_pow l z (e g)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `g:B->B` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `e:(B->B)->num`)) (concl th) &&
      is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:int`)) THEN
  ASM_REWRITE_TAC[]);;

let CYCLOTOMIC_CHARACTER_EPIMORPHISM = prove
 (`!(l:A ring) n z.
        ring_char l = 0 /\
        normal_extension(subfield_generated l {ring_0 l},l) I /\
        z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0)
        ==> group_epimorphism
             (galois_group(subfield_generated l {ring_0 l},l) I,
              unit_group(integer_mod_ring n))
             (cyclotomic_character l n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `field(l:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated l {ring_0 l}:A ring`;
                 `l:A ring`; `n:num`; `z:A`]
    CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ) THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `number_field(subfield_generated l {z:A})` ASSUME_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC THEN
    ASM_REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2] THEN
    MATCH_MP_TAC RING_OF_INTEGERS_ALGEBRAIC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_POW_RING_ORDER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN ring_carrier(subfield_generated l {z})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subfield_generated l {z:A}`; `z:A`; `n:num`]
    CYCLOTOMIC_FIELD_DEGREE) THEN
  ASM_SIMP_TAC[RING_ORDER_SUBFIELD_GENERATED; PRIME_SUBFIELD_SUBFIELD_GENERATED;
               SUBFIELD_GENERATED_IDEMPOT_GEN; SING_SUBSET]);;

let ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER = prove
 (`!(k:A ring) n.
        algebraically_closed_field k /\ ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\ ~(n = 0)
        ==> group_epimorphism
             (galois_group(subfield_generated k {ring_0 k},k) I,
              unit_group(integer_mod_ring n))
             (cyclotomic_character k n) /\
            continuous_map
             (pointwise_topology
               (group_carrier
                 (galois_group(subfield_generated k {ring_0 k},k) I)),
              discrete_topology(group_carrier(unit_group(integer_mod_ring n))))
             (cyclotomic_character k n) /\
            !f x. f IN group_carrier
                        (galois_group(subfield_generated k {ring_0 k},k) I) /\
                  x IN ring_carrier k /\ ring_pow k x n = ring_1 k
                  ==> f x = ring_pow k x
                    (num_of_int(cyclotomic_character k n f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`]
    ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY) THEN
  ASM_REWRITE_TAC[NUMBER_RULE `((0:num) divides n) <=> n = 0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `field(k:A ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CYCLOTOMIC_CHARACTER_EPIMORPHISM THEN
    EXISTS_TAC `z:A` THEN
    ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION];
    MATCH_MP_TAC CYCLOTOMIC_CHARACTER_CONTINUOUS THEN
    EXISTS_TAC `z:A` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `z:A`; `f:A->A`]
      CYCLOTOMIC_CHARACTER) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM);
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]]);;
