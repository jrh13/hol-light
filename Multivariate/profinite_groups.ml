(* ========================================================================= *)
(* Topological groups and profinite groups.                                  *)
(*                                                                           *)
(*   topological_group G top = top is a topology on the carrier of G in      *)
(*                             which multiplication, from prod_topology top  *)
(*                             top, and inversion are continuous             *)
(*   profinite_group G top   = G is a compact Hausdorff topological group in *)
(*                             which every open set containing 1 contains an *)
(*                             open normal subgroup                          *)
(*                                                                           *)
(* Topological groups: translations and inversion are homeomorphisms         *)
(* (TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS), so translates of open and closed   *)
(* sets are open and closed (OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES,           *)
(* CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES); open subgroups are closed        *)
(* (CLOSED_IN_OPEN_SUBGROUP), closed subgroups of finite index are open      *)
(* (OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX) and a subgroup containing an open  *)
(* neighbourhood of 1 is open (OPEN_IN_SUBGROUP_NEIGHBOURHOOD); the closure  *)
(* of a subgroup is a subgroup, normal if the subgroup is                    *)
(* (SUBGROUP_OF_CLOSURE_OF, NORMAL_SUBGROUP_OF_CLOSURE_OF); a topological    *)
(* group is Hausdorff iff {1} is closed (HAUSDORFF_SPACE_TOPOLOGICAL_GROUP). *)
(* A homomorphism of topological groups is continuous iff it is continuous   *)
(* at 1 (CONTINUOUS_MAP_GROUP_HOMOMORPHISM), into a discrete group iff its   *)
(* kernel is open (CONTINUOUS_MAP_GROUP_HOMOMORPHISM_DISCRETE), and the      *)
(* kernel of a continuous homomorphism into a Hausdorff group is closed      *)
(* (CLOSED_IN_GROUP_KERNEL). Subgroups with the subspace topology, quotients *)
(* G/N with the quotient topology, images under continuous open epimorphisms *)
(* and products are topological groups (TOPOLOGICAL_GROUP_SUBGROUP,          *)
(* TOPOLOGICAL_GROUP_QUOTIENT_GROUP,                                         *)
(* TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE, TOPOLOGICAL_GROUP_PRODUCT_GROUP, *)
(* TOPOLOGICAL_GROUP_PROD_GROUP); G/N is discrete for N open and Hausdorff   *)
(* for N closed (QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP,                     *)
(* HAUSDORFF_SPACE_QUOTIENT_GROUP).                                          *)
(*                                                                           *)
(* Profinite groups: finite groups with the discrete topology are profinite  *)
(* (PROFINITE_GROUP_FINITE_DISCRETE); in a compact group the open subgroups  *)
(* are the closed subgroups of finite index                                  *)
(* (OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP), so G/U is finite for U open *)
(* normal (PROFINITE_GROUP_FINITE_QUOTIENT); closed subgroups and quotients  *)
(* by closed normal subgroups are profinite                                  *)
(* (PROFINITE_GROUP_CLOSED_SUBGROUP, PROFINITE_GROUP_QUOTIENT_GROUP), and so *)
(* is the image of a continuous epimorphism into a Hausdorff space, the map  *)
(* being open and a quotient map (PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM);   *)
(* products and inverse limits of profinite groups are profinite             *)
(* (PROFINITE_GROUP_PRODUCT_GROUP, PROFINITE_GROUP_INVERSE_LIMIT), for       *)
(* example the limits of the Z/n along divisibility, among them Z_p and the  *)
(* profinite completion of Z                                                 *)
(* (PROFINITE_GROUP_INVERSE_LIMIT_INTEGER_MOD_GROUP), and every profinite    *)
(* group is the limit of its finite quotients, as a group and as a space     *)
(* (PROFINITE_GROUP_INVERSE_LIMIT_QUOTIENTS). It suffices that the open      *)
(* subgroups form a base at 1 (PROFINITE_GROUP_OPEN_SUBGROUPS), and the      *)
(* profinite groups are the compact Hausdorff totally disconnected           *)
(* topological groups (PROFINITE_GROUP_TOTALLY_DISCONNECTED). A closed       *)
(* subgroup is the intersection of the open subgroups containing it, a       *)
(* closed normal subgroup that of the open normal subgroups containing it    *)
(* (PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS,                                  *)
(* PROFINITE_GROUP_CLOSED_NORMAL_SUBGROUP_INTERS).                           *)
(*                                                                           *)
(* Groups of permutations: a subgroup G of symmetric_group X, with the       *)
(* topology of pointwise convergence pointwise_topology G of                 *)
(* Multivariate/metric.ml, is a topological group                            *)
(* (TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY) in which the pointwise stabilizers *)
(* of finite subsets of X are open subgroups forming a base at 1             *)
(* (OPEN_IN_POINTWISE_STABILIZER,                                            *)
(* POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER,                              *)
(* OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP); if every orbit is finite and G is   *)
(* closed, or equivalently contains every permutation of X agreeing on each  *)
(* finite set with one of its members, G is profinite                        *)
(* (PROFINITE_GROUP_POINTWISE_TOPOLOGY,                                      *)
(* PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL). Galois groups are instances    *)
(* (Multivariate/infinite_galois.ml).                                        *)
(*                                                                           *)
(* References: Neukirch, Schmidt and Wingberg, Cohomology of Number Fields,  *)
(* I.1; Serre, Galois Cohomology, I.1.1; Ribes and Zalesskii, Profinite      *)
(* Groups, 2.1.                                                              *)
(* ========================================================================= *)

needs "Multivariate/metric.ml";;
needs "Library/grouptheory.ml";;
needs "Library/symmetric_group.ml";;

(* ------------------------------------------------------------------------- *)
(* Topological groups. Multiplication is continuous from prod_topology top   *)
(* top, with the pair split by FST and SND, and inversion is continuous.     *)
(* Translations x |-> a x, x |-> x a and inversion are homeomorphisms, so    *)
(* translates of open and closed sets are open and closed. The complement of *)
(* a subgroup is the union of the cosets other than the subgroup             *)
(* (SUBGROUP_COMPLEMENT_RIGHT_COSETS of Library/grouptheory.ml), so open     *)
(* subgroups are closed and closed subgroups of finite index are open; a     *)
(* subgroup is the union of the translates of any open neighbourhood of 1    *)
(* inside it, so it is open if it contains one. Closures of subgroups are    *)
(* subgroups, by the continuity of multiplication on the closure of h CROSS  *)
(* h (CLOSURE_OF_CROSS), and closures of normal subgroups are normal,        *)
(* conjugation being a homeomorphism. A topological group is Hausdorff iff   *)
(* {1} is closed, the diagonal being the preimage of 1 under                 *)
(* (x,y) |-> x y^-1.                                                         *)
(* ------------------------------------------------------------------------- *)

let topological_group = new_definition
 `topological_group (G:A group) (top:A topology) <=>
        topspace top = group_carrier G /\
        continuous_map (prod_topology top top,top)
                       (\z. group_mul G (FST z) (SND z)) /\
        continuous_map (top,top) (group_inv G)`;;

let CONTINUOUS_MAP_GROUP_MUL = prove
 (`!G (top:A topology) (top':B topology) f g.
        topological_group G top /\
        continuous_map (top',top) f /\ continuous_map (top',top) g
        ==> continuous_map (top',top) (\x. group_mul G (f x) (g x))`,
  REWRITE_TAC[topological_group] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. group_mul G ((f:B->A) x) (g x)) =
    (\z. group_mul G (FST z) (SND z)) o (\x. f x,g x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (top:A topology) top` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED]);;

let CONTINUOUS_MAP_GROUP_INV = prove
 (`!G (top:A topology) (top':B topology) f.
        topological_group G top /\ continuous_map (top',top) f
        ==> continuous_map (top',top) (\x. group_inv G (f x))`,
  REWRITE_TAC[topological_group] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. group_inv G ((f:B->A) x)) = group_inv G o f`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS = prove
 (`!G (top:A topology) a.
        topological_group G top /\ a IN group_carrier G
        ==> homeomorphic_map (top,top) (group_mul G a) /\
            homeomorphic_map (top,top) (\x. group_mul G x a) /\
            homeomorphic_map (top,top) (group_inv G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  SUBGOAL_THEN
   `!b. b IN group_carrier G
        ==> continuous_map (top,top) (group_mul G b) /\
            continuous_map (top,top) (\x:A. group_mul G x b)`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`G:A group`; `top:A topology`; `top:A topology`;
                     `\x:A. b:A`; `\x:A. x`] CONTINUOUS_MAP_GROUP_MUL);
      MP_TAC(ISPECL [`G:A group`; `top:A topology`; `top:A topology`;
                     `\x:A. x`; `\x:A. b:A`] CONTINUOUS_MAP_GROUP_MUL)] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `group_mul G (group_inv G a):A->A`;
    EXISTS_TAC `\x:A. group_mul G x (group_inv G a)`;
    EXISTS_TAC `group_inv G:A->A`] THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_INV_INV] THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL_LINV; GROUP_MUL_RINV;
               GROUP_MUL_LID; GROUP_INV; GROUP_MUL] THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL_LINV; GROUP_MUL_RINV;
               GROUP_MUL_RID; GROUP_INV]);;

let OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES = prove
 (`!G (top:A topology) a u.
        topological_group G top /\ a IN group_carrier G /\ open_in top u
        ==> open_in top (left_coset G a u) /\
            open_in top (right_coset G u a) /\
            open_in top (IMAGE (group_inv G) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `a:A`]
                TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
  ASM_REWRITE_TAC[LEFT_COSET_AS_IMAGE; RIGHT_COSET_AS_IMAGE] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_MAP_OPENNESS]);;

let CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES = prove
 (`!G (top:A topology) a c.
        topological_group G top /\ a IN group_carrier G /\ closed_in top c
        ==> closed_in top (left_coset G a c) /\
            closed_in top (right_coset G c a) /\
            closed_in top (IMAGE (group_inv G) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `a:A`]
                TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
  ASM_REWRITE_TAC[LEFT_COSET_AS_IMAGE; RIGHT_COSET_AS_IMAGE] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_MAP_CLOSEDNESS]);;

let CLOSED_IN_OPEN_SUBGROUP = prove
 (`!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G /\ open_in top h
        ==> closed_in top h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[closed_in] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUBGROUP_COMPLEMENT_RIGHT_COSETS) THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_DIFF] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]);;

let OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX = prove
 (`!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G /\ closed_in top h /\
        FINITE(group_cosets G h)
        ==> open_in top h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `h = topspace top DIFF (group_carrier G DIFF h:A->bool)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUBGROUP_COMPLEMENT_RIGHT_COSETS) THEN
  MATCH_MP_TAC CLOSED_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_DIFF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `group_cosets G (h:A->bool)` THEN
    ASM_REWRITE_TAC[group_cosets] THEN SET_TAC[];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES]]);;

let OPEN_IN_SUBGROUP_NEIGHBOURHOOD = prove
 (`!G (top:A topology) h w.
        topological_group G top /\ h subgroup_of G /\
        open_in top w /\ group_id G IN w /\ w SUBSET h
        ==> open_in top h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `h = UNIONS {left_coset G x w | x | (x:A) IN h}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_COSET_AS_IMAGE; IN_IMAGE] THEN
    X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `IMAGE (group_mul G y) (w:A->bool)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `group_id G:A` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[GROUP_MUL_RID; SUBSET];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`c:A->bool`; `x:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [IN_IMAGE]) THEN
      ASM_MESON_TAC[subgroup_of; SUBSET]];
    MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:A group`; `top:A topology`; `x:A`; `w:A->bool`]
                  OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET]]);;

let SUBGROUP_OF_CLOSURE_OF = prove
 (`!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G
        ==> (top closure_of h) subgroup_of G`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
  SUBGOAL_THEN `(h:A->bool) SUBSET top closure_of h` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[subgroup_of] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
    ASM SET_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `top:A topology`; `group_inv G:A->A`;
                   `h:A->bool`] CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `(t:A->bool) SUBSET u
      ==> IMAGE (f:A->A) s SUBSET t ==> !x. x IN s ==> f x IN u`) THEN
    MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`prod_topology (top:A topology) top`; `top:A topology`;
                   `\z. group_mul G (FST z) (SND z):A`;
                   `(h:A->bool) CROSS h`]
                  CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[CLOSURE_OF_CROSS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `top closure_of (IMAGE (\z. group_mul G (FST z) (SND z))
                            ((h:A->bool) CROSS h)) SUBSET
      top closure_of h`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MONO THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
      ASM_REWRITE_TAC[]]]);;

let NORMAL_SUBGROUP_OF_CLOSURE_OF = prove
 (`!G (top:A topology) h.
        topological_group G top /\ h normal_subgroup_of G
        ==> (top closure_of h) normal_subgroup_of G`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[normal_subgroup_of] THEN
  ASM_SIMP_TAC[SUBGROUP_OF_CLOSURE_OF] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `a:A`]
                TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[LEFT_COSET_AS_IMAGE; RIGHT_COSET_AS_IMAGE] THEN
  MP_TAC(ISPECL [`group_mul G a:A->A`; `top:A topology`; `top:A topology`;
                 `h:A->bool`] HOMEOMORPHIC_MAP_CLOSURE_OF) THEN
  MP_TAC(ISPECL [`\x:A. group_mul G x a`; `top:A topology`;
                 `top:A topology`; `h:A->bool`]
                HOMEOMORPHIC_MAP_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM LEFT_COSET_AS_IMAGE; GSYM RIGHT_COSET_AS_IMAGE] THEN
  ASM_MESON_TAC[normal_subgroup_of]);;

let TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY = prove
 (`!G:A group. topological_group G (discrete_topology(group_carrier G))`,
  GEN_TAC THEN
  REWRITE_TAC[topological_group; TOPSPACE_DISCRETE_TOPOLOGY;
              PROD_TOPOLOGY_DISCRETE_TOPOLOGY;
              CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  SIMP_TAC[GROUP_MUL; GROUP_INV]);;

let HAUSDORFF_SPACE_TOPOLOGICAL_GROUP = prove
 (`!G (top:A topology).
        topological_group G top
        ==> (hausdorff_space top <=> closed_in top {group_id G})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HAUSDORFF_IMP_T1_SPACE) THEN
    REWRITE_TAC[T1_SPACE_CLOSED_IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GROUP_ID];
    DISCH_TAC] THEN
  REWRITE_TAC[HAUSDORFF_SPACE_CLOSED_IN_DIAGONAL] THEN
  SUBGOAL_THEN
   `{(x,x) | x IN topspace top} =
    {z | z IN topspace(prod_topology top top) /\
         (\z. group_mul G (FST z) (group_inv G (SND z))) z IN
         {group_id G:A}}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; EXTENSION; FORALL_PAIR_THM;
                    IN_ELIM_THM; IN_CROSS; IN_SING; PAIR_EQ; FST; SND] THEN
    REWRITE_TAC[GSYM group_div] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `(x:A) IN group_carrier G /\ y IN group_carrier G` THEN
    ASM_SIMP_TAC[GROUP_DIV_EQ_ID] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_FST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_GROUP_INV THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_SND]]);;

(* ------------------------------------------------------------------------- *)
(* Isomorphisms and homomorphisms of topological groups. A group isomorphism *)
(* that is a homeomorphism transfers the structure. A homomorphism of        *)
(* topological groups is continuous iff it is continuous at 1: an open set w *)
(* around f(x) is f(x) times the open set f(x)^-1 w around 1, whose preimage *)
(* contains an open u around 1, and x u is open around x. So a homomorphism  *)
(* into a group with the discrete topology is continuous iff its kernel is   *)
(* open, and the kernel of a continuous homomorphism into a Hausdorff group  *)
(* is closed. An epimorphic image under a continuous open map is a           *)
(* topological group, the square of the map being a quotient map             *)
(* (CONTINUOUS_OPEN_IMP_QUOTIENT_MAP).                                       *)
(* ------------------------------------------------------------------------- *)

let TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM = prove
 (`!G H (top:A topology) (top':B topology) f.
        topological_group H top' /\ topspace top = group_carrier G /\
        group_isomorphism (G,H) f /\ homeomorphic_map (top,top') f
        ==> topological_group G top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->A` MP_TAC) THEN
  REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
  REWRITE_TAC[topological_group] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC
     `\z:A#A. (g:B->A) (group_mul H ((f:A->B)(FST z)) (f(SND z)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `group_mul H ((f:A->B) x) (f y) = f(group_mul G x y)`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:A) IN topspace top`; `(y:A) IN topspace top`] THEN
      ASM_SIMP_TAC[GROUP_MUL];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]];
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `\x. (g:B->A) (group_inv H ((f:A->B) x))` THEN CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `group_inv H ((f:A->B) x) = f(group_inv G x)`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:A) IN topspace top` THEN ASM_SIMP_TAC[GROUP_INV];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[]]]);;

let CONTINUOUS_MAP_GROUP_HOMOMORPHISM = prove
 (`!G H (top:A topology) (top':B topology) f.
        topological_group G top /\ topological_group H top' /\
        group_homomorphism(G,H) f
        ==> (continuous_map (top,top') f <=>
             !v. open_in top' v /\ group_id H IN v
                 ==> ?u. open_in top u /\ group_id G IN u /\
                         IMAGE f u SUBSET v)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [topological_group] o check ((=) t o concl)))
   [`topological_group G (top:A topology)`;
    `topological_group H (top':B topology)`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [group_homomorphism]) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `v:B->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `{x | x IN topspace top /\ (f:A->B) x IN v}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[GROUP_ID];
      SET_TAC[]];
    DISCH_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
  X_GEN_TAC `w:B->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) x IN group_carrier H` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `left_coset H (group_inv H ((f:A->B) x)) w`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`H:B group`; `top':B topology`;
                     `group_inv H ((f:A->B) x)`; `w:B->bool`]
                    OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
      ASM_SIMP_TAC[GROUP_INV];
      REWRITE_TAC[LEFT_COSET_AS_IMAGE; IN_IMAGE] THEN
      EXISTS_TAC `(f:A->B) x` THEN ASM_SIMP_TAC[GROUP_MUL_LINV]];
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET o
    check (fun th -> concl th = `open_in top (u:A->bool)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET o
    check (fun th -> concl th = `open_in top' (w:B->bool)`)) THEN
  EXISTS_TAC `left_coset G x (u:A->bool)` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`G:A group`; `top:A topology`; `x:A`; `u:A->bool`]
                  OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[LEFT_COSET_AS_IMAGE; IN_IMAGE] THEN
    EXISTS_TAC `group_id G:A` THEN ASM_SIMP_TAC[GROUP_MUL_RID];
    REWRITE_TAC[LEFT_COSET_AS_IMAGE; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN group_carrier G` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:A->bool) SUBSET topspace top` THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_MUL] THEN
    UNDISCH_TAC
     `IMAGE (f:A->B) u SUBSET left_coset H (group_inv H (f x)) w` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; LEFT_COSET_AS_IMAGE; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:B) IN group_carrier H` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:B->bool) SUBSET topspace top'` THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_INV; GROUP_MUL_RINV;
                 GROUP_MUL_LID]]);;

let CONTINUOUS_MAP_GROUP_HOMOMORPHISM_DISCRETE = prove
 (`!G H (top:A topology) (f:A->B).
        topological_group G top /\ group_homomorphism(G,H) f
        ==> (continuous_map (top,discrete_topology(group_carrier H)) f <=>
             open_in top (group_kernel (G,H) f))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `H:B group`; `top:A topology`;
                 `discrete_topology(group_carrier(H:B group))`; `f:A->B`]
                CONTINUOUS_MAP_GROUP_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [group_homomorphism]) THEN
  REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `{group_id H:B}`) THEN
    REWRITE_TAC[SING_SUBSET; IN_SING; GROUP_ID] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
    MAP_EVERY EXISTS_TAC [`G:A group`; `u:A->bool`] THEN
    ASM_SIMP_TAC[SUBGROUP_GROUP_KERNEL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> concl th = `open_in top (u:A->bool)`)) THEN
    UNDISCH_TAC `IMAGE (f:A->B) u SUBSET {group_id H}` THEN
    ASM_REWRITE_TAC[group_kernel] THEN SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `v:B->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `group_kernel (G,H) (f:A->B)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[GROUP_ID] THEN
    UNDISCH_TAC `group_id H IN (v:B->bool)` THEN SET_TAC[]]);;

let CLOSED_IN_GROUP_KERNEL = prove
 (`!G H (top:A topology) (top':B topology) f.
        topological_group G top /\ topological_group H top' /\
        hausdorff_space top' /\
        group_homomorphism(G,H) f /\ continuous_map (top,top') f
        ==> closed_in top (group_kernel (G,H) f)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [topological_group] o check ((=) t o concl)))
   [`topological_group G (top:A topology)`;
    `topological_group H (top':B topology)`] THEN
  SUBGOAL_THEN
   `group_kernel (G,H) (f:A->B) =
    {x | x IN topspace top /\ f x IN {group_id H}}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[group_kernel; IN_SING];
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[T1_SPACE_CLOSED_IN_SING; HAUSDORFF_IMP_T1_SPACE;
                  GROUP_ID]]);;

let TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE = prove
 (`!G H (top:A topology) (top':B topology) f.
        topological_group G top /\ topspace top' = group_carrier H /\
        group_epimorphism(G,H) f /\
        continuous_map (top,top') f /\ open_map (top,top') f
        ==> topological_group H top'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_epimorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
  SUBGOAL_THEN `IMAGE (f:A->B) (topspace top) = topspace top'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `quotient_map (top,top') (f:A->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IMP_QUOTIENT_MAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[topological_group] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `prod_topology (top:A topology) top`
                   CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
    EXISTS_TAC `\(x,y). (f:A->B) x,(f:A->B) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IMP_QUOTIENT_MAP THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_PROD; OPEN_MAP_PROD; ETA_AX;
                      TOPSPACE_PROD_TOPOLOGY; IMAGE_PAIRED_CROSS];
      MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC `(f:A->B) o (\z:A#A. group_mul G (FST z) (SND z))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                     o_THM];
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC(ISPEC `top:A topology` CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
    EXISTS_TAC `f:A->B` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `(f:A->B) o (group_inv G:A->A)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Subgroups, quotient groups and products. A subgroup with the subspace     *)
(* topology is a topological group. For n normal in G the preimage under     *)
(* right_coset G n of a set of cosets is its union (RIGHT_COSET_PREIMAGE),   *)
(* so the preimage of the image of an open u is the union of the translates  *)
(* a u for a in n and right_coset G n is an open map; its square is then a   *)
(* quotient map of product spaces, multiplication and inversion descend, and *)
(* G/n with the quotient topology is a topological group, discrete when n is *)
(* open and Hausdorff when n is closed. The open normal subgroups of G/n     *)
(* correspond to those of G containing n, with isomorphic quotients.         *)
(* Products and binary products of topological groups, with the product      *)
(* topologies, are topological groups.                                       *)
(* ------------------------------------------------------------------------- *)

let TOPOLOGICAL_GROUP_SUBGROUP = prove
 (`!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G
        ==> topological_group (subgroup_generated G h) (subtopology top h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subgroup_of] o
    check (fun th -> concl th = `(h:A->bool) subgroup_of G`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  REWRITE_TAC[topological_group; TOPSPACE_SUBTOPOLOGY;
              CONJUNCT2 SUBGROUP_GENERATED] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`subtopology top (h:A->bool)`;
                     `subtopology top (h:A->bool)`] CONTINUOUS_MAP_FST) THEN
      MP_TAC(ISPECL [`subtopology top (h:A->bool)`;
                     `subtopology top (h:A->bool)`] CONTINUOUS_MAP_SND) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; SUBSET;
                  FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS; IN_INTER;
                  FST; SND] THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      ASM_SIMP_TAC[]]]);;

let OPEN_MAP_RIGHT_COSET = prove
 (`!G (top:A topology) n.
        topological_group G top /\ n normal_subgroup_of G
        ==> open_map (top,quotient_topology (top,right_coset G n))
                     (right_coset G n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[open_map; OPEN_IN_QUOTIENT_TOPOLOGY] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`G:A group`; `n:A->bool`;
                 `IMAGE (right_coset G n) (u:A->bool)`]
                RIGHT_COSET_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_GROUP] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (right_coset G n) (u:A->bool)) =
    UNIONS (IMAGE (\a. left_coset G a u) n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_IMAGE; LEFT_COSET_AS_IMAGE; RIGHT_COSET_AS_IMAGE] THEN
    SET_TAC[];
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE]] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:A) IN group_carrier G` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]]);;

let TOPOLOGICAL_GROUP_QUOTIENT_GROUP = prove
 (`!G (top:A topology) n.
        topological_group G top /\ n normal_subgroup_of G
        ==> topological_group (quotient_group G n)
                              (quotient_topology (top,right_coset G n))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `n:A->bool`]
                OPEN_MAP_RIGHT_COSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `right_coset G (n:A->bool)`]
                QUOTIENT_MAP_QUOTIENT_TOPOLOGY) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `right_coset G (n:A->bool)`]
                CONTINUOUS_MAP_QUOTIENT_TOPOLOGY) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (right_coset G n) (group_carrier G) =
    group_carrier(quotient_group G (n:A->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[QUOTIENT_GROUP] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace(quotient_topology (top,right_coset G n)) =
    group_carrier(quotient_group G (n:A->bool))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_QUOTIENT_TOPOLOGY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[topological_group] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `prod_topology (top:A topology) top`
                   CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
    EXISTS_TAC `\(x,y). right_coset G n (x:A),right_coset G n (y:A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IMP_QUOTIENT_MAP THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_PROD; OPEN_MAP_PROD; ETA_AX;
                      TOPSPACE_PROD_TOPOLOGY; IMAGE_PAIRED_CROSS];
      MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC `right_coset G n o (\z:A#A. group_mul G (FST z) (SND z))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                     o_THM; QUOTIENT_GROUP_MUL];
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC(ISPEC `top:A topology` CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
    EXISTS_TAC `right_coset G (n:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `right_coset G n o (group_inv G:A->A)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[o_THM; QUOTIENT_GROUP_INV];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]]);;

let QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP = prove
 (`!G (top:A topology) u.
        topological_group G top /\ u normal_subgroup_of G /\ open_in top u
        ==> quotient_topology (top,right_coset G u) =
            discrete_topology(group_carrier(quotient_group G u))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN SUBGOAL_THEN
   `IMAGE (right_coset G u) (group_carrier G) =
    group_carrier(quotient_group G (u:A->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[QUOTIENT_GROUP] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_QUOTIENT_TOPOLOGY;
              OPEN_IN_DISCRETE_TOPOLOGY] THEN
  X_GEN_TAC `v:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v SUBSET group_carrier(quotient_group G (u:A->bool))` THEN
  ASM_SIMP_TAC[RIGHT_COSET_PREIMAGE] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN
  X_GEN_TAC `X:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?g:A. g IN group_carrier G /\ X = right_coset G u g`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `v SUBSET group_carrier(quotient_group G (u:A->bool))` THEN
    ASM_SIMP_TAC[QUOTIENT_GROUP] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]]);;

let OPEN_NORMAL_SUBGROUP_QUOTIENT_IMAGE = prove
 (`!G (top:A topology) N U.
        topological_group G top /\ N normal_subgroup_of G /\
        U normal_subgroup_of G /\ open_in top U /\ N SUBSET U
        ==> IMAGE (right_coset G N) U normal_subgroup_of quotient_group G N /\
            open_in (quotient_topology(top,right_coset G N))
                    (IMAGE (right_coset G N) U) /\
            quotient_group G U isomorphic_group
            quotient_group (quotient_group G N) (IMAGE (right_coset G N) U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(N:A->bool) subgroup_of G /\ (U:A->bool) subgroup_of G /\
    U SUBSET group_carrier G /\ topspace top = group_carrier G`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP; SUBGROUP_OF_IMP_SUBSET] THEN
    ASM_MESON_TAC[topological_group];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_QUOTIENT_GROUP_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[OPEN_IN_QUOTIENT_TOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    SUBGOAL_THEN
     `{x | x IN group_carrier G /\
           right_coset G N x IN IMAGE (right_coset G N) U} = (U:A->bool)`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:A) IN group_carrier G` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`G:A group`; `N:A->bool`; `x:A`; `y:A`]
             RIGHT_COSET_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `x:A = group_mul G (group_div G x y) y` SUBST1_TAC THENL
       [ASM_SIMP_TAC[group_div; GSYM GROUP_MUL_ASSOC; GROUP_INV;
                     GROUP_MUL_LINV; GROUP_MUL_RID];
        ALL_TAC] THEN
      MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM SET_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[]; EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]];
    ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    MATCH_MP_TAC THIRD_GROUP_ISOMORPHISM_THEOREM THEN ASM_REWRITE_TAC[]]);;

let OPEN_NORMAL_SUBGROUP_QUOTIENT_PREIMAGE = prove
 (`!G (top:A topology) N V.
        topological_group G top /\ N normal_subgroup_of G /\
        V normal_subgroup_of quotient_group G N /\
        open_in (quotient_topology(top,right_coset G N)) V
        ==> {x | x IN group_carrier G /\ right_coset G N x IN V}
            normal_subgroup_of G /\
            open_in top {x | x IN group_carrier G /\ right_coset G N x IN V} /\
            N SUBSET {x | x IN group_carrier G /\ right_coset G N x IN V} /\
            quotient_group G
              {x | x IN group_carrier G /\ right_coset G N x IN V}
            isomorphic_group quotient_group (quotient_group G N) V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(N:A->bool) subgroup_of G /\ N SUBSET group_carrier G /\
    topspace top = group_carrier G`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP; SUBGROUP_OF_IMP_SUBSET] THEN
    ASM_MESON_TAC[topological_group];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN
    EXISTS_TAC `quotient_group G (N:A->bool)` THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET;
                 GROUP_EPIMORPHISM_IMP_HOMOMORPHISM];
    UNDISCH_TAC
     `open_in (quotient_topology(top,right_coset G N)) (V:(A->bool)->bool)` THEN
    ASM_REWRITE_TAC[OPEN_IN_QUOTIENT_TOPOLOGY] THEN SIMP_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`G:A group`; `N:A->bool`; `x:A`]
           RIGHT_COSET_EQ_SUBGROUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`quotient_group G (N:A->bool)`; `V:(A->bool)->bool`]
      IN_SUBGROUP_ID) THEN
    ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP; QUOTIENT_GROUP];
    MATCH_MP_TAC FIRST_GROUP_ISOMORPHISM_THEOREM_GEN THEN
    EXISTS_TAC `right_coset G (N:A->bool)` THEN
    ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET]]);;

let HAUSDORFF_SPACE_QUOTIENT_GROUP = prove
 (`!G (top:A topology) n.
        topological_group G top /\ n normal_subgroup_of G /\ closed_in top n
        ==> hausdorff_space (quotient_topology (top,right_coset G n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `n:A->bool`]
    TOPOLOGICAL_GROUP_QUOTIENT_GROUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAUSDORFF_SPACE_TOPOLOGICAL_GROUP
                                            th]) THEN
  ASM_SIMP_TAC[QUOTIENT_GROUP; CLOSED_IN_QUOTIENT_TOPOLOGY] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `topspace top = group_carrier(G:A group)` ASSUME_TAC THENL
   [ASM_MESON_TAC[topological_group]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SING_SUBSET; IN_IMAGE] THEN EXISTS_TAC `group_id G:A` THEN
    ASM_SIMP_TAC[RIGHT_COSET_ID; GROUP_ID];
    SUBGOAL_THEN
     `{x | x IN group_carrier G /\ right_coset G n x IN {n}} = n:A->bool`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_SING] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[RIGHT_COSET_EQ_SUBGROUP; SUBSET]]);;

let TOPOLOGICAL_GROUP_PRODUCT_GROUP = prove
 (`!k (G:K->A group) (top:K->A topology).
        (!i. i IN k ==> topological_group (G i) (top i))
        ==> topological_group (product_group k G) (product_topology k top)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN k ==> topspace((top:K->A topology) i) = group_carrier(G i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[topological_group]; ALL_TAC] THEN
  REWRITE_TAC[topological_group; TOPSPACE_PRODUCT_TOPOLOGY; PRODUCT_GROUP] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cartesian_product; o_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN ASM_REWRITE_TAC[RESTRICTION] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:(K->A)#(K->A). FST x i) = (\y. y i) o FST`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC];
      SUBGOAL_THEN `(\x:(K->A)#(K->A). SND x i) = (\y. y i) o SND`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `product_topology k (top:K->A topology)` THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND;
                 CONTINUOUS_MAP_PRODUCT_PROJECTION];
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN ASM_REWRITE_TAC[RESTRICTION] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_GROUP_INV THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION]]);;

let TOPOLOGICAL_GROUP_PROD_GROUP = prove
 (`!(G:A group) (H:B group) top top'.
        topological_group G top /\ topological_group H top'
        ==> topological_group (prod_group G H) (prod_topology top top')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[topological_group] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; PROD_GROUP] THEN
  REWRITE_TAC[LAMBDA_PAIR] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL ORELSE
   MATCH_MP_TAC CONTINUOUS_MAP_GROUP_INV) THEN
  ASM_REWRITE_TAC[topological_group] THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  MESON_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]);;

(* ------------------------------------------------------------------------- *)
(* Profinite groups (Neukirch, Schmidt and Wingberg, Cohomology of Number    *)
(* Fields, (1.1.3) and (1.1.4); Serre, Galois Cohomology, I.1.1). The base   *)
(* condition is taken as the definition: every open set containing 1         *)
(* contains an open normal subgroup; so every open set around x contains a   *)
(* coset u x of an open normal u. Compactness bounds the index of an open    *)
(* subgroup, since its cosets form a disjoint open cover, so in a compact    *)
(* group the open subgroups are the closed subgroups of finite index, and    *)
(* G/u is finite for u open normal. Profiniteness is invariant under         *)
(* homeomorphic isomorphisms; closed subgroups (with the subspace topology,  *)
(* NORMAL_SUBGROUP_INTER_SUBGROUP_GENERATED giving the base) and open        *)
(* subgroups are profinite, and so is the quotient by a closed normal        *)
(* subgroup, compact as a quotient of G.                                     *)
(* ------------------------------------------------------------------------- *)

let profinite_group = new_definition
 `profinite_group (G:A group) (top:A topology) <=>
        topological_group G top /\ compact_space top /\ hausdorff_space top /\
        !w. open_in top w /\ group_id G IN w
            ==> ?u. u normal_subgroup_of G /\ open_in top u /\ u SUBSET w`;;

let PROFINITE_GROUP_NEIGHBOURHOOD_BASE = prove
 (`!G (top:A topology).
        profinite_group G top
        ==> neighbourhood_base_at (group_id G)
             (\u. u normal_subgroup_of G /\ open_in top u) top`,
  REWRITE_TAC[profinite_group; neighbourhood_base_at] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u:A->bool`; `u:A->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  ASM_MESON_TAC[normal_subgroup_of; subgroup_of]);;

let PROFINITE_GROUP_COSET_NEIGHBOURHOOD = prove
 (`!G (top:A topology) w x.
        profinite_group G top /\ open_in top w /\ x IN w
        ==> ?u. u normal_subgroup_of G /\ open_in top u /\
                right_coset G u x SUBSET w`,
  REWRITE_TAC[profinite_group] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `left_coset G (group_inv G x) (w:A->bool)`) THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `group_inv G x:A`;
                 `w:A->bool`] OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
  ASM_SIMP_TAC[GROUP_INV] THEN DISCH_THEN(K ALL_TAC) THEN ANTS_TAC THENL
   [REWRITE_TAC[LEFT_COSET_AS_IMAGE; IN_IMAGE] THEN EXISTS_TAC `x:A` THEN
    ASM_SIMP_TAC[GROUP_MUL_LINV];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT2 o
    GEN_REWRITE_RULE I [normal_subgroup_of]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `u SUBSET left_coset G (group_inv G x) (w:A->bool)` THEN
  REWRITE_TAC[LEFT_COSET_AS_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:A) IN group_carrier G` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL_RINV; GROUP_MUL_LID; GROUP_INV]);;

let PROFINITE_GROUP_FINITE_DISCRETE = prove
 (`!G:A group.
        FINITE(group_carrier G)
        ==> profinite_group G (discrete_topology(group_carrier G))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[profinite_group; TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY;
                  COMPACT_SPACE_DISCRETE_TOPOLOGY;
                  HAUSDORFF_SPACE_DISCRETE_TOPOLOGY] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `{group_id G:A}` THEN
  ASM_REWRITE_TAC[TRIVIAL_NORMAL_SUBGROUP_OF; OPEN_IN_DISCRETE_TOPOLOGY;
                  SING_SUBSET; GROUP_ID]);;

let COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX = prove
 (`!G (top:A topology) h.
        topological_group G top /\ compact_space top /\
        h subgroup_of G /\ open_in top h
        ==> FINITE(group_cosets G h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_cosets G (h:A->bool)` o CONJUNCT2 o
    GEN_REWRITE_RULE I [compact_in] o GEN_REWRITE_RULE I [compact_space]) THEN
  ASM_SIMP_TAC[group_cosets; FORALL_IN_GSPEC; UNIONS_RIGHT_COSETS;
               SUBSET_REFL] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:A group`; `top:A topology`; `x:A`; `h:A->bool`]
                  OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `v:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  UNDISCH_TAC `group_carrier G SUBSET UNIONS (v:(A->bool)->bool)` THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:A. y IN group_carrier G /\ c = right_coset G h y`
  (X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `(v:(A->bool)->bool) SUBSET
                 {right_coset G h x | x | (x:A) IN group_carrier G}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `right_coset G h (x:A) = right_coset G h y`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`; `x:A`; `y:A`] RIGHT_COSETS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `x:A` THEN ASM_SIMP_TAC[IN_RIGHT_COSET_SELF]);;

let OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP = prove
 (`!G (top:A topology) h.
        topological_group G top /\ compact_space top /\ h subgroup_of G
        ==> (open_in top h <=> closed_in top h /\ FINITE(group_cosets G h))`,
  MESON_TAC[CLOSED_IN_OPEN_SUBGROUP; COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX;
            OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX]);;

let PROFINITE_GROUP_FINITE_QUOTIENT = prove
 (`!G (top:A topology) u.
        profinite_group G top /\ u normal_subgroup_of G /\ open_in top u
        ==> FINITE(group_carrier(quotient_group G u))`,
  SIMP_TAC[QUOTIENT_GROUP_CARRIER; profinite_group] THEN
  MESON_TAC[COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX;
            NORMAL_SUBGROUP_IMP_SUBGROUP]);;

let OPEN_NORMAL_SUBGROUP_INTERS = prove
 (`!G (top:A topology) f.
        topological_group G top /\ FINITE f /\
        (!u. u IN f ==> u normal_subgroup_of G /\ open_in top u)
        ==> (group_carrier G INTER INTERS f) normal_subgroup_of G /\
            open_in top (group_carrier G INTER INTERS f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN REWRITE_TAC[GSYM INTERS_INSERT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_OF_INTERS;
    MATCH_MP_TAC OPEN_IN_INTERS] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; NOT_INSERT_EMPTY; FORALL_IN_INSERT] THEN
  ASM_MESON_TAC[CARRIER_NORMAL_SUBGROUP_OF; OPEN_IN_TOPSPACE]);;

let PROFINITE_GROUP_HOMEOMORPHIC_ISOMORPHISM = prove
 (`!G H (top:A topology) (top':B topology) f.
        profinite_group H top' /\ topspace top = group_carrier G /\
        group_isomorphism (G,H) f /\ homeomorphic_map (top,top') f
        ==> profinite_group G top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
  SUBGOAL_THEN `topological_group G (top:A topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM THEN
    MAP_EVERY EXISTS_TAC [`H:B group`; `top':B topology`; `f:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  REWRITE_TAC[profinite_group] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP HOMEOMORPHIC_COMPACT_SPACE th;
                MATCH_MP HOMEOMORPHIC_HAUSDORFF_SPACE th]) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:A->B) w`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHIC_MAP_OPENNESS; OPEN_IN_SUBSET];
      SUBGOAL_THEN `group_id H = (f:A->B)(group_id G)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN group_carrier G /\ (f:A->B) x IN u}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN
    EXISTS_TAC `H:B group` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`f:A->B`; `top:A topology`; `top':B topology`;
                   `u:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->B) x IN IMAGE f w` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:A) = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]);;

let PROFINITE_GROUP_CLOSED_SUBGROUP = prove
 (`!G (top:A topology) h.
        profinite_group G top /\ h subgroup_of G /\ closed_in top h
        ==> profinite_group (subgroup_generated G h) (subtopology top h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[profinite_group] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[TOPOLOGICAL_GROUP_SUBGROUP; HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:A->bool` THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; CONJUNCT2 SUBGROUP_GENERATED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:A->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:A->bool) INTER u` THEN
  ASM_SIMP_TAC[NORMAL_SUBGROUP_INTER_SUBGROUP_GENERATED] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM SET_TAC[]]);;

let PROFINITE_GROUP_OPEN_SUBGROUP = prove
 (`!G (top:A topology) h.
        profinite_group G top /\ h subgroup_of G /\ open_in top h
        ==> profinite_group (subgroup_generated G h) (subtopology top h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_CLOSED_SUBGROUP THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_OPEN_SUBGROUP THEN
  EXISTS_TAC `G:A group` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [profinite_group]));;

let PROFINITE_GROUP_QUOTIENT_GROUP = prove
 (`!G (top:A topology) n.
        profinite_group G top /\ n normal_subgroup_of G /\ closed_in top n
        ==> profinite_group (quotient_group G n)
                            (quotient_topology (top,right_coset G n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[profinite_group] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  ASM_SIMP_TAC[TOPOLOGICAL_GROUP_QUOTIENT_GROUP;
               HAUSDORFF_SPACE_QUOTIENT_GROUP] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `top:A topology` COMPACT_SPACE_QUOTIENT_MAP_IMAGE) THEN
    EXISTS_TAC `right_coset G (n:A->bool)` THEN
    ASM_REWRITE_TAC[QUOTIENT_MAP_QUOTIENT_TOPOLOGY];
    ALL_TAC] THEN
  X_GEN_TAC `w:(A->bool)->bool` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP QUOTIENT_GROUP_ID th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [OPEN_IN_QUOTIENT_TOPOLOGY] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{x | x IN group_carrier G /\ right_coset G n (x:A) IN w}`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[GROUP_ID; RIGHT_COSET_ID]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (right_coset G n) (u:A->bool)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE THEN
    EXISTS_TAC `G:A group` THEN ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET];
    MP_TAC(ISPECL [`G:A group`; `top:A topology`; `n:A->bool`]
                  OPEN_MAP_RIGHT_COSET) THEN
    ASM_REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Continuous epimorphisms, total disconnectedness and closed subgroups. A   *)
(* continuous epimorphism f from a profinite group onto a group with a       *)
(* Hausdorff topology is a closed map (CONTINUOUS_IMP_CLOSED_MAP), hence a   *)
(* quotient map, and an open map, since the preimage of f(u) is the union of *)
(* the translates u k for k in the kernel; so the image is profinite. In a   *)
(* compact topological group a closed and open set k containing 1 contains   *)
(* an open subgroup: by compactness of k and the continuity of               *)
(* multiplication at the points (x,1), some open w around 1 has k w SUBSET   *)
(* k, and the elements g with k g and k g^-1 inside k form a subgroup inside *)
(* k containing w INTER w^-1. With the criterion that open subgroups suffice *)
(* for the base (the core of an open subgroup h, the kernel of the action on *)
(* its finitely many left cosets, is an open normal subgroup inside h) and   *)
(* the theorem of Wilder that a compact component of a locally compact       *)
(* Hausdorff space has a base of closed and open neighbourhoods              *)
(* (WILDER_LOCALLY_COMPACT_COMPONENT_THM), this gives the characterization   *)
(* of profinite groups as the compact Hausdorff totally disconnected         *)
(* topological groups; the converse holds since cosets of open subgroups are *)
(* closed and open. A point outside a closed subgroup h lies outside h u for *)
(* some open normal u, so a closed subgroup is the intersection of the open  *)
(* subgroups containing it, and a closed normal subgroup that of the open    *)
(* normal subgroups containing it.                                           *)
(* ------------------------------------------------------------------------- *)

let PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM = prove
 (`!G H (top:A topology) (top':B topology) f.
        profinite_group G top /\ hausdorff_space top' /\
        topspace top' = group_carrier H /\
        group_epimorphism(G,H) f /\ continuous_map (top,top') f
        ==> open_map (top,top') f /\ quotient_map (top,top') f /\
            profinite_group H top'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_epimorphism])
  THEN FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [group_homomorphism])
  THEN SUBGOAL_THEN `quotient_map (top,top') (f:A->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP THEN
    ASM_SIMP_TAC[CONTINUOUS_IMP_CLOSED_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_map (top,top') (f:A->B)` ASSUME_TAC THENL
   [REWRITE_TAC[open_map] THEN X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o SPEC `IMAGE (f:A->B) u` o CONJUNCT2 o
      GEN_REWRITE_RULE I [quotient_map]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `{x | x IN topspace top /\ (f:A->B) x IN IMAGE f u} =
      UNIONS (IMAGE (right_coset G u) (group_kernel (G,H) f))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE;
                  RIGHT_COSET_AS_IMAGE; IN_IMAGE; group_kernel] THEN
      X_GEN_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
        SUBGOAL_THEN `(y:A) IN group_carrier G` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `group_mul G (group_inv G y) x:A` THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC[GROUP_MUL; GROUP_INV];
          ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GROUP_MUL_LINV];
          EXISTS_TAC `y:A` THEN
          ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_INV; GROUP_MUL_RINV;
                       GROUP_MUL_LID]];
        DISCH_THEN(X_CHOOSE_THEN `k:A` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
          (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
        SUBGOAL_THEN `(y:A) IN group_carrier G` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC[GROUP_MUL];
          EXISTS_TAC `y:A` THEN ASM_SIMP_TAC[GROUP_MUL_RID]]];
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[profinite_group] THEN
  SUBGOAL_THEN `topological_group H (top':B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`G:A group`; `top:A topology`; `f:A->B`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `top:A topology` COMPACT_SPACE_QUOTIENT_MAP_IMAGE) THEN
    EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:B->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{x | x IN topspace top /\ (f:A->B) x IN w}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[GROUP_ID]];
    DISCH_THEN(X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `IMAGE (f:A->B) n` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE THEN
    EXISTS_TAC `G:A group` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `open_map (top,top') (f:A->B)` THEN
    REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP = prove
 (`!G (top:A topology) k.
        topological_group G top /\ compact_space top /\
        open_in top k /\ closed_in top k /\ group_id G IN k
        ==> ?h. h subgroup_of G /\ open_in top h /\ h SUBSET k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET o
    check (fun th -> concl th = `open_in top (k:A->bool)`)) THEN
  SUBGOAL_THEN
   `!x. ?a b. x IN k
              ==> open_in top a /\ open_in top b /\ x IN a /\
                  group_id G IN b /\
                  !y z:A. y IN a /\ z IN b ==> group_mul G y z IN k`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z. group_mul G (FST z) (SND z):A`;
                   `prod_topology (top:A topology) top`; `top:A topology`;
                   `k:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[OPEN_IN_PROD_TOPOLOGY_ALT] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `group_id G:A`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_ID; GROUP_MUL_RID] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
    MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a:A->A->bool`; `b:A->A->bool`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact_in top (k:A->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_COMPACT_SPACE]; ALL_TAC] THEN
  REWRITE_TAC[compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (a:A->A->bool) k` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:A->A->bool`; `k:A->bool`; `v:(A->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `k SUBSET UNIONS (v:(A->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `w = INTERS (topspace (top:A topology) INSERT IMAGE (b:A->A->bool) f)` THEN
  SUBGOAL_THEN
   `open_in top (w:A->bool) /\ group_id G IN w /\
    !y z. y IN k /\ z IN w ==> group_mul G y z IN k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTERS THEN
      ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
      REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; OPEN_IN_TOPSPACE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[INTERS_INSERT; IN_INTER; INTERS_IMAGE; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[GROUP_ID] THEN ASM_MESON_TAC[SUBSET];
      MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN
      REWRITE_TAC[INTERS_INSERT; IN_INTER; INTERS_IMAGE; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `k SUBSET UNIONS (IMAGE (a:A->A->bool) f)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `a:A->A->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN k ==> y IN group_carrier G` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `h = {g:A | g IN group_carrier G /\
               !y. y IN k ==> group_mul G y g IN k /\
                              group_mul G y (group_inv G g) IN k}` THEN
  SUBGOAL_THEN `(h:A->bool) subgroup_of G` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    REWRITE_TAC[subgroup_of; SUBSET; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[];
      REWRITE_TAC[GROUP_ID];
      ASM_SIMP_TAC[GROUP_ID; GROUP_MUL_RID; GROUP_INV_ID];
      X_GEN_TAC `g:A` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[GROUP_INV; GROUP_INV_INV];
      MAP_EVERY X_GEN_TAC [`g:A`; `g':A`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[GROUP_MUL; GROUP_INV_MUL; GROUP_INV] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_INV; GROUP_MUL]];
    ALL_TAC] THEN
  EXISTS_TAC `h:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
    EXISTS_TAC `G:A group` THEN
    EXISTS_TAC `(w:A->bool) INTER IMAGE (group_inv G) w` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`G:A group`; `top:A topology`; `group_id G:A`;
                     `w:A->bool`] OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
      ASM_SIMP_TAC[GROUP_ID];
      REWRITE_TAC[IN_INTER; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `group_id G:A` THEN ASM_REWRITE_TAC[GROUP_INV_ID];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET o
        check (fun th -> concl th = `open_in top (w:A->bool)`)) THEN
      EXPAND_TAC "h" THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `g:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:A) IN group_carrier G` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[GROUP_INV; GROUP_INV_INV] THEN ASM SET_TAC[]];
    EXPAND_TAC "h" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `g:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `group_id G:A`) THEN
    ASM_SIMP_TAC[GROUP_MUL_LID]]);;

let PROFINITE_GROUP_OPEN_SUBGROUPS = prove
 (`!G (top:A topology).
        profinite_group G top <=>
        topological_group G top /\ compact_space top /\ hausdorff_space top /\
        !w. open_in top w /\ group_id G IN w
            ==> ?h. h subgroup_of G /\ open_in top h /\ h SUBSET w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[profinite_group] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c ==> (p <=> q)) ==> (a /\ b /\ c /\ p <=> a /\ b /\ c /\ q)`)
  THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `w:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A->bool`) THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP];
    DISCH_THEN(X_CHOOSE_THEN `h:A->bool` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`]
                GROUP_ACTION_LEFT_COSET_MULTIPLICATION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = {left_coset G x h | x | x IN group_carrier (G:A group)}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(h:A->bool) IN L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `group_id G:A` THEN ASM_SIMP_TAC[GROUP_ID; LEFT_COSET_ID];
    ALL_TAC] THEN
  EXISTS_TAC
   `{g | g IN group_carrier G /\
         !c. c IN L ==> (IMAGE o group_mul (G:A group)) g c = c}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NORMAL_SUBGROUP_ACTION_KERNEL THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GROUP_ACTION_KERNEL_POINTWISE] THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTERS THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      MP_TAC(ISPECL [`G:A group`; `h:A->bool`]
                    CARD_EQ_LEFT_COSETS_GROUP_COSETS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP CARD_FINITE_CONG) THEN
      MATCH_MP_TAC COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "L" THEN REWRITE_TAC[FORALL_IN_GSPEC; ETA_AX] THEN
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION] THEN
      SUBGOAL_THEN
       `IMAGE (group_conjugation G a) h =
        right_coset G (left_coset G a h) (group_inv G (a:A))`
      SUBST1_TAC THENL
       [REWRITE_TAC[LEFT_COSET_AS_IMAGE; RIGHT_COSET_AS_IMAGE; GSYM IMAGE_o]
        THEN MATCH_MP_TAC(SET_RULE
         `(!x:A. x IN s ==> (f:A->A) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        X_GEN_TAC `k:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(k:A) IN group_carrier G` ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
        ASM_SIMP_TAC[o_THM; group_conjugation; GROUP_MUL_ASSOC; GROUP_INV];
        ASM_SIMP_TAC[OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES; GROUP_INV]]];
    TRANS_TAC SUBSET_TRANS `h:A->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `g:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `group_id G:A` THEN
    ASM_SIMP_TAC[GROUP_MUL_RID; IN_SUBGROUP_ID]]);;

let PROFINITE_GROUP_TOTALLY_DISCONNECTED = prove
 (`!G (top:A topology).
        profinite_group G top <=>
        topological_group G top /\ compact_space top /\ hausdorff_space top /\
        !x. x IN topspace top ==> connected_component_of top x = {x}`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN connected_component_of top x` ASSUME_TAC THENL
     [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SING_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:A group`; `top:A topology`; `topspace top DIFF {y:A}`;
                   `x:A`] PROFINITE_GROUP_COSET_NEIGHBOURHOOD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
        ASM_MESON_TAC[T1_SPACE_CLOSED_IN_SING; HAUSDORFF_IMP_T1_SPACE];
        REWRITE_TAC[IN_DIFF; IN_SING] THEN ASM_MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `connected_component_of top (x:A)`;
                   `right_coset G u (x:A)`] CONNECTED_IN_CLOPEN_CASES) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`G:A group`; `top:A topology`; `x:A`; `u:A->bool`]
                      CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
        ASM_MESON_TAC[CLOSED_IN_OPEN_SUBGROUP];
        MP_TAC(ISPECL [`G:A group`; `top:A topology`; `x:A`; `u:A->bool`]
                      OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q /\ (p ==> r) ==> p \/ q ==> r`) THEN CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:A` THEN ASM_SIMP_TAC[IN_RIGHT_COSET_SELF];
      UNDISCH_TAC `right_coset G u x SUBSET topspace top DIFF {y:A}` THEN
      UNDISCH_TAC `(y:A) IN connected_component_of top x` THEN SET_TAC[]];
    STRIP_TAC THEN REWRITE_TAC[PROFINITE_GROUP_OPEN_SUBGROUPS] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:A->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group]) THEN
    SUBGOAL_THEN `(group_id G:A) IN topspace top` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GROUP_ID]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `{group_id G:A}`; `w:A->bool`]
                  WILDER_LOCALLY_COMPACT_COMPONENT_THM) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_LOCALLY_COMPACT_SPACE; SING_SUBSET] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `connected_component_of top (group_id G:A) =
                      {group_id G}` (SUBST1_TAC o SYM) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF]];
        MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
        ASM_REWRITE_TAC[SING_SUBSET; FINITE_SING]];
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
       (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC))] THEN
    MP_TAC(ISPECL [`G:A group`; `top:A topology`; `u:A->bool`]
                  COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `u = topspace top DIFF (v:A->bool)` SUBST1_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`DISJOINT (u:A->bool) v`;
            `(u:A->bool) UNION v = topspace top`] THEN
          SET_TAC[];
          ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE]];
        UNDISCH_TAC `{group_id G:A} SUBSET u` THEN SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:A->bool` THEN
      UNDISCH_TAC `(u:A->bool) SUBSET w` THEN SET_TAC[]]]);;

let PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION = prove
 (`!G (top:A topology) h x.
        profinite_group G top /\ closed_in top h /\
        x IN group_carrier G /\ ~(x IN h)
        ==> ?u. u normal_subgroup_of G /\ open_in top u /\
                ~(x IN group_setmul G h u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`;
                 `topspace top DIFF h:A->bool`; `x:A`]
                PROFINITE_GROUP_COSET_NEIGHBOURHOOD) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_GROUP_SETMUL; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `(a:A) IN group_carrier G /\ (b:A) IN group_carrier G`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN right_coset G u x` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT2 o
      GEN_REWRITE_RULE I [normal_subgroup_of]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LEFT_COSET_AS_IMAGE; IN_IMAGE] THEN
    EXISTS_TAC `group_inv G b:A` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL_RINV; GROUP_MUL_RID;
                   GROUP_INV];
      ASM_MESON_TAC[IN_SUBGROUP_INV]];
    ASM SET_TAC[]]);;

let PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS = prove
 (`!G (top:A topology) h.
        profinite_group G top /\ h subgroup_of G /\ closed_in top h
        ==> INTERS {u | u subgroup_of G /\ open_in top u /\ h SUBSET u} = h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUBSET_INTERS; IN_ELIM_THM]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_THEN(LABEL_TAC "x") THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [profinite_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [topological_group]) THEN
  SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
   [USE_THEN "x" MATCH_MP_TAC THEN REWRITE_TAC[CARRIER_SUBGROUP_OF] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `topspace top = group_carrier (G:A group)`)) THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_SUBSET];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `h:A->bool`; `x:A`]
                PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  SUBGOAL_THEN
   `group_setmul G h u subgroup_of G /\
    open_in top (group_setmul G h u) /\
    (h:A->bool) SUBSET group_setmul G h u`
  MP_TAC THENL
   [ASM_SIMP_TAC[GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT; GROUP_SETMUL_INC] THEN
    MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
    MAP_EVERY EXISTS_TAC [`G:A group`; `u:A->bool`] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT; GROUP_SETMUL_INC;
                 IN_SUBGROUP_ID];
    ASM_MESON_TAC[]]);;

let PROFINITE_GROUP_CLOSED_NORMAL_SUBGROUP_INTERS = prove
 (`!G (top:A topology) h.
        profinite_group G top /\ h normal_subgroup_of G /\ closed_in top h
        ==> INTERS {u | u normal_subgroup_of G /\ open_in top u /\
                        h SUBSET u} = h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUBSET_INTERS; IN_ELIM_THM]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_THEN(LABEL_TAC "x") THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [profinite_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [topological_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP o
    check (fun th -> concl th = `(h:A->bool) normal_subgroup_of G`)) THEN
  SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
   [USE_THEN "x" MATCH_MP_TAC THEN REWRITE_TAC[CARRIER_NORMAL_SUBGROUP_OF] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `topspace top = group_carrier (G:A group)`)) THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_SUBSET];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `top:A topology`; `h:A->bool`; `x:A`]
                PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP o
    check (fun th -> concl th = `(u:A->bool) normal_subgroup_of G`)) THEN
  SUBGOAL_THEN
   `group_setmul G h u normal_subgroup_of G /\
    open_in top (group_setmul G h u) /\
    (h:A->bool) SUBSET group_setmul G h u`
  MP_TAC THENL
   [ASM_SIMP_TAC[GROUP_SETMUL_NORMAL_SUBGROUP; GROUP_SETMUL_INC] THEN
    MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
    MAP_EVERY EXISTS_TAC [`G:A group`; `u:A->bool`] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT; GROUP_SETMUL_INC;
                 IN_SUBGROUP_ID];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Products and inverse limits. A product of profinite groups is profinite:  *)
(* it is compact by Tychonoff (COMPACT_SPACE_PRODUCT_TOPOLOGY), and a basic  *)
(* open set around 1 restricts finitely many coordinates, so it contains a   *)
(* product of open normal subgroups proper only in those coordinates. The    *)
(* inverse limit inverse_limit_group k le G f of Library/grouptheory.ml is,  *)
(* for profinite G i and continuous f i j, closed in the product, an         *)
(* intersection of equalizers of maps into Hausdorff spaces, hence profinite *)
(* with the subspace topology. In particular the limits of the groups Z/n i  *)
(* along divisibility are profinite: for example the p-adic integers Z_p =   *)
(* lim Z/p^n (k = (:num), le = (<=), n i = p EXP i, for p nonzero) and the   *)
(* profinite completion of Z (k the nonzero numbers, le = (divides), n = I). *)
(* Conversely a profinite group is the limit of its finite quotients G/u     *)
(* over the open normal subgroups u ordered by reverse inclusion, as a group *)
(* and, with the product of the discrete topologies, as a space: g |-> (u    *)
(* g)_u is injective since G is Hausdorff and the u form a base at 1, onto   *)
(* since a compatible family of cosets, each closed, has the finite          *)
(* intersection property in the compact G, and a continuous bijection from a *)
(* compact space onto a Hausdorff one is a homeomorphism                     *)
(* (CONTINUOUS_IMP_HOMEOMORPHIC_MAP).                                        *)
(* ------------------------------------------------------------------------- *)

let PROFINITE_GROUP_PRODUCT_GROUP = prove
 (`!k (G:I->A group) (top:I->A topology).
        (!i. i IN k ==> profinite_group (G i) (top i))
        ==> profinite_group (product_group k G) (product_topology k top)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[profinite_group] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_GROUP_PRODUCT_GROUP THEN
    ASM_MESON_TAC[profinite_group];
    REWRITE_TAC[COMPACT_SPACE_PRODUCT_TOPOLOGY] THEN DISJ2_TAC THEN
    ASM_MESON_TAC[profinite_group];
    REWRITE_TAC[HAUSDORFF_SPACE_PRODUCT_TOPOLOGY] THEN DISJ2_TAC THEN
    ASM_MESON_TAC[profinite_group];
    ALL_TAC] THEN
  X_GEN_TAC `w:(I->A)->bool` THEN REWRITE_TAC[PRODUCT_GROUP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [OPEN_IN_PRODUCT_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `RESTRICTION k (\i. group_id((G:I->A group) i))`)
  THEN ASM_REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:I->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i IN k
        ==> ?v. v normal_subgroup_of (G:I->A group) i /\
                open_in ((top:I->A topology) i) v /\ v SUBSET u i /\
                (u i = topspace(top i) ==> v = group_carrier(G i))`
  MP_TAC THENL
   [X_GEN_TAC `i:I` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:I` o check (fun th ->
      can (find_term (fun t -> is_const t &&
                      fst(dest_const t) = "profinite_group")) (concl th)))
    THEN
    ASM_REWRITE_TAC[profinite_group] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(u:I->A->bool) i = topspace((top:I->A topology) i)` THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `group_carrier((G:I->A group) i)` THEN
      ASM_MESON_TAC[CARRIER_NORMAL_SUBGROUP_OF; OPEN_IN_TOPSPACE;
                    topological_group; SUBSET_REFL];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `v:I->A->bool` o
      REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  EXISTS_TAC `cartesian_product k (v:I->A->bool)` THEN
  ASM_SIMP_TAC[CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_CARTESIAN_PRODUCT_GEN] THEN DISJ2_TAC THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      FINITE_SUBSET) o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "FINITE"))
            (concl th))) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[topological_group;
      profinite_group];
    TRANS_TAC SUBSET_TRANS `cartesian_product k (u:I->A->bool)` THEN
    ASM_REWRITE_TAC[SUBSET_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    ASM_SIMP_TAC[]]);;

let PROFINITE_GROUP_INVERSE_LIMIT = prove
 (`!k (le:I->I->bool) (G:I->A group) (f:I->I->A->A) (top:I->A topology).
        (!i. i IN k ==> profinite_group (G i) (top i)) /\
        (!i j. i IN k /\ j IN k /\ le i j
               ==> group_homomorphism (G j,G i) (f i j) /\
                   continuous_map (top j,top i) (f i j))
        ==> profinite_group (inverse_limit_group k le G f)
             (subtopology (product_topology k top)
                          (group_carrier(inverse_limit_group k le G f)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:I->bool`; `le:I->I->bool`; `G:I->A group`;
                 `f:I->I->A->A`] INVERSE_LIMIT_SUBGROUP_OF_PRODUCT_GROUP) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[inverse_limit_group; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  MATCH_MP_TAC PROFINITE_GROUP_CLOSED_SUBGROUP THEN
  ASM_SIMP_TAC[PROFINITE_GROUP_PRODUCT_GROUP] THEN
  SUBGOAL_THEN
   `topspace(product_topology k (top:I->A topology)) =
    group_carrier(product_group k (G:I->A group))`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PRODUCT_GROUP] THEN
    REWRITE_TAC[cartesian_product; o_THM] THEN
    SUBGOAL_THEN
     `!i. i IN k ==> topspace((top:I->A topology) i) = group_carrier(G i)`
     (fun th -> SIMP_TAC[th]) THEN
    ASM_MESON_TAC[profinite_group; topological_group];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN group_carrier(product_group k G) /\
         !i j. i IN k /\ j IN k /\ le i j ==> f i j (x j) = x i} =
    INTERS (topspace(product_topology k (top:I->A topology)) INSERT
            {{x | x IN topspace(product_topology k top) /\
                  (f:I->I->A->A) i j (x j) = x i} |i,j|
             i IN k /\ j IN k /\ (le:I->I->bool) i j})`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INTERS_INSERT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    MESON_TAC[];
    MATCH_MP_TAC CLOSED_IN_INTERS THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; CLOSED_IN_TOPSPACE] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`i:I`; `j:I`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAPS_EQ THEN
    EXISTS_TAC `(top:I->A topology) i` THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[profinite_group]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. (f:I->I->A->A) i j (x j)) = f i j o (\x. x j)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `(top:I->A topology) j` THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION]]);;

let PROFINITE_GROUP_INVERSE_LIMIT_INTEGER_MOD_GROUP = prove
 (`!k (le:I->I->bool) (n:I->num).
        (!i. i IN k ==> ~(n i = 0)) /\
        (!i j. i IN k /\ j IN k /\ le i j ==> n i divides n j)
        ==> profinite_group
             (inverse_limit_group k le (\i. integer_mod_group(n i))
                                  (\i j x. x rem &(n i)))
             (subtopology
               (product_topology k
                 (\i. discrete_topology(group_carrier(integer_mod_group(n i)))))
               (group_carrier
                 (inverse_limit_group k le (\i. integer_mod_group(n i))
                                      (\i j x. x rem &(n i)))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_INVERSE_LIMIT THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_FINITE_DISCRETE THEN
    ASM_SIMP_TAC[FINITE_INTEGER_MOD_GROUP];
    MAP_EVERY X_GEN_TAC [`i:I`; `j:I`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GROUP_HOMOMORPHISM_INTEGER_MOD_GROUP_REM] THEN
    REWRITE_TAC[CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[INTEGER_MOD_GROUP_1R]]);;

let PROFINITE_GROUP_INVERSE_LIMIT_QUOTIENTS = prove
 (`!G (top:A topology).
        profinite_group G top
        ==> group_isomorphism
             (G,inverse_limit_group
                 {u | u normal_subgroup_of G /\ open_in top u}
                 (\u v. v SUBSET u) (quotient_group G)
                 (\u v x. right_coset G u (@g. g IN x)))
             (\g. RESTRICTION {u | u normal_subgroup_of G /\ open_in top u}
                    (\u. right_coset G u g)) /\
            homeomorphic_map
             (top,
              subtopology
               (product_topology {u | u normal_subgroup_of G /\ open_in top u}
                  (\u. discrete_topology(group_carrier(quotient_group G u))))
               (group_carrier
                 (inverse_limit_group
                   {u | u normal_subgroup_of G /\ open_in top u}
                   (\u v. v SUBSET u) (quotient_group G)
                   (\u v x. right_coset G u (@g. g IN x)))))
             (\g. RESTRICTION {u | u normal_subgroup_of G /\ open_in top u}
                    (\u. right_coset G u g))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
  THEN
  ABBREV_TAC `k = {u | u normal_subgroup_of G /\ open_in (top:A topology) u}`
  THEN
  SUBGOAL_THEN
   `!u v x:A. u IN k /\ v IN k /\ v SUBSET u /\ x IN group_carrier G
              ==> right_coset G u (@g. g IN right_coset G v x) =
                  right_coset G u x`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:A->bool`; `v:A->bool`; `x:A`] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      NORMAL_SUBGROUP_IMP_SUBGROUP o check ((=) t o concl)))
     [`(u:A->bool) normal_subgroup_of G`; `(v:A->bool) normal_subgroup_of G`]
    THEN
    SUBGOAL_THEN `(@g:A. g IN right_coset G v x) IN right_coset G v x`
    ASSUME_TAC THENL
     [CONV_TAC SELECT_CONV THEN EXISTS_TAC `x:A` THEN
      ASM_SIMP_TAC[IN_RIGHT_COSET_SELF];
      ALL_TAC] THEN
    ABBREV_TAC `y = @g:A. g IN right_coset G v x` THEN
    SUBGOAL_THEN `(y:A) IN group_carrier G /\ y IN right_coset G u x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`G:A group`; `v:A->bool`; `x:A`] RIGHT_COSET) THEN
        ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN ASM SET_TAC[];
        UNDISCH_TAC `(y:A) IN right_coset G v x` THEN
        SPEC_TAC(`y:A`,`y:A`) THEN
        REWRITE_TAC[GSYM SUBSET; RIGHT_COSET_AS_IMAGE] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RIGHT_COSETS_EQ] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:A` THEN ASM_SIMP_TAC[IN_RIGHT_COSET_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. u IN k /\ v IN k /\ v SUBSET u
          ==> group_homomorphism (quotient_group G v,quotient_group G u)
                                 (\X. right_coset G u (@g:A. g IN X))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(u:A->bool) normal_subgroup_of G /\ (v:A->bool) normal_subgroup_of G`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(u:A->bool) IN k`; `(v:A->bool) IN k`] THEN
      EXPAND_TAC "k" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[CONJUNCT1 QUOTIENT_GROUP] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[QUOTIENT_GROUP_MUL; GROUP_MUL] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`k:(A->bool)->bool`; `\u v:A->bool. v SUBSET u`;
    `quotient_group (G:A group)`;
    `\u (v:A->bool) (x:A->bool). right_coset G u (@g:A. g IN x)`]
   INVERSE_LIMIT_GROUP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC
   `L = inverse_limit_group k (\u v:A->bool. v SUBSET u)
         (quotient_group (G:A group))
         (\u (v:A->bool) (x:A->bool). right_coset G u (@g:A. g IN x))` THEN
  SUBGOAL_THEN
   `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u`
  ASSUME_TAC THENL [EXPAND_TAC "k" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `group_carrier(G:A group) IN (k:(A->bool)->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[CARRIER_NORMAL_SUBGROUP_OF] THEN
    ASM_MESON_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:A. g IN group_carrier G
          ==> RESTRICTION k (\u. right_coset G u g) IN group_carrier L`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[RESTRICTION] THEN
      UNDISCH_TAC
       `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u` THEN
      DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[QUOTIENT_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[RESTRICTION]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN group_carrier L
        ==> ?g:A. g IN group_carrier G /\
                  RESTRICTION k (\u. right_coset G u g) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:(A->bool)->(A->bool)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; cartesian_product] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?a:(A->bool)->A.
        !u. u IN k ==> a u IN group_carrier G /\ y u = right_coset G u (a u)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
      X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!u. u IN k ==> (y:(A->bool)->(A->bool)) u IN
                       group_carrier(quotient_group G u)` THEN
      DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
      UNDISCH_TAC
       `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u` THEN
      DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[QUOTIENT_GROUP; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u v. u IN k /\ v IN k /\ v SUBSET u
            ==> (y:(A->bool)->(A->bool)) u = right_coset G u (a v)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC
       `!u v. u IN k /\ v IN k /\ v SUBSET u
              ==> right_coset G u (@g:A. g IN (y:(A->bool)->(A->bool)) v) =
                  y u` THEN
      DISCH_THEN(MP_TAC o SPECL [`u:A->bool`; `v:A->bool`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC
       `!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                       (y:(A->bool)->(A->bool)) u = right_coset G u (a u)` THEN
      DISCH_THEN(MP_TAC o SPEC `v:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        length(fst(strip_forall(concl th))) = 3)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(INTERS (IMAGE (y:(A->bool)->(A->bool)) k) = {})`
    MP_TAC THENL
     [UNDISCH_TAC `compact_space(top:A topology)` THEN
      REWRITE_TAC[COMPACT_SPACE_FIP] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `u:A->bool` THEN
        DISCH_TAC THEN
        UNDISCH_TAC
         `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u`
        THEN DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
        UNDISCH_TAC
         `!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                         (y:(A->bool)->(A->bool)) u = right_coset G u (a u)`
        THEN DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN STRIP_TAC THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
        MP_TAC(ISPECL [`G:A group`; `top:A topology`;
                       `(a:(A->bool)->A) u`]
                      TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        REWRITE_TAC[RIGHT_COSET_AS_IMAGE] THEN
        MP_TAC(ISPECL [`\x:A. group_mul G x ((a:(A->bool)->A) u)`;
                       `top:A topology`; `top:A topology`; `u:A->bool`]
                      HOMEOMORPHIC_MAP_CLOSEDNESS) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBGROUP_OF_IMP_SUBSET THEN
          ASM_REWRITE_TAC[];
          DISCH_THEN SUBST1_TAC] THEN
        MATCH_MP_TAC CLOSED_IN_OPEN_SUBGROUP THEN
        EXISTS_TAC `G:A group` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `f':(A->bool)->bool` THEN REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:(A->bool)->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))
      THEN
      MP_TAC(ISPECL [`G:A group`; `top:A topology`; `s:(A->bool)->bool`]
                    OPEN_NORMAL_SUBGROUP_INTERS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(s:(A->bool)->bool) SUBSET k` THEN
        UNDISCH_TAC
         `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u`
        THEN SET_TAC[];
        STRIP_TAC] THEN
      ABBREV_TAC `v = group_carrier G INTER INTERS (s:(A->bool)->bool)` THEN
      SUBGOAL_THEN `(v:A->bool) IN k` ASSUME_TAC THENL
       [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(a:(A->bool)->A) v` THEN
      REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:A->bool) IN k /\ v SUBSET w` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(w:A->bool) IN s` THEN
        UNDISCH_TAC `(s:(A->bool)->bool) SUBSET k` THEN
        EXPAND_TAC "v" THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC
       `!u v. u IN k /\ v IN k /\ v SUBSET u
              ==> (y:(A->bool)->(A->bool)) u =
                  right_coset G u ((a:(A->bool)->A) v)` THEN
      DISCH_THEN(MP_TAC o SPECL [`w:A->bool`; `v:A->bool`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC IN_RIGHT_COSET_SELF THEN CONJ_TAC THENL
       [MATCH_MP_TAC NORMAL_SUBGROUP_IMP_SUBGROUP THEN
        UNDISCH_TAC
         `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u`
        THEN DISCH_THEN(MP_TAC o SPEC `w:A->bool`) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC
         `!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                         (y:(A->bool)->(A->bool)) u = right_coset G u (a u)`
        THEN DISCH_THEN(MP_TAC o SPEC `v:A->bool`) THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:A`) THEN
    SUBGOAL_THEN
     `!u. u IN k ==> (g:A) IN group_carrier G /\
                     right_coset G u g = (y:(A->bool)->(A->bool)) u`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u`
      THEN DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
      UNDISCH_TAC
       `!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                       (y:(A->bool)->(A->bool)) u = right_coset G u (a u)`
      THEN DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
      UNDISCH_TAC `!x. x IN k ==> (g:A) IN (y:(A->bool)->(A->bool)) x` THEN
      DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
      SUBGOAL_THEN `(g:A) IN group_carrier G` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`G:A group`; `u:A->bool`; `(a:(A->bool)->A) u`]
                      RIGHT_COSET) THEN
        ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN ASM SET_TAC[];
        ASM_SIMP_TAC[RIGHT_COSETS_EQ]] THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `g:A` THEN ASM_SIMP_TAC[IN_RIGHT_COSET_SELF];
      ALL_TAC] THEN
    EXISTS_TAC `g:A` THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `u:A->bool` THEN
    REWRITE_TAC[RESTRICTION] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `EXTENSIONAL k (y:(A->bool)->(A->bool))` THEN
      REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_carrier L SUBSET
    topspace(product_topology k
     (\u. discrete_topology(group_carrier(quotient_group G (u:A->bool)))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF;
                TOPSPACE_DISCRETE_TOPOLOGY] THEN
    ASM_REWRITE_TAC[SUBSET; cartesian_product; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    lhs(concl th) = `group_carrier(L:((A->bool)->(A->bool)) group)`)) THEN
  SUBGOAL_THEN
   `!g h:A. g IN group_carrier G /\ h IN group_carrier G
            ==> (RESTRICTION k (\u. right_coset G u g) =
                 RESTRICTION k (\u. right_coset G u h) <=> g = h)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:A`; `h:A`] THEN STRIP_TAC THEN
    EQ_TAC THENL [DISCH_TAC; SIMP_TAC[]] THEN
    MP_TAC(ISPECL [`G:A group`; `g:A`; `h:A`] GROUP_DIV_EQ_ID) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ABBREV_TAC `x = group_div G g (h:A)` THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN ASM_SIMP_TAC[GROUP_DIV]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!w. open_in top w /\ group_id G IN w
          ==> ?u:A->bool. u normal_subgroup_of G /\ open_in top u /\
                          u SUBSET w` THEN
    DISCH_THEN(MP_TAC o SPEC `topspace top DIFF {x:A}`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
        MP_TAC(ISPEC `top:A topology` T1_SPACE_CLOSED_IN_SING) THEN
        ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE];
        ASM_REWRITE_TAC[IN_DIFF; IN_SING; GROUP_ID] THEN
        UNDISCH_TAC `~(x:A = group_id G)` THEN MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(u:A->bool) IN k` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    UNDISCH_TAC
     `RESTRICTION k (\u. right_coset G u (g:A)) =
      RESTRICTION k (\u. right_coset G u h)` THEN
    DISCH_THEN(MP_TAC o C AP_THM `u:A->bool`) THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    ASM_SIMP_TAC[RIGHT_COSET_EQ] THEN
    UNDISCH_TAC `(u:A->bool) SUBSET topspace top DIFF {x:A}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_ISOMORPHISM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`g:A`; `h:A`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[RESTRICTION] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(GSYM QUOTIENT_GROUP_MUL) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_HOMEOMORPHIC_MAP THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[HAUSDORFF_SPACE_PRODUCT_TOPOLOGY;
                HAUSDORFF_SPACE_DISCRETE_TOPOLOGY];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]] THEN
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN
    UNDISCH_TAC
     `!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u` THEN
    DISCH_THEN(MP_TAC o SPEC `u:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`G:A group`; `top:A topology`; `u:A->bool`]
                  QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_QUOTIENT_TOPOLOGY];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    UNDISCH_TAC
     `group_carrier L SUBSET
      topspace(product_topology k
       (\u. discrete_topology(group_carrier(quotient_group G (u:A->bool)))))`
    THEN ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Groups of permutations with the topology of pointwise convergence         *)
(* (pointwise_topology of Multivariate/metric.ml). For G a subgroup of       *)
(* symmetric_group X, subgroup_generated (symmetric_group X) G with          *)
(* pointwise_topology G is a topological group: the fibre of (f,g) |-> f o g *)
(* at x over y is the union over w of {f | f w = y} CROSS {g | g x = w}, and *)
(* that of f |-> inverse f is {f | f y = x}. The pointwise stabilizer of a   *)
(* set is a closed subgroup, open for finite sets and normal for G-stable    *)
(* sets; permutations of X fix the points outside X, so the stabilizers of   *)
(* finite subsets of X form a base of neighbourhoods of 1, and a subgroup is *)
(* open iff it contains one of them. The topology is also the subspace       *)
(* topology, through g |-> RESTRICTION X g, of the product over X of         *)
(* discrete copies of X. If each orbit {g x | g IN G} of a point of X is     *)
(* finite and G is closed in the product, then G is profinite: it lies in    *)
(* the product of the finite orbits and of the points {x} outside X, compact *)
(* by Tychonoff, and the open stabilizers form a base at 1. With finite      *)
(* orbits, a function agreeing on each finite set with a member of G is a    *)
(* permutation of X, being injective and mapping each finite orbit into,     *)
(* hence onto, itself; so closedness may be replaced by the local condition  *)
(* that G contain every such permutation. A finite set of functions has the  *)
(* discrete pointwise topology.                                              *)
(* ------------------------------------------------------------------------- *)

let TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY = prove
 (`!X G:(A->A)->bool.
        G subgroup_of symmetric_group X
        ==> topological_group (subgroup_generated (symmetric_group X) G)
                              (pointwise_topology G)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[topological_group; TOPSPACE_POINTWISE_TOPOLOGY;
               CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               CONJUNCT2 SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SYMMETRIC_GROUP; CONTINUOUS_MAP_POINTWISE_TOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_POINTWISE_TOPOLOGY] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:A->A`; `g:A->A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`;
                   `f:A->A`; `g:A->A`] IN_SUBGROUP_MUL) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    SUBGOAL_THEN
     `{z | z IN (G:(A->A)->bool) CROSS G /\ (FST z o SND z) x = y} =
      UNIONS {{f | f IN G /\ f w = y} CROSS {f | f IN G /\ f x = w} |
              w IN (:A)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
                  IN_CROSS; o_THM; IN_UNIV] THEN
      MESON_TAC[];
      MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; OPEN_IN_CROSS] THEN
      REWRITE_TAC[OPEN_IN_POINTWISE_TOPOLOGY_POINT]];
    X_GEN_TAC `f:A->A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`;
                   `f:A->A`] IN_SUBGROUP_INV) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    SUBGOAL_THEN
     `{f:A->A | f IN G /\ inverse f x = y} = {f | f IN G /\ f y = x}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[PERMUTES_INVERSE_EQ];
      REWRITE_TAC[OPEN_IN_POINTWISE_TOPOLOGY_POINT]]]);;

let SUBGROUP_OF_POINTWISE_STABILIZER = prove
 (`!X G (k:A->bool).
        G subgroup_of symmetric_group X
        ==> {g | g IN G /\ !x. x IN k ==> g x = x} subgroup_of
            subgroup_generated (symmetric_group X) G`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[subgroup_of; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               CONJUNCT2 SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM; I_THM; o_THM] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`]
                  IN_SUBGROUP_ID) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP];
    X_GEN_TAC `f:A->A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`;
                     `f:A->A`] IN_SUBGROUP_INV) THEN
      ASM_REWRITE_TAC[SYMMETRIC_GROUP];
      ASM_MESON_TAC[PERMUTES_INVERSE_EQ]];
    MAP_EVERY X_GEN_TAC [`f:A->A`; `g:A->A`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`;
                   `f:A->A`; `g:A->A`] IN_SUBGROUP_MUL) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP]]);;

let OPEN_IN_POINTWISE_STABILIZER = prove
 (`!G (k:A->bool).
        FINITE k
        ==> open_in (pointwise_topology G)
                    {g | g IN G /\ !x. x IN k ==> g x = x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A->A)->bool`; `k:A->bool`; `I:A->A`]
                OPEN_IN_POINTWISE_TOPOLOGY_AGREE) THEN
  ASM_REWRITE_TAC[I_THM]);;

let CLOSED_IN_POINTWISE_STABILIZER = prove
 (`!G (k:A->bool).
        closed_in (pointwise_topology G)
                  {g | g IN G /\ !x. x IN k ==> g x = x}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G:(A->A)->bool`; `k:A->bool`; `I:A->A`]
                CLOSED_IN_POINTWISE_TOPOLOGY_AGREE) THEN
  REWRITE_TAC[I_THM]);;

let NORMAL_SUBGROUP_OF_POINTWISE_STABILIZER = prove
 (`!X G (k:A->bool).
        G subgroup_of symmetric_group X /\
        (!g x. g IN G /\ x IN k ==> g x IN k)
        ==> {g | g IN G /\ !x. x IN k ==> g x = x} normal_subgroup_of
            subgroup_generated (symmetric_group X) G`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NORMAL_SUBGROUP_CONJUGATION;
               SUBGROUP_OF_POINTWISE_STABILIZER] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; group_conjugation] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               CONJUNCT2 SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SYMMETRIC_GROUP; IN_ELIM_THM; o_THM] THEN
  X_GEN_TAC `a:A->A` THEN DISCH_TAC THEN X_GEN_TAC `h:A->A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `inverse (a:A->A) IN G` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`;
                   `a:A->A`] IN_SUBGROUP_INV) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`]
                  IN_SUBGROUP_MUL) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP] THEN
    DISCH_THEN(fun th -> ASM_MESON_TAC[th]);
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->A)(inverse a x) = inverse (a:A->A) x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[PERMUTES_INVERSES]]]);;

let POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER = prove
 (`!X G w:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        open_in (pointwise_topology G) w /\ I IN w
        ==> ?k. FINITE k /\ k SUBSET X /\
                {g | g IN G /\ !x. x IN k ==> g x = x} SUBSET w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(A->A)->bool`; `w:(A->A)->bool`; `I:A->A`]
                POINTWISE_TOPOLOGY_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k INTER (X:A->bool)` THEN
  ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET] THEN
  TRANS_TAC SUBSET_TRANS `{g | g IN G /\ !x:A. x IN k ==> g x = x}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `g:A->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:A) IN X` THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[permutes]);;

let OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP = prove
 (`!X G h:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        h subgroup_of subgroup_generated (symmetric_group X) G
        ==> (open_in (pointwise_topology G) h <=>
             ?k. FINITE k /\ k SUBSET X /\
                 {g | g IN G /\ !x. x IN k ==> g x = x} SUBSET h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_SUBGROUP_ID) THEN
    REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED; SYMMETRIC_GROUP];
    DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
    MAP_EVERY EXISTS_TAC
     [`subgroup_generated (symmetric_group X) (G:(A->A)->bool)`;
      `{g | g IN G /\ !x:A. x IN k ==> g x = x}`] THEN
    ASM_SIMP_TAC[TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY;
                 OPEN_IN_POINTWISE_STABILIZER] THEN
    REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED; SYMMETRIC_GROUP] THEN
    REWRITE_TAC[IN_ELIM_THM; I_THM] THEN
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`]
                  IN_SUBGROUP_ID) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP]]);;

let HOMEOMORPHIC_MAP_POINTWISE_RESTRICTION = prove
 (`!X G:(A->A)->bool.
        G subgroup_of symmetric_group X
        ==> homeomorphic_map
             (pointwise_topology G,
              subtopology (product_topology X (\x. discrete_topology X))
                          (IMAGE (RESTRICTION X) G))
             (RESTRICTION X)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:A->A. g IN G ==> (\x. if x IN X then RESTRICTION X g x else x) = g`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
    ASM_MESON_TAC[permutes];
    ALL_TAC] THEN
  ABBREV_TAC `P = product_topology X (\x:A. discrete_topology X)` THEN
  SUBGOAL_THEN
   `IMAGE (RESTRICTION X) (G:(A->A)->bool) SUBSET topspace P`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF; TOPSPACE_DISCRETE_TOPOLOGY]
    THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CARTESIAN_PRODUCT] THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL; RESTRICTION] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace(subtopology P (IMAGE (RESTRICTION X) G)) =
    IMAGE (RESTRICTION X) (G:(A->A)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `IMAGE (RESTRICTION X) (G:(A->A)->bool) SUBSET topspace P` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `\f:A->A x. if x IN X then f x else x` THEN
  ASM_REWRITE_TAC[homeomorphic_maps; TOPSPACE_POINTWISE_TOPOLOGY] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_POINTWISE_TOPOLOGY] THEN
    SIMP_TAC[FUN_IN_IMAGE] THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES] THEN
    ASM_REWRITE_TAC[TOPSPACE_POINTWISE_TOPOLOGY; RESTRICTION] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE];
      REWRITE_TAC[OPEN_IN_POINTWISE_TOPOLOGY_POINT]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_POINTWISE_TOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  ASM_CASES_TAC `(x:A) IN X` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(y:A) IN X` THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `{f | f IN topspace P /\ (\f:A->A. f x) f IN {y:A}}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC `discrete_topology (X:A->bool)` THEN
        ASM_REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY; SING_SUBSET] THEN
        EXPAND_TAC "P" THEN
        MP_TAC(ISPECL [`\x:A. discrete_topology (X:A->bool)`; `X:A->bool`;
                       `x:A`] CONTINUOUS_MAP_PRODUCT_PROJECTION) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC
         `IMAGE (RESTRICTION X) (G:(A->A)->bool) SUBSET topspace P` THEN
        REWRITE_TAC[IN_SING] THEN SET_TAC[]];
      SUBGOAL_THEN
       `{z | z IN IMAGE (RESTRICTION X) (G:(A->A)->bool) /\ z x = (y:A)} =
        {}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_IMAGE] THEN
        X_GEN_TAC `z:A->A` THEN
        DISCH_THEN(CONJUNCTS_THEN2
         (X_CHOOSE_THEN `g:A->A` STRIP_ASSUME_TAC) MP_TAC) THEN
        ASM_REWRITE_TAC[RESTRICTION] THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
        REWRITE_TAC[OPEN_IN_EMPTY]]];
    ASM_CASES_TAC `x:A = y` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; OPEN_IN_EMPTY] THEN
    ASM_REWRITE_TAC[SET_RULE `{x:A->A | x IN s} = s`;
                    OPEN_IN_SUBTOPOLOGY_REFL]]);;

let PERMUTES_POINTWISE_LIMIT = prove
 (`!X G f:A->A.
        G subgroup_of symmetric_group X /\
        (!x. x IN X ==> FINITE {g x | g IN G}) /\
        (!k. FINITE k ==> ?g. g IN G /\ !x. x IN k ==> g x = f x)
        ==> f permutes X`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. ?g. g IN G /\ g x = (f:A->A) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN
    REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:A. (f:A->A) x = f y ==> x = y` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{x:A,y}` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "FINITE"))
          (concl th))) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT] THEN
    REWRITE_TAC[NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. ~(x IN X) ==> (f:A->A) x = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
  REWRITE_TAC[permutes] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `(y:A) IN X` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ABBREV_TAC `orb = {g y | g IN (G:(A->A)->bool)}` THEN
  SUBGOAL_THEN `FINITE(orb:A->bool) /\ (y:A) IN orb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "orb" THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `I:A->A` THEN REWRITE_TAC[I_THM] THEN
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`]
                  IN_SUBGROUP_ID) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:A->A) orb SUBSET orb` ASSUME_TAC THENL
   [EXPAND_TAC "orb" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `g:A->A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `h:A->A` STRIP_ASSUME_TAC o
      SPEC `(g:A->A) y` o check (fun th ->
        is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
    EXISTS_TAC `(h:A->A) o (g:A->A)` THEN ASM_REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`symmetric_group (X:A->bool)`; `G:(A->A)->bool`;
                   `h:A->A`; `g:A->A`] IN_SUBGROUP_MUL) THEN
    ASM_REWRITE_TAC[SYMMETRIC_GROUP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`orb:A->bool`; `f:A->A`] SURJECTIVE_IFF_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PROFINITE_GROUP_POINTWISE_TOPOLOGY = prove
 (`!X G:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        (!x. x IN X ==> FINITE {g x | g IN G}) /\
        closed_in (product_topology (:A) (\x. discrete_topology (:A))) G
        ==> profinite_group (subgroup_generated (symmetric_group X) G)
                            (pointwise_topology G)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `!g:A->A. g IN G ==> g permutes X` ASSUME_TAC THENL
   [UNDISCH_TAC `(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)` THEN
    REWRITE_TAC[SYMMETRIC_GROUP; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[PROFINITE_GROUP_OPEN_SUBGROUPS] THEN
  ASM_SIMP_TAC[TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY;
               HAUSDORFF_SPACE_POINTWISE_TOPOLOGY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pointwise_topology] THEN
    MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `cartesian_product (:A) (\x. {g x | g IN (G:(A->A)->bool)})` THEN
    ASM_REWRITE_TAC[COMPACT_IN_CARTESIAN_PRODUCT] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      REWRITE_TAC[COMPACT_IN_DISCRETE_TOPOLOGY; SUBSET_UNIV; IN_UNIV] THEN
      X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN X` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:A}` THEN
      REWRITE_TAC[FINITE_SING; SUBSET; FORALL_IN_GSPEC; IN_SING] THEN
      ASM_MESON_TAC[permutes];
      REWRITE_TAC[SUBSET; IN_CARTESIAN_PRODUCT; EXTENSIONAL_UNIV; IN_UNIV] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONJUNCT2 SUBGROUP_GENERATED; SYMMETRIC_GROUP] THEN
  X_GEN_TAC `w:(A->A)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A->bool`; `G:(A->A)->bool`; `w:(A->A)->bool`]
                POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{g | g IN G /\ !x:A. x IN k ==> g x = x}` THEN
  ASM_SIMP_TAC[SUBGROUP_OF_POINTWISE_STABILIZER;
               OPEN_IN_POINTWISE_STABILIZER]);;

let PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL = prove
 (`!X G:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        (!x. x IN X ==> FINITE {g x | g IN G}) /\
        (!f. f permutes X /\
             (!k. FINITE k ==> ?g. g IN G /\ !x. x IN k ==> g x = f x)
             ==> f IN G)
        ==> profinite_group (subgroup_generated (symmetric_group X) G)
                            (pointwise_topology G)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_POINTWISE_TOPOLOGY THEN
  ASM_REWRITE_TAC[CLOSED_IN_POINTWISE_PRODUCT] THEN
  X_GEN_TAC `f:A->A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERMUTES_POINTWISE_LIMIT THEN
  EXISTS_TAC `G:(A->A)->bool` THEN ASM_REWRITE_TAC[]);;

let POINTWISE_TOPOLOGY_FINITE = prove
 (`!s:(A->B)->bool. FINITE s ==> pointwise_topology s = discrete_topology s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_T1_SPACE_IMP_DISCRETE_TOPOLOGY THEN
  ASM_SIMP_TAC[TOPSPACE_POINTWISE_TOPOLOGY; HAUSDORFF_IMP_T1_SPACE;
               HAUSDORFF_SPACE_POINTWISE_TOPOLOGY]);;
