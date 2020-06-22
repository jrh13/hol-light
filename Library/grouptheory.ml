(* ========================================================================= *)
(* Simple formulation of group theory with a type of "(A)group".             *)
(* ========================================================================= *)

needs "Library/frag.ml";;       (* Used eventually for free Abelian groups   *)
needs "Library/card.ml";;       (* Need cardinal arithmetic in a few places  *)
needs "Library/prime.ml";;      (* For elementary number-theoretic lemmas    *)

(* ------------------------------------------------------------------------- *)
(* Basic type of groups.                                                     *)
(* ------------------------------------------------------------------------- *)

let group_tybij =
  let eth = prove
   (`?s (z:A) n a.
          z IN s /\
          (!x. x IN s ==> n x IN s) /\
          (!x y. x IN s /\ y IN s ==> a x y IN s) /\
          (!x y z. x IN s /\ y IN s /\ z IN s
                   ==> a x (a y z) = a (a x y) z) /\
          (!x. x IN s ==> a z x = x /\ a x z = x) /\
          (!x. x IN s ==> a (n x) x = z /\ a x (n x) = z)`,
    MAP_EVERY EXISTS_TAC
     [`{ARB:A}`; `ARB:A`; `(\x. ARB):A->A`; `(\x y. ARB):A->A->A`] THEN
    REWRITE_TAC[IN_SING] THEN MESON_TAC[]) in
  new_type_definition "group" ("group","group_operations")
   (GEN_REWRITE_RULE DEPTH_CONV [EXISTS_UNPAIR_THM] eth);;

let group_carrier = new_definition
 `(group_carrier:(A)group->A->bool) = \g. FST(group_operations g)`;;

let group_id = new_definition
 `(group_id:(A)group->A) = \g. FST(SND(group_operations g))`;;

let group_inv = new_definition
 `(group_inv:(A)group->A->A) = \g. FST(SND(SND(group_operations g)))`;;

let group_mul = new_definition
 `(group_mul:(A)group->A->A->A) = \g. SND(SND(SND(group_operations g)))`;;

let ([GROUP_ID; GROUP_INV; GROUP_MUL; GROUP_MUL_ASSOC;
      GROUP_MUL_LID; GROUP_MUL_RID; GROUP_MUL_LINV; GROUP_MUL_RINV] as
     GROUP_PROPERTIES) = (CONJUNCTS o prove)
 (`(!G:A group. group_id G IN group_carrier G) /\
   (!G x:A. x IN group_carrier G ==> group_inv G x IN group_carrier G) /\
   (!G x y:A. x IN group_carrier G /\ y IN group_carrier G
              ==> group_mul G x y IN group_carrier G) /\
   (!G x y z:A. x IN group_carrier G /\
                y IN group_carrier G /\
                z IN group_carrier G
                ==> group_mul G x (group_mul G y z) =
                    group_mul G (group_mul G x y) z) /\
   (!G x:A. x IN group_carrier G ==> group_mul G (group_id G) x = x) /\
   (!G x:A. x IN group_carrier G ==> group_mul G x (group_id G) = x) /\
   (!G x:A. x IN group_carrier G
            ==> group_mul G (group_inv G x) x = group_id G) /\
   (!G x:A. x IN group_carrier G
            ==> group_mul G x(group_inv G x) = group_id G)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(SPEC `G:A group` (MATCH_MP(MESON[]
   `(!a. mk(dest a) = a) /\ (!r. P r <=> dest(mk r) = r)
    ==> !a. P(dest a)`) group_tybij)) THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul] THEN
  SIMP_TAC[]);;

let GROUPS_EQ = prove
 (`!G H:A group.
        G = H <=>
        group_carrier G = group_carrier H /\
        group_id G = group_id H /\
        group_inv G = group_inv H /\
        group_mul G = group_mul H`,
  REWRITE_TAC[GSYM PAIR_EQ] THEN
  REWRITE_TAC[group_carrier;group_id;group_inv;group_mul] THEN
  MESON_TAC[CONJUNCT1 group_tybij]);;

let GROUP_CARRIER_NONEMPTY = prove
 (`!G:A group. ~(group_carrier G = {})`,
  MESON_TAC[MEMBER_NOT_EMPTY; GROUP_ID]);;

(* ------------------------------------------------------------------------- *)
(* The trivial group on a given object.                                      *)
(* ------------------------------------------------------------------------- *)

let singleton_group = new_definition
 `singleton_group (a:A) = group({a},a,(\x. a),(\x y. a))`;;

let SINGLETON_GROUP = prove
 (`(!a:A. group_carrier(singleton_group a) = {a}) /\
   (!a:A. group_id(singleton_group a) = a) /\
   (!a:A. group_inv(singleton_group a) = \x. a) /\
   (!a:A. group_mul(singleton_group a) = \x y. a)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl singleton_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM singleton_group] THEN SIMP_TAC[IN_SING] THEN
  SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;

let trivial_group = new_definition
 `trivial_group G <=> group_carrier G = {group_id G}`;;

let TRIVIAL_IMP_FINITE_GROUP = prove
 (`!G:A group. trivial_group G ==> FINITE(group_carrier G)`,
  SIMP_TAC[trivial_group; FINITE_SING]);;

let TRIVIAL_GROUP_SINGLETON_GROUP = prove
 (`!a:A. trivial_group(singleton_group a)`,
  REWRITE_TAC[trivial_group; SINGLETON_GROUP]);;

let FINITE_SINGLETON_GROUP = prove
 (`!a:A. FINITE(group_carrier(singleton_group a))`,
  SIMP_TAC[TRIVIAL_IMP_FINITE_GROUP; TRIVIAL_GROUP_SINGLETON_GROUP]);;

let TRIVIAL_GROUP_SUBSET = prove
 (`!G:A group. trivial_group G <=> group_carrier G SUBSET {group_id G}`,
  SIMP_TAC[trivial_group; GSYM SUBSET_ANTISYM_EQ; SING_SUBSET; GROUP_ID]);;

let TRIVIAL_GROUP = prove
 (`!G:A group. trivial_group G <=> ?a. group_carrier G = {a}`,
  GEN_TAC THEN REWRITE_TAC[trivial_group] THEN MATCH_MP_TAC(SET_RULE
   `c IN s ==> (s = {c} <=> ?a. s = {a})`) THEN
  REWRITE_TAC[GROUP_ID]);;

let TRIVIAL_GROUP_ALT = prove
 (`!G:A group. trivial_group G <=> ?a. group_carrier G SUBSET {a}`,
  REWRITE_TAC[TRIVIAL_GROUP; GROUP_CARRIER_NONEMPTY; SET_RULE
   `(?a. s = {a}) <=> (?a. s SUBSET {a}) /\ ~(s = {})`]);;

let TRIVIAL_GROUP_HAS_SIZE_1 = prove
 (`!G:A group. trivial_group G <=> group_carrier(G) HAS_SIZE 1`,
  GEN_TAC THEN CONV_TAC(RAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[TRIVIAL_GROUP]);;

let GROUP_CARRIER_HAS_SIZE_1 = prove
 (`!G:A group. group_carrier(G) HAS_SIZE 1 <=> trivial_group G`,
  REWRITE_TAC[TRIVIAL_GROUP_HAS_SIZE_1]);;

(* ------------------------------------------------------------------------- *)
(* Opposite group (mainly just to avoid some duplicated variant proofs).     *)
(* ------------------------------------------------------------------------- *)

let opposite_group = new_definition
 `opposite_group(G:A group) =
        group(group_carrier G,group_id G,group_inv G,
              \x y. group_mul G y x)`;;

let OPPOSITE_GROUP = prove
 (`!G:A group.
        group_carrier(opposite_group G) = group_carrier G /\
        group_id(opposite_group G) = group_id G /\
        group_inv(opposite_group G) = group_inv G /\
        group_mul(opposite_group G) = \x y. group_mul G y x`,
  GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl opposite_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM opposite_group] THEN ANTS_TAC THENL
   [SIMP_TAC GROUP_PROPERTIES;
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let OPPOSITE_OPPOSITE_GROUP = prove
 (`!G:A group. opposite_group (opposite_group G) = G`,
  GEN_TAC THEN ONCE_REWRITE_TAC[opposite_group] THEN
  REWRITE_TAC[OPPOSITE_GROUP; ETA_AX] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1 group_tybij)] THEN
  AP_TERM_TAC THEN REWRITE_TAC[group_carrier; group_id; group_inv; group_mul]);;

let OPPOSITE_GROUP_INV = prove
 (`!G x:A. group_inv(opposite_group G) x = group_inv G x`,
  REWRITE_TAC[OPPOSITE_GROUP]);;

let OPPOSITE_GROUP_MUL = prove
 (`!G x y:A. group_mul(opposite_group G) x y = group_mul G y x`,
  REWRITE_TAC[OPPOSITE_GROUP]);;

let OPPOSITE_SINGLETON_GROUP = prove
 (`!a:A. opposite_group(singleton_group a) = singleton_group a`,
  REWRITE_TAC[GROUPS_EQ; SINGLETON_GROUP; OPPOSITE_GROUP]);;

let TRIVIAL_OPPOSITE_GROUP = prove
 (`!G:A group. trivial_group(opposite_group G) <=> trivial_group G`,
  REWRITE_TAC[trivial_group; OPPOSITE_GROUP]);;

let FINITE_OPPOSITE_GROUP = prove
 (`!G:A group. FINITE(group_carrier(opposite_group G)) <=>
               FINITE(group_carrier G)`,
  REWRITE_TAC[OPPOSITE_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* Derived operations and derived properties, including separate "powers"    *)
(* for natural number (group_pow) and integer (group_zpow) indices.          *)
(* ------------------------------------------------------------------------- *)

let group_div = new_definition
 `group_div G x y = group_mul G x (group_inv G y)`;;

let GROUP_DIV = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_div G x y) IN group_carrier G`,
  SIMP_TAC[group_div; GROUP_MUL; GROUP_INV]);;

let GROUP_MUL_LCANCEL = prove
 (`!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G
        ==> (group_mul G x y = group_mul G x z <=> y = z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `group_mul G (group_inv G x):A->A`) THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_INV; GROUP_MUL_LINV; GROUP_MUL_LID]);;

let GROUP_MUL_LCANCEL_IMP = prove
 (`!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G /\
        group_mul G x y = group_mul G x z
        ==> y = z`,
  MESON_TAC[GROUP_MUL_LCANCEL]);;

let GROUP_MUL_RCANCEL = prove
 (`!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G
        ==> (group_mul G x z = group_mul G y z <=> x = y)`,
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_MUL] THEN
  SIMP_TAC[GROUP_MUL_LCANCEL; OPPOSITE_GROUP]);;

let GROUP_MUL_RCANCEL_IMP = prove
 (`!G x y z:A.
        x IN group_carrier G /\ y IN group_carrier G /\ z IN group_carrier G /\
        group_mul G x z = group_mul G y z
        ==> x = y`,
  MESON_TAC[GROUP_MUL_RCANCEL]);;

let GROUP_LID_UNIQUE = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ group_mul G x y = y
        ==> x = group_id G`,
  MESON_TAC[GROUP_MUL_RCANCEL; GROUP_MUL_LID; GROUP_MUL; GROUP_ID]);;

let GROUP_RID_UNIQUE = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ group_mul G x y = x
        ==> y = group_id G`,
  MESON_TAC[GROUP_MUL_LCANCEL; GROUP_MUL_RID; GROUP_MUL; GROUP_ID]);;

let GROUP_LID_EQ = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G x y = y <=> x = group_id G)`,
  MESON_TAC[GROUP_LID_UNIQUE; GROUP_MUL_LID]);;

let GROUP_RID_EQ = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G x y = x <=> y = group_id G)`,
  MESON_TAC[GROUP_RID_UNIQUE; GROUP_MUL_RID]);;

let GROUP_LINV_UNIQUE = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_id G
        ==> group_inv G x = y`,
  MESON_TAC[GROUP_MUL_LCANCEL; GROUP_INV; GROUP_MUL_RINV]);;

let GROUP_RINV_UNIQUE = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_id G
        ==> group_inv G y = x`,
  MESON_TAC[GROUP_MUL_RCANCEL; GROUP_INV; GROUP_MUL_LINV]);;

let GROUP_LINV_EQ = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_inv G x = y <=> group_mul G x y = group_id G)`,
  MESON_TAC[GROUP_LINV_UNIQUE; GROUP_MUL_RINV]);;

let GROUP_RINV_EQ = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_inv G x = y <=> group_mul G y x = group_id G)`,
  MESON_TAC[GROUP_RINV_UNIQUE; GROUP_MUL_LINV]);;

let GROUP_MUL_EQ_ID = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G x y = group_id G <=> group_mul G y x = group_id G)`,
  MESON_TAC[GROUP_RINV_EQ; GROUP_LINV_EQ]);;

let GROUP_INV_INV = prove
 (`!G x:A. x IN group_carrier G ==> group_inv G (group_inv G x) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_LINV_UNIQUE THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_MUL_LINV]);;

let GROUP_INV_ID = prove
 (`!G:A group. group_inv G (group_id G) = group_id G`,
  GEN_TAC THEN MATCH_MP_TAC GROUP_LINV_UNIQUE THEN
  SIMP_TAC[GROUP_ID; GROUP_MUL_LID]);;

let GROUP_INV_EQ_ID = prove
 (`!G x:A.
        x IN group_carrier G
        ==> (group_inv G x = group_id G <=> x = group_id G)`,
  MESON_TAC[GROUP_INV_INV; GROUP_INV_ID]);;

let GROUP_INV_MUL = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_inv G (group_mul G x y) =
            group_mul G (group_inv G y) (group_inv G x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_LINV_UNIQUE THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GROUP_MUL_ASSOC] THEN
  W(MP_TAC o PART_MATCH (rand o rand)
    GROUP_MUL_ASSOC o lhand o lhand o snd) THEN
  ASM_SIMP_TAC[GROUP_MUL_RINV; GROUP_INV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GROUP_MUL_RINV; GROUP_INV; GROUP_MUL_RID]);;

let GROUP_INV_EQ = prove
 (`!G x y:A. x IN group_carrier G /\ y IN group_carrier G
             ==> (group_inv G x = group_inv G y <=> x = y)`,
  MESON_TAC[GROUP_INV_INV]);;

let GROUP_DIV_REFL = prove
 (`!G x:A. x IN group_carrier G ==> group_div G x x = group_id G`,
  SIMP_TAC[group_div; GROUP_MUL_RINV]);;

let GROUP_DIV_EQ_ID = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_div G x y = group_id G <=> x = y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `group_id G:A = group_div G y y` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GROUP_DIV_REFL];
    ASM_SIMP_TAC[group_div; GROUP_MUL_RCANCEL; GROUP_INV]]);;

let GROUP_COMMUTES_INV = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==>  group_mul G (group_inv G x) y = group_mul G y (group_inv G x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_MUL_LCANCEL_IMP THEN
  MAP_EVERY EXISTS_TAC [`G:A group`; `x:A`] THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_MUL; GROUP_MUL_ASSOC; GROUP_MUL_RINV] THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_MUL; GSYM GROUP_MUL_ASSOC; GROUP_MUL_RINV] THEN
  ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID]);;

let GROUP_COMMUTES_INV_EQ = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_mul G (group_inv G x) y = group_mul G y (group_inv G x) <=>
             group_mul G x y = group_mul G y x)`,
  MESON_TAC[GROUP_COMMUTES_INV; GROUP_INV_INV; GROUP_INV]);;

let GROUP_COMMUTES_MUL = prove
 (`!G x y z:A.
        x IN group_carrier G /\
        y IN group_carrier G /\
        z IN group_carrier G /\
        group_mul G x z = group_mul G z x /\
        group_mul G y z = group_mul G z y
        ==> group_mul G (group_mul G x y) z = group_mul G z (group_mul G x y)`,
  MESON_TAC[GROUP_MUL; GROUP_MUL_ASSOC]);;

let FORALL_IN_GROUP_CARRIER_INV = prove
 (`!(P:A->bool) G.
        (!x. x IN group_carrier G ==> P(group_inv G x)) <=>
        (!x. x IN group_carrier G ==> P x)`,
  MESON_TAC[GROUP_INV; GROUP_INV_INV]);;

let EXISTS_IN_GROUP_CARRIER_INV = prove
 (`!P G:A group.
        (?x. x IN group_carrier G /\ P(group_inv G x)) <=>
        (?x. x IN group_carrier G /\ P x)`,
  MESON_TAC[GROUP_INV; GROUP_INV_INV]);;

let group_pow = new_recursive_definition num_RECURSION
 `group_pow G x 0 = group_id G /\
  group_pow G x (SUC n) = group_mul G x (group_pow G x n)`;;

let GROUP_POW = prove
 (`!G (x:A) n. x IN group_carrier G ==> group_pow G x n IN group_carrier G`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[group_pow; GROUP_ID; GROUP_MUL]);;

let GROUP_POW_0 = prove
 (`!G (x:A). group_pow G x 0 = group_id G`,
  REWRITE_TAC[group_pow]);;

let GROUP_POW_1 = prove
 (`!G x:A. x IN group_carrier G ==> group_pow G x 1 = x`,
  SIMP_TAC[num_CONV `1`; group_pow; GROUP_MUL_RID]);;

let GROUP_POW_2 = prove
 (`!G x:A. x IN group_carrier G ==> group_pow G x 2 = group_mul G x x`,
  SIMP_TAC[num_CONV `2`; num_CONV `1`; group_pow; GROUP_MUL_RID]);;

let GROUP_POW_ID = prove
 (`!n. group_pow G (group_id G) n = group_id G`,
  INDUCT_TAC THEN ASM_SIMP_TAC[group_pow; GROUP_ID; GROUP_MUL_LID]);;

let GROUP_POW_ADD = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_pow G x (m + n) =
            group_mul G (group_pow G x m) (group_pow G x n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; ADD_CLAUSES; GROUP_POW; GROUP_MUL_LID] THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_POW]);;

let GROUP_POW_SUB = prove
 (`!G (x:A) m n.
        x IN group_carrier G /\ n <= m
        ==> group_pow G x (m - n) =
            group_div G (group_pow G x m) (group_pow G x n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_MUL_RCANCEL_IMP THEN
  MAP_EVERY EXISTS_TAC [`G:A group`; `group_pow G x n:A`] THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_MUL; GROUP_INV; group_div;
               GSYM GROUP_MUL_ASSOC; GROUP_MUL_LINV; GROUP_MUL_RID;
               GSYM GROUP_POW_ADD; SUB_ADD]);;

let GROUP_POW_SUB_ALT = prove
 (`!G (x:A) m n.
        x IN group_carrier G /\ n <= m
        ==> group_pow G x (m - n) =
            group_mul G (group_inv G (group_pow G x n)) (group_pow G x m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_MUL_LCANCEL_IMP THEN
  MAP_EVERY EXISTS_TAC [`G:A group`; `group_pow G x n:A`] THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_MUL; GROUP_INV; group_div; GROUP_MUL_ASSOC;
               GROUP_MUL_RINV; GROUP_MUL_LID; GSYM GROUP_POW_ADD;
               ARITH_RULE `n:num <= m ==> n + m - n = m`]);;

let GROUP_INV_POW = prove
 (`!G (x:A) n.
        x IN group_carrier G
        ==> group_inv G (group_pow G x n) = group_pow G (group_inv G x) n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 group_pow; GROUP_INV_ID] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARITH_RULE `SUC n = 1 + n`] THEN
  ASM_SIMP_TAC[ADD1; GROUP_POW_ADD; GROUP_INV; GROUP_INV_MUL; GROUP_POW;
               GROUP_POW_1]);;

let GROUP_POW_MUL = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_pow G x (m * n) = group_pow G (group_pow G x m) n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[GROUP_POW_0; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[GROUP_POW_ADD; CONJUNCT2 group_pow]);;

let GROUP_POW_POW = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_pow G (group_pow G x m) n = group_pow G x (m * n)`,
  SIMP_TAC[GROUP_POW_MUL]);;

let GROUP_COMMUTES_POW = prove
 (`!G (x:A) (y:A) n.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_mul G (group_pow G x n) y = group_mul G y (group_pow G x n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; GROUP_MUL_LID; GROUP_MUL_RID] THEN
  ASM_MESON_TAC[GROUP_MUL_ASSOC; GROUP_POW]);;

let GROUP_MUL_POW = prove
 (`!G (x:A) (y:A) n.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_pow G (group_mul G x y) n =
            group_mul G (group_pow G x n) (group_pow G y n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; GROUP_MUL_LID; GROUP_ID] THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL; GROUP_POW] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 group_pow)] THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL; GROUP_POW] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 group_pow)] THEN
  ASM_MESON_TAC[GROUP_COMMUTES_POW]);;

let group_zpow = new_definition
 `group_zpow G (x:A) n =
    if &0 <= n then group_pow G x (num_of_int n)
    else group_inv G (group_pow G x (num_of_int(--n)))`;;

let GROUP_ZPOW = prove
 (`!G (x:A) n. x IN group_carrier G ==> group_zpow G x n IN group_carrier G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_zpow] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_POW; GROUP_INV]);;

let GROUP_NPOW = prove
 (`!G (x:A) n. group_zpow G x (&n) = group_pow G x n`,
  REWRITE_TAC[NUM_OF_INT_OF_NUM; group_zpow; INT_POS]);;

let GROUP_ZPOW_0 = prove
 (`!G (x:A). group_zpow G x (&0) = group_id G`,
  REWRITE_TAC[GROUP_NPOW; GROUP_POW_0]);;

let GROUP_ZPOW_1 = prove
 (`!G x:A. x IN group_carrier G ==> group_zpow G x (&1) = x`,
  REWRITE_TAC[GROUP_NPOW; GROUP_POW_1]);;

let GROUP_ZPOW_2 = prove
 (`!G x:A. x IN group_carrier G ==> group_zpow G x (&2) = group_mul G x x`,
  REWRITE_TAC[GROUP_NPOW; GROUP_POW_2]);;

let GROUP_ZPOW_ID = prove
 (`!n. group_zpow G (group_id G) n = group_id G`,
  GEN_TAC THEN REWRITE_TAC[group_zpow; GROUP_POW_ID; GROUP_INV_ID; COND_ID]);;

let GROUP_ZPOW_NEG = prove
 (`!G (x:A) n.
        x IN group_carrier G
        ==> group_zpow G x (--n) = group_inv G (group_zpow G x n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_NEG_0; GROUP_NPOW; group_pow; GROUP_INV_ID] THEN
  REWRITE_TAC[group_zpow; INT_NEG_NEG] THEN
  ASM_SIMP_TAC[INT_ARITH `~(n:int = &0) ==> (&0 <= --n <=> ~(&0 <= n))`] THEN
  ASM_CASES_TAC `&0:int <= n` THEN
  ASM_SIMP_TAC[GROUP_INV_INV; GROUP_POW]);;

let GROUP_ZPOW_MINUS1 = prove
 (`!G x:A. x IN group_carrier G ==> group_zpow G x (-- &1) = group_inv G x`,
  SIMP_TAC[GROUP_ZPOW_NEG; GROUP_ZPOW_1]);;

let GROUP_ZPOW_POW = prove
 (`(!G (x:A) n. group_zpow G x (&n) = group_pow G x n) /\
   (!G (x:A) n. group_zpow G x (-- &n) = group_inv G (group_pow G x n))`,
  SIMP_TAC[group_zpow; INT_POS; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ; INT_NEG_0;
           INT_NEG_NEG; INT_ARITH `&0:int <= -- &n <=> &n:int = &0`] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[group_pow; GROUP_INV_ID]);;

let GROUP_ZPOW_ADD = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m + n) =
            group_mul G (group_zpow G x m) (group_zpow G x n)`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_THEN MP_TAC(SPEC `n:int` INT_IMAGE) THEN
  DISJ_CASES_THEN MP_TAC(SPEC `m:int` INT_IMAGE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:num` THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `q:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM INT_NEG_ADD; GROUP_ZPOW_NEG; GROUP_NPOW;
               INT_OF_NUM_ADD] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[GROUP_POW_ADD];
    DISJ_CASES_TAC(ARITH_RULE `p:num <= q \/ q <= p`) THENL
     [ASM_REWRITE_TAC[INT_ARITH `--x + y:int = y - x`];
      ASM_REWRITE_TAC[INT_ARITH `--x + y:int = --(x - y)`]] THEN
    ASM_SIMP_TAC[GROUP_ZPOW_NEG; INT_OF_NUM_SUB; GROUP_NPOW] THEN
    ASM_SIMP_TAC[GROUP_POW_SUB_ALT; GROUP_INV_MUL; GROUP_INV_INV;
                 GROUP_POW; GROUP_INV; GROUP_MUL];
    DISJ_CASES_TAC(ARITH_RULE `q:num <= p \/ p <= q`) THENL
     [ASM_REWRITE_TAC[INT_ARITH `y + --x:int = y - x`];
      ASM_REWRITE_TAC[INT_ARITH `y + --x:int = --(x - y)`]] THEN
    ASM_SIMP_TAC[GROUP_ZPOW_NEG; INT_OF_NUM_SUB; GROUP_NPOW] THEN
    ASM_SIMP_TAC[GROUP_POW_SUB; GROUP_INV_MUL; GROUP_INV_INV;
                 GROUP_POW; GROUP_INV; GROUP_MUL; group_div];
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_SIMP_TAC[GROUP_POW_ADD; GROUP_INV_MUL; GROUP_POW]]);;

let GROUP_ZPOW_SUB = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m - n) =
            group_div G (group_zpow G x m) (group_zpow G x n)`,
  SIMP_TAC[group_div; INT_SUB; GROUP_ZPOW_ADD; GROUP_ZPOW_NEG]);;

let GROUP_ZPOW_SUB_ALT = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m - n) =
            group_mul G (group_inv G (group_zpow G x n)) (group_zpow G x m)`,
  REWRITE_TAC[INT_ARITH `x - y:int = --y + x`] THEN
  SIMP_TAC[GROUP_ZPOW_ADD; GROUP_ZPOW_NEG]);;

let GROUP_INV_ZPOW = prove
 (`!G (x:A) n.
        x IN group_carrier G
        ==> group_inv G (group_zpow G x n) = group_zpow G (group_inv G x) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_zpow] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_INV_POW]);;

let GROUP_ZPOW_MUL = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> group_zpow G x (m * n) = group_zpow G (group_zpow G x m) n`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_THEN MP_TAC(SPEC `n:int` INT_IMAGE) THEN
  DISJ_CASES_THEN MP_TAC(SPEC `m:int` INT_IMAGE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:num` THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `q:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_NEG; INT_OF_NUM_MUL; GROUP_NPOW;
               GROUP_INV; GROUP_POW; GROUP_POW_MUL; GROUP_INV_POW;
               GROUP_INV_INV]);;

let GROUP_COMMUTES_ZPOW = prove
 (`!G (x:A) (y:A) n.
      x IN group_carrier G /\ y IN group_carrier G /\
      group_mul G x y = group_mul G y x
      ==> group_mul G (group_zpow G x n) y = group_mul G y (group_zpow G x n)`,
  REWRITE_TAC[FORALL_INT_CASES; GROUP_ZPOW_POW] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GROUP_COMMUTES_POW] THEN ASM_SIMP_TAC[GROUP_INV_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_COMMUTES_POW THEN
  ASM_MESON_TAC[GROUP_COMMUTES_INV; GROUP_INV]);;

let GROUP_MUL_ZPOW = prove
 (`!G (x:A) (y:A) n.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_zpow G (group_mul G x y) n =
            group_mul G (group_zpow G x n) (group_zpow G y n)`,
  REWRITE_TAC[FORALL_INT_CASES; GROUP_ZPOW_POW; GROUP_MUL_POW] THEN
  SIMP_TAC[GSYM GROUP_INV_MUL; GROUP_POW; GROUP_INV] THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_POW]);;

(* ------------------------------------------------------------------------- *)
(* Abelian groups.                                                           *)
(* ------------------------------------------------------------------------- *)

let abelian_group = new_definition
 `abelian_group (G:A group) <=>
  !x y. x IN group_carrier G /\ y IN group_carrier G
        ==> group_mul G x y = group_mul G y x`;;

let TRIVIAL_IMP_ABELIAN_GROUP = prove
 (`!G:A group. trivial_group G ==> abelian_group G`,
  SIMP_TAC[trivial_group; abelian_group; IN_SING]);;

let ABELIAN_SINGLETON_GROUP = prove
 (`!a:A. abelian_group(singleton_group a)`,
  SIMP_TAC[TRIVIAL_IMP_ABELIAN_GROUP; TRIVIAL_GROUP_SINGLETON_GROUP]);;

let ABELIAN_OPPOSITE_GROUP = prove
 (`!G:A group. abelian_group (opposite_group G) <=> abelian_group G`,
  SIMP_TAC[abelian_group; OPPOSITE_GROUP_MUL; OPPOSITE_GROUP] THEN
  MESON_TAC[]);;

let ABELIAN_GROUP_MUL_POW = prove
 (`!G (x:A) (y:A) n.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_pow G (group_mul G x y) n =
            group_mul G (group_pow G x n) (group_pow G y n)`,
  MESON_TAC[GROUP_MUL_POW; abelian_group]);;

let ABELIAN_GROUP_MUL_ZPOW = prove
 (`!G (x:A) (y:A) n.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_zpow G (group_mul G x y) n =
            group_mul G (group_zpow G x n) (group_zpow G y n)`,
  MESON_TAC[GROUP_MUL_ZPOW; abelian_group]);;

let ABELIAN_GROUP_DIV_ZPOW = prove
 (`!G x (y:A) n.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_zpow G (group_div G x y) n =
            group_div G (group_zpow G x n) (group_zpow G y n)`,
  MESON_TAC[group_div; GROUP_INV_ZPOW; ABELIAN_GROUP_MUL_ZPOW; GROUP_INV]);;

let ABELIAN_GROUP_MUL_AC = prove
 (`!G:A group.
        abelian_group G <=>
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> group_mul G x y = group_mul G y x) /\
        (!x y z. x IN group_carrier G /\ y IN group_carrier G /\
                 z IN group_carrier G
                 ==> group_mul G (group_mul G x y) z =
                     group_mul G x (group_mul G y z)) /\
        (!x y z. x IN group_carrier G /\ y IN group_carrier G /\
                 z IN group_carrier G
                 ==> group_mul G x (group_mul G y z) =
                     group_mul G y (group_mul G x z))`,
  REWRITE_TAC[abelian_group] THEN MESON_TAC[GROUP_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Totalized versions of the group operations (using additive terminology    *)
(* for variety's sake). This totalization can be quite convenient, e.g. for  *)
(* normalization and use of the "iterate" construct in the Abelian case.     *)
(* ------------------------------------------------------------------------- *)

let group_neg = new_definition
 `group_neg G x = if x IN group_carrier G then group_inv G x else x`;;

let group_add = new_definition
 `group_add G x (y:A) =
        if x IN group_carrier G /\ y IN group_carrier G
        then group_mul G x y
        else if x IN group_carrier G then y
        else if y IN group_carrier G then x
        else @w. ~(w IN group_carrier G)`;;

let group_nmul = new_recursive_definition num_RECURSION
 `group_nmul G 0 x = group_id G /\
  group_nmul G (SUC n) x = group_add G x (group_nmul G n x)`;;

let GROUP_NEG = prove
 (`!G x:A. group_neg G x IN group_carrier G <=> x IN group_carrier G`,
  REWRITE_TAC[group_neg] THEN MESON_TAC[GROUP_INV]);;

let GROUP_ADD = prove
 (`!G x y:A.
        group_add G x y IN group_carrier G <=>
        x IN group_carrier G /\ y IN group_carrier G`,
  REWRITE_TAC[group_add] THEN MESON_TAC[GROUP_MUL]);;

let GROUP_NEG_EQ_INV = prove
 (`!G x:A. x IN group_carrier G ==> group_neg G x = group_inv G x`,
  SIMP_TAC[group_neg]);;

let GROUP_ADD_EQ_MUL = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_add G x y = group_mul G x y`,
  SIMP_TAC[group_add]);;

let GROUP_ADD_LID = prove
 (`!G x:A. group_add G (group_id G) x = x`,
  SIMP_TAC[group_add; GROUP_ID; GROUP_MUL_LID; COND_ID]);;

let GROUP_ADD_RID = prove
 (`!G x:A. group_add G x (group_id G) = x`,
  SIMP_TAC[group_add; GROUP_ID; GROUP_MUL_RID; COND_ID]);;

let GROUP_ADD_ASSOC = prove
 (`!G x y z:A.
        group_add G x (group_add G y z) = group_add G (group_add G x y) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_add] THEN
  MAP_EVERY ASM_CASES_TAC
   [`(x:A) IN group_carrier G`;
    `(y:A) IN group_carrier G`;
    `(z:A) IN group_carrier G`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_MUL_ASSOC; COND_ID] THEN
  ASM_MESON_TAC[]);;

let GROUP_NEG_ADD = prove
 (`!G x y:A. group_neg G (group_add G x y) =
             group_add G (group_neg G y) (group_neg G x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_add; group_neg] THEN
  MAP_EVERY ASM_CASES_TAC
   [`(x:A) IN group_carrier G`;
    `(y:A) IN group_carrier G`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV_MUL; GROUP_INV; COND_ID] THEN
  ASM_MESON_TAC[]);;

let GROUP_NEG_NEG = prove
 (`!G x:A. group_neg G (group_neg G x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_neg] THEN
  MESON_TAC[GROUP_INV; GROUP_INV_INV]);;

let GROUP_NEG_ID = prove
 (`!G x:A. group_neg G (group_id G) = group_id G`,
  SIMP_TAC[group_neg; GROUP_INV_ID; GROUP_ID]);;

let GROUP_ADD_EQ_ID = prove
 (`!G x y:A. group_add G x y = group_id G <=> group_add G y x = group_id G`,
  REWRITE_TAC[group_add] THEN
  ASM_MESON_TAC[GROUP_ID; GROUP_ADD; GROUP_MUL_EQ_ID]);;

let GROUP_NEG_EQ_ID = prove
 (`!G x:A. group_neg G x = group_id G <=> x = group_id G`,
  MESON_TAC[GROUP_ID; GROUP_NEG; GROUP_INV_EQ_ID; GROUP_NEG_EQ_INV]);;

let GROUP_NMUL_EQ_POW = prove
 (`!G (x:A) n. x IN group_carrier G ==> group_nmul G n x = group_pow G x n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[group_nmul; group_pow; GROUP_ADD_EQ_MUL; GROUP_POW]);;

let GROUP_NMUL_ADD = prove
 (`!G (x:A) m n.
        group_nmul G (m + n) x =
        group_add G (group_nmul G m x) (group_nmul G n x)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_nmul; ADD_CLAUSES; GROUP_ADD_LID] THEN
  REWRITE_TAC[GROUP_ADD_ASSOC]);;

let GROUP_NMUL_MUL = prove
 (`!G (x:A) m n.
        group_nmul G (m * n) x = group_nmul G m (group_nmul G n x)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 group_nmul; MULT_CLAUSES] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_REWRITE_TAC[GROUP_NMUL_ADD; CONJUNCT2 group_nmul]);;

let GROUP_NMUL_1 = prove
 (`!G x:A. group_nmul G 1 x = x`,
  REWRITE_TAC[num_CONV `1`; group_nmul; GROUP_ADD_RID]);;

let GROUP_NEG_NMUL = prove
 (`!G (x:A) n.
        group_neg G (group_nmul G n x) = group_nmul G n (group_neg G x)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[group_nmul; GROUP_NEG_ID]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [group_nmul] THEN
  REWRITE_TAC[ADD1; GROUP_NMUL_ADD; GROUP_NEG_ADD] THEN
  ASM_REWRITE_TAC[GROUP_NMUL_1]);;

let GROUP_ADD_SYM = prove
 (`!G x y:A. abelian_group G ==> group_add G x y = group_add G y x`,
  SIMP_TAC[group_add; abelian_group] THEN MESON_TAC[]);;

let GROUP_ADD_SYM_EQ = prove
 (`!G:A group. (!x y. group_add G x y = group_add G y x) <=> abelian_group G`,
  REWRITE_TAC[group_add; abelian_group] THEN MESON_TAC[]);;

let GROUP_ADD_NMUL = prove
 (`!G (x:A) y n.
        abelian_group G
        ==> group_nmul G n (group_add G x y) =
            group_add G (group_nmul G n x) (group_nmul G n y)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_nmul; GROUP_ADD_LID] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GROUP_ADD_SYM_EQ]) THEN
  REWRITE_TAC[GROUP_ADD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[GROUP_ADD_ASSOC]);;

let NEUTRAL_GROUP_ADD = prove
 (`!G:A group. neutral(group_add G) = group_id G`,
  GEN_TAC THEN REWRITE_TAC[neutral] THEN
  MESON_TAC[GROUP_ADD_LID; GROUP_ADD_RID]);;

let MONOIDAL_GROUP_ADD = prove
 (`!G:A group. monoidal(group_add G) <=> abelian_group G`,
  REWRITE_TAC[monoidal; GROUP_ADD_ASSOC; NEUTRAL_GROUP_ADD; GROUP_ADD_LID;
              GSYM GROUP_ADD_SYM_EQ]);;

let ABELIAN_GROUP_SUM = prove
 (`!G (x:K->A) k.
        abelian_group G /\
        (!i. i IN k ==> x i IN group_carrier G) /\
        FINITE {i | i IN k /\ ~(x i = group_id G)}
        ==> iterate (group_add G) k x IN group_carrier G`,
  REWRITE_TAC[GSYM MONOIDAL_GROUP_ADD] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o
   REWRITE_RULE[NEUTRAL_GROUP_ADD; GROUP_ID; GROUP_ADD] o
   ISPEC `\x:A. x IN group_carrier G` o MATCH_MP
    (INST_TYPE [`:K`,`:A`; `:A`,`:B`] ITERATE_CLOSED)) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Procedure for equations s = t or equivalences s = t <=> s' = t' in        *)
(* the theory of groups, which will generate carrier membership              *)
(* conditions if they are not explicitly presented as an implication,        *)
(* e.g.                                                                      *)
(*                                                                           *)
(* GROUP_RULE                                                                *)
(*  `group_mul G a (group_inv G (group_mul G b a)) =                         *)
(*   group_inv G (group_mul G (group_inv G c) (group_mul G c b))`;;          *)
(*                                                                           *)
(* GROUP_RULE                                                                *)
(*  `!G x y z:A.                                                             *)
(*         x IN group_carrier G /\                                           *)
(*         y IN group_carrier G /\                                           *)
(*         z IN group_carrier G                                              *)
(*         ==> (group_mul G (group_div G z y)                                *)
(*                          (group_mul G x (group_div G y z)) =              *)
(*              group_id G <=>                                               *)
(*              group_inv G (group_mul G x y) = group_inv G y)`;;            *)
(* ------------------------------------------------------------------------- *)

let GROUP_RULE =
  let rec GROUP_MEM tm =
    if is_conj tm then CONJ (GROUP_MEM(lhand tm)) (GROUP_MEM(rand tm)) else
    try PART_MATCH I GROUP_ID tm with Failure _ ->
    try let th = try PART_MATCH rand GROUP_INV tm with Failure _ ->
                 try PART_MATCH rand GROUP_POW tm with Failure _ ->
                 try PART_MATCH rand GROUP_ZPOW tm with Failure _ ->
                 try PART_MATCH rand GROUP_MUL tm with Failure _ ->
                 PART_MATCH rand GROUP_DIV tm in
        MP th (GROUP_MEM(lhand(concl th)))
    with Failure _ -> ASSUME tm in
  let GROUP_REWR_CONV th =
    if not(is_imp(snd(strip_forall(concl th)))) then REWR_CONV th else
    let mfn = PART_MATCH (lhand o rand) th in
    fun tm -> let ith = mfn tm in MP ith (GROUP_MEM(lhand(concl ith))) in
  let GROUP_CANONIZE_CONV =
    let mfn_inv = (MATCH_MP o prove)
     (`!G t t':A.
            t = t' /\ t IN group_carrier G
            ==> group_inv G t = group_neg G t' /\
                group_inv G t IN group_carrier G`,
      SIMP_TAC[IMP_CONJ; group_neg; GROUP_INV])
    and mfn_neg = (MATCH_MP o prove)
     (`!G t t':A.
            t = t' /\ t IN group_carrier G
            ==> group_neg G t = group_neg G t' /\
                group_neg G t IN group_carrier G`,
      SIMP_TAC[GROUP_NEG])
    and mfn_pow = (MATCH_MP o prove)
     (`!G t (t':A) n.
            t = t' /\ t IN group_carrier G
            ==> group_pow G t n = group_nmul G n t' /\
                group_pow G t n IN group_carrier G`,
      SIMP_TAC[GROUP_NMUL_EQ_POW; IMP_CONJ; GROUP_POW])
    and mfn_nmul = (MATCH_MP o prove)
     (`!G t (t':A) n.
            t = t' /\ t IN group_carrier G
            ==> group_nmul G n t = group_nmul G n t' /\
                group_nmul G n t IN group_carrier G`,
      SIMP_TAC[GROUP_NMUL_EQ_POW; GROUP_POW; IMP_CONJ])
    and mfn_mul = (MATCH_MP o prove)
     (`!G s t s' t':A.
            (s = s' /\ s IN group_carrier G) /\
            (t = t' /\ t IN group_carrier G)
            ==> group_mul G s t = group_add G s' t' /\
                group_mul G s t IN group_carrier G`,
      SIMP_TAC[IMP_CONJ; group_add; GROUP_MUL])
    and mfn_add = (MATCH_MP o prove)
     (`!G s t s' t':A.
            (s = s' /\ s IN group_carrier G) /\
            (t = t' /\ t IN group_carrier G)
            ==> group_add G s t = group_add G s' t' /\
                group_add G s t IN group_carrier G`,
      SIMP_TAC[GROUP_ADD])
    and in_tm = `(IN):A->(A->bool)->bool`
    and gc_tm = `group_carrier:(A)group->A->bool` in
    let rec GROUP_TOTALIZE g tm =
      match tm with
        Comb(Comb(Comb(Const("group_mul",_),g),s),t) ->
            mfn_mul(CONJ (GROUP_TOTALIZE g s) (GROUP_TOTALIZE g t))
      | Comb(Comb(Comb(Const("group_add",_),g),s),t) ->
            mfn_add(CONJ (GROUP_TOTALIZE g s) (GROUP_TOTALIZE g t))
      | Comb(Comb(Comb(Const("group_pow",_),g),t),n) ->
            SPEC n (mfn_pow(GROUP_TOTALIZE g t))
      | Comb(Comb(Comb(Const("group_nmul",_),g),n),t) ->
            SPEC n (mfn_nmul(GROUP_TOTALIZE g t))
      | Comb(Comb(Const("group_inv",_),g),t) ->
            mfn_inv(GROUP_TOTALIZE g t)
      | Comb(Comb(Const("group_neg",_),g),t) ->
            mfn_neg(GROUP_TOTALIZE g t)
      | Comb(Const("group_id",_),g) ->
          CONJ (REFL tm) (ISPEC g GROUP_ID)
      | _ ->
          let ifn = inst[type_of tm,aty] in
          CONJ (REFL tm)
               (ASSUME(mk_comb(mk_comb(ifn in_tm,tm),mk_comb(ifn gc_tm,g)))) in
    let GROUP_CANONIZE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("group_mul",_),g),s),t)
      | Comb(Comb(Comb(Const("group_add",_),g),s),t)
      | Comb(Comb(Comb(Const("group_pow",_),g),s),t)
      | Comb(Comb(Comb(Const("group_nmul",_),g),s),t) ->
          CONJUNCT1(GROUP_TOTALIZE g tm)
      | Comb(Comb(Const("group_inv",_),g),t)
      | Comb(Comb(Const("group_neg",_),g),t) ->
          CONJUNCT1(GROUP_TOTALIZE g tm)
      | _ -> REFL tm in
    NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GROUP_ZPOW_POW; group_div] THENC
    GROUP_CANONIZE_CONV in
  let GROUP_NORM_CONV =
    let conv = (FIRST_CONV o map GROUP_REWR_CONV o CONJUNCTS o prove)
     (`(!G x:A. x IN group_carrier G
                ==> group_add G x (group_neg G x) = group_id G) /\
       (!G x:A. x IN group_carrier G
                ==> group_add G (group_neg G x) x = group_id G) /\
       (!G x y:A. x IN group_carrier G
                ==> group_add G x (group_add G (group_neg G x) y) = y) /\
       (!G x y:A. x IN group_carrier G
                ==> group_add G (group_neg G x) (group_add G x y) = y)`,
      REWRITE_TAC[GROUP_ADD_ASSOC] THEN
      SIMP_TAC[GROUP_NEG_EQ_INV; GROUP_ADD_EQ_MUL; GROUP_MUL_LINV;
               GROUP_MUL_RINV; GROUP_INV; GROUP_ADD_LID]) in
    let rec GROUP_NMUL_CONV tm =
      try REWR_CONV (CONJUNCT1 group_nmul) tm with Failure _ ->
      (LAND_CONV num_CONV THENC
       REWR_CONV(CONJUNCT2 group_nmul) THENC
       RAND_CONV GROUP_NMUL_CONV) tm in
    GROUP_CANONIZE_CONV THENC
    TOP_DEPTH_CONV GROUP_NMUL_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [GROUP_NEG_ADD; GROUP_NEG_NEG; GROUP_NEG_ID] THENC
    GEN_REWRITE_CONV DEPTH_CONV [GROUP_ADD_LID; GROUP_ADD_RID] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM GROUP_ADD_ASSOC] THENC
    TOP_DEPTH_CONV
     (GEN_REWRITE_CONV I [GROUP_ADD_LID; GROUP_ADD_RID] ORELSEC conv) in
  let GROUP_EQ_RULE tm =
    let l,r = dest_eq tm in
    TRANS (GROUP_NORM_CONV l) (SYM(GROUP_NORM_CONV r)) in
  let is_groupty ty = match ty with Tyapp("group",[a]) -> true | _ -> false in
  let rec list_of_gtm tm =
    match tm with
      Comb(Const("group_id",_),_) -> []
    | Comb(Comb(Const("group_neg",_),_),x) -> [false,x]
    | Comb(Comb(Comb(Const("group_add",_),_),
       Comb(Comb(Const("group_neg",_),_),x)),y) -> (false,x)::list_of_gtm y
    | Comb(Comb(Comb(Const("group_add",_),_),x),y) -> (true,x)::list_of_gtm y
    | _ -> [true,tm] in
  let find_rot l l' =
    find (fun n -> let l1,l2 = chop_list n l in l2@l1 = l')
         (0--(length l - 1)) in
  let rec GROUP_REASSOC_CONV n tm =
    if n = 0 then REFL tm
    else (REWR_CONV GROUP_ADD_ASSOC THENC GROUP_REASSOC_CONV(n-1)) tm in
  let GROUP_ROTATE_CONV n =
    if n = 0 then REFL else
    LAND_CONV(GROUP_REASSOC_CONV(n - 1)) THENC
    REWR_CONV GROUP_ADD_EQ_ID THENC
    LAND_CONV GROUP_NORM_CONV in
  let rec GROUP_EQ_HYPERNORM_CONV tm =
    let ts = list_of_gtm(lhand tm) in
    if length ts > 2 &
       (let p,v = hd ts and q,w = last ts in not(p = q) && v = w)
    then (GROUP_ROTATE_CONV 1 THENC GROUP_EQ_HYPERNORM_CONV) tm
    else REFL tm in
  fun tm ->
    let gvs = setify(find_terms (is_groupty o type_of) tm) in
    if gvs = [] then MESON[] tm else
    if length gvs > 1 then failwith "GROUP_RULE: Several groups involved" else
    let g = hd gvs in
    let GROUP_EQ_NORM_CONV =
      GROUP_REWR_CONV(GSYM(ISPEC g GROUP_DIV_EQ_ID)) THENC
      LAND_CONV GROUP_NORM_CONV in
    let avs,bod = strip_forall tm in
    let ant,con = if is_imp bod then [lhand bod],rand bod else [],bod in
    let th1 =
      if not(is_iff con) then GROUP_EQ_RULE con else
      let eq1,eq2 = dest_iff con in
      let th1 = (GROUP_EQ_NORM_CONV THENC GROUP_EQ_HYPERNORM_CONV) eq1
      and th2 = (GROUP_EQ_NORM_CONV THENC GROUP_EQ_HYPERNORM_CONV) eq2 in
      let ls1 = list_of_gtm(lhand(rand(concl th1)))
      and ls2 = list_of_gtm(lhand(rand(concl th2))) in
      try let n = find_rot ls1 ls2 in
          TRANS (CONV_RULE(RAND_CONV(GROUP_ROTATE_CONV n)) th1) (SYM th2)
      with Failure _ ->
          let th1' =
            GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV)
              [GSYM GROUP_ADD_ASSOC]
              (GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV)
               [GROUP_NEG_ADD; GROUP_NEG_NEG]
               (GEN_REWRITE_RULE RAND_CONV [GSYM GROUP_NEG_EQ_ID] th1))
          and ls1' = map (fun (p,v) -> not p,v) (rev ls1) in
          let n = find_rot ls1' ls2 in
          TRANS (CONV_RULE(RAND_CONV(GROUP_ROTATE_CONV n)) th1') (SYM th2) in
    let th2 =
      if ant = [] then th1
      else itlist PROVE_HYP (CONJUNCTS(ASSUME(hd ant))) th1 in
    let asl = hyp th2 in
    let th3 =
      if asl = [] then th2 else
      let asm = list_mk_conj asl in
      DISCH asm (itlist PROVE_HYP (CONJUNCTS(ASSUME asm)) th2) in
    let th4 = GENL avs th3 in
    let bvs = frees(concl th4) in
    GENL (sort (<) bvs) th4;;

let GROUP_TAC =
  REPEAT GEN_TAC THEN
  TRY(MATCH_MP_TAC(MESON[] `(u = v <=> s = t) ==> (u = v ==> s = t)`)) THEN
  W(fun (asl,w) ->
        let th = GROUP_RULE w in
        (MATCH_ACCEPT_TAC th ORELSE
         (MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])));;

(* ------------------------------------------------------------------------- *)
(* Iterated operation on groups, the first one being in a specific           *)
(* order given as an argument, the latter picking some arbitrary             *)
(* wellorder, usually with the expectation that it will be immaterial.       *)
(* ------------------------------------------------------------------------- *)

let group_product = new_definition
 `group_product (G:A group) =
        iterato (group_carrier G) (group_id G) (group_mul G)`;;

let group_sum = new_definition
 `group_sum (G:A group) =
        group_product G (@l. woset l /\ fld l = (:K))`;;

let GROUP_PRODUCT_EQ = prove
 (`!G (<<=) k (f:K->A) g.
        (!i. i IN k ==> f i = g i)
        ==> group_product G (<<=) k f = group_product G (<<=) k g`,
  REWRITE_TAC[group_product; ITERATO_EQ]);;

let GROUP_SUM_EQ = prove
 (`!G k (f:K->A) g.
        (!i. i IN k ==> f i = g i) ==> group_sum G k f = group_sum G k g`,
  REWRITE_TAC[group_sum; GROUP_PRODUCT_EQ]);;

let GROUP_PRODUCT_CLOSED = prove
 (`!P G (<<=) k (f:K->A).
       P(group_id G) /\
       (!x y. x IN group_carrier G /\ y IN group_carrier G /\
              P x /\ P y
              ==> P(group_mul G x y)) /\
       (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G) ==> P(f i))
       ==> P(group_product G (<<=) k f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_product] THEN
  MP_TAC(ISPECL
   [`group_carrier G:A->bool`; `group_id G:A`; `group_mul G:A->A->A`;
    `(<<=):K->K->bool`; `k:K->bool`; `f:K->A`;
    `\x:A. x IN group_carrier G /\ P x`]
   ITERATO_CLOSED) THEN
  ASM_SIMP_TAC[GROUP_ID; GROUP_MUL]);;

let GROUP_SUM_CLOSED = prove
 (`!P G k (f:K->A).
       P(group_id G) /\
       (!x y. x IN group_carrier G /\ y IN group_carrier G /\
              P x /\ P y
              ==> P(group_mul G x y)) /\
       (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G) ==> P(f i))
       ==> P(group_sum G k f)`,
  REWRITE_TAC[group_sum; GROUP_PRODUCT_CLOSED]);;

let GROUP_PRODUCT = prove
 (`!G (<<=) k (f:K->A). group_product G (<<=) k f IN group_carrier G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (REWRITE_RULE[]
   (ISPEC `\x:A. x IN group_carrier G` GROUP_PRODUCT_CLOSED)) THEN
  SIMP_TAC[GROUP_ID; GROUP_MUL]);;

let GROUP_SUM = prove
 (`!G k (f:K->A). group_sum G k f IN group_carrier G`,
  REWRITE_TAC[group_sum; GROUP_PRODUCT]);;

let GROUP_PRODUCT_SUPPORT = prove
 (`!G (<<=) k (f:K->A).
        group_product G (<<=) {i | i IN k /\ ~(f i = group_id G)} f =
        group_product G (<<=) k f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_product] THEN
  ONCE_REWRITE_TAC[GSYM ITERATO_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let GROUP_SUM_SUPPORT = prove
 (`!G k (f:K->A).
      group_sum G {i | i IN k /\ ~(f i = group_id G)} f =
      group_sum G k f`,
  REWRITE_TAC[group_sum; GROUP_PRODUCT_SUPPORT]);;

let GROUP_PRODUCT_RESTRICT = prove
 (`!G (<<=) k (f:K->A).
        group_product G (<<=) {i | i IN k /\ f i IN group_carrier G} f =
        group_product G (<<=) k f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_product] THEN
  ONCE_REWRITE_TAC[GSYM ITERATO_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let GROUP_SUM_RESTRICT = prove
 (`!G k (f:K->A).
        group_sum G {i | i IN k /\ f i IN group_carrier G} f =
        group_sum G k f`,
  REWRITE_TAC[group_sum; GROUP_PRODUCT_RESTRICT]);;

let GROUP_PRODUCT_EXPAND_CASES = prove
 (`!G (<<=) k (f:K->A).
        group_product G (<<=) k f =
        if FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}}
        then group_product G (<<=)
              {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} f
        else group_id G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_product] THEN
  MATCH_ACCEPT_TAC ITERATO_EXPAND_CASES);;

let GROUP_SUM_EXPAND_CASES = prove
 (`!G k (f:K->A).
        group_sum G k f =
        if FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}}
        then group_sum G
              {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} f
        else group_id G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_sum] THEN
  MATCH_ACCEPT_TAC GROUP_PRODUCT_EXPAND_CASES);;

let GROUP_PRODUCT_CLAUSES = prove
 (`!G (<<=) (f:K->A).
      group_product G (<<=) {} f = group_id G /\
      (!i k. FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}} /\
             (!j. j IN k ==> i <<= j /\ ~(j <<= i))
             ==> group_product G (<<=) (i INSERT k) f =
                   if f i IN group_carrier G ==> i IN k
                   then group_product G (<<=) k f
                   else group_mul G (f i) (group_product G (<<=) k f))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[group_product; ITERATO_CLAUSES] THEN
  ASM_CASES_TAC `(i:K) IN k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(f:K->A) i = group_id G` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GROUP_MUL_LID; GSYM group_product; GROUP_PRODUCT; GROUP_ID]);;

let GROUP_PRODUCT_CLAUSES_EXISTS = prove
 (`!G (<<=) (f:K->A).
      group_product G (<<=) {} f = group_id G /\
      (!k. FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} /\
           ~({i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} = {})
           ==> ?i. i IN k /\
                   f i IN group_carrier G DIFF {group_id G} /\
                   group_product G (<<=) k f =
                   group_mul G (f i) (group_product G (<<=) (k DELETE i) f))`,
  REWRITE_TAC[group_product] THEN
  MATCH_ACCEPT_TAC ITERATO_CLAUSES_EXISTS);;

let GROUP_SUM_CLAUSES_EXISTS = prove
 (`!G (f:K->A).
      group_sum G {} f = group_id G /\
      (!k. FINITE {i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} /\
           ~({i | i IN k /\ f i IN group_carrier G DIFF {group_id G}} = {})
           ==> ?i. i IN k /\
                   f i IN group_carrier G DIFF {group_id G} /\
                   group_sum G k f =
                   group_mul G (f i) (group_sum G (k DELETE i) f))`,
  REWRITE_TAC[group_sum] THEN MATCH_ACCEPT_TAC GROUP_PRODUCT_CLAUSES_EXISTS);;

let GROUP_COMMUTES_PRODUCT = prove
 (`!G (<<=) k (f:K->A) z.
        (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G)
             ==> group_mul G (f i) z = group_mul G z (f i)) /\
        z IN group_carrier G
        ==> group_mul G (group_product G (<<=) k f) z =
            group_mul G z (group_product G (<<=) k f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[]
   (ISPEC `\x:A. group_mul G x z = group_mul G z x` GROUP_PRODUCT_CLOSED)) THEN
  ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID] THEN
  ASM_MESON_TAC[GROUP_COMMUTES_MUL]);;

let GROUP_COMMUTES_SUM = prove
 (`!G k (f:K->A) z.
        (!i. i IN k /\ f i IN group_carrier G /\ ~(f i = group_id G)
             ==> group_mul G (f i) z = group_mul G z (f i)) /\
        z IN group_carrier G
        ==> group_mul G (group_sum G k f) z = group_mul G z (group_sum G k f)`,
  REWRITE_TAC[group_sum; GROUP_COMMUTES_PRODUCT]);;

let GROUP_PRODUCT_SING = prove
 (`!G (<<=) i (f:K->A).
        group_product G (<<=) {i} f =
        if f i IN group_carrier G then f i else group_id G`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GROUP_PRODUCT_CLAUSES; NOT_IN_EMPTY; EMPTY_GSPEC; FINITE_EMPTY] THEN
  SIMP_TAC[COND_SWAP; GROUP_MUL_RID]);;

let GROUP_SUM_SING = prove
 (`!G i (f:K->A).
        group_sum G {i} f =
        if f i IN group_carrier G then f i else group_id G`,
  REWRITE_TAC[group_sum; GROUP_PRODUCT_SING]);;

let GROUP_PRODUCT_UNION = prove
 (`!G (<<=) (f:K->A) s t.
        woset(<<=) /\ fld(<<=) = (:K) /\
        (FINITE {i | i IN s /\ f i IN group_carrier G DIFF {group_id G}} <=>
         FINITE {i | i IN t /\ f i IN group_carrier G DIFF {group_id G}}) /\
        (!x y. x IN s /\ y IN t ==> x <<= y /\ ~(x = y))
        ==> group_product G (<<=) (s UNION t) f =
            group_mul G (group_product G (<<=) s f)
                        (group_product G (<<=) t f)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GROUP_PRODUCT_EXPAND_CASES] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN s UNION t /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  REWRITE_TAC[FINITE_UNION] THEN ASM_CASES_TAC
  `FINITE {i | i IN t /\ (f:K->A) i IN group_carrier G DIFF {group_id G}}` THEN
  ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_ID] THEN
  SUBGOAL_THEN
   `(!i. i IN {i | i IN s /\ (f:K->A) i IN group_carrier G DIFF {group_id G}}
         ==> f i IN group_carrier G /\ ~(f i = group_id G)) /\
    (!i. i IN {i | i IN t /\ (f:K->A) i IN group_carrier G DIFF {group_id G}}
         ==> f i IN group_carrier G /\ ~(f i = group_id G))`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN {i | i IN s /\ f i IN group_carrier G DIFF {group_id G}} /\
          y IN {i | i IN t /\ (f:K->A) i IN group_carrier G DIFF {group_id G}}
          ==> x <<= y /\ ~(x = y)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (TAUT `(p <=> q) ==> (q ==> q /\ p)`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`fld(<<=) = (:K)`; `woset((<<=):K->K->bool)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`{i | i IN s /\ (f:K->A) i IN group_carrier G DIFF {group_id G}}`,
           `s:K->bool`) THEN
  SPEC_TAC(`{i | i IN t /\ (f:K->A) i IN group_carrier G DIFF {group_id G}}`,
           `t:K->bool`) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `t:K->bool` THEN DISCH_TAC THEN ASM_CASES_TAC
   `!i. i IN t ==> (f:K->A) i IN group_carrier G /\ ~(f i = group_id G)` THEN
  ASM_REWRITE_TAC[GSYM CONJ_ASSOC; IMP_IMP] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC(MESON[]
   `(!n s. FINITE s /\ CARD s = n ==> P s) ==> !s. FINITE s ==> P s`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:K->bool` THEN
  ASM_CASES_TAC `s:K->bool = {}` THEN
  ASM_REWRITE_TAC[UNION_EMPTY; GROUP_PRODUCT_CLAUSES_EXISTS] THEN
  SIMP_TAC[GROUP_MUL_LID; GROUP_PRODUCT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:K->bool` o last o CONJUNCTS o
        GEN_REWRITE_RULE I [woset]) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `i:K` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `(<<=):K->K->bool`; `f:K->A`]
        GROUP_PRODUCT_CLAUSES) THEN
  DISCH_THEN(MP_TAC o SPEC `i:K` o CONJUNCT2) THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `s DELETE (i:K)` th) THEN
    MP_TAC(SPEC `(s DELETE (i:K)) UNION t` th)) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_UNION; FINITE_RESTRICT;
    IN_DELETE; IN_UNION;
    SET_RULE `i IN s ==> i INSERT (s DELETE i) = s`;
    SET_RULE `i IN s ==> i INSERT (s DELETE i UNION t) = s UNION t`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s DELETE (i:K)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL; GROUP_PRODUCT]);;

let GROUP_PRODUCT_CLAUSES_LEFT = prove
 (`!G (f:num->A) m n.
        group_product G (<=) (m..n) f =
        if m <= n then
           if f m IN group_carrier G
           then group_mul G (f m) (group_product G (<=) (m+1..n) f)
           else group_product G (<=) (m+1..n) f
         else group_id G`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM NUMSEG_LREC];
    ASM_SIMP_TAC[EMPTY_NUMSEG; GSYM NOT_LE; GROUP_PRODUCT_CLAUSES]] THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_PRODUCT_UNION o lhand o snd) THEN
  SIMP_TAC[WOSET_num; FLD_num; FINITE_RESTRICT; FINITE_SING; FINITE_NUMSEG;
           IN_NUMSEG; IN_SING] THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GROUP_PRODUCT_SING] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_PRODUCT]);;

let GROUP_PRODUCT_CLAUSES_RIGHT = prove
 (`!G (f:num->A) m n.
        group_product G (<=) (m..n) f =
        if m <= n then
           if f n IN group_carrier G
           then if n = 0 then f 0
                else group_mul G (group_product G (<=) (m..n-1) f) (f n)
           else group_product G (<=) (m..n-1) f
         else group_id G`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[CONJUNCT1 LE; SUB_0; NUMSEG_CLAUSES] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_SIMP_TAC[GROUP_PRODUCT_SING] THEN
    REWRITE_TAC[GROUP_PRODUCT_CLAUSES];
    ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[GSYM NUMSEG_RREC];
    ASM_SIMP_TAC[EMPTY_NUMSEG; GSYM NOT_LE; GROUP_PRODUCT_CLAUSES]] THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = s UNION {a}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_PRODUCT_UNION o lhand o snd) THEN
  SIMP_TAC[WOSET_num; FLD_num; FINITE_RESTRICT; FINITE_SING; FINITE_NUMSEG;
           IN_NUMSEG; IN_SING] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GROUP_PRODUCT_SING] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_MUL_RID; GROUP_PRODUCT]);;

let GROUP_PRODUCT_CLAUSES_NUMSEG = prove
 (`(!G m f:num->A.
        group_product G (<=) (m..0) f =
        if m = 0 /\ f 0 IN group_carrier G then f 0 else group_id G) /\
   (!G m n f:num->A.
        group_product G (<=) (m..SUC n) f =
        if m <= SUC n /\ f(SUC n) IN group_carrier G
        then group_mul G (group_product G (<=) (m..n) f) (f(SUC n))
        else group_product G (<=) (m..n) f)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GROUP_PRODUCT_CLAUSES_RIGHT] THEN
  SIMP_TAC[CONJUNCT1 LE; NOT_SUC; SUC_SUB1; SUB_0; NUMSEG_SING;
           GROUP_PRODUCT_SING]
  THENL [MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `m <= SUC n` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EMPTY_NUMSEG; ARITH_RULE `~(m <= SUC n) ==> n < m`] THEN
  REWRITE_TAC[GROUP_PRODUCT_CLAUSES]);;

let GROUP_PRODUCT_CLAUSES_COMMUTING = prove
 (`!G (<<=) i k (f:K->A).
        woset(<<=) /\ fld(<<=) = (:K) /\
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}} /\
        (!j. j IN k /\ j <<= i /\ ~(j = i) /\
             f i IN group_carrier G /\ f j IN group_carrier G
             ==> group_mul G (f i) (f j) = group_mul G (f j) (f i))
        ==> group_product G (<<=) (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_product G (<<=) k f
                else group_mul G (f i) (group_product G (<<=) k f)`,
  let tac pfn =
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_PRODUCT_UNION o pfn o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> q)`) THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (MESON[FINITE_INSERT; FINITE_SUBSET]
          `FINITE s ==> !i. t SUBSET i INSERT s ==> FINITE t`)) THEN
        EXISTS_TAC `i:K` THEN SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
        ASM_REWRITE_TAC[IN_UNIV] THEN ASM SET_TAC[];];
      DISCH_THEN SUBST1_TAC] in
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ONCE_REWRITE_TAC[GSYM GROUP_PRODUCT_RESTRICT] THEN
    ONCE_REWRITE_TAC[GSYM GROUP_PRODUCT_SUPPORT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [NOT_IMP])] THEN
  SUBGOAL_THEN
   `k = {j:K | j IN k /\ j <<= i /\ ~(j = i)} UNION
        {j | j IN k /\ i <<= j /\ ~(j = i)}`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[SET_RULE
     `i INSERT (l UNION r) = (i INSERT l) UNION r`]] THEN
  tac lhand THEN
  ONCE_REWRITE_TAC[SET_RULE `i INSERT s = s UNION {i}`] THEN
  tac (lhand o lhand) THEN
  tac (rand o rand) THEN
   ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_PRODUCT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[GROUP_PRODUCT_SING] THEN
  MATCH_MP_TAC GROUP_COMMUTES_PRODUCT THEN ASM SET_TAC[]);;

let ABELIAN_GROUP_PRODUCT_CLAUSES = prove
 (`!G (<<=) i k (f:K->A).
        woset(<<=) /\ fld(<<=) = (:K) /\
        abelian_group G /\
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}}
        ==> group_product G (<<=) (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_product G (<<=) k f
                else group_mul G (f i) (group_product G (<<=) k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_PRODUCT_CLAUSES_COMMUTING THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[abelian_group]);;

let GROUP_SUM_CLAUSES_COMMUTING = prove
 (`!G i k (f:K->A).
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}} /\
        (!j. j IN k /\ ~(j = i) /\
             f i IN group_carrier G /\ f j IN group_carrier G
             ==> group_mul G (f i) (f j) = group_mul G (f j) (f i))
        ==> group_sum G (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_sum G k f
                else group_mul G (f i) (group_sum G k f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_sum] THEN
  MATCH_MP_TAC GROUP_PRODUCT_CLAUSES_COMMUTING THEN ASM_SIMP_TAC[] THEN
  CONV_TAC SELECT_CONV THEN REWRITE_TAC[WO]);;

let ABELIAN_GROUP_SUM_CLAUSES = prove
 (`!G i k (f:K->A).
        abelian_group G /\
        FINITE {j | j IN k /\ f j IN group_carrier G DIFF {group_id G}}
        ==> group_sum G (i INSERT k) f =
                if f i IN group_carrier G ==> i IN k
                then group_sum G k f
                else group_mul G (f i) (group_sum G k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_SUM_CLAUSES_COMMUTING THEN
  ASM_MESON_TAC[abelian_group]);;

let GROUP_PRODUCT_MUL = prove
 (`!G (<<=) k f (g:K->A).
      woset(<<=) /\ fld(<<=) = (:K) /\
      FINITE {i | i IN k /\ ~(f i = group_id G)} /\
      FINITE {i | i IN k /\ ~(g i = group_id G)} /\
      (!i. i IN k ==> f i IN group_carrier G /\ g i IN group_carrier G) /\
      pairwise (\i j. group_mul G (f i) (g j) = group_mul G (g j) (f i)) k
      ==> group_product G (<<=) k (\i. group_mul G (f i) (g i)) =
          group_mul G (group_product G (<<=) k f) (group_product G (<<=) k g)`,
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV) [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (funpow 3 BINDER_CONV) [SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[GSYM FINITE_UNION] THEN
  X_GEN_TAC `s:K->bool` THEN
  W(fun (asl,w) -> ABBREV_TAC(mk_eq(`t:K->bool`,rand(lhand w)))) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `group_product G (<<=) t (\i. group_mul G (f i) (g i)) =
    group_mul G (group_product G (<<=) t (f:K->A)) (group_product G (<<=) t g)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `!i. i IN t ==> (f:K->A) i IN group_carrier G /\ g i IN group_carrier G`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:K->bool` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] PAIRWISE_MONO)) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; UNDISCH_TAC `FINITE(t:K->bool)`] THEN
    FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl));
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [ALL_TAC; BINOP_TAC] THEN
    ONCE_REWRITE_TAC[GSYM GROUP_PRODUCT_RESTRICT] THEN
    ONCE_REWRITE_TAC[GSYM GROUP_PRODUCT_SUPPORT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPEC `G:A group` GROUP_MUL_LID) THEN
    MP_TAC(ISPEC `G:A group` GROUP_MUL_RID) THEN ASM SET_TAC[]] THEN
  SPEC_TAC(`t:K->bool`,`s:K->bool`) THEN MATCH_MP_TAC(MESON[]
   `(!n s. FINITE s /\ CARD s = n ==> P s)
    ==> !s. FINITE s ==> P s`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:K->bool` THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN
    REWRITE_TAC[GROUP_PRODUCT_CLAUSES] THEN SIMP_TAC[GROUP_MUL_LID; GROUP_ID];
    REPEAT DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[CARD_EQ_0]
     `CARD s = n ==> FINITE s /\ ~(n = 0) ==> ~(s = {})`)) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [woset]) THEN
  ASM_REWRITE_TAC[IMP_IMP; SUBSET_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `(!s. ~(s = {}) ==> P s) /\ ~(t = {}) ==> P t`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = {i:K} UNION (s DELETE i)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_PRODUCT_UNION o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_RESTRICT; FINITE_SING] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_PRODUCT_UNION o
    lhand o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_RESTRICT; FINITE_SING] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_PRODUCT_UNION o
    rand o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_RESTRICT; FINITE_SING] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GROUP_PRODUCT_SING] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s DELETE (i:K)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] PAIRWISE_MONO)) THEN
    SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL; GROUP_PRODUCT] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL; GROUP_PRODUCT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_COMMUTES_PRODUCT THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN ASM SET_TAC[]);;

let GROUP_SUM_MUL = prove
 (`!G k f (g:K->A).
        FINITE {i | i IN k /\ ~(f i = group_id G)} /\
        FINITE {i | i IN k /\ ~(g i = group_id G)} /\
        (!i. i IN k ==> f i IN group_carrier G /\ g i IN group_carrier G) /\
        pairwise (\i j. group_mul G (f i) (g j) = group_mul G (g j) (f i)) k
        ==> group_sum G k (\i. group_mul G (f i) (g i)) =
            group_mul G (group_sum G k f) (group_sum G k g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_sum] THEN
  MATCH_MP_TAC GROUP_PRODUCT_MUL THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SELECT_CONV THEN REWRITE_TAC[WO]);;

let th = prove
 (`(!G (<<=) k f (g:K->A).
         (!i. i IN k ==> f i = g i)
         ==> group_product G (<<=) k (\i. f i) = group_product G (<<=) k g) /\
   (!G k f (g:K->A).
         (!i. i IN k ==> f i = g i)
         ==> group_sum G k (\i. f i) = group_sum G k g)`,
  REWRITE_TAC[ETA_AX; GROUP_PRODUCT_EQ; GROUP_SUM_EQ]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Congugation.                                                              *)
(* ------------------------------------------------------------------------- *)

let group_conjugation = new_definition
 `group_conjugation G a x = group_mul G a (group_mul G x (group_inv G a))`;;

let GROUP_CONJUGATION = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_conjugation G x y IN group_carrier G`,
  SIMP_TAC[group_conjugation; GROUP_MUL; GROUP_INV]);;

let GROUP_CONJUGATION_CONJUGATION = prove
 (`!G a b x:A.
        a IN group_carrier G /\ b IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G a (group_conjugation G b x) =
            group_conjugation G (group_mul G a b) x`,
  SIMP_TAC[group_conjugation] THEN GROUP_TAC);;

let GROUP_CONJUGATION_EQ = prove
 (`!G a x y:A.
        a IN group_carrier G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (group_conjugation G a x = group_conjugation G a y <=> x = y)`,
  REWRITE_TAC[group_conjugation] THEN GROUP_TAC);;

let GROUP_CONJUGATION_EQ_SELF = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_conjugation G x y = y <=>
             group_mul G x y = group_mul G y x)`,
  REWRITE_TAC[group_conjugation] THEN GROUP_TAC);;

let GROUP_CONJUGATION_EQ_ID = prove
 (`!G a x:A.
        a IN group_carrier G /\ x IN group_carrier G
        ==> (group_conjugation G a x = group_id G <=> x = group_id G)`,
  REWRITE_TAC[group_conjugation] THEN GROUP_TAC);;

let GROUP_CONJUGATION_BY_ID = prove
 (`!G x:A. x IN group_carrier G ==> group_conjugation G (group_id G) x = x`,
  REWRITE_TAC[group_conjugation] THEN GROUP_TAC);;

let GROUP_CONJUGATION_LINV = prove
 (`!G a x:A.
        a IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G (group_inv G a) (group_conjugation G a x) = x`,
  SIMP_TAC[GROUP_CONJUGATION_CONJUGATION; GROUP_INV] THEN
  SIMP_TAC[GROUP_MUL_LINV; GROUP_CONJUGATION_BY_ID]);;

let GROUP_CONJUGATION_RINV = prove
 (`!G a x:A.
        a IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G a (group_conjugation G (group_inv G a) x) = x`,
  SIMP_TAC[GROUP_CONJUGATION_CONJUGATION; GROUP_INV] THEN
  SIMP_TAC[GROUP_MUL_RINV; GROUP_CONJUGATION_BY_ID]);;

let IN_IMAGE_GROUP_CONJUGATION = prove
 (`!G s x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        s SUBSET group_carrier G
        ==> (x IN IMAGE (group_conjugation G y) s <=>
             group_conjugation G (group_inv G y) x IN s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `!u. s SUBSET u /\ x IN u /\
        (!x. x IN u ==> f(g x) = x /\ g(f x) = x)
        ==> (x IN IMAGE f s <=> g x IN s)`) THEN
  EXISTS_TAC `group_carrier G:A->bool` THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION_LINV; GROUP_CONJUGATION_RINV]);;

let IMAGE_GROUP_CONJUGATION_SUBSET = prove
 (`!G (a:A) s.
        a IN group_carrier G /\ s SUBSET group_carrier G
        ==> IMAGE (group_conjugation G a) s SUBSET group_carrier G`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_CONJUGATION]);;

let IMAGE_GROUP_CONJUGATION_BY_ID = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> IMAGE (group_conjugation G (group_id G)) s = s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
  ASM_MESON_TAC[GROUP_CONJUGATION_BY_ID; SUBSET]);;

let IMAGE_GROUP_CONJUGATION_BY_MUL = prove
 (`!G s a b:A.
        a IN group_carrier G /\
        b IN group_carrier G /\
        s SUBSET group_carrier G
        ==> IMAGE (group_conjugation G (group_mul G a b)) s =
            IMAGE (group_conjugation G a) (IMAGE (group_conjugation G b) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  ASM_MESON_TAC[GROUP_CONJUGATION_CONJUGATION; o_THM; SUBSET]);;

let IMAGE_GROUP_CONJUGATION_BY_INV = prove
 (`!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G
        ==> (IMAGE (group_conjugation G (group_inv G a)) s = t <=>
             IMAGE (group_conjugation G a) t = s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> g(f x) = x) /\ (!y. y IN t ==> f(g y) = y)
    ==> (IMAGE f s = t <=> IMAGE g t = s)`) THEN
  ASM_MESON_TAC[SUBSET; GROUP_CONJUGATION_LINV; GROUP_CONJUGATION_RINV]);;

let IMAGE_GROUP_CONJUGATION_EQ_SWAP = prove
 (`!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G /\
        IMAGE (group_conjugation G (group_inv G a)) s = t
        ==> IMAGE (group_conjugation G a) t = s`,
  MESON_TAC[IMAGE_GROUP_CONJUGATION_BY_INV]);;

let IMAGE_GROUP_CONJUGATION_EQ_PREIMAGE = prove
 (`!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G
        ==> (IMAGE (group_conjugation G a) s = t <=>
             {x | x IN group_carrier G /\
                  group_conjugation G a x IN t} = s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `!g. s SUBSET u /\ t SUBSET u /\
        (!x. x IN u ==> f(x) IN u /\ g(f x) = x) /\
        (!y. y IN u ==> g(y) IN u /\ f(g(y)) = y)
       ==> (IMAGE f s = t <=> {x | x IN u /\ f x IN t} = s)`) THEN
  EXISTS_TAC `group_conjugation G (group_inv G (a:A))` THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION; GROUP_INV; GROUP_CONJUGATION_LINV;
               GROUP_CONJUGATION_RINV]);;

(* ------------------------------------------------------------------------- *)
(* Subgroups. We treat them as *sets* which seems to be a common convention. *)
(* And "subgroup_generated" can be used in the degenerate case where the set *)
(* is closed under the operations to cast from "subset" to "group".          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("subgroup_of",(12,"right"));;

let subgroup_of = new_definition
  `(s:A->bool) subgroup_of (G:A group) <=>
        s SUBSET group_carrier G /\
        group_id G IN s /\
        (!x. x IN s ==> group_inv G x IN s) /\
        (!x y. x IN s /\ y IN s ==> group_mul G x y IN s)`;;

let IN_SUBGROUP_ID = prove
 (`!G h:A->bool. h subgroup_of G ==> group_id G IN h`,
  SIMP_TAC[subgroup_of]);;

let IN_SUBGROUP_INV = prove
 (`!G h x:A. h subgroup_of G /\ x IN h ==> group_inv G x IN h`,
  SIMP_TAC[subgroup_of]);;

let IN_SUBGROUP_MUL = prove
 (`!G h x y:A. h subgroup_of G /\ x IN h /\ y IN h ==> group_mul G x y IN h`,
  SIMP_TAC[subgroup_of]);;

let IN_SUBGROUP_DIV = prove
 (`!G h x y:A. h subgroup_of G /\ x IN h /\ y IN h ==> group_div G x y IN h`,
  SIMP_TAC[group_div; IN_SUBGROUP_MUL; IN_SUBGROUP_INV]);;

let IN_SUBGROUP_POW = prove
 (`!G h (x:A) n. h subgroup_of G /\ x IN h ==> group_pow G x n IN h`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; IN_SUBGROUP_ID; IN_SUBGROUP_MUL]);;

let IN_SUBGROUP_ZPOW = prove
 (`!G h (x:A) n. h subgroup_of G /\ x IN h ==> group_zpow G x n IN h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_zpow] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[IN_SUBGROUP_INV; IN_SUBGROUP_POW]);;

let IN_SUBGROUP_CONJUGATION = prove
 (`!G h a x:A.
        h subgroup_of G /\ a IN h /\ x IN h ==> group_conjugation G a x IN h`,
  SIMP_TAC[subgroup_of; group_conjugation]);;

let IN_SUBGROUP_PRODUCT = prove
 (`!G h (<<=) k (f:K->A).
        h subgroup_of G /\
        (!i. i IN k /\ f i IN group_carrier G ==> f i IN h)
        ==> group_product G (<<=) k f IN h`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\x:A. x IN h` GROUP_PRODUCT_CLOSED)) THEN
  ASM_MESON_TAC[subgroup_of]);;

let IN_SUBGROUP_SUM = prove
 (`!G h k (f:K->A).
        h subgroup_of G /\
        (!i. i IN k /\ f i IN group_carrier G ==> f i IN h)
        ==> group_sum G k f IN h`,
  REWRITE_TAC[group_sum; IN_SUBGROUP_PRODUCT]);;

let IMAGE_GROUP_CONJUGATION_SUBGROUP = prove
 (`!G h a:A.
        h subgroup_of G /\ a IN h ==> IMAGE (group_conjugation G a) h = h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `!g. (!x. x IN s ==> f x IN s /\ g x IN s /\ g(f x) = x /\ f(g x) = x)
    ==> IMAGE f s = s`) THEN
  EXISTS_TAC `group_conjugation G (group_inv G a:A)` THEN
  ASM_MESON_TAC[IN_SUBGROUP_CONJUGATION; GROUP_CONJUGATION_LINV;
                GROUP_INV; GROUP_CONJUGATION_RINV; subgroup_of; SUBSET]);;

let SUBGROUP_OF_INTERS = prove
 (`!G (gs:(A->bool)->bool).
        (!g. g IN gs ==> g subgroup_of G) /\ ~(gs = {})
        ==> (INTERS gs) subgroup_of G`,
  REWRITE_TAC[subgroup_of; SUBSET; IN_INTERS] THEN SET_TAC[]);;

let SUBGROUP_OF_INTER = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G ==> (g INTER h) subgroup_of G`,
  REWRITE_TAC[subgroup_of; SUBSET; IN_INTER] THEN SET_TAC[]);;

let SUBGROUP_OF_UNIONS = prove
 (`!G k (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> h subgroup_of G) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> (UNIONS u) subgroup_of G`,
  REWRITE_TAC[subgroup_of] THEN SET_TAC[]);;

let SUBGROUP_OF_OPPOSITE_GROUP = prove
 (`!G h:A->bool. h subgroup_of opposite_group G <=> h subgroup_of G`,
  REWRITE_TAC[subgroup_of; OPPOSITE_GROUP] THEN MESON_TAC[]);;

let SUBGROUP_OF_IMP_SUBSET = prove
 (`!G s:A->bool. s subgroup_of G ==> s SUBSET group_carrier G`,
  SIMP_TAC[subgroup_of]);;

let SUBGROUP_OF_IMP_NONEMPTY = prove
 (`!G s:A->bool. s subgroup_of G ==> ~(s = {})`,
  REWRITE_TAC[subgroup_of] THEN SET_TAC[]);;

let TRIVIAL_SUBGROUP_OF = prove
 (`!G:A group. {group_id G} subgroup_of G`,
  SIMP_TAC[subgroup_of; IN_SING; SING_SUBSET] THEN
  MESON_TAC GROUP_PROPERTIES);;

let CARRIER_SUBGROUP_OF = prove
 (`!G:A group. (group_carrier G) subgroup_of G`,
  REWRITE_TAC[subgroup_of; SUBSET_REFL] THEN MESON_TAC GROUP_PROPERTIES);;

let FINITE_SUBGROUPS = prove
 (`!(G:A group). FINITE(group_carrier G) ==> FINITE {h | h subgroup_of G}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{h:A->bool | h SUBSET group_carrier G}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; subgroup_of] THEN SET_TAC[]);;

let FINITE_RESTRICTED_SUBGROUPS = prove
 (`!P (G:A group).
        FINITE(group_carrier G) ==> FINITE {h | h subgroup_of G /\ P h}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{h:A->bool | h SUBSET group_carrier G}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; subgroup_of] THEN SET_TAC[]);;

let subgroup_generated = new_definition
 `subgroup_generated G (s:A->bool) =
      group(INTERS {h | h subgroup_of G /\ (group_carrier G INTER s) SUBSET h},
            group_id G,group_inv G,group_mul G)`;;

let SUBGROUP_GENERATED = prove
 (`(!G s:A->bool.
        group_carrier (subgroup_generated G s) =
          INTERS {h | h subgroup_of G /\ (group_carrier G INTER s) SUBSET h}) /\
    (!G s:A->bool. group_id (subgroup_generated G s) = group_id G) /\
    (!G s:A->bool. group_inv (subgroup_generated G s) = group_inv G) /\
    (!G s:A->bool. group_mul (subgroup_generated G s) = group_mul G)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl subgroup_generated)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM subgroup_generated] THEN ANTS_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    REPLICATE_TAC 2 (GEN_REWRITE_TAC I [CONJ_ASSOC]) THEN CONJ_TAC THENL
     [MESON_TAC[subgroup_of]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `group_carrier G:A->bool`)) THEN
    REWRITE_TAC[INTER_SUBSET; SUBSET_REFL; CARRIER_SUBGROUP_OF] THEN
    MESON_TAC GROUP_PROPERTIES;
    DISCH_TAC THEN
    ASM_REWRITE_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let SUBGROUP_GENERATED_EQ = prove
 (`!G s:A->bool.
        subgroup_generated G s = G <=>
        group_carrier(subgroup_generated G s) = group_carrier G`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GROUPS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED]);;

let GROUP_ID_SUBGROUP = prove
 (`!G s:A->bool. group_id G IN group_carrier(subgroup_generated G s)`,
  MESON_TAC[GROUP_ID; SUBGROUP_GENERATED]);;

let ABELIAN_SUBGROUP_GENERATED = prove
 (`!G h:A->bool.
        abelian_group G ==> abelian_group(subgroup_generated G h)`,
  SIMP_TAC[abelian_group; SUBGROUP_GENERATED] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `group_carrier(G:A group)`)) THEN
  ASM_REWRITE_TAC[CARRIER_SUBGROUP_OF; INTER_SUBSET] THEN
  ASM_MESON_TAC[]);;

let GROUP_DIV_SUBGROUP_GENERATED = prove
 (`!G s:A->bool. group_div (subgroup_generated G s) = group_div G`,
  REWRITE_TAC[FUN_EQ_THM; group_div; SUBGROUP_GENERATED]);;

let GROUP_POW_SUBGROUP_GENERATED = prove
 (`!G s:A->bool. group_pow (subgroup_generated G s) = group_pow G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[group_pow; SUBGROUP_GENERATED]);;

let GROUP_ZPOW_SUBGROUP_GENERATED = prove
 (`!G s:A->bool. group_zpow (subgroup_generated G s) = group_zpow G`,
  REWRITE_TAC[group_zpow; GROUP_POW_SUBGROUP_GENERATED;
              SUBGROUP_GENERATED; FUN_EQ_THM]);;

let GROUP_CONJUGATION_SUBGROUP_GENERATED = prove
 (`!G s:A->bool.
    group_conjugation (subgroup_generated G s) = group_conjugation G`,
  REWRITE_TAC[group_conjugation; SUBGROUP_GENERATED; FUN_EQ_THM]);;

let SUBGROUP_GENERATED_RESTRICT = prove
 (`!G s:A->bool.
        subgroup_generated G s =
        subgroup_generated G (group_carrier G INTER s)`,
  REWRITE_TAC[subgroup_generated; SET_RULE `g INTER g INTER s = g INTER s`]);;

let SUBGROUP_SUBGROUP_GENERATED = prove
 (`!G s:A->bool. group_carrier(subgroup_generated G s) subgroup_of G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC SUBGROUP_OF_INTERS THEN
  SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `group_carrier G:A->bool` THEN
  REWRITE_TAC[CARRIER_SUBGROUP_OF; INTER_SUBSET]);;

let SUBGROUP_GENERATED_MONO = prove
 (`!G s t:A->bool.
        s SUBSET t
        ==> group_carrier(subgroup_generated G s) SUBSET
            group_carrier(subgroup_generated G t)`,
  REWRITE_TAC[SUBGROUP_GENERATED] THEN SET_TAC[]);;

let SUBGROUP_GENERATED_MINIMAL = prove
 (`!G h s:A->bool.
        s SUBSET h /\ h subgroup_of G
        ==> group_carrier(subgroup_generated G s) SUBSET h`,
  REWRITE_TAC[SUBGROUP_GENERATED; INTERS_GSPEC] THEN SET_TAC[]);;

let SUBGROUP_GENERATED_INDUCT = prove
 (`!G P s:A->bool.
        (!x. x IN group_carrier G /\ x IN s ==> P x) /\
        P(group_id G) /\
        (!x. P x ==> P(group_inv G x)) /\
        (!x y. P x /\ P y ==> P(group_mul G x y))
        ==> !x. x IN group_carrier(subgroup_generated G s) ==> P x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_INTER] THEN
  ONCE_REWRITE_TAC[SUBGROUP_GENERATED_RESTRICT] THEN MP_TAC(SET_RULE
    `group_carrier G INTER (s:A->bool) SUBSET group_carrier G`) THEN
  SPEC_TAC(`group_carrier G INTER (s:A->bool)`,`s:A->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `{x:A | x IN group_carrier G /\ P x}`;
                 `s:A->bool`] SUBGROUP_GENERATED_MINIMAL) THEN
  ANTS_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[subgroup_of; IN_ELIM_THM; SUBSET; GROUP_MUL; GROUP_INV;
               GROUP_ID]);;

let GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET = prove
 (`!G h:A->bool.
        group_carrier (subgroup_generated G h) SUBSET group_carrier G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC(SET_RULE `a IN s ==> INTERS s SUBSET a`) THEN
  REWRITE_TAC[IN_ELIM_THM; CARRIER_SUBGROUP_OF; INTER_SUBSET]);;

let SUBGROUP_GENERATED_SUPERSET = prove
 (`!G s:A->bool.
    subgroup_generated G s = G <=>
    group_carrier G SUBSET group_carrier(subgroup_generated G s)`,
  REWRITE_TAC[SUBGROUP_GENERATED_EQ; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]);;

let SUBGROUP_OF_SUBGROUP_GENERATED_EQ = prove
 (`!G h k:A->bool.
        h subgroup_of (subgroup_generated G k) <=>
        h subgroup_of G /\ h SUBSET group_carrier(subgroup_generated G k)`,
  REWRITE_TAC[subgroup_of; CONJUNCT2 SUBGROUP_GENERATED] THEN
  MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET_TRANS]);;

let FINITE_SUBGROUP_GENERATED = prove
 (`!G s:A->bool.
        FINITE(group_carrier G)
        ==> FINITE(group_carrier(subgroup_generated G s))`,
  MESON_TAC[FINITE_SUBSET; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]);;

let SUBGROUP_GENERATED_SUBSET_CARRIER = prove
 (`!G h:A->bool.
     group_carrier G INTER h SUBSET group_carrier(subgroup_generated G h)`,
  REWRITE_TAC[subgroup_of; SUBGROUP_GENERATED; SUBSET_INTERS] THEN SET_TAC[]);;

let SUBGROUP_GENERATED_MINIMAL_EQ = prove
 (`!G h s:A->bool.
        h subgroup_of G
        ==> (group_carrier (subgroup_generated G s) SUBSET h <=>
             group_carrier G INTER s SUBSET h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBGROUP_GENERATED_SUBSET_CARRIER];
    ONCE_REWRITE_TAC[SUBGROUP_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC[SUBGROUP_GENERATED_MINIMAL]]);;

let CARRIER_SUBGROUP_GENERATED_SUBGROUP = prove
 (`!G h:A->bool.
        h subgroup_of G ==> group_carrier (subgroup_generated G h) = h`,
  REWRITE_TAC[subgroup_of; SUBGROUP_GENERATED; INTERS_GSPEC] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[SET_RULE `h SUBSET g ==> g INTER h = h`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [GEN_REWRITE_TAC I [SUBSET]; ASM SET_TAC[]] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `h:A->bool`) THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ = prove
 (`!G h k:A->bool.
        k subgroup_of G
        ==> (h subgroup_of (subgroup_generated G k) <=>
             h subgroup_of G /\ h SUBSET k)`,
  REWRITE_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_EQ] THEN
  SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP]);;

let SUBGROUP_GENERATED_GROUP_CARRIER = prove
 (`!G:A group. subgroup_generated G (group_carrier G) = G`,
  GEN_TAC THEN REWRITE_TAC[GROUPS_EQ] THEN
  SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; CARRIER_SUBGROUP_OF] THEN
  REWRITE_TAC[SUBGROUP_GENERATED]);;

let SUBGROUP_OF_SUBGROUP_GENERATED = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ g SUBSET h
        ==> g subgroup_of (subgroup_generated G h)`,
  SIMP_TAC[subgroup_of; SUBGROUP_GENERATED; SUBSET_INTERS] THEN SET_TAC[]);;

let SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> s SUBSET group_carrier(subgroup_generated G s)`,
  MESON_TAC[SUBGROUP_GENERATED_SUBSET_CARRIER;
            SET_RULE `s SUBSET t <=> t INTER s = s`]);;

let SUBGROUP_GENERATED_REFL = prove
 (`!G s:A->bool. group_carrier G SUBSET s ==> subgroup_generated G s = G`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SUBGROUP_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET s ==> u INTER s = u`] THEN
  REWRITE_TAC[SUBGROUP_GENERATED_GROUP_CARRIER]);;

let SUBGROUP_GENERATED_INC = prove
 (`!G s x:A.
        s SUBSET group_carrier G /\ x IN s
        ==> x IN group_carrier(subgroup_generated G s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
  REWRITE_TAC[SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET]);;

let SUBGROUP_GENERATED_INC_GEN = prove
 (`!G s x:A.
        x IN group_carrier G /\ x IN s
        ==> x IN group_carrier(subgroup_generated G s)`,
  MESON_TAC[SUBGROUP_GENERATED_SUBSET_CARRIER; IN_INTER; SUBSET]);;

let SUBGROUP_OF_SUBGROUP_GENERATED_REV = prove
 (`!G g h:A->bool.
        g subgroup_of (subgroup_generated G h)
        ==> g subgroup_of G`,
  SIMP_TAC[subgroup_of; CONJUNCT2 SUBGROUP_GENERATED] THEN
  MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET_TRANS]);;

let TRIVIAL_GROUP_SUBGROUP_GENERATED = prove
 (`!G s:A->bool.
        trivial_group G ==> trivial_group(subgroup_generated G s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TRIVIAL_GROUP_ALT] THEN
  MESON_TAC[SUBSET_TRANS; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]);;

let TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL = prove
 (`!G s:A->bool.
        s SUBSET {group_id G} ==> trivial_group(subgroup_generated G s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TRIVIAL_GROUP_ALT; SUBGROUP_GENERATED] THEN
  EXISTS_TAC `group_id G:A` THEN
  MATCH_MP_TAC INTERS_SUBSET_STRONG THEN
  EXISTS_TAC `{group_id G:A}` THEN
  REWRITE_TAC[IN_ELIM_THM; TRIVIAL_SUBGROUP_OF] THEN ASM SET_TAC[]);;

let TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ = prove
 (`!G s:A->bool.
        trivial_group(subgroup_generated G s) <=>
        group_carrier G INTER s SUBSET {group_id G}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SUBGROUP_GENERATED_RESTRICT] THEN
  EQ_TAC THEN REWRITE_TAC[TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL] THEN
  REWRITE_TAC[TRIVIAL_GROUP_SUBSET] THEN
  REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
  REWRITE_TAC[GSYM SUBGROUP_GENERATED_RESTRICT] THEN
  REWRITE_TAC[SUBGROUP_GENERATED_SUBSET_CARRIER]);;

let TRIVIAL_GROUP_GENERATED_BY_ANYTHING = prove
 (`!G s:A->bool. trivial_group G ==> subgroup_generated G s = G`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:A->bool` o
    MATCH_MP TRIVIAL_GROUP_SUBGROUP_GENERATED) THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC[trivial_group; CONJUNCT2 SUBGROUP_GENERATED]);;

let SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED = prove
 (`!G s:A->bool.
        subgroup_generated G (group_carrier(subgroup_generated G s)) =
        subgroup_generated G s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED; SUBSET_REFL];
    MATCH_MP_TAC SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET THEN
    REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]]);;

let SUBGROUP_GENERATED_INSERT_ID = prove
 (`!G s:A->bool.
        subgroup_generated G (group_id G INSERT s) = subgroup_generated G s`,
  REWRITE_TAC[GROUPS_EQ; SUBGROUP_GENERATED] THEN
  REWRITE_TAC[EXTENSION; INTERS_GSPEC; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; TAUT
   `p /\ (q \/ r) ==> s <=> (q ==> p ==> s) /\ (p /\ r ==> s)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2; GROUP_ID] THEN
  MESON_TAC[subgroup_of]);;

let GROUP_CARRIER_SUBGROUP_GENERATED_MONO = prove
 (`!G s t:A->bool.
        group_carrier(subgroup_generated (subgroup_generated G s) t) SUBSET
        group_carrier(subgroup_generated G t)`,
  ONCE_REWRITE_TAC[SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_EQ] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTERS_ANTIMONO_GEN THEN
  X_GEN_TAC `h:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `h INTER group_carrier (subgroup_generated G s):A->bool` THEN
  REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
  ASM_SIMP_TAC[SUBGROUP_OF_INTER; SUBGROUP_SUBGROUP_GENERATED] THEN
  MP_TAC(ISPECL [`G:A group`; `s:A->bool`]
    GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  ASM SET_TAC[]);;

let SUBGROUP_GENERATED_IDEMPOT = prove
 (`!G s:A->bool.
        s SUBSET t
        ==> subgroup_generated (subgroup_generated G t) s =
            subgroup_generated G s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_MONO] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [SUBGROUP_GENERATED_RESTRICT] THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH rand SUBGROUP_GENERATED_SUBSET_CARRIER o
      rand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
    MP_TAC(ISPECL [`G:A group`; `t:A->bool`]
        SUBGROUP_GENERATED_SUBSET_CARRIER) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SUBGROUP_OF_SUBGROUP_GENERATED_REV THEN
    EXISTS_TAC `t:A->bool` THEN REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED]]);;

let TRIVIAL_GROUP_SUBGROUP_GENERATED_EMPTY = prove
 (`!G:A group. trivial_group(subgroup_generated G {})`,
  REWRITE_TAC[TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ] THEN SET_TAC[]);;

let SUBGROUP_OF_COMMUTING_ELEMENTS = prove
 (`!G z:A.
        z IN group_carrier G
        ==> {x | x IN group_carrier G /\ group_mul G x z = group_mul G z x}
            subgroup_of G`,
  REWRITE_TAC[subgroup_of; SUBSET_RESTRICT; IN_ELIM_THM] THEN
  SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID; GROUP_COMMUTES_MUL;
           GROUP_COMMUTES_INV; GROUP_MUL; GROUP_INV; GROUP_ID]);;

let GROUP_COMMUTES_SUBGROUP_GENERATED_EQ = prove
 (`!G s z:A.
        z IN group_carrier G
        ==> ((!x. x IN group_carrier(subgroup_generated G s)
                  ==> group_mul G x z = group_mul G z x) <=>
             (!x. x IN group_carrier G /\ x IN s
                  ==> group_mul G x z = group_mul G z x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUBGROUP_OF_COMMUTING_ELEMENTS) THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool` o
    MATCH_MP SUBGROUP_GENERATED_MINIMAL_EQ) THEN
  REWRITE_TAC[IN_GSPEC; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SET_RULE
   `s SUBSET {x | P x /\ Q x} <=>
    s SUBSET {x | P x} /\ s SUBSET {x | Q x}`] THEN
  SET_TAC[]);;

let GROUP_COMMUTES_SUBGROUP_GENERATED = prove
 (`!G s z:A.
        (!x. x IN s ==> group_mul G x z = group_mul G z x) /\
        z IN group_carrier G
        ==> (!x. x IN group_carrier(subgroup_generated G s)
                 ==> group_mul G x z = group_mul G z x)`,
  MESON_TAC[GROUP_COMMUTES_SUBGROUP_GENERATED_EQ]);;

let GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ = prove
 (`!G s t:A->bool.
        (!x y. x IN group_carrier(subgroup_generated G s) /\
               y IN group_carrier(subgroup_generated G t)
               ==> group_mul G x y = group_mul G y x) <=>
        (!x y. x IN group_carrier G /\ x IN s /\
               y IN group_carrier G /\ y IN t
               ==> group_mul G x y = group_mul G y x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM;
   TAUT `p /\ q /\ r /\ s ==> t <=> p /\ q ==> r /\ s ==> t`] THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  SIMP_TAC[GSYM GROUP_COMMUTES_SUBGROUP_GENERATED_EQ] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  MP_TAC(ISPECL [`G:A group`; `t:A->bool`]
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  SIMP_TAC[GROUP_COMMUTES_SUBGROUP_GENERATED_EQ; SUBSET]);;

let ABELIAN_GROUP_SUBGROUP_GENERATED_GEN = prove
 (`!G s:A->bool.
        (!x y. x IN group_carrier G /\ x IN s /\
               y IN group_carrier G /\ y IN s
               ==> group_mul G x y = group_mul G y x)
        ==> abelian_group (subgroup_generated G s)`,
  REWRITE_TAC[abelian_group; CONJUNCT2 SUBGROUP_GENERATED] THEN
  REWRITE_TAC[GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Direct products and sums.                                                 *)
(* ------------------------------------------------------------------------- *)

let prod_group = new_definition
 `prod_group (G:A group) (G':B group) =
        group((group_carrier G) CROSS (group_carrier G'),
              (group_id G,group_id G'),
              (\(x,x'). group_inv G x,group_inv G' x'),
              (\(x,x') (y,y'). group_mul G x y,group_mul G' x' y'))`;;

let PROD_GROUP = prove
 (`(!(G:A group) (G':B group).
        group_carrier (prod_group G G') =
        (group_carrier G) CROSS (group_carrier G')) /\
   (!(G:A group) (G':B group).
        group_id (prod_group G G') = (group_id G,group_id G')) /\
   (!(G:A group) (G':B group).
        group_inv (prod_group G G') =
          \(x,x'). group_inv G x,group_inv G' x') /\
   (!(G:A group) (G':B group).
        group_mul (prod_group G G') =
          \(x,x') (y,y'). group_mul G x y,group_mul G' x' y')`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl prod_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM prod_group] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    SIMP_TAC GROUP_PROPERTIES;
    DISCH_TAC THEN
    ASM_REWRITE_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let GROUP_POW_PROD_GROUP = prove
 (`!(G:A group) (H:B group) x y n.
        x IN group_carrier G /\ y IN group_carrier H
        ==> group_pow (prod_group G H) (x,y) n =
            (group_pow G x n,group_pow H y n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[group_pow; PROD_GROUP]);;

let GROUP_ZPOW_PROD_GROUP = prove
 (`!(G:A group) (H:B group) x y n.
        x IN group_carrier G /\ y IN group_carrier H
        ==> group_zpow (prod_group G H) (x,y) n =
            (group_zpow G x n,group_zpow H y n)`,
  REWRITE_TAC[FORALL_INT_CASES; GROUP_ZPOW_POW] THEN
  SIMP_TAC[GROUP_POW_PROD_GROUP; PROD_GROUP]);;

let OPPOSITE_PROD_GROUP = prove
 (`!(G1:A group) (G2:B group).
        opposite_group(prod_group G1 G2) =
        prod_group (opposite_group G1) (opposite_group G2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GROUPS_EQ; OPPOSITE_GROUP; PROD_GROUP] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM]);;

let TRIVIAL_PROD_GROUP = prove
 (`!(G:A group) (H:B group).
        trivial_group(prod_group G H) <=>
        trivial_group G /\ trivial_group H`,
  REWRITE_TAC[TRIVIAL_GROUP_SUBSET; PROD_GROUP; GSYM CROSS_SING] THEN
  REWRITE_TAC[SUBSET_CROSS; GROUP_CARRIER_NONEMPTY]);;

let FINITE_PROD_GROUP = prove
 (`!(G:A group) (H:B group).
        FINITE(group_carrier(prod_group G H)) <=>
        FINITE(group_carrier G) /\ FINITE(group_carrier H)`,
  REWRITE_TAC[PROD_GROUP; FINITE_CROSS_EQ; GROUP_CARRIER_NONEMPTY]);;

let ABELIAN_PROD_GROUP = prove
 (`!(G:A group) (H:B group).
        abelian_group(prod_group G H) <=>
        abelian_group G /\ abelian_group H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abelian_group; PROD_GROUP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
  MAP_EVERY (MP_TAC o C ISPEC GROUP_CARRIER_NONEMPTY)
   [`G:A group`; `H:B group`] THEN SET_TAC[]);;

let CROSS_SUBGROUP_OF_PROD_GROUP = prove
 (`!(G1:A group) (G2:B group) h1 h2.
        (h1 CROSS h2) subgroup_of (prod_group G1 G2) <=>
        h1 subgroup_of G1 /\ h2 subgroup_of G2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subgroup_of; FORALL_PAIR_THM; PROD_GROUP; IN_CROSS] THEN
  REWRITE_TAC[SUBSET_CROSS] THEN SET_TAC[]);;

let PROD_GROUP_SUBGROUP_GENERATED = prove
 (`!(G1:A group) (G2:B group) h1 h2.
        h1 subgroup_of G1 /\ h2 subgroup_of G2
        ==> (prod_group (subgroup_generated G1 h1) (subgroup_generated G2 h2) =
             subgroup_generated (prod_group G1 G2) (h1 CROSS h2))`,
  SIMP_TAC[GROUPS_EQ; CONJUNCT2 PROD_GROUP; CONJUNCT2 SUBGROUP_GENERATED] THEN
  SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP;
           CROSS_SUBGROUP_OF_PROD_GROUP; PROD_GROUP]);;

let product_group = new_definition
 `product_group k (G:K->A group) =
        group(cartesian_product k (\i. group_carrier(G i)),
              RESTRICTION k (\i. group_id (G i)),
              (\x. RESTRICTION k (\i. group_inv (G i) (x i))),
              (\x y. RESTRICTION k (\i. group_mul (G i) (x i) (y i))))`;;

let PRODUCT_GROUP = prove
 (`(!k (G:K->A group).
        group_carrier(product_group k G) =
          cartesian_product k (\i. group_carrier(G i))) /\
   (!k (G:K->A group).
        group_id (product_group k G) =
          RESTRICTION k (\i. group_id (G i))) /\
   (!k (G:K->A group).
        group_inv (product_group k G) =
          \x. RESTRICTION k (\i. group_inv (G i) (x i))) /\
   (!k (G:K->A group).
        group_mul (product_group k G) =
          (\x y. RESTRICTION k (\i. group_mul (G i) (x i) (y i))))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl product_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM product_group] THEN ANTS_TAC THENL
   [REWRITE_TAC[cartesian_product; RESTRICTION; EXTENSIONAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_SIMP_TAC GROUP_PROPERTIES;
    DISCH_TAC THEN
    ASM_REWRITE_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let OPPOSITE_PRODUCT_GROUP = prove
 (`!(G:K->A group) k.
        opposite_group(product_group k G) =
        product_group k (\i. opposite_group(G i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GROUPS_EQ; OPPOSITE_GROUP; PRODUCT_GROUP]);;

let TRIVIAL_PRODUCT_GROUP = prove
 (`!k (G:K->A group).
        trivial_group(product_group k G) <=>
        !i. i IN k ==> trivial_group(G i)`,
  REWRITE_TAC[TRIVIAL_GROUP_SUBSET; PRODUCT_GROUP] THEN
  REWRITE_TAC[GSYM CARTESIAN_PRODUCT_SINGS_GEN] THEN
  REWRITE_TAC[SUBSET_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ_EMPTY; GROUP_CARRIER_NONEMPTY]);;

let CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP = prove
 (`!k h G:K->A group.
        (cartesian_product k h) subgroup_of (product_group k G) <=>
        !i. i IN k ==> (h i) subgroup_of (G i)`,
  REWRITE_TAC[subgroup_of; PRODUCT_GROUP; RESTRICTION_IN_CARTESIAN_PRODUCT;
              SUBSET_CARTESIAN_PRODUCT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_CASES_TAC `cartesian_product k (h:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
          FORALL_CARTESIAN_PRODUCT_ELEMENTS] THEN
    MESON_TAC[]]);;

let PRODUCT_GROUP_SUBGROUP_GENERATED = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of (G i))
        ==> product_group k (\i. subgroup_generated (G i) (h i)) =
            subgroup_generated (product_group k G) (cartesian_product k h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUPS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 PRODUCT_GROUP; CONJUNCT2 SUBGROUP_GENERATED] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; PRODUCT_GROUP;
               CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP]);;

let FINITE_PRODUCT_GROUP = prove
 (`!k (G:K->A group).
        FINITE(group_carrier(product_group k G)) <=>
        FINITE {i | i IN k /\ ~trivial_group(G i)} /\
        !i. i IN k ==> FINITE(group_carrier(G i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PRODUCT_GROUP] THEN
  REWRITE_TAC[FINITE_CARTESIAN_PRODUCT; CARTESIAN_PRODUCT_EQ_EMPTY] THEN
  REWRITE_TAC[TRIVIAL_GROUP_ALT; GROUP_CARRIER_NONEMPTY]);;

let ABELIAN_PRODUCT_GROUP = prove
 (`!k (G:K->A group).
        abelian_group(product_group k G) <=>
        !i. i IN k ==> abelian_group(G i)`,
  REWRITE_TAC[abelian_group; PRODUCT_GROUP; RESTRICTION_EXTENSION] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ; CARTESIAN_PRODUCT_EQ_EMPTY;
           GROUP_CARRIER_NONEMPTY] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o RAND_CONV o ONCE_DEPTH_CONV)
   [RIGHT_IMP_FORALL_THM] THEN
  SIMP_TAC[IMP_IMP; FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ;
           CARTESIAN_PRODUCT_EQ_EMPTY; GROUP_CARRIER_NONEMPTY] THEN
  MESON_TAC[]);;

let sum_group = new_definition
  `sum_group k (G:K->A group) =
        subgroup_generated
         (product_group k G)
         {x | x IN cartesian_product k (\i. group_carrier(G i)) /\
              FINITE {i | i IN k /\ ~(x i = group_id(G i))}}`;;

let SUM_GROUP_EQ_PRODUCT_GROUP = prove
 (`!k (G:K->A group). FINITE k ==> sum_group k G = product_group k G`,
  SIMP_TAC[sum_group; FINITE_RESTRICT] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 PRODUCT_GROUP); IN_GSPEC] THEN
  REWRITE_TAC[SUBGROUP_GENERATED_GROUP_CARRIER]);;

let SUBGROUP_SUM_GROUP = prove
 (`!k (G:K->A group).
    {x | x IN cartesian_product k (\i. group_carrier(G i)) /\
         FINITE {i | i IN k /\ ~(x i = group_id(G i))}}
    subgroup_of product_group k G`,
  REWRITE_TAC[subgroup_of; PRODUCT_GROUP; SUBSET_RESTRICT] THEN
  REWRITE_TAC[RESTRICTION; cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
  SIMP_TAC[GROUP_ID; GROUP_INV_EQ_ID; GROUP_INV; GROUP_MUL] THEN
  REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IMP_IMP; GSYM FINITE_UNION] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[NOT_IMP; SUBSET; IN_ELIM_THM; IN_UNION] THEN
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[TAUT `~p \/ q <=> p ==> q`] THEN
  ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_ID]);;

let SUM_GROUP_CLAUSES = prove
 (`(!k (G:K->A group).
        group_carrier(sum_group k G) =
          {x | x IN cartesian_product k (\i. group_carrier(G i)) /\
               FINITE {i | i IN k /\ ~(x i = group_id(G i))}}) /\
   (!k (G:K->A group).
        group_id (sum_group k G) =
          RESTRICTION k (\i. group_id (G i))) /\
   (!k (G:K->A group).
        group_inv (sum_group k G) =
          \x. RESTRICTION k (\i. group_inv (G i) (x i))) /\
   (!k (G:K->A group).
        group_mul (sum_group k G) =
          (\x y. RESTRICTION k (\i. group_mul (G i) (x i) (y i))))`,
  SIMP_TAC[sum_group; SUBGROUP_SUM_GROUP;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[SUBGROUP_GENERATED; PRODUCT_GROUP]);;

let TRIVIAL_SUM_GROUP = prove
 (`!k (G:K->A group).
        trivial_group(sum_group k G) <=> !i. i IN k ==> trivial_group(G i)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[TRIVIAL_GROUP_SUBSET] THEN X_GEN_TAC `i:K` THEN
    REWRITE_TAC[SET_RULE `~(s SUBSET {a}) <=> ?x. x IN s /\ ~(x = a)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC
     `RESTRICTION k (\j. if j = i then a else group_id (G j)):K->A` THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; RESTRICTION_IN_CARTESIAN_PRODUCT;
                IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[GROUP_ID];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:K}` THEN
      REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING; RESTRICTION] THEN
      MESON_TAC[];
      DISCH_THEN(MP_TAC o C AP_THM `i:K`) THEN
      ASM_REWRITE_TAC[RESTRICTION]];
    DISCH_TAC THEN REWRITE_TAC[sum_group] THEN
    MATCH_MP_TAC TRIVIAL_GROUP_SUBGROUP_GENERATED THEN
    ASM_REWRITE_TAC[TRIVIAL_PRODUCT_GROUP]]);;

let CARTESIAN_PRODUCT_SUBGROUP_OF_SUM_GROUP = prove
 (`!k h G:K->A group.
        (cartesian_product k h) subgroup_of (sum_group k G) <=>
        (!i. i IN k ==> (h i) subgroup_of (G i)) /\
        (!z. z IN cartesian_product k h
             ==> FINITE {i | i IN k /\ ~(z i = group_id(G i))})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sum_group; SUBGROUP_OF_SUBGROUP_GENERATED_EQ] THEN
  REWRITE_TAC[GSYM sum_group; SUM_GROUP_CLAUSES] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET t
    ==> ((!x. x IN s ==> x IN t /\ P x) <=> (!x. x IN s ==> P x))`) THEN
  REWRITE_TAC[SUBSET_CARTESIAN_PRODUCT] THEN
  ASM_MESON_TAC[subgroup_of]);;

let SUM_GROUP_SUBGROUP_GENERATED = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of (G i))
        ==> sum_group k (\i. subgroup_generated (G i) (h i)) =
            subgroup_generated (sum_group k G) (cartesian_product k h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUPS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUM_GROUP_CLAUSES; CONJUNCT2 SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SUM_GROUP_CLAUSES; CONJUNCT2 SUBGROUP_GENERATED] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [SUBGROUP_GENERATED_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARRIER_SUBGROUP_GENERATED_SUBGROUP o
    rand o snd) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [sum_group] THEN
    REWRITE_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_EQ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBGROUP_OF_INTER THEN
      ASM_SIMP_TAC[CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP] THEN
      REWRITE_TAC[SUM_GROUP_CLAUSES; SUBGROUP_SUM_GROUP];
      SIMP_TAC[SUBGROUP_SUM_GROUP; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
      REWRITE_TAC[SUM_GROUP_CLAUSES] THEN SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[SUM_GROUP_CLAUSES; IN_INTER; IN_ELIM_THM; cartesian_product] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms etc.                                                        *)
(* ------------------------------------------------------------------------- *)

let group_homomorphism = new_definition
 `group_homomorphism (G,G') (f:A->B) <=>
        IMAGE f (group_carrier G) SUBSET group_carrier G' /\
        f (group_id G) = group_id G' /\
        (!x. x IN group_carrier G
             ==> f(group_inv G x) = group_inv G' (f x)) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> f(group_mul G x y) = group_mul G' (f x) (f y))`;;

let group_monomorphism = new_definition
 `group_monomorphism (G,G') (f:A->B) <=>
        group_homomorphism (G,G') f /\
        !x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
             ==> x = y`;;

let group_epimorphism = new_definition
 `group_epimorphism (G,G') (f:A->B) <=>
        group_homomorphism (G,G') f /\
        IMAGE f (group_carrier G) = group_carrier G'`;;

let group_endomorphism = new_definition
 `group_endomorphism G (f:A->A) <=> group_homomorphism (G,G) f`;;

let group_isomorphisms = new_definition
 `group_isomorphisms (G,G') ((f:A->B),g) <=>
        group_homomorphism (G,G') f /\
        group_homomorphism (G',G) g /\
        (!x. x IN group_carrier G ==> g(f x) = x) /\
        (!y. y IN group_carrier G' ==> f(g y) = y)`;;

let group_isomorphism = new_definition
 `group_isomorphism (G,G') (f:A->B) <=> ?g. group_isomorphisms (G,G') (f,g)`;;

let group_automorphism = new_definition
 `group_automorphism G (f:A->A) <=> group_isomorphism (G,G) f`;;

let GROUP_HOMOMORPHISM_EQ = prove
 (`!G H (f:A->B) f'.
        group_homomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_homomorphism (G,H) f'`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[GROUP_ID; GROUP_INV; GROUP_MUL]);;

let GROUP_MONOMORPHISM_EQ = prove
 (`!G H (f:A->B) f'.
        group_monomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_monomorphism (G,H) f'`,
  REWRITE_TAC[group_monomorphism; group_homomorphism; SUBSET] THEN
  SIMP_TAC[FORALL_IN_IMAGE; GROUP_ID; GROUP_INV; GROUP_MUL] THEN
  MESON_TAC[]);;

let GROUP_EPIMORPHISM_EQ = prove
 (`!G H (f:A->B) f'.
        group_epimorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_epimorphism (G,H) f'`,
  REWRITE_TAC[group_epimorphism; group_homomorphism; SUBSET] THEN
  SIMP_TAC[FORALL_IN_IMAGE; GROUP_ID; GROUP_INV; GROUP_MUL] THEN
  SET_TAC[]);;

let GROUP_ENDOMORPHISM_EQ = prove
 (`!G (f:A->A) f'.
        group_endomorphism G f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_endomorphism G f'`,
  REWRITE_TAC[group_endomorphism; GROUP_HOMOMORPHISM_EQ]);;

let GROUP_ISOMORPHISMS_EQ = prove
 (`!G H (f:A->B) g.
        group_isomorphisms(G,H) (f,g) /\
        (!x. x IN group_carrier G ==> f' x = f x) /\
        (!y. y IN group_carrier H ==> g' y = g y)
        ==> group_isomorphisms(G,H) (f',g')`,
  SIMP_TAC[group_isomorphisms; group_homomorphism; SUBSET] THEN
  SIMP_TAC[FORALL_IN_IMAGE; GROUP_ID; GROUP_INV; GROUP_MUL] THEN
  SET_TAC[]);;

let GROUP_ISOMORPHISM_EQ = prove
 (`!G H (f:A->B) f'.
        group_isomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_isomorphism (G,H) f'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[group_isomorphism] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[GROUP_ISOMORPHISMS_EQ]);;

let GROUP_AUTOMORPHISM_EQ = prove
 (`!G (f:A->A) f'.
        group_automorphism G f /\
        (!x. x IN group_carrier G ==> f' x = f x)
        ==> group_automorphism G f'`,
  REWRITE_TAC[group_automorphism; GROUP_ISOMORPHISM_EQ]);;

let GROUP_ISOMORPHISMS_SYM = prove
 (`!G G' (f:A->B) g.
        group_isomorphisms (G,G') (f,g) <=> group_isomorphisms(G',G) (g,f)`,
  REWRITE_TAC[group_isomorphisms] THEN MESON_TAC[]);;

let GROUP_ISOMORPHISMS_IMP_ISOMORPHISM = prove
 (`!(f:A->B) g G G'.
        group_isomorphisms (G,G') (f,g) ==> group_isomorphism (G,G') f`,
  REWRITE_TAC[group_isomorphism] THEN MESON_TAC[]);;

let GROUP_ISOMORPHISMS_IMP_ISOMORPHISM_ALT = prove
 (`!(f:A->B) g G G'.
        group_isomorphisms (G,G') (f,g) ==> group_isomorphism (G',G) g`,
  MESON_TAC[GROUP_ISOMORPHISMS_SYM; GROUP_ISOMORPHISMS_IMP_ISOMORPHISM]);;

let GROUP_HOMOMORPHISM = prove
 (`!G G' f:A->B.
        group_homomorphism (G,G') (f:A->B) <=>
        IMAGE f (group_carrier G) SUBSET group_carrier G' /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> f(group_mul G x y) = group_mul G' (f x) (f y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_homomorphism] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`group_id G:A`; `group_id G:A`]) THEN
    SIMP_TAC[GROUP_ID; GROUP_MUL_LID] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    ASM_MESON_TAC[GROUP_LID_UNIQUE; GROUP_ID];
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC GROUP_LINV_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `group_inv G x:A`]) THEN
    ASM_SIMP_TAC[GROUP_INV; GROUP_MUL_RINV]]);;

let GROUP_ISOMORPHISMS = prove
 (`!G H (f:A->B) g.
        group_isomorphisms(G,H) (f,g) <=>
        group_homomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> g(f x) = x) /\
        (!y. y IN group_carrier H ==> g y IN group_carrier G /\ f(g y) = y)`,
  REWRITE_TAC[group_isomorphisms; group_homomorphism] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[GROUP_ID; GROUP_INV; GROUP_MUL]);;

let GROUP_HOMOMORPHISM_OF_ID = prove
 (`!(f:A->B) G G'.
        group_homomorphism(G,G') f ==> f (group_id G) = group_id G'`,
  SIMP_TAC[group_homomorphism]);;

let GROUP_HOMOMORPHISM_INV = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x. x IN group_carrier G
                ==> f(group_inv G x) = group_inv G' (f x)`,
  SIMP_TAC[group_homomorphism]);;

let GROUP_HOMOMORPHISM_MUL = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x y. x IN group_carrier G /\ y IN group_carrier G
                  ==> f(group_mul G x y) = group_mul G' (f x) (f y)`,
  SIMP_TAC[group_homomorphism]);;

let GROUP_HOMOMORPHISM_DIV = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x y. x IN group_carrier G /\ y IN group_carrier G
                  ==> f(group_div G x y) = group_div G' (f x) (f y)`,
  REWRITE_TAC[group_homomorphism; group_div] THEN
  MESON_TAC[GROUP_MUL; GROUP_INV]);;

let GROUP_HOMOMORPHISM_POW = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x n. x IN group_carrier G
                  ==> f(group_pow G x n) = group_pow G' (f x) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_homomorphism] THEN DISCH_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[group_pow; GROUP_POW]);;

let GROUP_HOMOMORPHISM_ZPOW = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> !x n. x IN group_carrier G
                  ==> f(group_zpow G x n) = group_zpow G' (f x) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_zpow] THEN
  COND_CASES_TAC THEN
  ASM_MESON_TAC[GROUP_HOMOMORPHISM_POW; GROUP_HOMOMORPHISM_INV; GROUP_POW]);;

let GROUP_HOMOMORPHISM_ID = prove
 (`!G:A group. group_homomorphism (G,G) (\x. x)`,
  REWRITE_TAC[group_homomorphism; IMAGE_ID; SUBSET_REFL]);;

let GROUP_MONOMORPHISM_ID = prove
 (`!G:A group. group_monomorphism (G,G) (\x. x)`,
  SIMP_TAC[group_monomorphism; GROUP_HOMOMORPHISM_ID]);;

let GROUP_EPIMORPHISM_ID = prove
 (`!G:A group. group_epimorphism (G,G) (\x. x)`,
  SIMP_TAC[group_epimorphism; GROUP_HOMOMORPHISM_ID; IMAGE_ID]);;

let GROUP_ISOMORPHISMS_ID = prove
 (`!G:A group. group_isomorphisms (G,G) ((\x. x),(\x. x))`,
  REWRITE_TAC[group_isomorphisms; GROUP_HOMOMORPHISM_ID]);;

let GROUP_ISOMORPHISM_ID = prove
 (`!G:A group. group_isomorphism (G,G) (\x. x)`,
  REWRITE_TAC[group_isomorphism] THEN MESON_TAC[GROUP_ISOMORPHISMS_ID]);;

let GROUP_HOMOMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        group_homomorphism(G1,G2) f /\ group_homomorphism(G2,G3) g
        ==> group_homomorphism(G1,G3) (g o f)`,
  SIMP_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let GROUP_MONOMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        group_monomorphism(G1,G2) f /\ group_monomorphism(G2,G3) g
        ==> group_monomorphism(G1,G3) (g o f)`,
  REWRITE_TAC[group_monomorphism; group_homomorphism; INJECTIVE_ON_ALT] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let GROUP_MONOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        group_homomorphism(A,B) f /\ group_homomorphism(B,C) g /\
        group_monomorphism(A,C) (g o f)
        ==> group_monomorphism(A,B) f`,
  REWRITE_TAC[group_monomorphism; o_THM] THEN MESON_TAC[]);;

let GROUP_EPIMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        group_epimorphism(G1,G2) f /\ group_epimorphism(G2,G3) g
        ==> group_epimorphism(G1,G3) (g o f)`,
  SIMP_TAC[group_epimorphism; IMAGE_o] THEN
  MESON_TAC[GROUP_HOMOMORPHISM_COMPOSE]);;

let GROUP_EPIMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        group_homomorphism(A,B) f /\ group_homomorphism(B,C) g /\
        group_epimorphism(A,C) (g o f)
        ==> group_epimorphism(B,C) g`,
  REWRITE_TAC[group_epimorphism; group_homomorphism; o_THM; IMAGE_o] THEN
  SET_TAC[]);;

let GROUP_MONOMORPHISM_LEFT_INVERTIBLE = prove
 (`!G H (f:A->B) g.
        group_homomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> g(f x) = x)
        ==> group_monomorphism (G,H) f`,
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; group_monomorphism] THEN
  MESON_TAC[]);;

let GROUP_EPIMORPHISM_RIGHT_INVERTIBLE = prove
 (`!G H (f:A->B) g.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,G) g /\
        (!x. x IN group_carrier G ==> g(f x) = x)
        ==> group_epimorphism (H,G) g`,
  SIMP_TAC[group_epimorphism] THEN REWRITE_TAC[group_homomorphism] THEN
  SET_TAC[]);;

let GROUP_HOMOMORPHISM_INTO_SUBGROUP = prove
 (`!G G' h (f:A->B).
        group_homomorphism (G,G') f /\ IMAGE f (group_carrier G) SUBSET h
        ==> group_homomorphism (G,subgroup_generated G' h) f`,
  REPEAT GEN_TAC THEN SIMP_TAC[group_homomorphism; SUBGROUP_GENERATED] THEN
  REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]);;

let GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN = prove
 (`!(f:A->B) G H s.
      group_homomorphism(G,subgroup_generated H s) f <=>
      group_homomorphism(G,H) f /\
      IMAGE f (group_carrier G) SUBSET group_carrier(subgroup_generated H s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_homomorphism] THEN
  MP_TAC(ISPECL [`H:B group`; `s:B->bool`]
    GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBGROUP_GENERATED] THEN SET_TAC[]);;

let GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ = prove
 (`!G G' h (f:A->B).
        h subgroup_of G'
        ==> (group_homomorphism (G,subgroup_generated G' h) f <=>
             group_homomorphism (G,G') f /\
             IMAGE f (group_carrier G) SUBSET h)`,
  SIMP_TAC[GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP]);;

let GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED = prove
 (`!(f:A->B) G H s.
        group_homomorphism (G,H) f
        ==> group_homomorphism(subgroup_generated G s,H) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_homomorphism] THEN
  MP_TAC(ISPECL [`G:A group`; `s:A->bool`]
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  SIMP_TAC[SUBSET; SUBGROUP_GENERATED] THEN SET_TAC[]);;

let GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS = prove
 (`!G H g h (f:A->B).
      group_homomorphism(G,H) f /\ IMAGE f g SUBSET h
      ==> group_homomorphism(subgroup_generated G g,subgroup_generated H h) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_INDUCT THEN RULE_ASSUM_TAC
   (REWRITE_RULE[group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  MP_TAC(REWRITE_RULE[SUBSET] (ISPECL [`G:A group`; `g:A->bool`]
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] SUBGROUP_GENERATED_SUBSET_CARRIER) THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[GROUP_ID; SUBGROUP_GENERATED];
    ASM_MESON_TAC[GROUP_ID; SUBGROUP_GENERATED];
    ASM_MESON_TAC[GROUP_INV; SUBGROUP_GENERATED];
    ASM_MESON_TAC[GROUP_MUL; SUBGROUP_GENERATED]]);;

let GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED = prove
 (`!(f:A->B) G H s.
        group_monomorphism (G,H) f
        ==> group_monomorphism(subgroup_generated G s,H) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_monomorphism] THEN
  MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED] THEN
  MP_TAC(ISPECL [`G:A group`; `s:A->bool`]
    GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  SET_TAC[]);;

let GROUP_MONOMORPHISM_BETWEEN_SUBGROUPS = prove
 (`!G H s t (f:A->B).
      group_monomorphism(G,H) f /\ IMAGE f s SUBSET t
      ==> group_monomorphism(subgroup_generated G s,subgroup_generated H t) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_monomorphism] THEN
  SIMP_TAC[GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS] THEN
  MP_TAC(ISPECL [`G:A group`; `s:A->bool`]
    GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  SET_TAC[]);;

let GROUP_MONOMORPHISM_INTO_SUPERGROUP = prove
 (`!G G' t (f:A->B).
        group_monomorphism(G,subgroup_generated G' t) f
        ==> group_monomorphism(G,G') f`,
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN] THEN
  MESON_TAC[]);;

let GROUP_HOMOMORPHISM_INCLUSION = prove
 (`!G s:A->bool. group_homomorphism(subgroup_generated G s,G) (\x. x)`,
  SIMP_TAC[GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED;
           GROUP_HOMOMORPHISM_ID]);;

let GROUP_MONOMORPHISM_INCLUSION = prove
 (`!G s:A->bool. group_monomorphism(subgroup_generated G s,G) (\x. x)`,
  SIMP_TAC[GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED;
           GROUP_MONOMORPHISM_ID]);;

let SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE = prove
 (`!G H (f:A->B) s.
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> group_carrier (subgroup_generated H (IMAGE f s)) =
            IMAGE f (group_carrier(subgroup_generated G s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC SUBGROUP_GENERATED_INDUCT THEN
    REWRITE_TAC[FORALL_IN_IMAGE_2] THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    MP_TAC(REWRITE_RULE[SUBSET] (ISPECL [`G:A group`; `s:A->bool`]
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET)) THEN
    FIRST_X_ASSUM(MP_TAC o GSYM o GEN_REWRITE_RULE I [group_homomorphism]) THEN
    ASM_SIMP_TAC[SUBGROUP_GENERATED_INC; FUN_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[SUBGROUP_GENERATED; GROUP_ID; GROUP_INV; GROUP_MUL];
    FIRST_ASSUM(MP_TAC o ISPECL [`s:A->bool`; `IMAGE (f:A->B) s`] o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS)) THEN
    SIMP_TAC[group_homomorphism; SUBSET_REFL]]);;

let GROUP_EPIMORPHISM_BETWEEN_SUBGROUPS = prove
 (`!G H (f:A->B).
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> group_epimorphism(subgroup_generated G s,
                              subgroup_generated H (IMAGE f s)) f`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN] THEN
  SIMP_TAC[GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED] THEN
  ASM_SIMP_TAC[SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE; SUBSET_REFL]);;

let GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ_GEN = prove
 (`!(f:A->B) G H s.
      group_epimorphism(G,subgroup_generated H s) f <=>
      group_homomorphism(G,H) f /\
      IMAGE f (group_carrier G) = group_carrier(subgroup_generated H s)`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN] THEN
  SET_TAC[]);;

let GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ = prove
 (`!G G' h (f:A->B).
        h subgroup_of G'
        ==> (group_epimorphism (G,subgroup_generated G' h) f <=>
             group_homomorphism (G,G') f /\
             IMAGE f (group_carrier G) = h)`,
  SIMP_TAC[GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ_GEN;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP]);;

let GROUP_ISOMORPHISM = prove
 (`!G G' f:A->B.
      group_isomorphism (G,G') (f:A->B) <=>
      group_homomorphism (G,G') f /\
      IMAGE f (group_carrier G) = group_carrier G' /\
      (!x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
             ==> x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_isomorphism; group_isomorphisms; group_homomorphism] THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME
    `IMAGE (f:A->B) (group_carrier G) = group_carrier G'`)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_IMAGE_2] THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC(GROUP_PROPERTIES));;

let GROUP_ISOMORPHISM_SUBSET = prove
 (`!G G' f:A->B.
      group_isomorphism (G,G') (f:A->B) <=>
      group_homomorphism (G,G') f /\
      (!z. z IN group_carrier G' ==> ?x. x IN group_carrier G /\ f x = z) /\
      (!x y. x IN group_carrier G /\ y IN group_carrier G /\ f x = f y
             ==> x = y)`,
  REWRITE_TAC[GROUP_ISOMORPHISM; group_homomorphism] THEN
  SET_TAC[]);;

let SUBGROUP_OF_HOMOMORPHIC_IMAGE = prove
 (`!G G' (f:A->B).
        group_homomorphism (G,G') f /\ h subgroup_of G
        ==> IMAGE f h subgroup_of G'`,
  REWRITE_TAC[group_homomorphism; subgroup_of] THEN SET_TAC[]);;

let SUBGROUP_OF_HOMOMORPHIC_PREIMAGE = prove
 (`!G H (f:A->B) h.
        group_homomorphism(G,H) f /\ h subgroup_of H
        ==> {x | x IN group_carrier G /\ f x IN h} subgroup_of G`,
  REWRITE_TAC[group_homomorphism; subgroup_of; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[GROUP_ID; GROUP_INV; GROUP_MUL]);;

let SUBGROUP_OF_EPIMORPHIC_PREIMAGE = prove
 (`!G H (f:A->B) h.
        group_epimorphism(G,H) f /\ h subgroup_of H
        ==> {x | x IN group_carrier G /\ f x IN h} subgroup_of G /\
            IMAGE f {x | x IN group_carrier G /\ f x IN h} = h`,
  REWRITE_TAC[group_epimorphism] THEN
  REWRITE_TAC[group_homomorphism; subgroup_of; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  MESON_TAC[GROUP_ID; GROUP_INV; GROUP_MUL]);;

let GROUP_MONOMORPHISM_EPIMORPHISM = prove
 (`!G G' f:A->B.
        group_monomorphism (G,G') f /\ group_epimorphism (G,G') f <=>
        group_isomorphism (G,G') f`,
  REWRITE_TAC[GROUP_ISOMORPHISM; group_monomorphism; group_epimorphism] THEN
  MESON_TAC[]);;

let SUBGROUP_MONOMORPHISM_EPIMORPHISM = prove
 (`!G G' s (f:A->B).
        group_monomorphism(G,G') f /\
        group_epimorphism(G,subgroup_generated G' s) f <=>
        group_isomorphism(G,subgroup_generated G' s) f`,
  MESON_TAC[GROUP_MONOMORPHISM_EPIMORPHISM; GROUP_MONOMORPHISM_INTO_SUPERGROUP;
            GROUP_HOMOMORPHISM_INTO_SUBGROUP; group_monomorphism;
            group_epimorphism]);;

let GROUP_ISOMORPHISM_IMP_MONOMORPHISM = prove
 (`!G G' (f:A->B).
        group_isomorphism (G,G') f ==> group_monomorphism (G,G') f`,
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM]);;

let GROUP_ISOMORPHISM_IMP_EPIMORPHISM = prove
 (`!G G' (f:A->B).
        group_isomorphism (G,G') f ==> group_epimorphism (G,G') f`,
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM]);;

let GROUP_MONOMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) G H. group_monomorphism(G,H) f ==> group_homomorphism(G,H) f`,
  SIMP_TAC[group_monomorphism]);;

let GROUP_EPIMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) G H. group_epimorphism(G,H) f ==> group_homomorphism(G,H) f`,
  SIMP_TAC[group_epimorphism]);;

let GROUP_ISOMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) G H. group_isomorphism(G,H) f ==> group_homomorphism(G,H) f`,
  SIMP_TAC[GROUP_ISOMORPHISM]);;

let GROUP_AUTOMORPHISM_IMP_ENDOMORPHISM = prove
 (`!G (f:A->A). group_automorphism G f ==> group_endomorphism G f`,
  REWRITE_TAC[group_automorphism; group_endomorphism] THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE = prove
 (`!G H (f:A->B).
        FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
        CARD(group_carrier G) = CARD(group_carrier H)
        ==> (group_isomorphism(G,H) f <=> group_monomorphism(G,H) f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_IMP_MONOMORPHISM] THEN
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[group_monomorphism; group_epimorphism] THEN
  REWRITE_TAC[group_homomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC(ISPECL
   [`group_carrier G:A->bool`; `group_carrier H:B->bool`; `f:A->B`]
        SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let GROUP_ISOMORPHISM_EQ_EPIMORPHISM_FINITE = prove
 (`!G H (f:A->B).
        FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
        CARD(group_carrier G) = CARD(group_carrier H)
        ==> (group_isomorphism(G,H) f <=> group_epimorphism(G,H) f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_IMP_EPIMORPHISM] THEN
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[group_monomorphism; group_epimorphism] THEN
  REWRITE_TAC[group_homomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC(ISPECL
   [`group_carrier G:A->bool`; `group_carrier H:B->bool`; `f:A->B`]
        SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let GROUP_ISOMORPHISMS_CONJUGATION = prove
 (`!G a:A.
        a IN group_carrier G
        ==> group_isomorphisms (G,G)
             (group_conjugation G a,group_conjugation G (group_inv G a))`,
  REWRITE_TAC[group_isomorphisms; GROUP_HOMOMORPHISM] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_CONJUGATION; GROUP_MUL;
           GROUP_CONJUGATION_CONJUGATION; GROUP_INV] THEN
  SIMP_TAC[GROUP_MUL_LINV; GROUP_MUL_RINV; GROUP_CONJUGATION_BY_ID] THEN
  REWRITE_TAC[group_conjugation] THEN REPEAT STRIP_TAC THEN GROUP_TAC);;

let GROUP_AUTOMORPHISM_CONJUGATION = prove
 (`!G a:A.
        a IN group_carrier G ==> group_automorphism G (group_conjugation G a)`,
  REWRITE_TAC[group_automorphism; group_isomorphism] THEN
  MESON_TAC[GROUP_ISOMORPHISMS_CONJUGATION]);;

let GROUP_ISOMORPHISM_CONJUGATION = prove
 (`!G a:A. a IN group_carrier G
           ==> group_isomorphism (G,G) (group_conjugation G a)`,
  REWRITE_TAC[GSYM group_automorphism; GROUP_AUTOMORPHISM_CONJUGATION]);;

let GROUP_HOMOMORPHISM_CONJUGATION = prove
 (`!G a:A. a IN group_carrier G
           ==> group_homomorphism (G,G) (group_conjugation G a)`,
  SIMP_TAC[GROUP_ISOMORPHISM_CONJUGATION;
           GROUP_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let CARD_LE_GROUP_MONOMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_monomorphism(G,H) f ==> group_carrier G <=_c group_carrier H`,
  REWRITE_TAC[group_monomorphism; le_c; group_homomorphism] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `f:A->B` THEN ASM SET_TAC[]);;

let CARD_LE_GROUP_EPIMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_epimorphism(G,H) f ==> group_carrier H <=_c group_carrier G`,
  REWRITE_TAC[group_epimorphism; LE_C; group_homomorphism] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `f:A->B` THEN ASM SET_TAC[]);;

let CARD_EQ_GROUP_ISOMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_isomorphism(G,H) f ==> group_carrier G =_c group_carrier H`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; GSYM CARD_LE_ANTISYM] THEN
  MESON_TAC[CARD_LE_GROUP_MONOMORPHIC_IMAGE; CARD_LE_GROUP_EPIMORPHIC_IMAGE]);;

let FINITE_GROUP_MONOMORPHIC_PREIMAGE = prove
 (`!G H (f:A->B).
        group_monomorphism(G,H) f /\ FINITE(group_carrier H)
        ==> FINITE(group_carrier G)`,
  MESON_TAC[CARD_LE_FINITE; CARD_LE_GROUP_MONOMORPHIC_IMAGE]);;

let FINITE_GROUP_EPIMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_epimorphism(G,H) f /\ FINITE(group_carrier G)
        ==> FINITE(group_carrier H)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) THEN
  ASM_MESON_TAC[CARD_LE_GROUP_EPIMORPHIC_IMAGE]);;

let CARD_EQ_GROUP_MONOMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_monomorphism(G,H) f
        ==> IMAGE f (group_carrier G) =_c group_carrier G`,
  REWRITE_TAC[group_monomorphism] THEN MESON_TAC[CARD_EQ_IMAGE]);;

let GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS = prove
 (`!G H g h (f:A->B) f'.
      group_isomorphisms(G,H) (f,f') /\
      IMAGE f g SUBSET h /\ IMAGE f' h SUBSET g
      ==> group_isomorphisms (subgroup_generated G g,subgroup_generated H h)
                             (f,f')`,
  SIMP_TAC[group_isomorphisms; GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS] THEN
  MESON_TAC[SUBSET; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]);;

let GROUP_ISOMORPHISM_BETWEEN_SUBGROUPS = prove
 (`!G H g h (f:A->B).
      group_isomorphism(G,H) f /\ g SUBSET group_carrier G /\ IMAGE f g = h
      ==> group_isomorphism(subgroup_generated G g,subgroup_generated H h) f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[group_isomorphism] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f':B->A` THEN
  REWRITE_TAC[group_isomorphisms] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS; SUBSET_REFL];
    ALL_TAC;
    ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
    ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET]] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SUBGROUP_GENERATED_RESTRICT] THEN
  MATCH_MP_TAC GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN
  ASM SET_TAC[]);;

let GROUP_ISOMORPHISMS_COMPOSE = prove
 (`!G1 G2 G3 (f1:A->B) (f2:B->C) g1 g2.
        group_isomorphisms(G1,G2) (f1,g1) /\ group_isomorphisms(G2,G3) (f2,g2)
        ==> group_isomorphisms(G1,G3) (f2 o f1,g1 o g2)`,
  SIMP_TAC[group_isomorphisms; group_homomorphism;
           SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let GROUP_ISOMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        group_isomorphism(G1,G2) f /\ group_isomorphism(G2,G3) g
        ==> group_isomorphism(G1,G3) (g o f)`,
  REWRITE_TAC[group_isomorphism] THEN MESON_TAC[GROUP_ISOMORPHISMS_COMPOSE]);;

let GROUP_ISOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        group_homomorphism(A,B) f /\ group_homomorphism(B,C) g /\
        group_isomorphism(A,C) (g o f)
        ==> group_monomorphism(A,B) f /\ group_epimorphism(B,C) g`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  MESON_TAC[GROUP_MONOMORPHISM_COMPOSE_REV; GROUP_EPIMORPHISM_COMPOSE_REV]);;

let GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        group_epimorphism (A,B) f /\
        group_homomorphism (B,C) g /\
        group_isomorphism (A,C) (g o f)
        ==> group_isomorphism (A,B) f /\ group_isomorphism (B,C) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GROUP_ISOMORPHISM_COMPOSE_REV; group_epimorphism;
                  GROUP_MONOMORPHISM_EPIMORPHISM];
    REWRITE_TAC[group_isomorphism; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f':B->A` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM group_isomorphism] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN
    EXISTS_TAC `(g:B->C) o f o (f':B->A)` THEN CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN
      ASM_MESON_TAC[GROUP_ISOMORPHISMS_SYM; group_isomorphism];
      RULE_ASSUM_TAC(REWRITE_RULE
       [group_isomorphisms; group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC[o_THM]]]);;

let GROUP_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        group_homomorphism (A,B) f /\
        group_monomorphism (B,C) g /\
        group_isomorphism (A,C) (g o f)
        ==> group_isomorphism (A,B) f /\ group_isomorphism (B,C) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GROUP_ISOMORPHISM_COMPOSE_REV; group_monomorphism;
                  GROUP_MONOMORPHISM_EPIMORPHISM];
    REWRITE_TAC[group_isomorphism; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g':C->B` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM group_isomorphism] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN
    EXISTS_TAC `(g':C->B) o g o (f:A->B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN
      ASM_MESON_TAC[GROUP_ISOMORPHISMS_SYM; group_isomorphism];
      RULE_ASSUM_TAC(REWRITE_RULE
       [group_isomorphisms; group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC[o_THM]]]);;

let GROUP_ISOMORPHISM_INVERSE = prove
 (`!(f:A->B) g G H.
        group_isomorphism(G,H) f /\
        (!x. x IN group_carrier G ==> g(f x) = x)
        ==> group_isomorphism(H,G) g`,
  REWRITE_TAC[group_isomorphism; group_isomorphisms; group_homomorphism] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `f:A->B` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!y. y IN group_carrier H ==> (g:B->A) y IN group_carrier G`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN group_carrier H ==> (f:A->B)(g y) = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[GROUP_ID; GROUP_INV; GROUP_MUL]);;

let GROUP_ISOMORPHISMS_OPPOSITE_GROUP = prove
 (`!G:A group.
        group_isomorphisms(G,opposite_group G) (group_inv G,group_inv G)`,
  REWRITE_TAC[group_isomorphisms; group_homomorphism; OPPOSITE_GROUP] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_INV_ID] THEN
  SIMP_TAC[GROUP_INV; GROUP_INV_MUL; GROUP_INV_INV]);;

let GROUP_ISOMORPHISM_OPPOSITE_GROUP = prove
 (`!G:A group.
        group_isomorphism(G,opposite_group G) (group_inv G)`,
  REWRITE_TAC[group_isomorphism] THEN
  MESON_TAC[GROUP_ISOMORPHISMS_OPPOSITE_GROUP]);;

let GROUP_HOMOMORPHISM_FROM_TRIVIAL_GROUP = prove
 (`!(f:A->B) G H.
        trivial_group G
        ==> (group_homomorphism(G,H) f <=> f(group_id G) = group_id H)`,
  REPEAT GEN_TAC THEN SIMP_TAC[trivial_group; group_homomorphism] THEN
  ASM_CASES_TAC `(f:A->B)(group_id G) = group_id H` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[IN_SING; GROUP_MUL_LID; GROUP_ID; SUBSET; FORALL_IN_IMAGE;
               GROUP_INV_ID]);;

let GROUP_MONOMORPHISM_FROM_TRIVIAL_GROUP = prove
 (`!(f:A->B) G H.
        trivial_group G
        ==> (group_monomorphism (G,H) f <=> group_homomorphism (G,H) f)`,
  REWRITE_TAC[group_monomorphism; trivial_group] THEN SET_TAC[]);;

let GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP = prove
 (`!(f:A->B) G H.
        trivial_group H
        ==> (group_monomorphism (G,H) f <=>
             group_homomorphism (G,H) f /\ trivial_group G)`,
  SIMP_TAC[group_monomorphism; trivial_group; group_homomorphism] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `G:A group` GROUP_ID) THEN SET_TAC[]);;

let GROUP_EPIMORPHISM_FROM_TRIVIAL_GROUP = prove
 (`!(f:A->B) G H.
        trivial_group G
        ==> (group_epimorphism (G,H) f <=>
             group_homomorphism (G,H) f /\ trivial_group H)`,
  SIMP_TAC[group_epimorphism; trivial_group; group_homomorphism] THEN
  SET_TAC[]);;

let GROUP_EPIMORPHISM_TO_TRIVIAL_GROUP = prove
 (`!(f:A->B) G H.
        trivial_group H
        ==> (group_epimorphism (G,H) f <=>
             group_homomorphism (G,H) f)`,
  REWRITE_TAC[group_epimorphism; trivial_group; group_homomorphism] THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY(MP_TAC o C ISPEC GROUP_ID) [`G:A group`; `H:B group`] THEN
  SET_TAC[]);;

let GROUP_HOMOMORPHISM_PAIRWISE = prove
 (`!(f:A->B#C) G H K.
        group_homomorphism(G,prod_group H K) f <=>
        group_homomorphism(G,H) (FST o f) /\
        group_homomorphism(G,K) (SND o f)`,
  REWRITE_TAC[group_homomorphism; PROD_GROUP] THEN
  REWRITE_TAC[FORALL_PAIR_FUN_THM; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; IN_CROSS; PAIR_EQ] THEN MESON_TAC[]);;

let GROUP_HOMOMORPHISM_PAIRED = prove
 (`!(f:A->B) (g:A->C) G H K.
        group_homomorphism(G,prod_group H K) (\x. f x,g x) <=>
        group_homomorphism(G,H) f /\
        group_homomorphism(G,K) g`,
  REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRWISE; o_DEF; ETA_AX]);;

let GROUP_HOMOMORPHISM_PAIRED2 = prove
 (`!(f:A->B) (g:C->D) G H G' H'.
        group_homomorphism(prod_group G H,prod_group G' H')
                (\(x,y). f x,g y) <=>
        group_homomorphism(G,G') f /\ group_homomorphism(H,H') g`,
  REWRITE_TAC[group_homomorphism; PROD_GROUP; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[GROUP_ID]);;

let GROUP_ISOMORPHISMS_PAIRED2 = prove
 (`!(f:A->B) (g:C->D) f' g' G H G' H'.
        group_isomorphisms(prod_group G H,prod_group G' H')
                ((\(x,y). f x,g y),(\(x,y). f' x,g' y)) <=>
        group_isomorphisms(G,G') (f,f') /\
        group_isomorphisms(H,H') (g,g')`,
  REWRITE_TAC[group_isomorphisms; GROUP_HOMOMORPHISM_PAIRED2] THEN
  REWRITE_TAC[PROD_GROUP; FORALL_IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[GROUP_ID]);;

let GROUP_ISOMORPHISM_PAIRED2 = prove
 (`!(f:A->B) (g:C->D) G H G' H'.
        group_isomorphism(prod_group G H,prod_group G' H')
                (\(x,y). f x,g y) <=>
        group_isomorphism(G,G') f /\ group_isomorphism(H,H') g`,
  REWRITE_TAC[GROUP_ISOMORPHISM; GROUP_HOMOMORPHISM_PAIRED2] THEN
  REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS; IMAGE_PAIRED_CROSS] THEN
  REWRITE_TAC[CROSS_EQ; IMAGE_EQ_EMPTY; GROUP_CARRIER_NONEMPTY; PAIR_EQ] THEN
  MESON_TAC[GROUP_ID]);;

let GROUP_HOMOMORPHISM_OF_FST = prove
 (`!(f:A->C) A (B:B group) C.
        group_homomorphism (prod_group A B,C) (f o FST) <=>
        group_homomorphism (A,C) f`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_GROUP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[GROUP_ID]);;

let GROUP_HOMOMORPHISM_OF_SND = prove
 (`!(f:B->C) (A:A group) B C.
        group_homomorphism (prod_group A B,C) (f o SND) <=>
        group_homomorphism (B,C) f`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_GROUP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[GROUP_ID]);;

let GROUP_EPIMORPHISM_OF_FST = prove
 (`!(f:A->C) A (B:B group) C.
        group_epimorphism (prod_group A B,C) (f o FST) <=>
        group_epimorphism (A,C) f`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_OF_FST] THEN
  REWRITE_TAC[PROD_GROUP; IMAGE_o; IMAGE_FST_CROSS; GROUP_CARRIER_NONEMPTY]);;

let GROUP_EPIMORPHISM_OF_SND = prove
 (`!(f:B->C) (A:A group) B C.
        group_epimorphism (prod_group A B,C) (f o SND) <=>
        group_epimorphism (B,C) f`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_OF_SND] THEN
  REWRITE_TAC[PROD_GROUP; IMAGE_o; IMAGE_SND_CROSS; GROUP_CARRIER_NONEMPTY]);;

let GROUP_HOMOMORPHISM_FST = prove
 (`!(A:A group) (B:B group). group_homomorphism (prod_group A B,A) FST`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_GROUP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[GROUP_ID]);;

let GROUP_HOMOMORPHISM_SND = prove
 (`!(A:A group) (B:B group). group_homomorphism (prod_group A B,B) SND`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_GROUP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[GROUP_ID]);;

let GROUP_EPIMORPHISM_FST = prove
 (`!(A:A group) (B:B group). group_epimorphism (prod_group A B,A) FST`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_FST] THEN
  REWRITE_TAC[PROD_GROUP; IMAGE_o; IMAGE_FST_CROSS; GROUP_CARRIER_NONEMPTY]);;

let GROUP_EPIMORPHISM_SND = prove
 (`!(A:A group) (B:B group). group_epimorphism (prod_group A B,B) SND`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_SND] THEN
  REWRITE_TAC[PROD_GROUP; IMAGE_o; IMAGE_SND_CROSS; GROUP_CARRIER_NONEMPTY]);;

let GROUP_ISOMORPHISM_FST = prove
 (`!(G:A group) (H:B group).
        group_isomorphism (prod_group G H,G) FST <=> trivial_group H`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[GROUP_EPIMORPHISM_FST] THEN
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM_FST] THEN
  SIMP_TAC[FORALL_PAIR_THM; PROD_GROUP; IN_CROSS; PAIR_EQ] THEN
  REWRITE_TAC[TRIVIAL_GROUP_ALT] THEN
  MP_TAC(ISPEC `G:A group` GROUP_CARRIER_NONEMPTY) THEN SET_TAC[]);;

let GROUP_ISOMORPHISM_SND = prove
 (`!(G:A group) (H:B group).
        group_isomorphism (prod_group G H,H) SND <=> trivial_group G`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[GROUP_EPIMORPHISM_SND] THEN
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM_SND] THEN
  SIMP_TAC[FORALL_PAIR_THM; PROD_GROUP; IN_CROSS; PAIR_EQ] THEN
  REWRITE_TAC[TRIVIAL_GROUP_ALT] THEN
  MP_TAC(ISPEC `H:B group` GROUP_CARRIER_NONEMPTY) THEN SET_TAC[]);;

let GROUP_ISOMORPHISMS_PROD_GROUP_SWAP = prove
 (`!(G:A group) (H:B group).
        group_isomorphisms (prod_group G H,prod_group H G)
                           ((\(x,y). y,x),(\(y,x). x,y))`,
  REWRITE_TAC[group_isomorphisms; FORALL_PAIR_THM] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRWISE; o_DEF; LAMBDA_PAIR] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] GROUP_HOMOMORPHISM_OF_FST;
              REWRITE_RULE[o_DEF] GROUP_HOMOMORPHISM_OF_SND] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_ID]);;

let GROUP_HOMOMORPHISM_COMPONENTWISE = prove
 (`!G k H (f:A->K->B).
        group_homomorphism(G,product_group k H) f <=>
        IMAGE f (group_carrier G) SUBSET EXTENSIONAL k /\
        !i. i IN k ==> group_homomorphism (G,H i) (\x. f x i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PRODUCT_GROUP; IN_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[RESTRICTION_UNIQUE_ALT] THEN
  REWRITE_TAC[SET_RULE `f IN EXTENSIONAL s <=> EXTENSIONAL s f`] THEN
  ASM_CASES_TAC
   `!x. x IN group_carrier G ==> EXTENSIONAL k ((f:A->K->B) x)`
  THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[GROUP_ID; GROUP_INV; GROUP_MUL] THEN
  MESON_TAC[]);;

let GROUP_HOMOMORPHISM_COMPONENTWISE_UNIV = prove
 (`!G k (f:A->K->B).
        group_homomorphism(G,product_group (:K) H) f <=>
        !i. group_homomorphism (G,H i) (\x. f x i)`,
  REWRITE_TAC[GROUP_HOMOMORPHISM_COMPONENTWISE; IN_UNIV] THEN
  REWRITE_TAC[SET_RULE `s SUBSET P <=> !x. x IN s ==> P x`] THEN
  REWRITE_TAC[EXTENSIONAL_UNIV]);;

let GROUP_HOMOMORPHISM_PRODUCT_PROJECTION = prove
 (`!(G:K->A group) k i.
        i IN k ==> group_homomorphism (product_group k G,G i) (\x. x i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`product_group k (G:K->A group)`; `k:K->bool`; `G:K->A group`;
                 `\x:K->A. x`]
        GROUP_HOMOMORPHISM_COMPONENTWISE) THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_ID] THEN
 ASM_SIMP_TAC[GROUP_HOMOMORPHISM_COMPONENTWISE]);;

let GROUP_EPIMORPHISM_PRODUCT_PROJECTION = prove
 (`!(G:K->A group) k i.
        i IN k ==> group_epimorphism (product_group k G,G i) (\x. x i)`,
  SIMP_TAC[group_epimorphism; GROUP_HOMOMORPHISM_PRODUCT_PROJECTION] THEN
  SIMP_TAC[IMAGE_PROJECTION_CARTESIAN_PRODUCT; PRODUCT_GROUP;
           CARTESIAN_PRODUCT_EQ_EMPTY; GROUP_CARRIER_NONEMPTY]);;

let ABELIAN_GROUP_EPIMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
     group_epimorphism(G,H) f /\ abelian_group G ==> abelian_group H`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[group_epimorphism; group_homomorphism; abelian_group] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE_2] THEN ASM SET_TAC[]);;

let ABELIAN_GROUP_HOMOMORPHISM_GROUP_MUL = prove
 (`!(f:A->B) g A B.
        abelian_group B /\
        group_homomorphism(A,B) f /\ group_homomorphism(A,B) g
        ==> group_homomorphism(A,B) (\x. group_mul B (f x) (g x))`,
  REWRITE_TAC[group_homomorphism; ABELIAN_GROUP_MUL_AC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[GROUP_MUL_LID; GROUP_ID; GROUP_MUL; GROUP_INV_MUL; GROUP_INV]);;

let ABELIAN_GROUP_HOMOMORPHISM_INVERSION = prove
 (`!G:A group. group_homomorphism (G,G) (group_inv G) <=> abelian_group G`,
  REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE; GROUP_INV] THEN
  SIMP_TAC[GROUP_INV_MUL; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GROUP_CARRIER_INV; abelian_group] THEN MESON_TAC[]);;

let ABELIAN_GROUP_ISOMORPHISMS_INVERSION = prove
 (`!G:A group. group_isomorphisms (G,G) (group_inv G,group_inv G) <=>
               abelian_group G`,
  SIMP_TAC[GROUP_ISOMORPHISMS; ABELIAN_GROUP_HOMOMORPHISM_INVERSION] THEN
  SIMP_TAC[GROUP_INV_INV; GROUP_INV]);;

let ABELIAN_GROUP_ISOMORPHISM_INVERSION = prove
 (`!G:A group. group_isomorphism (G,G) (group_inv G) <=> abelian_group G`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[GROUP_ISOMORPHISM_IMP_HOMOMORPHISM;
              ABELIAN_GROUP_HOMOMORPHISM_INVERSION];
    MESON_TAC[ABELIAN_GROUP_ISOMORPHISMS_INVERSION; group_isomorphism]]);;

let ABELIAN_GROUP_MONOMORPHISM_INVERSION = prove
 (`!G:A group. group_monomorphism (G,G) (group_inv G) <=> abelian_group G`,
  MESON_TAC[GROUP_ISOMORPHISM_IMP_MONOMORPHISM;
            GROUP_MONOMORPHISM_IMP_HOMOMORPHISM;
            ABELIAN_GROUP_HOMOMORPHISM_INVERSION;
            ABELIAN_GROUP_ISOMORPHISM_INVERSION]);;

let ABELIAN_GROUP_EPIMORPHISM_INVERSION = prove
 (`!G:A group. group_epimorphism (G,G) (group_inv G) <=> abelian_group G`,
  MESON_TAC[GROUP_ISOMORPHISM_IMP_EPIMORPHISM;
            GROUP_EPIMORPHISM_IMP_HOMOMORPHISM;
            ABELIAN_GROUP_HOMOMORPHISM_INVERSION;
            ABELIAN_GROUP_ISOMORPHISM_INVERSION]);;

let ABELIAN_GROUP_HOMOMORPHISM_POWERING = prove
 (`!(G:A group) n.
        abelian_group G ==> group_homomorphism(G,G) (\x. group_pow G x n)`,
  REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE; GROUP_POW] THEN
  SIMP_TAC[ABELIAN_GROUP_MUL_POW]);;

let ABELIAN_GROUP_HOMOMORPHISM_ZPOWERING = prove
 (`!(G:A group) n.
        abelian_group G ==> group_homomorphism(G,G) (\x. group_zpow G x n)`,
  REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE; GROUP_ZPOW] THEN
  SIMP_TAC[ABELIAN_GROUP_MUL_ZPOW]);;

let ABELIAN_GROUP_HOMOMORPHISM_GROUP_SUM = prove
 (`!(f:K->A->B) k A B.
        abelian_group B /\
        (!i. i IN k ==> group_homomorphism (A i,B) (f i))
        ==> group_homomorphism
              (sum_group k A,B)
              (\x. iterate (group_add B) k (\i. (f i) (x i)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SUM_GROUP_CLAUSES; IN_ELIM_THM] THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ABELIAN_GROUP_SUM THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
    ASM SET_TAC[];
    DISCH_TAC THEN ASM_SIMP_TAC[GSYM GROUP_ADD_EQ_MUL] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand)
       (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] ITERATE_OP_GEN) o
       rand o snd) THEN
    ASM_REWRITE_TAC[MONOIDAL_GROUP_ADD] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(x:K->A) IN group_carrier (sum_group k A)`;
        UNDISCH_TAC `(y:K->A) IN group_carrier (sum_group k A)`] THEN
      REWRITE_TAC[SUM_GROUP_CLAUSES; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[support; NEUTRAL_GROUP_ADD] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    W(MP_TAC o PART_MATCH rand
       (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] ITERATE_EQ) o snd) THEN
    ASM_SIMP_TAC[GROUP_ADD_EQ_MUL; SUM_GROUP_CLAUSES; MONOIDAL_GROUP_ADD] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[RESTRICTION] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [SUM_GROUP_CLAUSES; IN_ELIM_THM; cartesian_product;
      group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[GROUP_ADD_EQ_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* Relation of isomorphism.                                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("isomorphic_group",(12, "right"));;

let isomorphic_group = new_definition
 `G isomorphic_group G' <=> ?f:A->B. group_isomorphism (G,G') f`;;

let GROUP_ISOMORPHISM_IMP_ISOMORPHIC = prove
 (`!G H f:A->B. group_isomorphism (G,H) f ==> G isomorphic_group H`,
  REWRITE_TAC[isomorphic_group] THEN MESON_TAC[]);;

let ISOMORPHIC_GROUP_REFL = prove
 (`!G:A group. G isomorphic_group G`,
  GEN_TAC THEN REWRITE_TAC[isomorphic_group] THEN EXISTS_TAC `\x:A. x` THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_ID]);;

let ISOMORPHIC_GROUP_SYM = prove
 (`!(G:A group) (H:B group). G isomorphic_group H <=> H isomorphic_group G`,
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  MESON_TAC[GROUP_ISOMORPHISMS_SYM]);;

let ISOMORPHIC_GROUP_TRANS = prove
 (`!(G1:A group) (G2:B group) (G3:C group).
        G1 isomorphic_group G2 /\ G2 isomorphic_group G3
        ==> G1 isomorphic_group G3`,
  REWRITE_TAC[isomorphic_group] THEN MESON_TAC[GROUP_ISOMORPHISM_COMPOSE]);;

let ISOMORPHIC_GROUP_OPPOSITE_GROUP = prove
 (`!G:A group. (opposite_group G) isomorphic_group G`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  MESON_TAC[GROUP_ISOMORPHISMS_OPPOSITE_GROUP]);;

let ISOMORPHIC_GROUP_TRIVIALITY = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H ==> (trivial_group G <=> trivial_group H)`,
  REWRITE_TAC[isomorphic_group; TRIVIAL_GROUP; group_isomorphism;
              group_isomorphisms; group_homomorphism] THEN
  SET_TAC[]);;

let ISOMORPHIC_TO_TRIVIAL_GROUP = prove
 (`(!(G:A group) (H:B group).
        trivial_group G ==> (G isomorphic_group H <=> trivial_group H)) /\
   (!(G:A group) (H:B group).
        trivial_group H ==> (G isomorphic_group H <=> trivial_group G))`,
  let lemma = prove
   (`!(G:A group) (H:B group).
        trivial_group G ==> (G isomorphic_group H <=> trivial_group H)`,
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC[ISOMORPHIC_GROUP_TRIVIALITY]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[TRIVIAL_GROUP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    X_GEN_TAC `b:B` THEN DISCH_TAC THEN
    REWRITE_TAC[isomorphic_group; GROUP_ISOMORPHISM] THEN
    EXISTS_TAC `(\x. b):A->B` THEN
    ASM_REWRITE_TAC[group_homomorphism] THEN
    SIMP_TAC[IN_SING; IMAGE_CLAUSES; SUBSET_REFL] THEN
    ASM_MESON_TAC[GROUP_ID; GROUP_INV; GROUP_MUL; IN_SING]) in
  REWRITE_TAC[lemma] THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[lemma]);;

let ISOMORPHIC_TRIVIAL_GROUPS = prove
 (`!(G:A group) (H:B group).
        trivial_group G /\ trivial_group H
        ==> G isomorphic_group H`,
  MESON_TAC[ISOMORPHIC_TO_TRIVIAL_GROUP]);;

let ISOMORPHIC_GROUP_SINGLETON_GROUP = prove
 (`(!(G:A group) (b:B).
        G isomorphic_group singleton_group b <=> trivial_group G) /\
   (!a:A (G:B group).
        singleton_group a isomorphic_group G <=> trivial_group G)`,
  MESON_TAC[ISOMORPHIC_TO_TRIVIAL_GROUP; TRIVIAL_GROUP_SINGLETON_GROUP]);;

let ISOMORPHIC_GROUP_PROD_GROUPS = prove
 (`!(G:A group) (G':B group) (H:C group) (H':D group).
        G isomorphic_group G' /\ H isomorphic_group H'
        ==> (prod_group G H) isomorphic_group (prod_group G' H')`,
  REWRITE_TAC[isomorphic_group; group_isomorphism; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM GROUP_ISOMORPHISMS_PAIRED2] THEN MESON_TAC[]);;

let ISOMORPHIC_GROUP_PROD_GROUP_SYM = prove
 (`!(G:A group) (H:B group).
        prod_group G H isomorphic_group prod_group H G`,
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  MESON_TAC[GROUP_ISOMORPHISMS_PROD_GROUP_SWAP]);;

let ISOMORPHIC_GROUP_PROD_GROUP_SWAP_LEFT = prove
 (`!(G:A group) (H:B group) (K:C group).
        prod_group G H isomorphic_group K <=>
        prod_group H G isomorphic_group K`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_GROUP_TRANS) THEN
  REWRITE_TAC[ISOMORPHIC_GROUP_PROD_GROUP_SYM]);;

let ISOMORPHIC_GROUP_PROD_GROUP_SWAP_RIGHT = prove
 (`!(G:A group) (H:B group) (K:C group).
        G isomorphic_group prod_group H K <=>
        G isomorphic_group prod_group K H`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[ISOMORPHIC_GROUP_PROD_GROUP_SWAP_LEFT]);;

let ISOMORPHIC_PROD_TRIVIAL_GROUP = prove
 (`(!(G:A group) (H:B group).
        trivial_group G ==> (prod_group G H isomorphic_group H)) /\
   (!(G:A group) (H:B group).
        trivial_group H ==> (prod_group G H isomorphic_group G)) /\
   (!(G:A group) (H:B group).
        trivial_group G ==> (H isomorphic_group prod_group G H)) /\
   (!(G:A group) (H:B group).
        trivial_group H ==> (G isomorphic_group prod_group G H))`,
  let lemma = prove
   (`!(G:A group) (H:B group).
        trivial_group G ==> (prod_group G H isomorphic_group H)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_group] THEN
    EXISTS_TAC `SND:A#B->B` THEN ASM_REWRITE_TAC[GROUP_ISOMORPHISM_SND]) in
  GEN_REWRITE_TAC I [CONJ_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ISOMORPHIC_GROUP_PROD_GROUP_SWAP_LEFT] THEN
  REWRITE_TAC[lemma]);;

let ISOMORPHIC_GROUP_PRODUCT_GROUP,ISOMORPHIC_GROUP_SUM_GROUP =
 (CONJ_PAIR o prove)
 (`(!(G:K->A group) (H:K->B group) k.
        (!i. i IN k ==> (G i) isomorphic_group (H i))
        ==> (product_group k G) isomorphic_group (product_group k H)) /\
   (!(G:K->A group) (H:K->B group) k.
        (!i. i IN k ==> (G i) isomorphic_group (H i))
        ==> (sum_group k G) isomorphic_group (sum_group k H))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; group_isomorphisms] THEN
  MAP_EVERY X_GEN_TAC [`f:K->A->B`; `g:K->B->A`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(MESON[]
   `(!x y. Q x y ==> S x y) /\ (?x y. Q x y /\ P x y /\ (P x y ==> R x y))
    ==> (?x y. P x y /\ Q x y ) /\ (?x y. R x y /\ S x y)`) THEN
  REWRITE_TAC[sum_group] THEN CONJ_TAC THENL
   [MESON_TAC[REWRITE_RULE[SUBSET] GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x. RESTRICTION k (\i. (f:K->A->B) i (x i))`;
    `\y. RESTRICTION k (\i. (g:K->B->A) i (y i))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN
    SIMP_TAC[PRODUCT_GROUP; RESTRICTION; cartesian_product;
             IN_ELIM_THM; EXTENSIONAL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM; PRODUCT_GROUP;
                cartesian_product; IN_ELIM_THM; EXTENSIONAL;
                SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [group_homomorphism]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PRODUCT_GROUP] THEN
  DISCH_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[IMP_CONJ_ALT] GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `i:K` THEN
  ASM_CASES_TAC `(i:K) IN k` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[RESTRICTION] THEN RULE_ASSUM_TAC(REWRITE_RULE
   [group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM SET_TAC[]);;

let ISOMORPHIC_PRODUCT_GROUP_DISJOINT_UNION = prove
 (`!(f:K->A group) k l.
        DISJOINT k l
        ==> product_group (k UNION l) f isomorphic_group
            prod_group (product_group k f) (product_group l f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_group; group_isomorphism] THEN
  REWRITE_TAC[GROUP_ISOMORPHISMS] THEN
  EXISTS_TAC `\(f:K->A). RESTRICTION k f,RESTRICTION l f` THEN
  EXISTS_TAC `\((f:K->A),g) x. if x IN k then f x else g x` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRED;
                GROUP_HOMOMORPHISM_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION; GROUP_HOMOMORPHISM_PRODUCT_PROJECTION; IN_UNION];
    REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    SIMP_TAC[RESTRICTION_UNIQUE; IN_CARTESIAN_PRODUCT; PRODUCT_GROUP] THEN
    REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN ASM SET_TAC[]]);;

let ISOMORPHIC_GROUP_CARD_EQ = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H ==> group_carrier G =_c group_carrier H`,
  REWRITE_TAC[isomorphic_group; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[CARD_EQ_GROUP_ISOMORPHIC_IMAGE]);;

let ISOMORPHIC_GROUP_FINITENESS = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H
        ==> (FINITE(group_carrier G) <=> FINITE(group_carrier H))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_CARD_EQ) THEN
  REWRITE_TAC[CARD_FINITE_CONG]);;

let ISOMORPHIC_GROUP_INFINITENESS = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H
        ==> (INFINITE(group_carrier G) <=> INFINITE(group_carrier H))`,
  REWRITE_TAC[INFINITE; TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN
  REWRITE_TAC[ISOMORPHIC_GROUP_FINITENESS]);;

let ISOMORPHIC_GROUP_HAS_ORDER = prove
 (`!(G:A group) (H:B group) n.
        G isomorphic_group H
        ==> (group_carrier G HAS_SIZE n <=> group_carrier H HAS_SIZE n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_CARD_EQ) THEN
  MESON_TAC[CARD_HAS_SIZE_CONG]);;

let ISOMORPHIC_GROUP_ORDER = prove
 (`!(G:A group) (H:B group) n.
        G isomorphic_group H /\
        (FINITE(group_carrier G) \/ FINITE(group_carrier H))
        ==> CARD(group_carrier G) = CARD(group_carrier H)`,
  MESON_TAC[ISOMORPHIC_GROUP_HAS_ORDER; HAS_SIZE;
            ISOMORPHIC_GROUP_FINITENESS]);;

let ISOMORPHIC_GROUP_ABELIANNESS = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H ==> (abelian_group G <=> abelian_group H)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABELIAN_GROUP_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[isomorphic_group; ISOMORPHIC_GROUP_SYM;
                GROUP_MONOMORPHISM_EPIMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Perform group operations setwise.                                         *)
(* ------------------------------------------------------------------------- *)

let group_setinv = new_definition
 `group_setinv G g = {group_inv G x | x IN g}`;;

let group_setmul = new_definition
 `group_setmul G g h = {group_mul G x y | x IN g /\ y IN h}`;;

let GROUP_SETINV_AS_IMAGE = prove
 (`!G:A group. group_setinv G = IMAGE (group_inv G)`,
  REWRITE_TAC[FUN_EQ_THM; group_setinv; SIMPLE_IMAGE; ETA_AX]);;

let SUBGROUP_OF_SETWISE = prove
 (`!G s:A->bool.
        s subgroup_of G <=>
        s SUBSET group_carrier G /\
        group_id G IN s /\
        group_setinv G s SUBSET s /\
        group_setmul G s s SUBSET s`,
  REWRITE_TAC[subgroup_of; group_setinv; group_setmul] THEN SET_TAC[]);;

let OPPOSITE_GROUP_SETINV = prove
 (`!G s:A->bool.
        group_setinv (opposite_group G) s = group_setinv G s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_setinv; OPPOSITE_GROUP]);;

let OPPOSITE_GROUP_SETMUL = prove
 (`!G s t:A->bool.
        group_setmul (opposite_group G) s t = group_setmul G t s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_setmul; OPPOSITE_GROUP] THEN
  SET_TAC[]);;

let GROUP_SETINV_EQ_EMPTY = prove
 (`!G g:A->bool. group_setinv G g = {} <=> g = {}`,
  REWRITE_TAC[group_setinv] THEN SET_TAC[]);;

let GROUP_SETMUL_EQ_EMPTY = prove
 (`!G g h:A->bool. group_setmul G g h = {} <=> g = {} \/ h = {}`,
  REWRITE_TAC[group_setmul] THEN SET_TAC[]);;

let GROUP_SETMUL_EMPTY = prove
 (`(!G s:A->bool. group_setmul G s {} = {}) /\
   (!G t:A->bool. group_setmul G {} t = {})`,
  REWRITE_TAC[GROUP_SETMUL_EQ_EMPTY]);;

let GROUP_SETINV_MONO = prove
 (`!G s s':A->bool.
        s SUBSET s' ==> group_setinv G s SUBSET group_setinv G s'`,
  REWRITE_TAC[group_setinv] THEN SET_TAC[]);;

let GROUP_SETMUL_MONO = prove
 (`!G s t s' t':A->bool.
        s SUBSET s' /\ t SUBSET t'
        ==> group_setmul G s t SUBSET group_setmul G s' t'`,
  REWRITE_TAC[group_setmul] THEN SET_TAC[]);;

let GROUP_SETMUL_INC_GEN = prove
 (`(!G s t:A->bool.
        group_id G IN s /\ t SUBSET group_carrier G
        ==> t SUBSET group_setmul G s t) /\
   (!G s t:A->bool.
        s SUBSET group_carrier G /\ group_id G IN t
        ==> s SUBSET group_setmul G s t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_setmul; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`group_id G:A`; `x:A`];
    MAP_EVERY EXISTS_TAC [`x:A`; `group_id G:A`]] THEN
  ASM_MESON_TAC[SUBSET; GROUP_MUL_LID; GROUP_MUL_RID]);;

let GROUP_SETMUL_INC = prove
 (`(!G s t:A->bool.
        s subgroup_of G /\ t subgroup_of G ==> t SUBSET group_setmul G s t) /\
   (!G s t:A->bool.
        s subgroup_of G /\ t subgroup_of G ==> s SUBSET group_setmul G s t)`,
  MESON_TAC[GROUP_SETMUL_INC_GEN; subgroup_of]);;

let FINITE_GROUP_SETMUL = prove
 (`!G s t:A->bool.
        FINITE s /\ FINITE t ==> FINITE(group_setmul G s t)`,
  SIMP_TAC[group_setmul; FINITE_PRODUCT_DEPENDENT]);;

let GROUP_SETMUL_SYM_ELEMENTWISE = prove
 (`!G s t u:A->bool.
        (!a. a IN s ==> group_setmul G {a} t = group_setmul G u {a})
        ==> group_setmul G s t = group_setmul G u s`,
  REWRITE_TAC[group_setmul] THEN SET_TAC[]);;

let GROUP_SETINV_SING = prove
 (`!G x:A. group_setinv G {x} = {group_inv G x}`,
  REWRITE_TAC[group_setinv] THEN SET_TAC[]);;

let GROUP_SETMUL_SING = prove
 (`!G x y:A. group_setmul G {x} {y} = {group_mul G x y}`,
  REWRITE_TAC[group_setmul] THEN SET_TAC[]);;

let GROUP_SETINV = prove
 (`!G g:A->bool.
        g SUBSET group_carrier G ==> group_setinv G g SUBSET group_carrier G`,
  SIMP_TAC[group_setinv; SUBSET; FORALL_IN_GSPEC; GROUP_INV]);;

let GROUP_SETMUL = prove
 (`!G g h:A->bool.
        g SUBSET group_carrier G /\ h SUBSET group_carrier G==>
        group_setmul G g h SUBSET group_carrier G`,
  SIMP_TAC[group_setmul; SUBSET; FORALL_IN_GSPEC; GROUP_MUL]);;

let GROUP_SETMUL_LID = prove
 (`!G g:A->bool.
        g SUBSET group_carrier G ==> group_setmul G {group_id G} g = g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_setmul] THEN MATCH_MP_TAC(SET_RULE
   `(!y. y IN s ==> f a y = y) ==> {f x y | x IN {a} /\ y IN s} = s`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[GROUP_MUL_LID]);;

let GROUP_SETMUL_RID = prove
 (`!G g:A->bool.
        g SUBSET group_carrier G ==> group_setmul G g {group_id G} = g`,
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETMUL] THEN
  MESON_TAC[GROUP_SETMUL_LID; OPPOSITE_GROUP]);;

let GROUP_SETMUL_ASSOC = prove
 (`!G g h i:A->bool.
        g SUBSET group_carrier G /\ h SUBSET group_carrier G /\
        i SUBSET group_carrier G
        ==> group_setmul G g (group_setmul G h i) =
            group_setmul G (group_setmul G g h) i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_setmul] THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN s /\ y IN {g w z | w IN t /\ z IN u}} =
    {f x (g y z) | x IN s /\ y IN t /\ z IN u}`] THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN {g w z | w IN s /\ z IN t} /\ y IN u} =
    {f (g x y) z | x IN s /\ y IN t /\ z IN u}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y z. P x y z ==> f x y z = g x y z)
    ==> {f x y z | P x y z} = {g x y z | P x y z}`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_MUL_ASSOC THEN
  ASM SET_TAC[]);;

let GROUP_SETMUL_SYM = prove
 (`!G g h:A->bool.
        abelian_group G /\ g SUBSET group_carrier G /\ h SUBSET group_carrier G
        ==> group_setmul G g h = group_setmul G h g`,
  REWRITE_TAC[abelian_group; group_setmul] THEN SET_TAC[]);;

let GROUP_SETINV_SUBGROUP = prove
 (`!G h:A->bool. h subgroup_of G ==> group_setinv G h = h`,
  REWRITE_TAC[group_setinv; subgroup_of; SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x IN s /\ f(f x) = x) ==> {f x | x IN s} = s`) THEN
  ASM_SIMP_TAC[GROUP_INV_INV]);;

let GROUP_SETMUL_LSUBSET = prove
 (`!G h s:A->bool.
        h subgroup_of G /\ s SUBSET h /\ ~(s = {}) ==> group_setmul G s h = h`,
  REWRITE_TAC[group_setmul; subgroup_of; SUBSET] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; GROUP_MUL; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MAP_EVERY EXISTS_TAC [`y:A`; `group_mul G (group_inv G y) x:A`] THEN
  ASM_SIMP_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_MUL_ASSOC o rand o snd) THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GROUP_MUL_RINV; GROUP_MUL_LID]);;

let GROUP_SETMUL_RSUBSET = prove
 (`!G h s:A->bool.
        h subgroup_of G /\ s SUBSET h /\ ~(s = {}) ==> group_setmul G h s = h`,
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETMUL] THEN
  SIMP_TAC[GROUP_SETMUL_LSUBSET; SUBGROUP_OF_OPPOSITE_GROUP; OPPOSITE_GROUP]);;

let GROUP_SETMUL_LSUBSET_EQ = prove
 (`!G h s:A->bool.
        h subgroup_of G /\ s SUBSET group_carrier G
        ==> (group_setmul G s h = h <=> s SUBSET h /\ ~(s = {}))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_MESON_TAC[GROUP_SETMUL_EQ_EMPTY; SUBGROUP_OF_IMP_NONEMPTY];
    ASM_REWRITE_TAC[]] THEN
  EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[GROUP_SETMUL_LSUBSET]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[group_setmul; IN_ELIM_THM; SUBSET] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `group_id G:A`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
  ASM_SIMP_TAC[GROUP_MUL_RID]);;

let GROUP_SETMUL_RSUBSET_EQ = prove
 (`!G h s:A->bool.
        h subgroup_of G /\ s SUBSET group_carrier G
        ==> (group_setmul G h s = h <=> s SUBSET h /\ ~(s = {}))`,
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETMUL] THEN
  SIMP_TAC[GROUP_SETMUL_LSUBSET_EQ; SUBGROUP_OF_OPPOSITE_GROUP;
           OPPOSITE_GROUP]);;

let IMAGE_GROUP_CONJUGATION = prove
 (`!G (a:A) s.
        IMAGE (group_conjugation G a) s =
        group_setmul G {a} (group_setmul G s {group_inv G a})`,
  REWRITE_TAC[group_conjugation; group_setmul; IMAGE] THEN SET_TAC[]);;

let IMAGE_GROUP_CONJUGATION_EQ = prove
 (`!G (a:A) s t.
        a IN group_carrier G /\
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G
        ==> (IMAGE (group_conjugation G a) s = t <=>
             group_setmul G {a} s = group_setmul G t {a})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_GROUP_CONJUGATION] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `\s. group_setmul G s {a:A}`);
    DISCH_THEN(MP_TAC o AP_TERM `\s. group_setmul G s {group_inv G a:A}`)] THEN
  ASM_SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_SETMUL; GROUP_INV;
   GROUP_SETMUL_SING; GROUP_MUL_LINV; GROUP_MUL_RINV; GROUP_SETMUL_RID]);;

let GROUP_SETMUL_SUBGROUP = prove
 (`!G h:A->bool.
        h subgroup_of G ==> group_setmul G h h = h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_SETMUL_LSUBSET THEN
  ASM_MESON_TAC[SUBGROUP_OF_IMP_NONEMPTY; SUBSET_REFL]);;

let GROUP_SETMUL_LCANCEL = prove
 (`!G g h x:A.
        x IN group_carrier G /\
        g SUBSET group_carrier G /\ h SUBSET group_carrier G
        ==> (group_setmul G {x} g = group_setmul G {x} h <=> g = h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `group_setmul G {group_inv G x:A}`) THEN
  ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_INV] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_SING; GROUP_MUL_LINV; GROUP_SETMUL_LID]);;

let GROUP_SETMUL_RCANCEL = prove
 (`!G g h x:A.
        x IN group_carrier G /\ g SUBSET group_carrier G /\
        h SUBSET group_carrier G
        ==> (group_setmul G g {x} = group_setmul G h {x} <=> g = h)`,
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETMUL] THEN
  SIMP_TAC[GROUP_SETMUL_LCANCEL; OPPOSITE_GROUP]);;

let GROUP_SETMUL_LCANCEL_SET = prove
 (`!G h x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ h subgroup_of G
        ==> (group_setmul G h {x} = group_setmul G h {y} <=>
             group_div G x y IN h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  TRANS_TAC EQ_TRANS
   `group_setmul G (group_setmul G h {x}) {group_inv G y}  =
    group_setmul G (group_setmul G h {y:A}) {group_inv G y}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_SETMUL_RCANCEL THEN
    ASM_SIMP_TAC[GROUP_INV; GROUP_SETMUL; SING_SUBSET];
    ASM_SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; GROUP_INV; SING_SUBSET] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_SING; GROUP_MUL_RINV; GROUP_SETMUL_RID] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_RSUBSET_EQ; SING_SUBSET; group_div;
                 GROUP_INV; GROUP_MUL; NOT_INSERT_EMPTY]]);;

let GROUP_SETMUL_RCANCEL_SET = prove
 (`!G h x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\ h subgroup_of G
        ==> (group_setmul G {x} h = group_setmul G {y} h <=>
             group_mul G (group_inv G x) y IN h)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETMUL] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_LCANCEL_SET; OPPOSITE_GROUP;
               SUBGROUP_OF_OPPOSITE_GROUP; group_div]);;

let SUBGROUP_SETMUL_EQ = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> ((group_setmul G g h) subgroup_of G <=>
             group_setmul G g h = group_setmul G h g)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; group_setmul; FORALL_IN_GSPEC] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THENL
     [DISCH_THEN(MP_TAC o SPEC `group_mul G x y:A`) THEN
      REWRITE_TAC[group_setmul; IN_ELIM_THM] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
      MAP_EVERY X_GEN_TAC [`w:A`; `z:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `group_inv (G:A group)`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
      ASM_SIMP_TAC[GROUP_INV_INV; GROUP_MUL] THEN
      ASM_SIMP_TAC[GROUP_INV_MUL] THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC
       `group_mul G (group_inv G y) (group_inv G x):A`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
      REWRITE_TAC[group_setmul; IN_ELIM_THM] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
      ASM_SIMP_TAC[GROUP_INV_MUL; GROUP_INV; GROUP_MUL; GROUP_INV_INV] THEN
      ASM_MESON_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[SUBGROUP_OF_SETWISE] THEN
    ASM_SIMP_TAC[GROUP_SETMUL; SUBGROUP_OF_IMP_SUBSET] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[group_setmul; group_setinv; SUBSET; IMP_CONJ;
                  RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
      ASM_SIMP_TAC[GROUP_INV_MUL; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[GROUP_MUL_LID]; ALL_TAC] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP(SET_RULE
       `s = t ==> !x. x IN s ==> x IN t`)) THEN
      REWRITE_TAC[group_setmul; FORALL_IN_GSPEC] THEN
      DISCH_THEN(MP_TAC o SPECL [`group_inv G x:A`; `group_inv G y:A`]) THEN
      ASM SET_TAC[];
      TRANS_TAC SUBSET_TRANS
       `group_setmul G (group_setmul G h g) (group_setmul G g h):A->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
      TRANS_TAC SUBSET_TRANS
       `group_setmul G h (group_setmul G g (group_setmul G g h)):A->bool` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[GROUP_SETMUL_ASSOC; subgroup_of; GROUP_SETMUL;
                      SUBSET_REFL];
        ALL_TAC] THEN
      TRANS_TAC SUBSET_TRANS
       `group_setmul G h (group_setmul G (group_setmul G g g) h):A->bool` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[GROUP_SETMUL_ASSOC; subgroup_of; GROUP_SETMUL;
                      SUBSET_REFL];
        ALL_TAC] THEN
      ASM_SIMP_TAC[GROUP_SETMUL_SUBGROUP] THEN
      ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; SUBGROUP_OF_IMP_SUBSET] THEN
      ASM_SIMP_TAC[GROUP_SETMUL_SUBGROUP; SUBSET_REFL]]]);;

let SUBGROUP_SETMUL = prove
 (`!G g h:A->bool.
        abelian_group G /\ g subgroup_of G /\ h subgroup_of G
        ==> (group_setmul G g h) subgroup_of G`,
  MESON_TAC[GROUP_SETMUL_SYM; SUBGROUP_SETMUL_EQ; subgroup_of]);;

let SUBGROUP_GENERATED_SETMUL = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> subgroup_generated G (group_setmul G g h) =
            subgroup_generated G (g UNION h)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN
  REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[SUBSET; group_setmul; FORALL_IN_GSPEC; FORALL_IN_UNION] THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[SUBGROUP_GENERATED; GROUP_MUL]
     `x IN group_carrier(subgroup_generated G s) /\
      y IN group_carrier(subgroup_generated G s)
      ==> group_mul G x y IN group_carrier(subgroup_generated G s)`) THEN
    CONJ_TAC;
    REPEAT STRIP_TAC] THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_INC THEN
  ASM_SIMP_TAC[UNION_SUBSET; IN_UNION; SUBGROUP_OF_IMP_SUBSET] THEN
  ASM_SIMP_TAC[GSYM group_setmul; GROUP_SETMUL; SUBGROUP_OF_IMP_SUBSET] THEN
  REWRITE_TAC[group_setmul; IN_ELIM_THM] THEN
  ASM_MESON_TAC[GROUP_MUL_LID; GROUP_MUL_RID; subgroup_of; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Group actions.                                                            *)
(* ------------------------------------------------------------------------- *)

let group_action = new_definition
 `group_action G s (a:A->X->X) <=>
        (!g x. g IN group_carrier G /\ x IN s ==> a g x IN s) /\
        (!x. x IN s ==> a (group_id G) x = x) /\
        (!g h x. g IN group_carrier G /\ h IN group_carrier G /\ x IN s
                 ==> a (group_mul G g h) x = a g (a h x))`;;

let GROUP_ACTION_ALT = prove
 (`!G s (a:A->X->X).
        group_action G s (a:A->X->X) <=>
        (!g x. g IN group_carrier G /\ x IN s ==> a g x IN s) /\
        (!x. x IN s ==> a (group_id G) x = x) /\
        (!g h x. g IN group_carrier G /\ h IN group_carrier G /\ x IN s
                 ==> a g (a h x) = a (group_mul G g h) x)`,
  REWRITE_TAC[group_action] THEN MESON_TAC[]);;

let GROUP_ACTION_MUL = prove
 (`!G s (a:A->X->X) g h x.
        group_action G s a /\
        g IN group_carrier G /\
        h IN group_carrier G /\
        x IN s
        ==> a g (a h x) = a (group_mul G g h) x`,
  SIMP_TAC[group_action]);;

let GROUP_ACTION_LINV = prove
 (`!G s (a:A->X->X) g x.
        group_action G s a /\ g IN group_carrier G /\ x IN s
        ==> a (group_inv G g) (a g x) = x`,
  REWRITE_TAC[group_action] THEN MESON_TAC[GROUP_MUL_LINV; GROUP_INV]);;

let GROUP_ACTION_RINV = prove
 (`!G s (a:A->X->X) g x.
        group_action G s a /\ g IN group_carrier G /\ x IN s
        ==> a g (a (group_inv G g) x) = x`,
  REWRITE_TAC[group_action] THEN MESON_TAC[GROUP_MUL_RINV; GROUP_INV]);;

let GROUP_ACTION_BIJECTIVE = prove
 (`!G s (a:A->X->X) g.
        group_action G s a /\ g IN group_carrier G
        ==> !y. y IN s ==> ?!x. x IN s /\ a g x = y`,
  MESON_TAC[GROUP_ACTION_LINV; GROUP_INV; GROUP_INV_INV; group_action]);;

let GROUP_ACTION_SURJECTIVE = prove
 (`!G s (a:A->X->X) g y.
        group_action G s a /\ g IN group_carrier G /\ y IN s
        ==> ?x. a g x = y`,
  MESON_TAC[GROUP_ACTION_BIJECTIVE]);;

let GROUP_ACTION_INJECTIVE = prove
 (`!G s (a:A->X->X).
        group_action G s a /\ g IN group_carrier G /\ x IN s /\ y IN s
        ==> (a g x = a g y <=> x = y)`,
  MESON_TAC[GROUP_ACTION_BIJECTIVE; group_action]);;

let GROUP_ACTION_ON_SUBSET = prove
 (`!G s t (a:A->X->X).
        group_action G s a /\
        t SUBSET s /\
        (!g x. g IN group_carrier G /\ x IN t ==> a g x IN t)
        ==> group_action G t a`,
  REWRITE_TAC[group_action] THEN SET_TAC[]);;

let GROUP_ACTION_FROM_SUBGROUP = prove
 (`!G s h (a:A->X->X).
        group_action G s a ==> group_action (subgroup_generated G h) s a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_action] THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`]
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED] THEN SET_TAC[]);;

let GROUP_ACTION_IMAGE = prove
 (`!G u s (a:A->X->X).
        group_action G s a /\
        (!t. t IN u ==> t SUBSET s) /\
        (!g t. g IN group_carrier G /\ t IN u ==> IMAGE (a g) t IN u)
        ==> group_action G u (IMAGE o a)`,
  REWRITE_TAC[group_action; o_DEF] THEN SET_TAC[]);;

let GROUP_ACTION_IMAGE_SIZED = prove
 (`!G s k (a:A->X->X).
        group_action G s a
        ==> group_action G {t | t SUBSET s /\ t HAS_SIZE k} (IMAGE o a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ACTION_IMAGE THEN
  EXISTS_TAC `s:X->bool` THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:A`; `t:X->bool`] THEN STRIP_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[group_action]) THEN ASM SET_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_MESON_TAC[GROUP_ACTION_INJECTIVE; SUBSET]]);;

let group_stabilizer = new_definition
 `group_stabilizer G (a:A->X->X) x = {g | g IN group_carrier G /\ a g x = x}`;;

let GROUP_STABILIZER_SUBSET_CARRIER = prove
 (`!G a x. group_stabilizer G a x SUBSET group_carrier G`,
  REWRITE_TAC[group_stabilizer; SUBSET_RESTRICT]);;

let FINITE_GROUP_STABILIZER = prove
 (`!G (a:A->X->X) x.
        FINITE(group_carrier G) ==> FINITE(group_stabilizer G a x)`,
  MESON_TAC[GROUP_STABILIZER_SUBSET_CARRIER; FINITE_SUBSET]);;

let SUBGROUP_OF_GROUP_STABILIZER = prove
 (`!G s (a:A->X->X) x.
        group_action G s a /\ x IN s ==> group_stabilizer G a x subgroup_of G`,
  REWRITE_TAC[subgroup_of; group_stabilizer; SUBSET_RESTRICT] THEN
  SIMP_TAC[group_action; IN_ELIM_THM; GROUP_ID; GROUP_INV; GROUP_MUL] THEN
  ASM_MESON_TAC[GROUP_MUL_LINV; GROUP_INV]);;

let GROUP_STABILIZER_NONEMPTY = prove
 (`!G (a:A->X->X) s x.
        group_action G s a /\ x IN s ==> ~(group_stabilizer G a x = {})`,
  REWRITE_TAC[group_action; GSYM MEMBER_NOT_EMPTY] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `group_id G:A` THEN
  ASM_SIMP_TAC[group_stabilizer; IN_ELIM_THM; GROUP_ID]);;

let GROUP_STABILIZER_SUBGROUP_GENERATED = prove
 (`!G h (a:A->X->X) x.
        group_stabilizer (subgroup_generated G h) a x =
        group_carrier(subgroup_generated G h) INTER group_stabilizer G a x`,
  REWRITE_TAC[group_stabilizer; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET]);;

let GROUP_STABILIZER_ON_SUBGROUP = prove
 (`!G h (a:A->X->X) x.
        h subgroup_of G
        ==> group_stabilizer (subgroup_generated G h) a x =
            h INTER group_stabilizer G a x`,
  SIMP_TAC[GROUP_STABILIZER_SUBGROUP_GENERATED;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP]);;

let GROUP_ACTION_KERNEL_POINTWISE = prove
 (`!G s (a:A->X->X).
        {g | g IN group_carrier G /\ !x. x IN s ==> a g x = x} =
        if s = {} then group_carrier G
        else INTERS {group_stabilizer G a x | x IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERS_GSPEC; group_stabilizer] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let GROUP_ACTION_EQ = prove
 (`!G s (a:A->X->X) g h x.
        group_action G s a /\
        g IN group_carrier G /\ h IN group_carrier G /\
        x IN s
        ==> (a g x = a h x <=>
             group_mul G (group_inv G g) h IN group_stabilizer G a x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_stabilizer; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(a:A->X->X) (group_inv G g)`);
    DISCH_THEN(MP_TAC o AP_TERM `(a:A->X->X) g`)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GROUP_ACTION_ALT]) THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GROUP_MUL_LINV; GROUP_MUL_ASSOC;
               GROUP_MUL_RINV; GROUP_MUL_LID] THEN
  MESON_TAC[]);;

let GROUP_ACTION_FIBRES = prove
 (`!G s (a:A->X->X) h x.
        group_action G s a /\ h IN group_carrier G /\ x IN s
        ==> {g | g IN group_carrier G /\ (a:A->X->X) g x = a h x} =
            IMAGE (group_mul G h) (group_stabilizer G a x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `!g. (!x. x IN u ==> (P x <=> g x IN t)) /\ t SUBSET u /\
        (!y. y IN u ==> f y IN u /\ g(f y) = y /\ f(g y) = y)
        ==> {x | x IN u /\ P x} = IMAGE f t`) THEN
  EXISTS_TAC `group_mul G (group_inv G h:A)` THEN
  REWRITE_TAC[GROUP_STABILIZER_SUBSET_CARRIER] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[GROUP_ACTION_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_MUL_LINV; GROUP_MUL_RINV; GROUP_MUL_ASSOC;
               GROUP_MUL; GROUP_INV; GROUP_MUL_LID]);;

let group_orbit = new_definition
 `group_orbit G s (a:A->X->X) x y <=>
        x IN s /\ y IN s /\ ?g. g IN group_carrier G /\ a g x = y`;;

let GROUP_ORBIT_IN_SET = prove
 (`!G s (a:A->X->X) x y.
        group_orbit G s a x y ==> x IN s /\ y IN s`,
  SIMP_TAC[group_orbit]);;

let IN_GROUP_ORBIT = prove
 (`!G s (a:A->X->X) x y.
        y IN group_orbit G s a x <=>
        x IN s /\ y IN s /\ ?g. g IN group_carrier G /\ a g x = y`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  REWRITE_TAC[group_orbit]);;

let GROUP_ORBIT = prove
 (`!G s (a:A->X->X) x.
        group_action G s a
        ==> group_orbit G s a x =
            if x IN s then {a g x | g IN group_carrier G} else {}`,
  REWRITE_TAC[group_action] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ONCE_REWRITE_TAC[EXTENSION] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  ASM_REWRITE_TAC[group_orbit; IN_ELIM_THM] THEN ASM SET_TAC[]);;

let GROUP_ORBIT_SUBSET = prove
 (`!G s (a:A->X->X) x. group_orbit G s a x SUBSET s`,
  REWRITE_TAC[SET_RULE `s SUBSET t <=> !x. s x ==> x IN t`] THEN
  REWRITE_TAC[group_orbit] THEN SET_TAC[]);;

let GROUP_ORBIT_ON_SUBSET = prove
 (`!G s t (a:A->X->X).
        t SUBSET s /\ x IN t
        ==> group_orbit G t a x = t INTER group_orbit G s a x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `u = t INTER v <=> !x. u x <=> x IN t /\ v x`] THEN
  REWRITE_TAC[group_orbit] THEN ASM SET_TAC[]);;

let FINITE_GROUP_ORBIT = prove
 (`!G s (a:A->X->X) x.
        FINITE(group_carrier G) \/ FINITE s ==> FINITE(group_orbit G s a x)`,
  REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[GROUP_ORBIT_SUBSET; FINITE_SUBSET]] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\g. (a:A->X->X) g x) (group_carrier G)` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SET_RULE `P SUBSET s <=> !x. P x ==> x IN s`] THEN
  REWRITE_TAC[IN_IMAGE; group_orbit] THEN SET_TAC[]);;

let GROUP_ORBIT_REFL_EQ = prove
 (`!G s (a:A->X->X) x.
        group_action G s a ==> (group_orbit G s a x x <=> x IN s)`,
  REWRITE_TAC[group_action; group_orbit] THEN MESON_TAC[GROUP_ID]);;

let GROUP_ORBIT_REFL = prove
 (`!G s (a:A->X->X) x.
        group_action G s a /\ x IN s
        ==> group_orbit G s a x x`,
  MESON_TAC[GROUP_ORBIT_REFL_EQ]);;

let IN_GROUP_ORBIT_SELF = prove
 (`!G s (a:A->X->X) x.
        group_action G s a /\ x IN s ==> x IN group_orbit G s a x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN] THEN
  ASM_SIMP_TAC[GROUP_ORBIT_REFL]);;

let GROUP_ORBIT_EMPTY = prove
 (`!G s (a:A->X->X) x. ~(x IN s) ==> group_orbit G s a x = {}`,
  REWRITE_TAC[SET_RULE `s = {} <=> !x. ~s x`] THEN SIMP_TAC[group_orbit]);;

let GROUP_ORBIT_EQ_EMPTY = prove
 (`!G s (a:A->X->X) x.
        group_action G s a
        ==> (group_orbit G s a x = {} <=> ~(x IN s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[GROUP_ORBIT_EMPTY] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; IN_GROUP_ORBIT_SELF]);;

let GROUP_ORBIT_SYM_EQ = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a
        ==> (group_orbit G s a x y <=> group_orbit G s a y x)`,
  REWRITE_TAC[group_action; group_orbit] THEN
  ASM_MESON_TAC[GROUP_INV; GROUP_MUL_LINV]);;

let GROUP_ORBIT_SYM = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a /\ group_orbit G s a x y
        ==> group_orbit G s a y x`,
  MESON_TAC[GROUP_ORBIT_SYM_EQ]);;

let GROUP_ORBIT_TRANS = prove
 (`!G s (a:A->X->X) x y z.
        group_action G s a /\ group_orbit G s a x y /\ group_orbit G s a y z
        ==> group_orbit G s a x z`,
  REWRITE_TAC[group_action; group_orbit] THEN
  ASM_MESON_TAC[GROUP_MUL]);;

let GROUP_ORBIT_EQ = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a /\ x IN s /\ y IN s
        ==> (group_orbit G s a x = group_orbit G s a y <=>
             group_orbit G s a x y)`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[GROUP_ORBIT_REFL_EQ; GROUP_ORBIT_SYM_EQ; GROUP_ORBIT_TRANS]);;

let CLOSED_GROUP_ORBIT = prove
 (`!G s (a:A->X->X) x g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) (group_orbit G s a x) SUBSET group_orbit G s a x`,
  REWRITE_TAC[group_action] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[group_orbit] THEN ASM_MESON_TAC[GROUP_MUL]);;

let GROUP_ORBIT_EQ_SING = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a
        ==> (group_orbit G s a y = {x} <=>
             x IN s /\ y = x /\ !g. g IN group_carrier G ==> a g x = x)`,
  REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  ASM_SIMP_TAC[GROUP_ORBIT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  MP_TAC(ISPEC `G:A group` GROUP_ID) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_action]) THEN ASM SET_TAC[]);;

let GROUP_ORBIT_EQ_SING_SELF = prove
 (`!G s (a:A->X->X) x.
        group_action G s a
        ==> (group_orbit G s a x = {x} <=>
             x IN s /\ !g. g IN group_carrier G ==> a g x = x)`,
  SIMP_TAC[GROUP_ORBIT_EQ_SING]);;

let GROUP_ORBIT_HAS_SIZE_1 = prove
 (`!G s (a:A->X->X) x.
        group_action G s a
        ==> (group_orbit G s a x HAS_SIZE 1 <=>
             x IN s /\ !g. g IN group_carrier G ==> a g x = x)`,
  REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  ASM_SIMP_TAC[GROUP_ORBIT_EQ_SING] THEN SET_TAC[]);;

let GROUP_ACTION_INVARIANT_SUBSET = prove
 (`!G s (a:A->X->X) t.
        group_action G s a /\ t SUBSET s
        ==> ((!g. g IN group_carrier G ==> IMAGE (a g) t SUBSET t) <=>
             (!g. g IN group_carrier G ==> IMAGE (a g) t = t))`,
  REWRITE_TAC[GROUP_ACTION_ALT] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[SUBSET_REFL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!g. (!x. x IN s ==> f(g x) = x /\ g(f x) = x) /\
        IMAGE f s SUBSET s /\ IMAGE g s SUBSET s
        ==> IMAGE f s = s`) THEN
  EXISTS_TAC `(a:A->X->X) (group_inv G g)` THEN
  ASM_SIMP_TAC[GROUP_INV] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_MUL_LINV; GROUP_MUL_RINV]);;

let GROUP_ACTION_CLOSED = prove
 (`!G s (a:A->X->X) g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) s SUBSET s`,
  REWRITE_TAC[group_action] THEN SET_TAC[]);;

let GROUP_ACTION_INVARIANT = prove
 (`!G s (a:A->X->X) g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) s = s`,
  MESON_TAC[GROUP_ACTION_CLOSED; GROUP_ACTION_INVARIANT_SUBSET; SUBSET_REFL]);;

let INVARIANT_GROUP_ORBIT = prove
 (`!G s (a:A->X->X) x g.
        group_action G s a /\ g IN group_carrier G
        ==> IMAGE (a g) (group_orbit G s a x) = group_orbit G s a x`,
  MESON_TAC[GROUP_ACTION_INVARIANT_SUBSET; GROUP_ORBIT_SUBSET;
                CLOSED_GROUP_ORBIT]);;

let SUBSET_GROUP_ORBIT_CLOSED = prove
 (`!G s (a:A->X->X) x t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t SUBSET t)
        ==> (group_orbit G s a x SUBSET t <=>
             x IN s ==> ~DISJOINT (group_orbit G s a x) t)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:X) IN s` THEN
  ASM_SIMP_TAC[GROUP_ORBIT_EMPTY; EMPTY_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE
   `~(s = {}) /\ (~DISJOINT s t ==> s SUBSET t)
    ==> (s SUBSET t <=> ~DISJOINT s t)`) THEN
  ASM_SIMP_TAC[GROUP_ORBIT_EQ_EMPTY; LEFT_IMP_EXISTS_THM; SET_RULE
   `~DISJOINT s t <=> ?z. z IN t /\ s z`] THEN
  X_GEN_TAC `z:X` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  W(MP_TAC o PART_MATCH (rand o rand) GROUP_ORBIT_EQ o lhand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_CASES_TAC `(z:X) IN s` THENL [DISCH_THEN SUBST1_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[GROUP_ORBIT_EQ_EMPTY] THEN
  ASM_SIMP_TAC[GROUP_ORBIT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_action]) THEN ASM SET_TAC[]);;

let SUBSET_GROUP_ORBIT_INVARIANT = prove
 (`!G s (a:A->X->X) x t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t = t)
        ==> (group_orbit G s a x SUBSET t <=>
             x IN s ==> ~DISJOINT (group_orbit G s a x) t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_GROUP_ORBIT_CLOSED THEN
  ASM_SIMP_TAC[SUBSET_REFL]);;

let GROUP_ORBITS_EQ = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a /\ x IN s /\ y IN s
        ==> (group_orbit G s a x = group_orbit G s a y <=>
             ~DISJOINT (group_orbit G s a x) (group_orbit G s a y))`,
  SIMP_TAC[GROUP_ORBIT_EQ; SET_RULE `DISJOINT s t <=> !x. ~(s x /\ t x)`] THEN
  MESON_TAC[GROUP_ORBIT_REFL_EQ; GROUP_ORBIT_SYM_EQ; GROUP_ORBIT_TRANS]);;

let DISJOINT_GROUP_ORBITS = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a /\ x IN s /\ y IN s
        ==> (DISJOINT (group_orbit G s a x) (group_orbit G s a y) <=>
             ~(group_orbit G s a x = group_orbit G s a y))`,
  SIMP_TAC[GROUP_ORBITS_EQ]);;

let PAIRWISE_DISJOINT_GROUP_ORBITS = prove
 (`!G h:A->bool.
        group_action G s a
        ==> pairwise DISJOINT {group_orbit G s a x |x| x IN s}`,
  REWRITE_TAC[SIMPLE_IMAGE; PAIRWISE_IMAGE] THEN
  SIMP_TAC[pairwise; DISJOINT_GROUP_ORBITS]);;

let UNIONS_GROUP_ORBITS_CLOSED = prove
 (`!G s (a:A->X->X) t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t SUBSET t)
        ==> UNIONS {group_orbit G s a x |x| x IN t} = t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN t ==> x IN f x) /\
    (!x. x IN t /\ ~DISJOINT (f x) t ==> f x SUBSET t)
    ==> UNIONS {f x | x IN t} = t`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[IN_GROUP_ORBIT_SELF; SUBSET];
    ASM_MESON_TAC[SUBSET_GROUP_ORBIT_CLOSED; SUBSET]]);;

let UNIONS_GROUP_ORBITS_INVARIANT = prove
 (`!G s (a:A->X->X) t.
        group_action G s a /\ t SUBSET s /\
        (!g. g IN group_carrier G ==> IMAGE (a g) t = t)
        ==> UNIONS {group_orbit G s a x |x| x IN t} = t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC UNIONS_GROUP_ORBITS_CLOSED THEN
  ASM_SIMP_TAC[UNIONS_GROUP_ORBITS_CLOSED; SUBSET_REFL]);;

let UNIONS_GROUP_ORBITS = prove
 (`!G s (a:A->X->X).
        group_action G s a
        ==> UNIONS {group_orbit G s a x |x| x IN s} = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC UNIONS_GROUP_ORBITS_INVARIANT THEN
  ASM_MESON_TAC[GROUP_ACTION_INVARIANT; SUBSET_REFL]);;

let NSUM_CARD_GROUP_ORBITS = prove
 (`!G s (a:A->X->X).
        group_action G s a /\ FINITE s
        ==> nsum {group_orbit G s a x | x | x IN s} CARD = CARD s`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  W(MP_TAC o PART_MATCH (rand o rand) CARD_UNIONS o rand o snd) THEN
  ASM_SIMP_TAC[UNIONS_GROUP_ORBITS; GSYM pairwise] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM DISJOINT; ETA_AX] THEN
  ASM_SIMP_TAC[PAIRWISE_DISJOINT_GROUP_ORBITS] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_GROUP_ORBIT]);;

let ORBIT_STABILIZER_MUL_GEN = prove
 (`!G s (a:A->X->X) x.
      group_action G s a /\ x IN s
      ==> group_orbit G s a x *_c group_stabilizer G a x =_c group_carrier G`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_ORBIT; SIMPLE_IMAGE] THEN
  MATCH_MP_TAC CARD_EQ_IMAGE_MUL_FIBRES THEN
  X_GEN_TAC `g:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] GROUP_ACTION_FIBRES)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC CARD_EQ_IMAGE THEN
  REWRITE_TAC[group_stabilizer; IN_ELIM_THM] THEN
  ASM_MESON_TAC[GROUP_MUL_LCANCEL_IMP]);;

let ORBIT_STABILIZER_MUL = prove
 (`!G s (a:A->X->X) x.
      FINITE(group_carrier G) /\ group_action G s a /\ x IN s
      ==> CARD(group_orbit G s a x) * CARD(group_stabilizer G a x) =
          CARD(group_carrier G)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORBIT_STABILIZER_MUL_GEN) THEN
  ASM_SIMP_TAC[FINITE_GROUP_STABILIZER; FINITE_GROUP_ORBIT; CARD_EQ_CARD;
                CARD_MUL_FINITE; CARD_MUL_C]);;

let CARD_GROUP_ORBIT_DIVIDES = prove
 (`!G s (a:A->X->X) x.
        FINITE(group_carrier G) /\ group_action G s a /\ x IN s
        ==> CARD(group_orbit G s a x) divides CARD(group_carrier G)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP ORBIT_STABILIZER_MUL) THEN
  CONV_TAC NUMBER_RULE);;

let CARD_GROUP_STABILIZER_DIVIDES = prove
 (`!G s (a:A->X->X) x.
        FINITE(group_carrier G) /\ group_action G s a /\ x IN s
        ==> CARD(group_stabilizer G a x) divides CARD(group_carrier G)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP ORBIT_STABILIZER_MUL) THEN
  CONV_TAC NUMBER_RULE);;

let GROUP_STABILIZER_OF_ACTION = prove
 (`!G s (a:A->X->X) g x.
        group_action G s a /\ g IN group_carrier G /\ x IN s
        ==> group_stabilizer G a (a g x) =
            IMAGE (group_conjugation G g) (group_stabilizer G a x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_stabilizer] THEN
  CONV_TAC SYM_CONV THEN
  ASM_SIMP_TAC[IMAGE_GROUP_CONJUGATION_EQ_PREIMAGE; SUBSET_RESTRICT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; group_conjugation] THEN
  X_GEN_TAC `h:A` THEN ASM_CASES_TAC `(h:A) IN group_carrier G` THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GROUP_ACTION_ALT]) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
      [GROUP_MUL; GROUP_INV] THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL; GROUP_INV;
               GROUP_MUL_LINV; GROUP_MUL_RID] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [group_action]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC GROUP_ACTION_INJECTIVE THEN
  ASM_MESON_TAC[group_action]);;

let GROUP_ACTION_SUBGROUP_TRANSLATION = prove
 (`!G (h:A->bool).
    group_action (subgroup_generated G h) (group_carrier G) (group_mul G)`,
  REWRITE_TAC[group_action; CONJUNCT2 SUBGROUP_GENERATED] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[SUBSET] GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET))) THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_MUL_LID; GROUP_MUL_ASSOC]);;

let GROUP_STABILIZER_SUBGROUP_TRANSLATION = prove
 (`!G h a:A.
        h subgroup_of G /\ a IN group_carrier G
        ==> group_stabilizer (subgroup_generated G h) (group_mul G) a =
            {group_id G}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[group_stabilizer; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  MATCH_MP_TAC(SET_RULE
   `a IN s /\ (!x. x IN s ==> (P x <=> x = a))
    ==> {x | x IN s /\ P x} = {a}`) THEN
  ASM_MESON_TAC[subgroup_of; SUBSET; GROUP_RULE
   `group_mul G g a = a <=> g = group_id G`]);;

let GROUP_ACTION_GROUP_TRANSLATION = prove
 (`!G. group_action G (group_carrier G) (group_mul G)`,
  MESON_TAC[GROUP_ACTION_SUBGROUP_TRANSLATION;
            SUBGROUP_GENERATED_GROUP_CARRIER]);;

let GROUP_STABILIZER_GROUP_TRANSLATION = prove
 (`!G a:A.
        a IN group_carrier G
        ==> group_stabilizer G (group_mul G) a = {group_id G}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `group_carrier G:A->bool`; `a:A`]
        GROUP_STABILIZER_SUBGROUP_TRANSLATION) THEN
  ASM_REWRITE_TAC[CARRIER_SUBGROUP_OF; SUBGROUP_GENERATED_GROUP_CARRIER]);;

let GROUP_ACTION_SUBSET_TRANSLATION = prove
 (`!(G:A group) u.
      (!s. s IN u ==> s SUBSET group_carrier G) /\
      (!a s. a IN group_carrier G /\ s IN u ==> IMAGE (group_mul G a) s IN u)
      ==> group_action G u (IMAGE o group_mul G)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ACTION_IMAGE THEN
  ASM_MESON_TAC[GROUP_ACTION_GROUP_TRANSLATION]);;

let GROUP_ACTION_CONJUGATION = prove
 (`!G:A group. group_action G (group_carrier G) (group_conjugation G)`,
  REWRITE_TAC[group_action] THEN
  SIMP_TAC[GROUP_CONJUGATION; GROUP_CONJUGATION_BY_ID;
           GSYM GROUP_CONJUGATION_CONJUGATION]);;

let CARD_GROUP_SETMUL_GEN = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_setmul G g h) *_c (g INTER h) =_c g *_c h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`prod_group (subgroup_generated G g) (subgroup_generated G h:A group)`;
    `group_setmul (G:A group) g h`;
    `\(x,y) (z:A). group_mul G x (group_mul G z (group_inv G y))`;
    `group_id G:A`]
   ORBIT_STABILIZER_MUL_GEN) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q ==> r) ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[group_action; PROD_GROUP; FORALL_PAIR_THM; IN_CROSS;
      CONJUNCT2 SUBGROUP_GENERATED; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[group_setmul; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x1:A` THEN DISCH_TAC THEN X_GEN_TAC `y1:A` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`x2:A`; `y2:A`] THEN STRIP_TAC THEN
      EXISTS_TAC `group_mul G x1 x2:A` THEN
      EXISTS_TAC `group_mul G y2 (group_inv G y1):A` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[subgroup_of]; ALL_TAC];
      ALL_TAC;
      ALL_TAC;
      REPEAT(EXISTS_TAC `group_id G:A`) THEN
      ASM_MESON_TAC[subgroup_of; SUBSET; GROUP_MUL_LID]] THEN
    REPEAT STRIP_TAC THEN GROUP_TAC THEN
    ASM_MESON_TAC[subgroup_of; SUBSET];
    STRIP_TAC THEN MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_EQ_CONG THEN
    ASM_SIMP_TAC[PROD_GROUP; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    REWRITE_TAC[CROSS; GSYM mul_c; CARD_EQ_REFL]] THEN
  MATCH_MP_TAC CARD_MUL_CONG THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_REFL_IMP THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[GROUP_ORBIT_SUBSET] THEN ASM_SIMP_TAC[GROUP_ORBIT] THEN
    REWRITE_TAC[SUBSET; group_setmul; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IN_ELIM_THM; PROD_GROUP; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 EXISTS_PAIR_THM; IN_CROSS] THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `group_inv G y:A`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[subgroup_of]; ALL_TAC] THEN
    GROUP_TAC THEN ASM_MESON_TAC[subgroup_of; SUBSET];
    TRANS_TAC CARD_EQ_TRANS `IMAGE (\x:A. x,x) (g INTER h)` THEN
    SIMP_TAC[CARD_EQ_IMAGE; FORALL_PAIR_THM; PAIR_EQ] THEN
    MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
    ASM_SIMP_TAC[IN_ELIM_THM; PROD_GROUP; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 group_stabilizer] THEN
    REWRITE_TAC[CROSS; SET_RULE
     `{z | z IN {x,y | P x y} /\ Q z} = {x,y | P x y /\ Q(x,y)}`] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_IMAGE; PAIR_EQ; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `(x:A) IN g` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:A) IN h` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    TRANS_TAC EQ_TRANS `y:A = x` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    GROUP_TAC THEN ASM_MESON_TAC[subgroup_of; SUBSET]]);;

let CARD_GROUP_SETMUL_MUL = prove
 (`!G g h:A->bool.
        FINITE g /\ FINITE h /\ g subgroup_of G /\ h subgroup_of G
        ==> CARD(group_setmul G g h) * CARD(g INTER h) = CARD g * CARD h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `g:A->bool`; `h:A->bool`]
        CARD_GROUP_SETMUL_GEN) THEN
  ASM_SIMP_TAC[CARD_EQ_CARD; FINITE_GROUP_SETMUL; FINITE_INTER;
               CARD_MUL_FINITE_EQ; CARD_MUL_C]);;

let CARD_GROUP_SETMUL = prove
 (`!G g h:A->bool.
        FINITE g /\ FINITE h /\ g subgroup_of G /\ h subgroup_of G
        ==> CARD(group_setmul G g h) = (CARD g * CARD h) DIV CARD(g INTER h)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `0` THEN ASM_SIMP_TAC[ADD_CLAUSES; CARD_GROUP_SETMUL_MUL] THEN
  MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 0 < n`) THEN
  ASM_SIMP_TAC[CARD_EQ_0; FINITE_INTER] THEN
  MATCH_MP_TAC SUBGROUP_OF_IMP_NONEMPTY THEN
  ASM_MESON_TAC[SUBGROUP_OF_INTER]);;

let CARD_GROUP_SETMUL_DIVIDES = prove
 (`!G g h:A->bool.
        FINITE g /\ FINITE h /\ g subgroup_of G /\ h subgroup_of G
        ==> CARD(group_setmul G g h) divides CARD(g) * CARD(h)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM CARD_GROUP_SETMUL_MUL] THEN
  CONV_TAC NUMBER_RULE);;

let GROUP_ORBIT_COMMON_DIVISOR = prove
 (`!G s (a:A->X->X) n.
        group_action G s a /\
        FINITE s /\
        (!x. x IN s ==> n divides CARD(group_orbit G s a x))
        ==> n divides CARD s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP UNIONS_GROUP_ORBITS) THEN
  W(MP_TAC o PART_MATCH(lhand o rand) CARD_UNIONS o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SIMPLE_IMAGE; IMAGE_EQ_EMPTY; IMP_CONJ;
               RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FINITE_GROUP_ORBIT;
               IMP_CONJ; GSYM DISJOINT; DISJOINT_GROUP_ORBITS] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC DIVIDES_NSUM THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE]);;

let GROUP_ORBIT_COMMON_INDEX = prove
 (`!G s (a:A->X->X) p k.
        group_action G s a /\
        FINITE s /\ (s = {} ==> k = 0) /\
        (!x. x IN s ==> k <= index p (CARD(group_orbit G s a x)))
        ==> k <= index p (CARD s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_INDEX] THEN
  SIMP_TAC[FINITE_GROUP_ORBIT; CARD_EQ_0; GROUP_ORBIT_EQ_EMPTY; IMP_CONJ] THEN
  ASM_CASES_TAC `s:X->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; CARD_CLAUSES; DIVIDES_0] THEN
  ASM_MESON_TAC[GROUP_ORBIT_COMMON_DIVISOR; MEMBER_NOT_EMPTY]);;

let PGROUP_ACTION_FIXPOINTS = prove
 (`!G s (a:A->X->X) p k.
        group_action G s a /\ FINITE s /\
        prime p /\ (group_carrier G) HAS_SIZE (p EXP k)
        ==> (CARD {x | x IN s /\ !g. g IN group_carrier G ==> a g x = x} ==
             CARD s) (mod p)`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM GROUP_ORBIT_HAS_SIZE_1] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!y:num. x = y /\ (y == z) (mod n) ==> (x == z) (mod n)`) THEN
  EXISTS_TAC
   `nsum {t | t IN {group_orbit G s (a:A->X->X) x | x | x IN s} /\
              t HAS_SIZE 1} (\i. 1)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_RESTRICT; NSUM_CONST; FINITE_IMAGE] THEN
    REWRITE_TAC[MULT_CLAUSES; SET_RULE
     `{y | y IN IMAGE f s /\ P y} = IMAGE f {x | x IN s /\ P(f x)}`] THEN
    ASM_SIMP_TAC[GROUP_ORBIT_HAS_SIZE_1; TAUT `p /\ p /\ q <=> p /\ q`] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[GSYM GROUP_ORBIT_HAS_SIZE_1] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_SIMP_TAC[GROUP_ORBIT_HAS_SIZE_1; FINITE_RESTRICT] THEN
    ASM_SIMP_TAC[GSYM GROUP_ORBIT_EQ_SING_SELF] THEN SET_TAC[];
    REWRITE_TAC[NSUM_RESTRICT_SET]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] NSUM_CARD_GROUP_ORBITS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CONG_NSUM THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:X` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_GROUP_ORBIT] THEN
  MP_TAC(ISPECL [`G:A group`; `s:X->bool`; `a:A->X->X`; `x:X`]
        CARD_GROUP_ORBIT_DIVIDES) THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NUMBER_RULE `(n:num == n) (mod p)`] THEN
  REWRITE_TAC[NUMBER_RULE `(0 == n) (mod p) <=> p divides n`] THEN
  ASM_SIMP_TAC[PRIME_DIVEXP_EQ; DIVIDES_REFL] THEN ASM_MESON_TAC[EXP]);;

let PGROUP_ACTION_FIXPOINT = prove
 (`!G s (a:A->X->X) p k.
        group_action G s a /\
        prime p /\ (group_carrier G) HAS_SIZE (p EXP k) /\
        FINITE s /\ ~(p divides CARD s)
        ==> ?x. x IN s /\ !g. g IN group_carrier G ==> a g x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `s:X->bool`; `a:A->X->X`; `p:num`; `k:num`]
        PGROUP_ACTION_FIXPOINTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `(x == y) (mod p) ==> x = 0 ==> p divides y`)) THEN
  ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Right and left cosets.                                                    *)
(* ------------------------------------------------------------------------- *)

let right_coset = new_definition
 `right_coset G h x = group_setmul G h {x}`;;

let left_coset = new_definition
 `left_coset G x h = group_setmul G {x} h`;;

let LEFT_COSET_AS_IMAGE = prove
 (`!(x:A) h. left_coset G x h = IMAGE (group_mul G x) h`,
  REWRITE_TAC[left_coset; group_setmul] THEN SET_TAC[]);;

let RIGHT_COSET = prove
 (`!G h x:A.
        x IN group_carrier G /\ h SUBSET group_carrier G
        ==> right_coset G h x SUBSET group_carrier G`,
  SIMP_TAC[right_coset; GROUP_SETMUL; SING_SUBSET]);;

let LEFT_COSET = prove
 (`!G h x:A.
        x IN group_carrier G /\ h SUBSET group_carrier G
        ==> left_coset G x h SUBSET group_carrier G`,
  SIMP_TAC[left_coset; GROUP_SETMUL; SING_SUBSET]);;

let IN_RIGHT_COSET = prove
 (`!G h x a:A.
        h SUBSET group_carrier G /\
        a IN group_carrier G /\ x IN group_carrier G
        ==> (x IN right_coset G h a <=>
             group_mul G x (group_inv G a) IN h)`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[right_coset; group_setmul; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`; UNWIND_THM2] THEN
  EQ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[] `P a ==> a IN h ==> ?y. y IN h /\ P y`)] THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; GSYM GROUP_MUL_ASSOC; GROUP_MUL_LINV;
               GROUP_MUL_RINV; GROUP_MUL_RID; GROUP_INV]);;

let IN_LEFT_COSET = prove
 (`!G h x a:A.
        h SUBSET group_carrier G /\
        a IN group_carrier G /\ x IN group_carrier G
        ==> (x IN left_coset G a h <=>
             group_mul G (group_inv G a) x IN h)`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[left_coset; group_setmul; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; RIGHT_EXISTS_AND_THM] THEN
  EQ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[] `P a ==> a IN h ==> ?y. y IN h /\ P y`)] THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; GROUP_MUL_ASSOC; GROUP_MUL_LINV;
               GROUP_MUL_RINV; GROUP_MUL_LID; GROUP_INV]);;

let IN_RIGHT_COSET_INV = prove
 (`!G h x y:A.
        h SUBSET group_carrier G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> (x IN right_coset G h (group_inv G y) <=>
             group_mul G x y IN h)`,
  SIMP_TAC[IN_RIGHT_COSET; GROUP_INV; GROUP_INV_INV]);;

let IN_LEFT_COSET_INV = prove
 (`!G h x y:A.
        h SUBSET group_carrier G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> (x IN left_coset G (group_inv G y) h <=>
             group_mul G y x IN h)`,
  SIMP_TAC[IN_LEFT_COSET; GROUP_INV; GROUP_INV_INV]);;

let GROUP_SETINV_LEFT_COSET_GEN,GROUP_SETINV_RIGHT_COSET_GEN =
 (CONJ_PAIR o prove)
 (`(!G h a:A.
        h subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (left_coset G a h) =
            right_coset G h (group_inv G a)) /\
   (!G h a:A.
        h subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (right_coset G h a) =
            left_coset G (group_inv G a) h)`,
  REWRITE_TAC[GROUP_SETINV_AS_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM FORALL_IN_GROUP_CARRIER_INV] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; AND_FORALL_THM; IMP_IMP] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[GROUP_INV_INV] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
   `!u. s SUBSET u /\ t SUBSET u /\ (!x. x IN u ==> f(f x) = x) /\
        (!x. x IN u ==> (f x IN t <=> x IN s)) /\
        (!x. x IN u ==> (f x IN s <=> x IN t))
        ==> IMAGE f s = t /\ IMAGE f t = s`) THEN
  EXISTS_TAC `group_carrier G:A->bool` THEN
  ASM_SIMP_TAC[IN_LEFT_COSET; IN_RIGHT_COSET; SUBGROUP_OF_IMP_SUBSET;
               GROUP_INV_INV; GROUP_INV; LEFT_COSET; RIGHT_COSET] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `G:A group` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] IN_SUBGROUP_INV)) THEN
  ASM_SIMP_TAC[GROUP_INV_MUL; GROUP_INV_INV; GROUP_INV]);;

let RIGHT_COSET_OPPOSITE_GROUP = prove
 (`!G h x:A. right_coset G h x = left_coset (opposite_group G) x h`,
  REWRITE_TAC[left_coset; right_coset; OPPOSITE_GROUP_SETMUL]);;

let LEFT_COSET_OPPOSITE_GROUP = prove
 (`!G h x:A. left_coset G x h = right_coset (opposite_group G) h x`,
  REWRITE_TAC[left_coset; right_coset; OPPOSITE_GROUP_SETMUL]);;

let GROUP_CONJUGATION_RIGHT_COSET = prove
 (`!G h x:A.
     x IN group_carrier G /\ h SUBSET group_carrier G
     ==> IMAGE (group_conjugation G x) (right_coset G h x) = left_coset G x h`,
  REWRITE_TAC[IMAGE_GROUP_CONJUGATION; left_coset; right_coset] THEN
  SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_SETMUL;
           GROUP_INV; GROUP_SETMUL_SING; GROUP_MUL_RINV; GROUP_SETMUL_RID]);;

let RIGHT_COSET_GROUP_CONJUGATION = prove
 (`!G h x:A.
     x IN group_carrier G /\ h SUBSET group_carrier G
     ==> right_coset G (IMAGE (group_conjugation G x) h) x =
         left_coset G x h`,
  REWRITE_TAC[IMAGE_GROUP_CONJUGATION; left_coset; right_coset] THEN
  SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_SETMUL;
           GROUP_INV; GROUP_SETMUL_SING; GROUP_MUL_LINV; GROUP_SETMUL_RID]);;

let LEFT_COSET_LEFT_COSET = prove
 (`!x y h:A->bool.
        x IN group_carrier G /\
        y IN group_carrier G /\
        h SUBSET group_carrier G
        ==> left_coset G x (left_coset G y h) =
            left_coset G (group_mul G x y) h`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[LEFT_COSET_AS_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; SUBSET]);;

let RIGHT_COSET_RIGHT_COSET = prove
 (`!x y h:A->bool.
        h SUBSET group_carrier G /\
        x IN group_carrier G /\
        y IN group_carrier G
        ==> right_coset G (right_coset G h x) y =
            right_coset G h (group_mul G x y)`,
  REWRITE_TAC[RIGHT_COSET_OPPOSITE_GROUP] THEN
  SIMP_TAC[LEFT_COSET_LEFT_COSET; OPPOSITE_GROUP]);;

let RIGHT_COSET_ID = prove
 (`!G h:A->bool.
        h SUBSET group_carrier G ==> right_coset G h (group_id G) = h`,
  SIMP_TAC[right_coset; group_setmul; SET_RULE
   `{f x y | P x /\ y IN {a}} = {f x a | P x}`] THEN
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s`) THEN
  ASM_SIMP_TAC[GROUP_MUL_RID]);;

let LEFT_COSET_ID = prove
 (`!G h:A->bool.
        h SUBSET group_carrier G ==> left_coset G (group_id G) h = h`,
  MESON_TAC[RIGHT_COSET_ID; LEFT_COSET_OPPOSITE_GROUP; OPPOSITE_GROUP]);;

let LEFT_COSET_TRIVIAL = prove
 (`!G x:A. x IN group_carrier G ==> left_coset G x {group_id G} = {x}`,
  SIMP_TAC[left_coset; GROUP_SETMUL_SING; GROUP_ID; GROUP_MUL_RID]);;

let RIGHT_COSET_TRIVIAL = prove
 (`!G x:A. x IN group_carrier G ==> right_coset G {group_id G} x = {x}`,
  SIMP_TAC[right_coset; GROUP_SETMUL_SING; GROUP_ID; GROUP_MUL_LID]);;

let LEFT_COSET_CARRIER = prove
 (`!G x:A. x IN group_carrier G
           ==> left_coset G x (group_carrier G) = group_carrier G`,
  SIMP_TAC[left_coset; GROUP_SETMUL_LSUBSET; SING_SUBSET; NOT_INSERT_EMPTY;
           CARRIER_SUBGROUP_OF]);;

let RIGHT_COSET_CARRIER = prove
 (`!G x:A. x IN group_carrier G
           ==> right_coset G (group_carrier G) x = group_carrier G`,
  SIMP_TAC[right_coset; GROUP_SETMUL_RSUBSET; SING_SUBSET; NOT_INSERT_EMPTY;
           CARRIER_SUBGROUP_OF]);;

let RIGHT_COSET_EQ = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (right_coset G h x = right_coset G h y <=> group_div G x y IN h)`,
  SIMP_TAC[GROUP_SETMUL_LCANCEL_SET; right_coset]);;

let LEFT_COSET_EQ = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (left_coset G x h = left_coset G y h <=>
             group_mul G (group_inv G x) y IN h)`,
  SIMP_TAC[GROUP_SETMUL_RCANCEL_SET; left_coset]);;

let RIGHT_COSET_EQ_SUBGROUP = prove
 (`!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (right_coset G h x = h <=> x IN h)`,
  SIMP_TAC[right_coset; GROUP_SETMUL_RSUBSET_EQ; SING_SUBSET] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY]);;

let LEFT_COSET_EQ_SUBGROUP = prove
 (`!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (left_coset G x h = h <=> x IN h)`,
  SIMP_TAC[left_coset; GROUP_SETMUL_LSUBSET_EQ; SING_SUBSET] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY]);;

let RIGHT_COSET_EQ_EMPTY = prove
 (`!G h x:A. right_coset G h x = {} <=> h = {}`,
  REWRITE_TAC[right_coset; GROUP_SETMUL_EQ_EMPTY; NOT_INSERT_EMPTY]);;

let LEFT_COSET_EQ_EMPTY = prove
 (`!G h x:A. left_coset G x h = {} <=> h = {}`,
  REWRITE_TAC[left_coset; GROUP_SETMUL_EQ_EMPTY; NOT_INSERT_EMPTY]);;

let RIGHT_COSET_NONEMPTY = prove
 (`!G h x:A. h subgroup_of G ==> ~(right_coset G h x = {})`,
  REWRITE_TAC[RIGHT_COSET_EQ_EMPTY; SUBGROUP_OF_IMP_NONEMPTY]);;

let LEFT_COSET_NONEMPTY = prove
 (`!G h x:A. h subgroup_of G ==> ~(left_coset G x h = {})`,
  REWRITE_TAC[LEFT_COSET_EQ_EMPTY; SUBGROUP_OF_IMP_NONEMPTY]);;

let IN_RIGHT_COSET_SELF = prove
 (`!G h x:A.
      h subgroup_of G /\ x IN group_carrier G ==> x IN right_coset G h x`,
  REWRITE_TAC[subgroup_of; right_coset; group_setmul; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[GROUP_MUL_LID]);;

let IN_LEFT_COSET_SELF = prove
 (`!G h x:A.
      h subgroup_of G /\ x IN group_carrier G ==> x IN left_coset G x h`,
  REWRITE_TAC[subgroup_of; left_coset; group_setmul; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[GROUP_MUL_RID]);;

let UNIONS_RIGHT_COSETS = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> UNIONS {right_coset G h x |x| x IN group_carrier G} =
            group_carrier G`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RIGHT_COSET; SUBGROUP_OF_IMP_SUBSET] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; SUBSET] THEN
  ASM_MESON_TAC[IN_RIGHT_COSET_SELF]);;

let UNIONS_LEFT_COSETS = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> UNIONS {left_coset G x h |x| x IN group_carrier G} =
            group_carrier G`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[LEFT_COSET; SUBGROUP_OF_IMP_SUBSET] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; SUBSET] THEN
  ASM_MESON_TAC[IN_LEFT_COSET_SELF]);;

let RIGHT_COSETS_EQ = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (right_coset G h x = right_coset G h y <=>
             ~(DISJOINT (right_coset G h x) (right_coset G h y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[GSYM DISJOINT_EMPTY_REFL; RIGHT_COSET_NONEMPTY] THEN
  ASM_SIMP_TAC[RIGHT_COSET_EQ; LEFT_IMP_EXISTS_THM; IMP_CONJ; SET_RULE
   `~DISJOINT s t <=> ?x. x IN s /\ ?y. y IN t /\ x = y`] THEN
  REWRITE_TAC[right_coset; group_setmul; FORALL_IN_GSPEC; IN_SING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  X_GEN_TAC `u:A` THEN DISCH_TAC THEN X_GEN_TAC `v:A` THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `group_mul G (group_inv G u):A->A`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
  ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_INV; GROUP_MUL_LINV; GROUP_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[group_div; GSYM GROUP_MUL_ASSOC; GROUP_INV; GROUP_MUL;
               GROUP_MUL_RINV; GROUP_MUL_RID]);;

let LEFT_COSETS_EQ = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (left_coset G x h = left_coset G y h <=>
             ~(DISJOINT (left_coset G x h) (left_coset G y h)))`,
  REWRITE_TAC[LEFT_COSET_OPPOSITE_GROUP] THEN
  SIMP_TAC[RIGHT_COSETS_EQ; SUBGROUP_OF_OPPOSITE_GROUP; OPPOSITE_GROUP]);;

let DISJOINT_RIGHT_COSETS = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (DISJOINT (right_coset G h x) (right_coset G h y) <=>
             ~(right_coset G h x = right_coset G h y))`,
  SIMP_TAC[RIGHT_COSETS_EQ]);;

let DISJOINT_LEFT_COSETS = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> (DISJOINT (left_coset G x h) (left_coset G y h) <=>
             ~(left_coset G x h = left_coset G y h))`,
  SIMP_TAC[LEFT_COSETS_EQ]);;

let PAIRWISE_DISJOINT_RIGHT_COSETS = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> pairwise DISJOINT {right_coset G h a |a| a IN group_carrier G}`,
  REWRITE_TAC[SIMPLE_IMAGE; PAIRWISE_IMAGE] THEN
  SIMP_TAC[pairwise; DISJOINT_RIGHT_COSETS]);;

let PAIRWISE_DISJOINT_LEFT_COSETS = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> pairwise DISJOINT {left_coset G a h |a| a IN group_carrier G}`,
  REWRITE_TAC[SIMPLE_IMAGE; PAIRWISE_IMAGE] THEN
  SIMP_TAC[pairwise; DISJOINT_LEFT_COSETS]);;

let IMAGE_RIGHT_COSET_SWITCH = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> IMAGE (\a. group_mul G a (group_mul G (group_inv G x) y))
                  (right_coset G h x) =
            right_coset G h y`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `group_setmul G (right_coset G h x) {group_mul G (group_inv G x) y:A}` THEN
  CONJ_TAC THENL [REWRITE_TAC[group_setmul] THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[right_coset] THEN
  ASM_SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; GROUP_SETMUL; SING_SUBSET;
               GROUP_MUL; GROUP_INV; GROUP_SETMUL_SING; GROUP_MUL_ASSOC;
               GROUP_MUL_RINV; GROUP_MUL_LID]);;

let IMAGE_LEFT_COSET_SWITCH = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> IMAGE (\a. group_mul G (group_div G y x) a)
                  (left_coset G x h) =
            left_coset G y h`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `group_setmul G {group_div G y x:A} (left_coset G x h)` THEN
  CONJ_TAC THENL [REWRITE_TAC[group_setmul] THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[left_coset; group_div] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; GROUP_SETMUL; SING_SUBSET;
               GROUP_MUL; GROUP_INV; GROUP_SETMUL_SING; GSYM GROUP_MUL_ASSOC;
               GROUP_MUL_LINV; GROUP_MUL_RID]);;

let CARD_EQ_LEFT_RIGHT_COSETS = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> {left_coset G x h |x| x IN group_carrier G} =_c
            {right_coset G h x |x| x IN group_carrier G}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_C_INVOLUTION THEN
  EXISTS_TAC `group_setinv(G:A group)` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; FORALL_AND_THM;
               TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  ASM_SIMP_TAC[GROUP_SETINV_LEFT_COSET_GEN; GROUP_SETINV_RIGHT_COSET_GEN;
               GROUP_INV; GROUP_INV_INV] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[GROUP_INV]);;

let CARD_EQ_RIGHT_COSETS = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> right_coset G h x =_c right_coset G h y`,
  let lemma = prove
   (`!f g. (IMAGE f s = t /\ IMAGE g t = s) /\
           (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> s =_c t`,
    REWRITE_TAC[eq_c; LEFT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC `\a:A. group_mul G a (group_mul G (group_inv G x) y)` THEN
  EXISTS_TAC `\a:A. group_mul G a (group_mul G (group_inv G y) x)` THEN
  ASM_SIMP_TAC[IMAGE_RIGHT_COSET_SWITCH; INJECTIVE_ON_ALT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_MUL_RCANCEL THEN
  ASM_MESON_TAC[GROUP_MUL; GROUP_INV; SUBSET; RIGHT_COSET;
                SUBGROUP_OF_IMP_SUBSET]);;

let GROUP_ID_IN_LEFT_COSET_GEN = prove
 (`!G h x:A.
        h SUBSET group_carrier G /\ x IN group_carrier G
        ==> (group_id G IN left_coset G x h <=> group_inv G x IN h)`,
  REWRITE_TAC[left_coset; group_setmul; IN_ELIM_THM; IN_SING; SUBSET] THEN
  MESON_TAC[GROUP_LINV_EQ]);;

let GROUP_ID_IN_LEFT_COSET = prove
 (`!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (group_id G IN left_coset G x h <=> x IN h)`,
  SIMP_TAC[subgroup_of; GROUP_ID_IN_LEFT_COSET_GEN] THEN
  MESON_TAC[GROUP_INV_INV; SUBSET]);;

let SUBGROUP_OF_LEFT_COSET = prove
 (`!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (left_coset G x h subgroup_of G <=> left_coset G x h = h)`,
  MESON_TAC[LEFT_COSET_EQ_SUBGROUP; subgroup_of; GROUP_ID_IN_LEFT_COSET]);;

let GROUP_ID_IN_RIGHT_COSET_GEN = prove
 (`!G h x:A.
        h SUBSET group_carrier G /\ x IN group_carrier G
        ==> (group_id G IN right_coset G h x <=> group_inv G x IN h)`,
  REWRITE_TAC[right_coset; group_setmul; IN_ELIM_THM; IN_SING; SUBSET] THEN
  MESON_TAC[GROUP_RINV_EQ]);;

let GROUP_ID_IN_RIGHT_COSET = prove
 (`!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (group_id G IN right_coset G h x <=> x IN h)`,
  SIMP_TAC[subgroup_of; GROUP_ID_IN_RIGHT_COSET_GEN] THEN
  MESON_TAC[GROUP_INV_INV; SUBSET]);;

let SUBGROUP_OF_RIGHT_COSET = prove
 (`!G h x:A.
        h subgroup_of G /\ x IN group_carrier G
        ==> (right_coset G h x subgroup_of G <=> right_coset G h x = h)`,
  MESON_TAC[RIGHT_COSET_EQ_SUBGROUP; subgroup_of; GROUP_ID_IN_RIGHT_COSET]);;

let CARD_EQ_LEFT_COSETS = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> left_coset G x h =_c left_coset G y h`,
  SIMP_TAC[LEFT_COSET_OPPOSITE_GROUP; SUBGROUP_OF_OPPOSITE_GROUP;
           OPPOSITE_GROUP; CARD_EQ_RIGHT_COSETS]);;

let CARD_EQ_RIGHT_COSET_SUBGROUP = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> right_coset G h x =_c h`,
  MESON_TAC[CARD_EQ_RIGHT_COSETS; GROUP_ID; RIGHT_COSET_ID;
            SUBGROUP_OF_IMP_SUBSET]);;

let CARD_EQ_LEFT_COSET_SUBGROUP = prove
 (`!G h x y:A.
        h subgroup_of G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> left_coset G x h =_c h`,
  MESON_TAC[CARD_EQ_LEFT_COSETS; GROUP_ID; LEFT_COSET_ID;
            SUBGROUP_OF_IMP_SUBSET]);;

let GROUP_ORBIT_SUBGROUP_TRANSLATION = prove
 (`!G h a:A.
   h subgroup_of G /\ a IN group_carrier G
   ==> group_orbit (subgroup_generated G h) (group_carrier G) (group_mul G) a =
       right_coset G h a`,
  SIMP_TAC[SUBGROUP_OF_IMP_SUBSET; GROUP_ORBIT;
           GROUP_ACTION_SUBGROUP_TRANSLATION] THEN
  SIMP_TAC[right_coset; group_setmul;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  SET_TAC[]);;

let GROUP_ORBIT_GROUP_TRANSLATION = prove
 (`!G a:A.
    a IN group_carrier G
    ==> group_orbit G (group_carrier G) (group_mul G) a = group_carrier G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `group_carrier G:A->bool`; `a:A`]
        GROUP_ORBIT_SUBGROUP_TRANSLATION) THEN
  ASM_REWRITE_TAC[CARRIER_SUBGROUP_OF; SUBGROUP_GENERATED_GROUP_CARRIER] THEN
  ASM_SIMP_TAC[RIGHT_COSET_CARRIER]);;

let ORBIT_STABILIZER_GEN = prove
 (`!G s (a:A->X->X) x.
      group_action G s a /\ x IN s
      ==> group_orbit G s a x =_c
          {left_coset G g (group_stabilizer G a x) |g| g IN group_carrier G}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_ORBIT; SIMPLE_IMAGE] THEN
  MATCH_MP_TAC CARD_EQ_IMAGES THEN
  ASM_MESON_TAC[GROUP_ACTION_EQ; LEFT_COSET_EQ;
                SUBGROUP_OF_GROUP_STABILIZER]);;

let ORBIT_STABILIZER = prove
 (`!G s (a:A->X->X) x.
      FINITE(group_carrier G) /\ group_action G s a /\ x IN s
      ==> CARD (group_orbit G s a x) =
          CARD {left_coset G g (group_stabilizer G a x) |g|
                g IN group_carrier G}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORBIT_STABILIZER_GEN) THEN
  ASM_SIMP_TAC[FINITE_GROUP_STABILIZER; FINITE_GROUP_ORBIT; CARD_EQ_CARD;
               SIMPLE_IMAGE; FINITE_IMAGE]);;

let GROUP_ACTION_LEFT_COSET_MULTIPLICATION = prove
 (`!G h:A->bool.
        h SUBSET group_carrier G
        ==> group_action G {left_coset G x h | x | x IN group_carrier G}
                           (IMAGE o group_mul G)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ACTION_SUBSET_TRANSLATION THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[LEFT_COSET] THEN REWRITE_TAC[LEFT_COSET_AS_IMAGE] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN X_GEN_TAC `b:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM IMAGE_o; o_DEF] THEN
  EXISTS_TAC `group_mul G a b:A` THEN ASM_SIMP_TAC[GROUP_MUL] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  ASM_MESON_TAC[GROUP_MUL_ASSOC; SUBSET]);;

let GROUP_ORBIT_LEFT_COSET_MULTIPLICATION = prove
 (`!G h a:A.
        a IN group_carrier G /\ h subgroup_of G
        ==> group_orbit G { left_coset G x h | x | x IN group_carrier G}
                          (IMAGE o group_mul G) (left_coset G a h) =
            { left_coset G x h | x | x IN group_carrier G}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  ASM_SIMP_TAC[GROUP_ORBIT; GROUP_ACTION_LEFT_COSET_MULTIPLICATION] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[GSYM LEFT_COSET_AS_IMAGE; LEFT_COSET_LEFT_COSET; o_DEF] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LEFT_COSET_EQ; GROUP_MUL; LEFT_COSET_LEFT_COSET;
   GROUP_INV_MUL; MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  CONJ_TAC THEN X_GEN_TAC `b:A` THEN DISCH_TAC THENL
   [EXISTS_TAC `group_mul G b a:A`;
    EXISTS_TAC `group_mul G b (group_inv G a):A`] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[subgroup_of]
   `h subgroup_of G ==> x = group_id G ==> x IN h`)) THEN
  GROUP_TAC);;

let GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION = prove
 (`!G h a:A.
        a IN group_carrier G /\ h subgroup_of G
        ==> group_stabilizer G (IMAGE o group_mul G) (left_coset G a h) =
            IMAGE (group_conjugation G a) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_stabilizer] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [SYM(MATCH_MP GROUP_SETINV_SUBGROUP th)]) THEN
  REWRITE_TAC[group_setinv; SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  REWRITE_TAC[group_stabilizer; o_THM; GSYM LEFT_COSET_AS_IMAGE] THEN
  ASM_SIMP_TAC[LEFT_COSET_LEFT_COSET; GROUP_MUL; LEFT_COSET_EQ] THEN
  REWRITE_TAC[NOT_IMP] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f(g x) = x) /\ (!x. x IN s ==> f x IN s /\ g(f x) = x) /\
    t SUBSET s
    ==> {x | x IN s /\ g x IN t} = IMAGE f t`) THEN
  ASM_SIMP_TAC[group_conjugation; GROUP_INV; GROUP_MUL] THEN
  REPEAT STRIP_TAC THEN GROUP_TAC);;

let GROUP_ORBIT_LEFT_COSET_MULTIPLICATION_ID = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> group_orbit G { left_coset G x h | x | x IN group_carrier G}
                          (IMAGE o group_mul G) h =
            { left_coset G x h | x | x IN group_carrier G}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`; `group_id G:A`]
        GROUP_ORBIT_LEFT_COSET_MULTIPLICATION) THEN
  ASM_SIMP_TAC[LEFT_COSET_ID; SUBGROUP_OF_IMP_SUBSET; GROUP_ID]);;

let GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION_ID = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> group_stabilizer G (IMAGE o group_mul G) h = h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`; `group_id G:A`]
        GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION) THEN
  ASM_SIMP_TAC[LEFT_COSET_ID; SUBGROUP_OF_IMP_SUBSET; GROUP_ID] THEN
  DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
  ASM_MESON_TAC[GROUP_CONJUGATION_BY_ID; SUBSET; subgroup_of]);;

let LAGRANGE_THEOREM_LEFT_GEN = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> {left_coset G x h | x | x IN group_carrier G} *_c h =_c
            group_carrier G`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_ACTION_LEFT_COSET_MULTIPLICATION) THEN
  DISCH_THEN(MP_TAC o SPEC `h:A->bool` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] ORBIT_STABILIZER_MUL_GEN)) THEN
  ASM_SIMP_TAC[GROUP_ORBIT_LEFT_COSET_MULTIPLICATION_ID;
               GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION_ID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `group_id G:A` THEN ASM_SIMP_TAC[LEFT_COSET_ID; GROUP_ID]);;

let LAGRANGE_THEOREM_RIGHT_GEN = prove
 (`!G h:A->bool.
        h subgroup_of G
        ==> {right_coset G h x | x | x IN group_carrier G} *_c h =_c
            group_carrier G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RIGHT_COSET_OPPOSITE_GROUP] THEN
  ONCE_REWRITE_TAC[SYM(CONJUNCT1(SPEC_ALL OPPOSITE_GROUP))] THEN
  MATCH_MP_TAC LAGRANGE_THEOREM_LEFT_GEN THEN
  ASM_REWRITE_TAC[SUBGROUP_OF_OPPOSITE_GROUP; OPPOSITE_GROUP]);;

let LAGRANGE_THEOREM_LEFT = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h |x| x IN group_carrier G} * CARD h =
            CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(h:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[subgroup_of; FINITE_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LAGRANGE_THEOREM_LEFT_GEN) THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; CARD_EQ_CARD; FINITE_IMAGE;
               CARD_MUL_FINITE; CARD_MUL_C]);;

let LAGRANGE_THEOREM_RIGHT = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x |x| x IN group_carrier G} * CARD h =
            CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RIGHT_COSET_OPPOSITE_GROUP] THEN
  ONCE_REWRITE_TAC[SYM(CONJUNCT1(SPEC_ALL OPPOSITE_GROUP))] THEN
  MATCH_MP_TAC LAGRANGE_THEOREM_LEFT THEN
  ASM_REWRITE_TAC[SUBGROUP_OF_OPPOSITE_GROUP; OPPOSITE_GROUP]);;

let LAGRANGE_THEOREM = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> (CARD h) divides CARD(group_carrier G)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP LAGRANGE_THEOREM_RIGHT) THEN
  NUMBER_TAC);;

let CARD_LEFT_COSETS_DIVIDES = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h | x | x IN group_carrier G} divides
            CARD(group_carrier G)`,
  MESON_TAC[divides; LAGRANGE_THEOREM_LEFT]);;

let CARD_RIGHT_COSETS_DIVIDES = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x | x | x IN group_carrier G} divides
            CARD(group_carrier G)`,
  MESON_TAC[divides; LAGRANGE_THEOREM_RIGHT]);;

let LAGRANGE_THEOREM_LEFT_DIV = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h | x | x IN group_carrier G} =
            CARD(group_carrier G) DIV CARD h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP LAGRANGE_THEOREM_LEFT) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC DIV_MULT THEN
  ASM_MESON_TAC[subgroup_of; FINITE_SUBSET; CARD_EQ_0;
                SUBGROUP_OF_IMP_NONEMPTY]);;

let LAGRANGE_THEOREM_RIGHT_DIV = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x | x | x IN group_carrier G} =
            CARD(group_carrier G) DIV CARD h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP LAGRANGE_THEOREM_RIGHT) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC DIV_MULT THEN
  ASM_MESON_TAC[subgroup_of; FINITE_SUBSET; CARD_EQ_0;
                SUBGROUP_OF_IMP_NONEMPTY]);;

let GROUP_SETMUL_PROD_GROUP = prove
 (`!(G1:A group) (G2:B group) s1 s2 t1 t2.
        group_setmul (prod_group G1 G2) (s1 CROSS s2) (t1 CROSS t2) =
        (group_setmul G1 s1 t1) CROSS (group_setmul G2 s2 t2)`,
  REWRITE_TAC[group_setmul; CROSS; PROD_GROUP; SET_RULE
   `{f x y | x IN {g a b | P a b} /\ y IN {h c d | Q c d}} =
    {f (g a b) (h c d) | P a b /\ Q c d}`] THEN
  SET_TAC[]);;

let RIGHT_COSET_PROD_GROUP = prove
 (`!G1 G2 h1 h2 (x1:A) (x2:B).
        right_coset (prod_group G1 G2) (h1 CROSS h2) (x1,x2) =
        (right_coset G1 h1 x1) CROSS (right_coset G2 h2 x2)`,
  REWRITE_TAC[right_coset; GSYM CROSS_SING; GROUP_SETMUL_PROD_GROUP]);;

let LEFT_COSET_PROD_GROUP = prove
 (`!G1 G2 h1 h2 (x1:A) (x2:B).
        left_coset (prod_group G1 G2) (x1,x2) (h1 CROSS h2) =
        (left_coset G1 x1 h1) CROSS (left_coset G2 x2 h2)`,
  REWRITE_TAC[left_coset; GSYM CROSS_SING; GROUP_SETMUL_PROD_GROUP]);;

let GROUP_SETMUL_PRODUCT_GROUP = prove
 (`!(G:K->A group) k s t.
        group_setmul (product_group k G)
                     (cartesian_product k s) (cartesian_product k t) =
        cartesian_product k (\i. group_setmul (G i) (s i) (t i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_setmul; CARTESIAN_PRODUCT_AS_RESTRICTIONS;
              PRODUCT_GROUP] THEN
  REWRITE_TAC[IN_ELIM_THM; SET_RULE
   `{f x y | x,y | x IN {g x | P x} /\ y IN {g f | Q f}} =
    {f (g x) (g y) | P x /\ Q y}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; TAUT
   `p ==> (q /\ r) /\ s <=> (p ==> s) /\ (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[GSYM RESTRICTION_EXTENSION; SET_RULE
   `{RESTRICTION k f | f | ?x y. RESTRICTION k f = RESTRICTION k (g x y) /\
                                 R x y} =
    {RESTRICTION k (g x y) | R x y}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. R x y ==> f x y = g x y)
    ==> {f x y | R x y} = {g x y | R x y}`) THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN SIMP_TAC[RESTRICTION]);;

let RIGHT_COSET_PRODUCT_GROUP = prove
 (`!(G:K->A group) h x k.
        right_coset (product_group k G) (cartesian_product k h) x =
        cartesian_product k (\i. right_coset (G i) (h i) (x i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[right_coset] THEN
  REWRITE_TAC[GSYM GROUP_SETMUL_PRODUCT_GROUP] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_SINGS_GEN] THEN
  REWRITE_TAC[group_setmul; PRODUCT_GROUP; SET_RULE
   `{f x y | x,y | P x /\ y IN {a}} = {f x a | P x}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> {f x | x IN s} = {g x | x IN s}`) THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN SIMP_TAC[RESTRICTION]);;

let LEFT_COSET_PRODUCT_GROUP = prove
 (`!(G:K->A group) h x k.
        left_coset (product_group k G) x (cartesian_product k h) =
        cartesian_product k (\i. left_coset (G i) (x i) (h i))`,
  REWRITE_TAC[LEFT_COSET_OPPOSITE_GROUP; OPPOSITE_PRODUCT_GROUP] THEN
  REWRITE_TAC[RIGHT_COSET_PRODUCT_GROUP]);;

let GROUP_SETINV_SUBGROUP_GENERATED = prove
 (`!G h:A->bool.
        group_setinv (subgroup_generated G h) = group_setinv G`,
  REWRITE_TAC[group_setinv; FUN_EQ_THM; SUBGROUP_GENERATED]);;

let GROUP_SETMUL_SUBGROUP_GENERATED = prove
 (`!G h:A->bool.
        group_setmul (subgroup_generated G h) = group_setmul G`,
  REWRITE_TAC[group_setmul; FUN_EQ_THM; SUBGROUP_GENERATED]);;

let RIGHT_COSET_SUBGROUP_GENERATED = prove
 (`!G h k x. right_coset (subgroup_generated G h) k x = right_coset G k x`,
  REWRITE_TAC[right_coset; GROUP_SETMUL_SUBGROUP_GENERATED]);;

let LEFT_COSET_SUBGROUP_GENERATED = prove
 (`!G h k x. left_coset (subgroup_generated G h) x k = left_coset G x k`,
  REWRITE_TAC[left_coset; GROUP_SETMUL_SUBGROUP_GENERATED]);;

(* ------------------------------------------------------------------------- *)
(* Normal subgroups.                                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("normal_subgroup_of",(12,"right"));;

let normal_subgroup_of = new_definition
  `(n:A->bool) normal_subgroup_of (G:A group) <=>
        n subgroup_of G /\
        !x. x IN group_carrier G ==> left_coset G x n = right_coset G n x`;;

let NORMAL_SUBGROUP_IMP_SUBGROUP = prove
 (`!G n:A->bool. n normal_subgroup_of G ==> n subgroup_of G`,
  SIMP_TAC[normal_subgroup_of]);;

let NORMAL_SUBGROUP_OF_IMP_SUBSET = prove
 (`!G n:A->bool. n normal_subgroup_of G ==> n SUBSET group_carrier G`,
  MESON_TAC[SUBGROUP_OF_IMP_SUBSET; normal_subgroup_of]);;

let NORMAL_SUBGROUP_OF_OPPOSITE_GROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of opposite_group G <=> n normal_subgroup_of G`,
  REWRITE_TAC[normal_subgroup_of; SUBGROUP_OF_OPPOSITE_GROUP] THEN
  REWRITE_TAC[GSYM LEFT_COSET_OPPOSITE_GROUP; OPPOSITE_GROUP;
              GSYM RIGHT_COSET_OPPOSITE_GROUP] THEN
  MESON_TAC[]);;

let ABELIAN_GROUP_NORMAL_SUBGROUP = prove
 (`!G n:A->bool.
        abelian_group G ==> (n normal_subgroup_of G <=> n subgroup_of G)`,
  REWRITE_TAC[normal_subgroup_of; left_coset; right_coset; subgroup_of] THEN
  MESON_TAC[GROUP_SETMUL_SYM; SING_SUBSET]);;

let NORMAL_SUBGROUP_CONJUGATE_ALT = prove
 (`!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        !x. x IN group_carrier G
            ==> group_setmul G {group_inv G x} (group_setmul G n {x}) = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_subgroup_of] THEN
  ASM_CASES_TAC `(n:A->bool) subgroup_of G` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[left_coset; right_coset] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_INV] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_SING; GROUP_MUL_LINV; GROUP_SETMUL_LID];
    DISCH_THEN(MP_TAC o AP_TERM `group_setmul G {x:A}`) THEN
    ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; GROUP_INV; GROUP_SETMUL; SING_SUBSET] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_SING; GROUP_MUL_RINV; GROUP_SETMUL_LID]]);;

let NORMAL_SUBGROUP_CONJUGATE_INV = prove
 (`!G n:A->bool.
      n normal_subgroup_of G <=>
      n subgroup_of G /\
      !x. x IN group_carrier G
          ==> group_setmul G {group_inv G x} (group_setmul G n {x}) SUBSET n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATE_ALT] THEN
  ASM_CASES_TAC `(n:A->bool) subgroup_of G` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  EQ_TAC THEN SIMP_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_inv G (x:A)`) THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_INV_INV] THEN DISCH_THEN(MP_TAC o
   ISPEC `\y:A. group_mul G (group_inv G x) (group_mul G y x)` o
   MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[group_setmul; SIMPLE_IMAGE;
    SET_RULE `{f x y | x IN {a} /\ P y} = {f a y | P y}`;
    SET_RULE `{f x y | P x /\ y IN {a}} = {f x a | P x}`] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> IMAGE f s SUBSET t ==> s SUBSET t`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [GROUP_MUL_ASSOC; GROUP_MUL; GROUP_INV; GROUP_MUL_LINV] THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL_LINV; GROUP_MUL; GROUP_INV] THEN
  ASM_SIMP_TAC[GROUP_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL_LINV; GROUP_MUL; GROUP_INV] THEN
  ASM_SIMP_TAC[GROUP_MUL_RID]);;

let NORMAL_SUBGROUP_CONJUGATION_EQ = prove
 (`!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !a. a IN group_carrier G ==> IMAGE (group_conjugation G a) h = h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_subgroup_of] THEN
  ASM_CASES_TAC `(h:A->bool) subgroup_of G` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[IMAGE_GROUP_CONJUGATION; left_coset; right_coset] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `group_inv G x:A`) THEN
    ASM_SIMP_TAC[GROUP_INV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_INV] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_SING; GROUP_SETMUL_LID; GROUP_MUL_RINV];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    ASM_SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_INV; GROUP_SETMUL;
                 GROUP_SETMUL_SING; GROUP_MUL_LINV; GROUP_SETMUL_RID]]);;

let NORMAL_SUBGROUP_CONJUGATION = prove
 (`!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !a. a IN group_carrier G ==> IMAGE (group_conjugation G a) h SUBSET h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION_EQ] THEN
  ASM_CASES_TAC `(h:A->bool) subgroup_of G` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  EQ_TAC THEN SIMP_TAC[GSYM SUBSET_ANTISYM_EQ] THEN DISCH_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_inv G x:A`) THEN
  ASM_SIMP_TAC[GROUP_INV] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN h ==> f(g x) = x)
    ==> IMAGE g h SUBSET h ==> h SUBSET IMAGE f h`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION_CONJUGATION; GROUP_INV] THEN
  ASM_SIMP_TAC[GROUP_MUL_RINV; GROUP_CONJUGATION_BY_ID]);;

let NORMAL_SUBGROUP_CONJUGATION_SUPERSET = prove
 (`!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !a. a IN group_carrier G ==> h SUBSET IMAGE (group_conjugation G a) h`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[NORMAL_SUBGROUP_CONJUGATION_EQ; SUBSET_REFL];
    SIMP_TAC[NORMAL_SUBGROUP_CONJUGATION] THEN STRIP_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_inv G x:A`) THEN
  ASM_SIMP_TAC[GROUP_INV] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN h ==> g(f x) = x)
    ==> h SUBSET IMAGE f h ==> IMAGE g h SUBSET h`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION_CONJUGATION; GROUP_INV] THEN
  ASM_SIMP_TAC[GROUP_MUL_RINV; GROUP_CONJUGATION_BY_ID]);;

let ABELIAN_GROUP_CONJUGATION = prove
 (`!G a x:A.
        abelian_group G /\ a IN group_carrier G /\ x IN group_carrier G
        ==> group_conjugation G a x = x`,
  SIMP_TAC[GROUP_CONJUGATION_EQ_SELF; abelian_group]);;

let NORMAL_SUBGROUP_OF_INTERS = prove
 (`!G gs. (!g. g IN gs ==> g normal_subgroup_of G) /\ ~(gs = {})
          ==> INTERS gs normal_subgroup_of G`,
  SIMP_TAC[NORMAL_SUBGROUP_CONJUGATION; SUBGROUP_OF_INTERS] THEN SET_TAC[]);;

let NORMAL_SUBGROUP_OF_INTER = prove
 (`!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G
        ==> g INTER h normal_subgroup_of G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC NORMAL_SUBGROUP_OF_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY]);;

let NORMAL_SUBGROUP_ACTION_KERNEL = prove
 (`!G s (a:A->X->X).
        group_action G s a
        ==> {g | g IN group_carrier G /\ !x. x IN s ==> a g x = x}
            normal_subgroup_of G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_ACTION_KERNEL_POINTWISE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[CARRIER_SUBGROUP_OF] THEN
    MATCH_MP_TAC SUBGROUP_OF_INTERS THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUBGROUP_OF_GROUP_STABILIZER];
    X_GEN_TAC `g:A` THEN DISCH_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]THEN
  X_GEN_TAC `h:A` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [group_action]) THEN
  ASM_SIMP_TAC[GROUP_ID; GROUP_INV; GROUP_MUL; group_conjugation] THEN
  ASM_MESON_TAC[GROUP_ACTION_RINV]);;

let NORMAL_SUBGROUP_LEFT_EQ_RIGHT_COSETS = prove
 (`!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        {left_coset G x n |x| x IN group_carrier G} =
        {right_coset G n x |x| x IN group_carrier G}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_subgroup_of] THEN
  ASM_CASES_TAC `(n:A->bool) subgroup_of G` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> {f x | x IN s} = {g x | x IN s}`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> x IN f x /\ x IN g x) /\
      (!x y. x IN s /\ y IN s /\ ~(f x = f y) ==> DISJOINT (f x) (f y)) /\
      {f x | x IN s} = {g x | x IN s}
      ==> !x. x IN s ==> f x = g x`) THEN
    ASM_SIMP_TAC[IN_LEFT_COSET_SELF; IN_RIGHT_COSET_SELF] THEN
    ASM_SIMP_TAC[DISJOINT_LEFT_COSETS]]);;

let NORMAL_SUBGROUP_LEFT_SUBSET_RIGHT_COSETS,
    NORMAL_SUBGROUP_RIGHT_SUBSET_LEFT_COSETS = (CONJ_PAIR o prove)
 (`(!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        {left_coset G x n |x| x IN group_carrier G} SUBSET
        {right_coset G n x |x| x IN group_carrier G}) /\
   (!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\
        {right_coset G n x |x| x IN group_carrier G} SUBSET
        {left_coset G x n |x| x IN group_carrier G})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_LEFT_EQ_RIGHT_COSETS] THEN
  ASM_CASES_TAC `(n:A->bool) subgroup_of G` THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] DIFF_UNIONS_PAIRWISE_DISJOINT)) THEN
  ASM_SIMP_TAC[UNIONS_LEFT_COSETS; UNIONS_RIGHT_COSETS; DIFF_EQ_EMPTY;
    PAIRWISE_DISJOINT_RIGHT_COSETS; PAIRWISE_DISJOINT_LEFT_COSETS] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[EMPTY_UNIONS] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN t ==> ~(P x))
    ==> (!x. x IN t DIFF s ==> P x) ==> t SUBSET s`) THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; LEFT_COSET_NONEMPTY; RIGHT_COSET_NONEMPTY]);;

let NORMAL_SUBGROUP_MUL_SYM = prove
 (`!G h:A->bool.
        h normal_subgroup_of G <=>
        h subgroup_of G /\
        !x y. x IN group_carrier G /\ y IN group_carrier G
              ==> (group_mul G x y IN h <=> group_mul G y x IN h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_subgroup_of] THEN
  ASM_CASES_TAC `(h:A->bool) subgroup_of G` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM FORALL_IN_GROUP_CARRIER_INV] THEN
  TRANS_TAC EQ_TRANS
   `!x y:A. x IN group_carrier G /\ y IN group_carrier G
            ==> (y IN left_coset G (group_inv G x) h <=>
                 y IN right_coset G h (group_inv G x))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`G:A group`; `h:A->bool`] LEFT_COSET) THEN
    MP_TAC(ISPECL [`G:A group`; `h:A->bool`] RIGHT_COSET) THEN
    ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN
    REWRITE_TAC[SUBSET; EXTENSION] THEN MESON_TAC[GROUP_INV];
    ASM_SIMP_TAC[IN_LEFT_COSET_INV; IN_RIGHT_COSET_INV;
                 SUBGROUP_OF_IMP_SUBSET]]);;

let TRIVIAL_NORMAL_SUBGROUP_OF = prove
 (`!G:A group. {group_id G} normal_subgroup_of G`,
  SIMP_TAC[normal_subgroup_of; TRIVIAL_SUBGROUP_OF;
           RIGHT_COSET_TRIVIAL; LEFT_COSET_TRIVIAL]);;

let CARRIER_NORMAL_SUBGROUP_OF = prove
 (`!G:A group. (group_carrier G) normal_subgroup_of G`,
  SIMP_TAC[normal_subgroup_of; CARRIER_SUBGROUP_OF] THEN
  SIMP_TAC[LEFT_COSET_CARRIER; RIGHT_COSET_CARRIER]);;

let GROUP_SETINV_RIGHT_COSET = prove
 (`!G n a:A.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (right_coset G n a) =
            right_coset G n (group_inv G a)`,
  REWRITE_TAC[normal_subgroup_of; left_coset; right_coset] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  TRANS_TAC EQ_TRANS
    `group_setmul G {group_inv G a} (group_setinv G n):A->bool` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[group_setinv; group_setmul;
      SET_RULE `{f x y | P x /\ y IN {a}} = {f x a | P x}`;
      SET_RULE `{f x y | x IN {a} /\ P y} = {f a y | P y}`] THEN
    REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[GROUP_INV_MUL; o_DEF];
    ASM_SIMP_TAC[GROUP_SETINV_SUBGROUP; GROUP_INV]]);;

let GROUP_SETINV_LEFT_COSET = prove
 (`!G n a:A.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_setinv G (left_coset G a n) =
            left_coset G (group_inv G a) n`,
  REWRITE_TAC[LEFT_COSET_OPPOSITE_GROUP] THEN
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETINV] THEN
  SIMP_TAC[GROUP_SETINV_RIGHT_COSET; NORMAL_SUBGROUP_OF_OPPOSITE_GROUP;
           OPPOSITE_GROUP]);;

let GROUP_SETMUL_RIGHT_COSET = prove
 (`!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_setmul G (right_coset G n a) (right_coset G n b) =
            right_coset G n (group_mul G a b)`,
  REWRITE_TAC[normal_subgroup_of; left_coset; right_coset] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[SING_SUBSET;
    MESON[GROUP_SETMUL_ASSOC; GROUP_SETMUL; GROUP_SETINV]
   `a SUBSET group_carrier G /\ b SUBSET group_carrier G /\
    c SUBSET group_carrier G /\ d SUBSET group_carrier G
    ==> group_setmul G (group_setmul G a b) (group_setmul G c d) =
        group_setmul G a (group_setmul G (group_setmul G b c) d)`] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_SUBGROUP] THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_mul G a b:A`) THEN
  ASM_SIMP_TAC[GROUP_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; SING_SUBSET; GROUP_SETMUL_SING]);;

let GROUP_SETMUL_LEFT_COSET = prove
 (`!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_setmul G (left_coset G a n) (left_coset G b n) =
            left_coset G (group_mul G a b) n`,
  REWRITE_TAC[LEFT_COSET_OPPOSITE_GROUP] THEN
  ONCE_REWRITE_TAC[GSYM OPPOSITE_GROUP_SETMUL] THEN
  SIMP_TAC[GROUP_SETMUL_RIGHT_COSET; NORMAL_SUBGROUP_OF_OPPOSITE_GROUP;
           OPPOSITE_GROUP]);;

let CROSS_NORMAL_SUBGROUP_OF_PROD_GROUP = prove
 (`!(G1:A group) (G2:B group) h1 h2.
        (h1 CROSS h2) normal_subgroup_of (prod_group G1 G2) <=>
        h1 normal_subgroup_of G1 /\ h2 normal_subgroup_of G2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_subgroup_of] THEN
  REWRITE_TAC[FORALL_PAIR_THM; RIGHT_COSET_PROD_GROUP; LEFT_COSET_PROD_GROUP;
    CROSS_SUBGROUP_OF_PROD_GROUP; CROSS_EQ; PROD_GROUP; IN_CROSS] THEN
  ASM_CASES_TAC `(h1:A->bool) subgroup_of G1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(h2:B->bool) subgroup_of G2` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RIGHT_COSET_NONEMPTY; LEFT_COSET_NONEMPTY] THEN
  MESON_TAC[GROUP_ID]);;

let NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED_GEN = prove
 (`!G s h:A->bool.
        h normal_subgroup_of G /\
        h SUBSET group_carrier(subgroup_generated G s)
        ==> h normal_subgroup_of (subgroup_generated G s)`,
  SIMP_TAC[normal_subgroup_of; SUBGROUP_OF_SUBGROUP_GENERATED_EQ] THEN
  SIMP_TAC[LEFT_COSET_SUBGROUP_GENERATED; RIGHT_COSET_SUBGROUP_GENERATED] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]);;

let NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED = prove
 (`!G s h:A->bool.
        h normal_subgroup_of G /\ h SUBSET s
        ==> h normal_subgroup_of (subgroup_generated G s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED_GEN THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH rand SUBGROUP_GENERATED_SUBSET_CARRIER o
    rand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
  ASM_SIMP_TAC[SUBSET_INTER; NORMAL_SUBGROUP_IMP_SUBGROUP;
               SUBGROUP_OF_IMP_SUBSET]);;

let GROUP_SETMUL_NORMAL_SUBGROUP_LEFT = prove
 (`!G n h:A->bool.
        n normal_subgroup_of G /\ h subgroup_of G
        ==> group_setmul G n h subgroup_of G`,
  REWRITE_TAC[normal_subgroup_of; left_coset; right_coset] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUBGROUP_SETMUL_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_setmul; subgroup_of]) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[group_setmul] THEN MATCH_MP_TAC(SET_RULE
  `(!x. x IN s ==> {f x y | y IN t} = {f y x | y IN t})
    ==> {f x y | x IN s /\ y IN t} = {f y x | y IN t /\ x IN s}`) THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  REWRITE_TAC[group_setmul; IN_SING] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC EQ_IMP THEN BINOP_TAC] THEN
  ASM SET_TAC[]);;

let GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT = prove
 (`!G h n:A->bool.
        h subgroup_of G /\ n normal_subgroup_of G
        ==> group_setmul G h n subgroup_of G`,
  REWRITE_TAC[normal_subgroup_of; left_coset; right_coset] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUBGROUP_SETMUL_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_setmul; subgroup_of]) THEN
  REWRITE_TAC[group_setmul] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> {f x y | y IN t} = {f y x | y IN t})
    ==> {f x y | x IN s /\ y IN t} = {f y x | y IN t /\ x IN s}`) THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  REWRITE_TAC[group_setmul; IN_SING] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC EQ_IMP THEN BINOP_TAC] THEN
  ASM SET_TAC[]);;

let GROUP_SETMUL_NORMAL_SUBGROUP = prove
 (`!G h k:A->bool.
        h normal_subgroup_of G /\ k normal_subgroup_of G
        ==> group_setmul G h k normal_subgroup_of G`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT; left_coset; right_coset;
               normal_subgroup_of; NORMAL_SUBGROUP_IMP_SUBGROUP] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [normal_subgroup_of])) THEN
  REWRITE_TAC[subgroup_of; left_coset; right_coset] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o CONJUNCT1) ASSUME_TAC)) THEN
  ASM_MESON_TAC[GROUP_SETMUL_ASSOC; SING_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Congugate subgroups, or more generally subsets.                           *)
(* ------------------------------------------------------------------------- *)

let group_conjugate = new_definition
 `group_conjugate (G:A group) s t <=>
        s SUBSET group_carrier G /\
        t SUBSET group_carrier G /\
        ?a. a IN group_carrier G /\ IMAGE (group_conjugation G a) s = t`;;

let GROUP_CONJUGATE_REFL = prove
 (`!G s:A->bool.
        group_conjugate G s s <=> s SUBSET group_carrier G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_conjugate] THEN
  MESON_TAC[GROUP_ID; IMAGE_GROUP_CONJUGATION_BY_ID]);;

let GROUP_CONJUGATE_SYM = prove
 (`!G s t:A->bool. group_conjugate G s t <=> group_conjugate G t s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_conjugate] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [GSYM EXISTS_IN_GROUP_CARRIER_INV] THEN
  MESON_TAC[IMAGE_GROUP_CONJUGATION_BY_INV]);;

let GROUP_CONJUGATE_TRANS = prove
 (`!G s t u:A->bool.
        group_conjugate G s t /\ group_conjugate G t u
        ==> group_conjugate G s u`,
  REWRITE_TAC[group_conjugate] THEN
  MESON_TAC[GROUP_MUL; IMAGE_GROUP_CONJUGATION_BY_MUL]);;

let GROUP_CONJUGATE_SUBGROUPS_GENERATED = prove
 (`!G s t:A->bool.
        group_conjugate G s t
        ==> group_conjugate G (group_carrier(subgroup_generated G s))
                              (group_carrier(subgroup_generated G t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_conjugate] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:A` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_CONJUGATION]);;

let GROUP_CONJUGATE_IMP_ISOMORPHIC = prove
 (`!G s t:A->bool.
      group_conjugate G s t
      ==> (subgroup_generated G s) isomorphic_group (subgroup_generated G t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_conjugate; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `group_conjugation G (a:A)` THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_BETWEEN_SUBGROUPS THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_CONJUGATION]);;

let GROUP_CONJUGATE_IMP_CARD_EQ = prove
 (`!G s t:A->bool. group_conjugate G s t ==> s =_c t`,
  REWRITE_TAC[group_conjugate] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN
  ASM_MESON_TAC[GROUP_CONJUGATION_EQ; SUBSET]);;

let GROUP_ORBIT_CONJUGATE_STABILIZERS = prove
 (`!G s (a:A->X->X) x y.
      group_action G s a /\ group_orbit G s a x y
      ==> group_conjugate G (group_stabilizer G a x) (group_stabilizer G a y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_orbit] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `g:A` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[group_conjugate; GROUP_STABILIZER_SUBSET_CARRIER] THEN
  ASM_MESON_TAC[GROUP_STABILIZER_OF_ACTION]);;

let CARD_EQ_GROUP_ORBIT_STABILIZERS = prove
 (`!G s (a:A->X->X) x y.
        group_action G s a /\ group_orbit G s a x y
        ==> group_stabilizer G a x =_c group_stabilizer G a y`,
  MESON_TAC[GROUP_ORBIT_CONJUGATE_STABILIZERS; GROUP_CONJUGATE_IMP_CARD_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Centralizer and normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

let group_centralizer = new_definition
 `group_centralizer G s =
        {x:A | x IN group_carrier G /\
               !y. y IN group_carrier G /\ y IN s
                   ==> group_mul G x y = group_mul G y x}`;;

let group_normalizer = new_definition
 `group_normalizer G s =
        {x:A | x IN group_carrier G /\
               group_setmul G {x} (group_carrier G INTER s) =
               group_setmul G (group_carrier G INTER s) {x}}`;;

let GROUP_CENTRALIZER = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_centralizer G s =
             {x | x IN group_carrier G /\
                  !y. y IN s ==> group_mul G x y = group_mul G y x}`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_NORMALIZER = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_normalizer G s =
             {x | x IN group_carrier G /\
                  group_setmul G {x} s = group_setmul G s {x}}`,
  SIMP_TAC[group_normalizer; SET_RULE `s SUBSET u ==> u INTER s = s`]);;

let GROUP_NORMALIZER_CONJUGATION_EQ = prove
 (`!G s:A->bool.
        group_normalizer G s =
             {x | x IN group_carrier G /\
                  IMAGE (group_conjugation G x) (group_carrier G INTER s) =
                  (group_carrier G INTER s)}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[group_normalizer; IN_ELIM_THM] THEN
  MESON_TAC[IMAGE_GROUP_CONJUGATION_EQ; INTER_SUBSET]);;

let GROUP_NORMALIZER_CONJUGATION = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_normalizer G s =
            {x | x IN group_carrier G /\ IMAGE (group_conjugation G x) s = s}`,
  SIMP_TAC[GROUP_NORMALIZER_CONJUGATION_EQ; SET_RULE
   `s SUBSET u ==> u INTER s = s`]);;

let GROUP_NORMALIZER_FINITE = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G /\ FINITE s
        ==> group_normalizer G s =
            {x | x IN group_carrier G /\
                 IMAGE (group_conjugation G x) s SUBSET s}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_NORMALIZER_CONJUGATION] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `a:A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_MESON_TAC[GROUP_CONJUGATION_EQ; SUBSET]);;

let GROUP_CENTRALIZER_RESTRICT = prove
 (`!G s:A->bool.
        group_centralizer G s =
        group_centralizer G (group_carrier G INTER s)`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_NORMALIZER_RESTRICT = prove
 (`!G s:A->bool.
        group_normalizer G s =
        group_normalizer G (group_carrier G INTER s)`,
  REWRITE_TAC[group_normalizer; SET_RULE `u INTER u INTER s = u INTER s`]);;

let GROUP_CENTRALIZER_SUBSET_CARRIER = prove
 (`!G s:A->bool. group_centralizer G s SUBSET group_carrier G`,
  REWRITE_TAC[group_centralizer; SUBSET_RESTRICT]);;

let GROUP_NORMALIZER_SUBSET_CARRIER = prove
 (`!G s:A->bool. group_normalizer G s SUBSET group_carrier G`,
  REWRITE_TAC[group_normalizer; SUBSET_RESTRICT]);;

let FINITE_GROUP_CENTRALIZER = prove
 (`!(G:A group) s. FINITE(group_carrier G) ==> FINITE(group_centralizer G s)`,
  MESON_TAC[FINITE_SUBSET; GROUP_CENTRALIZER_SUBSET_CARRIER]);;

let FINITE_GROUP_NORMALIZER = prove
 (`!(G:A group) s. FINITE(group_carrier G) ==> FINITE(group_normalizer G s)`,
  MESON_TAC[FINITE_SUBSET; GROUP_NORMALIZER_SUBSET_CARRIER]);;

let GROUP_CENTRALIZER_SUBSET_NORMALIZER = prove
 (`!G s:A->bool. group_centralizer G s SUBSET group_normalizer G s`,
  REWRITE_TAC[group_centralizer; group_normalizer; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_SETMUL_SYM_ELEMENTWISE THEN
  REWRITE_TAC[GROUP_SETMUL_SING] THEN ASM SET_TAC[]);;

let SUBGROUP_GROUP_CENTRALIZER = prove
 (`!G s:A->bool. (group_centralizer G s) subgroup_of G`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_centralizer; subgroup_of; IN_ELIM_THM] THEN
  SIMP_TAC[SUBSET_RESTRICT; GROUP_ID; GROUP_MUL_LID; GROUP_MUL_RID] THEN
  SIMP_TAC[GROUP_INV; GROUP_MUL] THEN
  CONJ_TAC THENL [MESON_TAC[GROUP_COMMUTES_INV]; ALL_TAC] THEN
  SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL] THEN
  SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL] THEN
  SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL]);;

let SUBGROUP_GROUP_NORMALIZER = prove
 (`!G s:A->bool. (group_normalizer G s) subgroup_of G`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GROUP_NORMALIZER_RESTRICT] THEN
  MP_TAC(SET_RULE
   `group_carrier G INTER s SUBSET (group_carrier G:A->bool)`) THEN
  SPEC_TAC(`group_carrier G INTER s:A->bool`,`s:A->bool`) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_NORMALIZER_CONJUGATION] THEN
  REWRITE_TAC[subgroup_of; IN_ELIM_THM; SUBSET_RESTRICT; GROUP_ID] THEN
  ASM_SIMP_TAC[IMAGE_GROUP_CONJUGATION_BY_ID; GROUP_INV; GROUP_MUL] THEN
  ASM_SIMP_TAC[IMAGE_GROUP_CONJUGATION_BY_INV] THEN
  ASM_SIMP_TAC[IMAGE_GROUP_CONJUGATION_BY_MUL]);;

let GROUP_CENTRALIZER_SUBGROUP_GENERATED = prove
 (`!G h s:A->bool.
        s SUBSET h /\ h subgroup_of G
        ==> group_centralizer (subgroup_generated G h) s =
             h INTER group_centralizer G s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET group_carrier G` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[];
    ASM_SIMP_TAC[GROUP_CENTRALIZER; CARRIER_SUBGROUP_GENERATED_SUBGROUP]] THEN
  REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[]);;

let GROUP_NORMALIZER_SUBGROUP_GENERATED = prove
 (`!G h s:A->bool.
        s SUBSET h /\ h subgroup_of G
        ==> group_normalizer (subgroup_generated G h) s =
             h INTER group_normalizer G s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET group_carrier G` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[];
    ASM_SIMP_TAC[GROUP_NORMALIZER; CARRIER_SUBGROUP_GENERATED_SUBGROUP]] THEN
  REWRITE_TAC[GROUP_SETMUL_SUBGROUP_GENERATED] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[]);;

let IN_GROUP_CENTRALIZER_ID = prove
 (`!(G:A group) s. group_id G IN group_centralizer G s`,
  REWRITE_TAC[group_centralizer; IN_ELIM_THM; GROUP_ID] THEN
  SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID]);;

let IN_GROUP_NORMALIZER_ID = prove
 (`!(G:A group) s. group_id G IN group_normalizer G s`,
  MESON_TAC[SUBSET; GROUP_CENTRALIZER_SUBSET_NORMALIZER;
            IN_GROUP_CENTRALIZER_ID]);;

let GROUP_CENTRALIZER_NONEMPTY = prove
 (`!(G:A group) s. ~(group_centralizer G s = {})`,
  MESON_TAC[IN_GROUP_CENTRALIZER_ID; MEMBER_NOT_EMPTY]);;

let GROUP_NORMALIZER_NONEMPTY = prove
 (`!(G:A group) s. ~(group_normalizer G s = {})`,
  MESON_TAC[IN_GROUP_NORMALIZER_ID; MEMBER_NOT_EMPTY]);;

let GROUP_CENTRALIZER_SUBSET = prove
 (`!G s:A->bool.
        s SUBSET group_centralizer G s <=>
        s SUBSET group_carrier G /\
        !a b. a IN s /\ b IN s ==> group_mul G a b = group_mul G b a`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_CENTRALIZER_SUBSET_EQ = prove
 (`!g h:A->bool.
        h subgroup_of G
        ==> (h SUBSET group_centralizer G h <=>
             abelian_group(subgroup_generated G h))`,
  SIMP_TAC[abelian_group; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[GROUP_CENTRALIZER_SUBSET; subgroup_of; SUBGROUP_GENERATED] THEN
  SET_TAC[]);;

let GROUP_CENTRE_EQ_CARRIER = prove
 (`!G:A group.
        group_centralizer G (group_carrier G) = group_carrier G <=>
        abelian_group G`,
  REWRITE_TAC[group_centralizer; abelian_group] THEN SET_TAC[]);;

let GROUP_CENTRALIZER_CENTRALIZER_SUBSET = prove
 (`!G s:A->bool.
        s SUBSET group_centralizer G (group_centralizer G s) <=>
        s SUBSET group_carrier G`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_NORMALIZER_MAXIMAL_GEN = prove
 (`!G h n:A->bool.
        h normal_subgroup_of (subgroup_generated G n) <=>
        h subgroup_of (subgroup_generated G n) /\
        group_carrier G INTER n SUBSET group_normalizer G h`,
  REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION_EQ;
              SUBGROUP_OF_SUBGROUP_GENERATED_EQ] THEN
  SIMP_TAC[GSYM SUBGROUP_GENERATED_MINIMAL_EQ; SUBGROUP_GROUP_NORMALIZER] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(h:A->bool) subgroup_of G` THEN
  ASM_SIMP_TAC[GROUP_NORMALIZER_CONJUGATION; SUBGROUP_OF_IMP_SUBSET;
               GROUP_CONJUGATION_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SET_RULE
    `s SUBSET {x | x IN t /\ Q x} <=> s SUBSET t /\ !x. x IN s ==> Q x`]);;

let GROUP_NORMALIZER_MAXIMAL = prove
 (`!G h n:A->bool.
        n subgroup_of G
        ==> (h normal_subgroup_of (subgroup_generated G n) <=>
             h subgroup_of G /\ h SUBSET n /\ n SUBSET group_normalizer G h)`,
  SIMP_TAC[GROUP_NORMALIZER_MAXIMAL_GEN; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
           SUBGROUP_OF_SUBGROUP_GENERATED_EQ; SUBGROUP_OF_IMP_SUBSET;
           SET_RULE `s SUBSET t ==> t INTER s = s`] THEN
  MESON_TAC[]);;

let NORMAL_SUBGROUP_NORMALIZER_CONTAINS_CARRIER = prove
 (`!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\ group_carrier G SUBSET group_normalizer G n`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`G:A group`; `n:A->bool`; `group_carrier G:A->bool`]
        GROUP_NORMALIZER_MAXIMAL) THEN
  REWRITE_TAC[SUBGROUP_GENERATED_GROUP_CARRIER; CARRIER_SUBGROUP_OF] THEN
  MESON_TAC[SUBGROUP_OF_IMP_SUBSET]);;

let NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER = prove
 (`!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\ group_normalizer G n = group_carrier G`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; GROUP_NORMALIZER_SUBSET_CARRIER] THEN
  REWRITE_TAC[NORMAL_SUBGROUP_NORMALIZER_CONTAINS_CARRIER]);;

let GROUP_NORMALIZER_SUBSET = prove
 (`!G h:A->bool.
        h subgroup_of G ==> h SUBSET group_normalizer G h`,
  SIMP_TAC[GROUP_NORMALIZER_CONJUGATION; SUBGROUP_OF_IMP_SUBSET] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IMAGE_GROUP_CONJUGATION_SUBGROUP] THEN
  SIMP_TAC[subgroup_of; SUBSET]);;

let NORMAL_SUBGROUP_OF_NORMALIZER = prove
 (`!G h:A->bool.
        h normal_subgroup_of (subgroup_generated G (group_normalizer G h)) <=>
        h subgroup_of G`,
  SIMP_TAC[GROUP_NORMALIZER_MAXIMAL; SUBGROUP_GROUP_NORMALIZER] THEN
  REWRITE_TAC[SUBSET_REFL; TAUT `(p /\ q <=> p) <=> p ==> q`] THEN
  REWRITE_TAC[GROUP_NORMALIZER_SUBSET]);;

let GROUP_CENTRALIZER_POINTWISE = prove
 (`!G s:A->bool.
        group_centralizer G s =
        if s = {} then group_carrier G
        else INTERS {group_centralizer G {x} | x IN s}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[group_centralizer; NOT_IN_EMPTY; IN_GSPEC] THEN
  REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_SING] THEN ASM SET_TAC[]);;

let GROUP_CENTRALIZER_ALT = prove
 (`!G s:A->bool.
        group_centralizer G s =
         {x | x IN group_carrier G /\
              !y. y IN group_carrier G /\ y IN s
                  ==> group_conjugation G x y = y}`,
  REWRITE_TAC[group_centralizer; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[GROUP_CONJUGATION_EQ_SELF]);;

let NORMAL_SUBGROUP_CENTRALIZER_NORMALIZER = prove
 (`!G h:A->bool.
        group_centralizer G h normal_subgroup_of
        subgroup_generated G (group_normalizer G h)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GROUP_CENTRALIZER_RESTRICT; GROUP_NORMALIZER_RESTRICT] THEN
  MP_TAC(SET_RULE
  `group_carrier G INTER (h:A->bool) SUBSET group_carrier G`) THEN
  SPEC_TAC(`group_carrier G INTER (h:A->bool)`,`h:A->bool`) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION] THEN
  REWRITE_TAC[GROUP_CONJUGATION_SUBGROUP_GENERATED] THEN
  SIMP_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ;
           SUBGROUP_GROUP_CENTRALIZER; SUBGROUP_GROUP_NORMALIZER;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP;
           GROUP_CENTRALIZER_SUBSET_NORMALIZER] THEN
  ASM_SIMP_TAC[GROUP_CENTRALIZER_ALT; GROUP_NORMALIZER_CONJUGATION] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[GROUP_CONJUGATION] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [group_conjugation] THEN
  ASM_SIMP_TAC[GSYM GROUP_CONJUGATION_CONJUGATION; GROUP_MUL; GROUP_INV] THEN
  MATCH_MP_TAC(MESON[]
   `f(h y) = y /\ g(h y) = h y ==> f(g(h y)) = y`) THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION_RINV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[GROUP_CONJUGATION; GROUP_INV] THEN UNDISCH_TAC `(y:A) IN h` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN FIRST_X_ASSUM (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  ASM_SIMP_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM; GROUP_CONJUGATION_LINV]);;

let NORMAL_SUBGROUP_CENTRALIZER = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_centralizer G n normal_subgroup_of G`,
  MESON_TAC[NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER;
            SUBGROUP_GENERATED_GROUP_CARRIER;
            NORMAL_SUBGROUP_CENTRALIZER_NORMALIZER]);;

let GROUP_NORMALIZER_SING = prove
 (`!G a:A. group_normalizer G {a} = group_centralizer G {a}`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GROUP_NORMALIZER_RESTRICT; GROUP_CENTRALIZER_RESTRICT] THEN
  REWRITE_TAC[group_normalizer; group_centralizer] THEN
  ASM_CASES_TAC `(a:A) IN group_carrier G` THENL
   [ASM_SIMP_TAC[GROUP_SETMUL_SING;
                 SET_RULE `a IN s ==> s INTER {a} = {a}`] THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> s INTER {a} = {}`; NOT_IN_EMPTY;
                 INTER_EMPTY; GROUP_SETMUL_EMPTY]]);;

let GROUP_CENTRALIZER_GALOIS_EQ = prove
 (`!G s t:A->bool.
        s SUBSET group_carrier G /\ t SUBSET group_carrier G
        ==> (s SUBSET group_centralizer G t <=>
             t SUBSET group_centralizer G s)`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_CENTRALIZER_GALOIS = prove
 (`!G s t:A->bool.
        s SUBSET group_carrier G /\ t SUBSET group_centralizer G s
        ==> s SUBSET group_centralizer G t`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_CENTRALIZER_MONO = prove
 (`!G s t:A->bool.
        s SUBSET t ==> group_centralizer G t SUBSET group_centralizer G s`,
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let GROUP_ACTION_CONJUGATION_NORMAL_SUBGROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_action G n (group_conjugation G)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ACTION_ON_SUBSET THEN
  EXISTS_TAC `group_carrier G:A->bool` THEN
  REWRITE_TAC[GROUP_ACTION_CONJUGATION] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NORMAL_SUBGROUP_CONJUGATION]) THEN
  SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN SET_TAC[]);;

let GROUP_STABILIZER_CONJUGATION = prove
 (`!G a:A.
     a IN group_carrier G
     ==> group_stabilizer G (group_conjugation G) a =
         group_centralizer G {a}`,
  REWRITE_TAC[group_stabilizer; group_centralizer; IN_SING] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[GROUP_CONJUGATION_EQ_SELF]);;

let GROUP_ORBIT_CONJUGATION_GEN = prove
 (`!G s x:A.
        s SUBSET group_carrier G
        ==> group_orbit G s (group_conjugation G) x =
            if x IN s then {y | y IN s /\ group_conjugate G {x} {y}} else {}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_GROUP_ORBIT; group_conjugate] THEN
  ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES] THEN
  REWRITE_TAC[SET_RULE `{a} = {b} <=> a = b`] THEN ASM SET_TAC[]);;

let GROUP_ORBIT_CONJUGATION = prove
 (`!G x:A.
        group_orbit G (group_carrier G) (group_conjugation G) x =
        if x IN group_carrier G
        then {y | y IN group_carrier G /\ group_conjugate G {x} {y}}
        else {}`,
  SIMP_TAC[GROUP_ORBIT_CONJUGATION_GEN; SUBSET_REFL]);;

let GROUP_ACTION_IMAGE_CONJUGATION = prove
 (`!G u:(A->bool)->bool.
        (!t. t IN u ==> t SUBSET group_carrier G) /\
        (!g t. g IN group_carrier G /\ t IN u
               ==> IMAGE (group_conjugation G g) t IN u)
        ==> group_action G u (IMAGE o group_conjugation G)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ACTION_IMAGE THEN
  EXISTS_TAC `group_carrier G:A->bool` THEN
  ASM_REWRITE_TAC[GROUP_ACTION_CONJUGATION]);;

let GROUP_STABILIZER_IMAGE_CONJUGATION = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> group_stabilizer G (IMAGE o group_conjugation G) s =
            group_normalizer G s`,
  SIMP_TAC[GROUP_NORMALIZER_CONJUGATION; group_stabilizer; o_THM]);;

let GROUP_ACTION_IMAGE_CONJUGATION_CARRIER = prove
 (`!G:A group. group_action G {s | s SUBSET group_carrier G}
                              (IMAGE o group_conjugation G)`,
  GEN_TAC THEN MATCH_MP_TAC GROUP_ACTION_IMAGE_CONJUGATION THEN
  REWRITE_TAC[IN_ELIM_THM; IMAGE_GROUP_CONJUGATION_SUBSET]);;

let GROUP_ACTION_IMAGE_CONJUGATION_SUBGROUPS = prove
 (`!G:A group. group_action G {n | n subgroup_of G}
                              (IMAGE o group_conjugation G)`,
  GEN_TAC THEN MATCH_MP_TAC GROUP_ACTION_IMAGE_CONJUGATION THEN
  REWRITE_TAC[IN_ELIM_THM; SUBGROUP_OF_IMP_SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_IMAGE THEN
  ASM_MESON_TAC[GROUP_HOMOMORPHISM_CONJUGATION]);;

let GROUP_ORBIT_IMAGE_CONJUGATION = prove
 (`!G. group_orbit G {s | s SUBSET group_carrier G}
                     (IMAGE o group_conjugation G) =
       group_conjugate G`,
  REWRITE_TAC[FUN_EQ_THM; group_orbit; group_conjugate; IN_ELIM_THM; o_THM]);;

let GROUP_ORBIT_IMAGE_CONJUGATION_GEN = prove
 (`!G u s:A->bool.
        (!t. t IN u ==> t SUBSET group_carrier G) /\ s IN u
        ==> group_orbit G u (IMAGE o group_conjugation G) s =
            \t. t IN u /\ group_conjugate G s t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  REWRITE_TAC[group_orbit; group_conjugate; o_THM] THEN ASM SET_TAC[]);;

let CARD_CONJUGATE_SUBSETS_MUL_GEN = prove
 (`!G s:A->bool.
        s SUBSET group_carrier G
        ==> {t | group_conjugate G s t} *_c group_normalizer G s =_c
            group_carrier G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE `{t | P t} = P`] THEN
  ASM_SIMP_TAC[GSYM GROUP_STABILIZER_IMAGE_CONJUGATION; ETA_AX] THEN
  ASM_SIMP_TAC[GSYM GROUP_ORBIT_IMAGE_CONJUGATION] THEN
  MATCH_MP_TAC ORBIT_STABILIZER_MUL_GEN THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; GROUP_CONJUGATE_REFL] THEN
  MATCH_MP_TAC GROUP_ACTION_IMAGE_CONJUGATION THEN
  SIMP_TAC[IN_ELIM_THM; IMAGE_GROUP_CONJUGATION_SUBSET]);;

let CARD_CONJUGATE_SUBSETS_MUL = prove
 (`!G s:A->bool.
        FINITE(group_carrier G) /\ s SUBSET group_carrier G
        ==> CARD {t | group_conjugate G s t} * CARD(group_normalizer G s) =
            CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CARD_CONJUGATE_SUBSETS_MUL_GEN) THEN
  FIRST_ASSUM(MP_TAC o GSYM o
    MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_CARD_IMP)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARD_FINITE_CONG) THEN
  ASM_REWRITE_TAC[CARD_MUL_FINITE_EQ] THEN REWRITE_TAC[mul_c; GSYM CROSS] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CROSS_EMPTY; CARD_CLAUSES; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[CARD_CROSS]);;

let CARD_CONJUGATE_SUBSETS = prove
 (`!G s:A->bool.
        FINITE(group_carrier G) /\ s SUBSET group_carrier G
        ==> CARD {t | group_conjugate G s t} =
            CARD(group_carrier G) DIV CARD(group_normalizer G s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CARD_CONJUGATE_SUBSETS_MUL) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC DIV_MULT THEN
  ASM_SIMP_TAC[CARD_EQ_0; FINITE_GROUP_NORMALIZER;
               GROUP_NORMALIZER_NONEMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Quotient groups.                                                          *)
(* ------------------------------------------------------------------------- *)

let quotient_group = new_definition
 `quotient_group G (n:A->bool) =
        group ({right_coset G n x |x| x IN group_carrier G},
               n,group_setinv G,group_setmul G)`;;

let QUOTIENT_GROUP = prove
 (`(!G n:A->bool.
        n normal_subgroup_of G
        ==> group_carrier(quotient_group G n) =
              {right_coset G n x |x| x IN group_carrier G}) /\
   (!G n:A->bool.
        n normal_subgroup_of G
        ==> group_id(quotient_group G n) = n) /\
   (!G n:A->bool.
        n normal_subgroup_of G
        ==> group_inv(quotient_group G n) = group_setinv G) /\
   (!G n:A->bool.
        n normal_subgroup_of G
        ==> group_mul(quotient_group G n) = group_setmul G)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl quotient_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM quotient_group] THEN ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[group_carrier; group_id; group_inv; group_mul]] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_RIGHT_COSET; GROUP_SETINV_RIGHT_COSET;
               GROUP_MUL; GROUP_INV] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[normal_subgroup_of]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[RIGHT_COSET_ID; GROUP_ID];
    ASM_MESON_TAC[GROUP_INV];
    ASM_MESON_TAC[GROUP_MUL];
    ASM_SIMP_TAC[GROUP_MUL_ASSOC];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[right_coset; GROUP_SETMUL_ASSOC; SING_SUBSET];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[left_coset; GSYM GROUP_SETMUL_ASSOC; SING_SUBSET]] THEN
    ASM_SIMP_TAC[GROUP_SETMUL_SUBGROUP];
    ASM_SIMP_TAC[GROUP_MUL_LINV; GROUP_MUL_RINV; RIGHT_COSET_ID]]);;

let ABELIAN_QUOTIENT_GROUP = prove
 (`!G n:A->bool.
     abelian_group G /\ n subgroup_of G ==> abelian_group(quotient_group G n)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[abelian_group; QUOTIENT_GROUP; ABELIAN_GROUP_NORMAL_SUBGROUP;
               IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_SYM; RIGHT_COSET; SUBGROUP_OF_IMP_SUBSET]);;

let FINITE_QUOTIENT_GROUP = prove
 (`!G n:A->bool.
        FINITE(group_carrier G) /\ n normal_subgroup_of G
        ==> FINITE(group_carrier(quotient_group G n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[QUOTIENT_GROUP] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE]);;

let TRIVIAL_QUOTIENT_GROUP = prove
 (`!G n:A->bool.
        trivial_group G /\  n normal_subgroup_of G
        ==> trivial_group(quotient_group G n)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [trivial_group] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[TRIVIAL_GROUP; QUOTIENT_GROUP] THEN
  SET_TAC[]);;

let QUOTIENT_GROUP_ID = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_id(quotient_group G n) = n`,
  REWRITE_TAC[QUOTIENT_GROUP]);;

let QUOTIENT_GROUP_INV = prove
 (`!G n a:A.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_inv (quotient_group G n) (right_coset G n a) =
            right_coset G n (group_inv G a)`,
  SIMP_TAC[QUOTIENT_GROUP; GROUP_SETINV_RIGHT_COSET]);;

let QUOTIENT_GROUP_MUL = prove
 (`!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_mul (quotient_group G n)
                      (right_coset G n a) (right_coset G n b) =
            right_coset G n (group_mul G a b)`,
  SIMP_TAC[QUOTIENT_GROUP; GROUP_SETMUL_RIGHT_COSET]);;

let QUOTIENT_GROUP_DIV = prove
 (`!G n a b:A.
        n normal_subgroup_of G /\ a IN group_carrier G /\ b IN group_carrier G
        ==> group_div (quotient_group G n)
                      (right_coset G n a) (right_coset G n b) =
            right_coset G n (group_div G a b)`,
  SIMP_TAC[group_div; QUOTIENT_GROUP_INV; QUOTIENT_GROUP_MUL; GROUP_INV]);;

let QUOTIENT_GROUP_POW = prove
 (`!G n (a:A) k.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_pow (quotient_group G n) (right_coset G n a) k =
            right_coset G n (group_pow G a k)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[group_pow; QUOTIENT_GROUP_MUL; GROUP_POW] THEN
  ASM_SIMP_TAC[QUOTIENT_GROUP_ID; NORMAL_SUBGROUP_IMP_SUBGROUP;
               SUBGROUP_OF_IMP_SUBSET; RIGHT_COSET_ID]);;

let QUOTIENT_GROUP_ZPOW = prove
 (`!G n (a:A) k.
        n normal_subgroup_of G /\ a IN group_carrier G
        ==> group_zpow (quotient_group G n) (right_coset G n a) k =
            right_coset G n (group_zpow G a k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_zpow] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[QUOTIENT_GROUP_INV; QUOTIENT_GROUP_POW; GROUP_POW]);;

let GROUP_HOMOMORPHISM_RIGHT_COSET = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_homomorphism (G,quotient_group G n) (right_coset G n)`,
  SIMP_TAC[group_homomorphism; QUOTIENT_GROUP_INV; QUOTIENT_GROUP_MUL] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; QUOTIENT_GROUP] THEN
  SIMP_TAC[normal_subgroup_of; subgroup_of; RIGHT_COSET_ID] THEN SET_TAC[]);;

let GROUP_EPIMORPHISM_RIGHT_COSET = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_epimorphism (G,quotient_group G n) (right_coset G n)`,
  SIMP_TAC[group_epimorphism; GROUP_HOMOMORPHISM_RIGHT_COSET] THEN
  SIMP_TAC[QUOTIENT_GROUP] THEN SET_TAC[]);;

let CARD_LE_QUOTIENT_GROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_carrier(quotient_group G n) <=_c group_carrier G`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_RIGHT_COSET) THEN
  REWRITE_TAC[CARD_LE_GROUP_EPIMORPHIC_IMAGE]);;

let CARD_QUOTIENT_GROUP_DIVIDES = prove
 (`!G n:A->bool.
        FINITE(group_carrier G) /\ n normal_subgroup_of G
        ==> CARD(group_carrier(quotient_group G n)) divides
            CARD(group_carrier G)`,
  SIMP_TAC[QUOTIENT_GROUP; CARD_RIGHT_COSETS_DIVIDES;
           NORMAL_SUBGROUP_IMP_SUBGROUP]);;

let TRIVIAL_QUOTIENT_GROUP_EQ = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> (trivial_group(quotient_group G n) <=> n = group_carrier G)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[TRIVIAL_GROUP_SUBSET; QUOTIENT_GROUP] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_SING] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
  SIMP_TAC[RIGHT_COSET_EQ_SUBGROUP] THEN
  REWRITE_TAC[subgroup_of] THEN SET_TAC[]);;

let TRIVIAL_QUOTIENT_GROUP_SELF = prove
 (`!G:A group. trivial_group(quotient_group G (group_carrier G))`,
  SIMP_TAC[TRIVIAL_QUOTIENT_GROUP_EQ; CARRIER_NORMAL_SUBGROUP_OF]);;

let QUOTIENT_GROUP_TRIVIAL = prove
 (`!G:A group. quotient_group G {group_id G} isomorphic_group G`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `right_coset G {group_id G:A}` THEN
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; group_monomorphism;
           GROUP_EPIMORPHISM_RIGHT_COSET; GROUP_HOMOMORPHISM_RIGHT_COSET;
           TRIVIAL_SUBGROUP_OF; TRIVIAL_NORMAL_SUBGROUP_OF;
           RIGHT_COSET_EQ; IMP_CONJ; IN_SING; GROUP_DIV_EQ_ID]);;

let GROUP_ISOMORPHISM_PROD_QUOTIENT_GROUP = prove
 (`!(G1:A group) (G2:B group) n1 n2.
        n1 normal_subgroup_of G1 /\ n2 normal_subgroup_of G2
        ==> group_isomorphism(prod_group (quotient_group G1 n1)
                                         (quotient_group G2 n2),
                              quotient_group (prod_group G1 G2) (n1 CROSS n2))
                             (\(s,t). s CROSS t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_ISOMORPHISM] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; SET_RULE
   `(IMAGE f s SUBSET t /\ P) /\ IMAGE f s = t /\ Q <=>
    IMAGE f s SUBSET t /\ t SUBSET IMAGE f s /\ P /\ Q`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] IN_IMAGE] THEN
  ASM_SIMP_TAC[CONJUNCT1 QUOTIENT_GROUP;
               CROSS_NORMAL_SUBGROUP_OF_PROD_GROUP] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  REWRITE_TAC[RIGHT_COSET_PROD_GROUP; PROD_GROUP; IN_CROSS] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[CROSS_EQ; PAIR_EQ; RIGHT_COSET_NONEMPTY;
               NORMAL_SUBGROUP_IMP_SUBGROUP] THEN
  ASM_SIMP_TAC[QUOTIENT_GROUP; CROSS_NORMAL_SUBGROUP_OF_PROD_GROUP] THEN
  REWRITE_TAC[GROUP_SETMUL_PROD_GROUP]);;

let ISOMORPHIC_QUOTIENT_PROD_GROUP = prove
 (`!(G1:A group) (G2:B group) n1 n2.
        n1 normal_subgroup_of G1 /\ n2 normal_subgroup_of G2
        ==> quotient_group (prod_group G1 G2) (n1 CROSS n2) isomorphic_group
            prod_group (quotient_group G1 n1) (quotient_group G2 n2)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_PROD_QUOTIENT_GROUP) THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_IMP_ISOMORPHIC]);;

let CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP = prove
 (`!(G:K->A group) h k.
        (cartesian_product k h) normal_subgroup_of (product_group k G) <=>
        !i. i IN k ==> (h i) normal_subgroup_of (G i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_subgroup_of] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP] THEN
  REWRITE_TAC[RIGHT_COSET_PRODUCT_GROUP; LEFT_COSET_PRODUCT_GROUP] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ; CARTESIAN_PRODUCT_EQ_EMPTY] THEN
  REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  ASM_CASES_TAC `!i. i IN k ==> (h:K->A->bool) i subgroup_of G i` THENL
   [ASM_SIMP_TAC[RIGHT_COSET_NONEMPTY]; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; PRODUCT_GROUP; IMP_IMP] THEN
  REWRITE_TAC[FORALL_CARTESIAN_PRODUCT_ELEMENTS] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ_EMPTY; GROUP_CARRIER_NONEMPTY]);;

let GROUP_ISOMORPHISM_PRODUCT_QUOTIENT_GROUP = prove
 (`!(G:K->A group) n k.
        (!i. i IN k ==> (n i) normal_subgroup_of (G i))
        ==> group_isomorphism
              (product_group k (\i. quotient_group (G i) (n i)),
               quotient_group (product_group k G) (cartesian_product k n))
              (cartesian_product k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_ISOMORPHISM] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; SET_RULE
   `(IMAGE f s SUBSET t /\ P) /\ IMAGE f s = t /\ Q <=>
    IMAGE f s SUBSET t /\ t SUBSET IMAGE f s /\ P /\ Q`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[PRODUCT_GROUP; QUOTIENT_GROUP; RIGHT_COSET_PRODUCT_GROUP;
               CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP;
               GROUP_SETMUL_PRODUCT_GROUP; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ; CARTESIAN_PRODUCT_EQ_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:K->A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; CARTESIAN_PRODUCT_EQ] THEN
    REWRITE_TAC[IN_ELIM_THM; cartesian_product] THEN
    ASM_SIMP_TAC[QUOTIENT_GROUP; IN_ELIM_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:K->A` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    EXISTS_TAC `RESTRICTION k (y:K->A)` THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:K->A` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; CARTESIAN_PRODUCT_EQ] THEN
    REWRITE_TAC[IN_ELIM_THM; cartesian_product] THEN STRIP_TAC THEN EXISTS_TAC
     `RESTRICTION k (\i. right_coset (G i) (n i) (x i)):K->A->bool` THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    ASM_SIMP_TAC[RESTRICTION; QUOTIENT_GROUP] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[IN_ELIM_THM; cartesian_product; RESTRICTION; QUOTIENT_GROUP];
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; cartesian_product; EXTENSIONAL;
                 QUOTIENT_GROUP] THEN
    ASM_MESON_TAC[RIGHT_COSET_EQ_EMPTY; SUBGROUP_OF_IMP_NONEMPTY;
                  normal_subgroup_of]]);;

let ISOMORPHIC_QUOTIENT_PRODUCT_GROUP = prove
 (`!(G:K->A group) n k.
        (!i. i IN k ==> (n i) normal_subgroup_of (G i))
        ==> (quotient_group (product_group k G) (cartesian_product k n))
            isomorphic_group
            (product_group k (\i. quotient_group (G i) (n i)))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_PRODUCT_QUOTIENT_GROUP) THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_IMP_ISOMORPHIC]);;

let SUBGROUP_OF_QUOTIENT_GROUP,SUBGROUP_OF_QUOTIENT_GROUP_ALT =
 (CONJ_PAIR o prove)
 (`(!G n h:(A->bool)->bool.
        n normal_subgroup_of G
        ==> (h subgroup_of quotient_group G n <=>
             ?k. k subgroup_of G /\ { right_coset G n x | x IN k} = h)) /\
   (!G n h:(A->bool)->bool.
        n normal_subgroup_of G
        ==> (h subgroup_of quotient_group G n <=>
             ?k. k subgroup_of G /\
                 n SUBSET k /\
                 { right_coset G n x | x IN k} = h))`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
    `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> q) /\ (p ==> r) /\ (q ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    DISCH_TAC THEN
    EXISTS_TAC `{x:A | x IN group_carrier G /\ right_coset G n x IN h}` THEN
    MATCH_MP_TAC(TAUT `q /\ p /\ r ==> p /\ q /\ r`) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP IN_SUBGROUP_ID) THEN
      MATCH_MP_TAC(SET_RULE
       `n SUBSET {x | x IN s /\ f x = z}
        ==> z IN h ==> n SUBSET {x | x IN s /\ f x IN h}`) THEN
      ASM_SIMP_TAC[QUOTIENT_GROUP; SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RIGHT_COSET_EQ_SUBGROUP; normal_subgroup_of;
                    subgroup_of; SUBSET];
      REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBGROUP_OF_EPIMORPHIC_PREIMAGE THEN
      EXISTS_TAC `quotient_group (G:A group) n` THEN
      ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET; ETA_AX]];
    DISCH_THEN(X_CHOOSE_THEN `k:A->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC `G:A group` THEN
    ASM_SIMP_TAC[GROUP_HOMOMORPHISM_RIGHT_COSET; ETA_AX]]);;

let SUBGROUP_OF_QUOTIENT_GROUP_GENERATED_BY = prove
 (`!G n h:(A->bool)->bool.
        n normal_subgroup_of G /\ h subgroup_of quotient_group G n
        ==> ?k. k subgroup_of G /\ n SUBSET k /\
                quotient_group (subgroup_generated G k) n =
                subgroup_generated (quotient_group G n) h`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC
   `h:(A->bool)->bool` o  MATCH_MP SUBGROUP_OF_QUOTIENT_GROUP_ALT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GROUPS_EQ] THEN
  ASM_SIMP_TAC[QUOTIENT_GROUP; CONJUNCT2 SUBGROUP_GENERATED;
               NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED;
               CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  ASM_REWRITE_TAC[GROUP_SETINV_SUBGROUP_GENERATED;
                  GROUP_SETMUL_SUBGROUP_GENERATED;
                  RIGHT_COSET_SUBGROUP_GENERATED]);;

let QUOTIENT_GROUP_SUBGROUP_GENERATED = prove
 (`!G h n:A->bool.
        n normal_subgroup_of G /\ h subgroup_of G /\ n SUBSET h
        ==> quotient_group (subgroup_generated G h) n =
            subgroup_generated (quotient_group G n)
                               {right_coset G n x | x IN h}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUPS_EQ; QUOTIENT_GROUP; CONJUNCT2 SUBGROUP_GENERATED;
               NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[GROUP_SETINV_SUBGROUP_GENERATED; GROUP_SETMUL_SUBGROUP_GENERATED;
              RIGHT_COSET_SUBGROUP_GENERATED] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_RIGHT_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBGROUP_OF_HOMOMORPHIC_IMAGE)) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; SIMPLE_IMAGE; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Kernels and images of homomorphisms.                                      *)
(* ------------------------------------------------------------------------- *)

let group_kernel = new_definition
 `group_kernel (G,G') (f:A->B) =
    {x | x IN group_carrier G /\ f x = group_id G'}`;;

let group_image = new_definition
 `group_image (G:A group,G':B group) (f:A->B) = IMAGE f (group_carrier G)`;;

let GROUP_KERNEL_ID = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> group_id G IN group_kernel (G,G') f`,
  SIMP_TAC[group_homomorphism; group_kernel; IN_ELIM_THM; GROUP_ID]);;

let GROUP_KERNEL_NONEMPTY = prove
 (`!G H (f:A->B).
        group_homomorphism(G,H) f ==> ~(group_kernel(G,H) f = {})`,
  MESON_TAC[GROUP_KERNEL_ID; NOT_IN_EMPTY]);;

let GROUP_KERNEL_SUBSET_CARRIER = prove
 (`!G H (f:A->B). group_kernel(G,H) f SUBSET group_carrier G`,
  REWRITE_TAC[group_kernel; SUBSET_RESTRICT]);;

let GROUP_MONOMORPHISM = prove
 (`!G G' (f:A->B).
        group_monomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_kernel (G,G') f = {group_id G}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_monomorphism] THEN
  REWRITE_TAC[TAUT `(p /\ q <=> p /\ r) <=> p ==> (q <=> r)`] THEN
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SING_SUBSET] THEN
  ASM_REWRITE_TAC[SUBSET; IN_SING; group_kernel; IN_ELIM_THM; GROUP_ID] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `group_id G:A`]) THEN
    ASM_SIMP_TAC[GROUP_ID];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `group_div G x y:A`) THEN
    ASM_SIMP_TAC[group_div; GROUP_MUL; GROUP_INV] THEN
    REWRITE_TAC[GSYM group_div] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_DIV_EQ_ID o
      rand o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_DIV_EQ_ID o snd) THEN
    ASM_SIMP_TAC[]]);;

let GROUP_MONOMORPHISM_ALT = prove
 (`!G G' (f:A->B).
        group_monomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        !x. x IN group_carrier G /\ f x = group_id G' ==> x = group_id G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GROUP_MONOMORPHISM; group_kernel] THEN
  MP_TAC(ISPEC `G:A group` GROUP_ID) THEN
  REWRITE_TAC[group_homomorphism] THEN SET_TAC[]);;

let GROUP_MONOMORPHISM_ALT_EQ = prove
 (`!G G' f:A->B.
        group_monomorphism (G,G') f <=>
        group_homomorphism (G,G') f /\
        !x. x IN group_carrier G ==> (f x = group_id G' <=> x = group_id G)`,
  MESON_TAC[GROUP_MONOMORPHISM_ALT; group_homomorphism]);;

let GROUP_EPIMORPHISM = prove
 (`!G G' (f:A->B).
        group_epimorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_image (G,G') f = group_carrier G'`,
  REWRITE_TAC[group_epimorphism; group_image] THEN MESON_TAC[]);;

let GROUP_EPIMORPHISM_ALT = prove
 (`!G G' (f:A->B).
        group_epimorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_carrier G' SUBSET group_image (G,G') f`,
  REWRITE_TAC[GROUP_EPIMORPHISM; group_homomorphism; group_image] THEN
  MESON_TAC[SUBSET_ANTISYM_EQ]);;

let GROUP_ISOMORPHISM_GROUP_KERNEL_GROUP_IMAGE = prove
 (`!G G' (f:A->B).
        group_isomorphism (G,G') f <=>
        group_homomorphism(G,G') f /\
        group_kernel (G,G') f = {group_id G} /\
        group_image (G,G') f = group_carrier G'`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[GROUP_MONOMORPHISM; GROUP_EPIMORPHISM] THEN MESON_TAC[]);;

let GROUP_ISOMORPHISM_ALT = prove
 (`!G G' (f:A->B).
      group_isomorphism (G,G') f <=>
      IMAGE f (group_carrier G) = group_carrier G' /\
      (!x y. x IN group_carrier G /\ y IN group_carrier G
             ==> f(group_mul G x y) = group_mul G' (f x) (f y)) /\
      (!x. x IN group_carrier G /\ f x = group_id G' ==> x = group_id G)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `group_homomorphism (G,G') (f:A->B)` THENL
   [ALL_TAC;
    ASM_MESON_TAC[GROUP_HOMOMORPHISM; GROUP_ISOMORPHISM; SUBSET_REFL]] THEN
  ASM_REWRITE_TAC[GROUP_ISOMORPHISM_GROUP_KERNEL_GROUP_IMAGE;
                  group_kernel; group_image] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN
  MP_TAC(ISPEC `G:A group` GROUP_ID) THEN ASM SET_TAC[]);;

let SUBGROUP_GROUP_KERNEL = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f ==> (group_kernel (G,G') f) subgroup_of G`,
  SIMP_TAC[group_homomorphism; subgroup_of; group_kernel; IN_ELIM_THM; SUBSET;
           FORALL_IN_IMAGE; GROUP_MUL_LID; GROUP_ID; GROUP_MUL;
           GROUP_INV_ID; GROUP_INV]);;

let SUBGROUP_GROUP_IMAGE = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f ==> (group_image (G,G') f) subgroup_of G'`,
  SIMP_TAC[group_homomorphism; subgroup_of; group_image; SUBSET;
           FORALL_IN_IMAGE; FORALL_IN_IMAGE_2; IN_IMAGE] THEN
  MESON_TAC[GROUP_MUL; GROUP_INV; GROUP_ID]);;

let GROUP_KERNEL_TO_SUBGROUP_GENERATED = prove
 (`!G H s (f:A->B).
        group_kernel (G,subgroup_generated H s) f = group_kernel(G,H) f`,
  REWRITE_TAC[group_kernel; SUBGROUP_GENERATED]);;

let GROUP_IMAGE_TO_SUBGROUP_GENERATED = prove
 (`!G H s (f:A->B).
        group_image (G,subgroup_generated H s) f = group_image(G,H) f`,
  REWRITE_TAC[group_image]);;

let GROUP_KERNEL_FROM_SUBGROUP_GENERATED = prove
 (`!G H s f:A->B.
        s subgroup_of G
        ==> group_kernel(subgroup_generated G s,H) f =
            group_kernel(G,H) f INTER s`,
  SIMP_TAC[group_kernel; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[subgroup_of] THEN SET_TAC[]);;

let GROUP_IMAGE_FROM_SUBGROUP_GENERATED = prove
 (`!G H s f:A->B.
        s subgroup_of G
        ==> group_image(subgroup_generated G s,H) f =
            group_image(G,H) f INTER IMAGE f s`,
  SIMP_TAC[group_image; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[subgroup_of] THEN SET_TAC[]);;

let GROUP_ISOMORPHISM_ONTO_IMAGE = prove
 (`!(f:A->B) G H.
        group_isomorphism(G,subgroup_generated H (group_image (G,H) f)) f <=>
        group_monomorphism(G,H) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[group_monomorphism; group_epimorphism] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN] THEN
  ASM_CASES_TAC `group_homomorphism (G,H) (f:A->B)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; SUBGROUP_GROUP_IMAGE] THEN
  REWRITE_TAC[group_image; SUBSET_REFL]);;

let NORMAL_SUBGROUP_GROUP_KERNEL = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> (group_kernel (G,G') f) normal_subgroup_of G`,
  SIMP_TAC[NORMAL_SUBGROUP_CONJUGATE_INV; SUBGROUP_GROUP_KERNEL] THEN
  REWRITE_TAC[group_homomorphism; group_setmul] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF;
      SET_RULE `{f x y | P x /\ y IN {a}} = {f x a | P x}`;
      SET_RULE `{f x y | x IN {a} /\ P y} = {f a y | P y}`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; group_kernel; IN_ELIM_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[GROUP_INV; GROUP_MUL; GROUP_MUL_LID; GROUP_MUL_LINV]);;

let GROUP_KERNEL_RIGHT_COSET = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> group_kernel(G,quotient_group G n) (right_coset G n) = n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[group_kernel; QUOTIENT_GROUP_ID] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [normal_subgroup_of]) THEN
  REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  ASM_SIMP_TAC[RIGHT_COSET_EQ_SUBGROUP] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN SET_TAC[]);;

let CARD_EQ_GROUP_IMAGE_KERNEL = prove
 (`!G H (f:A->B).
        group_homomorphism(G,H) f
        ==> group_image(G,H) f *_c group_kernel(G,H) f =_c group_carrier G`,
  REWRITE_TAC[group_homomorphism; group_image; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_EQ_IMAGE_MUL_FIBRES THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN TRANS_TAC CARD_EQ_TRANS
   `IMAGE (group_mul G x) (group_kernel(G,H) (f:A->B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_REFL_IMP;
    MATCH_MP_TAC CARD_EQ_IMAGE THEN REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN
    ASM_MESON_TAC[GROUP_MUL_LCANCEL_IMP]] THEN
  MATCH_MP_TAC(SET_RULE
   `!g. IMAGE f s SUBSET t /\ IMAGE g t SUBSET s /\ (!y. y IN t ==> f(g y) = y)
        ==> t = IMAGE f s`) THEN
  EXISTS_TAC `group_mul G (group_inv G x:A)` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; group_kernel] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GROUP_MUL_RID; GROUP_MUL_LID;
               GROUP_MUL_LINV; GROUP_MUL_ASSOC; GROUP_MUL_RINV]);;

let CARD_DIVIDES_GROUP_MONOMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_monomorphism(G,H) f /\ FINITE(group_carrier H)
        ==> CARD(group_carrier G) divides CARD(group_carrier H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(group_carrier G) = CARD(group_image (G,H) (f:A->B))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
    REWRITE_TAC[group_image] THEN
    ASM_MESON_TAC[CARD_EQ_GROUP_MONOMORPHIC_IMAGE;
                  FINITE_GROUP_MONOMORPHIC_PREIMAGE];
    MATCH_MP_TAC LAGRANGE_THEOREM THEN
    ASM_MESON_TAC[SUBGROUP_GROUP_IMAGE; group_monomorphism]]);;

let CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_epimorphism(G,H) f /\ FINITE(group_carrier G)
        ==> CARD(group_carrier H) divides CARD(group_carrier G)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GROUP_EPIMORPHISM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARD_EQ_GROUP_IMAGE_KERNEL) THEN DISCH_THEN
   (MP_TAC o (MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_CARD_IMP))) THEN
  ASM_REWRITE_TAC[group_image; mul_c; GSYM CROSS; group_kernel] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[FINITE_CROSS; CARD_CROSS; FINITE_IMAGE; FINITE_RESTRICT] THEN
  CONV_TAC NUMBER_RULE);;

let QUOTIENT_GROUP_UNIVERSAL_EXPLICIT = prove
 (`!G G' n (f:A->B).
        group_homomorphism (G,G') f /\ n normal_subgroup_of G /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G /\
               right_coset G n x = right_coset G n y
               ==> f x = f y)
        ==> ?g. group_homomorphism(quotient_group G n,G') g /\
                !x. x IN group_carrier G ==> g(right_coset G n x) = f x`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GSYM o GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:(A->bool)->B` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[QUOTIENT_GROUP] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[GROUP_SETINV_RIGHT_COSET; GROUP_SETMUL_RIGHT_COSET] THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV] THEN
  SUBGOAL_THEN `n = right_coset G n (group_id G:A)` SUBST1_TAC THENL
   [ASM_MESON_TAC[RIGHT_COSET_ID; normal_subgroup_of;
                  SUBGROUP_OF_IMP_SUBSET];
    ASM_SIMP_TAC[GROUP_ID]]);;

let QUOTIENT_GROUP_UNIVERSAL = prove
 (`!G G' n (f:A->B).
        group_homomorphism (G,G') f /\
        n normal_subgroup_of G /\
        n SUBSET group_kernel (G,G') f
        ==> ?g. group_homomorphism(quotient_group G n,G') g /\
                !x. x IN group_carrier G ==> g(right_coset G n x) = f x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC QUOTIENT_GROUP_UNIVERSAL_EXPLICIT THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_div G x y:A` o REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[GSYM RIGHT_COSET_EQ; group_kernel; IN_ELIM_THM; GROUP_DIV;
               NORMAL_SUBGROUP_IMP_SUBGROUP] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_DIV] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC GROUP_DIV_EQ_ID THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[]);;

let QUOTIENT_GROUP_UNIVERSAL_EPIMORPHISM = prove
 (`!G G' n (f:A->B).
        group_epimorphism (G,G') f /\
        n normal_subgroup_of G /\
        n SUBSET group_kernel (G,G') f
        ==> ?g. group_epimorphism(quotient_group G n,G') g /\
                !x. x IN group_carrier G ==> g(right_coset G n x) = f x`,
  REWRITE_TAC[group_epimorphism] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `G':B group`; `n:A->bool`; `f:A->B`]
        QUOTIENT_GROUP_UNIVERSAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[QUOTIENT_GROUP] THEN ASM SET_TAC[]);;

let GROUP_KERNEL_FROM_TRIVIAL_GROUP = prove
 (`!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group G
        ==> group_kernel (G,H) f = group_carrier G`,
  REWRITE_TAC[trivial_group; group_kernel; group_homomorphism] THEN
  SET_TAC[]);;

let GROUP_IMAGE_FROM_TRIVIAL_GROUP = prove
 (`!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group G
        ==> group_image (G,H) f = {group_id H}`,
  REWRITE_TAC[trivial_group; group_image; group_homomorphism] THEN
  SET_TAC[]);;

let GROUP_KERNEL_TO_TRIVIAL_GROUP = prove
 (`!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group H
        ==> group_kernel (G,H) f = group_carrier G`,
  REWRITE_TAC[trivial_group; group_kernel; group_homomorphism] THEN
  SET_TAC[]);;

let GROUP_IMAGE_TO_TRIVIAL_GROUP = prove
 (`!G H (f:A->B).
        group_homomorphism (G,H) f /\ trivial_group H
        ==> group_image (G,H) f = group_carrier H`,
  REWRITE_TAC[trivial_group; group_image; group_homomorphism] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SING_SUBSET; IN_IMAGE] THEN
  ASM_MESON_TAC[GROUP_ID]);;

let FIRST_GROUP_ISOMORPHISM_THEOREM = prove
 (`!G G' (f:A->B).
        group_homomorphism(G,G') f
        ==> (quotient_group G (group_kernel (G,G') f)) isomorphic_group
            (subgroup_generated G' (group_image (G,G') f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_group; GROUP_ISOMORPHISM] THEN
  FIRST_ASSUM(MP_TAC o SPEC `group_kernel (G,G') (f:A->B)` o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
     QUOTIENT_GROUP_UNIVERSAL_EXPLICIT)) THEN
  ASM_SIMP_TAC[NORMAL_SUBGROUP_GROUP_KERNEL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[IMP_CONJ; RIGHT_COSET_EQ; SUBGROUP_GROUP_KERNEL];
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g:(A->bool)->B` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ; SUBGROUP_GROUP_IMAGE;
             QUOTIENT_GROUP; NORMAL_SUBGROUP_GROUP_KERNEL;
             CARRIER_SUBGROUP_GENERATED_SUBGROUP; SUBGROUP_GROUP_KERNEL] THEN
    REWRITE_TAC[group_image] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[RIGHT_COSET_EQ; SUBGROUP_GROUP_KERNEL]] THEN
  SIMP_TAC[group_kernel; IN_ELIM_THM; GROUP_DIV] THEN RULE_ASSUM_TAC
   (REWRITE_RULE[group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[group_div; GROUP_INV] THEN
  ASM_SIMP_TAC[GSYM group_div; GROUP_DIV_EQ_ID]);;

let FIRST_GROUP_EPIMORPHISM_THEOREM = prove
 (`!G G' (f:A->B).
        group_epimorphism(G,G') f
        ==> (quotient_group G (group_kernel (G,G') f)) isomorphic_group G'`,
  REWRITE_TAC[group_epimorphism] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIRST_GROUP_ISOMORPHISM_THEOREM) THEN
  ASM_REWRITE_TAC[group_image; SUBGROUP_GENERATED_GROUP_CARRIER]);;

let GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_RIGHT = prove
 (`!G H (f:A->B) s.
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> {x | x IN group_carrier G /\ f x IN IMAGE f s} =
            group_setmul G s (group_kernel(G,H) f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; group_kernel; IN_ELIM_THM; group_setmul] THEN
  X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    EXISTS_TAC `group_mul G (group_inv G x) z:A` THEN
    ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL_RINV; GROUP_MUL_LID;
                 GROUP_INV; GROUP_MUL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_MUL) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_INV) THEN
    ASM_SIMP_TAC[GROUP_INV] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GROUP_MUL_LINV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE; RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[GROUP_ADD]] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC[GROUP_MUL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GROUP_MUL_RID THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[]]);;

let GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_LEFT = prove
 (`!G H (f:A->B) s.
        group_homomorphism(G,H) f /\ s SUBSET group_carrier G
        ==> {x | x IN group_carrier G /\ f x IN IMAGE f s} =
            group_setmul G (group_kernel(G,H) f) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; group_kernel; IN_ELIM_THM; group_setmul] THEN
  X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    EXISTS_TAC `group_mul G z (group_inv G x):A` THEN
    ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL_LINV; GROUP_MUL_RID;
                 GROUP_INV; GROUP_MUL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_MUL) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_INV) THEN
    ASM_SIMP_TAC[GROUP_INV] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GROUP_MUL_RINV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE; RIGHT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[GROUP_ADD]] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC[GROUP_MUL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GROUP_MUL_LID THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[]]);;

let GROUP_HOMOMORPHISM_IMAGE_PREIMAGE = prove
 (`!G H (f:A->B) t.
        group_homomorphism(G,H) f
        ==> IMAGE f {x | x IN group_carrier G /\ f x IN t} =
            t INTER (group_image(G,H) f)`,
  REWRITE_TAC[group_homomorphism; group_image] THEN SET_TAC[]);;

let GROUP_HOMOMORPHISM_PREIMAGE_IMAGE = prove
 (`!G H (f:A->B) s.
        group_homomorphism(G,H) f /\
        group_kernel(G,H) f SUBSET s /\
        s subgroup_of G
        ==> {x | x IN group_carrier G /\ f x IN IMAGE f s} = s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_RIGHT o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[subgroup_of]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[GROUP_SETMUL_RSUBSET_EQ; GROUP_KERNEL_NONEMPTY;
               GROUP_KERNEL_SUBSET_CARRIER]);;

let GROUP_HOMOMORPHISM_IMAGE_PREIMAGE_EQ = prove
 (`!G H (f:A->B) t.
        group_homomorphism(G,H) f /\ t SUBSET group_image(G,H) f
        ==> IMAGE f {x | x IN group_carrier G /\ f x IN t} = t`,
  SIMP_TAC[GROUP_HOMOMORPHISM_IMAGE_PREIMAGE] THEN SET_TAC[]);;

let GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE = prove
 (`!G H (f:A->B) k.
        group_epimorphism(G,H) f
        ==> (k subgroup_of H <=>
             ?j. j subgroup_of G /\
                 group_kernel(G,H) f SUBSET j /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GROUP_EPIMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBGROUP_OF_HOMOMORPHIC_IMAGE]] THEN
  EXISTS_TAC `{x | x IN group_carrier G /\ (f:A->B) x IN k}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[group_kernel; SUBSET; IN_ELIM_THM; IN_SUBGROUP_ID];
    RULE_ASSUM_TAC(REWRITE_RULE
     [GROUP_EPIMORPHISM; group_image; subgroup_of]) THEN ASM SET_TAC[]]);;

let GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT = prove
 (`!G H (f:A->B) j.
        group_epimorphism(G,H) f
        ==> (j subgroup_of G /\ group_kernel(G,H) f SUBSET j <=>
             ?k. k subgroup_of H /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GROUP_EPIMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `IMAGE (f:A->B) j` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBGROUP_OF_HOMOMORPHIC_IMAGE]; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `j SUBSET s /\ (!x y. x IN j /\ y IN s /\ f x = f y ==> y IN j)
      ==> {x | x IN s /\ f x IN IMAGE f j} = j`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:A = group_mul G (group_div G y x) x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[group_div; GSYM GROUP_MUL_ASSOC; GROUP_INV;
                   GROUP_MUL_LINV; GROUP_MUL_RID];
      MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[group_kernel; IN_ELIM_THM; GROUP_DIV] THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP GROUP_HOMOMORPHISM_DIV th]) THEN
      W(MP_TAC o PART_MATCH (lhand o rand) GROUP_DIV_EQ_ID o snd) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `k:B->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "j" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; group_kernel; IN_ELIM_THM] THEN
      ASM_MESON_TAC[IN_SUBGROUP_ID]]]);;

let NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE = prove
 (`!G H (f:A->B) j.
        group_homomorphism(G,H) f /\ j normal_subgroup_of H
        ==> {x | x IN group_carrier G /\ f x IN j} normal_subgroup_of G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_MUL_SYM] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_OF_HOMOMORPHIC_PREIMAGE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_MUL) THEN
  SIMP_TAC[IN_ELIM_THM; GROUP_MUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[]);;

let NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE = prove
 (`!G H (f:A->B) n.
        group_epimorphism(G,H) f /\ n normal_subgroup_of G
        ==> IMAGE f n normal_subgroup_of H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATE_INV] THEN
  REWRITE_TAC[group_epimorphism] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBGROUP_OF_HOMOMORPHIC_IMAGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN
  REWRITE_TAC[group_setmul; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_SING; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o GSYM o CONJUNCT2)) THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; FUN_IN_IMAGE]);;

let NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ = prove
 (`!G H (f:A->B) j k.
        group_epimorphism (G,H) f /\
        k subgroup_of H /\
        {x | x IN group_carrier G /\ f x IN k} = j
        ==> (j normal_subgroup_of G <=> k normal_subgroup_of H)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    ASM_MESON_TAC[NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE;
                  group_epimorphism]] THEN
  SUBGOAL_THEN `k = IMAGE (f:A->B) j` SUBST1_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; group_epimorphism]) THEN
  ASM SET_TAC[]);;

let GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE = prove
 (`!G H (f:A->B) k.
        group_epimorphism(G,H) f
        ==> (k normal_subgroup_of H <=>
             ?j. j normal_subgroup_of G /\
                 group_kernel(G,H) f SUBSET j /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  MESON_TAC[GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE;
            NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ;
            NORMAL_SUBGROUP_IMP_SUBGROUP]);;

let GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE_ALT = prove
 (`!G H (f:A->B) j.
        group_epimorphism(G,H) f
        ==> (j normal_subgroup_of G /\ group_kernel(G,H) f SUBSET j <=>
             ?k. k normal_subgroup_of H /\
                 {x | x IN group_carrier G /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  MESON_TAC[GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT;
            NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ;
            NORMAL_SUBGROUP_IMP_SUBGROUP]);;

let SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ = prove
 (`!G H (f:A->B) j.
        group_isomorphism(G,H) f /\ j SUBSET group_carrier G
        ==> ((IMAGE f j) subgroup_of H <=> j subgroup_of G)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    ASM_MESON_TAC[GROUP_ISOMORPHISM_IMP_HOMOMORPHISM;
                  SUBGROUP_OF_HOMOMORPHIC_IMAGE]] THEN
  SUBGOAL_THEN
   `j = {x | x IN group_carrier G /\ (f:A->B) x IN IMAGE f j}`
  SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[group_isomorphism; group_isomorphisms]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN
    ASM_MESON_TAC[GROUP_ISOMORPHISM_IMP_HOMOMORPHISM]]);;

let NORMAL_SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ = prove
 (`!G H (f:A->B) j.
        group_isomorphism(G,H) f /\ j SUBSET group_carrier G
        ==> ((IMAGE f j) normal_subgroup_of H <=> j normal_subgroup_of G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ) THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (q' ==> p') /\ (p' ==> (q' <=> q))
    ==> (p' <=> p) ==> (q' <=> q)`) THEN
  REWRITE_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ THEN
  EXISTS_TAC `f:A->B` THEN ASM_SIMP_TAC[GROUP_ISOMORPHISM_IMP_EPIMORPHISM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_isomorphism; group_isomorphisms]) THEN
  ASM SET_TAC[]);;

let GROUP_CONJUGATE_SUBGROUP_OF = prove
 (`!G s t:A->bool.
        group_conjugate G s t
        ==> (s subgroup_of G <=> t subgroup_of G)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_conjugate; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:A` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_CONJUGATION]);;

let GROUP_CONJUGATE_NORMAL_SUBGROUP_OF = prove
 (`!G s t:A->bool.
        group_conjugate G s t
        ==> (s normal_subgroup_of G <=> t normal_subgroup_of G)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_conjugate; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:A` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NORMAL_SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_CONJUGATION]);;

let NORMAL_SUBGROUP_CONJUGATE = prove
 (`!G n:A->bool.
        n normal_subgroup_of G <=>
        n subgroup_of G /\ !n'. group_conjugate G n n' ==> n' = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION_EQ] THEN
  REWRITE_TAC[group_conjugate] THEN
  MESON_TAC[IMAGE_GROUP_CONJUGATION_SUBSET; SUBGROUP_OF_IMP_SUBSET]);;

let NORMAL_SUBGROUP_CONJUGATE_EQ = prove
 (`!G n n':A->bool.
        n normal_subgroup_of G \/ n' normal_subgroup_of G
        ==> (group_conjugate G n n' <=> n = n')`,
  MESON_TAC[NORMAL_SUBGROUP_CONJUGATE; GROUP_CONJUGATE_NORMAL_SUBGROUP_OF;
            GROUP_CONJUGATE_REFL; NORMAL_SUBGROUP_OF_IMP_SUBSET]);;

let QUOTIENT_SUBGROUP_CORRESPONDENCE = prove
 (`!(G:A group) j k.
        j normal_subgroup_of G
        ==> (k subgroup_of (quotient_group G j) <=>
             ?i. i subgroup_of G /\ j SUBSET i /\
                 {x | x IN group_carrier G /\ right_coset G j x IN k} = i /\
                 IMAGE (right_coset G j) i = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_RIGHT_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE) THEN
  ASM_SIMP_TAC[GROUP_KERNEL_RIGHT_COSET]);;

let QUOTIENT_NORMAL_SUBGROUP_CORRESPONDENCE = prove
 (`!(G:A group) j k.
        j normal_subgroup_of G
        ==> (k normal_subgroup_of (quotient_group G j) <=>
             ?i. i normal_subgroup_of G /\ j SUBSET i /\
                 {x | x IN group_carrier G /\ right_coset G j x IN k} = i /\
                 IMAGE (right_coset G j) i = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_RIGHT_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE) THEN
  ASM_SIMP_TAC[GROUP_KERNEL_RIGHT_COSET]);;

let FIRST_GROUP_ISOMORPHISM_THEOREM_GEN = prove
 (`!G H (f:A->B) j k.
        group_epimorphism(G,H) f /\
        k normal_subgroup_of H /\ {x | x IN group_carrier G /\ f x IN k} = j
        ==> quotient_group G j isomorphic_group quotient_group H k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `quotient_group H (k:B->bool)`;
                 `right_coset H k o (f:A->B)`]
        FIRST_GROUP_EPIMORPHISM_THEOREM) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC GROUP_EPIMORPHISM_COMPOSE THEN EXISTS_TAC `H:B group` THEN
    ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET];
    MATCH_MP_TAC EQ_IMP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[group_kernel; QUOTIENT_GROUP_ID; o_THM] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN EXPAND_TAC "j" THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `(x:A) IN group_carrier G` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RIGHT_COSET_EQ_SUBGROUP THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_epimorphism; normal_subgroup_of]) THEN
  ASM SET_TAC[]);;

let FIRST_GROUP_ISOMORPHISM_THEOREM_GEN_ALT = prove
 (`!G H (f:A->B) j k.
        group_epimorphism(G,H) f /\ j normal_subgroup_of G /\
        group_kernel (G,H) f SUBSET j /\ IMAGE f j = k
        ==> quotient_group G j isomorphic_group quotient_group H k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIRST_GROUP_ISOMORPHISM_THEOREM_GEN THEN
  EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE_ALT]);;

let SIMPLE_GROUP_EPIMORPHIC_IMAGE_EQ = prove
 (`!G H (f:A->B).
      group_epimorphism(G,H) f
      ==> ((!k. k normal_subgroup_of H
                ==> k = {group_id H} \/ k = group_carrier H) <=>
           (!h. h normal_subgroup_of G /\ group_kernel(G,H) f PSUBSET h
                ==> h = group_carrier G))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PSUBSET; TAUT
   `p /\ q /\ ~r ==> s <=> p /\ q ==> r \/ s`] THEN
  ASM_SIMP_TAC[GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE_ALT] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    SUBGROUP_OF_EPIMORPHIC_PREIMAGE)) THEN
  SIMP_TAC[IMP_CONJ; NORMAL_SUBGROUP_IMP_SUBGROUP] THEN
  DISCH_THEN(K ALL_TAC) THEN  REWRITE_TAC[group_kernel] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:B->bool` THEN
  ASM_CASES_TAC `(k:B->bool) normal_subgroup_of H` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[group_epimorphism; subgroup_of; normal_subgroup_of;
       group_homomorphism]) THEN
  ASM SET_TAC[]);;

let NO_PROPER_SUBGROUP_EPIMORPHIC_IMAGE_EQ = prove
 (`!G H (f:A->B).
      group_epimorphism(G,H) f
      ==> ((!k. k subgroup_of H
                ==> k = {group_id H} \/ k = group_carrier H) <=>
           (!h. h subgroup_of G /\ group_kernel(G,H) f PSUBSET h
                ==> h = group_carrier G))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PSUBSET; TAUT
   `p /\ q /\ ~r ==> s <=> p /\ q ==> r \/ s`] THEN
  ASM_SIMP_TAC[GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    SUBGROUP_OF_EPIMORPHIC_PREIMAGE)) THEN
  SIMP_TAC[IMP_CONJ] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[group_kernel] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:B->bool` THEN
  ASM_CASES_TAC `(k:B->bool) subgroup_of H` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[group_epimorphism; subgroup_of; group_homomorphism]) THEN
  ASM SET_TAC[]);;

let MAXIMAL_SUBGROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> ((!h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G) <=>
             (!k. k subgroup_of quotient_group G n
                  ==> k = {group_id(quotient_group G n)} \/
                      k = group_carrier(quotient_group G n)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_RIGHT_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP NO_PROPER_SUBGROUP_EPIMORPHIC_IMAGE_EQ) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[GROUP_KERNEL_RIGHT_COSET]);;

let MAXIMAL_NORMAL_SUBGROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> ((!h. h normal_subgroup_of G /\ n PSUBSET h
                  ==> h = group_carrier G) <=>
             (!k. k normal_subgroup_of quotient_group G n
                  ==> k = {group_id(quotient_group G n)} \/
                      k = group_carrier(quotient_group G n)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_RIGHT_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIMPLE_GROUP_EPIMORPHIC_IMAGE_EQ) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[GROUP_KERNEL_RIGHT_COSET]);;

(* ------------------------------------------------------------------------- *)
(* Trivial homomorphisms.                                                    *)
(* ------------------------------------------------------------------------- *)

let trivial_homomorphism = new_definition
 `trivial_homomorphism(G,G') (f:A->B) <=>
        group_homomorphism(G,G') f /\
        !x. x IN group_carrier G ==> f x = group_id G'`;;

let GROUP_KERNEL_IMAGE_TRIVIAL = prove
 (`!(f:A->B) G G'.
        group_homomorphism (G,G') f
        ==> (group_kernel(G,G') f = group_carrier G <=>
             group_image(G,G') f = {group_id G'})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_homomorphism; group_image; group_kernel] THEN
  MP_TAC(ISPEC `G:A group` GROUP_ID) THEN SET_TAC[]);;

let TRIVIAL_HOMOMORPHISM_GROUP_KERNEL = prove
 (`!(f:A->B) G G'.
        trivial_homomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_kernel(G,G') f = group_carrier G`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[trivial_homomorphism; group_kernel; group_homomorphism] THEN
  SET_TAC[]);;

let TRIVIAL_HOMOMORPHISM_GROUP_IMAGE = prove
 (`!(f:A->B) G G'.
        trivial_homomorphism(G,G') f <=>
        group_homomorphism(G,G') f /\
        group_image(G,G') f = {group_id G'}`,
  MESON_TAC[TRIVIAL_HOMOMORPHISM_GROUP_KERNEL; GROUP_KERNEL_IMAGE_TRIVIAL]);;

let GROUP_HOMOMORPHISM_TRIVIAL = prove
 (`!G H. group_homomorphism (G,H) (\x. group_id H)`,
  SIMP_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE; GROUP_MUL_LID;
           GROUP_INV_ID; GROUP_ID]);;

let TRIVIAL_HOMOMORPHISM_TRIVIAL = prove
 (`!G H. trivial_homomorphism (G,H) (\x. group_id H)`,
  REWRITE_TAC[trivial_homomorphism; GROUP_HOMOMORPHISM_TRIVIAL]);;

let GROUP_MONOMORPHISM_TRIVIAL = prove
 (`!G H. group_monomorphism (G,H) (\x. group_id H) <=> trivial_group G`,
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM_TRIVIAL] THEN
  REWRITE_TAC[TRIVIAL_GROUP_ALT] THEN SET_TAC[]);;

let GROUP_EPIMORPHISM_TRIVIAL = prove
 (`!G H. group_epimorphism (G,H) (\x. group_id H) <=> trivial_group H`,
  REWRITE_TAC[group_epimorphism; GROUP_HOMOMORPHISM_TRIVIAL] THEN
  SIMP_TAC[GROUP_CARRIER_NONEMPTY; SET_RULE
   `~(s = {}) ==> IMAGE (\x. a) s = {a}`] THEN
  REWRITE_TAC[trivial_group; EQ_SYM_EQ]);;

let GROUP_ISOMORPHISM_TRIVIAL = prove
 (`!G H. group_isomorphism (G,H) (\x. group_id H) <=>
         trivial_group G /\ trivial_group H`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_TRIVIAL; GROUP_EPIMORPHISM_TRIVIAL]);;

(* ------------------------------------------------------------------------- *)
(* The order of a group element. This is defined as 0 for the infinite case. *)
(* This keeps theorems uniform and is analogous to "characteristic zero".    *)
(* That is, x^n = 1 iff n is divisible by the order of x, in all cases.      *)
(* ------------------------------------------------------------------------- *)

let group_element_order = new_definition
 `group_element_order G (x:A) =
        @d. !n. group_pow G x n = group_id G <=> d divides n`;;

let GROUP_POW_EQ_ID = prove
 (`!G (x:A) n.
        x IN group_carrier G
        ==> (group_pow G x n = group_id G <=>
             (group_element_order G x) divides n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[group_element_order] THEN CONV_TAC SELECT_CONV THEN
  ASM_CASES_TAC `!n. group_pow G (x:A) n = group_id G ==> n = 0` THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[NUMBER_RULE `0 divides n <=> n = 0`] THEN
    ASM_MESON_TAC[CONJUNCT1 group_pow];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM])] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[NOT_IMP; GSYM LT_NZ; TAUT
   `p ==> q ==> r <=> ~r /\ p ==> ~q`] THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  MP_TAC(SPECL [`n:num`; `d:num`] DIVISION) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[NUMBER_RULE `d divides (a * d + b) <=> d divides b`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[GROUP_POW_ADD; GROUP_POW_MUL; GROUP_POW_ID] THEN
  ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_POW] THEN
  ASM_CASES_TAC `n MOD d = 0` THEN
  ASM_REWRITE_TAC[CONJUNCT1 group_pow; NUMBER_RULE `n divides 0`] THEN
  ASM_SIMP_TAC[LT_NZ] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[NOT_LE]);;

let GROUP_POW_ELEMENT_ORDER = prove
 (`!G x:A. x IN group_carrier G
           ==> group_pow G x (group_element_order G x) = group_id G`,
  SIMP_TAC[GROUP_POW_EQ_ID; NUMBER_RULE `(d:num) divides d`]);;

let GROUP_ZPOW_EQ_ID = prove
 (`!G (x:A) n.
        x IN group_carrier G
        ==> (group_zpow G x n = group_id G <=>
             &(group_element_order G x) divides n)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_THEN
   (X_CHOOSE_THEN `m:num` SUBST1_TAC) (SPEC `n:int` INT_IMAGE) THEN
  ASM_SIMP_TAC[GROUP_NPOW; GROUP_ZPOW_NEG; GROUP_INV_EQ_ID;
               GROUP_POW; GROUP_POW_EQ_ID] THEN
  REWRITE_TAC[INTEGER_RULE `m divides (--n:int) <=> m divides n`] THEN
  REWRITE_TAC[num_divides]);;

let GROUP_ZPOW_EQ_ALT = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> (group_zpow G x m = group_zpow G x n <=>
             &(group_element_order G x) divides n - m)`,
  SIMP_TAC[GSYM GROUP_ZPOW_EQ_ID; GROUP_ZPOW_SUB] THEN
  SIMP_TAC[GROUP_DIV_EQ_ID; GROUP_ZPOW] THEN MESON_TAC[]);;

let GROUP_ZPOW_EQ = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> (group_zpow G x m = group_zpow G x n <=>
             (m == n) (mod &(group_element_order G x)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_ZPOW_EQ_ALT] THEN
  CONV_TAC INTEGER_RULE);;

let GROUP_POW_EQ = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> (group_pow G x m = group_pow G x n <=>
             (m == n) (mod (group_element_order G x)))`,
  SIMP_TAC[GSYM GROUP_NPOW; GROUP_ZPOW_EQ; num_congruent]);;

let GROUP_ELEMENT_ORDER_EQ_0 = prove
 (`!G (x:A).
        x IN group_carrier G
        ==> (group_element_order G x = 0 <=>
              !n. ~(n = 0) ==> ~(group_pow G x n = group_id G))`,
  SIMP_TAC[GROUP_POW_EQ_ID] THEN MESON_TAC
   [NUMBER_RULE `0 divides n <=> n = 0`; NUMBER_RULE `!n. n divides n`]);;

let GROUP_ELEMENT_ORDER_UNIQUE = prove
 (`!G (x:A) d.
        x IN group_carrier G
        ==> (group_element_order G x = d <=>
             !n. group_pow G x n = group_id G <=> d divides n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GROUP_POW_EQ_ID) THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  MESON_TAC[DIVIDES_ANTISYM; NUMBER_RULE `(n:num) divides n`]);;

let GROUP_ELEMENT_ORDER_EQ_1 = prove
 (`!G (x:A).
        x IN group_carrier G
        ==> (group_element_order G x = 1 <=> x = group_id G)`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE; NUMBER_RULE `1 divides n`] THEN
  MESON_TAC[GROUP_POW_ID; GROUP_POW_1]);;

let GROUP_ELEMENT_ORDER_UNIQUE_PRIME = prove
 (`!G (x:A) p.
        x IN group_carrier G /\ prime p
        ==> (group_element_order G x = p <=>
             ~(x = group_id G) /\ group_pow G x p = group_id G)`,
  SIMP_TAC[GROUP_POW_EQ_ID; GSYM GROUP_ELEMENT_ORDER_EQ_1] THEN
  REWRITE_TAC[prime] THEN
  MESON_TAC[NUMBER_RULE `1 divides n /\ n divides n`]);;

let GROUP_ELEMENT_ORDER_ID = prove
 (`!G:A group. group_element_order G (group_id G) = 1`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_1; GROUP_ID]);;

let GROUP_ELEMENT_ORDER_INV = prove
 (`!G x:A.
        x IN group_carrier G
        ==> group_element_order G (group_inv G x) = group_element_order G x`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE; GROUP_INV; GSYM GROUP_INV_POW] THEN
  SIMP_TAC[GROUP_INV_EQ_ID; GROUP_POW; GROUP_POW_EQ_ID]);;

let FINITE_GROUP_ELEMENT_ORDER_NONZERO = prove
 (`!G x:A.
        FINITE(group_carrier G) /\ x IN group_carrier G
        ==> ~(group_element_order G x = 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM INFINITE] THEN DISCH_TAC THEN
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `IMAGE (\n. group_pow G (x:A) n) (:num)` THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_POW] THEN
  MATCH_MP_TAC INFINITE_IMAGE THEN
  ASM_SIMP_TAC[GROUP_POW_EQ; IN_UNIV; num_INFINITE] THEN
  CONV_TAC NUMBER_RULE);;

let GROUP_ELEMENT_ORDER_POW = prove
 (`!G (x:A) k.
        x IN group_carrier G /\ ~(k = 0) /\ k divides group_element_order G x
        ==> group_element_order G (group_pow G x k) =
            group_element_order G x DIV k`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE; GROUP_POW; GSYM GROUP_POW_MUL] THEN
  SIMP_TAC[GROUP_POW_EQ_ID] THEN REWRITE_TAC[divides] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM divides; DIV_MULT] THEN
  UNDISCH_TAC `~(k = 0)` THEN CONV_TAC NUMBER_RULE);;

let GROUP_ELEMENT_ORDER_POW_GEN = prove
 (`!G (x:A) k.
        x IN group_carrier G
        ==> group_element_order G (group_pow G x k) =
            if k = 0 then 1
            else group_element_order G x DIV gcd(group_element_order G x,k)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 group_pow; GROUP_ELEMENT_ORDER_ID] THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE; GROUP_POW] THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_MUL] THEN
  ASM_SIMP_TAC[GROUP_POW_EQ_ID] THEN X_GEN_TAC `n:num` THEN
  SPEC_TAC(`group_element_order G (x:A)`,`d:num`) THEN GEN_TAC THEN
  MP_TAC(NUMBER_RULE `gcd(d:num,k) divides d`) THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [th] THEN
    MP_TAC(SYM th)) THEN
  ASM_SIMP_TAC[DIV_MULT; NUMBER_RULE `gcd(d,k) = 0 <=> d = 0 /\ k = 0`] THEN
  UNDISCH_TAC `~(k = 0)` THEN NUMBER_TAC);;

let GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN = prove
 (`!G x (y:A) n.
        x IN group_carrier G /\
        y IN group_carrier G /\
        group_mul G x y = group_mul G y x /\
        group_element_order G x divides n /\
        group_element_order G y divides n
        ==> group_element_order G (group_mul G x y) divides n`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM GROUP_POW_EQ_ID; IMP_CONJ; GROUP_MUL] THEN
  SIMP_TAC[GROUP_MUL_POW; GROUP_MUL_LID; GROUP_ID]);;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN = prove
 (`!G x (y:A) n.
        abelian_group G /\
        x IN group_carrier G /\
        y IN group_carrier G /\
        group_element_order G x divides n /\
        group_element_order G y divides n
        ==> group_element_order G (group_mul G x y) divides n`,
  REWRITE_TAC[abelian_group] THEN
  MESON_TAC[GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN]);;

let GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM = prove
 (`!G x (y:A).
        x IN group_carrier G /\
        y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_element_order G (group_mul G x y) divides
            lcm(group_element_order G x,group_element_order G y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE);;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM = prove
 (`!G x (y:A).
        abelian_group G /\
        x IN group_carrier G /\
        y IN group_carrier G
        ==> group_element_order G (group_mul G x y) divides
            lcm(group_element_order G x,group_element_order G y)`,
  REWRITE_TAC[abelian_group] THEN
  MESON_TAC[GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM]);;

let GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) G H x.
        group_monomorphism(G,H) f /\ x IN group_carrier G
        ==> group_element_order H (f x) = group_element_order G x`,
  REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_element_order] THEN
  ASM_SIMP_TAC[GSYM GROUP_HOMOMORPHISM_POW; GROUP_POW]);;

let GROUP_ELEMENT_ORDER_CONJUGATION = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_element_order G (group_conjugation G x y) =
            group_element_order G y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  ASM_MESON_TAC[GROUP_ISOMORPHISM_IMP_MONOMORPHISM;
                GROUP_AUTOMORPHISM_CONJUGATION; group_automorphism]);;

let IMAGE_GROUP_CONJUGATION_TORSION_GEN = prove
 (`!G P a:A.
        a IN group_carrier G
        ==> IMAGE (group_conjugation G a)
                  {x | x IN group_carrier G /\ P(group_element_order G x)} =
            {x | x IN group_carrier G /\ P(group_element_order G x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `!g. (!x. x IN s ==> f x IN s /\ g(f x) = x) /\
        (!x. x IN s ==> g x IN s /\ f(g x) = x)
        ==> IMAGE f s = s`) THEN
  EXISTS_TAC `group_conjugation G (group_inv G a:A)` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GROUP_ELEMENT_ORDER_CONJUGATION; GROUP_CONJUGATION;
               GROUP_CONJUGATION_LINV; GROUP_CONJUGATION_RINV; GROUP_INV]);;

let NORMAL_SUBGROUP_OF_TORSION_GEN = prove
 (`!P G:A group.
        {x | x IN group_carrier G /\ P(group_element_order G x)}
        normal_subgroup_of G <=>
        {x | x IN group_carrier G /\ P(group_element_order G x)}
        subgroup_of G`,
  GEN_TAC THEN REWRITE_TAC[NORMAL_SUBGROUP_CONJUGATION_EQ] THEN
  ASM_SIMP_TAC[IMAGE_GROUP_CONJUGATION_TORSION_GEN]);;

let NORMAL_SUBGROUP_OF_TORSION = prove
 (`!G:A group.
        {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}
        normal_subgroup_of G <=>
        {x | x IN group_carrier G /\ ~(group_element_order G x = 0)}
        subgroup_of G`,
  REWRITE_TAC[NORMAL_SUBGROUP_OF_TORSION_GEN]);;

let GROUP_ELEMENT_ORDER_MUL_DIVIDES = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> group_element_order G (group_mul G x y)
            divides (group_element_order G x * group_element_order G y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_EQ_ID; GROUP_MUL] THEN
  ASM_SIMP_TAC[GROUP_MUL_POW] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [MULT_SYM] THEN
  ASM_SIMP_TAC[GROUP_POW_MUL; GROUP_POW_ELEMENT_ORDER] THEN
  SIMP_TAC[GROUP_POW_ID; GROUP_MUL_LID; GROUP_ID]);;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES = prove
 (`!G x y:A.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
        ==> group_element_order G (group_mul G x y)
            divides (group_element_order G x * group_element_order G y)`,
  MESON_TAC[GROUP_ELEMENT_ORDER_MUL_DIVIDES; abelian_group]);;

let GROUP_POW_MUL_EQ_ID_SYM = prove
 (`!G n x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> (group_pow G (group_mul G x y) n = group_id G <=>
             group_pow G (group_mul G y x) n = group_id G)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `group_mul G (group_inv G x)
               (group_mul G (group_pow G (group_mul G x y) n) x):A =
    group_id G` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GROUP_MUL; GROUP_POW; GROUP_RULE
     `group_mul G (group_inv G x) (group_mul G z x) = group_id G <=>
      z = group_id G`];
    AP_THM_TAC THEN AP_TERM_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; GROUP_MUL_LID; GROUP_MUL_LINV] THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_MUL; GROUP_RULE
   `group_mul G (group_inv G x)
                (group_mul G (group_mul G (group_mul G x y) z) x) =
    group_mul G (group_mul G y x)
                (group_mul G (group_inv G x) (group_mul G z x))`]);;

let GROUP_ELEMENT_ORDER_MUL_SYM = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G
        ==> group_element_order G (group_mul G x y) =
            group_element_order G (group_mul G y x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_element_order] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[GROUP_POW_MUL_EQ_ID_SYM]);;

let GROUP_ELEMENT_ORDER_UNIQUE_ALT = prove
 (`!G (x:A) n.
        x IN group_carrier G /\ ~(n = 0)
        ==> (group_element_order G x = n <=>
             group_pow G x n = group_id G /\
             !m. 0 < m /\ m < n ==> ~(group_pow G x m = group_id G))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GROUP_POW_ELEMENT_ORDER] THEN
    ASM_SIMP_TAC[GROUP_POW_EQ_ID] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE] THEN
    X_GEN_TAC `m:num` THEN EQ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `group_pow G (x:A) m = group_id G` THEN
      FIRST_ASSUM(MP_TAC o SPEC `m:num` o MATCH_MP DIVISION) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      ASM_SIMP_TAC[GROUP_POW_ADD; NUMBER_RULE
       `(n:num) divides (q * n + r) <=> n divides r`] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_SIMP_TAC[GROUP_POW_MUL; GROUP_POW_ID; GROUP_MUL_LID; GROUP_POW] THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[LE_1; NUMBER_RULE `n divides 0`];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
      ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; GROUP_POW_MUL; GROUP_POW_ID]]]);;

let GROUP_ELEMENT_ORDER_EQ_2 = prove
 (`!G x:A.
        x IN group_carrier G
        ==> (group_element_order G x = 2 <=>
             ~(x = group_id G) /\ group_pow G x 2 = group_id G)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE_ALT; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `0 < m /\ m < 2 <=> m = 1`] THEN
  ASM_SIMP_TAC[GROUP_POW_1] THEN MESON_TAC[]);;

let GROUP_ELEMENT_ORDER_EQ_2_ALT = prove
 (`!G x:A.
        x IN group_carrier G
        ==> (group_element_order G x = 2 <=>
             ~(x = group_id G) /\ group_inv G x = x)`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_2; GROUP_LINV_EQ; GROUP_POW_2]);;

let GROUP_ELEMENT_ORDER_POW_DIVIDES = prove
 (`!G (x:A) n.
        x IN group_carrier G
        ==> group_element_order G (group_pow G x n) divides
            group_element_order G x`,
 REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM GROUP_POW_EQ_ID; GROUP_POW] THEN
 ASM_SIMP_TAC[GROUP_POW_POW] THEN
 ASM_SIMP_TAC[GROUP_POW_EQ_ID] THEN CONV_TAC NUMBER_RULE);;

let GROUP_ELEMENT_ORDER_MUL_EQ = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x /\
        coprime(group_element_order G x,group_element_order G y)
        ==> group_element_order G (group_mul G x y) =
            group_element_order G x * group_element_order G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_MUL_DIVIDES] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a:num) divides (b * c) /\ b divides (a * c) /\ coprime(a,b)
    ==> (a * b) divides c`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_EQ_ID] THEN
  MATCH_MP_TAC(MESON[]
   `(group_mul G (group_pow G x m) (group_pow G y m) = group_pow G x m /\
     group_mul G (group_pow G x n) (group_pow G y n) = group_pow G y n) /\
    (group_mul G (group_pow G x m) (group_pow G y m) = group_id G /\
     group_mul G (group_pow G x n) (group_pow G y n) = group_id G)
    ==> group_pow G x m = group_id G /\ group_pow G y n = group_id G`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GROUP_POW_MUL; GROUP_POW_ELEMENT_ORDER; GROUP_POW_ID] THEN
    ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID; GROUP_POW];
    ASM_SIMP_TAC[GSYM GROUP_MUL_POW] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[GROUP_POW_MUL; GROUP_MUL; GROUP_POW_ELEMENT_ORDER] THEN
    REWRITE_TAC[GROUP_POW_ID]]);;

let ABELIAN_GROUP_ELEMENT_ORDER_MUL_EQ = prove
 (`!G x y:A.
        abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G /\
        coprime(group_element_order G x,group_element_order G y)
        ==> group_element_order G (group_mul G x y) =
            group_element_order G x * group_element_order G y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ELEMENT_ORDER_MUL_EQ THEN
  ASM_MESON_TAC[abelian_group]);;

let GROUP_ELEMENT_ORDER_LCM_EXISTS = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> ?z. z IN group_carrier G /\
                group_element_order G z =
                lcm(group_element_order G x,group_element_order G y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `group_element_order G (x:A) = 0` THENL
   [ASM_MESON_TAC[LCM_0]; ALL_TAC] THEN
  ASM_CASES_TAC `group_element_order G (y:A) = 0` THENL
   [ASM_MESON_TAC[LCM_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`group_element_order G (x:A)`; `group_element_order G (y:A)`]
        LCM_COPRIME_DECOMP) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  REWRITE_TAC[divides; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m':num` THEN DISCH_TAC THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC(SYM th)) THEN
  EXISTS_TAC `group_mul G (group_pow G x m') (group_pow G y n'):A` THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_POW] THEN
  SUBGOAL_THEN
   `group_element_order G (group_pow G (x:A) m') = m /\
    group_element_order G (group_pow G (y:A) n') = n`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_POW_GEN] THEN CONJ_TAC THEN
    (COND_CASES_TAC THENL [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC]) THEN
    REWRITE_TAC[NUMBER_RULE `gcd(a * b:num,a) = a /\ gcd(a * b,b) = b`] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT];
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_ELEMENT_ORDER_MUL_EQ o
      lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GROUP_POW] THEN MATCH_MP_TAC GROUP_COMMUTES_POW THEN
    ASM_SIMP_TAC[GROUP_POW] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC GROUP_COMMUTES_POW THEN ASM_REWRITE_TAC[]]);;

let ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS = prove
 (`!G x y:A.
        abelian_group G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> ?z. z IN group_carrier G /\
                group_element_order G z =
                lcm(group_element_order G x,group_element_order G y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ELEMENT_ORDER_LCM_EXISTS THEN
  ASM_MESON_TAC[abelian_group]);;

let ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL = prove
 (`!G:A group.
      abelian_group G /\ FINITE(group_carrier G)
      ==> ?x. x IN group_carrier G /\
              !y. y IN group_carrier G
                  ==> group_element_order G y divides group_element_order G x`,
  REPEAT STRIP_TAC THEN MP_TAC(fst(EQ_IMP_RULE(ISPEC
   `IMAGE (group_element_order G) (group_carrier G:A->bool)` num_MAX))) THEN
  REWRITE_TAC[MESON[IN] `IMAGE f s x <=> x IN IMAGE f s`] THEN
  ASM_SIMP_TAC[GSYM num_FINITE; FINITE_IMAGE] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY; IMAGE_EQ_EMPTY; GROUP_CARRIER_NONEMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  REWRITE_TAC[DIVIDES_LCM_LEFT] THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS];
    ASM_MESON_TAC[DIVIDES_LE; LCM; FINITE_GROUP_ELEMENT_ORDER_NONZERO;
                  LCM_ZERO]]);;

let ABELIAN_GROUP_ELEMENT_ORDER_DIVIDES_MAXIMAL_ALT = prove
 (`!G:A group.
        abelian_group G /\ FINITE(group_carrier G)
        ==> ?x. x IN group_carrier G /\
                !y. y IN group_carrier G
                    ==> group_pow G y (group_element_order G x) = group_id G`,
  SIMP_TAC[GROUP_POW_EQ_ID] THEN
  REWRITE_TAC[ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL]);;

let GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED = prove
 (`!G h x:A.
        group_element_order (subgroup_generated G h) x =
        group_element_order G x`,
  REWRITE_TAC[group_element_order; GROUP_POW_SUBGROUP_GENERATED;
              SUBGROUP_GENERATED]);;

let GROUP_ELEMENT_ORDER_PROD_GROUP = prove
 (`!(G:A group) (H:B group) x y.
        x IN group_carrier G /\ y IN group_carrier H
        ==> group_element_order (prod_group G H) (x,y) =
            lcm(group_element_order G x,group_element_order H y)`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE; PROD_GROUP; IN_CROSS] THEN
  SIMP_TAC[GROUP_POW_PROD_GROUP; PAIR_EQ; GROUP_POW_EQ_ID] THEN
  CONV_TAC NUMBER_RULE);;

let GROUP_ELEMENT_ORDER_PROD_GROUP_ALT = prove
 (`!(G:A group) (H:B group) z.
        z IN group_carrier(prod_group G H)
        ==> group_element_order (prod_group G H) z =
            lcm(group_element_order G (FST z),group_element_order H (SND z))`,
  REWRITE_TAC[FORALL_PAIR_THM; PROD_GROUP; IN_CROSS] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_PROD_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* Cyclic groups.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBGROUP_OF_POWERS = prove
 (`!G (x:A).
      x IN group_carrier G ==> {group_zpow G x n | n IN (:int)} subgroup_of G`,
  REWRITE_TAC[subgroup_of; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
  SIMP_TAC[GROUP_ZPOW; GSYM GROUP_ZPOW_ADD; GSYM GROUP_ZPOW_NEG] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[GROUP_NPOW; group_pow]);;

let CARRIER_SUBGROUP_GENERATED_BY_SING = prove
 (`!G x:A.
        x IN group_carrier G
        ==> group_carrier(subgroup_generated G {x}) =
            {group_zpow G x n | n IN (:int)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[SUBGROUP_OF_POWERS; SING_SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[GROUP_ZPOW_1; IN_UNIV];
    MP_TAC(ISPECL [`G:A group`; `{x:A}`] SUBGROUP_SUBGROUP_GENERATED) THEN
    REWRITE_TAC[subgroup_of; SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    STRIP_TAC THEN X_GEN_TAC `n:int` THEN
    DISJ_CASES_THEN MP_TAC(SPEC `n:int` INT_IMAGE) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    ASM_SIMP_TAC[GROUP_ZPOW_NEG; GROUP_NPOW] THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN SPEC_TAC(`m:num`,`m:num`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[group_pow] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SING_SUBSET] THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET THEN
    ASM_REWRITE_TAC[SING_SUBSET]]);;

let cyclic_group = new_definition
 `cyclic_group G <=>
        ?x. x IN group_carrier G /\ subgroup_generated G {x} = G`;;

let CYCLIC_GROUP = prove
 (`!G:A group.
        cyclic_group G <=>
        ?x. x IN group_carrier G /\
            group_carrier G = {group_zpow G x n | n IN (:int)}`,
  GEN_TAC THEN REWRITE_TAC[cyclic_group] THEN MATCH_MP_TAC(MESON[]
   `(!x. P x ==> (Q x <=> R x))
    ==> ((?x. P x /\ Q x) <=> (?x. P x /\ R x))`) THEN
  SIMP_TAC[GSYM CARRIER_SUBGROUP_GENERATED_BY_SING] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN MESON_TAC[]);;

let CYCLIC_IMP_ABELIAN_GROUP = prove
 (`!G:A group. cyclic_group G ==> abelian_group G`,
  SIMP_TAC[CYCLIC_GROUP; abelian_group; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  SIMP_TAC[GSYM GROUP_ZPOW_ADD] THEN REWRITE_TAC[INT_ADD_SYM]);;

let TRIVIAL_IMP_CYCLIC_GROUP = prove
 (`!G:A group. trivial_group G ==> cyclic_group G`,
  REWRITE_TAC[trivial_group; cyclic_group] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `group_id G:A` THEN
  ASM_MESON_TAC[SUBGROUP_GENERATED_GROUP_CARRIER; GROUP_ID]);;

let CYCLIC_GROUP_ALT = prove
 (`!G:A group. cyclic_group G <=> ?x. subgroup_generated G {x} = G`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[cyclic_group]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` MP_TAC) THEN
  ASM_CASES_TAC `(a:A) IN group_carrier G` THENL
   [ASM_MESON_TAC[cyclic_group]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC TRIVIAL_IMP_CYCLIC_GROUP THEN
  REWRITE_TAC[TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ] THEN
  ASM SET_TAC[]);;

let CYCLIC_GROUP_GENERATED = prove
 (`!G x:A. cyclic_group(subgroup_generated G {x})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CYCLIC_GROUP_ALT] THEN
  EXISTS_TAC `x:A` THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  SIMP_TAC[SUBGROUP_GENERATED_IDEMPOT; SUBSET_REFL]);;

let CYCLIC_GROUP_EPIMORPHIC_IMAGE = prove
 (`!G H (f:A->B).
        group_epimorphism(G,H) f /\ cyclic_group G ==> cyclic_group H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_epimorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o GSYM) MP_TAC) THEN
  REWRITE_TAC[CYCLIC_GROUP] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:A->B) x` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `t = IMAGE f s ==> !x. x IN s ==> f x IN t`)) THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[GSYM(MATCH_MP GROUP_HOMOMORPHISM_ZPOW th)]) THEN
  SET_TAC[]);;

let ISOMORPHIC_GROUP_CYCLICITY = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H ==> (cyclic_group G <=> cyclic_group H)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CYCLIC_GROUP_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[isomorphic_group; ISOMORPHIC_GROUP_SYM;
                GROUP_MONOMORPHISM_EPIMORPHISM]);;

let SUBGROUP_OF_CYCLIC_GROUP_EXPLICIT = prove
 (`!G h x:A.
        x IN group_carrier G /\ h subgroup_of (subgroup_generated G {x})
        ==> ?k. h = {group_zpow G x (&k * n) | n IN (:int)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  ASM_CASES_TAC `(h:A->bool) subgroup_of G` THENL
   [ALL_TAC; ASM_MESON_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_REV]] THEN
  SIMP_TAC[subgroup_of; CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
  REWRITE_TAC[SUBGROUP_GENERATED] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h SUBSET {group_zpow G (x:A) (&0)}` THENL
   [EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; GSYM SUBSET_ANTISYM_EQ;
                    SET_RULE `{a |x| x IN UNIV} = {a}`] THEN
    ASM_REWRITE_TAC[GROUP_ZPOW_0; SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. 0 < n /\ group_pow G (x:A) n IN h` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `h SUBSET {f x | x IN (:int)} ==> ~(h SUBSET {f(&0)})
      ==> ?n. ~(n = &0) /\ f n IN h`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `num_of_int(abs n)` THEN
    REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_LT] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    ASM_REWRITE_TAC[GSYM INT_ABS_NZ] THEN REWRITE_TAC[INT_ABS] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_ZPOW_NEG];
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[TAUT `(p ==> ~(q /\ r)) <=> q /\ p ==> ~r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`subgroup_generated G (h:A->bool)`; `group_pow G x k:A`]
        GROUP_ZPOW) THEN
    REWRITE_TAC[GROUP_ZPOW_SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    ASM_SIMP_TAC[GROUP_ZPOW_MUL; GROUP_NPOW];
    DISCH_THEN(LABEL_TAC "*")] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `h SUBSET {f x | x IN s} ==> (!x. f x IN h ==> P(f x))
   ==> !y. y IN h ==> P y`)) THEN
  X_GEN_TAC `m:int` THEN DISCH_THEN(fun th ->
    EXISTS_TAC `m div (&k)` THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MP_TAC(SPECL [`m:int`; `&k:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; GSYM LT_NZ; INT_ABS_NUM] THEN
  SPEC_TAC(`m div &k`,`q:int`) THEN
  SPEC_TAC(`m rem &k`,`r:int`) THEN ONCE_REWRITE_TAC[TAUT
   `p /\ q /\ r ==> s <=> q ==> r /\ p ==> s`] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `q:int`] THEN
  REWRITE_TAC[INT_OF_NUM_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[INT_ADD_RID] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[LT_NZ] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN REWRITE_TAC[GSYM GROUP_NPOW] THEN
  SUBST1_TAC(INT_ARITH `&m:int = --(&k * q) + (q * &k + &m)`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_ZPOW_ADD o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_NEG]);;

let SUBGROUP_OF_CYCLIC_GROUP = prove
 (`!G h:A->bool.
        cyclic_group G /\ h subgroup_of G
        ==> cyclic_group(subgroup_generated G h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CYCLIC_GROUP] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cyclic_group]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`; `x:A`]
   SUBGROUP_OF_CYCLIC_GROUP_EXPLICIT) THEN
  ASM_REWRITE_TAC[GROUP_ZPOW_SUBGROUP_GENERATED] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_MUL] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  EXISTS_TAC `group_zpow G x (&k):A` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `&1:int` THEN
  ASM_SIMP_TAC[IN_UNIV; GROUP_ZPOW_1; GROUP_ZPOW]);;

let CYCLIC_GROUP_QUOTIENT_GROUP = prove
 (`!G n:A->bool.
     cyclic_group G /\ n subgroup_of G ==> cyclic_group(quotient_group G n)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(n:A->bool) normal_subgroup_of G` THENL
   [ALL_TAC;
    ASM_MESON_TAC[ABELIAN_GROUP_NORMAL_SUBGROUP;
                  CYCLIC_IMP_ABELIAN_GROUP]] THEN
  REWRITE_TAC[CYCLIC_GROUP] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `right_coset G n (x:A)` THEN
  ASM_SIMP_TAC[QUOTIENT_GROUP] THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; ETA_AX] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_UNIV; o_THM] THEN EXISTS_TAC `&1:int` THEN
    ASM_SIMP_TAC[GROUP_ZPOW_1];
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[QUOTIENT_GROUP_ZPOW; o_THM]]);;

let NO_PROPER_SUBGROUPS_IMP_CYCLIC = prove
 (`!G:A group.
        (!h. h subgroup_of G ==> h SUBSET {group_id G} \/ h = group_carrier G)
        ==> cyclic_group G`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `trivial_group(G:A group)` THEN
  ASM_SIMP_TAC[TRIVIAL_IMP_CYCLIC_GROUP] THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE RAND_CONV [TRIVIAL_GROUP_SUBSET]) THEN
  REWRITE_TAC[SET_RULE `~(s SUBSET {a}) <=> ?x. x IN s /\ ~(x = a)`] THEN
  REWRITE_TAC[cyclic_group] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `group_carrier (subgroup_generated G {a:A})`) THEN
  REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
  ASM_SIMP_TAC[IN_SING; SUBGROUP_GENERATED_INC; IN_SING; SING_SUBSET]);;

let [FINITE_CYCLIC_SUBGROUP; INFINITE_CYCLIC_SUBGROUP;
     FINITE_CYCLIC_SUBGROUP_ALT; INFINITE_CYCLIC_SUBGROUP_ALT] =
 (CONJUNCTS o prove)
 (`(!G x:A.
        x IN group_carrier G
        ==> (FINITE(group_carrier(subgroup_generated G {x})) <=>
             ?n. ~(n = 0) /\ group_pow G x n = group_id G)) /\
   (!G x:A.
        x IN group_carrier G
        ==> (INFINITE(group_carrier(subgroup_generated G {x})) <=>
             !m n. group_pow G x m = group_pow G x n ==> m = n)) /\
   (!G x:A.
        x IN group_carrier G
        ==> (FINITE(group_carrier(subgroup_generated G {x})) <=>
             ?n. ~(n = &0) /\ group_zpow G x n = group_id G)) /\
   (!G x:A.
        x IN group_carrier G
        ==> (INFINITE(group_carrier(subgroup_generated G {x})) <=>
             !m n. group_zpow G x m = group_zpow G x n ==> m = n))`,
  REWRITE_TAC[INFINITE; AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:A) IN group_carrier G` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(r ==> ~p) /\ (r' ==> r) /\ (~r' ==> q) /\ (q ==> q') /\ (q' ==> p)
    ==> (p <=> q) /\ (~p <=> r) /\ (p <=> q') /\ (~p <=> r')`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `(:num)` o MATCH_MP INFINITE_IMAGE_INJ) THEN
    ASM_SIMP_TAC[num_INFINITE; CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
    REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[GSYM GROUP_NPOW] THEN SET_TAC[];
    REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_EQ] THEN SET_TAC[];
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
    MATCH_MP_TAC INT_WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:int`; `n:int`] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `num_of_int(n - m)` THEN
    ASM_SIMP_TAC[GSYM GROUP_NPOW; INT_OF_NUM_OF_INT; INT_LT_IMP_LE;
                 INT_SUB_LT; GSYM INT_OF_NUM_EQ; INT_SUB_0; GROUP_ZPOW_SUB;
                 GROUP_DIV_REFL; GROUP_ZPOW];
    REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM GROUP_NPOW] THEN MESON_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `?n. ~(n = 0) /\ group_pow G (x:A) n = group_id G`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `num_of_int(abs n)` THEN
      REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_EQ] THEN
      SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_ABS_ZERO] THEN
      ASM_REWRITE_TAC[INT_ABS] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[GROUP_ZPOW_NEG; GROUP_INV_ID];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (group_pow G (x:A)) (0..n)` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; SUBSET] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; IN_IMAGE; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `a:int` THEN
      MP_TAC(ISPECL [`a:int`; `&n:int`] INT_DIVISION) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      SPEC_TAC(`a rem &n`,`b:int`) THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
      REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS; INT_ABS_NUM;
                  INT_OF_NUM_LT] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[LT_IMP_LE; GROUP_ZPOW_ADD; GROUP_ZPOW_MUL] THEN
      ASM_REWRITE_TAC[GROUP_NPOW; GROUP_ZPOW_ID] THEN
      ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_POW]]]);;

let FINITE_CYCLIC_SUBGROUP_ORDER = prove
 (`!G x:A.
        x IN group_carrier G
        ==> (FINITE(group_carrier(subgroup_generated G {x})) <=>
             ~(group_element_order G x = 0))`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_0; FINITE_CYCLIC_SUBGROUP] THEN
  MESON_TAC[]);;

let INFINITE_CYCLIC_SUBGROUP_ORDER = prove
  (`!G x:A.
        x IN group_carrier G
        ==> (INFINITE (group_carrier(subgroup_generated G {x})) <=>
             group_element_order G x = 0)`,
  SIMP_TAC[INFINITE; FINITE_CYCLIC_SUBGROUP_ORDER]);;

let FINITE_CYCLIC_SUBGROUP_EXPLICIT = prove
 (`!G x:A.
        FINITE(group_carrier(subgroup_generated G {x})) /\ x IN group_carrier G
        ==> group_carrier(subgroup_generated G {x}) =
            {group_pow G x n |n| n < group_element_order G x}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV; GSYM GROUP_NPOW] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[GROUP_ZPOW_EQ_ALT]; MESON_TAC[]] THEN
  X_GEN_TAC `n:int` THEN
  MP_TAC(ISPECL [`n:int`; `&(group_element_order G (x:A)):int`]
        INT_DIVISION) THEN
  SPEC_TAC(`n div &(group_element_order G (x:A))`,`q:int`) THEN
  SPEC_TAC(`n rem &(group_element_order G (x:A))`,`r:int`) THEN
  REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[INT_OF_NUM_EQ; GSYM FINITE_CYCLIC_SUBGROUP_ORDER] THEN
  REWRITE_TAC[INT_ABS_NUM] THEN STRIP_TAC THEN EXISTS_TAC `num_of_int r` THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; GSYM INT_OF_NUM_LT] THEN
  CONV_TAC INTEGER_RULE);;

let CARD_CYCLIC_SUBGROUP_ORDER = prove
 (`!G x:A.
        FINITE(group_carrier(subgroup_generated G {x})) /\ x IN group_carrier G
        ==> CARD(group_carrier(subgroup_generated G {x})) =
            group_element_order G x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FINITE_CYCLIC_SUBGROUP_EXPLICIT] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN MATCH_MP_TAC WLOG_LE THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM GROUP_NPOW; GROUP_ZPOW_EQ_ALT; INT_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM num_divides] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let PRIME_ORDER_IMP_NO_PROPER_SUBGROUPS = prove
 (`!(G:A group) p.
        (group_carrier G) HAS_SIZE p /\ (p = 1 \/ prime p)
        ==> !h. h subgroup_of G
                ==> h = {group_id G} \/ h = group_carrier G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE; ONE_OR_PRIME] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT `p ==> q \/ r <=> p /\ ~q ==> r`]) THEN
  MATCH_MP_TAC(SET_RULE
   `z IN s /\ (!x. x IN s /\ ~(x = z) ==> s = t) ==> s = {z} \/ s = t`) THEN
  ASM_SIMP_TAC[IN_SUBGROUP_ID] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`] LAGRANGE_THEOREM) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= n ==> ~(n = 1)`) THEN
  TRANS_TAC LE_TRANS `CARD {group_id G:A,x}` THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; ARITH];
    MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[subgroup_of; FINITE_SUBSET]]);;

let PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS,
    NO_PROPER_SUBGROUPS_EQ_CYCLIC_PRIME_ORDER = (CONJ_PAIR o prove)
 (`(!(G:A group).
        FINITE(group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G))) <=>
        !h. h subgroup_of G ==> h = {group_id G} \/ h = group_carrier G) /\
   (!(G:A group).
        (!h. h subgroup_of G ==> h = {group_id G} \/ h = group_carrier G) <=>
        cyclic_group G /\
        FINITE(group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G))))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> n) /\ (n ==> c) /\ (c /\ n ==> p)
    ==> (p <=> n) /\ (n <=> c /\ p)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC PRIME_ORDER_IMP_NO_PROPER_SUBGROUPS THEN
    REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC NO_PROPER_SUBGROUPS_IMP_CYCLIC THEN
    ASM SET_TAC[];
    STRIP_TAC THEN REWRITE_TAC[ONE_OR_PRIME]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cyclic_group]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:A group`; `x:A`] INFINITE_CYCLIC_SUBGROUP_ALT) THEN
  ASM_REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT `(~p <=> q) ==> ~q ==> p`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC
     `{group_zpow G (group_zpow G (x:A) (&2)) n | n IN (:int)}`) THEN
    ASM_SIMP_TAC[SUBGROUP_OF_POWERS; GROUP_ZPOW; GSYM GROUP_ZPOW_MUL] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `{f n | n IN (:int)} = {a} ==> f(&1) = a`)) THEN
      DISCH_TAC THEN
      DISCH_THEN(MP_TAC o SPECL [`&2 * &1:int`; `&0:int`]) THEN
      ASM_REWRITE_TAC[GROUP_ZPOW_0] THEN CONV_TAC INT_ARITH;
      REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:int` (STRIP_ASSUME_TAC o GSYM)) THEN
      DISCH_THEN(MP_TAC o SPECL [`&2 * n:int`; `&1:int`]) THEN
      ASM_SIMP_TAC[GROUP_ZPOW_1] THEN MATCH_MP_TAC(INT_ARITH
       `n:int <= &0 \/ &1 <= n ==> ~(&2 * n = &1)`) THEN
      INT_ARITH_TAC];
    DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0;GROUP_CARRIER_NONEMPTY; NUMBER_RULE
   `0 divides n <=> n = 0`] THEN
  DISCH_TAC THEN
  ABBREV_TAC `m = CARD(group_carrier(G:A group)) DIV n` THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[DIV_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY; NOT_LT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `group_carrier(subgroup_generated G {group_pow G x m:A})`) THEN
  SUBGOAL_THEN `group_element_order G (group_pow G (x:A) m) = n`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      GROUP_ELEMENT_ORDER_POW o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `CARD(group_carrier G:A->bool) DIV n = m` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    ASM_SIMP_TAC[GSYM CARD_CYCLIC_SUBGROUP_ORDER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST1_TAC) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[DIV_MULT] THEN DISCH_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(group_carrier (subgroup_generated G {group_pow G x m:A}))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CYCLIC_SUBGROUP_ORDER; GROUP_POW] THEN
    ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_POW];
    ALL_TAC] THEN
  REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `CARD:(A->bool)->num`) THEN
  ASM_SIMP_TAC[CARD_CYCLIC_SUBGROUP_ORDER; GROUP_POW; CARD_SING]);;

let ABELIAN_SIMPLE_GROUP = prove
 (`!G:A group.
        abelian_group G
        ==> ((!h. h normal_subgroup_of G
                  ==> h = {group_id G} \/ h = group_carrier G) <=>
             FINITE(group_carrier G) /\
             (CARD (group_carrier G) = 1 \/ prime(CARD(group_carrier G))))`,
  REWRITE_TAC[PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS] THEN
  SIMP_TAC[ABELIAN_GROUP_NORMAL_SUBGROUP]);;

let PRIME_ORDER_IMP_CYCLIC_GROUP = prove
 (`!G:A group.
        FINITE(group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G)))
        ==> cyclic_group G`,
  REWRITE_TAC[PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS] THEN
  REWRITE_TAC[NO_PROPER_SUBGROUPS_EQ_CYCLIC_PRIME_ORDER] THEN
  SIMP_TAC[]);;

let GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER = prove
 (`!G x:A.
        x IN group_carrier G /\ FINITE(group_carrier G)
        ==> (group_element_order G x) divides CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CARD_CYCLIC_SUBGROUP_ORDER; FINITE_SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC LAGRANGE_THEOREM THEN
  ASM_REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED]);;

let GROUP_POW_GROUP_ORDER = prove
 (`!G x:A.
        x IN group_carrier G /\ FINITE(group_carrier G)
        ==> group_pow G x (CARD(group_carrier G)) = group_id G`,
  SIMP_TAC[GROUP_POW_EQ_ID; GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER]);;

let SUBGROUP_OF_FINITE_CYCLIC_GROUP = prove
 (`!G h a:A.
        FINITE(group_carrier G) /\
        a IN group_carrier G /\
        subgroup_generated G {a} = G
        ==> (h subgroup_of G <=>
             ?d. d divides CARD(group_carrier G) /\
                 h = group_carrier(subgroup_generated G {group_pow G a d}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; MESON_TAC[SUBGROUP_SUBGROUP_GENERATED]] THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`; `a:A`]
        SUBGROUP_OF_CYCLIC_GROUP_EXPLICIT) THEN
  ASM_SIMP_TAC[GROUP_ZPOW_MUL] THEN
  ASM_SIMP_TAC[GSYM CARRIER_SUBGROUP_GENERATED_BY_SING; GROUP_ZPOW] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  EXISTS_TAC `gcd(k,CARD(group_carrier G:A->bool))` THEN
  ASM_REWRITE_TAC[GCD] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; GROUP_POW; GROUP_NPOW] THEN
  REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; IN_UNIV] THEN
  ASM_SIMP_TAC[GSYM GROUP_NPOW; GSYM GROUP_ZPOW_MUL; GROUP_ZPOW_EQ] THEN
  REWRITE_TAC[NUM_GCD] THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:A group`; `a:A`] CARD_CYCLIC_SUBGROUP_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC INTEGER_RULE);;

let COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS = prove
 (`!(G:A group) d.
        FINITE(group_carrier G) /\ cyclic_group G
        ==> (CARD {h | h subgroup_of G /\ CARD h = d} =
             if d divides CARD(group_carrier G) then 1 else 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC o REWRITE_RULE[cyclic_group]) THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(MESON[HAS_SIZE] `s HAS_SIZE 1 ==> CARD s = 1`);
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICTED_SUBGROUPS] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[LAGRANGE_THEOREM]] THEN
  CONV_TAC HAS_SIZE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `~(d * k = 0)` MP_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY];
    REWRITE_TAC[DE_MORGAN_THM; MULT_EQ_0] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`G:A group`; `a:A`] CARD_CYCLIC_SUBGROUP_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MATCH_MP_TAC(SET_RULE
   `(?x. P x) /\ (!x. P x ==> !x'. P x' ==> x = x')
    ==> ?a. {x | P x} = {a}`) THEN
  MP_TAC(GEN `h:A->bool` (ISPECL [`G:A group`; `h:A->bool`; `a:A`]
        SUBGROUP_OF_FINITE_CYCLIC_GROUP)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
   [REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
    EXISTS_TAC `k:num` THEN REWRITE_TAC[UNWIND_THM2] THEN
    ASM_SIMP_TAC[CARD_CYCLIC_SUBGROUP_ORDER; FINITE_SUBGROUP_GENERATED;
                 GROUP_POW] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[divides; MULT_SYM]; ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_POW_GEN] THEN
    SIMP_TAC[NUMBER_RULE `k divides g ==> gcd(g:num,k) = k`] THEN
    ASM_MESON_TAC[MULT_SYM; DIV_MULT];
    REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `k1:num` THEN
    GEN_REWRITE_TAC BINDER_CONV [IMP_CONJ] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `k2:num` THEN
    GEN_REWRITE_TAC BINDER_CONV [IMP_CONJ] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_SIMP_TAC[CARD_CYCLIC_SUBGROUP_ORDER; GROUP_POW;
                 FINITE_SUBGROUP_GENERATED; GROUP_ELEMENT_ORDER_POW_GEN] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[DIVIDES_ZERO; MULT_EQ_0]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[DIVIDES_ZERO; MULT_EQ_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[NUMBER_RULE `k divides g ==> gcd(g:num,k) = k`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUM_RING
     `g DIV k2 = g DIV k1
      ==> g DIV k1 * k1 = g /\ g DIV k2 * k2 = g /\ ~(g = 0)
          ==> k1 = k2`)) THEN
    ASM_REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
    ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY]]);;

let COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS_ALL = prove
 (`!G:A group.
      FINITE(group_carrier G) /\ cyclic_group G
      ==> CARD {h | h subgroup_of G} =
          CARD {d | d divides CARD(group_carrier G)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[CARD_IMAGE_INJ]
   `!f. FINITE s /\
        t = IMAGE f s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> CARD s = CARD t`) THEN
  EXISTS_TAC `CARD:(A->bool)->num` THEN ASM_SIMP_TAC[FINITE_SUBGROUPS] THEN
  MATCH_MP_TAC(SET_RULE
   `(!y. y IN t ==> ?a. {x | x IN s /\ f x = y} = {a}) /\
    (!y. ~(y IN t) ==> {x | x IN s /\ f x = y} = {})
    ==> t = IMAGE f s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`) THEN
  REWRITE_TAC[GSYM(HAS_SIZE_CONV `s HAS_SIZE 1`); GSYM HAS_SIZE_0] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; HAS_SIZE; FINITE_RESTRICTED_SUBGROUPS] THEN
  ASM_SIMP_TAC[COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS]);;

let MAXIMAL_SUBGROUP_PRIME_INDEX = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> ((!h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G) <=>
             FINITE {right_coset G n x | x | x IN group_carrier G} /\
             (CARD {right_coset G n x | x | x IN group_carrier G} = 1 \/
              prime(CARD {right_coset G n x | x | x IN group_carrier G})))`,
  SIMP_TAC[MAXIMAL_SUBGROUP; GSYM PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS] THEN
  SIMP_TAC[QUOTIENT_GROUP]);;

let PRIME_INDEX_MAXIMAL_PROPER_SUBGROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> (FINITE {right_coset G n x | x | x IN group_carrier G} /\
             prime(CARD {right_coset G n x | x | x IN group_carrier G}) <=>
             ~(n = group_carrier G) /\
             !h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G)`,
  SIMP_TAC[MAXIMAL_SUBGROUP_PRIME_INDEX] THEN
  SIMP_TAC[GSYM TRIVIAL_QUOTIENT_GROUP_EQ] THEN
  SIMP_TAC[TRIVIAL_GROUP_HAS_SIZE_1; QUOTIENT_GROUP; HAS_SIZE] THEN
  MESON_TAC[prime]);;

let MAXIMAL_PROPER_SUBGROUP_PRIME_INDEX = prove
 (`!G n:A->bool.
        n normal_subgroup_of G /\ ~(n = group_carrier G)
        ==> ((!h. h subgroup_of G /\ n PSUBSET h ==> h = group_carrier G) <=>
             FINITE {right_coset G n x | x | x IN group_carrier G} /\
             prime(CARD {right_coset G n x | x | x IN group_carrier G}))`,
  SIMP_TAC[PRIME_INDEX_MAXIMAL_PROPER_SUBGROUP]);;

let GROUP_ZPOW_CANCEL = prove
 (`!G n x y:A.
        FINITE(group_carrier G) /\ coprime(n,&(CARD(group_carrier G))) /\
        x IN group_carrier G /\ y IN group_carrier G /\
        group_zpow G x n = group_zpow G y n
        ==> x = y`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(SET_RULE
   `(?g. (!x. x IN s ==> g(f x) = x))
    ==> !x y. x IN s /\ y IN s /\ f x = f y ==> x = y`) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:int` o MATCH_MP (INTEGER_RULE
   `coprime(n:int,g) ==> ?m. (n * m == &1) (mod g)`)) THEN
  EXISTS_TAC `\x:A. group_zpow G x m` THEN SIMP_TAC[GSYM GROUP_ZPOW_MUL] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `group_zpow G (x:A) (&1)` THEN
  ASM_SIMP_TAC[GROUP_ZPOW_EQ] THEN ASM_SIMP_TAC[GROUP_ZPOW_1] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(a:int == b) (mod d) ==> e divides d ==> (a == b) (mod e)`)) THEN
  ASM_SIMP_TAC[GSYM num_divides; GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER]);;

let GROUP_POW_CANCEL = prove
 (`!G n x y:A.
        FINITE(group_carrier G) /\ coprime(n,CARD(group_carrier G)) /\
        x IN group_carrier G /\ y IN group_carrier G /\
        group_pow G x n = group_pow G y n
        ==> x = y`,
  REWRITE_TAC[num_coprime; GSYM GROUP_NPOW; GROUP_ZPOW_CANCEL]);;

(* ------------------------------------------------------------------------- *)
(* The additive group of integers.                                           *)
(* ------------------------------------------------------------------------- *)

let integer_group = new_definition
 `integer_group = group((:int),&0,(--),(+))`;;

let INTEGER_GROUP = prove
 (`group_carrier integer_group = (:int) /\
   group_id integer_group = &0 /\
   group_inv integer_group = (--) /\
   group_mul integer_group = (+)`,
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl integer_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM integer_group] THEN REWRITE_TAC[IN_UNIV] THEN
  ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;

let ABELIAN_INTEGER_GROUP = prove
 (`abelian_group integer_group`,
  REWRITE_TAC[abelian_group; INTEGER_GROUP; INT_ADD_SYM]);;

let INFINITE_INTEGER_GROUP = prove
 (`INFINITE(group_carrier integer_group)`,
  REWRITE_TAC[INTEGER_GROUP; int_INFINITE]);;

let GROUP_POW_INTEGER_GROUP = prove
 (`!x n. group_pow integer_group x n = &n * x`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_pow; INTEGER_GROUP; GSYM INT_OF_NUM_SUC] THEN
  INT_ARITH_TAC);;

let GROUP_ZPOW_INTEGER_GROUP = prove
 (`!x n. group_zpow integer_group x n = n * x`,
  GEN_TAC THEN
  SIMP_TAC[FORALL_INT_CASES; GROUP_ZPOW_NEG; GROUP_NPOW;
           INTEGER_GROUP; GROUP_POW_INTEGER_GROUP; IN_UNIV] THEN
  INT_ARITH_TAC);;

let GROUP_ENDOMORPHISM_INTEGER_GROUP_MUL = prove
 (`!c. group_endomorphism integer_group (\x. c * x)`,
  REWRITE_TAC[group_endomorphism; group_homomorphism; INTEGER_GROUP] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN INT_ARITH_TAC);;

let GROUP_ENDOMORPHISM_INTEGER_GROUP_EXPLICIT = prove
 (`!f. group_endomorphism integer_group f ==> f = \x. f(&1) * x`,
  REWRITE_TAC[group_endomorphism; group_homomorphism; INTEGER_GROUP] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `x:int` THEN
  REWRITE_TAC[] THEN MP_TAC(SPEC `x:int` INT_IMAGE) THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  SPEC_TAC(`x:int`,`x:int`) THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  ASM_REWRITE_TAC[FORALL_UNWIND_THM2; INT_ARITH
   `--x:int = y * --z <=> x = y * z`] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[INT_MUL_RZERO] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC);;

let GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ,
    GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ_ALT =
 (CONJ_PAIR o prove)
 (`(!f. group_endomorphism integer_group f <=> ?c. f = \x. c * x) /\
   (!f. group_endomorphism integer_group f <=> ?!c. f = \x. c * x)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!c. P(m c)) /\ (!f. P f ==> ?c. f = m c) /\
    (!c d. m c = m d ==> c = d)
    ==> (P f <=> ?c. f = m c) /\ (P f <=> ?!c. f = m c)`) THEN
  REWRITE_TAC[GROUP_ENDOMORPHISM_INTEGER_GROUP_MUL] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:int->int` THEN DISCH_TAC THEN
    EXISTS_TAC `(f:int->int) (&1)` THEN
   MATCH_MP_TAC GROUP_ENDOMORPHISM_INTEGER_GROUP_EXPLICIT THEN
   ASM_REWRITE_TAC[];
   REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[INT_MUL_RID]]);;

let GROUP_HOMOMORPHISM_GROUP_ZPOW = prove
 (`!G x:A. x IN group_carrier G
           ==> group_homomorphism(integer_group,G) (group_zpow G x)`,
  REWRITE_TAC[group_homomorphism; INTEGER_GROUP; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[IN_UNIV; GROUP_ZPOW_ADD; GROUP_ZPOW_NEG;
           GROUP_ZPOW_0; GROUP_ZPOW]);;

let GROUP_EPIMORPHISM_GROUP_ZPOW = prove
 (`!G x:A. x IN group_carrier G
           ==> group_epimorphism (integer_group,subgroup_generated G {x})
                                 (group_zpow G x)`,
  SIMP_TAC[group_epimorphism; INTEGER_GROUP; SIMPLE_IMAGE; ETA_AX;
           CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED] THEN
  MATCH_MP_TAC GROUP_HOMOMORPHISM_INTO_SUBGROUP THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_ZPOW] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; INTEGER_GROUP] THEN
  SET_TAC[]);;

let GROUP_ISOMORPHISM_GROUP_ZPOW = prove
 (`!G x:A. INFINITE(group_carrier(subgroup_generated G {x})) /\
           x IN group_carrier G
           ==> group_isomorphism (integer_group,subgroup_generated G {x})
                                 (group_zpow G x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_EPIMORPHISM_GROUP_ZPOW) THEN
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM;
           group_monomorphism; group_epimorphism] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[INTEGER_GROUP; IN_UNIV] THEN
  ASM_MESON_TAC[INFINITE_CYCLIC_SUBGROUP_ALT]);;

let ISOMORPHIC_GROUP_INFINITE_CYCLIC_INTEGER = prove
 (`!G:A group.
        cyclic_group G /\ INFINITE(group_carrier G)
        ==> G isomorphic_group integer_group`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cyclic_group]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:A group`; `x:A`] GROUP_ISOMORPHISM_GROUP_ZPOW) THEN
  ASM_REWRITE_TAC[GROUP_ISOMORPHISM_IMP_ISOMORPHIC]);;

let ISOMORPHIC_INFINITE_CYCLIC_GROUPS = prove
 (`!(G:A group) (H:B group).
        cyclic_group G /\ INFINITE(group_carrier G) /\
        cyclic_group H /\ INFINITE(group_carrier H)
        ==> G isomorphic_group H`,
  REPEAT STRIP_TAC THEN TRANS_TAC ISOMORPHIC_GROUP_TRANS `integer_group` THEN
  GEN_REWRITE_TAC RAND_CONV [ISOMORPHIC_GROUP_SYM] THEN
  ASM_SIMP_TAC[ISOMORPHIC_GROUP_INFINITE_CYCLIC_INTEGER]);;

(* ------------------------------------------------------------------------- *)
(* Additive group of integers modulo n (n = 0 gives just the integers).      *)
(* ------------------------------------------------------------------------- *)

let integer_mod_group = new_definition
  `integer_mod_group n =
     if n = 0 then integer_group else
     group({m | &0 <= m /\ m < &n},
           &0,
           (\a. --a rem &n),
           (\a b. (a + b) rem &n))`;;

let INTEGER_MOD_GROUP = prove
 (`(group_carrier(integer_mod_group 0) = (:int)) /\
   (!n. 0 < n
        ==> group_carrier(integer_mod_group n) = {m | &0 <= m /\ m < &n}) /\
   (!n. group_id(integer_mod_group n) = &0) /\
   (!n. group_inv(integer_mod_group n) = \a. --a rem &n) /\
   (!n. group_mul(integer_mod_group n) = \a b. (a + b) rem &n)`,
  REWRITE_TAC[integer_mod_group; INTEGER_GROUP] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_GROUP; LT_REFL; INT_REM_0] THENL
   [REWRITE_TAC[FUN_EQ_THM]; ASM_SIMP_TAC[LE_1]] THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul] THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM(CONJUNCT2 group_tybij)] THEN
  MP_TAC(GEN `m:int` (SPECL [`m:int`; `&n:int`] INT_DIVISION)) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_ABS_NUM; FORALL_AND_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; INT_LE_REFL] THEN
  ASM_SIMP_TAC[INT_OF_NUM_LT; LE_1; INT_ADD_LID; INT_ADD_RID] THEN
  SIMP_TAC[INT_REM_LT] THEN
  ONCE_REWRITE_TAC[GSYM INT_ADD_REM] THEN
  REWRITE_TAC[INT_REM_REM] THEN REWRITE_TAC[INT_ADD_REM; INT_ADD_ASSOC] THEN
  REWRITE_TAC[INT_ADD_LINV; INT_ADD_RINV; INT_REM_ZERO]);;

let GROUP_CARRIER_INTEGER_MOD_GROUP = prove
 (`!n. group_carrier (integer_mod_group n) = IMAGE (\x. x rem &n) (:int)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[INTEGER_MOD_GROUP; INT_REM_0; IMAGE_ID; LE_1] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) /\ (!x. f x IN s)
    ==> s = IMAGE f UNIV`) THEN
  SIMP_TAC[IN_ELIM_THM; INT_REM_LT] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  ASM_SIMP_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT; LE_1]);;

let GROUP_POW_INTEGER_MOD_GROUP = prove
 (`!n x m. group_pow (integer_mod_group n) x m = (&m * x) rem &n`,
  GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[INT_REM_0; integer_mod_group; GROUP_POW_INTEGER_GROUP];
    INDUCT_TAC THEN
    ASM_REWRITE_TAC[group_pow; INTEGER_MOD_GROUP; INT_MUL_LZERO; INT_REM_ZERO;
                    GSYM INT_OF_NUM_SUC; INT_ADD_RDISTRIB; INT_MUL_LID] THEN
    ONCE_REWRITE_TAC[GSYM INT_ADD_REM] THEN
    REWRITE_TAC[INT_REM_REM] THEN REWRITE_TAC[INT_ADD_SYM]]);;

let GROUP_ZPOW_INTEGER_MOD_GROUP = prove
 (`!n x m. group_zpow (integer_mod_group n) x m = (m * x) rem &n`,
  REWRITE_TAC[FORALL_INT_CASES] THEN
  REWRITE_TAC[GROUP_ZPOW_POW; GROUP_POW_INTEGER_MOD_GROUP] THEN
  REWRITE_TAC[INTEGER_MOD_GROUP; INT_REM_EQ; INTEGER_RULE
    `(--x:int == y) (mod n) <=> (x == --y) (mod n)`] THEN
  REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let ABELIAN_INTEGER_MOD_GROUP = prove
 (`!n. abelian_group(integer_mod_group n)`,
  REWRITE_TAC[abelian_group; INTEGER_MOD_GROUP; INT_ADD_SYM]);;

let INTEGER_MOD_GROUP_0 = prove
 (`!n. &0 IN group_carrier(integer_mod_group n)`,
  MESON_TAC[INTEGER_MOD_GROUP; GROUP_ID]);;

let INTEGER_MOD_GROUP_1R = prove
 (`!n x. (x rem &n) IN group_carrier(integer_mod_group n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  ASM_SIMP_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT; LE_1]);;

let INTEGER_MOD_GROUP_1 = prove
 (`!n. &1 IN group_carrier(integer_mod_group n) <=> ~(n = 1)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_group; INTEGER_GROUP; IN_UNIV] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[LE_1; INTEGER_MOD_GROUP; IN_ELIM_THM] THEN
    REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

let GROUP_HOMOMORPHISM_PROD_INTEGER_MOD_GROUP = prove
 (`!m n.
        group_homomorphism
         (integer_mod_group (m * n),
          prod_group (integer_mod_group m) (integer_mod_group n))
         (\a. (a rem &m),(a rem &n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM] THEN
  SIMP_TAC[PROD_GROUP; SUBSET; FORALL_IN_IMAGE; IN_CROSS; PAIR_EQ] THEN
  SIMP_TAC[INTEGER_MOD_GROUP; GSYM INT_OF_NUM_MUL; INT_REM_REM_MUL] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INTEGER_MOD_GROUP_1R]);;

let TRIVIAL_INTEGER_MOD_GROUP = prove
 (`!n. trivial_group(integer_mod_group n) <=> n = 1`,
  GEN_TAC THEN ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[TRIVIAL_GROUP_SUBSET; INTEGER_MOD_GROUP; ARITH] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN INT_ARITH_TAC;
    REWRITE_TAC[TRIVIAL_GROUP_ALT] THEN MATCH_MP_TAC(SET_RULE
     `!a b. (a IN s /\ b IN s /\ ~(a = b)) ==> ~(?c. s SUBSET {c})`) THEN
    MAP_EVERY EXISTS_TAC [`&0:int`; `&1:int`] THEN
    ASM_REWRITE_TAC[INTEGER_MOD_GROUP_0; INTEGER_MOD_GROUP_1] THEN
    CONV_TAC INT_REDUCE_CONV]);;

let NON_TRIVIAL_INTEGER_GROUP = prove
 (`~(trivial_group integer_group)`,
  MP_TAC(SPEC `0` TRIVIAL_INTEGER_MOD_GROUP) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[integer_mod_group]);;

let GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1 = prove
 (`!n. group_element_order (integer_mod_group n) (&1) = n`,
  SIMP_TAC[group_element_order; INTEGER_MOD_GROUP] THEN
  SIMP_TAC[GROUP_POW_INTEGER_MOD_GROUP] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; MULT_CLAUSES; INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; GSYM DIVIDES_MOD] THEN
  GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MESON_TAC[DIVIDES_ANTISYM]);;

let GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1R = prove
 (`!n. group_element_order (integer_mod_group n) (&1 rem &n) = n`,
  SIMP_TAC[group_element_order; INTEGER_MOD_GROUP] THEN
  SIMP_TAC[GROUP_POW_INTEGER_MOD_GROUP] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_OF_NUM_MUL; MULT_CLAUSES; INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; GSYM DIVIDES_MOD] THEN
  GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MESON_TAC[DIVIDES_ANTISYM]);;

let GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP = prove
 (`!n m. group_element_order (integer_mod_group n) (&m) =
         if m = 0 /\ n = 0 then 1 else n DIV gcd(n,m)`,
  REPEAT GEN_TAC THEN TRANS_TAC EQ_TRANS
   `group_element_order (integer_mod_group n) ((&m * &1 rem &n) rem &n)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[group_element_order; GROUP_POW_INTEGER_MOD_GROUP] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM GROUP_POW_INTEGER_MOD_GROUP] THEN
  SIMP_TAC[GROUP_ELEMENT_ORDER_POW_GEN; INTEGER_MOD_GROUP_1R] THEN
  REWRITE_TAC[GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1R] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_REFL; NUMBER_RULE `gcd(n,0) = n`]);;

let INTEGER_MOD_SUBGROUP_GENERATED_BY_1R = prove
 (`!n. subgroup_generated (integer_mod_group n) {&1 rem &n} =
       integer_mod_group n`,
  GEN_TAC THEN REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; INTEGER_MOD_GROUP_1R] THEN
    REWRITE_TAC[GROUP_ZPOW_INTEGER_MOD_GROUP] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_RID] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[INTEGER_MOD_GROUP; INT_REM_0; IN_GSPEC; LE_1] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. f x IN s) /\ (!x. x IN s ==> f x = x)
   ==> {f x | x IN UNIV} = s`) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; INT_DIVISION; INT_OF_NUM_EQ;
               INT_LT_REM; INT_OF_NUM_LT; LE_1; INT_REM_LT]);;

let INTEGER_MOD_SUBGROUP_GENERATED_BY_1 = prove
 (`!n. subgroup_generated (integer_mod_group n) {&1} =
       integer_mod_group n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 1` THEN
  ASM_SIMP_TAC[TRIVIAL_GROUP_GENERATED_BY_ANYTHING;
               TRIVIAL_INTEGER_MOD_GROUP] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM INTEGER_MOD_SUBGROUP_GENERATED_BY_1R] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[INT_REM_EQ_SELF] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LE; INT_OF_NUM_LT; INT_ABS_NUM] THEN
  ASM_ARITH_TAC);;

let CYCLIC_GROUP_INTEGER_MOD_GROUP = prove
 (`!n. cyclic_group(integer_mod_group n)`,
  ONCE_REWRITE_TAC[GSYM INTEGER_MOD_SUBGROUP_GENERATED_BY_1] THEN
  REWRITE_TAC[CYCLIC_GROUP_GENERATED]);;

let CYCLIC_INTEGER_GROUP = prove
 (`cyclic_group integer_group`,
  MP_TAC(SPEC `0` CYCLIC_GROUP_INTEGER_MOD_GROUP) THEN
  REWRITE_TAC[integer_mod_group]);;

let FINITE_INTEGER_MOD_GROUP = prove
 (`!n. FINITE(group_carrier(integer_mod_group n)) <=> ~(n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; int_INFINITE; GSYM INFINITE] THEN
  REWRITE_TAC[FINITE_INT_SEG]);;

let GROUP_EPIMORPHISM_INTEGER_MOD_GROUP_ZPOW = prove
 (`!n. ~(n = 1)
       ==> group_epimorphism (integer_group,integer_mod_group n)
                             (group_zpow (integer_mod_group n) (&1))`,
  MESON_TAC[INTEGER_MOD_GROUP_1; INTEGER_MOD_SUBGROUP_GENERATED_BY_1;
            GROUP_EPIMORPHISM_GROUP_ZPOW; GROUP_ZPOW_SUBGROUP_GENERATED]);;

let GROUP_ISOMORPHISM_GROUP_ZPOW_GEN = prove
 (`!G x:A.
        x IN group_carrier G
        ==> group_isomorphism (integer_mod_group (group_element_order G x),
                               subgroup_generated G {x})
                              (group_zpow G x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `group_element_order G (x:A) = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_group] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_GROUP_ZPOW THEN
    ASM_SIMP_TAC[INFINITE; FINITE_CYCLIC_SUBGROUP_ORDER];
    REWRITE_TAC[GROUP_ISOMORPHISM_ALT] THEN
    ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; CONJUNCT2 SUBGROUP_GENERATED]] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[SET_RULE `y IN IMAGE f {x | P x} <=> ?x. P x /\ f x = y`] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_EQ_ID; GSYM GROUP_ZPOW_ADD; GROUP_ZPOW_EQ_ALT] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; GSYM INT_EXISTS_POS; GSYM CONJ_ASSOC] THEN
  ASM_SIMP_TAC[GROUP_ZPOW; INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[FINITE_CYCLIC_SUBGROUP_EXPLICIT; FINITE_CYCLIC_SUBGROUP_ORDER;
               FORALL_IN_GSPEC; GROUP_ZPOW_POW; INT_REM_DIV] THEN
  REWRITE_TAC[INTEGER_RULE `(d:int) divides (n - (n - q * d))`] THEN
  REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[GSYM num_divides; INT_OF_NUM_EQ] THEN
  MESON_TAC[DIVIDES_LE; NOT_LE]);;

let ISOMORPHIC_GROUP_CYCLIC_INTEGER = prove
 (`!G:A group. cyclic_group G <=> ?n. G isomorphic_group integer_mod_group n`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[cyclic_group] THEN
    MESON_TAC[GROUP_ISOMORPHISM_GROUP_ZPOW_GEN; ISOMORPHIC_GROUP_SYM;
              isomorphic_group];
    MESON_TAC[ISOMORPHIC_GROUP_CYCLICITY; CYCLIC_GROUP_INTEGER_MOD_GROUP]]);;

let ORDER_INTEGER_MOD_GROUP = prove
 (`!n. ~(n = 0) ==> CARD(group_carrier(integer_mod_group n)) = n`,
  SIMP_TAC[INTEGER_MOD_GROUP; LE_1] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{m:int | &0 <= m /\ m < &n} = IMAGE (&) {i | i < n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
    SIMP_TAC[IN_ELIM_THM; IN_IMAGE; INT_OF_NUM_LT; INT_POS] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ] THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_EQ; UNWIND_THM1];
    SIMP_TAC[CARD_IMAGE_INJ; INT_OF_NUM_EQ; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[CARD_NUMSEG_LT]]);;

let ISOMORPHIC_FINITE_CYCLIC_INTEGER_MOD_GROUP = prove
 (`!G:A group.
        cyclic_group G /\ FINITE(group_carrier G)
        ==> G isomorphic_group integer_mod_group (CARD(group_carrier G))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o
   GEN_REWRITE_RULE I [ISOMORPHIC_GROUP_CYCLIC_INTEGER]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ISOMORPHIC_GROUP_ORDER)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_FINITENESS) THEN
  ASM_SIMP_TAC[FINITE_INTEGER_MOD_GROUP; ORDER_INTEGER_MOD_GROUP]);;

let ISOMORPHIC_GROUP_INTEGER_MOD_GROUP = prove
 (`(!(G:A group) n.
        G isomorphic_group integer_mod_group n <=>
        cyclic_group G /\
        (n = 0 /\ INFINITE(group_carrier G) \/
         ~(n = 0) /\ (group_carrier G) HAS_SIZE n)) /\
   (!(G:A group) n.
        integer_mod_group n isomorphic_group G <=>
        cyclic_group G /\
        (n = 0 /\ INFINITE(group_carrier G) \/
         ~(n = 0) /\ (group_carrier G) HAS_SIZE n))`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[] THEN
  GEN_TAC THEN REWRITE_TAC[ISOMORPHIC_GROUP_CYCLIC_INTEGER] THEN
  MATCH_MP_TAC(MESON[]
   `(!m n. R m /\ R n ==> P m ==> P n) /\
    (!n. P n ==> R n)
    ==> !n. P n <=> (?m. P m) /\ R n`) THEN
  REWRITE_TAC[HAS_SIZE; INFINITE] THEN
  CONJ_TAC THENL [MESON_TAC[]; REPEAT STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_FINITENESS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ISOMORPHIC_GROUP_HAS_ORDER)) THEN
  REWRITE_TAC[FINITE_INTEGER_MOD_GROUP; HAS_SIZE] THEN
  MESON_TAC[ORDER_INTEGER_MOD_GROUP]);;

let ISOMORPHIC_INTEGER_MOD_GROUPS = prove
 (`!m n. integer_mod_group m isomorphic_group integer_mod_group n <=>
         m = n`,
  REWRITE_TAC[ISOMORPHIC_GROUP_INTEGER_MOD_GROUP; HAS_SIZE; INFINITE;
              FINITE_INTEGER_MOD_GROUP; CYCLIC_GROUP_INTEGER_MOD_GROUP] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[ORDER_INTEGER_MOD_GROUP] THEN ASM_ARITH_TAC);;

let ISOMORPHIC_FINITE_CYCLIC_GROUPS = prove
 (`!(G:A group) (H:B group).
        cyclic_group G /\ cyclic_group H /\
        FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
        CARD(group_carrier G) = CARD(group_carrier H)
        ==> G isomorphic_group H`,
  REPEAT STRIP_TAC THEN TRANS_TAC ISOMORPHIC_GROUP_TRANS
   `integer_mod_group(CARD(group_carrier G:A->bool))` THEN
  REWRITE_TAC[ISOMORPHIC_GROUP_INTEGER_MOD_GROUP] THEN
  ASM_SIMP_TAC[INFINITE; HAS_SIZE; CARD_EQ_0; GROUP_CARRIER_NONEMPTY]);;

let CYCLIC_IMP_COUNTABLE_GROUP = prove
 (`!G:A group. cyclic_group G ==> COUNTABLE(group_carrier G)`,
  REWRITE_TAC[CYCLIC_GROUP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE] THEN
  SIMP_TAC[COUNTABLE_IMAGE; INT_COUNTABLE]);;

let SUBGROUP_GENERATED_ELEMENT_ORDER = prove
 (`!G a:A.
        FINITE(group_carrier G) /\ a IN group_carrier G
        ==> (subgroup_generated G {a} = G <=>
             group_element_order G a = CARD(group_carrier G))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (group_carrier (subgroup_generated G {a:A}))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
    ALL_TAC] THEN
  EQ_TAC THENL [ASM_MESON_TAC[CARD_CYCLIC_SUBGROUP_ORDER]; DISCH_TAC] THEN
  REWRITE_TAC[SUBGROUP_GENERATED_EQ] THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN
  ASM_SIMP_TAC[CARD_CYCLIC_SUBGROUP_ORDER]);;

let CYCLIC_GROUP_ELEMENT_ORDER = prove
 (`!G:A group.
        FINITE(group_carrier G)
        ==> (cyclic_group G <=>
             ?a. a IN group_carrier G /\
                 group_element_order G a = CARD(group_carrier G))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cyclic_group] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:A` THEN ASM_CASES_TAC `(a:A) IN group_carrier G` THEN
  ASM_SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER]);;

let [CYCLIC_PROD_INTEGER_MOD_GROUP;
     ISOMORPHIC_PROD_INTEGER_MOD_GROUP;
     GROUP_ISOMORPHISM_PROD_INTEGER_MOD_GROUP] = (CONJUNCTS o prove)
 (`(!m n. cyclic_group (prod_group (integer_mod_group m) (integer_mod_group n))
          <=> coprime(m,n)) /\
   (!m n.
        prod_group (integer_mod_group m) (integer_mod_group n) isomorphic_group
        integer_mod_group (m * n) <=>
        coprime(m,n)) /\
   (!m n.
        group_isomorphism
         (integer_mod_group (m * n),
          prod_group (integer_mod_group m) (integer_mod_group n))
         (\a. (a rem &m),(a rem &n)) <=>
        coprime(m,n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(r ==> q) /\ (q ==> p) /\ (p ==> c) /\ (c ==> r)
    ==> (p <=> c) /\ (q <=> c) /\ (r <=> c)`) THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[GROUP_ISOMORPHISM_IMP_ISOMORPHIC];
    DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_CYCLICITY) THEN
    REWRITE_TAC[CYCLIC_GROUP_INTEGER_MOD_GROUP];
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[CYCLIC_GROUP] THEN
    REWRITE_TAC[MESON[] `~(?x. P x /\ Q x) <=> !x. P x ==> ~Q x`] THEN
    SIMP_TAC[FORALL_PAIR_THM; PROD_GROUP; IN_CROSS;
             GROUP_ZPOW_INTEGER_MOD_GROUP; GROUP_ZPOW_PROD_GROUP] THEN
    REWRITE_TAC[GROUP_CARRIER_INTEGER_MOD_GROUP] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN
    MATCH_MP_TAC(SET_RULE `!z. z IN s /\ ~(z IN t) ==> ~(s = t)`) THEN
    REWRITE_TAC[EXISTS_PAIR_THM; EXISTS_IN_IMAGE; RIGHT_EXISTS_AND_THM;
                IN_CROSS; GSYM CONJ_ASSOC; IN_UNIV; IN_ELIM_THM] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[PAIR_EQ; INT_REM_EQ] THEN
    POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[num_coprime; NOT_EXISTS_THM] THEN MESON_TAC[INTEGER_RULE
     `(x * a == &1) (mod m) /\ (x * b == &1) (mod n) /\
      (y * a == &0) (mod m) /\ (y * b == &1) (mod n)
      ==> coprime(m,n)`];
    REWRITE_TAC[GROUP_ISOMORPHISM_SUBSET] THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_PROD_INTEGER_MOD_GROUP] THEN
    REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_SIMP_TAC[INT_REM_0; MULT_CLAUSES; INT_REM_1;
                   NUMBER_RULE `coprime(0,n) <=> n = 1`] THEN
      SIMP_TAC[INTEGER_MOD_GROUP; ARITH; IN_UNIV; IN_ELIM_THM] THEN
      REWRITE_TAC[UNWIND_THM2] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_SIMP_TAC[INT_REM_0; MULT_CLAUSES; INT_REM_1;
                   NUMBER_RULE `coprime(n,0) <=> n = 1`] THEN
      SIMP_TAC[INTEGER_MOD_GROUP; ARITH; IN_UNIV; IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; MULT_EQ_0] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_coprime]) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:int`; `b:int`] o MATCH_MP (INTEGER_RULE
         `coprime(m:int,n)
          ==> !a b. ?c. (c == a) (mod m) /\ (c == b) (mod n)`)) THEN
      ASM_SIMP_TAC[GSYM INT_REM_EQ; INT_REM_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c rem &(m * n)` THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      ASM_SIMP_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT; MULT_EQ_0; LE_1] THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_REM_REM_MUL];
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_coprime]) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:int`; `b:int`] o MATCH_MP (INTEGER_RULE
         `coprime(m:int,n)
          ==> !a b. (a == b) (mod m) /\ (a == b) (mod n)
        ==> (a == b) (mod (m * n))`)) THEN
      ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN MATCH_MP_TAC INT_REM_LT THEN
      ASM_REWRITE_TAC[INT_OF_NUM_MUL]]]);;

let CYCLIC_PROD_GROUP = prove
 (`!(G:A group) (H:B group).
        cyclic_group (prod_group G H) <=>
        cyclic_group G /\ cyclic_group H /\
        (trivial_group G \/
         trivial_group H \/
         FINITE(group_carrier G) /\ FINITE(group_carrier H) /\
         coprime(CARD(group_carrier G),CARD(group_carrier H)))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `cyclic_group(G:A group)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CYCLIC_GROUP_EPIMORPHIC_IMAGE) THEN
    EXISTS_TAC `FST:A#B->A` THEN REWRITE_TAC[GROUP_EPIMORPHISM_FST]] THEN
  ASM_CASES_TAC `cyclic_group(H:B group)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CYCLIC_GROUP_EPIMORPHIC_IMAGE) THEN
    EXISTS_TAC `SND:A#B->B` THEN REWRITE_TAC[GROUP_EPIMORPHISM_SND]] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ISOMORPHIC_GROUP_CYCLIC_INTEGER] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_CYCLICITY o
    MATCH_MP ISOMORPHIC_GROUP_PROD_GROUPS) THEN
  FIRST_ASSUM(CONJUNCTS_THEN
   (SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY)) THEN
  FIRST_ASSUM(CONJUNCTS_THEN
   (MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_GROUP_ORDER))) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN
   (SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_FINITENESS)) THEN
  SIMP_TAC[FINITE_INTEGER_MOD_GROUP; CYCLIC_PROD_INTEGER_MOD_GROUP;
           TRIVIAL_INTEGER_MOD_GROUP; ORDER_INTEGER_MOD_GROUP] THEN
  ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[NUMBER_RULE `coprime(1,n)`] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[NUMBER_RULE `coprime(n,1)`] THEN
  ASM_CASES_TAC `m = 0` THEN
  ASM_SIMP_TAC[NUMBER_RULE `coprime(0,n) <=> n = 1`] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[NUMBER_RULE `coprime(n,0) <=> n = 1`]);;

let CYCLIC_PRIME_ORDER_GROUP = prove
 (`!G (a:A).
        FINITE (group_carrier G) /\
        (CARD(group_carrier G) = 1 \/ prime(CARD(group_carrier G))) /\
        a IN group_carrier G /\ ~(a = group_id G)
        ==> subgroup_generated G {a} = G`,
  REWRITE_TAC[ONE_OR_PRIME] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUBGROUP_GENERATED_ELEMENT_ORDER] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_element_order G (a:A)`) THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER] THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_1]);;

let GENERATOR_INTEGER_MOD_GROUP = prove
 (`!n a. subgroup_generated (integer_mod_group n) {a} = integer_mod_group n <=>
         (n <= 1 \/ &0 <= a /\ a < &n) /\ coprime(&n,a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  ASM_CASES_TAC `a IN group_carrier(integer_mod_group n)` THENL
   [ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
    REWRITE_TAC[GROUP_CARRIER_INTEGER_MOD_GROUP] THEN
    REWRITE_TAC[GROUP_ZPOW_INTEGER_MOD_GROUP] THEN
    MATCH_MP_TAC(TAUT `q /\ (p <=> r) ==> (p <=> q /\ r)`) THEN
    CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN ASM_CASES_TAC `n = 0` THEN
      ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; IN_ELIM_THM; ARITH];
      REWRITE_TAC[INT_REM_EQ; SET_RULE
       `{(x * a) rem &n | x IN (:int)} = IMAGE (\x. x rem &n) (:int) <=>
        !x. ?y. (y * a) rem &n = x rem &n`] THEN
      EQ_TAC THENL [DISCH_THEN(MP_TAC o SPEC `&1:int`); ALL_TAC] THEN
      CONV_TAC INTEGER_RULE];
    SUBGOAL_THEN `trivial_group (subgroup_generated (integer_mod_group n) {a})`
    MP_TAC THENL
     [REWRITE_TAC[TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ] THEN ASM SET_TAC[];
      REWRITE_TAC[trivial_group] THEN DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SUBGROUP_GENERATED] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM trivial_group; TRIVIAL_INTEGER_MOD_GROUP] THEN
    POP_ASSUM MP_TAC THEN
    ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[LE_REFL] THENL
     [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_SIMP_TAC[INTEGER_MOD_GROUP; LE_1; IN_UNIV; IN_ELIM_THM] THEN
    ASM_ARITH_TAC]);;

let CYCLIC_GROUP_PRIME_ORDER_EQ = prove
 (`!(G:A group).
        (!a. a IN group_carrier G /\ ~(a = group_id G)
             ==> subgroup_generated G {a} = G) <=>
        FINITE(group_carrier G) /\
        (CARD (group_carrier G) = 1 \/ prime (CARD (group_carrier G)))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CYCLIC_PRIME_ORDER_GROUP] THEN
  DISCH_TAC THEN ASM_CASES_TAC `trivial_group(G:A group)` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[trivial_group]) THEN
    ASM_REWRITE_TAC[FINITE_SING; CARD_SING];
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [TRIVIAL_GROUP_SUBSET])] THEN
  REWRITE_TAC[SUBSET; IN_SING; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> r) ==> p /\ (q \/ r)`) THEN
  SUBGOAL_THEN `G = subgroup_generated G {z:A}` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
   SUBST1_TAC th THEN ASM_SIMP_TAC[CARD_CYCLIC_SUBGROUP_ORDER] THEN
   REWRITE_TAC[TAUT `p /\ (p ==> q) <=> p /\ q`] THEN
   SUBST1_TAC th THEN ASM_SIMP_TAC[FINITE_CYCLIC_SUBGROUP_ORDER]) THEN
  ABBREV_TAC `d = group_element_order G (z:A)` THEN
  MATCH_MP_TAC(TAUT `(p ==> ~q) /\ q ==> ~p /\ q`) THEN CONJ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[prime; ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH_EQ] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPEC `d:num` ONE_OR_PRIME_DIVIDES_OR_COPRIME) THEN
  EXPAND_TAC "d" THEN ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_1] THEN
  DISCH_THEN SUBST1_TAC THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `(d:num) divides n` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_pow G (z:A) n`) THEN
  ASM_SIMP_TAC[GROUP_POW_EQ_ID; GROUP_POW] THEN
  DISCH_THEN(MP_TAC o AP_TERM `group_carrier:A group->A->bool`) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; GROUP_POW] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:int` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [SYM(MATCH_MP GROUP_POW_1 th)]) THEN
  REWRITE_TAC[GSYM GROUP_NPOW; num_coprime] THEN
  ASM_SIMP_TAC[GSYM GROUP_ZPOW_MUL; GROUP_ZPOW_EQ_ALT] THEN
  CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Sylow's theorems and p-groups.                                            *)
(* ------------------------------------------------------------------------- *)

let SYLOW_THEOREM_COUNT_MOD = prove
 (`!(G:A group) p k.
        FINITE(group_carrier G) /\
        prime p /\
        p EXP k divides CARD(group_carrier G)
        ==> (CARD {h | h subgroup_of G /\ CARD h = p EXP k} == 1) (mod p)`,
  let lemma = prove
   (`!(s:A->bool) (t:B->bool) k.
          FINITE s /\ FINITE t /\ CARD s = CARD t
          ==> CARD {s' | s' SUBSET s /\ CARD s' = k} =
              CARD {t' | t' SUBSET t /\ CARD t' = k}`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
     (X_CHOOSE_THEN `f:A->B` MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
    REWRITE_TAC[INJECTIVE_ON_ALT] THEN STRIP_TAC THEN
    SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_IMAGE; SET_RULE
     `{t' | (?u. u SUBSET s /\ t' = f u) /\ P t'} =
      IMAGE f {u | u SUBSET s /\ P(f u)}`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o rand o snd) THEN
    ASM_SIMP_TAC[FINITE_RESTRICTED_SUBSETS] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(MESON[] `(p ==> y = x) ==> (p /\ x = k <=> p /\ y = k)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[FINITE_SUBSET]])
  and SYLOW_LEMMA = prove
   (`!(G:A group) p k n.
          FINITE(group_carrier G) /\
          prime p /\
          p EXP k * n = CARD(group_carrier G)
          ==> (CARD {t | t SUBSET group_carrier G /\ CARD t = p EXP k} ==
               CARD {h | h subgroup_of G /\ CARD h = p EXP k} * n)
              (mod (p * n))`,
    REPEAT STRIP_TAC THEN MAP_EVERY ABBREV_TAC
     [`m = {t:A->bool | t SUBSET group_carrier G /\ t HAS_SIZE p EXP k}`;
      `a = \x:A. IMAGE (group_mul G x)`] THEN
    SUBGOAL_THEN `FINITE(m:(A->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN MATCH_MP_TAC FINITE_RESTRICTED_SUBSETS THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `group_action (G:A group) (m:(A->bool)->bool) a`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "a"] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] GROUP_ACTION_IMAGE_SIZED) THEN
      REWRITE_TAC[GROUP_ACTION_GROUP_TRANSLATION; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!t. t IN m
          ==> CARD(group_stabilizer G (a:A->(A->bool)->(A->bool)) t)
              divides p EXP k`
    ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
      X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `t:A->bool` o MATCH_MP
        (REWRITE_RULE[IMP_CONJ] SUBGROUP_OF_GROUP_STABILIZER)) THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`subgroup_generated G
            (group_stabilizer G (a:A->(A->bool)->(A->bool)) t)`;
        `t:A->bool`;
        `group_mul(G:A group)`]
        GROUP_ORBIT_COMMON_DIVISOR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC GROUP_ACTION_ON_SUBSET THEN
        EXISTS_TAC `group_carrier G:A->bool` THEN
        ASM_SIMP_TAC[GROUP_ACTION_FROM_SUBGROUP;
                     CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                     GROUP_ACTION_GROUP_TRANSLATION] THEN
        EXPAND_TAC "a" THEN
        REWRITE_TAC[group_stabilizer; IN_ELIM_THM] THEN SET_TAC[];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL
         [`subgroup_generated G
            (group_stabilizer G (a:A->(A->bool)->(A->bool)) t)`;
          `group_carrier G:A->bool`; `t:A->bool`; `group_mul(G:A group)`]
          GROUP_ORBIT_ON_SUBSET) THEN
        ASM_SIMP_TAC[GROUP_ORBIT_SUBGROUP_TRANSLATION] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN
         `t INTER right_coset G (group_stabilizer G a t) x =
          right_coset G (group_stabilizer G (a:A->(A->bool)->(A->bool)) t) x`
        SUBST1_TAC THENL
         [REWRITE_TAC[SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
          REWRITE_TAC[right_coset; group_setmul; SUBSET; FORALL_IN_GSPEC] THEN
          REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING] THEN
          EXPAND_TAC "a" THEN REWRITE_TAC[group_stabilizer] THEN
          REWRITE_TAC[IN_ELIM_THM; FORALL_UNWIND_THM2] THEN ASM SET_TAC[];
          MATCH_MP_TAC(NUMBER_RULE `m:num = n ==> n divides m`) THEN
          MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
          ASM_SIMP_TAC[FINITE_GROUP_STABILIZER] THEN
          MATCH_MP_TAC CARD_EQ_RIGHT_COSET_SUBGROUP THEN ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!t r. t SUBSET group_carrier G /\ CARD t = r <=>
             t SUBSET group_carrier G /\ t HAS_SIZE r) /\
      (!h r. (h:A->bool) subgroup_of G /\ CARD h = r <=>
             h subgroup_of G /\ h HAS_SIZE r)`
     (fun th -> REWRITE_TAC[th]) THENL
      [ASM_MESON_TAC[subgroup_of; HAS_SIZE; FINITE_SUBSET]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      NSUM_CARD_GROUP_ORBITS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!g. (nsum s g == nsum s f) (mod n) /\ nsum s g = z
          ==> (nsum s f == z) (mod n)`) THEN
    EXISTS_TAC  `\s:(A->bool)->bool. if CARD s = n then CARD s else 0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONG_NSUM THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[NUMBER_RULE `(a:num == a) (mod n)`] THEN
      MP_TAC(ISPECL
       [`G:A group`; `m:(A->bool)->bool`;
        `a:A->(A->bool)->(A->bool)`; `t:A->bool`] ORBIT_STABILIZER_MUL) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[DIVIDES_PRIMEPOW] THEN REWRITE_TAC[SYM(ASSUME
       `p EXP k * n = CARD(group_carrier G:A->bool)`)] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; LE_LT; IMP_CONJ] THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      DISCH_THEN SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
        DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
        REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC; EXP];
        ALL_TAC] THEN
      REWRITE_TAC[NUM_RING `a * p = p * b <=> p = 0 \/ a = b`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN CONV_TAC NUMBER_RULE;
      SIMP_TAC[] THEN REWRITE_TAC[GSYM NSUM_RESTRICT_SET; SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[NSUM_CONST; ETA_AX; FINITE_IMAGE; FINITE_RESTRICT]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `{x | x IN IMAGE (group_orbit G m (a:A->(A->bool)->(A->bool))) m /\
           CARD x = n} =
      IMAGE (\h. {left_coset G x h | x | x IN group_carrier G})
            {h | h subgroup_of G /\ h HAS_SIZE p EXP k}`
    SUBST1_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_SIMP_TAC[FINITE_RESTRICTED_SUBGROUPS] THEN
      MAP_EVERY X_GEN_TAC [`h1:A->bool`; `h2:A->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o ISPEC `group_id G:A` o MATCH_MP (SET_RULE
       `{f x | x IN u} = {g x | x IN u}
        ==> !a. a IN u ==> ?b. b IN u /\ g b = f a`)) THEN
      ASM_SIMP_TAC[GROUP_ID; LEFT_COSET_ID; SUBGROUP_OF_IMP_SUBSET] THEN
      ASM_MESON_TAC[SUBGROUP_OF_LEFT_COSET]] THEN
    MATCH_MP_TAC(SET_RULE
     `!Q. s'' SUBSET {x | x IN s /\ Q x} /\
          (!x. x IN s ==> f x = f' x) /\
          (!x. x IN s ==> ?x'. x' IN s /\ Q x' /\ f x' = f x) /\
          (!x. x IN s /\ Q x ==> (P(f x) <=> x IN s''))
          ==> {y | y IN IMAGE f s /\ P y} = IMAGE f' s''`) THEN
    EXISTS_TAC `\t:A->bool. group_id G IN t` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[subgroup_of] THEN SET_TAC[];
      ASM_SIMP_TAC[GROUP_ORBIT] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[o_THM; LEFT_COSET_AS_IMAGE];
      ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
      ASM_SIMP_TAC[GROUP_ORBIT_EQ] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_ORBIT_SYM_EQ) THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      SIMP_TAC[group_orbit; NOT_IMP; CONJ_ASSOC; RIGHT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      REWRITE_TAC[UNWIND_THM1] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(q ==> ~p)`] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [group_action]) THEN
      SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[IN_IMAGE] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(q ==> ~p)`] THEN EXPAND_TAC "m" THEN
      SIMP_TAC[IN_ELIM_THM; SUBSET; GROUP_RULE
       `group_id G = group_mul G g h <=> g = group_inv G h`] THEN
      REWRITE_TAC[NOT_IMP] THEN X_GEN_TAC `t:A->bool` THEN
      ASM_CASES_TAC `t:A->bool = {}` THENL
       [ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES] THEN
        ASM_MESON_TAC[EXP_EQ_0; PRIME_0];
        ASM_MESON_TAC[GROUP_INV; MEMBER_NOT_EMPTY]];
      X_GEN_TAC `t:A->bool` THEN DISCH_THEN(fun th ->
        STRIP_ASSUME_TAC th THEN MP_TAC(CONJUNCT1 th)) THEN
      EXPAND_TAC "m" THEN
      REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[GSYM HAS_SIZE]] THEN
    TRANS_TAC EQ_TRANS
     `CARD(group_stabilizer G (a:A->(A->bool)->(A->bool)) t) = p EXP k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NUM_RING
       `x * y = p * n /\ ~(p * n = 0) ==> (x = n <=> y = p)`) THEN
      ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY] THEN
      ASM_SIMP_TAC[ORBIT_STABILIZER_MUL];
      SUBST1_TAC(SYM(ASSUME `CARD(t:A->bool) = p EXP k`))] THEN
    SUBGOAL_THEN `group_stabilizer G (a:A->(A->bool)->(A->bool)) t SUBSET t`
    ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN
      REWRITE_TAC[group_stabilizer; SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `group_id G:A` THEN
      ASM_SIMP_TAC[GROUP_MUL_RID];
      ASM_SIMP_TAC[SUBSET_CARD_EQ]] THEN
    EQ_TAC THENL [ASM_MESON_TAC[SUBGROUP_OF_GROUP_STABILIZER]; DISCH_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[group_stabilizer] THEN
    MATCH_MP_TAC(SET_RULE
     `t SUBSET u /\ (!x. x IN u ==> (P x <=> x IN t))
      ==> t SUBSET {x | x IN u /\ P x}`) THEN
    ASM_SIMP_TAC[GSYM LEFT_COSET_AS_IMAGE; LEFT_COSET_EQ_SUBGROUP]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (ASSUME_TAC o SYM)) THEN
  MP_TAC(ISPECL
   [`G:A group`; `p:num`; `k:num`; `n:num`] SYLOW_LEMMA) THEN
  MP_TAC(ISPECL
   [`integer_mod_group (p EXP k * n)`; `p:num`; `k:num`; `n:num`]
   SYLOW_LEMMA) THEN
  ASM_SIMP_TAC[ORDER_INTEGER_MOD_GROUP; CARD_EQ_0; GROUP_CARRIER_NONEMPTY;
               FINITE_INTEGER_MOD_GROUP] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `~(n = 0) /\ s = s' /\ t = 1
    ==> (s == t * n) (mod (p * n))
        ==> (s' == t' * n) (mod (p * n))
            ==> (t' == 1) (mod p)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MULT_EQ_0; CARD_EQ_0; GROUP_CARRIER_NONEMPTY];
    MATCH_MP_TAC lemma THEN
    ASM_SIMP_TAC[ORDER_INTEGER_MOD_GROUP; CARD_EQ_0; GROUP_CARRIER_NONEMPTY;
               FINITE_INTEGER_MOD_GROUP];
    ASM_SIMP_TAC[ORDER_INTEGER_MOD_GROUP; FINITE_INTEGER_MOD_GROUP;
                 CYCLIC_GROUP_INTEGER_MOD_GROUP; GROUP_CARRIER_NONEMPTY;
                 CARD_EQ_0; COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS]]);;

let SYLOW_THEOREM = prove
 (`!(G:A group) p k.
        FINITE(group_carrier G) /\
        prime p /\
        p EXP k divides CARD(group_carrier G)
        ==> ?h. h subgroup_of G /\ CARD h = p EXP k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [SET_RULE `(?x. P x) <=> ~({x | P x} = {})`] THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_0; FINITE_RESTRICTED_SUBGROUPS] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`; `k:num`] SYLOW_THEOREM_COUNT_MOD) THEN
  ASM_REWRITE_TAC[NUMBER_RULE `(0 == n) (mod p) <=> p divides n`] THEN
  ASM_MESON_TAC[DIVIDES_ONE; prime]);;

let CAUCHY_GROUP_THEOREM = prove
 (`!(G:A group) p.
        FINITE(group_carrier G) /\ prime p /\ p divides CARD(group_carrier G)
        ==> ?x. x IN group_carrier G /\ group_element_order G x = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`; `1`] SYLOW_THEOREM) THEN
  ASM_REWRITE_TAC[EXP_1; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~trivial_group(subgroup_generated G (h:A->bool))` MP_TAC THENL
   [ASM_SIMP_TAC[TRIVIAL_GROUP_HAS_SIZE_1; HAS_SIZE;
                 FINITE_SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    ASM_MESON_TAC[PRIME_1];
    ASM_SIMP_TAC[TRIVIAL_GROUP_SUBSET; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 CONJUNCT2 SUBGROUP_GENERATED]] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC o MATCH_MP (SET_RULE
   `~(h SUBSET {a}) ==> ?x. x IN h /\ ~(x = a)`)) THEN
  SUBGOAL_THEN `(a:A) IN group_carrier G` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`subgroup_generated G h:A group`; `a:A`]
        GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_OF_IMP_SUBSET; FINITE_SUBSET];
    REWRITE_TAC[GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED]] THEN
  ASM_MESON_TAC[prime; GROUP_ELEMENT_ORDER_EQ_1]);;

let PRIME_DIVIDES_GROUP_ORDER = prove
 (`!(G:A group) p.
    FINITE(group_carrier G) /\ prime p
    ==> ((?x. x IN group_carrier G /\ p divides (group_element_order G x)) <=>
         p divides CARD(group_carrier G))`,
  MESON_TAC[GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER;
            CAUCHY_GROUP_THEOREM; DIVIDES_REFL; DIVIDES_TRANS]);;

let COPRIME_GROUP_ORDER = prove
 (`!(G:A group) n.
    FINITE(group_carrier G)
    ==> ((!x. x IN group_carrier G ==> coprime(group_element_order G x,n)) <=>
         coprime(CARD(group_carrier G),n))`,
  REWRITE_TAC[COPRIME_PRIME_EQ] THEN MESON_TAC[PRIME_DIVIDES_GROUP_ORDER]);;

let PGROUP_GEN = prove
 (`!(G:A group) Q.
        FINITE(group_carrier G)
        ==> ((!x p. x IN group_carrier G /\
                    prime p /\
                    p divides group_element_order G x
                    ==> Q p) <=>
             (!p. prime p /\ p divides CARD(group_carrier G) ==> Q p))`,
 ASM_MESON_TAC[CAUCHY_GROUP_THEOREM; GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER;
                DIVIDES_PRIME_PRIME; DIVIDES_TRANS]);;

let PGROUP = prove
 (`!(G:A group) p.
        FINITE(group_carrier G) /\ prime p
        ==> ((!x. x IN group_carrier G
                  ==> ?k. group_element_order G x = p EXP k) <=>
             ?k. CARD(group_carrier G) = p EXP k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PRIME_POWER_EXISTS] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC PGROUP_GEN THEN ASM_REWRITE_TAC[]);;

let FINITE_GROUP_POW_INJECTIVE_EQ = prove
 (`!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x y. x IN group_carrier G /\ y IN group_carrier G /\
                    group_pow G x n = group_pow G y n
                    ==> x = y) <=>
             coprime(n,CARD(group_carrier G)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[GROUP_POW_CANCEL]] THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[COPRIME_PRIME_EQ; LEFT_IMP_EXISTS_THM; NOT_FORALL_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[NOT_IMP] THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`] CAUCHY_GROUP_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN EXISTS_TAC `group_id G:A` THEN
  ASM_SIMP_TAC[GROUP_POW_ID; GROUP_ID] THEN
  ASM_SIMP_TAC[GROUP_POW_EQ_ID; GSYM GROUP_ELEMENT_ORDER_EQ_1] THEN
  ASM_MESON_TAC[PRIME_1]);;

let FINITE_GROUP_ZPOW_INJECTIVE_EQ = prove
 (`!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x y. x IN group_carrier G /\ y IN group_carrier G /\
                    group_zpow G x n = group_zpow G y n
                    ==> x = y) <=>
             coprime(n,&(CARD(group_carrier G))))`,
  REWRITE_TAC[FORALL_INT_CASES; GROUP_ZPOW_POW; GSYM num_coprime;
              INTEGER_RULE `coprime(--x:int,y) <=> coprime(x,y)`] THEN
  SIMP_TAC[IMP_CONJ; GROUP_INV_EQ; GROUP_POW] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; FINITE_GROUP_POW_INJECTIVE_EQ]);;

let FINITE_GROUP_POW_SURJECTIVE_EQ = prove
 (`!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x. x IN group_carrier G
                  ==> ?y. y IN group_carrier G /\ group_pow G y n = x) <=>
             coprime(n,CARD(group_carrier G)))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SURJECTIVE_IFF_INJECTIVE o
        lhand o snd) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_POW] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FINITE_GROUP_POW_INJECTIVE_EQ THEN
  ASM_REWRITE_TAC[]);;

let FINITE_GROUP_ZPOW_SURJECTIVE_EQ = prove
 (`!(G:A group) n.
        FINITE(group_carrier G)
        ==> ((!x. x IN group_carrier G
                  ==> ?y. y IN group_carrier G /\ group_zpow G y n = x) <=>
             coprime(n,&(CARD(group_carrier G))))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SURJECTIVE_IFF_INJECTIVE o
        lhand o snd) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_ZPOW] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FINITE_GROUP_ZPOW_INJECTIVE_EQ THEN
  ASM_REWRITE_TAC[]);;

let FINITE_GROUP_ZROOT_EXISTS = prove
 (`!G n x:A.
        FINITE(group_carrier G) /\
        coprime(n,&(CARD(group_carrier G))) /\
        x IN group_carrier G
        ==> ?y. y IN group_carrier G /\ group_zpow G y n = x`,
  MESON_TAC[FINITE_GROUP_ZPOW_SURJECTIVE_EQ]);;

let FINITE_GROUP_ROOT_EXISTS = prove
 (`!G n x:A.
        FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G)) /\
        x IN group_carrier G
        ==> ?y. y IN group_carrier G /\ group_pow G y n = x`,
  MESON_TAC[FINITE_GROUP_POW_SURJECTIVE_EQ]);;

let ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ = prove
 (`!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G)
        ==> (group_monomorphism (G,G) (\x. group_pow G x n) <=>
             coprime(n,CARD(group_carrier G)))`,
  SIMP_TAC[group_monomorphism; ABELIAN_GROUP_HOMOMORPHISM_POWERING] THEN
  MESON_TAC[FINITE_GROUP_POW_INJECTIVE_EQ]);;

let ABELIAN_GROUP_MONOMORPHISM_POWERING = prove
 (`!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G))
        ==> group_monomorphism (G,G) (\x. group_pow G x n)`,
  MESON_TAC[ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ]);;

let ABELIAN_GROUP_ISOMORPHISM_POWERING_EQ = prove
 (`!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G)
        ==> (group_isomorphism (G,G) (\x. group_pow G x n) <=>
             coprime(n,CARD(group_carrier G)))`,
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE] THEN
  REWRITE_TAC[ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ]);;

let ABELIAN_GROUP_ISOMORPHISM_POWERING = prove
 (`!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G))
        ==> group_isomorphism (G,G) (\x. group_pow G x n)`,
  MESON_TAC[ABELIAN_GROUP_ISOMORPHISM_POWERING_EQ]);;

let ABELIAN_GROUP_EPIMORPHISM_POWERING_EQ = prove
 (`!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G)
        ==> (group_epimorphism (G,G) (\x. group_pow G x n) <=>
             coprime(n,CARD(group_carrier G)))`,
  ASM_SIMP_TAC[GSYM GROUP_ISOMORPHISM_EQ_EPIMORPHISM_FINITE] THEN
  REWRITE_TAC[ABELIAN_GROUP_ISOMORPHISM_POWERING_EQ]);;

let ABELIAN_GROUP_EPIMORPHISM_POWERING = prove
 (`!(G:A group) n.
        abelian_group G /\ FINITE(group_carrier G) /\
        coprime(n,CARD(group_carrier G))
        ==> group_epimorphism (G,G) (\x. group_pow G x n)`,
  MESON_TAC[ABELIAN_GROUP_EPIMORPHISM_POWERING_EQ]);;

let SYLOW_THEOREM_CONJUGATE_GEN = prove
 (`!(G:A group) p k h j.
        prime p /\
        h subgroup_of G /\
        FINITE {left_coset G x h | x | x IN group_carrier G} /\
        ~(p divides CARD {left_coset G x h | x | x IN group_carrier G}) /\
        j subgroup_of G /\ FINITE j /\ CARD j = p EXP k
        ==> ?a. a IN group_carrier G /\
                j SUBSET IMAGE (group_conjugation G a) h`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a:A->(A->bool)->(A->bool) = IMAGE o group_mul G` THEN
  SUBGOAL_THEN
   `group_action (subgroup_generated G j:A group)
                 {left_coset G x h | x | x IN group_carrier G} a`
  MP_TAC THENL
   [MATCH_MP_TAC GROUP_ACTION_FROM_SUBGROUP THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN
    MATCH_MP_TAC GROUP_ACTION_LEFT_COSET_MULTIPLICATION THEN
    ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p:num`; `k:num`] o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] PGROUP_ACTION_FIXPOINT)) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; HAS_SIZE] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `group_inv G x:A`) THEN
  ASM_SIMP_TAC[IN_SUBGROUP_INV] THEN
  SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM LEFT_COSET_AS_IMAGE; o_THM] THEN
  ASM_SIMP_TAC[LEFT_COSET_LEFT_COSET; SUBGROUP_OF_IMP_SUBSET; GROUP_INV;
               GROUP_MUL; LEFT_COSET_EQ] THEN
  ASM_SIMP_TAC[IN_IMAGE_GROUP_CONJUGATION; SUBGROUP_OF_IMP_SUBSET] THEN
  REWRITE_TAC[group_conjugation] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN GROUP_TAC);;

let SYLOW_THEOREM_CONJUGATE_SUBSET = prove
 (`!(G:A group) p k l h j.
        FINITE(group_carrier G) /\ prime p /\
        ~(p EXP (k + 1) divides CARD(group_carrier G)) /\
        h subgroup_of G /\ CARD h = p EXP k /\
        j subgroup_of G /\ CARD j = p EXP l
        ==> ?a. a IN group_carrier G /\
                j SUBSET IMAGE (group_conjugation G a) h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SYLOW_THEOREM_CONJUGATE_GEN THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `l:num`] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FINITE_SUBSET; subgroup_of]] THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`] LAGRANGE_THEOREM_LEFT) THEN
  ASM_REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`; GSYM SIMPLE_IMAGE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `m * p EXP k = n /\ p divides m ==> p EXP k * p EXP 1 divides n`)) THEN
  ASM_REWRITE_TAC[GSYM EXP_ADD]);;

let SYLOW_THEOREM_CONJUGATE_ALT = prove
 (`!(G:A group) p k h h'.
        FINITE(group_carrier G) /\ prime p /\
        ~(p EXP (k + 1) divides CARD(group_carrier G)) /\
        h subgroup_of G /\ CARD h = p EXP k /\
        h' subgroup_of G /\ CARD h' = p EXP k
        ==> group_conjugate G h h'`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[group_conjugate; SUBGROUP_OF_IMP_SUBSET] THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`; `k:num`; `k:num`; `h:A->bool`;
                 `h':A->bool`] SYLOW_THEOREM_CONJUGATE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
  ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET; CARD_IMAGE_LE; subgroup_of]);;

let SYLOW_THEOREM_CONJUGATE = prove
 (`!(G:A group) p k h h'.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k /\
        h' subgroup_of G /\ CARD h' = p EXP k
        ==> group_conjugate G h h'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SYLOW_THEOREM_CONJUGATE_ALT THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; DE_MORGAN_THM] THEN
  ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY] THEN
  REWRITE_TAC[ARITH_RULE `~(k + 1 <= k)`] THEN ASM_MESON_TAC[PRIME_1]);;

let SYLOW_THEOREM_CONJUGATE_EQ = prove
 (`!(G:A group) p k h h'.
      FINITE(group_carrier G) /\ prime p /\
      index p (CARD(group_carrier G)) = k /\
      h subgroup_of G /\ CARD h = p EXP k
      ==> (h' subgroup_of G /\ CARD h' = p EXP k <=> group_conjugate G h h')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_MESON_TAC[SYLOW_THEOREM_CONJUGATE]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[GROUP_CONJUGATE_SUBGROUP_OF]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP GROUP_CONJUGATE_IMP_CARD_EQ) THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  ASM_MESON_TAC[CARD_EQ_CARD_IMP; FINITE_SUBSET; SUBGROUP_OF_IMP_SUBSET]);;

let SYLOW_THEOREM_PGROUP_SUPERSET = prove
 (`!G p k (h:A->bool).
        FINITE(group_carrier G) /\ prime p /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> ?h'. h' subgroup_of G /\ h SUBSET h' /\
                 CARD h' = p EXP (index p (CARD(group_carrier G)))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL
   [`G:A group`; `p:num`; `index p (CARD(group_carrier G:A->bool))`]
   SYLOW_THEOREM) THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`;
                 `index p (CARD(group_carrier  G:A->bool))`;
                 `k:num`; `s:A->bool`; `h:A->bool`]
        SYLOW_THEOREM_CONJUGATE_SUBSET) THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; ARITH_RULE `~(p + 1 <= p)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (group_conjugation G (a:A)) s` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_OF_HOMOMORPHIC_IMAGE;
                  GROUP_HOMOMORPHISM_CONJUGATION];
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[GROUP_CONJUGATION_EQ; SUBSET; FINITE_SUBSET; subgroup_of]]);;

let SYLOW_THEOREM_NORMAL_UNIQUE = prove
 (`!(G:A group) p k h h'.
      FINITE(group_carrier G) /\ prime p /\
      index p (CARD(group_carrier G)) = k /\
      h normal_subgroup_of G /\ CARD h = p EXP k
      ==> (h' subgroup_of G /\ CARD h' = p EXP k <=> h' = h)`,
  MESON_TAC[SYLOW_THEOREM_CONJUGATE_EQ; normal_subgroup_of;
                NORMAL_SUBGROUP_CONJUGATE_EQ]);;

let SYLOW_THEOREM_COUNT_NORMALIZER = prove
 (`!(G:A group) h p k.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> CARD {h | h subgroup_of G /\ CARD h = p EXP k} =
            CARD(group_carrier G) DIV CARD(group_normalizer G h)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CARD_CONJUGATE_SUBSETS; SUBGROUP_OF_IMP_SUBSET] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC SYLOW_THEOREM_CONJUGATE_EQ THEN
  ASM_REWRITE_TAC[]);;

let SYLOW_THEOREM_COUNT_NORMALIZER_MUL = prove
 (`!(G:A group) h p k.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> CARD {h | h subgroup_of G /\ CARD h = p EXP k} *
            CARD(group_normalizer G h) =
            CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`] CARD_CONJUGATE_SUBSETS_MUL) THEN
  ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC SYLOW_THEOREM_CONJUGATE_EQ THEN
  ASM_REWRITE_TAC[]);;

let SYLOW_THEOREM_NORMAL_UNIQUE_EQ = prove
 (`!G p k h:A->bool.
        FINITE (group_carrier G) /\
        prime p /\
        index p (CARD (group_carrier G)) = k /\
        h subgroup_of G /\
        CARD h = p EXP k
        ==> ((!h'. h' subgroup_of G /\ CARD h' = p EXP k <=> h' = h) <=>
             h normal_subgroup_of G)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SYLOW_THEOREM_NORMAL_UNIQUE]] THEN
  REWRITE_TAC[SET_RULE `(!x. P x <=> x = a) <=> {x | P x} = {a}`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`; `p:num`; `k:num`]
        SYLOW_THEOREM_COUNT_NORMALIZER_MUL) THEN
  ASM_REWRITE_TAC[CARD_SING; MULT_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER] THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[GROUP_NORMALIZER_SUBSET_CARRIER]);;

let SYLOW_THEOREM_UNIQUE = prove
 (`!(G:A group) p k.
        FINITE(group_carrier G) /\
        prime p /\
        index p (CARD(group_carrier G)) = k
        ==> ((?!h. h subgroup_of G /\ CARD h = p EXP k) <=>
             (?h. h normal_subgroup_of G /\ CARD h = p EXP k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `h:A->bool` THEN
  ASM_CASES_TAC `CARD(h:A->bool) = p EXP k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(h:A->bool) subgroup_of G` THENL
   [ALL_TAC; ASM_MESON_TAC[normal_subgroup_of]] THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`; `k:num`; `h:A->bool`]
        SYLOW_THEOREM_NORMAL_UNIQUE_EQ) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SYLOW_THEOREM_COUNT_DIVISOR = prove
 (`!(G:A group) p k.
        FINITE(group_carrier G) /\ prime p /\
        index p (CARD(group_carrier G)) = k
        ==> CARD {h | h subgroup_of G /\ CARD h = p EXP k}
            divides (CARD(group_carrier G)) DIV (p EXP k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`; `k:num`] SYLOW_THEOREM) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; PRIMEPOW_DIVIDES_INDEX;
               DIVIDES_DIVIDES_DIV; LE_REFL] THEN
  X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `s:A->bool`; `p:num`; `k:num`]
        SYLOW_THEOREM_COUNT_NORMALIZER_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC(NUMBER_RULE `(p:num) divides n ==> p * m divides m * n`) THEN
  MP_TAC(ISPECL [`subgroup_generated G (group_normalizer G s):A group`;
                 `s:A->bool`] LAGRANGE_THEOREM) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; SUBGROUP_GROUP_NORMALIZER;
               SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FINITE_GROUP_NORMALIZER] THEN
  ASM_SIMP_TAC[GROUP_NORMALIZER_SUBSET]);;

let PGROUP_NONTRIVIAL_CENTRE_GEN = prove
 (`!G (n:A->bool) p k.
        prime p /\ (group_carrier G) HAS_SIZE (p EXP k) /\
        n normal_subgroup_of G /\ ~(n = {group_id G})
        ==> {group_id G} PSUBSET
            (group_centralizer G (group_carrier G) INTER n)`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`G:A group`; `n DELETE (group_id G:A)`;
    `group_conjugation (G:A group)`; `p:num`; `k:num`]
        PGROUP_ACTION_FIXPOINT) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE; IMP_CONJ] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
   [NORMAL_SUBGROUP_CONJUGATION]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [MATCH_MP_TAC GROUP_ACTION_ON_SUBSET THEN
    EXISTS_TAC `group_carrier G:A->bool` THEN
    REWRITE_TAC[GROUP_ACTION_CONJUGATION] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_DELETE]] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `x:A`] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[GROUP_CONJUGATION_EQ_ID] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q ==> r) ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; DISCH_TAC] THEN ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
    ASM_SIMP_TAC[DIVIDES_SUB_1] THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] LAGRANGE_THEOREM)) THEN
    ASM_SIMP_TAC[DIVIDES_PRIMEPOW; LEFT_IMP_EXISTS_THM] THEN
    ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN MATCH_MP_TAC num_INDUCTION THEN
    SIMP_TAC[EXP; NUMBER_RULE `(p * q == 1) (mod p) <=> p = 1`] THEN
    ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `(n:A->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; CONV_TAC(LAND_CONV HAS_SIZE_CONV)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `z IN s /\ (!x. P x ==> x IN s DELETE z)
      ==> (?x. P x) ==> {z} PSUBSET s`) THEN
    REWRITE_TAC[IN_DELETE; IN_INTER] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[subgroup_of; SUBGROUP_GROUP_CENTRALIZER]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[group_centralizer; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[GROUP_CONJUGATION_EQ_SELF]]);;

let PGROUP_NONTRIVIAL_CENTRE = prove
 (`!(G:A group) p k.
        prime p /\ ~(k = 0) /\ (group_carrier G) HAS_SIZE (p EXP k)
        ==> {group_id G} PSUBSET (group_centralizer G (group_carrier G))`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`G:A group`; `group_carrier G:A->bool`; `p:num`; `k:num`]
   PGROUP_NONTRIVIAL_CENTRE_GEN) THEN
  ASM_REWRITE_TAC[CARRIER_NORMAL_SUBGROUP_OF; HAS_SIZE] THEN
  ASM_REWRITE_TAC[GSYM trivial_group; TRIVIAL_GROUP_HAS_SIZE_1; HAS_SIZE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[EXP_EQ_1; PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[group_centralizer] THEN SET_TAC[]);;

let PGROUP_DIVIDES_NORMALIZER_QUOTIENT = prove
 (`!G p k h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\
        h subgroup_of G /\ CARD h = p EXP k /\
        p divides CARD(group_carrier G) DIV CARD h
        ==> p divides CARD(group_normalizer G h) DIV CARD h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(h:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[subgroup_of; FINITE_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `a:A->(A->bool)->(A->bool) = IMAGE o group_mul G` THEN
  SUBGOAL_THEN
   `group_action (subgroup_generated G h:A group)
                 {left_coset G x h | x | x IN group_carrier G} a`
  MP_TAC THENL
   [MATCH_MP_TAC GROUP_ACTION_FROM_SUBGROUP THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN
    MATCH_MP_TAC GROUP_ACTION_LEFT_COSET_MULTIPLICATION THEN
    ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p:num`; `k:num`] o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] PGROUP_ACTION_FIXPOINTS)) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; HAS_SIZE] THEN
  ASM_SIMP_TAC[LAGRANGE_THEOREM_LEFT_DIV] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE]; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `p divides y /\ x:num = z ==> (x == y) (mod p) ==> p divides z`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `CARD { left_coset (subgroup_generated G (group_normalizer G h)) x h |x|
           (x:A) IN group_carrier
                     (subgroup_generated G (group_normalizer G h))}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LEFT_COSET_SUBGROUP_GENERATED] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; SUBGROUP_OF_IMP_SUBSET;
                SUBGROUP_GROUP_NORMALIZER; GROUP_NORMALIZER_CONJUGATION] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. P x /\ R(f x) <=> Q x)
      ==> {y | y IN {f x | P x} /\ R y} = {f x | Q x}`) THEN
    X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN group_carrier G` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[o_THM; GSYM LEFT_COSET_AS_IMAGE] THEN
    MATCH_MP_TAC(MESON[IN_SUBGROUP_INV; subgroup_of; SUBSET; GROUP_INV_INV]
     `h subgroup_of G /\ ((!x. x IN h ==> P(group_inv G x)) <=> Q)
      ==> ((!x. x IN h ==> P x) <=> Q)`) THEN
    SUBGOAL_THEN `!x:A. x IN h ==> x IN group_carrier G` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; subgroup_of]; ALL_TAC] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [LEFT_COSET_LEFT_COSET; LEFT_COSET_EQ; GROUP_MUL; GROUP_INV; GROUP_INV_INV;
      SUBGROUP_OF_IMP_SUBSET; GROUP_INV_MUL; GSYM GROUP_MUL_ASSOC] THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand)
      IMAGE_GROUP_CONJUGATION_BY_INV o rand o snd) THEN
    ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) /\
      (IMAGE g s SUBSET s ==> IMAGE g s = s)
      ==> ((!x. x IN s ==> f x IN s) <=> IMAGE g s = s)`) THEN CONJ_TAC
    THENL [ASM_SIMP_TAC[group_conjugation; GROUP_INV_INV]; DISCH_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN
    REPEAT(CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_MESON_TAC[GROUP_CONJUGATION_EQ; GROUP_INV];
    W(MP_TAC o PART_MATCH (lhand o rand) LAGRANGE_THEOREM_LEFT_DIV o
      lhand o snd) THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP; GROUP_NORMALIZER_SUBSET;
                 SUBGROUP_GROUP_NORMALIZER; FINITE_GROUP_NORMALIZER;
                 SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ]]);;

let PGROUP_SUBGROUP_PSUBSET_NORMALIZER = prove
 (`!G p k h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\ CARD(group_carrier G) = p EXP k /\
        h subgroup_of G /\ ~(h = group_carrier G)
        ==> h PSUBSET group_normalizer G h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `h:A->bool`] LAGRANGE_THEOREM) THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CARD_SUBSET_EQ; subgroup_of]] THEN
  ASM_SIMP_TAC[PSUBSET; GROUP_NORMALIZER_SUBSET] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`G:A group`; `p:num`; `i:num`; `h:A->bool`]
        PGROUP_DIVIDES_NORMALIZER_QUOTIENT) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(p = 1)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0; PRIME_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_REFL; EXP_EQ_0; DIVIDES_ONE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  ASM_SIMP_TAC[EXP_ADD; DIV_MULT; EXP_EQ_0; EXP] THEN
  CONV_TAC NUMBER_RULE);;

let PGROUP_MAXIMAL_NORMAL_SUBGROUP_OF = prove
 (`!G p k h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\ CARD(group_carrier G) = p EXP k /\
        h subgroup_of G /\
        (!h'. h' subgroup_of G /\ h PSUBSET h' ==> h' = group_carrier G)
        ==> h normal_subgroup_of G`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h:A->bool = group_carrier G` THEN
  ASM_REWRITE_TAC[CARRIER_NORMAL_SUBGROUP_OF] THEN
  ASM_REWRITE_TAC[NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBGROUP_GROUP_NORMALIZER] THEN
  MATCH_MP_TAC PGROUP_SUBGROUP_PSUBSET_NORMALIZER THEN ASM_MESON_TAC[]);;

let PGROUP_FRATTINI = prove
 (`!(G:A group) p k h j.
        prime p /\
        FINITE j /\ j normal_subgroup_of G /\
        h SUBSET j /\ h subgroup_of G /\
        index p (CARD j) = k /\ CARD h = p EXP k
        ==> group_setmul G (group_normalizer G h) j = group_carrier G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[GROUP_SETMUL; GROUP_NORMALIZER_SUBSET_CARRIER;
               NORMAL_SUBGROUP_OF_IMP_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN
  GEN_REWRITE_TAC I [GSYM FORALL_IN_GROUP_CARRIER_INV] THEN
  X_GEN_TAC `g:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`subgroup_generated G (j:A->bool)`; `p:num`; `k:num`;
    `h:A->bool`; `IMAGE (group_conjugation G (g:A)) h`]
        SYLOW_THEOREM_CONJUGATE) THEN
  ASM_SIMP_TAC[group_conjugate; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               NORMAL_SUBGROUP_IMP_SUBGROUP;
               SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ;
               GROUP_CONJUGATION_SUBGROUP_GENERATED] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBGROUP_OF_HOMOMORPHIC_IMAGE;
                    GROUP_HOMOMORPHISM_CONJUGATION];
      ASM_MESON_TAC[NORMAL_SUBGROUP_CONJUGATION; IMAGE_SUBSET; SUBSET_TRANS];
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
      ASM_MESON_TAC[GROUP_CONJUGATION_EQ; SUBSET; subgroup_of; FINITE_SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; normal_subgroup_of; subgroup_of]; ALL_TAC] THEN
    REWRITE_TAC[group_setmul; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`group_mul G (group_inv G g) x:A`; `group_inv G x:A`] THEN
    ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL_RINV; GROUP_MUL_RID;
                 GROUP_INV; GROUP_MUL] THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[normal_subgroup_of; IN_SUBGROUP_INV]] THEN
    ASM_SIMP_TAC[GROUP_NORMALIZER_CONJUGATION; SUBGROUP_OF_IMP_SUBSET] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; GROUP_INV; GROUP_MUL;
                IMAGE_GROUP_CONJUGATION_BY_MUL;
                SUBGROUP_OF_IMP_SUBSET] THEN
    ASM_SIMP_TAC[IMAGE_GROUP_CONJUGATION_BY_INV; GROUP_INV;
                 SUBGROUP_OF_IMP_SUBSET; IMAGE_GROUP_CONJUGATION_SUBSET]]);;

let PGROUP_SELF_NORMALIZER = prove
 (`!G p k s h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\
        index p (CARD(group_carrier G)) = k /\
        s subgroup_of G /\ CARD s = p EXP k /\
        h subgroup_of G /\ group_normalizer G s SUBSET h
        ==> group_normalizer G h = h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[GROUP_NORMALIZER_SUBSET] THEN
  MP_TAC(ISPECL [`subgroup_generated G (group_normalizer G (h:A->bool))`;
                 `p:num`; `k:num`; `s:A->bool`;
                 `h:A->bool`]
        PGROUP_FRATTINI) THEN
  ASM_REWRITE_TAC[NORMAL_SUBGROUP_OF_NORMALIZER] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; subgroup_of];
      ASM_MESON_TAC[GROUP_NORMALIZER_SUBSET; SUBSET_TRANS];
      ASM_SIMP_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ;
                   SUBGROUP_GROUP_NORMALIZER] THEN
      ASM_MESON_TAC[GROUP_NORMALIZER_SUBSET; SUBSET_TRANS];
      REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`G:A group`; `h:A->bool`] LAGRANGE_THEOREM) THEN
        ASM_REWRITE_TAC[DIVIDES_INDEX] THEN
        ASM_SIMP_TAC[CARD_EQ_0; GROUP_CARRIER_NONEMPTY] THEN ASM_MESON_TAC[];
        MP_TAC(ISPECL [`subgroup_generated G h:A group`; `s:A->bool`]
          LAGRANGE_THEOREM) THEN
        ASM_SIMP_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ;
                     CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[FINITE_SUBSET; subgroup_of; GROUP_NORMALIZER_SUBSET;
                        SUBSET_TRANS];
          SIMP_TAC[LE_INDEX] THEN
          ASM_MESON_TAC[PRIME_1; CARD_EQ_0; FINITE_SUBSET; subgroup_of;
                        SUBGROUP_OF_IMP_NONEMPTY]]]];
    REWRITE_TAC[GROUP_SETMUL_SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 SUBGROUP_GROUP_NORMALIZER] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV [SYM(MATCH_MP GROUP_SETMUL_SUBGROUP th)]) THEN
    MATCH_MP_TAC GROUP_SETMUL_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    TRANS_TAC SUBSET_TRANS `group_normalizer G s:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_NORMALIZER_SUBGROUP_GENERATED o
      lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBGROUP_GROUP_NORMALIZER] THEN
    ASM_MESON_TAC[GROUP_NORMALIZER_SUBSET; SUBSET_TRANS]]);;

let PGROUP_NORMALIZER_NORMALIZER = prove
 (`!G p k h:A->bool.
        FINITE(group_carrier G) /\
        prime p /\
        index p (CARD(group_carrier G)) = k /\
        h subgroup_of G /\ CARD h = p EXP k
        ==> group_normalizer G (group_normalizer G h) = group_normalizer G h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PGROUP_SELF_NORMALIZER THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `k:num`; `h:A->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL; SUBGROUP_GROUP_NORMALIZER]);;

(* ------------------------------------------------------------------------- *)
(* Theorems related to "internal" direct sums.                               *)
(* ------------------------------------------------------------------------- *)

let GROUP_DISJOINT_SUM_ALT = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (g INTER h SUBSET {group_id G} <=> g INTER h = {group_id G})`,
  REWRITE_TAC[subgroup_of] THEN SET_TAC[]);;

let GROUP_DISJOINT_SUM_ID = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (g INTER h SUBSET {group_id G} <=>
             !x y. x IN g /\ y IN h /\ group_mul G x y = group_id G
                   ==> x = group_id G /\ y = group_id G)`,
  REWRITE_TAC[SUBSET; IN_INTER; IN_SING; subgroup_of] THEN
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `!x y:A. x IN g /\ y IN h /\ group_mul G x (group_inv G y) = group_id G
            ==> x = group_id G /\ group_inv G y = group_id G` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM group_div; GROUP_DIV_EQ_ID;
                 GROUP_INV_EQ_ID; IMP_CONJ] THEN
    MESON_TAC[];
    ASM_MESON_TAC[GROUP_INV_INV]]);;

let GROUP_DISJOINT_SUM_CANCEL = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (g INTER h SUBSET {group_id G} <=>
             !x x' y y'. x IN g /\ x' IN g /\ y IN h /\ y' IN h /\
                         group_mul G x y = group_mul G x' y'
                         ==> x = x' /\ y = y')`,
  SIMP_TAC[GROUP_DISJOINT_SUM_ID] THEN
  REWRITE_TAC[SUBSET; subgroup_of] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `x':A`; `y:A`; `y':A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`group_mul G (group_inv G x') x:A`; `group_div G y y':A`]) THEN
    ASM_SIMP_TAC[GROUP_DIV_EQ_ID; GROUP_INV_EQ_ID; GROUP_DIV] THEN
    ASM_SIMP_TAC[GSYM GROUP_LINV_EQ; GROUP_INV; GROUP_INV_INV] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM
    `\z:A. group_mul G (group_inv G x') (group_mul G z (group_inv G y'))`) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_inv G x)
         (group_mul G (group_mul G x y) (group_inv G y)) = group_id G`] THEN
    ASM_SIMP_TAC[group_div] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    W(fun (_,w) -> ASM_SIMP_TAC[GROUP_RULE w]);
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`x:A`; `group_id G:A`; `y:A`; `group_id G:A`]) THEN
    ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_ID]]);;

let GROUP_SUM_COMMUTING_IMP_NORMAL = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G /\
        group_carrier G SUBSET group_setmul G g h /\
        (!x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)
        ==> g normal_subgroup_of G /\ h normal_subgroup_of G`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[normal_subgroup_of] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[group_setmul] THEN SPEC_TAC(`a:A`,`a:A`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; left_coset; right_coset] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(x:A) IN group_carrier G /\ y IN group_carrier G /\
                g SUBSET group_carrier G /\ h SUBSET group_carrier G`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[subgroup_of; SUBSET]; ALL_TAC]) THEN
  REWRITE_TAC[GSYM GROUP_SETMUL_SING] THENL
   [ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; GROUP_SETMUL; SING_SUBSET] THEN
    TRANS_TAC EQ_TRANS `group_setmul G (group_setmul G {x:A} g) {y}` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; GROUP_SETMUL; SING_SUBSET] THEN
      AP_TERM_TAC THEN REWRITE_TAC[group_setmul] THEN ASM SET_TAC[];
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[GROUP_SETMUL_LSUBSET; GROUP_SETMUL_RSUBSET;
                   SING_SUBSET; NOT_INSERT_EMPTY]];

    ASM_SIMP_TAC[GROUP_SETMUL_ASSOC; GROUP_SETMUL; SING_SUBSET] THEN
    TRANS_TAC EQ_TRANS `group_setmul G (group_setmul G {x:A} h) {y}` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM GROUP_SETMUL_ASSOC; GROUP_SETMUL; SING_SUBSET] THEN
      ASM_SIMP_TAC[GROUP_SETMUL_LSUBSET; GROUP_SETMUL_RSUBSET;
                   SING_SUBSET; NOT_INSERT_EMPTY];
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[group_setmul] THEN ASM SET_TAC[]]]);;

let GROUP_SUM_NORMAL_IMP_COMMUTING = prove
 (`!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G /\
        g INTER h SUBSET {group_id G}
        ==> !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    GROUP_DISJOINT_SUM_CANCEL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN group_carrier G /\ y IN group_carrier G`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[normal_subgroup_of; subgroup_of; SUBSET]; ALL_TAC] THEN
  MP_TAC(CONJ (ASSUME `(g:A->bool) normal_subgroup_of G`)
              (ASSUME `(h:A->bool) normal_subgroup_of G`)) THEN
  REWRITE_TAC[normal_subgroup_of; IMP_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPEC `x:A`) (MP_TAC o SPEC `y:A`)) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `u = v /\ s = t
    ==> (!x. x IN t ==> x IN s) /\ (!x. x IN u ==> x IN v)`)) THEN
  REWRITE_TAC[right_coset; left_coset; group_setmul; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':A` (STRIP_ASSUME_TAC o GSYM)) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':A` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_MESON_TAC[]);;

let GROUP_SUM_NORMAL_EQ_COMMUTING = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G /\
        group_carrier G SUBSET group_setmul G g h /\
        g INTER h SUBSET {group_id G}
        ==> (g normal_subgroup_of G /\ h normal_subgroup_of G <=>
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC GROUP_SUM_NORMAL_IMP_COMMUTING THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC GROUP_SUM_COMMUTING_IMP_NORMAL THEN
    ASM_REWRITE_TAC[]]);;

let GROUP_HOMOMORPHISM_GROUP_MUL_GEN = prove
 (`!G g h:A->bool.
        group_homomorphism
            (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
            (\(x,y). group_mul G x y) <=>
        !x y. x IN group_carrier G /\ x IN g /\
              y IN group_carrier G /\ y IN h
              ==> group_mul G x y = group_mul G y x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:A,y:A)` o
      MATCH_MP GROUP_HOMOMORPHISM_INV) THEN
    ASM_SIMP_TAC[PROD_GROUP; IN_CROSS; CONJUNCT2 SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[SUBGROUP_GENERATED_INC_GEN] THEN GROUP_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ] THEN
  DISCH_TAC THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET; GROUP_MUL];
    REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED]] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(x1:A) IN group_carrier G /\
    (x2:A) IN group_carrier G /\
    (y1:A) IN group_carrier G /\
    (y2:A) IN group_carrier G`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
    ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL]] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[GROUP_MUL_ASSOC; GROUP_MUL] THEN
  ASM_MESON_TAC[]);;

let GROUP_HOMOMORPHISM_GROUP_MUL_EQ = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_homomorphism
              (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
              (\(x,y). group_mul G x y) <=>
              !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM_GROUP_MUL_GEN] THEN
  ASM_MESON_TAC[subgroup_of; SUBSET]);;

let GROUP_HOMOMORPHISM_GROUP_MUL = prove
 (`!G g h:A->bool.
        abelian_group G
        ==> group_homomorphism
              (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
              (\(x,y). group_mul G x y)`,
  SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_MUL_GEN] THEN
  REWRITE_TAC[abelian_group; subgroup_of; SUBSET] THEN SET_TAC[]);;

let GROUP_EPIMORPHISM_GROUP_MUL_EQ = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_epimorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             group_setmul G g h = group_carrier G /\
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`,
  SIMP_TAC[group_epimorphism; GROUP_HOMOMORPHISM_GROUP_MUL_EQ] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [CONJ_SYM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; group_setmul] THEN
  ASM_SIMP_TAC[PROD_GROUP; CARRIER_SUBGROUP_GENERATED_SUBGROUP; IN_CROSS] THEN
  SET_TAC[]);;

let GROUP_MONOMORPHISM_GROUP_MUL_EQ = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_monomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h = {group_id G} /\
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`,
  SIMP_TAC[group_monomorphism; GROUP_HOMOMORPHISM_GROUP_MUL_EQ] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [CONJ_SYM] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[GROUP_DISJOINT_SUM_CANCEL; GSYM GROUP_DISJOINT_SUM_ALT] THEN
  ASM_SIMP_TAC[PROD_GROUP; CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN MESON_TAC[]);;

let GROUP_ISOMORPHISM_GROUP_MUL_ALT = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h = {group_id G} /\
             group_setmul G g h = group_carrier G /\
             !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  ASM_SIMP_TAC[GROUP_EPIMORPHISM_GROUP_MUL_EQ;
                GROUP_MONOMORPHISM_GROUP_MUL_EQ] THEN
  CONV_TAC TAUT);;

let GROUP_ISOMORPHISM_GROUP_MUL_EQ = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g normal_subgroup_of G /\ h normal_subgroup_of G /\
             g INTER h = {group_id G} /\
             group_setmul G g h = group_carrier G)`,
  SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL_ALT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT
   `(i /\ s ==> (n /\ n' <=> c))
    ==> (i /\ s /\ c <=> n /\ n' /\ i /\ s)`) THEN
  STRIP_TAC THEN MATCH_MP_TAC GROUP_SUM_NORMAL_EQ_COMMUTING THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

let GROUP_ISOMORPHISM_GROUP_MUL_GEN = prove
 (`!G g h:A->bool.
        g normal_subgroup_of G /\ h normal_subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h SUBSET {group_id G} /\
             group_setmul G g h = group_carrier G)`,
  SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL_EQ; NORMAL_SUBGROUP_IMP_SUBGROUP;
           GROUP_DISJOINT_SUM_ALT]);;

let GROUP_ISOMORPHISM_GROUP_MUL = prove
 (`!G g h:A->bool.
        abelian_group G /\ g subgroup_of G /\ h subgroup_of G
        ==> (group_isomorphism
               (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
               (\(x,y). group_mul G x y) <=>
             g INTER h SUBSET {group_id G} /\
             group_setmul G g h = group_carrier G)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ISOMORPHISM_GROUP_MUL_GEN THEN
  ASM_MESON_TAC[ABELIAN_GROUP_NORMAL_SUBGROUP]);;

let GROUP_INTER_IM_KER = prove
 (`!(f:A->B) (g:B->C) G H K.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_monomorphism(G,K) (g o f)
        ==> (group_image(G,H) f) INTER (group_kernel(H,K) g) =
            {group_id H}`,
  SIMP_TAC[GSYM GROUP_DISJOINT_SUM_ALT; SUBGROUP_GROUP_IMAGE;
           SUBGROUP_GROUP_KERNEL] THEN
  REWRITE_TAC[GROUP_MONOMORPHISM; group_image; group_kernel; o_THM] THEN
  REWRITE_TAC[group_homomorphism] THEN SET_TAC[]);;

let GROUP_SUM_IM_KER = prove
 (`!(f:A->B) (g:B->C) G H K.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_epimorphism(G,K) (g o f)
        ==> group_setmul H (group_image(G,H) f) (group_kernel(H,K) g) =
            group_carrier H`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[GROUP_SETMUL; SUBGROUP_OF_IMP_SUBSET;
                SUBGROUP_GROUP_IMAGE; SUBGROUP_GROUP_KERNEL] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  REWRITE_TAC[group_setmul; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [group_epimorphism]) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:B->C) y` o MATCH_MP (SET_RULE
   `P /\ IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; o_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[group_image; group_kernel; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `group_mul H (group_inv H ((f:A->B) x)) y` THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GROUP_MUL_ASSOC; GROUP_MUL_RINV;
               GROUP_MUL_LID; GROUP_MUL_LINV]);;

let GROUP_SUM_KER_IM = prove
 (`!(f:A->B) (g:B->C) G H K.
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_epimorphism(G,K) (g o f)
        ==> group_setmul H (group_kernel(H,K) g) (group_image(G,H) f) =
            group_carrier H`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[GROUP_SETMUL; SUBGROUP_OF_IMP_SUBSET;
                SUBGROUP_GROUP_IMAGE; SUBGROUP_GROUP_KERNEL] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  REWRITE_TAC[group_setmul; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [group_epimorphism]) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:B->C) y` o MATCH_MP (SET_RULE
   `P /\ IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; o_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[group_image; group_kernel; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `group_mul H y (group_inv H ((f:A->B) x))` THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_INV; GSYM GROUP_MUL_ASSOC; GROUP_MUL_RINV;
               GROUP_MUL_RID; GROUP_MUL_LINV]);;

let GROUP_SEMIDIRECT_SUM_IM_KER = prove
 (`!(f:A->B) (g:B->C) G H K.
      group_homomorphism(G,H) f /\
      group_homomorphism(H,K) g /\
      group_isomorphism(G,K) (g o f)
      ==> (group_image(G,H) f) INTER (group_kernel(H,K) g) = {group_id H} /\
          group_setmul H (group_image(G,H) f) (group_kernel(H,K) g) =
          group_carrier H`,
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; GROUP_INTER_IM_KER] THEN
  SIMP_TAC[GROUP_SUM_IM_KER]);;

let GROUP_SEMIDIRECT_SUM_KER_IM = prove
 (`!(f:A->B) (g:B->C) G H K.
      group_homomorphism(G,H) f /\
      group_homomorphism(H,K) g /\
      group_isomorphism(G,K) (g o f)
      ==> (group_kernel(H,K) g) INTER (group_image(G,H) f) = {group_id H} /\
           group_setmul H (group_kernel(H,K) g) (group_image(G,H) f) =
           group_carrier H`,
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; GROUP_INTER_IM_KER] THEN
  SIMP_TAC[GROUP_SUM_KER_IM]);;

let GROUP_ISOMORPHISM_GROUP_MUL_IM_KER = prove
 (`!(f:A->B) (g:B->C) G H K.
        abelian_group H /\
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_isomorphism(G,K) (g o f)
        ==> group_isomorphism
              (prod_group (subgroup_generated H (group_image(G,H) f))
                          (subgroup_generated H (group_kernel(H,K) g)),H)
              (\(x,y). group_mul H x y)`,
  SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL;
           SUBGROUP_GROUP_IMAGE; SUBGROUP_GROUP_KERNEL] THEN
  SIMP_TAC[GROUP_SEMIDIRECT_SUM_IM_KER; SUBSET_REFL]);;

let GROUP_ISOMORPHISM_GROUP_MUL_KER_IM = prove
 (`!(f:A->B) (g:B->C) G H K.
        abelian_group H /\
        group_homomorphism(G,H) f /\
        group_homomorphism(H,K) g /\
        group_isomorphism(G,K) (g o f)
        ==> group_isomorphism
              (prod_group (subgroup_generated H (group_kernel(H,K) g))
                          (subgroup_generated H (group_image(G,H) f)),H)
              (\(x,y). group_mul H x y)`,
  SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL;
           SUBGROUP_GROUP_IMAGE; SUBGROUP_GROUP_KERNEL] THEN
  SIMP_TAC[GROUP_SEMIDIRECT_SUM_KER_IM; SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Internal versus external direct sums over an arbitrary indexing set.      *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_GROUP_SUM_GEN = prove
 (`!k l G (h:K->A->bool).
      k SUBSET l
      ==> (group_homomorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                                 y IN group_carrier G /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k)`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    REWRITE_TAC[pairwise] THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
    STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G /\ y IN group_carrier G`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
      ALL_TAC] THEN
    MAP_EVERY ASM_CASES_TAC [`x:A = group_id G`; `y:A = group_id G`] THEN
    ASM_SIMP_TAC[GROUP_MUL_LID; GROUP_MUL_RID] THEN
    FIRST_ASSUM(MP_TAC o
     SPEC `RESTRICTION l
            (\l. if l = i then x else if l = j then y else group_id G):K->A` o
     MATCH_MP GROUP_HOMOMORPHISM_INV) THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; CONJUNCT2 SUBGROUP_GENERATED] THEN
    REWRITE_TAC[IN_ELIM_THM; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    SIMP_TAC[RESTRICTION_THM] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `l:K` THEN DISCH_TAC THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[GROUP_ID_SUBGROUP]);
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:K,j:K}` THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `{i:K,j:K}` o MATCH_MP (MESON[]
     `group_sum G k f = group_inv G(group_sum G k g)
      ==> !k'. group_sum G k' f = group_sum G k f /\
               group_sum G k' g = group_sum G k g
               ==> group_sum G k' f = group_inv G (group_sum G k' g)`)) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC[GSYM GROUP_SUM_SUPPORT] THEN
      CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[GROUP_INV_EQ_ID; GROUP_ID];
      ALL_TAC] THEN
    REWRITE_TAC[group_sum] THEN
    ABBREV_TAC `(<<=) = @l. woset l /\ fld l = (:K)` THEN
    SUBGOAL_THEN `woset(<<=) /\ fld(<<=) = (:K)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "<<=" THEN CONV_TAC SELECT_CONV THEN REWRITE_TAC[WO];
      ALL_TAC] THEN
    SUBGOAL_THEN `(i:K) <<= j \/ j <<= i` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[];
      ALL_TAC;
      ONCE_REWRITE_TAC[SET_RULE `{i,j} = {j,i}`]] THEN
    (W(MP_TAC o PART_MATCH (lhand o rand)
        (CONJUNCT2(SPEC_ALL GROUP_PRODUCT_CLAUSES)) o
      lhand o lhand o snd) THEN
     W(MP_TAC o PART_MATCH (lhand o rand)
        (CONJUNCT2(SPEC_ALL GROUP_PRODUCT_CLAUSES)) o
      rand o rand o lhand o rand o snd) THEN
     REPLICATE_TAC 2 (ANTS_TAC THENL
      [SIMP_TAC[FINITE_RESTRICT; FINITE_SING] THEN
       ASM_REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
       ASM_REWRITE_TAC[IN_UNIV] THEN ASM_MESON_TAC[];
       DISCH_THEN SUBST1_TAC])) THEN
    ASM_SIMP_TAC[GROUP_INV; IN_SING; GROUP_PRODUCT_SING] THEN GROUP_TAC;
    DISCH_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM; SUM_GROUP_CLAUSES] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GROUP_SUM] THEN
    MAP_EVERY X_GEN_TAC [`f:K->A`; `g:K->A`] THEN
    REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) GROUP_SUM_MUL o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (MESON[FINITE_SUBSET]
           `FINITE {i | i IN l /\ P i}
            ==> {i | i IN k /\ P i} SUBSET {i | i IN l /\ P i}
                ==> FINITE {i | i IN k /\ P i}`)) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
          (REWRITE_RULE[IMP_CONJ] PAIRWISE_IMP)) THEN
        ASM SET_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC GROUP_SUM_EQ THEN
      ASM_SIMP_TAC[RESTRICTION]]]);;

let GROUP_HOMOMORPHISM_GROUP_SUM_EQ = prove
 (`!k l G (h:K->A->bool).
      k SUBSET l /\
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_homomorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k)`,
  REWRITE_TAC[subgroup_of] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_SUM_GEN; pairwise] THEN
  ASM SET_TAC[]);;

let GROUP_HOMOMORPHISM_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k
        ==> group_homomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_SUM_GEN; SUBSET_REFL] THEN
  REWRITE_TAC[pairwise] THEN MESON_TAC[]);;

let GROUP_HOMOMORPHISM_ABELIAN_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        abelian_group G
        ==> group_homomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`,
  REWRITE_TAC[abelian_group] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_SUM_GEN; SUBSET_REFL; pairwise] THEN
  ASM_SIMP_TAC[]);;

let SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN = prove
 (`!k l G (h:K->A->bool).
        k SUBSET l
        ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),
                                subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k) <=>
             pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                                   y IN group_carrier G /\ y IN (h j)
                                   ==> group_mul G x y = group_mul G y x) k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ_GEN] THEN
  SIMP_TAC[GSYM GROUP_HOMOMORPHISM_GROUP_SUM_GEN] THEN
  REWRITE_TAC[TAUT `(p /\ q <=> p) <=> p ==> q`] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:K->A` THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC IN_SUBGROUP_SUM THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
    X_GEN_TAC `i:K` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a IN s ==> a IN t`) THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_MONO THEN ASM SET_TAC[];
    W(MP_TAC o PART_MATCH (lhand o rand)
      SUBGROUP_GENERATED_MINIMAL_EQ o snd) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[CARRIER_SUBGROUP_OF; SUBGROUP_OF_HOMOMORPHIC_IMAGE];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `(!i. i IN f ==> !x. x IN i /\ x IN u ==> x IN t)
      ==> u INTER UNIONS f SUBSET t`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `RESTRICTION l (\l. if l = i then x else group_id G):K->A` THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; RESTRICTION_IN_CARTESIAN_PRODUCT;
                IN_ELIM_THM; CONJUNCT2 SUBGROUP_GENERATED] THEN
    ONCE_REWRITE_TAC[GSYM GROUP_SUM_SUPPORT] THEN
    REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[RESTRICTION_THM] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[MESON[] `(if p then q else T) <=> p ==> q`] THEN
    ASM_SIMP_TAC[SUBGROUP_GENERATED_INC_GEN; GROUP_ID_SUBGROUP; COND_ID] THEN
    REWRITE_TAC[SET_RULE
     `{j | ~(P j ==> j = i ==> Q)} = {j | j = i /\ P i /\ ~Q}`] THEN
    ASM_CASES_TAC `x:A = group_id G` THEN
    ASM_REWRITE_TAC[GROUP_SUM_CLAUSES_EXISTS; EMPTY_GSPEC; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[SING_GSPEC; GROUP_SUM_SING; FINITE_SING]]);;

let SUBGROUP_EPIMORPHISM_GROUP_SUM_EQ = prove
 (`!k l G (h:K->A->bool).
      k SUBSET l /\
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),
                              subgroup_generated G (UNIONS {h i | i IN k}))
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k)`,
  REWRITE_TAC[subgroup_of] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN; pairwise] THEN
  ASM SET_TAC[]);;

let SUBGROUP_EPIMORPHISM_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN; SUBSET_REFL] THEN
  REWRITE_TAC[pairwise] THEN MESON_TAC[]);;

let SUBGROUP_EPIMORPHISM_ABELIAN_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        abelian_group G
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`,
  REWRITE_TAC[abelian_group] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN; SUBSET_REFL; pairwise] THEN
  ASM_SIMP_TAC[]);;

let GROUP_EPIMORPHISM_GROUP_SUM_GEN = prove
 (`!k l G (h:K->A->bool).
        k SUBSET l
        ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                               (group_sum G k) <=>
             pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                                   y IN group_carrier G /\ y IN (h j)
                                   ==> group_mul G x y = group_mul G y x) k /\
             subgroup_generated G (UNIONS {h i | i IN k}) = G)`,
  REWRITE_TAC[group_epimorphism] THEN
  SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_SUM_GEN] THEN
  SIMP_TAC[GSYM SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN] THEN
  REWRITE_TAC[group_epimorphism; SUBGROUP_GENERATED_EQ] THEN
  MESON_TAC[]);;

let GROUP_EPIMORPHISM_GROUP_SUM_EQ = prove
 (`!k l G (h:K->A->bool).
        k SUBSET l /\
        (!i. i IN k ==> (h i) subgroup_of G)
        ==> (group_epimorphism (sum_group l (\i. subgroup_generated G (h i)),G)
                               (group_sum G k) <=>
             pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                   ==> group_mul G x y = group_mul G y x) k /\
             subgroup_generated G (UNIONS {h i | i IN k}) = G)`,
  REWRITE_TAC[subgroup_of] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_EPIMORPHISM_GROUP_SUM_GEN; pairwise] THEN
  ASM SET_TAC[]);;

let GROUP_EPIMORPHISM_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GROUP_EPIMORPHISM_GROUP_SUM_GEN; SUBSET_REFL] THEN
  REWRITE_TAC[pairwise] THEN MESON_TAC[]);;

let GROUP_EPIMORPHISM_ABELIAN_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        abelian_group G /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G
        ==> group_epimorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`,
  REWRITE_TAC[abelian_group] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[GROUP_EPIMORPHISM_GROUP_SUM_GEN; SUBSET_REFL; pairwise] THEN
  ASM_SIMP_TAC[]);;

let GROUP_MONOMORPHISM_GROUP_SUM_GEN = prove
 (`!k G (h:K->A->bool).
      group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                         (group_sum G k) <=>
      pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                            y IN group_carrier G /\ y IN (h j)
                            ==> group_mul G x y = group_mul G y x) k /\
      !i. i IN k
          ==> group_carrier
                 (subgroup_generated G (h i)) INTER
              group_carrier
                 (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
              {group_id G}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GROUP_MONOMORPHISM_ALT] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_SUM_GEN; SUBSET_REFL] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  REWRITE_TAC[GSYM GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ] THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    SIMP_TAC[GSYM GROUP_DISJOINT_SUM_ALT; SUBGROUP_SUBGROUP_GENERATED] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN group_carrier G` ASSUME_TAC THENL
     [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k DELETE (i:K)`; `k:K->bool`; `G:A group`;
                   `h:K->A->bool`] SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN) THEN
    ASM_REWRITE_TAC[group_epimorphism; DELETE_SUBSET] THEN
    ASM_REWRITE_TAC[GSYM GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         PAIRWISE_MONO)) THEN SET_TAC[];
      DISCH_THEN(MP_TAC o SPEC `x:A` o MATCH_MP (SET_RULE
       `P /\ IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`))] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `z:K->A` THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; CONJUNCT2 SUBGROUP_GENERATED] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `RESTRICTION k (\j. if j = i then group_inv G x else (z:K->A) j)`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[SUM_GROUP_CLAUSES; IN_ELIM_THM] THEN
        REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[GROUP_INV; SUBGROUP_GENERATED]; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (MESON[FINITE_INSERT; FINITE_SUBSET]
          `FINITE t ==> !x. s SUBSET x INSERT t ==> FINITE s`)) THEN
        EXISTS_TAC `i:K` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        SIMP_TAC[IMP_CONJ; RESTRICTION; CONJUNCT2 SUBGROUP_GENERATED] THEN
        SET_TAC[];
        MP_TAC(ISPECL [`G:A group`; `i:K`; `k DELETE (i:K)`;
                       `\j. if j = i then group_inv G x else (z:K->A) j`]
          GROUP_SUM_CLAUSES_COMMUTING) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
             (MESON[FINITE_INSERT; FINITE_SUBSET]
                `FINITE t ==> !x. s SUBSET x INSERT t ==> FINITE s`)) THEN
            EXISTS_TAC `i:K` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
            SIMP_TAC[IMP_CONJ; RESTRICTION; CONJUNCT2 SUBGROUP_GENERATED] THEN
            SET_TAC[];
            X_GEN_TAC `j:K` THEN REWRITE_TAC[IN_DELETE] THEN
            DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
            ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
            MATCH_MP_TAC GROUP_COMMUTES_INV THEN
            FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
            ASM_MESON_TAC[]];
          ASM_SIMP_TAC[RESTRICTION_THM; SET_RULE
           `i IN k ==> i INSERT (k DELETE i) = k`] THEN
          DISCH_THEN SUBST1_TAC] THEN
        ASM_SIMP_TAC[GROUP_INV; IN_DELETE] THEN
        MATCH_MP_TAC(MESON[GROUP_MUL_LINV]
         `x IN group_carrier G /\ x = y
          ==> group_mul G (group_inv G x) y = group_id G`) THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC GROUP_SUM_EQ THEN SIMP_TAC[IN_DELETE]];
      GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `i:K`) THEN
      ASM_REWRITE_TAC[RESTRICTION; SUM_GROUP_CLAUSES] THEN
      REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED] THEN GROUP_TAC];
    X_GEN_TAC `z:K->A` THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; CONJUNCT2 SUBGROUP_GENERATED] THEN
    STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC[RESTRICTION_UNIQUE] THEN
    X_GEN_TAC `i:K` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:A group`; `i:K`; `k DELETE (i:K)`; `z:K->A`]
      GROUP_SUM_CLAUSES_COMMUTING) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          FINITE_SUBSET)) THEN SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
        REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]];
      DISCH_THEN(MP_TAC o SYM)] THEN
    ASM_SIMP_TAC[RESTRICTION_THM; IN_DELETE; SET_RULE
     `i IN k ==> i INSERT (k DELETE i) = k`] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
      DISCH_TAC THEN CONV_TAC SYM_CONV] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o
      GEN_REWRITE_RULE (BINDER_CONV o RAND_CONV) [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_SING] THEN
    DISCH_THEN(SUBST1_TAC o SYM o SPEC `(z:K->A) i`) THEN
    ASM_SIMP_TAC[IN_INTER] THEN FIRST_ASSUM(MP_TAC o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ_ALT] (REWRITE_RULE[CONJ_ASSOC]
        GROUP_RINV_UNIQUE))) THEN
    REWRITE_TAC[GROUP_SUM] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC IN_SUBGROUP_INV THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
    MATCH_MP_TAC IN_SUBGROUP_SUM THEN
    REWRITE_TAC[SUBGROUP_SUBGROUP_GENERATED] THEN
    X_GEN_TAC `j:K` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_MONO THEN ASM SET_TAC[]]);;

let GROUP_MONOMORPHISM_GROUP_SUM_EQ = prove
 (`!k G (h:K->A->bool).
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k /\
           !i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})`,
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM_GEN;
           CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[subgroup_of; pairwise] THEN SET_TAC[]);;

let GROUP_MONOMORPHISM_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`,
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM_EQ]);;

let GROUP_MONOMORPHISM_ABELIAN_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_monomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`,
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM_EQ] THEN
  REWRITE_TAC[abelian_group; subgroup_of; pairwise] THEN SET_TAC[]);;

let SUBGROUP_ISOMORPHISM_GROUP_SUM_GEN = prove
 (`!k G (h:K->A->bool).
        group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                           subgroup_generated G (UNIONS {h i | i IN k}))
                          (group_sum G k) <=>
        pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                              y IN group_carrier G /\ y IN (h j)
                              ==> group_mul G x y = group_mul G y x) k /\
        !i. i IN k
          ==> group_carrier
                 (subgroup_generated G (h i)) INTER
              group_carrier
                 (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
              {group_id G}`,
  REWRITE_TAC[GSYM SUBGROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_GROUP_SUM_GEN] THEN
  SIMP_TAC[SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN; SUBSET_REFL] THEN
  CONV_TAC TAUT);;

let SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ = prove
 (`!k G (h:K->A->bool).
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                              subgroup_generated G (UNIONS {h i | i IN k}))
                             (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k /\
           !i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})`,
  REWRITE_TAC[GSYM SUBGROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM_EQ] THEN
  SIMP_TAC[SUBGROUP_EPIMORPHISM_GROUP_SUM_EQ; SUBSET_REFL] THEN
  CONV_TAC TAUT);;

let SUBGROUP_ISOMORPHISM_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`,
  REWRITE_TAC[GSYM SUBGROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM] THEN
  SIMP_TAC[SUBGROUP_EPIMORPHISM_GROUP_SUM; SUBSET_REFL] THEN
  CONV_TAC TAUT);;

let SUBGROUP_ISOMORPHISM_ABELIAN_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        (!i. i IN k
             ==> h i INTER
                 group_carrier
                   (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                 {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),
                               subgroup_generated G (UNIONS {h i | i IN k}))
                               (group_sum G k)`,
  REWRITE_TAC[abelian_group] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ; SUBSET_REFL; pairwise] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[]);;

let GROUP_ISOMORPHISM_GROUP_SUM_GEN = prove
 (`!k G (h:K->A->bool).
        group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                          (group_sum G k) <=>
        pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                              y IN group_carrier G /\ y IN (h j)
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        !i. i IN k
          ==> group_carrier
                 (subgroup_generated G (h i)) INTER
              group_carrier
                 (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
              {group_id G}`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_GROUP_SUM_GEN] THEN
  SIMP_TAC[GROUP_EPIMORPHISM_GROUP_SUM_GEN; SUBSET_REFL] THEN
  CONV_TAC TAUT);;

let GROUP_ISOMORPHISM_GROUP_SUM_EQ = prove
 (`!k G (h:K->A->bool).
      (!i. i IN k ==> (h i) subgroup_of G)
      ==> (group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                             (group_sum G k) <=>
           pairwise (\i j. !x y. x IN (h i) /\ y IN (h j)
                                 ==> group_mul G x y = group_mul G y x) k /\
           subgroup_generated G (UNIONS {h i | i IN k}) = G /\
           !i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM_EQ] THEN
  SIMP_TAC[GROUP_EPIMORPHISM_GROUP_SUM_EQ; SUBSET_REFL] THEN
  CONV_TAC TAUT);;

let GROUP_ISOMORPHISM_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                               (group_sum G k)`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[GROUP_MONOMORPHISM_GROUP_SUM] THEN
  SIMP_TAC[GROUP_EPIMORPHISM_GROUP_SUM; SUBSET_REFL] THEN
  CONV_TAC TAUT);;

let GROUP_ISOMORPHISM_ABELIAN_GROUP_SUM = prove
 (`!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
             ==> h i INTER
                 group_carrier
                   (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                 {group_id G})
        ==> group_isomorphism (sum_group k (\i. subgroup_generated G (h i)),G)
                              (group_sum G k)`,
  REWRITE_TAC[abelian_group] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_GROUP_SUM_EQ; SUBSET_REFL; pairwise] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN ASM SET_TAC[]);;

let ISOMORPHIC_SUM_GROUP_GEN = prove
 (`!k G (h:K->A->bool).
        pairwise (\i j. !x y. x IN group_carrier G /\ x IN (h i) /\
                              y IN group_carrier G /\ y IN (h j)
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
             ==> group_carrier
                    (subgroup_generated G (h i)) INTER
                 group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                 {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`,
  REWRITE_TAC[GSYM GROUP_ISOMORPHISM_GROUP_SUM_GEN; isomorphic_group] THEN
  MESON_TAC[]);;

let ISOMORPHIC_SUM_GROUP = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) subgroup_of G) /\
        pairwise (\i j. !x y. x IN h i /\ y IN h j
                              ==> group_mul G x y = group_mul G y x) k /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `group_sum (G:A group) (k:K->bool)` THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_GROUP_SUM]);;

let ISOMORPHIC_ABELIAN_SUM_GROUP = prove
 (`!k G (h:K->A->bool).
        abelian_group G /\
        (!i. i IN k ==> (h i) subgroup_of G) /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `group_sum (G:A group) (k:K->bool)` THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_ABELIAN_GROUP_SUM]);;

let ISOMORPHIC_NORMAL_SUM_GROUP = prove
 (`!k G (h:K->A->bool).
        (!i. i IN k ==> (h i) normal_subgroup_of G) /\
        subgroup_generated G (UNIONS {h i | i IN k}) = G /\
        (!i. i IN k
               ==> h i INTER
                   group_carrier
                    (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =
                   {group_id G})
        ==> sum_group k (\i. subgroup_generated G (h i)) isomorphic_group G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISOMORPHIC_SUM_GROUP THEN
  ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP] THEN
  REWRITE_TAC[pairwise] THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
  STRIP_TAC THEN MATCH_MP_TAC GROUP_SUM_NORMAL_IMP_COMMUTING THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o
    GEN_REWRITE_RULE (BINDER_CONV o RAND_CONV) [EXTENSION]) THEN
  ASM_REWRITE_TAC[GSYM EXTENSION] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET t' ==> s INTER t SUBSET s INTER t'`) THEN
  TRANS_TAC SUBSET_TRANS
   `group_carrier(subgroup_generated G ((h:K->A->bool) j))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 NORMAL_SUBGROUP_IMP_SUBGROUP; SUBSET_REFL];
    MATCH_MP_TAC SUBGROUP_GENERATED_MONO THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Free Abelian groups on a set, using the "frag" type constructor.          *)
(* ------------------------------------------------------------------------- *)

let free_abelian_group = new_definition
 `free_abelian_group (s:A->bool) =
    group({c | frag_support c SUBSET s},frag_0,frag_neg,frag_add)`;;

let FREE_ABELIAN_GROUP = prove
 (`(!s:A->bool.
        group_carrier(free_abelian_group s) = {c | frag_support c SUBSET s}) /\
   (!s:A->bool. group_id(free_abelian_group s) = frag_0) /\
   (!s:A->bool. group_inv(free_abelian_group s) = frag_neg) /\
   (!s:A->bool. group_mul(free_abelian_group s) = frag_add)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl free_abelian_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM free_abelian_group] THEN ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; FRAG_SUPPORT_NEG; FRAG_SUPPORT_0; EMPTY_SUBSET] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_ADD o lhand o snd) THEN
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE];
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let ABELIAN_FREE_ABELIAN_GROUP = prove
 (`!s:A->bool. abelian_group(free_abelian_group s)`,
  REWRITE_TAC[abelian_group; FREE_ABELIAN_GROUP] THEN
  REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE);;

let FREE_ABELIAN_GROUP_POW = prove
 (`!(s:A->bool) x n.
        group_pow (free_abelian_group s) x n = frag_cmul (&n) x`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[FREE_ABELIAN_GROUP; group_pow; GSYM INT_OF_NUM_SUC] THEN
  CONV_TAC FRAG_MODULE);;

let FREE_ABELIAN_GROUP_ZPOW = prove
 (`!(s:A->bool) x n.
        group_zpow (free_abelian_group s) x n = frag_cmul n x`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_INT_CASES] THEN
  REWRITE_TAC[GROUP_ZPOW_POW; FREE_ABELIAN_GROUP_POW; FREE_ABELIAN_GROUP] THEN
  CONV_TAC FRAG_MODULE);;

let FRAG_OF_IN_FREE_ABELIAN_GROUP = prove
 (`!s x:A. frag_of x IN group_carrier(free_abelian_group s) <=> x IN s`,
  REWRITE_TAC[FREE_ABELIAN_GROUP; FRAG_SUPPORT_OF; SING_SUBSET; IN_ELIM_THM]);;

let FREE_ABELIAN_GROUP_INDUCT = prove
 (`!P s:A->bool.
        P(frag_0) /\
        (!x y. x IN group_carrier(free_abelian_group s) /\
               y IN group_carrier(free_abelian_group s) /\
               P x /\ P y
               ==> P(frag_sub x y)) /\
        (!a. a IN s ==> P(frag_of a))
        ==> !x. x IN group_carrier(free_abelian_group s) ==> P x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  ASM_SIMP_TAC[FRAG_SUPPORT_OF; FRAG_SUPPORT_0; EMPTY_SUBSET; SING_SUBSET] THEN
  ASM_MESON_TAC[FRAG_SUPPORT_SUB; SUBSET_TRANS; UNION_SUBSET]);;

let FREE_ABELIAN_GROUP_UNIVERSAL = prove
 (`!(f:A->B) s G.
        IMAGE f s SUBSET group_carrier G /\ abelian_group G
        ==> ?h. group_homomorphism(free_abelian_group s,G) h /\
                !x. x IN s ==> h(frag_of x) = f x`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. iterate (group_add G) s
                          (\a. group_zpow G ((f:A->B) a) (dest_frag x a))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS
      `iterate (group_add G) {x}
         (\a. group_zpow G ((f:A->B) a) (dest_frag (frag_of x) a))` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET o
        GEN_REWRITE_RULE I [GSYM MONOIDAL_GROUP_ADD]) THEN
      SIMP_TAC[IN_UNIV; IN_SING; SUBSET; DEST_FRAG_OF; NEUTRAL_GROUP_ADD] THEN
      ASM_REWRITE_TAC[GROUP_ZPOW_0];
      ASM_SIMP_TAC[ITERATE_SING; MONOIDAL_GROUP_ADD] THEN
      ASM_SIMP_TAC[DEST_FRAG_OF; GROUP_ZPOW_1]]] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o ISPEC `\x:B. x IN group_carrier G` o
      MATCH_MP ITERATE_CLOSED o
      GEN_REWRITE_RULE I [GSYM MONOIDAL_GROUP_ADD]) THEN
    REWRITE_TAC[GROUP_ID; NEUTRAL_GROUP_ADD; GROUP_ADD] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FREE_ABELIAN_GROUP; SUBSET; IN_ELIM_THM]) THEN
    X_GEN_TAC `a:A` THEN
    ASM_CASES_TAC `dest_frag x (a:A) = &0` THEN
    ASM_REWRITE_TAC[GROUP_ZPOW_0] THEN STRIP_TAC THEN
    MATCH_MP_TAC GROUP_ZPOW THEN
    RULE_ASSUM_TAC(REWRITE_RULE[frag_support]) THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  ASM_SIMP_TAC[GSYM GROUP_ADD_EQ_MUL] THEN
  MAP_EVERY X_GEN_TAC [`x:A frag`; `y:A frag`] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (rand o rand)
    (MATCH_MP ITERATE_OP_GEN (GEN_REWRITE_RULE I [GSYM MONOIDAL_GROUP_ADD] th))
      o rand o snd)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `frag_support x:A->bool`;
      EXISTS_TAC `frag_support y:A->bool`] THEN
    REWRITE_TAC[FINITE_FRAG_SUPPORT] THEN
    REWRITE_TAC[support; frag_support; FREE_ABELIAN_GROUP] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_UNIV; CONTRAPOS_THM; IMP_CONJ] THEN
    REWRITE_TAC[NEUTRAL_GROUP_ADD; GROUP_NPOW; group_pow];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ o
        GEN_REWRITE_RULE I [GSYM MONOIDAL_GROUP_ADD]) THEN
  ASM_SIMP_TAC[GROUP_ADD_EQ_MUL; FREE_ABELIAN_GROUP; DEST_FRAG_ADD;
               GROUP_ZPOW_ADD; GROUP_ZPOW]);;

let ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING = prove
 (`!x:A. integer_group isomorphic_group free_abelian_group {x}`,
  GEN_TAC THEN REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `\n. frag_cmul n (frag_of(x:A))` THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; GROUP_MONOMORPHISM_ALT;
              GROUP_EPIMORPHISM_ALT; group_image] THEN
  REWRITE_TAC[group_homomorphism; INTEGER_GROUP; FREE_ABELIAN_GROUP] THEN
  REWRITE_TAC[IN_UNIV; FRAG_OF_NONZERO;
   FRAG_MODULE `frag_cmul (--n) x = frag_neg(frag_cmul n x)`;
   FRAG_MODULE `frag_cmul(a + b) c = frag_add (frag_cmul a c) (frag_cmul b c)`;
   FRAG_MODULE `frag_cmul c x = frag_0 <=> c = &0 \/ x = frag_0`] THEN
  ONCE_REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
  REWRITE_TAC[TAUT `p /\ p /\ q <=> p /\ q`] THEN CONJ_TAC THENL
   [MESON_TAC[FRAG_SUPPORT_CMUL; FRAG_SUPPORT_OF]; ALL_TAC] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[FRAG_MODULE `frag_cmul (&0) x = frag_0`;
    FRAG_MODULE  `frag_cmul (&1) x = x`;
    FRAG_MODULE `frag_sub (frag_cmul a c) (frag_cmul b c) =
                 frag_cmul (a - b) c`]);;

let GROUP_HOMOMORPHISM_FREE_ABELIAN_GROUPS_ID = prove
 (`!k k':A->bool.
    group_homomorphism (free_abelian_group k,free_abelian_group k') (\x. x) <=>
    k SUBSET k'`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  EQ_TAC THENL [DISCH_TAC; SET_TAC[]] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `frag_of(x:A)`) THEN
  ASM_REWRITE_TAC[FRAG_SUPPORT_OF; SING_SUBSET]);;

let GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM = prove
 (`!k (f:K->A->bool).
        pairwise (\i j. DISJOINT (f i) (f j)) k
        ==> group_isomorphism (sum_group k (\i. free_abelian_group(f i)),
                               free_abelian_group(UNIONS {f i | i IN k}))
                              (iterate frag_add k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM;
              GROUP_EPIMORPHISM_ALT; GROUP_MONOMORPHISM_ALT] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ (p ==> r) ==> (p /\ q) /\ (p /\ r)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUM o lhand o snd) THEN
      ASM SET_TAC[];
      W(MP_TAC o PART_MATCH (rand o rand)
        (MATCH_MP ITERATE_OP_GEN MONOIDAL_FRAG_ADD) o rand o snd) THEN
      ASM_REWRITE_TAC[support; NEUTRAL_FRAG_ADD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
      SIMP_TAC[RESTRICTION]];
    ONCE_REWRITE_TAC[SUBSET]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FREE_ABELIAN_GROUP; SUM_GROUP_CLAUSES; IN_ELIM_THM] THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
    X_GEN_TAC `x:K->A frag` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
    ASM_CASES_TAC `(i:K) IN k` THEN ASM_SIMP_TAC[RESTRICTION] THEN
    REWRITE_TAC[GSYM FRAG_SUPPORT_EQ_EMPTY] THEN
    SUBGOAL_THEN
     `iterate frag_add (i INSERT (k DELETE i)) (x:K->A frag) = frag_0`
    MP_TAC THENL
     [ASM_SIMP_TAC[SET_RULE `x IN s ==> x INSERT (s DELETE x) = s`];
      W(MP_TAC o PART_MATCH (lhand o rand)
       (CONJUNCT2(MATCH_MP ITERATE_CLAUSES_GEN MONOIDAL_FRAG_ADD)) o
       lhand o lhand o snd)] THEN
    REWRITE_TAC[IN_DELETE] THEN ANTS_TAC THENL
     [REWRITE_TAC[support; NEUTRAL_FRAG_ADD] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; FRAG_MODULE
     `frag_add x y = frag_0 <=> y = frag_neg x`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP(MESON[FRAG_SUPPORT_NEG]
     `x = frag_neg y ==> frag_support x = frag_support y`)) THEN
    MATCH_MP_TAC(SET_RULE
     `!u. s SUBSET u /\ DISJOINT t u ==> s = t ==> t = {}`) THEN
    EXISTS_TAC `UNIONS {(f:K->A->bool) j | j IN (k DELETE i)}` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUM o lhand o snd) THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `DISJOINT t u ==> s SUBSET t ==> DISJOINT s u`) THEN
      REWRITE_TAC[SET_RULE
       `DISJOINT a (UNIONS {f i | i IN s}) <=>
        !i. i IN s ==> DISJOINT a (f i)`] THEN
      X_GEN_TAC `j:K` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM_MESON_TAC[]];
    DISCH_THEN(ASSUME_TAC o MATCH_MP SUBGROUP_GROUP_IMAGE) THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
    MATCH_MP_TAC FRAG_INDUCTION THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_SUBGROUP_ID) THEN
      REWRITE_TAC[FREE_ABELIAN_GROUP];
      ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] IN_SUBGROUP_DIV)) THEN
      REWRITE_TAC[FREE_ABELIAN_GROUP; group_div] THEN
      SIMP_TAC[FRAG_MODULE `frag_add x (frag_neg y) = frag_sub x y`]] THEN
    REWRITE_TAC[FORALL_IN_UNIONS] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    REWRITE_TAC[group_image; IN_IMAGE] THEN EXISTS_TAC
     `RESTRICTION k (\j:K. if j = i then frag_of(a:A) else frag_0)` THEN
    REWRITE_TAC[SUM_GROUP_CLAUSES; IN_ELIM_THM; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP] THEN REPEAT CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS
       `iterate frag_add {i}
         (RESTRICTION k (\j:K. if j = i then frag_of(a:A) else frag_0))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[MATCH_MP ITERATE_SING MONOIDAL_FRAG_ADD] THEN
        ASM_REWRITE_TAC[RESTRICTION];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC(REWRITE_RULE
         [IMP_IMP; RIGHT_IMP_FORALL_THM] ITERATE_SUPERSET) THEN
        REWRITE_TAC[MONOIDAL_FRAG_ADD] THEN
        ASM_REWRITE_TAC[SING_SUBSET; IN_SING; NEUTRAL_FRAG_ADD] THEN
        SIMP_TAC[RESTRICTION; IN_ELIM_THM]];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; FRAG_SUPPORT_OF; SING_SUBSET] THEN
      REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:K}` THEN
      REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `j:K` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[RESTRICTION; IN_SING] THEN
      MESON_TAC[]]]);;

let ISOMORPHIC_FREE_ABELIAN_GROUP_UNIONS = prove
 (`!k:(A->bool)->bool.
        pairwise DISJOINT k
        ==> free_abelian_group(UNIONS k) isomorphic_group
            sum_group k free_abelian_group`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  MP_TAC(ISPECL [`k:(A->bool)->bool`; `\x:A->bool. x`]
        GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC) THEN
  REWRITE_TAC[IN_GSPEC]);;

let ISOMORPHIC_SUM_INTEGER_GROUP = prove
 (`!k:A->bool.
        sum_group k (\i. integer_group) isomorphic_group free_abelian_group k`,
  GEN_TAC THEN
  TRANS_TAC ISOMORPHIC_GROUP_TRANS
    `sum_group k (\i:A. free_abelian_group {i})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISOMORPHIC_GROUP_SUM_GROUP THEN
    REWRITE_TAC[ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING];
    MP_TAC(ISPECL [`k:A->bool`; `\x:A. {x}`]
        GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM) THEN
    REWRITE_TAC[pairwise; UNIONS_SINGS] THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MESON_TAC[isomorphic_group]]);;

let CARD_EQ_FREE_ABELIAN_GROUP_INFINITE = prove
 (`!s:A->bool. INFINITE s ==> group_carrier(free_abelian_group s) =_c s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FREE_ABELIAN_GROUP] THEN
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS
      `{f | IMAGE f s SUBSET (:int) /\
       {x | ~(f x = &0)} SUBSET s /\
       FINITE {x:A | ~(f x = &0)}}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_UNIV; le_c] THEN
      EXISTS_TAC `dest_frag:A frag->A->int` THEN SIMP_TAC[GSYM FRAG_EQ] THEN
      REWRITE_TAC[IN_ELIM_THM; FINITE_FRAG_SUPPORT; GSYM frag_support];
      W(MP_TAC o PART_MATCH lhand CARD_LE_RESTRICTED_FUNSPACE o
        lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_TRANS) THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        CARD_EQ_FINITE_SUBSETS o lhand o snd) THEN
      REWRITE_TAC[INFINITE; FINITE_CROSS_EQ] THEN
      ASM_SIMP_TAC[INFINITE_NONEMPTY; UNIV_NOT_EMPTY] THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; GSYM INFINITE] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
      REWRITE_TAC[CROSS; GSYM mul_c] THEN
      W(MP_TAC o PART_MATCH lhand CARD_MUL_SYM o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
      MATCH_MP_TAC CARD_MUL_ABSORB THEN
      ASM_REWRITE_TAC[UNIV_NOT_EMPTY] THEN
      MATCH_MP_TAC CARD_LE_COUNTABLE_INFINITE THEN
      ASM_REWRITE_TAC[INT_COUNTABLE]];
    REWRITE_TAC[le_c] THEN EXISTS_TAC `frag_of:A->A frag` THEN
    REWRITE_TAC[IN_ELIM_THM; FRAG_SUPPORT_OF; SING_SUBSET] THEN
    SIMP_TAC[FRAG_OF_EQ]]);;

let CARD_EQ_HOMOMORPHISMS_FROM_FREE_ABELIAN_GROUP = prove
 (`!(s:A->bool) (G:B group).
        abelian_group G
        ==> {f | EXTENSIONAL (group_carrier(free_abelian_group s)) f /\
                 group_homomorphism(free_abelian_group s,G) f} =_c
            (group_carrier G) ^_c s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_C; eq_c] THEN
  EXISTS_TAC `\(f:(A)frag->B). RESTRICTION s (f o frag_of)` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  CONJ_TAC THENL
   [SIMP_TAC[group_homomorphism; RESTRICTION; o_THM; FREE_ABELIAN_GROUP;
             SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_ELIM_THM; FRAG_SUPPORT_OF; IN_SING];
    X_GEN_TAC `f:A->B` THEN STRIP_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:A->B`; `s:A->bool`; `G:B group`]
        FREE_ABELIAN_GROUP_UNIVERSAL) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:(A)frag->B` THEN STRIP_TAC THEN EXISTS_TAC
     `RESTRICTION (group_carrier(free_abelian_group s)) (g:A frag->B)` THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
       `group_homomorphism(free_abelian_group s,G) (g:A frag->B)` THEN
      REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
      SIMP_TAC[RESTRICTION; GROUP_MUL];
      UNDISCH_TAC `EXTENSIONAL s (f:A->B)` THEN
      SIMP_TAC[EXTENSIONAL; RESTRICTION; FUN_EQ_THM; IN_ELIM_THM; o_THM] THEN
      DISCH_TAC THEN X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN s` THEN
      ASM_SIMP_TAC[FREE_ABELIAN_GROUP; FRAG_SUPPORT_OF; SING_SUBSET;
                   IN_ELIM_THM]];
    MAP_EVERY X_GEN_TAC [`g:A frag->B`; `h:A frag->B`] THEN
    REWRITE_TAC[FUN_EQ_THM; EXTENSIONAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!c. frag_support c SUBSET s ==> (g:A frag->B) c = h c`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
    MATCH_MP_TAC FRAG_INDUCTION THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET];
      REPEAT(FIRST_X_ASSUM(MP_TAC o el 1 o CONJUNCTS o
        GEN_REWRITE_RULE I [group_homomorphism])) THEN
      SIMP_TAC[FREE_ABELIAN_GROUP];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[RESTRICTION; o_THM; FRAG_SUPPORT_OF; SING_SUBSET] THEN
      SIMP_TAC[];
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[FRAG_SUPPORT_SUB; SUBSET_TRANS; UNION_SUBSET];
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_DIV)) THEN
        REWRITE_TAC[group_div; FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
        REWRITE_TAC[FRAG_MODULE `frag_add x (frag_neg y) = frag_sub x y`] THEN
        ASM_SIMP_TAC[]]]]);;

let ISOMORPHIC_FREE_ABELIAN_GROUPS = prove
 (`!(s:A->bool) (t:B->bool).
      free_abelian_group s isomorphic_group free_abelian_group t <=>
      s =_c t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `{&0:int,&1} ^_c (s:A->bool) =_c {&0:int, &1} ^_c (t:B->bool)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`s:A->bool`; `integer_mod_group 2`]
            CARD_EQ_HOMOMORPHISMS_FROM_FREE_ABELIAN_GROUP) THEN
      MP_TAC(ISPECL [`t:B->bool`; `integer_mod_group 2`]
            CARD_EQ_HOMOMORPHISMS_FROM_FREE_ABELIAN_GROUP) THEN
      REWRITE_TAC[ABELIAN_INTEGER_MOD_GROUP] THEN
      SIMP_TAC[INTEGER_MOD_GROUP; ARITH_RULE `0 < 2`] THEN
      REWRITE_TAC[INT_ARITH `&0:int <= m /\ m < &2 <=> m = &0 \/ m = &1`] THEN
      REWRITE_TAC[SET_RULE `{x | x = a \/ x = b} = {a,b}`] THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
        MP_TAC th THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_EQ_TRANS)) THEN
      REWRITE_TAC[EQ_C_BIJECTIONS; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isomorphic_group]) THEN
      REWRITE_TAC[group_isomorphism; group_isomorphisms;
                  LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`f:A frag->B frag`; `g:B frag->A frag`] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`\(h:A frag->int).
            RESTRICTION (group_carrier (free_abelian_group t))
                        (h o (g:B frag->A frag))`;
        `\(h:B frag->int).
            RESTRICTION (group_carrier (free_abelian_group s))
                        (h o (f:A frag->B frag))`] THEN
      REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `h:A frag->int`; X_GEN_TAC `k:B frag->int`] THEN
      STRIP_TAC THEN
      (CONJ_TAC THENL
       [MATCH_MP_TAC(MESON[GROUP_HOMOMORPHISM_EQ]
         `group_homomorphism(G,H) f /\
          (!x. x IN group_carrier G ==> RESTRICTION s f x = f x)
          ==> group_homomorphism(G,H) (RESTRICTION s f)`) THEN
        SIMP_TAC[RESTRICTION] THEN ASM_MESON_TAC[GROUP_HOMOMORPHISM_COMPOSE];
        REPEAT(FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o
          REWRITE_RULE[group_homomorphism])) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[EXTENSIONAL; IN_ELIM_THM]) THEN
        GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
        ASM_SIMP_TAC[RESTRICTION; o_THM] THEN ASM_MESON_TAC[]]);
      FIRST_ASSUM(MP_TAC o MATCH_MP CARD_FINITE_CONG) THEN
      REWRITE_TAC[CARD_EXP_FINITE_EQ; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[SET_RULE `{a,b} SUBSET {c} <=> a = b /\ a = c`] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC[MESON[FINITE_EMPTY] `s = {} \/ FINITE s <=> FINITE s`] THEN
      REWRITE_TAC[TAUT `(p <=> q) <=> p /\ q \/ ~p /\ ~q`] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC
         `{&0:int, &1} ^_c (s:A->bool) =_c {&0:int, &1} ^_c (t:B->bool)` THEN
        ASM_SIMP_TAC[CARD_EQ_CARD; CARD_EXP_FINITE_EQ; FINITE_INSERT;
                     FINITE_EMPTY; CARD_EXP_C] THEN
        REWRITE_TAC[EQ_EXP] THEN
        SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
        REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
        MP_TAC(ISPEC `t:B->bool` CARD_EQ_FREE_ABELIAN_GROUP_INFINITE) THEN
        ASM_REWRITE_TAC[INFINITE] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_EQ_TRANS) THEN
        ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
        MP_TAC(ISPEC `s:A->bool` CARD_EQ_FREE_ABELIAN_GROUP_INFINITE) THEN
        ASM_REWRITE_TAC[INFINITE] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_EQ_TRANS) THEN
        ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
        ASM_SIMP_TAC[ISOMORPHIC_GROUP_CARD_EQ]]];
    REWRITE_TAC[EQ_C_BIJECTIONS; isomorphic_group; group_isomorphism] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:A->B`; `g:B->A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`frag_of o (f:A->B)`; `s:A->bool`; `free_abelian_group(t:B->bool)`]
          FREE_ABELIAN_GROUP_UNIVERSAL) THEN
    REWRITE_TAC[ABELIAN_FREE_ABELIAN_GROUP; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; o_THM; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FRAG_SUPPORT_OF; SING_SUBSET] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:A frag->B frag` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`frag_of o (g:B->A)`; `t:B->bool`; `free_abelian_group(s:A->bool)`]
          FREE_ABELIAN_GROUP_UNIVERSAL) THEN
    REWRITE_TAC[ABELIAN_FREE_ABELIAN_GROUP; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; o_THM; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FRAG_SUPPORT_OF; SING_SUBSET] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:B frag->A frag` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[group_isomorphisms] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
    CONJ_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
    MATCH_MP_TAC FRAG_INDUCTION THEN
    REWRITE_TAC[FRAG_SUPPORT_0; FRAG_SUPPORT_OF; IN_SING; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[SING_SUBSET] THEN REPEAT(FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [group_homomorphism])) THEN
    REWRITE_TAC[SET_RULE `IMAGE f s SUBSET t <=> !x. x IN s ==> f x IN t`] THEN
    SIMP_TAC[FREE_ABELIAN_GROUP; IN_ELIM_THM] THEN
    REWRITE_TAC[FRAG_MODULE `frag_sub x y = frag_add x (frag_neg y)`] THEN
    SIMP_TAC[FRAG_SUPPORT_NEG] THEN REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_ADD o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
    ASM_REWRITE_TAC[UNION_SUBSET; FRAG_SUPPORT_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* Basic things about exact sequences.                                       *)
(* ------------------------------------------------------------------------- *)

let group_exactness = new_definition
 `group_exactness (G,H,K) ((f:A->B),(g:B->C)) <=>
        group_homomorphism (G,H) f /\ group_homomorphism (H,K) g /\
        group_image (G,H) f = group_kernel (H,K) g`;;

let short_exact_sequence = new_definition
 `short_exact_sequence(A,B,C) (f:A->B,g:B->C) <=>
        group_monomorphism (A,B) f /\
        group_exactness (A,B,C) (f,g) /\
        group_epimorphism (B,C) g`;;

let SHORT_EXACT_SEQUENCE = prove
 (`!(f:A->B) (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) <=>
        group_monomorphism (A,B) f /\
        group_epimorphism (B,C) g /\
        group_image (A,B) f = group_kernel (B,C) g`,
  REWRITE_TAC[short_exact_sequence; group_monomorphism;
              group_exactness; group_epimorphism] THEN
  MESON_TAC[]);;

let GROUP_EXACTNESS_MONOMORPHISM = prove
 (`!f:(A->B) (g:B->C) A B C.
        trivial_group A
        ==> (group_exactness (A,B,C) (f,g) <=>
             group_homomorphism(A,B) f /\ group_monomorphism (B,C) g)`,
  SIMP_TAC[GROUP_MONOMORPHISM; group_exactness; trivial_group; group_image;
           IMAGE_CLAUSES; group_homomorphism] THEN
  MESON_TAC[]);;

let GROUP_EXACTNESS_EPIMORPHISM = prove
 (`!f:(A->B) (g:B->C) A B C.
        trivial_group C
        ==> (group_exactness (A,B,C) (f,g) <=>
             group_epimorphism(A,B) f /\ group_homomorphism (B,C) g)`,
  SIMP_TAC[GROUP_EPIMORPHISM; group_exactness; trivial_group] THEN
  SIMP_TAC[group_homomorphism; group_kernel] THEN SET_TAC[]);;

let EXTREMELY_SHORT_EXACT_SEQUENCE = prove
 (`!f:(A->B) (g:B->C) A B C.
        group_exactness (A,B,C) (f,g) /\
        trivial_group A /\ trivial_group C
        ==> trivial_group B`,
  REWRITE_TAC[group_exactness] THEN
  MESON_TAC[GROUP_KERNEL_TO_TRIVIAL_GROUP; GROUP_IMAGE_FROM_TRIVIAL_GROUP;
            trivial_group]);;

let GROUP_EXACTNESS_EPIMORPHISM_EQ_TRIVIALITY = prove
 (`!(f:A->B) (g:B->C) (h:C->D) A B C D.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h)
        ==> (group_epimorphism (A,B) f <=> trivial_homomorphism(B,C) g)`,
  REWRITE_TAC[group_exactness; GROUP_EPIMORPHISM] THEN
  SIMP_TAC[TRIVIAL_HOMOMORPHISM_GROUP_KERNEL]);;

let GROUP_EXACTNESS_MONOMORPHISM_EQ_TRIVIALITY = prove
 (`!(f:A->B) (g:B->C) (h:C->D) A B C D.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h)
        ==> (group_monomorphism (C,D) h <=>  trivial_homomorphism(B,C) g)`,
  REWRITE_TAC[group_exactness; GROUP_MONOMORPHISM] THEN
  SIMP_TAC[TRIVIAL_HOMOMORPHISM_GROUP_IMAGE]);;

let VERY_SHORT_EXACT_SEQUENCE = prove
 (`!(f:A->B) (g:B->C) (h:C->D) A B C D.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        trivial_group A /\ trivial_group D
        ==> group_isomorphism (B,C) g`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[GROUP_MONOMORPHISM; GROUP_EPIMORPHISM; group_exactness] THEN
  MESON_TAC[GROUP_IMAGE_FROM_TRIVIAL_GROUP;
            GROUP_KERNEL_TO_TRIVIAL_GROUP]);;

let GROUP_EXACTNESS_EQ_TRIVIALITY = prove
 (`!f:(A->B) (g:B->C) (h:C->D) (k:D->E) A B C D E.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,k)
        ==> (trivial_group C <=>
             group_epimorphism (A,B) f /\
             group_monomorphism (D,E) k)`,
  REWRITE_TAC[group_exactness; GROUP_EPIMORPHISM;
              GROUP_MONOMORPHISM] THEN
  ASM_MESON_TAC[trivial_group; GROUP_IMAGE_FROM_TRIVIAL_GROUP;
                GROUP_KERNEL_IMAGE_TRIVIAL]);;

let GROUP_EXACTNESS_IMP_TRIVIALITY = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (k:D->E) A B C D E.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,k) /\
        group_isomorphism (A,B) f /\
        group_isomorphism (D,E) k
        ==> trivial_group C`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  MESON_TAC[GROUP_EXACTNESS_EQ_TRIVIALITY]);;

let GROUP_EXACTNESS_ISOMORPHISM_EQ_TRIVIALITY = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (j:D->E) (k:E->G) A B C D E G.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,j) /\
        group_exactness (D,E,G) (j,k)
        ==> (group_isomorphism (C,D) h <=>
             trivial_homomorphism(B,C) g /\ trivial_homomorphism(D,E) j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP GROUP_EXACTNESS_MONOMORPHISM_EQ_TRIVIALITY)
   (MP_TAC o MATCH_MP GROUP_EXACTNESS_EPIMORPHISM_EQ_TRIVIALITY)) THEN
  MESON_TAC[]);;

let GROUP_EXACTNESS_ISOMORPHISM_EQ_MONO_EPI = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (j:D->E) (k:E->G) A B C D E G.
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,D) (g,h) /\
        group_exactness (C,D,E) (h,j) /\
        group_exactness (D,E,G) (j,k)
        ==> (group_isomorphism (C,D) h <=>
             group_epimorphism(A,B) f /\ group_monomorphism(E,G) k)`,
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM;
              GROUP_EPIMORPHISM; GROUP_MONOMORPHISM] THEN
  REWRITE_TAC[group_exactness] THEN MESON_TAC[GROUP_KERNEL_IMAGE_TRIVIAL]);;

let SHORT_EXACT_SEQUENCE_NORMAL_SUBGROUP = prove
 (`!G n:A->bool.
        n normal_subgroup_of G
        ==> short_exact_sequence
             (subgroup_generated G n,G,quotient_group G n)
             ((\x. x),right_coset G n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SHORT_EXACT_SEQUENCE; I_DEF] THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_INCLUSION] THEN
  ASM_SIMP_TAC[GROUP_EPIMORPHISM_RIGHT_COSET] THEN
  ASM_SIMP_TAC[GROUP_KERNEL_RIGHT_COSET; group_image; IMAGE_ID] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               NORMAL_SUBGROUP_IMP_SUBGROUP]);;

let SHORT_EXACT_SEQUENCE_PROD_GROUP = prove
 (`!(G:A group) (H:B group).
        short_exact_sequence(G,prod_group G H,H) ((\x. x,group_id H),SND)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SHORT_EXACT_SEQUENCE; GROUP_EPIMORPHISM_SND] THEN
  SIMP_TAC[group_monomorphism; PAIR_EQ] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRED] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL; GROUP_HOMOMORPHISM_ID] THEN
  REWRITE_TAC[group_image; group_kernel; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  REWRITE_TAC[PROD_GROUP; IN_CROSS] THEN MESON_TAC[GROUP_ID]);;

let SHORT_EXACT_SEQUENCE_PROD_GROUP_ALT = prove
 (`!(G:A group) (H:B group).
        short_exact_sequence(H,prod_group G H,G) ((\x. group_id G,x),FST)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SHORT_EXACT_SEQUENCE; GROUP_EPIMORPHISM_FST] THEN
  SIMP_TAC[group_monomorphism; PAIR_EQ] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRED] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL; GROUP_HOMOMORPHISM_ID] THEN
  REWRITE_TAC[group_image; group_kernel; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  REWRITE_TAC[PROD_GROUP; IN_CROSS] THEN MESON_TAC[GROUP_ID]);;

let EXACT_SEQUENCE_SUM_LEMMA = prove
 (`!(f:X->C) (g:X->D) (h:A->C) (i:A->X) (j:B->X) (k:B->D) A B C D X.
        abelian_group X /\
        group_isomorphism(A,C) h /\
        group_isomorphism(B,D) k /\
        group_exactness(A,X,D) (i,g) /\
        group_exactness(B,X,C) (j,f) /\
        (!x. x IN group_carrier A ==> f(i x) = h x) /\
        (!x. x IN group_carrier B ==> g(j x) = k x)
        ==> group_isomorphism (prod_group A B,X)
                              (\(x,y). group_mul X (i x) (j y)) /\
            group_isomorphism (X,prod_group C D) (\z. f z,g z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_exactness] THEN STRIP_TAC THEN
  ABBREV_TAC `ij:A#B->X = \(x,y). group_mul X (i x) (j y)` THEN
  ABBREV_TAC `gf:X->C#D = \z. f z,g z` THEN
  MATCH_MP_TAC GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV THEN
  SUBGOAL_THEN `group_homomorphism (prod_group A B,X) (ij:A#B->X)`
  ASSUME_TAC THENL
   [EXPAND_TAC "ij" THEN REWRITE_TAC[LAMBDA_PAIR] THEN
    MATCH_MP_TAC ABELIAN_GROUP_HOMOMORPHISM_GROUP_MUL THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_OF_FST; GROUP_HOMOMORPHISM_OF_SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `group_homomorphism (X,prod_group C D) (gf:X->C#D)`
  ASSUME_TAC THENL
   [EXPAND_TAC "gf" THEN REWRITE_TAC[GROUP_HOMOMORPHISM_PAIRED] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GROUP_EPIMORPHISM_ALT] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN
    EXISTS_TAC `(\(x,y). h x,k y):A#B->C#D` THEN
    ASM_REWRITE_TAC[GROUP_ISOMORPHISM_PAIRED2] THEN
    MAP_EVERY EXPAND_TAC ["gf"; "ij"] THEN
    REWRITE_TAC[PROD_GROUP; o_DEF; PAIR_EQ; IN_CROSS; FORALL_PAIR_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [GROUP_ISOMORPHISM; group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[GROUP_LID_EQ; GROUP_RID_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_image; group_kernel]) THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:X` THEN DISCH_TAC THEN
  UNDISCH_TAC `group_image (B,X) (j:B->X) = group_kernel (X,C) (f:X->C)` THEN
  MP_TAC(ASSUME `group_isomorphism (A,C) (h:A->C)`) THEN
  REWRITE_TAC[group_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h':C->A` THEN REWRITE_TAC[group_isomorphisms] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE o
    SPEC `group_div X x ((i:A->X)((h':C->A)(f x)))`) THEN
  REWRITE_TAC[group_kernel; group_image; IN_ELIM_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [group_homomorphism; GROUP_ISOMORPHISM; SUBSET; FORALL_IN_IMAGE]) THEN
  ANTS_TAC THENL
   [ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [group_div; GROUP_INV; GROUP_MUL; GROUP_MUL_RINV];
    EXPAND_TAC "ij" THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:B` THEN SIMP_TAC[PROD_GROUP; IN_CROSS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
    EXISTS_TAC `(h':C->A)(f(x:X))` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
        W(MP_TAC o PART_MATCH (lhand o rand)
              (GEN_REWRITE_RULE I [abelian_group] th) o rand o snd)) THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [group_div; GROUP_INV; GROUP_MUL; GSYM GROUP_MUL_ASSOC;
      GROUP_MUL_LINV; GROUP_MUL_RID]]);;

let SHORT_EXACT_SEQUENCE_QUOTIENT = prove
 (`!(f:A->B) (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g)
        ==> subgroup_generated B (group_image(A,B) f) isomorphic_group A /\
            quotient_group B (group_image(A,B) f) isomorphic_group C`,
  REWRITE_TAC[short_exact_sequence] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN EXISTS_TAC `f:A->B` THEN
    ASM_REWRITE_TAC[GROUP_ISOMORPHISM_ONTO_IMAGE];
    MP_TAC(ISPECL
     [`B:B group`; `C:C group`; `g:B->C`]
     FIRST_GROUP_ISOMORPHISM_THEOREM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GROUP_EPIMORPHISM; group_exactness]) THEN
    ASM_REWRITE_TAC[SUBGROUP_GENERATED_GROUP_CARRIER]]);;

let TRIVIAL_GROUPS_IMP_SHORT_EXACT_SEQUENCE = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (k:D->E) A B C D E.
        trivial_group A /\ trivial_group E /\
        group_exactness(A,B,C) (f,g) /\
        group_exactness(B,C,D) (g,h) /\
        group_exactness(C,D,E) (h,k)
        ==> short_exact_sequence(B,C,D) (g,h)`,
  SIMP_TAC[IMP_CONJ; GROUP_EXACTNESS_MONOMORPHISM; GROUP_EXACTNESS_EPIMORPHISM;
           short_exact_sequence]);;

let SHORT_EXACT_SEQUENCE_TRIVIAL_GROUPS = prove
 (`!(g:B->C) h B C D.
        short_exact_sequence(B,C,D) (g,h) <=>
        ?f:(A->B) (k:D->E) A E.
                trivial_group A /\ trivial_group E /\
                group_exactness(A,B,C) (f,g) /\
                group_exactness(B,C,D) (g,h) /\
                group_exactness(C,D,E) (h,k)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[TRIVIAL_GROUPS_IMP_SHORT_EXACT_SEQUENCE] THEN
  REWRITE_TAC[short_exact_sequence] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`(\x. group_id B):A->B`; `(\x. ARB):D->E`;
    `singleton_group (ARB:A)`; `singleton_group (ARB:E)`] THEN
  ASM_SIMP_TAC[TRIVIAL_GROUP_SINGLETON_GROUP;
               GROUP_EXACTNESS_MONOMORPHISM; GROUP_EXACTNESS_EPIMORPHISM] THEN
  REWRITE_TAC[group_homomorphism; SINGLETON_GROUP] THEN
  SIMP_TAC[GROUP_INV_ID; GROUP_MUL_LID; GROUP_ID; SUBSET; FORALL_IN_IMAGE;
           IN_SING]);;

let SPLITTING_SUBLEMMA_GEN = prove
 (`!(f:A->B) (g:B->C) A B C h k.
        group_exactness(A,B,C) (f,g) /\
        group_image(A,B) f = h /\ k subgroup_of B /\
        h INTER k SUBSET {group_id B} /\ group_setmul B h k = group_carrier B
        ==> group_isomorphism(subgroup_generated B k,
                              subgroup_generated C (group_image(B,C) g)) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group_exactness] THEN
  ASM_CASES_TAC `group_image(A,B) (f:A->B) = h` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `group_kernel(B,C) (g:B->C) = h` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:B->bool) subgroup_of B` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_GROUP_KERNEL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; GROUP_MONOMORPHISM;
              GROUP_EPIMORPHISM_ALT] THEN
  REWRITE_TAC[TAUT `(p /\ q) /\ (p /\ r) <=> p /\ q /\ r`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN;
                 CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 SUBGROUP_GROUP_IMAGE;
                 GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[group_image; SUBGROUP_OF_IMP_SUBSET; IMAGE_SUBSET];
    ASM_SIMP_TAC[GROUP_KERNEL_FROM_SUBGROUP_GENERATED;
                 GROUP_KERNEL_TO_SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[SUBGROUP_GENERATED; GSYM GROUP_DISJOINT_SUM_ALT];
    ASM_SIMP_TAC[SUBSET; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
                 SUBGROUP_GROUP_IMAGE] THEN
    REWRITE_TAC[group_image; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    SUBST1_TAC(SYM(ASSUME
     `group_setmul B (h:B->bool) k = group_carrier B`)) THEN
    REWRITE_TAC[group_setmul; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[group_epimorphism; group_homomorphism;
                                subgroup_of; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[IN_IMAGE] THEN EXISTS_TAC `y:B` THEN
    UNDISCH_TAC `(x:B) IN h` THEN SUBST1_TAC(SYM(ASSUME
       `group_kernel (B,C) (g:B->C) = h`)) THEN
    SIMP_TAC[group_kernel; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[GROUP_MUL_LID]]);;

let SPLITTING_SUBLEMMA = prove
 (`!(f:A->B) (g:B->C) A B C h k.
        short_exact_sequence(A,B,C) (f,g) /\
        group_image(A,B) f = h /\ k subgroup_of B /\
        h INTER k SUBSET {group_id B} /\ group_setmul B h k = group_carrier B
        ==> group_isomorphism(A,subgroup_generated B h) f /\
            group_isomorphism(subgroup_generated B k,C) g`,
  REWRITE_TAC[short_exact_sequence] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[GROUP_ISOMORPHISM_ONTO_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `C = subgroup_generated C (group_image(B,C) (g:B->C))`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[group_epimorphism; group_image;
                  SUBGROUP_GENERATED_GROUP_CARRIER];
    MATCH_MP_TAC SPLITTING_SUBLEMMA_GEN THEN ASM_MESON_TAC[]]);;

let SPLITTING_LEMMA_LEFT_GEN = prove
 (`!(f:A->B) f' (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(B,A) f' /\
        group_isomorphism(A,A) (f' o f)
        ==> ?h k. h normal_subgroup_of B /\ k normal_subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `f':B->A`; `A:A group`; `B:B group`; `A:A group`]
        GROUP_SEMIDIRECT_SUM_IM_KER) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[short_exact_sequence; group_exactness]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`h = group_image(A,B) (f:A->B)`; `k = group_kernel(B,A) (f':B->A)`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`h:B->bool`; `k:B->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC(TAUT
   `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[NORMAL_SUBGROUP_GROUP_KERNEL;
                  short_exact_sequence; group_exactness];
    REWRITE_TAC[normal_subgroup_of] THEN STRIP_TAC THEN
    MATCH_MP_TAC SPLITTING_SUBLEMMA THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let SPLITTING_LEMMA_LEFT = prove
 (`!(f:A->B) f' (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(B,A) f' /\
        (!x. x IN group_carrier A ==> f'(f x) = x)
        ==> ?h k. h normal_subgroup_of B /\ k normal_subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPLITTING_LEMMA_LEFT_GEN THEN
  EXISTS_TAC `f':B->A` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN EXISTS_TAC `\x:A. x` THEN
  ASM_REWRITE_TAC[o_THM; GROUP_ISOMORPHISM_ID]);;

let SPLITTING_LEMMA_LEFT_PROD_GROUP = prove
 (`!(f:A->B) f' (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        abelian_group B /\
        group_homomorphism(B,A) f' /\
        (!x. x IN group_carrier A ==> f'(f x) = x)
        ==> B isomorphic_group prod_group A C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `f':B->A`; `g:B->C`;
        `A:A group`; `B:B group`; `C:C group`]
        SPLITTING_LEMMA_LEFT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:B->bool`; `k:B->bool`] THEN STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_GROUP_TRANS
   `prod_group (subgroup_generated B h)
               (subgroup_generated B (k:B->bool))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN
    EXISTS_TAC `\(x:B,y). group_mul B x y` THEN
    ASM_SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL; NORMAL_SUBGROUP_IMP_SUBGROUP];
    MATCH_MP_TAC ISOMORPHIC_GROUP_PROD_GROUPS THEN
    GEN_REWRITE_TAC LAND_CONV [ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN ASM_MESON_TAC[]]);;

let SPLITTING_LEMMA_RIGHT_GEN = prove
 (`!(f:A->B) (g:B->C) g' A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(C,B) g' /\
        group_isomorphism(C,C) (g o g')
        ==> ?h k. h normal_subgroup_of B /\ k subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g':C->B`; `g:B->C`; `C:C group`; `B:B group`; `C:C group`]
        GROUP_SEMIDIRECT_SUM_KER_IM) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[short_exact_sequence; group_exactness]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`k = group_image(C,B) (g':C->B)`; `h = group_kernel(B,C) (g:B->C)`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`h:B->bool`; `k:B->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC(TAUT
   `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[SUBGROUP_GROUP_IMAGE; NORMAL_SUBGROUP_GROUP_KERNEL;
                  short_exact_sequence; group_exactness];
    REWRITE_TAC[normal_subgroup_of] THEN STRIP_TAC THEN
    MATCH_MP_TAC SPLITTING_SUBLEMMA THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[short_exact_sequence; group_exactness]]);;

let SPLITTING_LEMMA_RIGHT = prove
 (`!(f:A->B) (g:B->C) g' A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        group_homomorphism(C,B) g' /\
        (!z. z IN group_carrier C ==> g(g' z) = z)
        ==> ?h k. h normal_subgroup_of B /\ k subgroup_of B /\
                  h INTER k SUBSET {group_id B} /\
                  group_setmul B h k = group_carrier B /\
                  group_isomorphism(A,subgroup_generated B h) f /\
                  group_isomorphism(subgroup_generated B k,C) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPLITTING_LEMMA_RIGHT_GEN THEN
  EXISTS_TAC `g':C->B` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN EXISTS_TAC `\x:C. x` THEN
  ASM_REWRITE_TAC[o_THM; GROUP_ISOMORPHISM_ID]);;

let SPLITTING_LEMMA_RIGHT_PROD_GROUP = prove
 (`!(f:A->B) (g:B->C) g' A B C.
        short_exact_sequence(A,B,C) (f,g) /\
        abelian_group B /\
        group_homomorphism(C,B) g' /\
        (!z. z IN group_carrier C ==> g(g' z) = z)
        ==> B isomorphic_group prod_group A C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `g':C->B`;
        `A:A group`; `B:B group`; `C:C group`]
        SPLITTING_LEMMA_RIGHT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:B->bool`; `k:B->bool`] THEN STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_GROUP_TRANS
   `prod_group (subgroup_generated B h)
               (subgroup_generated B (k:B->bool))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN
    EXISTS_TAC `\(x:B,y). group_mul B x y` THEN
    ASM_SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL; NORMAL_SUBGROUP_IMP_SUBGROUP];
    MATCH_MP_TAC ISOMORPHIC_GROUP_PROD_GROUPS THEN
    GEN_REWRITE_TAC LAND_CONV [ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN ASM_MESON_TAC[]]);;

let SPLITTING_LEMMA_FREE_ABELIAN_GROUP = prove
 (`!(f:A->B) (g:B->C) A B C (s:D->bool).
        short_exact_sequence (A,B,C) (f,g) /\
        abelian_group B /\ C isomorphic_group free_abelian_group s
        ==> B isomorphic_group prod_group A C`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPLITTING_LEMMA_RIGHT_PROD_GROUP THEN
  MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->C`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [short_exact_sequence]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_epimorphism]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s = t ==> !y. ?x. y IN t ==> x IN s /\ f x = y`)) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g':C->B` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isomorphic_group]) THEN
  REWRITE_TAC[isomorphic_group; group_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:C->D frag`; `h':D frag->C`] THEN
  REWRITE_TAC[group_isomorphisms] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(g':C->B) o (h':D frag->C) o frag_of`; `s:D->bool`; `B:B group`]
        FREE_ABELIAN_GROUP_UNIVERSAL) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ANTS_TAC THENL
   [GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV)
     [GSYM FRAG_OF_IN_FREE_ABELIAN_GROUP] THEN
    RULE_ASSUM_TAC( REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:D frag->B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(k:D frag->B) o (h:C->D frag)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[GROUP_HOMOMORPHISM_COMPOSE]; ALL_TAC] THEN
    X_GEN_TAC `c:C` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `c = (h':D frag->C) (h c) /\
      h c IN group_carrier(free_abelian_group s)`
    (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THENL
     [RULE_ASSUM_TAC( REWRITE_RULE[group_homomorphism]) THEN ASM SET_TAC[];
      SPEC_TAC(`(h:C->D frag) c`,`d:D frag`)] THEN
    ASM_SIMP_TAC[o_THM] THEN
    MATCH_MP_TAC FREE_ABELIAN_GROUP_INDUCT THEN
    ASM_SIMP_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      MP_TAC(MATCH_MP GROUP_HOMOMORPHISM_DIV th) THEN
      MP_TAC(REWRITE_RULE[group_homomorphism; SUBSET] th))) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; group_div] THEN
    REWRITE_TAC[CONJUNCT2 FREE_ABELIAN_GROUP; FRAG_MODULE
     `frag_add x (frag_neg y) = frag_sub x y`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[FRAG_OF_IN_FREE_ABELIAN_GROUP]]);;

let FOUR_LEMMA_MONO = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (f':A'->B') (g':B'->C') (h':C'->D') a b c d
     A B C D A' B' C' D'.
      group_epimorphism(A,A') a /\
      group_monomorphism(B,B') b /\
      group_homomorphism(C,C') c /\
      group_monomorphism(D,D') d /\
      group_exactness(A,B,C) (f,g) /\ group_exactness(B,C,D) (g,h) /\
      group_exactness(A',B',C') (f',g') /\ group_exactness(B',C',D') (g',h') /\
      (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
      (!y. y IN group_carrier B ==> g'(b y) = c(g y)) /\
      (!z. z IN group_carrier C ==> h'(c z) = d(h z))
      ==> group_monomorphism(C,C') c`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GROUP_MONOMORPHISM_ALT] THEN
  REWRITE_TAC[group_epimorphism; group_monomorphism; group_exactness] THEN
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[group_image; group_kernel] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:C` THEN STRIP_TAC THEN
  MAP_EVERY (ASSUME_TAC o C ISPEC GROUP_ID)
   [`A:A group`; `B:B group`; `C:C group`; `D:D group`;
    `A':A' group`; `B':B' group`; `C':C' group`; `D':D' group`] THEN
  SUBGOAL_THEN `(h:C->D) x = group_id D`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?y. y IN group_carrier B /\ (g:B->C) y = x`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?w. w IN group_carrier A' /\ (f':A'->B') w = (b:B->B') y`
  STRIP_ASSUME_TAC THEN ASM SET_TAC[]);;

let FOUR_LEMMA_EPI = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (f':A'->B') (g':B'->C') (h':C'->D') a b c d
     A B C D A' B' C' D'.
      group_epimorphism(A,A') a /\
      group_homomorphism(B,B') b /\
      group_epimorphism(C,C') c /\
      group_monomorphism(D,D') d /\
      group_exactness(A,B,C) (f,g) /\ group_exactness(B,C,D) (g,h) /\
      group_exactness(A',B',C') (f',g') /\ group_exactness(B',C',D') (g',h') /\
      (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
      (!y. y IN group_carrier B ==> g'(b y) = c(g y)) /\
      (!z. z IN group_carrier C ==> h'(c z) = d(h z))
      ==> group_epimorphism(B,B') b`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GROUP_EPIMORPHISM_ALT] THEN
  REWRITE_TAC[group_epimorphism; group_monomorphism; group_exactness] THEN
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[group_image; group_kernel] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:B'` THEN DISCH_TAC THEN
  MAP_EVERY (ASSUME_TAC o C ISPEC GROUP_ID)
   [`A:A group`; `B:B group`; `C:C group`; `D:D group`;
    `A':A' group`; `B':B' group`; `C':C' group`; `D':D' group`] THEN
  SUBGOAL_THEN `?y. y IN group_carrier C /\ (c:C->C') y = (g':B'->C') x`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:C->D) y = group_id D`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z. z IN group_carrier B /\ (g:B->C) z = y`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w =  group_mul B' x (group_inv B' ((b:B->B') z))` THEN
  SUBGOAL_THEN `(w:B') IN group_carrier B'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[GROUP_MUL; GROUP_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `(g':B'->C') w = group_id C'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[GROUP_INV; GROUP_MUL_RINV];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. v IN group_carrier A' /\ (f':A'->B') v = w`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?u. u IN group_carrier A /\ (a:A->A') u = v`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `group_mul B ((f:A->B) u) z` THEN ASM_SIMP_TAC[GROUP_MUL] THEN
  SUBGOAL_THEN `(b:B->B') ((f:A->B) u) = w`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME
   `group_mul B' x (group_inv B' ((b:B->B') z)) = w`)) THEN
  ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_INV;
               GROUP_MUL_LINV; GROUP_MUL_RID]);;

let FIVE_LEMMA = prove
 (`!(f:A->B) (g:B->C) (h:C->D) (k:D->E)
    (f':A'->B') (g':B'->C') (h':C'->D') (k':D'->E') a b c d e
     A B C D E A' B' C' D' E'.
      group_epimorphism(A,A') a /\
      group_isomorphism(B,B') b /\
      group_homomorphism(C,C') c /\
      group_isomorphism(D,D') d /\
      group_monomorphism(E,E') e /\
      group_exactness(A,B,C) (f,g) /\
      group_exactness(B,C,D) (g,h) /\
      group_exactness(C,D,E) (h,k) /\
      group_exactness(A',B',C') (f',g') /\
      group_exactness(B',C',D') (g',h') /\
      group_exactness(C',D',E') (h',k') /\
      (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
      (!y. y IN group_carrier B ==> g'(b y) = c(g y)) /\
      (!z. z IN group_carrier C ==> h'(c z) = d(h z)) /\
      (!w. w IN group_carrier D ==> k'(d w) = e(k w))
      ==> group_isomorphism(C,C') c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT
   `a /\ (b /\ b') /\ c /\ (d /\ d') /\ e /\
    fg /\ gh /\ hk /\ fg' /\ gh' /\ hk' /\
    ca /\ cb /\ cc /\ cd
    ==> (a /\ b /\ c /\ d /\ fg /\ gh /\ fg' /\ gh' /\ ca /\ cb /\ cc) /\
        (b' /\ c /\ d' /\ e /\ gh /\ hk /\ gh' /\ hk' /\ cb /\ cc /\ cd)`)) THEN
  MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[FOUR_LEMMA_MONO; FOUR_LEMMA_EPI]);;

let SHORT_FIVE_LEMMA_MONO = prove
 (`!(f:A->B) (g:B->C) (f':A'->B') (g':B'->C') a b c A B C A' B' C'.
        group_monomorphism(A,A') a /\
        group_homomorphism(B,B') b /\
        group_monomorphism(C,C') c /\
        short_exact_sequence(A,B,C) (f,g) /\
        short_exact_sequence(A',B',C') (f',g') /\
        (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
        (!y. y IN group_carrier B ==> g'(b y) = c(g y))
        ==> group_monomorphism(B,B') b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(?(w:Z->A) (z:C->Z) W Z.
        trivial_group W /\ trivial_group Z /\
        group_exactness (W,A,B) (w,f:A->B) /\
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,Z) (g:B->C,z)) /\
    (?(w':Z->A') (z':C'->Z) W' Z'.
        trivial_group W' /\ trivial_group Z' /\
        group_exactness (W',A',B') (w',f':A'->B') /\
        group_exactness (A',B',C') (f',g') /\
        group_exactness (B',C',Z') (g':B'->C',z'))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SHORT_EXACT_SEQUENCE_TRIVIAL_GROUPS]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`w:Z->A`; `f:A->B`; `g:B->C`; `w':Z->A'`; `f':A'->B'`; `g':B'->C'`;
    `(\x. group_id W'):Z->Z`; `a:A->A'`; `b:B->B'`; `c:C->C'`;
    `W:Z group`; `A:A group`; `B:B group`; `C:C group`;
    `W':Z group`; `A':A' group`; `B':B' group`; `C':C' group`]
        FOUR_LEMMA_MONO) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[GROUP_EPIMORPHISM_TO_TRIVIAL_GROUP] THEN
  ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_exactness; group_monomorphism;
    trivial_group; group_homomorphism]) THEN
  ASM SET_TAC[]);;

let SHORT_FIVE_LEMMA_EPI = prove
 (`!(f:A->B) (g:B->C) (f':A'->B') (g':B'->C') a b c A B C A' B' C'.
        group_epimorphism(A,A') a /\
        group_homomorphism(B,B') b /\
        group_epimorphism(C,C') c /\
        short_exact_sequence(A,B,C) (f,g) /\
        short_exact_sequence(A',B',C') (f',g') /\
        (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
        (!y. y IN group_carrier B ==> g'(b y) = c(g y))
        ==> group_epimorphism(B,B') b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(?(w:Z->A) (z:C->Z) W Z.
        trivial_group W /\ trivial_group Z /\
        group_exactness (W,A,B) (w,f:A->B) /\
        group_exactness (A,B,C) (f,g) /\
        group_exactness (B,C,Z) (g:B->C,z)) /\
    (?(w':Z->A') (z':C'->Z) W' Z'.
        trivial_group W' /\ trivial_group Z' /\
        group_exactness (W',A',B') (w',f':A'->B') /\
        group_exactness (A',B',C') (f',g') /\
        group_exactness (B',C',Z') (g':B'->C',z'))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SHORT_EXACT_SEQUENCE_TRIVIAL_GROUPS]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:A->B`; `g:B->C`; `z:C->Z`;  `f':A'->B'`; `g':B'->C'`; `z':C'->Z`;
    `a:A->A'`; `b:B->B'`; `c:C->C'`; `(\x. group_id Z'):Z->Z`;
    `A:A group`; `B:B group`; `C:C group`; `Z:Z group`;
    `A':A' group`; `B':B' group`; `C':C' group`; `Z':Z group`]
        FOUR_LEMMA_EPI) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP] THEN
  ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[group_exactness; group_epimorphism;
    trivial_group; group_homomorphism]) THEN
  ASM SET_TAC[]);;

let SHORT_FIVE_LEMMA = prove
 (`!(f:A->B) (g:B->C) (f':A'->B') (g':B'->C') a b c A B C A' B' C'.
        group_isomorphism(A,A') a /\
        group_homomorphism(B,B') b /\
        group_isomorphism(C,C') c /\
        short_exact_sequence(A,B,C) (f,g) /\
        short_exact_sequence(A',B',C') (f',g') /\
        (!x. x IN group_carrier A ==> f'(a x) = b(f x)) /\
        (!y. y IN group_carrier B ==> g'(b y) = c(g y))
        ==> group_isomorphism(B,B') b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT
   `(a /\ a') /\ b /\ (c /\ c') /\ d /\ e /\ f /\ g
    ==> (a /\ b /\ c /\ d /\ e /\ f /\ g) /\
        (a' /\ b /\ c' /\ d /\ e /\ f /\ g)`)) THEN
  MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[SHORT_FIVE_LEMMA_MONO; SHORT_FIVE_LEMMA_EPI]);;

let EXACT_SEQUENCE_HEXAGON_LEMMA = prove
 (`!(f:X->C) (g:X->D) (h:A->C) (h':C->A) (i:A->X) (j:B->X) (k:B->D) (k':D->B)
    (a:A->Y) (b:B->Y) (c:W->C) (d:W->D) (l:W->X) (m:X->Y) A B C D W X Y.
        abelian_group X /\
        group_homomorphism(A,Y) a /\
        group_homomorphism(B,Y) b /\
        group_homomorphism(W,C) c /\
        group_homomorphism(W,D) d /\
        group_isomorphisms(A,C) (h,h') /\
        group_isomorphisms(B,D) (k,k') /\
        group_exactness(A,X,D) (i,g) /\
        group_exactness(B,X,C) (j,f) /\
        group_exactness(W,X,Y) (l,m) /\
        (!x. x IN group_carrier W ==> f(l x) = c x) /\
        (!x. x IN group_carrier W ==> g(l x) = d x) /\
        (!x. x IN group_carrier A ==> f(i x) = h x) /\
        (!x. x IN group_carrier A ==> m(i x) = a x) /\
        (!x. x IN group_carrier B ==> g(j x) = k x) /\
        (!x. x IN group_carrier B ==> m(j x) = b x)
        ==> !x. x IN group_carrier W
                ==> group_inv Y (a(h'(c x))) = b(k'(d x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:W->X) x IN group_carrier X` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[group_homomorphism; group_exactness]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(c:W->C) x IN group_carrier C /\
    (h':C->A) (c x) IN group_carrier A /\
    (a:A->Y) (h'(c x)) IN group_carrier Y /\
    (i:A->X) (h'(c x)) IN group_carrier X /\
    (d:W->D) x IN group_carrier D /\
    (k':D->B) (d x) IN group_carrier B /\
    (b:B->Y) (k'(d x)) IN group_carrier Y /\
    (j:B->X) (k'(d x)) IN group_carrier X`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE
     [group_isomorphisms; group_homomorphism; group_exactness]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:X->C`; `g:X->D`; `h:A->C`; `i:A->X`; `j:B->X`; `k:B->D`;
    `A:A group`; `B:B group`; `C:C group`; `D:D group`; `X:X group`]
   EXACT_SEQUENCE_SUM_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[group_isomorphism]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM_ALT] o
        CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPEC `(l:W->X) x` o MATCH_MP(SET_RULE
   `IMAGE f s = t /\ P ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
  ASM_REWRITE_TAC[PROD_GROUP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:B`] THEN REWRITE_TAC[IN_CROSS] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(i:A->X) u IN group_carrier X /\
    (j:B->X) v IN group_carrier X /\
    (f:X->C) (i u) IN group_carrier C /\
    (f:X->C) (j v) IN group_carrier C /\
    (g:X->D) (i u) IN group_carrier D /\
    (g:X->D) (j v) IN group_carrier D`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE
     [group_isomorphisms; group_homomorphism; group_exactness]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_RULE
   `group_inv G x = y <=> group_mul G x y = group_id G`] THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (rand o rand) th o lhand o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (rand o rand) th o rand o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `group_exactness (W,X,Y) ((l:W->X),(m:X->Y))` THEN
  REWRITE_TAC[group_exactness] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[group_homomorphism] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[GSYM(el 3 (CONJUNCTS th))]) THEN
  REWRITE_TAC[group_image; group_kernel] THEN
  MATCH_MP_TAC(SET_RULE
   `y IN s /\ y IN IMAGE l t
    ==> IMAGE l t = {x | x IN s /\ m x = z} ==> m y = z`) THEN
  ASM_SIMP_TAC[GROUP_MUL; IN_IMAGE] THEN EXISTS_TAC `x:W` THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  BINOP_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (rand o rand) th o rand o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THENL
   [SUBGOAL_THEN
    `group_mul C ((f:X->C) ((i:A->X) u)) ((f:X->C) (((j:B->X) v))) = h u`
    MP_TAC THENL
     [ALL_TAC; RULE_ASSUM_TAC(REWRITE_RULE
       [group_isomorphisms; group_homomorphism; group_exactness]) THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN
    `group_mul D ((g:X->D) ((i:A->X) u)) ((g:X->D) (((j:B->X) v))) = k v`
    MP_TAC THENL
     [ALL_TAC; RULE_ASSUM_TAC(REWRITE_RULE
       [group_isomorphisms; group_homomorphism; group_exactness]) THEN
      ASM SET_TAC[]]] THEN
  FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (rand o rand) th o rand o snd)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GROUP_RULE `group_mul G x y = x <=> y = group_id G`] THEN
  ASM_SIMP_TAC[GROUP_RULE `group_mul G x y = y <=> x = group_id G`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
       [group_isomorphisms; group_homomorphism; group_exactness;
        group_image; group_kernel]) THEN
  ASM SET_TAC[]);;
