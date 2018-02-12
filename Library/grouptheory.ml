(* ========================================================================= *)
(* Simple formulation of group theory with a type of "(A)group".             *)
(* ========================================================================= *)

needs "Library/frag.ml";;       (* Used eventually for free Abelian groups   *)
needs "Library/card.ml";;       (* Need cardinal arithmetic in a few places  *)

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

let SUBGROUP_GENERATED_INC = prove
 (`!G s x:A.
        s SUBSET group_carrier G /\ x IN s
        ==> x IN group_carrier(subgroup_generated G s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
  REWRITE_TAC[SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET]);;

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

let GROUP_MONOMORPHISM_EPIMORPHISM = prove
 (`!G G' f:A->B.
        group_monomorphism (G,G') f /\ group_epimorphism (G,G') f <=>
        group_isomorphism (G,G') f`,
  REWRITE_TAC[GROUP_ISOMORPHISM; group_monomorphism; group_epimorphism] THEN
  MESON_TAC[]);;

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

let ISOMORPHIC_GROUP_CARD_EQ = prove
 (`!(G:A group) (H:B group).
        G isomorphic_group H ==> group_carrier G =_c group_carrier H`,
  REWRITE_TAC[isomorphic_group; GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[eq_c; group_monomorphism; group_epimorphism] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

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

let SUBGROUP_GENERATED_SETOP = prove
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
(* Right and left cosets.                                                    *)
(* ------------------------------------------------------------------------- *)

let right_coset = new_definition
 `right_coset G h x = group_setmul G h {x}`;;

let left_coset = new_definition
 `left_coset G x h = group_setmul G {x} h`;;

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

let RIGHT_COSET_OPPOSITE_GROUP = prove
 (`!G h x:A. right_coset G h x = left_coset (opposite_group G) x h`,
  REWRITE_TAC[left_coset; right_coset; OPPOSITE_GROUP_SETMUL]);;

let LEFT_COSET_OPPOSITE_GROUP = prove
 (`!G h x:A. left_coset G x h = right_coset (opposite_group G) h x`,
  REWRITE_TAC[left_coset; right_coset; OPPOSITE_GROUP_SETMUL]);;

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

let LAGRANGE_THEOREM_RIGHT = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {right_coset G h x |x| x IN group_carrier G} * CARD h =
            CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(h:A->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; subgroup_of]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [SYM(MATCH_MP UNIONS_RIGHT_COSETS th)]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNIONS o rand o snd) THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  ASM_SIMP_TAC[GSYM DISJOINT; DISJOINT_RIGHT_COSETS] THEN
  REWRITE_TAC[right_coset; group_setmul; SET_RULE
   `{f x y | x IN s /\ y IN {a}} = IMAGE (\x. f x a) s`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM NSUM_CONST; FINITE_IMAGE] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
  ASM_SIMP_TAC[IMP_CONJ; GROUP_MUL_RCANCEL]);;

let LAGRANGE_THEOREM_LEFT = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> CARD {left_coset G x h |x| x IN group_carrier G} * CARD h =
            CARD(group_carrier G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEFT_COSET_OPPOSITE_GROUP] THEN
  ONCE_REWRITE_TAC[SYM(CONJUNCT1(SPEC_ALL OPPOSITE_GROUP))] THEN
  MATCH_MP_TAC LAGRANGE_THEOREM_RIGHT THEN
  ASM_REWRITE_TAC[SUBGROUP_OF_OPPOSITE_GROUP; OPPOSITE_GROUP]);;

let LAGRANGE_THEOREM = prove
 (`!G h:A->bool.
        FINITE(group_carrier G) /\ h subgroup_of G
        ==> (CARD h) divides CARD(group_carrier G)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP LAGRANGE_THEOREM_RIGHT) THEN
  NUMBER_TAC);;

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

let NORMAL_SUBGROUP_CONJUGATE = prove
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

let TRIVIAL_QUOTIENT_GROUP_SELF = prove
 (`!G:A group. trivial_group(quotient_group G (group_carrier G))`,
  SIMP_TAC[trivial_group; QUOTIENT_GROUP; CARRIER_NORMAL_SUBGROUP_OF] THEN
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `~(s = {}) /\ (!x. x IN s ==> f x = a) ==> {f x | x IN s} = {a}`) THEN
  REWRITE_TAC[RIGHT_COSET_CARRIER; GROUP_CARRIER_NONEMPTY]);;

let QUOTIENT_GROUP_TRIVIAL = prove
 (`!G:A group. quotient_group G {group_id G} isomorphic_group G`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `right_coset G {group_id G:A}` THEN
  SIMP_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM; group_monomorphism;
           GROUP_EPIMORPHISM_RIGHT_COSET; GROUP_HOMOMORPHISM_RIGHT_COSET;
           TRIVIAL_SUBGROUP_OF; TRIVIAL_NORMAL_SUBGROUP_OF;
           RIGHT_COSET_EQ; IMP_CONJ; IN_SING; GROUP_DIV_EQ_ID]);;

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

let SUBGROUP_OF_HOMOMORPHIC_IMAGE = prove
 (`!G G' (f:A->B).
        group_homomorphism (G,G') f /\ h subgroup_of G
        ==> IMAGE f h subgroup_of G'`,
  REWRITE_TAC[group_homomorphism; subgroup_of] THEN SET_TAC[]);;

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
  SIMP_TAC[NORMAL_SUBGROUP_CONJUGATE; SUBGROUP_GROUP_KERNEL] THEN
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

let QUOTIENT_GROUP_UNIVERSAL = prove
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
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] QUOTIENT_GROUP_UNIVERSAL)) THEN
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

let GROUP_ZPOW_EQ = prove
 (`!G (x:A) m n.
        x IN group_carrier G
        ==> (group_zpow G x m = group_zpow G x n <=>
             &(group_element_order G x) divides n - m)`,
  SIMP_TAC[GSYM GROUP_ZPOW_EQ_ID; GROUP_ZPOW_SUB] THEN
  SIMP_TAC[GROUP_DIV_EQ_ID; GROUP_ZPOW] THEN MESON_TAC[]);;

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

let GROUP_ELEMENT_ORDER_ID = prove
 (`!G:A group. group_element_order G (group_id G) = 1`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_1; GROUP_ID]);;

let GROUP_ELEMENT_ORDER_INV = prove
 (`!G x:A.
        x IN group_carrier G
        ==> group_element_order G (group_inv G x) = group_element_order G x`,
  SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE; GROUP_INV; GSYM GROUP_INV_POW] THEN
  SIMP_TAC[GROUP_INV_EQ_ID; GROUP_POW; GROUP_POW_EQ_ID]);;

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

let GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) G H x.
        group_monomorphism(G,H) f /\ x IN group_carrier G
        ==> group_element_order H (f x) = group_element_order G x`,
  REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_element_order] THEN
  ASM_SIMP_TAC[GSYM GROUP_HOMOMORPHISM_POW; GROUP_POW]);;

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

let FINITE_CYCLIC_SUBGROUP_EXPLICIT = prove
 (`!G x:A.
        FINITE(group_carrier(subgroup_generated G {x})) /\ x IN group_carrier G
        ==> group_carrier(subgroup_generated G {x}) =
            {group_pow G x n |n| n < group_element_order G x}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV; GSYM GROUP_NPOW] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[GROUP_ZPOW_EQ]; MESON_TAC[]] THEN
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
  ASM_SIMP_TAC[GSYM GROUP_NPOW; GROUP_ZPOW_EQ; INT_OF_NUM_SUB] THEN
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

let GROUP_HOMOMORPHISM_GROUP_MUL_REV = prove
 (`!G g h:A->bool.
        group_homomorphism
          (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
          (\(x,y). group_mul G x y)
        ==> !x y. x IN group_carrier G /\ y IN group_carrier G /\
                  x IN g /\ y IN h
                  ==> group_mul G x y = group_mul G y x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A,y:A`; `x:A,y:A`] o el 3 o CONJUNCTS o
    REWRITE_RULE[group_homomorphism]) THEN
  REWRITE_TAC[PROD_GROUP; IN_CROSS] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET]
     SUBGROUP_GENERATED_SUBSET_CARRIER) THEN
    ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC[GROUP_MUL_LCANCEL; GSYM GROUP_MUL_ASSOC; GROUP_MUL] THEN
    ASM_SIMP_TAC[GROUP_MUL_RCANCEL; GROUP_MUL_ASSOC; GROUP_MUL]]);;

let GROUP_HOMOMORPHISM_GROUP_MUL_EQ = prove
 (`!G g h:A->bool.
        g subgroup_of G /\ h subgroup_of G
        ==> (group_homomorphism
              (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
              (\(x,y). group_mul G x y) <=>
              !x y. x IN g /\ y IN h ==> group_mul G x y = group_mul G y x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_GROUP_MUL_REV) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PROD_GROUP; FORALL_PAIR_THM; IN_CROSS] THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
  REWRITE_TAC[SUBGROUP_GENERATED] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subgroup_of; SUBSET]) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [GROUP_MUL_LCANCEL; GSYM GROUP_MUL_ASSOC; GROUP_MUL] THEN
  ASM_SIMP_TAC[GROUP_MUL_RCANCEL; GROUP_MUL_ASSOC; GROUP_MUL] THEN
  ASM_MESON_TAC[]);;

let GROUP_HOMOMORPHISM_GROUP_MUL = prove
 (`!G g h:A->bool.
        abelian_group G /\ g subgroup_of G /\ h subgroup_of G
        ==> group_homomorphism
              (prod_group (subgroup_generated G g) (subgroup_generated G h),G)
              (\(x,y). group_mul G x y)`,
  SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_MUL_EQ] THEN
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

let ISOMORPHIC_GROUP_INFINITE_CYCLIC_GROUPS = prove
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

let INTEGER_MOD_GROUP_1 = prove
 (`!n. &1 IN group_carrier(integer_mod_group n) <=> ~(n = 1)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_group; INTEGER_GROUP; IN_UNIV] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[LE_1; INTEGER_MOD_GROUP; IN_ELIM_THM] THEN
    REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

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

let INTEGER_MOD_SUBGROUP_GENERATED_BY_1 = prove
 (`!n. subgroup_generated (integer_mod_group n) {&1} =
       integer_mod_group n`,
  GEN_TAC THEN REWRITE_TAC[GROUPS_EQ; CONJUNCT2 SUBGROUP_GENERATED] THEN
  ASM_CASES_TAC `n = 1` THENL
   [MP_TAC(SPEC `1` TRIVIAL_INTEGER_MOD_GROUP) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o SPEC `{&1:int}` o
     MATCH_MP TRIVIAL_GROUP_SUBGROUP_GENERATED) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[trivial_group]) THEN
    ASM_REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED];
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; INTEGER_MOD_GROUP_1] THEN
    REWRITE_TAC[GROUP_ZPOW_INTEGER_MOD_GROUP; INT_MUL_RID] THEN
    ASM_CASES_TAC `n = 0` THEN
    ASM_SIMP_TAC[INTEGER_MOD_GROUP; INT_REM_0; IN_GSPEC; LE_1] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. f x IN s) /\ (!x. x IN s ==> f x = x)
     ==> {f x | x IN UNIV} = s`) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; INT_DIVISION; INT_OF_NUM_EQ;
                 INT_LT_REM; INT_OF_NUM_LT; LE_1; INT_REM_LT]]);;

let CYCLIC_GROUP_INTEGER_MOD_GROUP = prove
 (`!n. cyclic_group(integer_mod_group n)`,
  ONCE_REWRITE_TAC[GSYM INTEGER_MOD_SUBGROUP_GENERATED_BY_1] THEN
  REWRITE_TAC[CYCLIC_GROUP_GENERATED]);;

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
  ASM_SIMP_TAC[GROUP_ZPOW_EQ_ID; GSYM GROUP_ZPOW_ADD; GROUP_ZPOW_EQ] THEN
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

let SHORT_EXACT_SEQUENCE = prove
 (`!(f:A->B) (g:B->C) A B C.
        short_exact_sequence(A,B,C) (f,g) <=>
        group_monomorphism (A,B) f /\
        group_epimorphism (B,C) g /\
        group_image (A,B) f = group_kernel (B,C) g`,
  REWRITE_TAC[short_exact_sequence; group_monomorphism;
              group_exactness; group_epimorphism] THEN
  MESON_TAC[]);;

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
