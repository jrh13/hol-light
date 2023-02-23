(* ========================================================================== *)
(* A Verified Compute Primitive for Candle.                                   *)
(*                                                                            *)
(* This theory defines the types and functions needed for the kernel built-in *)
(* call-by-value interpreter of compute expressions (cexp). compute expects   *)
(* a certain set of characteristic equations for :num arithmetic as well as   *)
(* auxiliary constants (e.g., COND for if-then-else) occurring in the         *)
(* characterizing equations.                                                  *)
(* ========================================================================== *)

needs "define.ml";;

(* -------------------------------------------------------------------------- *)
(* Definition of cexps (compute expressions) and operations on cexps.         *)
(* -------------------------------------------------------------------------- *)

let cval_INDUCT, cval_RECURSION = define_type
  "cval = Cexp_num num | Cexp_pair cval cval";;

let cexp_add_def = define
  `(Cexp_add (Cexp_num m) (Cexp_num n) = Cexp_num (m + n)) /\
   (Cexp_add (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num m) /\
   (Cexp_add (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num n) /\
   (Cexp_add (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num 0)`;;

let cexp_sub_def = define
  `(Cexp_sub (Cexp_num m) (Cexp_num n) = Cexp_num (m - n)) /\
   (Cexp_sub (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num m) /\
   (Cexp_sub (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num 0) /\
   (Cexp_sub (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num 0)`;;

let cexp_mul_def = define
  `(Cexp_mul (Cexp_num m) (Cexp_num n) = Cexp_num (m * n)) /\
   (Cexp_mul (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num 0) /\
   (Cexp_mul (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num 0) /\
   (Cexp_mul (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num 0)`;;

let cexp_div_def = define
  `(Cexp_div (Cexp_num m) (Cexp_num n) = Cexp_num (m DIV n)) /\
   (Cexp_div (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num 0) /\
   (Cexp_div (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num 0) /\
   (Cexp_div (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num 0)`;;

let cexp_mod_def = define
  `(Cexp_mod (Cexp_num m) (Cexp_num n) = Cexp_num (m MOD n)) /\
   (Cexp_mod (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num m) /\
   (Cexp_mod (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num 0) /\
   (Cexp_mod (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num 0)`;;

let cexp_less_def = define
  `(Cexp_less (Cexp_num m) (Cexp_num n) =
     Cexp_num (if m < n then SUC 0 else 0)) /\
   (Cexp_less (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num 0) /\
   (Cexp_less (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num 0) /\
   (Cexp_less (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num 0)`;;

let cexp_if_def = define
  `(Cexp_if (Cexp_num (SUC m)) (p1: cval) (q1: cval) = p1) /\
   (Cexp_if (Cexp_pair p2 q2) p1 q1 = p1) /\
   (Cexp_if (Cexp_num 0) p1 q1 = q1)`;;

let cexp_fst_def = define
  `(Cexp_fst (Cexp_pair p1 q1) = p1) /\
   (Cexp_fst (Cexp_num m) = Cexp_num 0)`;;

let cexp_snd_def = define
  `(Cexp_snd (Cexp_pair p1 q1) = q1) /\
   (Cexp_snd (Cexp_num m) = Cexp_num 0)`;;

let cexp_ispair_def = define
  `(Cexp_ispair (Cexp_pair p1 q1) = Cexp_num (SUC 0)) /\
   (Cexp_ispair (Cexp_num m) = Cexp_num 0)`;;

let cexp_eq_def = define
  `Cexp_eq (p1: cval) q1 = Cexp_num (if p1 = q1 then SUC 0 else 0)`;;

(* -------------------------------------------------------------------------- *)
(* Prepare the list of characteristic equations in the way compute wants it.  *)
(* The theorems need be exactly those below (if they are only alpha equiv.    *)
(* then compute_init will crash with an unhelpful error). They also need to   *)
(* be fed to compute_init in exactly this order.                              *)
(* -------------------------------------------------------------------------- *)

let COMPUTE_INIT_THMS =
  let [COND_TRUE; COND_FALSE] = (CONJUNCTS o prove) (
    `COND T (m:num) (n:num) = m /\
     COND F m n = n`,
    REWRITE_TAC []) in
  let [IF_TRUE; IF_FALSE] = (CONJUNCTS o prove) (
    `COND T (x:bool) (y:bool) = x /\
     COND F x y = y`,
    REWRITE_TAC []) in
  let NUMERAL_EQ = SPEC_ALL NUMERAL in
  let BIT0_EQ = SPEC_ALL BIT0 in
  let BIT1_EQ = SPEC_ALL BIT1 in
  let [ADD_EQ1; ADD_EQ2] = (CONJUNCTS o prove) (
    `0 + n = n /\
     (SUC m) + n = SUC (m + n)`,
    REWRITE_TAC [ADD]) in
  let [SUB_EQ1; SUB_EQ2; SUB_EQ3] = (CONJUNCTS o prove) (
     `0 - n = 0 /\
      m - 0 = m /\
      (SUC m) - (SUC n) = m - n`,
     REWRITE_TAC [SUB_0; SUB_PRESUC; SUB_SUC]) in
  let [MUL_EQ1; MUL_EQ2] = (CONJUNCTS o prove) (
    `0 * n = 0 /\
     (SUC m) * n = n + (m * n)`,
    REWRITE_TAC [MULT_CLAUSES; ADD_SYM]) in
  let SUB_LEMMA = prove (
    `n <= m ==> (m = n + k <=> m - n = k)`,
    STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [ADD_SUB; ADD_SUB2] THEN
    POP_ASSUM (SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [LE_EXISTS]) THEN
    POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [EQ_ADD_LCANCEL; ADD_SYM; ADD_SUB]) in
  let DIV_RECURSIVE = prove (
    `m DIV n = if n = 0 then 0 else if m < n then 0 else SUC ((m - n) DIV n)`,
    ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC [DIV_ZERO] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM LT_NZ]) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [DIV_LT] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT; LE_LT]) THEN
    POP_ASSUM DISJ_CASES_TAC THEN
    REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
    ASM_SIMP_TAC [SUB_REFL; DIV_0; GSYM ONE; DIV_REFL; GSYM LT_NZ] THEN
    MATCH_MP_TAC DIV_UNIQ THEN
    ASM_SIMP_TAC [RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB] THEN
    EXISTS_TAC `(m - n) MOD n` THEN
    ASM_SIMP_TAC [MOD_LT_EQ_LT; GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    ASM_SIMP_TAC [GSYM ADD_ASSOC; LT_IMP_LE; SUB_LEMMA; DIVISION_SIMP;
                  ADD_SYM]) in
  let MOD_RECURSIVE = prove (
    `m MOD n = if n = 0 then m else if m < n then m else (m - n) MOD n`,
    ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC [MOD_ZERO] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM LT_NZ]) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [MOD_LT] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN
    MATCH_MP_TAC MOD_EQ THEN
    EXISTS_TAC `1` THEN ASM_SIMP_TAC [MULT_CLAUSES; SUB_ADD]) in
  let [LESS_EQ1; LESS_EQ2; LESS_EQ3] = (CONJUNCTS o prove) (
    `(m < 0 <=> F) /\
    (0 < SUC n <=> T) /\
    (SUC m < SUC n <=> (m < n))`,
    REWRITE_TAC [LT_SUC; LT_0; LT]) in
  let [NUMEQ1; NUMEQ2; NUMEQ3; NUMEQ4] = (CONJUNCTS o prove) (
    `(0 = 0 <=> T) /\
    (0 = SUC n <=> F) /\
    (SUC m = 0 <=> F) /\
    (SUC m = SUC n <=> m = n)`,
    REWRITE_TAC [NOT_SUC; SUC_INJ]) in
  let [PAIR_EQ1; PAIR_EQ2; PAIR_EQ3; PAIR_EQ4] = (CONJUNCTS o prove) (
    `(Cexp_pair p1 q1 = Cexp_pair p2 q2 <=> if p1 = p2 then q1 = q2 else F) /\
    (Cexp_num m = Cexp_num n <=> m = n) /\
    (Cexp_num m = Cexp_pair p1 q1 <=> F) /\
    (Cexp_pair p1 q1 = Cexp_num n <=> F)`,
    REWRITE_TAC [injectivity "cval"; distinctness "cval"] THEN
    COND_CASES_TAC THEN REWRITE_TAC []) in
  let LET_EQ = prove (
    `LET (f:cval->cval) (p1:cval) = f p1`,
    REWRITE_TAC [LET_DEF]) in
  [COND_TRUE; COND_FALSE; IF_TRUE; IF_FALSE; NUMERAL_EQ; BIT0_EQ; BIT1_EQ;
   ADD_EQ1; ADD_EQ2; SUB_EQ1; SUB_EQ2; SUB_EQ3; MUL_EQ1; MUL_EQ2; DIV_RECURSIVE;
   MOD_RECURSIVE; LESS_EQ1; LESS_EQ2; LESS_EQ3; NUMEQ1; NUMEQ2; NUMEQ3; NUMEQ4;
  ] @
  CONJUNCTS cexp_add_def @
  CONJUNCTS cexp_sub_def @
  CONJUNCTS cexp_mul_def @
  CONJUNCTS cexp_div_def @
  CONJUNCTS cexp_mod_def @
  CONJUNCTS cexp_less_def @
  CONJUNCTS cexp_if_def @
  CONJUNCTS cexp_fst_def @
  CONJUNCTS cexp_snd_def @
  CONJUNCTS cexp_ispair_def @
  [cexp_eq_def; PAIR_EQ1; PAIR_EQ2; PAIR_EQ3; PAIR_EQ4; LET_EQ]
;;

(* -------------------------------------------------------------------------- *)
(* compute takes a list defn_eqs of _compute equations_ and a term tm of type *)
(* :cval, and returns a theorem |- tm = tm' where tm' is a fully reduced      *)
(* version of tm.                                                             *)
(*                                                                            *)
(* A _compute equation_ is an equation c x1 ... xN = e, where c is a constant,*)
(* and x1 ... xN are variables of type :cval, and e is closed under x1 ... xN.*)
(*                                                                            *)
(* The equations in defn_eqs and the term tm may only contain constants that  *)
(* have compute equations associated with them in the list.                   *)
(* -------------------------------------------------------------------------- *)

let compute defn_eqs tm =
  Kernel.compute (COMPUTE_INIT_THMS,
                  map (REWRITE_CONV [LET_END_DEF]) defn_eqs) tm;;

(* -------------------------------------------------------------------------- *)
(* We'll install some overloads to make it easier to build cexps.             *)
(* -------------------------------------------------------------------------- *)

make_overloadable "lessc"   `:A->A->A`;;
make_overloadable "divc"    `:A->A->A`;;
make_overloadable "modc"    `:A->A->A`;;
make_overloadable "ifc"     `:A->A->A->A`;;
make_overloadable "fstc"    `:A->A`;;
make_overloadable "ispairc" `:A->A`;;
make_overloadable "sndc"    `:A->A`;;
make_overloadable "numc"    `:num->A`;;
make_overloadable "pairc"   `:A->A->A`;;
make_overloadable "eqc"     `:A->A->A`;;

parse_as_infix("lessc",(12,"right"));;
parse_as_infix("divc",(22,"left"));;
parse_as_infix("modc",(22,"left"));;
parse_as_infix("eqc",(12,"right"));;

do_list overload_interface
 ["+",`Cexp_add`;
  "-",`Cexp_sub`;
  "*",`Cexp_mul`;
  "lessc",`Cexp_less`;
  "divc",`Cexp_div`;
  "modc",`Cexp_mod`;
  "ifc", `Cexp_if`;
  "fstc", `Cexp_fst`;
  "sndc", `Cexp_snd`;
  "numc", `Cexp_num`;
  "ispairc", `Cexp_ispair`;
  "pairc", `Cexp_pair`;
  "eqc", `Cexp_eq`;
  ];;

(* -------------------------------------------------------------------------- *)
(* Recursive definitions of cexps.                                            *)
(* -------------------------------------------------------------------------- *)

let cexp_if = prove (
  `Cexp_if n p q = if ~(n = numc 0) then p else q`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC [cexp_if_def; ONE] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:cval` (cases "cval")) THEN
  SIMP_TAC [injectivity "cval"; ONE] THEN
  STRUCT_CASES_TAC (SPEC `a:num` num_CASES) THEN
  REWRITE_TAC [NOT_SUC; SUC_INJ; cexp_if_def]);;

let cval_size_def = define
  `(cval_size (numc n) = 1) /\
   (cval_size (pairc p q) = 1 + cval_size p + cval_size q)`;;

let cval_sum_size_def = define
  `(cval_sum_size (numc n) = n) /\
   (cval_sum_size (pairc p q) = 1 + cval_sum_size p + cval_sum_size q)`;;
