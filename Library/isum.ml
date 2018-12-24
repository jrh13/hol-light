(* ========================================================================= *)
(* Define integer sums, with most theorems derived automatically.            *)
(* ========================================================================= *)

let isum = new_definition
 `isum = iterate((+):int->int->int)`;;

let NEUTRAL_INT_ADD = prove
 (`neutral((+):int->int->int) = &0`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[INT_ADD_LID; INT_ADD_RID]);;

let MONOIDAL_INT_ADD = prove
 (`monoidal((+):int->int->int)`,
  REWRITE_TAC[monoidal; NEUTRAL_INT_ADD] THEN INT_ARITH_TAC);;

let ISUM_SUPPORT = prove
 (`!f s. isum (support (+) f s) f = isum s f`,
  REWRITE_TAC[isum; ITERATE_SUPPORT]);;

let int_isum = prove
 (`!f:A->int s. real_of_int(isum s f) = sum s (\x. real_of_int(f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sum; isum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN
   `support(+) (\x:A. real_of_int(f x)) s = support(+) f s`
  SUBST1_TAC THENL
   [REWRITE_TAC[support; NEUTRAL_REAL_ADD; NEUTRAL_INT_ADD] THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NEUTRAL_REAL_ADD; NEUTRAL_INT_ADD; int_of_num_th] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`support(+) (f:A->int) s`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_INT_ADD; MONOIDAL_REAL_ADD] THEN
  SIMP_TAC[NEUTRAL_INT_ADD; NEUTRAL_REAL_ADD; int_of_num_th; int_add_th]);;

(* ------------------------------------------------------------------------- *)
(* Generalize INT_OF_REAL_THM for most common sum patterns.                  *)
(* ------------------------------------------------------------------------- *)

let INT_OF_REAL_THM =
  let dest = `real_of_int`
  and real_ty = `:real`
  and int_ty = `:int`
  and cond_th = prove
   (`real_of_int(if b then x else y) =
       if b then real_of_int x else real_of_int y`,
    COND_CASES_TAC THEN REWRITE_TAC[])
  and compose_th = prove
   (`(\x. real_of_int((f o g) x)) = (\x. real_of_int(f x)) o g`,
    REWRITE_TAC[o_DEF]) in
  let thlist = map GSYM
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th;
    int_sub_th; int_abs_th; int_max_th; int_min_th; int_pow_th;
    int_isum; GSYM BETA_THM; GSYM ETA_AX; compose_th; cond_th] in
  let REW_RULE = GEN_REWRITE_RULE REDEPTH_CONV thlist in
  let is_fun_into_real ty =
    try match dest_type ty with
          "fun",[s;t] when t = real_ty -> mk_fun_ty s int_ty
        | "real",[] -> int_ty
        | _ -> failwith ""
    with Failure _ -> ty in
  let int_of_real_ty ty =
    try match dest_type ty with
          "real",[] -> int_ty
        | "fun",[s;t] when t = real_ty -> mk_fun_ty s int_ty
        | _ -> ty
    with Failure _ -> ty in
  let int_tm_of_real_var v =
     let s,ty = dest_var v in
     let tys,rty = splitlist dest_fun_ty ty in
     if rty <> real_ty then v else
     let ity = itlist mk_fun_ty tys int_ty in
     let vs = map genvar tys in
     list_mk_abs(vs,mk_comb(dest,list_mk_comb(mk_var(s,ity),vs))) in
  let int_of_real_var v =
     let s,ty = dest_var v in
     let tys,rty = splitlist dest_fun_ty ty in
     if rty <> real_ty then v else
     let ity = itlist mk_fun_ty tys int_ty in
     mk_var(s,ity) in
  let INT_OF_REAL_THM1 th =
    let newavs = subtract (frees (concl th)) (freesl (hyp th)) in
    let avs,bod = strip_forall(concl th) in
    let allavs = newavs@avs in
    let avs' = map int_tm_of_real_var allavs in
    let avs'' = map int_of_real_var avs in
    GENL avs'' (REW_RULE(SPECL avs' (GENL newavs th))) in
  let rec INT_OF_REAL_THM th =
    if is_conj(concl th) then CONJ (INT_OF_REAL_THM1 (CONJUNCT1 th))
                                   (INT_OF_REAL_THM1 (CONJUNCT2 th))
    else INT_OF_REAL_THM1 th in
  INT_OF_REAL_THM;;

(* ------------------------------------------------------------------------- *)
(* Apply it in all the cases where it works.                                 *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_ISUM = INT_OF_REAL_THM CARD_EQ_SUM;;
let INT_SUB_POW = INT_OF_REAL_THM REAL_SUB_POW;;
let ISUM_0 = INT_OF_REAL_THM SUM_0;;
let ISUM_ABS = INT_OF_REAL_THM SUM_ABS;;
let ISUM_ABS_BOUND = INT_OF_REAL_THM SUM_ABS_BOUND;;
let ISUM_ABS_LE = INT_OF_REAL_THM SUM_ABS_LE;;
let ISUM_ABS_NUMSEG = INT_OF_REAL_THM SUM_ABS_NUMSEG;;
let ISUM_ADD = INT_OF_REAL_THM SUM_ADD;;
let ISUM_ADD_NUMSEG = INT_OF_REAL_THM SUM_ADD_NUMSEG;;
let ISUM_ADD_SPLIT = INT_OF_REAL_THM SUM_ADD_SPLIT;;
let ISUM_BIJECTION = INT_OF_REAL_THM SUM_BIJECTION;;
let ISUM_BOUND = INT_OF_REAL_THM SUM_BOUND;;
let ISUM_BOUND_LT = INT_OF_REAL_THM SUM_BOUND_LT;;
let ISUM_BOUND_LT_ALL = INT_OF_REAL_THM SUM_BOUND_LT_ALL;;
let ISUM_CASES = INT_OF_REAL_THM SUM_CASES;;
let ISUM_CLAUSES = INT_OF_REAL_THM SUM_CLAUSES;;
let ISUM_CLAUSES_LEFT = INT_OF_REAL_THM SUM_CLAUSES_LEFT;;
let ISUM_CLAUSES_NUMSEG = INT_OF_REAL_THM SUM_CLAUSES_NUMSEG;;
let ISUM_CLAUSES_RIGHT = INT_OF_REAL_THM SUM_CLAUSES_RIGHT;;
let ISUM_COMBINE_L = INT_OF_REAL_THM SUM_COMBINE_L;;
let ISUM_COMBINE_R = INT_OF_REAL_THM SUM_COMBINE_R;;
let ISUM_CONST = INT_OF_REAL_THM SUM_CONST;;
let ISUM_CONST_NUMSEG = INT_OF_REAL_THM SUM_CONST_NUMSEG;;
let ISUM_DELETE = INT_OF_REAL_THM SUM_DELETE;;
let ISUM_DELETE_CASES = INT_OF_REAL_THM SUM_DELETE_CASES;;
let ISUM_DELTA = INT_OF_REAL_THM SUM_DELTA;;
let ISUM_DIFF = INT_OF_REAL_THM SUM_DIFF;;
let ISUM_DIFFS = INT_OF_REAL_THM SUM_DIFFS;;
let ISUM_EQ = INT_OF_REAL_THM SUM_EQ;;
let ISUM_EQ_0 = INT_OF_REAL_THM SUM_EQ_0;;
let ISUM_EQ_0_NUMSEG = INT_OF_REAL_THM SUM_EQ_0_NUMSEG;;
let ISUM_EQ_GENERAL = INT_OF_REAL_THM SUM_EQ_GENERAL;;
let ISUM_EQ_GENERAL_INVERSES = INT_OF_REAL_THM SUM_EQ_GENERAL_INVERSES;;
let ISUM_EQ_NUMSEG = INT_OF_REAL_THM SUM_EQ_NUMSEG;;
let ISUM_EQ_SUPERSET = INT_OF_REAL_THM SUM_EQ_SUPERSET;;
let ISUM_GROUP = INT_OF_REAL_THM SUM_GROUP;;
let ISUM_IMAGE = INT_OF_REAL_THM SUM_IMAGE;;
let ISUM_IMAGE_GEN = INT_OF_REAL_THM SUM_IMAGE_GEN;;
let ISUM_IMAGE_LE = INT_OF_REAL_THM SUM_IMAGE_LE;;
let ISUM_IMAGE_NONZERO = INT_OF_REAL_THM SUM_IMAGE_NONZERO;;
let ISUM_INCL_EXCL = INT_OF_REAL_THM SUM_INCL_EXCL;;
let ISUM_INJECTION = INT_OF_REAL_THM SUM_INJECTION;;
let ISUM_LE = INT_OF_REAL_THM SUM_LE;;
let ISUM_LE_INCLUDED = INT_OF_REAL_THM SUM_LE_INCLUDED;;
let ISUM_LE_NUMSEG = INT_OF_REAL_THM SUM_LE_NUMSEG;;
let ISUM_LMUL = INT_OF_REAL_THM SUM_LMUL;;
let ISUM_LT = INT_OF_REAL_THM SUM_LT;;
let ISUM_LT_ALL = INT_OF_REAL_THM SUM_LT_ALL;;
let ISUM_MULTICOUNT = INT_OF_REAL_THM SUM_MULTICOUNT;;
let ISUM_MULTICOUNT_GEN = INT_OF_REAL_THM SUM_MULTICOUNT_GEN;;
let ISUM_NEG = INT_OF_REAL_THM SUM_NEG;;
let ISUM_OFFSET = INT_OF_REAL_THM SUM_OFFSET;;
let ISUM_OFFSET_0 = INT_OF_REAL_THM SUM_OFFSET_0;;
let ISUM_PARTIAL_PRE = INT_OF_REAL_THM SUM_PARTIAL_PRE;;
let ISUM_PARTIAL_SUC = INT_OF_REAL_THM SUM_PARTIAL_SUC;;
let ISUM_POS_BOUND = INT_OF_REAL_THM SUM_POS_BOUND;;
let ISUM_POS_EQ_0 = INT_OF_REAL_THM SUM_POS_EQ_0;;
let ISUM_POS_EQ_0_NUMSEG = INT_OF_REAL_THM SUM_POS_EQ_0_NUMSEG;;
let ISUM_POS_LE = INT_OF_REAL_THM SUM_POS_LE;;
let ISUM_POS_LE_NUMSEG = INT_OF_REAL_THM SUM_POS_LE_NUMSEG;;
let ISUM_RESTRICT = INT_OF_REAL_THM SUM_RESTRICT;;
let ISUM_RESTRICT_SET = INT_OF_REAL_THM SUM_RESTRICT_SET;;
let ISUM_RMUL = INT_OF_REAL_THM SUM_RMUL;;
let ISUM_SING = INT_OF_REAL_THM SUM_SING;;
let ISUM_SING_NUMSEG = INT_OF_REAL_THM SUM_SING_NUMSEG;;
let ISUM_SUB = INT_OF_REAL_THM SUM_SUB;;
let ISUM_SUBSET = INT_OF_REAL_THM SUM_SUBSET;;
let ISUM_SUBSET_SIMPLE = INT_OF_REAL_THM SUM_SUBSET_SIMPLE;;
let ISUM_SUB_NUMSEG = INT_OF_REAL_THM SUM_SUB_NUMSEG;;
let ISUM_ISUM_RESTRICT = INT_OF_REAL_THM SUM_SUM_RESTRICT;;
let ISUM_SUPERSET = INT_OF_REAL_THM SUM_SUPERSET;;
let ISUM_SWAP = INT_OF_REAL_THM SUM_SWAP;;
let ISUM_SWAP_NUMSEG = INT_OF_REAL_THM SUM_SWAP_NUMSEG;;
let ISUM_TRIV_NUMSEG = INT_OF_REAL_THM SUM_TRIV_NUMSEG;;
let ISUM_UNION = INT_OF_REAL_THM SUM_UNION;;
let ISUM_UNIONS_NONZERO = INT_OF_REAL_THM SUM_UNIONS_NONZERO;;
let ISUM_UNION_EQ = INT_OF_REAL_THM SUM_UNION_EQ;;
let ISUM_UNION_LZERO = INT_OF_REAL_THM SUM_UNION_LZERO;;
let ISUM_UNION_NONZERO = INT_OF_REAL_THM SUM_UNION_NONZERO;;
let ISUM_UNION_RZERO = INT_OF_REAL_THM SUM_UNION_RZERO;;
let ISUM_ZERO_EXISTS = INT_OF_REAL_THM SUM_ZERO_EXISTS;;
let REAL_OF_NUM_ISUM = INT_OF_REAL_THM REAL_OF_NUM_SUM;;
let REAL_OF_NUM_ISUM_NUMSEG = INT_OF_REAL_THM REAL_OF_NUM_SUM_NUMSEG;;

(* ------------------------------------------------------------------------- *)
(* Manually derive the few cases where it doesn't.                           *)
(*                                                                           *)
(* Note that SUM_BOUND_GEN and SUM_BOUND_LT_GEN don't seem to have immediate *)
(* analogs over the integers since they involve division.                    *)
(*                                                                           *)
(* Should really roll ADMISSIBLE_ISUM into "define" as well.                 *)
(* ------------------------------------------------------------------------- *)

let ISUM_ISUM_PRODUCT = prove
 (`!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> isum s (\i. isum (t i) (x i)) =
            isum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  REWRITE_TAC[isum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_INT_ADD]);;

let ADMISSIBLE_ISUM = prove
 (`!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
   ==> admissible(<<) p s (\f x. isum(a(x)..b(x)) (h f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ISUM_EQ_NUMSEG THEN ASM_MESON_TAC[]);;

let INT_SUB_POW_L1 = prove
 (`!x n. 1 <= n ==> &1 - x pow n = (&1 - x) * isum (0..n - 1) (\i. x pow i)`,
  SIMP_TAC[INT_OF_REAL_THM REAL_SUB_POW_L1; ETA_AX]);;

let INT_SUB_POW_R1 = prove
 (`!x n. 1 <= n ==> x pow n - &1 = (x - &1) * isum (0..n - 1) (\i. x pow i)`,
  SIMP_TAC[INT_OF_REAL_THM REAL_SUB_POW_R1; ETA_AX]);;

let ISUM_UNIV = prove
 (`!f:A->int s. support (+) f (:A) SUBSET s ==> isum s f = isum (:A) f`,
  REWRITE_TAC[isum] THEN MATCH_MP_TAC ITERATE_UNIV THEN
  REWRITE_TAC[MONOIDAL_INT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Expand "isum (m..n) f" where m and n are numerals.                        *)
(* ------------------------------------------------------------------------- *)

let EXPAND_ISUM_CONV =
  let [pth_0; pth_1; pth_2] = (CONJUNCTS o prove)
   (`(n < m ==> isum(m..n) f = &0) /\
     isum(m..m) f = f m /\
     (m <= n ==> isum (m..n) f = f m + isum (m + 1..n) f)`,
    REWRITE_TAC[ISUM_CLAUSES_LEFT; ISUM_SING_NUMSEG; ISUM_TRIV_NUMSEG])
  and ns_tm = `..` and f_tm = `f:num->int`
  and m_tm = `m:num` and n_tm = `n:num` in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s && fst(dest_const s) = "isum")
    then failwith "EXPAND_ISUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    if n < m then
      let th1 = INST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_0 in
      MP th1 (EQT_ELIM(NUM_LT_CONV(lhand(concl th1))))
    else if n = m then CONV_RULE (RAND_CONV(TRY_CONV BETA_CONV))
                                 (INST [ftm,f_tm; mtm,m_tm] pth_1)
    else
      let th1 = INST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_2 in
      let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
      CONV_RULE (RAND_CONV(COMB2_CONV (RAND_CONV(TRY_CONV BETA_CONV))
       (LAND_CONV(LAND_CONV NUM_ADD_CONV) THENC conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Extend the congruences.                                                   *)
(* ------------------------------------------------------------------------- *)

let th = prove
 (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> isum s (\i. f(i)) = isum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> isum(a..b) (\i. f(i)) = isum(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> isum {y | p y} (\i. f(i)) = isum {y | p y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;
