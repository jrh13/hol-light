(* ========================================================================= *)
(* Simple universal variant of Bob Solovay's procedure for vector spaces.    *)
(* ========================================================================= *)

needs "Multivariate/misc.ml";;
needs "Multivariate/vectors.ml";;

(* ------------------------------------------------------------------------- *)
(* Initial simplification so we just use dot products between vectors.       *)
(* ------------------------------------------------------------------------- *)

let VECTOR_SUB_ELIM_THM = prove
 (`(--x = --(&1) % x) /\
   (x - y = x + --(&1) % y)`,
  VECTOR_ARITH_TAC);;

let NORM_ELIM_THM = prove
 (`!P t. P (norm t) = !x. &0 <= x /\ (x pow 2 = (t:real^N) dot t) ==> P x`,
  GEN_TAC THEN REWRITE_TAC[vector_norm] THEN
  MESON_TAC[DOT_POS_LE; SQRT_POW2; SQRT_UNIQUE;
            REAL_POW_2; REAL_POW2_ABS; REAL_ABS_POS]);;

let NORM_ELIM_CONV =
  let dest_norm tm =
    let nm,v = dest_comb tm in
    if fst(dest_const nm) <> "vector_norm" then failwith "dest_norm"
    else v in
  let is_norm = can dest_norm in
  fun tm ->
    let t = find_term (fun t -> is_norm t && free_in t tm) tm in
    let v = dest_norm t in
    let w = genvar(type_of t) in
    let th1 = ISPECL [mk_abs(w,subst[w,t] tm); v] NORM_ELIM_THM in
    CONV_RULE(COMB2_CONV (RAND_CONV BETA_CONV)
                         (BINDER_CONV(RAND_CONV BETA_CONV))) th1;;

let NORM_ELIM_TAC =
  CONV_TAC NORM_ELIM_CONV THEN GEN_TAC;;

let SOLOVAY_TAC =
  REWRITE_TAC[orthogonal; GSYM DOT_EQ_0] THEN
  REWRITE_TAC[VECTOR_EQ] THEN
  REWRITE_TAC[VECTOR_SUB_ELIM_THM] THEN
  REWRITE_TAC[NORM_EQ; NORM_LE; NORM_LT; real_gt; real_ge] THEN
  REPEAT NORM_ELIM_TAC THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL];;

(* ------------------------------------------------------------------------- *)
(* Iterative Gram-Schmidt type process.                                      *)
(* ------------------------------------------------------------------------- *)

let component = new_definition
  `component (b:real^N) x = (b dot x) / (b dot b)`;;

let COMPONENT_ORTHOGONAL = prove
 (`!b:real^N x. orthogonal b (x - (component b x) % b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b = vec 0 :real^N` THENL
   [ASM_REWRITE_TAC[orthogonal; DOT_LZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[orthogonal; component] THEN
  REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_SUB_REFL; REAL_DIV_RMUL; DOT_EQ_0]);;

let ORTHOGONAL_SUM_LEMMA = prove
 (`!cs vs.
       ALL (orthogonal x) vs /\ orthogonal x z /\ (LENGTH cs = LENGTH vs)
        ==> orthogonal x (ITLIST2 (\a v s. a % v + s) cs vs z)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; NOT_SUC; ITLIST2; LENGTH; ALL] THEN
  ASM_SIMP_TAC[ORTHOGONAL_CLAUSES; SUC_INJ]);;

let GRAM_SCHMIDT_LEMMA = prove
 (`!w:real^N vs. ?u as.
        ALL (orthogonal u) vs /\ (LENGTH as = LENGTH vs) /\
        (w = ITLIST2 (\a v s. a % v + s) as vs u)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC list_INDUCT THEN
  SIMP_TAC[ALL; LENGTH; ITLIST2; LENGTH_EQ_NIL] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN EXISTS_TAC `w:real^N` THEN
    EXISTS_TAC `[]:real list` THEN REWRITE_TAC[ITLIST2];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N`; `vs:(real^N)list`] THEN
  REWRITE_TAC[LENGTH_EQ_CONS] THEN DISCH_TAC THEN X_GEN_TAC `w:real^N` THEN
  FIRST_X_ASSUM(fun th ->
     MP_TAC(SPEC `w:real^N` th) THEN MP_TAC(SPEC `v:real^N` th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` (X_CHOOSE_THEN `cs:real list`
    (STRIP_ASSUME_TAC o GSYM))) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `as:real list`
    (STRIP_ASSUME_TAC o GSYM))) THEN
  MP_TAC(ISPECL [`z:real^N`; `u:real^N`] COMPONENT_ORTHOGONAL) THEN
  ABBREV_TAC `k = component z (u:real^N)` THEN
  ABBREV_TAC `x = u - k % z :real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`x:real^N`; `CONS k (MAP2 (\a c. a - k * c) as cs)`] THEN
  REWRITE_TAC[CONS_11; RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  SUBGOAL_THEN `ALL (orthogonal(x:real^N)) vs` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (orthogonal(z:real^N)) vs` THEN
    UNDISCH_TAC `ALL (orthogonal(u:real^N)) vs` THEN
    REWRITE_TAC[IMP_IMP; AND_ALL] THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[] THEN
    EXPAND_TAC "x" THEN SIMP_TAC[ORTHOGONAL_CLAUSES];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC ORTHOGONAL_SUM_LEMMA THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ORTHOGONAL_SYM];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[LENGTH_MAP2];
    ALL_TAC] THEN
  REWRITE_TAC[ITLIST2; VECTOR_ARITH `(a = b + c:real^N) = (c = a - b)`] THEN
  MAP_EVERY EXPAND_TAC ["v"; "w"; "x"] THEN
  UNDISCH_TAC `LENGTH(vs:(real^N)list) = LENGTH(cs:real list)` THEN
  UNDISCH_TAC `LENGTH(vs:(real^N)list) = LENGTH(as:real list)` THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MAP_EVERY (fun v -> SPEC_TAC(v,v))
   [`vs:(real^N)list`; `cs:real list`; `as:real list`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; NOT_SUC; ITLIST2; LENGTH; ALL; SUC_INJ; MAP2] THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence this is a simple equality.                                          *)
(* ------------------------------------------------------------------------- *)

let SOLOVAY_LEMMA = prove
 (`!P vs. (!w:real^N. P w vs) =
          (!as u. ALL (orthogonal u) vs /\ (LENGTH as = LENGTH vs)
                  ==> P (ITLIST2 (\a v s. a % v + s) as vs u) vs)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`w:real^N`; `vs:(real^N)list`] GRAM_SCHMIDT_LEMMA) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set up the specific instances to get rid of list stuff.                   *)
(* ------------------------------------------------------------------------- *)

let FORALL_LENGTH_CLAUSES = prove
 (`((!l. (LENGTH l = 0) ==> P l) = P []) /\
   ((!l. (LENGTH l = SUC n) ==> P l) =
         (!h t. (LENGTH t = n) ==> P (CONS h t)))`,
  MESON_TAC[LENGTH; LENGTH_EQ_NIL; NOT_SUC; LENGTH_EQ_CONS]);;

let ORTHOGONAL_SIMP_CLAUSES = prove
 (`orthogonal u x
   ==> (u dot x = &0) /\ (x dot u = &0) /\
       (u dot (a % x) = &0) /\ ((a % x) dot u = &0) /\
       (u dot (a % x + y) = u dot y) /\ ((a % x + y) dot u = y dot u) /\
       (u dot (y + a % x) = u dot y) /\ ((y + a % x) dot u = y dot u)`,
  SIMP_TAC[orthogonal; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [DOT_SYM] THEN
  SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID]);;

(* ------------------------------------------------------------------------- *)
(* A nicer proforma version.                                                 *)
(* ------------------------------------------------------------------------- *)

let ITLIST2_0_LEMMA = prove
 (`!u as vs. ITLIST2 (\a v s. a % v + s) as vs u =
             ITLIST2 (\a v s. a % v + s) as vs (vec 0) + u`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST2_DEF; VECTOR_ADD_LID] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_ASSOC]);;

let SOLOVAY_PROFORMA_EQ = prove
 (`(!w:real^N. P (MAP ((dot) w) (CONS w vs)) vs) =
   (!u. ALL (orthogonal u) vs
        ==> !as. (LENGTH as = LENGTH vs)
                 ==> P (CONS
                          ((ITLIST2 (\a v s. a % v + s) as vs (vec 0)) dot
                           (ITLIST2 (\a v s. a % v + s) as vs (vec 0)) +
                           u dot u)
                          (MAP ((dot)
                                (ITLIST2 (\a v s. a % v + s) as vs (vec 0)))
                               vs))
                 vs)`,
  MP_TAC(ISPEC `\w:real^N vs.  P (MAP ((dot) w) (CONS w vs)) vs :bool`
               SOLOVAY_LEMMA) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `u:real^N` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `as:(real)list` THEN REWRITE_TAC[IMP_IMP] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b = c)) ==> (a ==> b <=> a ==> c)`) THEN
  STRIP_TAC THEN REWRITE_TAC[MAP] THEN BINOP_TAC THEN
  REWRITE_TAC[CONS_11] THEN ONCE_REWRITE_TAC[ITLIST2_0_LEMMA] THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a + u) dot (a + u) = a dot a + &2 * (u dot a) + u dot u`] THEN
  REWRITE_TAC[REAL_ARITH `(a + &2 * b + c = a + c) <=> (b = &0)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[DOT_LADD] THEN CONJ_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`vs:(real^N)list`,`vs:(real^N)list`) THEN
    SPEC_TAC(`as:(real)list`,`as:(real)list`) THEN
    REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
    REWRITE_TAC[ALL; ITLIST2; DOT_RZERO; SUC_INJ] THEN
    ASM_SIMP_TAC[DOT_RADD] THEN
    REWRITE_TAC[REAL_ADD_RID; DOT_RMUL] THEN
    SIMP_TAC[orthogonal] THEN REWRITE_TAC[REAL_MUL_RZERO];
    MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[REAL_ARITH `(a + b = a) <=> (b = &0)`] THEN
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `orthogonal (u:real^N)` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[orthogonal]]);;

(* ------------------------------------------------------------------------- *)
(* The implication that we normally use.                                     *)
(* ------------------------------------------------------------------------- *)

let SOLOVAY_PROFORMA = prove
 (`!P vs.
   (!c. &0 <= c
        ==> !as. (LENGTH as = LENGTH vs)
                 ==> P (CONS ((ITLIST2 (\a v s. a % v + s) as vs (vec 0)) dot
                              (ITLIST2 (\a v s. a % v + s) as vs (vec 0)) + c)
                             (MAP ((dot)
                                   (ITLIST2 (\a v s. a % v + s) as vs (vec 0)))
                                  vs))
                    vs)
   ==> !w:real^N. P (MAP ((dot) w) (CONS w vs)) vs`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SOLOVAY_PROFORMA_EQ] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[DOT_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Automatically set up an implication for n (+1 eliminated) quantifier.     *)
(* ------------------------------------------------------------------------- *)

let SOLOVAY_RULE =
  let v_tm = `v:(real^N)list` and d_tm = `d:real list`
  and elv_tm = `EL:num->(real^N)list->real^N`
  and eld_tm = `EL:num->(real)list->real`
  and rn_ty = `:real^N`
  and rewr_rule = REWRITE_RULE
   [MAP; EL; HD; TL; LENGTH; FORALL_LENGTH_CLAUSES;
    ITLIST2; VECTOR_ADD_RID; VECTOR_ADD_LID; DOT_LZERO]
  and sewr_rule = PURE_ONCE_REWRITE_RULE[DOT_SYM] in
  fun n ->
    let args =
      map (fun i -> mk_comb(mk_comb(elv_tm,mk_small_numeral i),v_tm))
          (0--(n-1)) @
      map (fun i -> mk_comb(mk_comb(eld_tm,mk_small_numeral i),d_tm))
          (1--n) @
      [mk_comb(mk_comb(eld_tm,mk_small_numeral 0),d_tm)] in
    let pty = itlist (mk_fun_ty o type_of) args bool_ty in
    let p_tm = list_mk_abs([d_tm;v_tm],list_mk_comb(mk_var("P",pty),args))
    and vs = make_args "v" [] (replicate rn_ty n) in
    let th1 = ISPECL [p_tm; mk_list(vs,rn_ty)] SOLOVAY_PROFORMA in
    let th2 = rewr_rule(CONV_RULE(TOP_DEPTH_CONV num_CONV) th1) in
    let th3 = sewr_rule th2 in
    itlist (fun v -> MATCH_MP MONO_FORALL o GEN v) vs th3;;

(* ------------------------------------------------------------------------- *)
(* Now instantiate it to some special cases.                                 *)
(* ------------------------------------------------------------------------- *)

let MK_SOLOVAY_PROFORMA =
  let preths = map SOLOVAY_RULE (0--9) in
  fun n -> if n < 10 then el n preths else SOLOVAY_RULE n;;

(* ------------------------------------------------------------------------- *)
(* Apply it to a goal.                                                       *)
(* ------------------------------------------------------------------------- *)

let is_vector_ty ty =
  match ty with
   Tyapp("cart",[Tyapp("real",[]);_]) -> true
  | _ -> false;;

let SOLOVAY_REDUCE_TAC (asl,w) =
  let avs = sort (<) (filter (is_vector_ty o type_of) (frees w)) in
  (REWRITE_TAC[DOT_SYM] THEN
   MAP_EVERY (fun v -> SPEC_TAC(v,v)) (rev avs) THEN
   MATCH_MP_TAC(MK_SOLOVAY_PROFORMA (length avs - 1)) THEN
   REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_RADD; DOT_RMUL; DOT_LZERO;
               DOT_RZERO] THEN
   REPEAT GEN_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Overall tactic.                                                           *)
(* ------------------------------------------------------------------------- *)

let SOLOVAY_VECTOR_TAC =
  REWRITE_TAC[dist; real_gt; real_ge; NORM_LT; NORM_LE; GSYM DOT_POS_LT] THEN
  REPEAT GEN_TAC THEN SOLOVAY_TAC THEN
  REWRITE_TAC[DOT_LZERO; DOT_RZERO] THEN
  REPEAT SOLOVAY_REDUCE_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID; REAL_MUL_RID;
              REAL_ADD_LID; REAL_ADD_RID] THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG;
              REAL_MUL_LID; REAL_MUL_RID; GSYM real_sub];;

(* ------------------------------------------------------------------------- *)
(* An example where REAL_RING then works.                                    *)
(* ------------------------------------------------------------------------- *)

let PYTHAGORAS = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_RING);;

(*** Actually in this case we can fairly easily do things manually, though
     we do need to explicitly use symmetry of the dot product.

let PYTHAGORAS = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  REWRITE_TAC[NORM_POW_2; orthogonal; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  CONV_TAC REAL_RING);;

 ***)

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

needs "Examples/sos.ml";;

let EXAMPLE_1 = prove
 (`!x y:real^N. x dot y <= norm x * norm y`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;

let EXAMPLE_2 = prove
 (`!x y:real^N. a % (x + y) = a % x + a % y`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;

(*** Takes a few minutes but does work

let EXAMPLE_3 = prove
 (`!x y:real^N. norm (x + y) <= norm x + norm y`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;

****)

let EXAMPLE_4 = prove
 (`!x y z. x dot (y + z) = (x dot y) + (x dot z)`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;

let EXAMPLE_5 = prove
 (`!x y. (x dot x = &0) ==> (x dot y = &0)`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;

(* ------------------------------------------------------------------------- *)
(* This is NORM_INCREASES_ONLINE.                                            *)
(* ------------------------------------------------------------------------- *)

g `!a d:real^N.
    ~(d = vec 0) ==> norm (a + d) > norm a \/ norm (a - d) > norm a`;;

time e SOLOVAY_VECTOR_TAC;;

time e (CONV_TAC REAL_SOS);;

(* ------------------------------------------------------------------------- *)
(* DIST_INCREASES_ONLINE                                                     *)
(* ------------------------------------------------------------------------- *)

g `!b a d:real^N.
    ~(d = vec 0) ==> dist(a,b + d) > dist(a,b) \/ dist(a,b - d) > dist(a,b)`;;

time e SOLOVAY_VECTOR_TAC;;

time e (CONV_TAC REAL_SOS);;

(* ------------------------------------------------------------------------- *)
(* This one doesn't seem to work easily, but I think it does eventually.     *)
(* ------------------------------------------------------------------------- *)

(****
let EXAMPLE_6 = prove
 (`!a x. norm(a % x) = abs(a) * norm x`;;
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;
 ****)

let EXAMPLE_7 = prove
 (`!x. abs(norm x) = norm x`,
   SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;

(*** But this is (at least) really slow

let EXAMPLE_8 = prove
 (`!x y. abs(norm(x) - norm(y)) <= abs(norm(x - y))`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;
****)

(* ------------------------------------------------------------------------- *)
(* One from separating hyperplanes with a richer structure.                  *)
(* ------------------------------------------------------------------------- *)

needs "Rqe/make.ml";;

let EXAMPLE_9 = prove
 (`!x:real^N y. x dot y > &0 ==> ?u. &0 < u /\ norm(u % y - x) < norm x`,
  SOLOVAY_VECTOR_TAC THEN
  W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  CONV_TAC REAL_QELIM_CONV);;

(* ------------------------------------------------------------------------- *)
(* Even richer set of quantifier alternations.                               *)
(* ------------------------------------------------------------------------- *)

let EXAMPLE_10 = prove
 (`!x:real^N y.
        x dot y > &0
        ==> ?u. &0 < u /\
                !v. &0 < v /\ v <= u ==> norm(v % y - x) < norm x`,
  SOLOVAY_VECTOR_TAC THEN
  W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  CONV_TAC REAL_QELIM_CONV);;
