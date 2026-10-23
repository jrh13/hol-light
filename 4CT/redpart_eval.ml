(* ========================================================================= *)
(* 4CT/redpart_eval.ml                                                       *)
(*                                                                           *)
(* The four discharge bound checks of unavoidability.v (discharged by        *)
(* computation in the Coq proof, unavoidability.v:33):                       *)
(*                                                                           *)
(*   check_dbound1 (redpart the_quiz_tree) (the_drule_fork n) (pcons_ n) 5   *)
(*                                                                           *)
(* for n = 5..8, evaluated by call-by-value reduction (compute_fast.ml) into *)
(* THE_DBOUND1_CHECK.  The compset redpart_compset extends the cfquiz        *)
(* compset of quiztree_eval.ml with the part, part_mirror, discharge,        *)
(* hubcap, quiztree and redpart definitions.  Two definitions are not        *)
(* directly executable and get computable lemmas: cmp_range (quantified      *)
(* conditions over arities) is tabulated as the 15 x 15 table                *)
(* CMP_RANGE_TABLE, each entry decided by ARITH_TAC or a witness in 5..13,   *)
(* and qzt_truncate (an existential constructor test) is spelt out by        *)
(* constructor cases in QZT_TRUNCATE_CLAUSES.  Recursions on SUC patterns    *)
(* (drop_part, take_part, ITER, check_dbound1_rec, ...) are driven by        *)
(* suc_rec_conv (num_CONV on the numeral argument first).                    *)
(*                                                                           *)
(* The quiz tree is not expanded: CBV traverses the whole right-hand side of *)
(* a rule (87531 nodes for the_quiz_tree) at every use, so instead the       *)
(* three-level lookups of redpart (qzt_getr s (qzt_truncate qt), qzt_get1    *)
(* ahub qt, then qzt_getr twice) are tabulated as rewrite rules on the       *)
(* symbolic paths (QZT_LOOKUP_RULES, 862 rules; only the leaf lists appear   *)
(* as values):                                                               *)
(*                                                                           *)
(*   qzt_getr r (qzt_truncate the_quiz_tree) = qzt_get1 Qa_i the_quiz_tree   *)
(*   qzt_getr r (qzt_get1 Qa_i the_quiz_tree) = qzt_get1 Qa_j (qzt_get1 ..)  *)
(*   qzt_getr r (qzt_get1 Qa_j (qzt_get1 Qa_i the_quiz_tree)) = <leaf list>  *)
(*   qzt_proper (qzt_get1 Qa_i the_quiz_tree) = T/F                          *)
(* ========================================================================= *)

needs "4CT/redpart.ml";;
needs "4CT/quiztree_eval.ml";;

(* ------------------------------------------------------------------------- *)
(* SUC-pattern recursions: put the numeral argument (position argpos,        *)
(* 0-based) into SUC form, then use the recursion clauses once.              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* cmp_range r1 r2: decide the two quantified range conditions.              *)
(* ------------------------------------------------------------------------- *)

let decide_forall_conv c =
  try EQT_INTRO(prove(c, ARITH_TAC)) with Failure _ ->
    EQF_INTRO(tryfind
      (fun k -> prove(mk_neg c, REWRITE_TAC[NOT_FORALL_THM] THEN
                                          EXISTS_TAC (mk_small_numeral k) THEN
                                          ARITH_TAC))
                      (5--13));;

let cmp_range_conv tm =
  let th1 = REWRITE_CONV[cmp_range; mem_range] tm in
  let rec simp t =
    if is_cond t then
      let c,(x,y) = dest_cond t in
      let th = REWRITE_CONV[decide_forall_conv c] t in
      TRANS th (simp (rand(concl th)))
    else REFL t in
  TRANS th1 (simp (rand(concl th1)));;

let prange_consts =
  map (fun s -> mk_const(s,[]))
      ["Pr55";"Pr66";"Pr77";"Pr88";"Pr99";"Pr56";"Pr67";"Pr78";"Pr89";"Pr57";
       "Pr68";"Pr79";
       "Pr58";"Pr69";"Pr59"];;

(* 225 theorems |- cmp_range Pri Prj = Psubset / Pdisjoint / Pstraddle       *)
let CMP_RANGE_TABLE =
  flat (map (fun r1 -> map (fun r2 -> cmp_range_conv
                            (list_mk_comb(`cmp_range`,[r1;r2])))
                           prange_consts) prange_consts);;

(* ------------------------------------------------------------------------- *)
(* qzt_truncate by constructor cases (the evaluator rewrites with these      *)
(* seven clauses rather than with the match form of the definition).         *)
(* ------------------------------------------------------------------------- *)

let QZT_TRUNCATE_CLAUSES = prove
 (`qzt_truncate QztNil = QztNil /\
   (!q1 q2 q3 t. qzt_truncate (QztLeaf q1 q2 q3 t) = QztLeaf q1 q2 q3 t) /\
   (!t5 t6 t7 t8. qzt_truncate (QztNode t5 t6 t7 t8) = QztNode t5 t6 t7 t8) /\
   (!t9 t10 t11. qzt_truncate (QztHubNode QztNil t9 t10 t11) =
   QztHubNode QztNil t9 t10 t11) /\
   (!q1 q2 q3 t t9 t10 t11. qzt_truncate
   (QztHubNode (QztLeaf q1 q2 q3 t) t9 t10 t11) =
                            QztHubNode (QztLeaf q1 q2 q3 t) t9 t10 t11) /\
   (!t5 t6 t7 t8 t9 t10 t11. qzt_truncate
   (QztHubNode (QztNode t5 t6 t7 t8) t9 t10 t11) =
                             QztNode t5 t6 t7 t8) /\
   (!s9 s10 s11 s58 t9 t10 t11. qzt_truncate
   (QztHubNode (QztHubNode s58 s9 s10 s11) t9 t10 t11) =
                                QztHubNode (QztHubNode s58 s9 s10 s11)
                                t9 t10 t11)`,
  REWRITE_TAC[qzt_truncate]);;

(* ------------------------------------------------------------------------- *)
(* The quiz-tree lookup table (see the header).                              *)
(* ------------------------------------------------------------------------- *)

let QZT_GETR_NODE = prove
 (`!a b c d. qzt_getr Pr55 (QztNode a b c d) = a /\
 qzt_getr Pr66 (QztNode a b c d) = b /\
             qzt_getr Pr77 (QztNode a b c d) = c /\
             qzt_getr Pr88 (QztNode a b c d) = d /\
             qzt_getr Pr99 (QztNode a b c d) = QztNil /\
             qzt_getr Pr56 (QztNode a b c d) = b /\
             qzt_getr Pr67 (QztNode a b c d) = c /\
             qzt_getr Pr78 (QztNode a b c d) = d /\
             qzt_getr Pr89 (QztNode a b c d) = QztNil /\
             qzt_getr Pr57 (QztNode a b c d) = c /\
             qzt_getr Pr68 (QztNode a b c d) = d /\
             qzt_getr Pr79 (QztNode a b c d) = QztNil /\
             qzt_getr Pr58 (QztNode a b c d) = d /\
             qzt_getr Pr69 (QztNode a b c d) = QztNil /\
             qzt_getr Pr59 (QztNode a b c d) = QztNil`,
  REWRITE_TAC[qzt_getr] THEN REWRITE_TAC(both_dirs (distinctness "prange")));;

let QZT_GET1_NODE = prove
 (`!a b c d. qzt_get1 Qa5 (QztNode a b c d) = a /\
 qzt_get1 Qa6 (QztNode a b c d) = b /\
             qzt_get1 Qa7 (QztNode a b c d) = c /\
             qzt_get1 Qa8 (QztNode a b c d) = d /\
             qzt_get1 Qa9 (QztNode a b c d) = QztNil /\
             qzt_get1 Qa10 (QztNode a b c d) = QztNil /\
             qzt_get1 Qa11 (QztNode a b c d) = QztNil`,
  REWRITE_TAC[qzt_get1] THEN REWRITE_TAC(both_dirs (distinctness "qarity")));;

let QZT_GET1_HUB = prove
 (`!t58 t9 t10 t11. qzt_get1 Qa5 (QztHubNode t58 t9 t10 t11) =
 qzt_get1 Qa5 t58 /\
                    qzt_get1 Qa6 (QztHubNode t58 t9 t10 t11) =
                    qzt_get1 Qa6 t58 /\
                    qzt_get1 Qa7 (QztHubNode t58 t9 t10 t11) =
                    qzt_get1 Qa7 t58 /\
                    qzt_get1 Qa8 (QztHubNode t58 t9 t10 t11) =
                    qzt_get1 Qa8 t58 /\
                    qzt_get1 Qa9 (QztHubNode t58 t9 t10 t11) = t9 /\
                    qzt_get1 Qa10 (QztHubNode t58 t9 t10 t11) = t10 /\
                    qzt_get1 Qa11 (QztHubNode t58 t9 t10 t11) = t11`,
  REWRITE_TAC[qzt_get1] THEN REWRITE_TAC(both_dirs (distinctness "qarity")));;

(* One lookup step on an explicit tree term, by a single matching rewrite    *)
let qzt_step_conv =
  GEN_REWRITE_CONV I
    [QZT_GETR_NODE; QZT_GET1_NODE; QZT_GET1_HUB; qzt_getr; qzt_get1;
                      QZT_TRUNCATE_CLAUSES; qzt_proper];;

(* |- f X = value  from  |- X = <explicit tree>                              *)
let qzt_apply f th = TRANS (AP_TERM f th)
  (qzt_step_conv (mk_comb(f, rand(concl th))));;

let qarity_consts = map (fun s -> mk_const(s,[]))
  ["Qa5";"Qa6";"Qa7";"Qa8";"Qa9";"Qa10";"Qa11"];;

(* The arity index qzt_getr selects for a range (upper bound), None = QztNil *)
let prange_to_qa r =
  match fst(dest_const r) with
    "Pr55" -> Some `Qa5` | "Pr56" | "Pr66" -> Some `Qa6`
    | "Pr57" | "Pr67" | "Pr77" -> Some `Qa7`
  | "Pr58" | "Pr68" | "Pr78" | "Pr88" -> Some `Qa8` | _ -> None;;

let is_qzt_node t = is_comb t && fst(dest_const(fst(strip_comb t)))
  = "QztNode";;

let qzt_lookup_rules () =
  let t0 = Sys.time() in
  let th_trunc = qzt_apply `qzt_truncate` THE_QUIZ_TREE_VALUE in
  let th_get1 = map (fun qa ->
      let th = qzt_apply (mk_comb(`qzt_get1`, qa)) THE_QUIZ_TREE_VALUE in
      let r = rand(concl th) in
      if is_comb r && fst(dest_const(fst(strip_comb r))) = "qzt_get1"
      then TRANS th (qzt_step_conv r) else th) qarity_consts in
  let get1_of qa = assoc qa (zip qarity_consts th_get1) in
  let level1 = map (fun r ->
      let lhs_th = qzt_apply (mk_comb(`qzt_getr`, r)) th_trunc in
      match prange_to_qa r with
        Some qa -> TRANS lhs_th (SYM (get1_of qa))
      | None -> lhs_th) prange_consts in
  let th_get12 = flat (map (fun qa_i ->
      let th_i = get1_of qa_i in
      if not (is_qzt_node (rand(concl th_i))) then [] else
      map (fun qa_j -> (qa_i, qa_j, qzt_apply (mk_comb(`qzt_get1`, qa_j))
                        th_i)) qarity_consts)
    qarity_consts) in
  let level2 = flat (map (fun qa_i ->
      let th_i = get1_of qa_i in
      map (fun r ->
        let lhs_th = qzt_apply (mk_comb(`qzt_getr`, r)) th_i in
        match prange_to_qa r with
          Some qa_j when is_qzt_node (rand(concl th_i)) ->
            let (_,_,th_ij) = find
              (fun (a,b,_) -> a = qa_i && b = qa_j) th_get12 in
            TRANS lhs_th (SYM th_ij)
        | _ -> lhs_th) prange_consts) qarity_consts) in
  let level3 = flat (map (fun (_,_,th_ij) ->
      map (fun r -> qzt_apply (mk_comb(`qzt_getr`, r)) th_ij) prange_consts)
        th_get12) in
  let proper = map (fun th -> qzt_apply `qzt_proper` th) th_get1 in
  let rules = level1 @ level2 @ level3 @ proper in
  Printf.printf "QZT_LOOKUP_RULES: %d rules in %.1f s\n%!" (length rules)
    (Sys.time() -. t0);
  rules;;

let QZT_LOOKUP_RULES = qzt_lookup_rules();;

(* ------------------------------------------------------------------------- *)
(* The compset.                                                              *)
(* ------------------------------------------------------------------------- *)

let redpart_compset () =
  let cs = cfquiz_compset() in
(* the_quiz_tree must stay a NEUTRAL constant: drop its definitional rule    *)
(* (cfquiz_compset has it, so that the_quiz_tree could be computed) and add  *)
(* the lookup table instead                                                  *)
  Compute.scrub_thms [the_quiz_tree] cs;
  Compute.add_thms QZT_LOOKUP_RULES cs;
  List.iter (fun c -> Compute.add_conv c cs)
    [(`(*):num->num->num`, 2, NUM_MULT_CONV);
     (`MAX:num->num->num`, 2, NUM_MAX_CONV);
     (`MIN:num->num->num`, 2, NUM_MIN_CONV)];
  List.iter (fun (c,ar,cl,pos) -> Compute.add_conv (c, ar,
                                                    suc_rec_conv cl pos) cs)
    [(`drop_part`, 2, drop_part, 0); (`take_part`, 2, take_part, 0);
     (`ITER:num->(A->A)->A->A`, 3, ITER, 0);
     (`check_dbound1_rec`, 5, check_dbound1_rec, 4);
     (`check_dbound2_rec`, 7, check_dbound2_rec, 6);
     (`check_2dbound2_rec`, 13, check_2dbound2_rec, 12);
     (`red_zpart_rec`, 8, red_zpart_rec, 6);
     (`redpart_loop`, 4, redpart_loop, 2)];
  Compute.add_thms
  (both_dirs (distinctness "prange") @ both_dirs (distinctness "subpart_loc") @
                    both_dirs (distinctness "part") @ both_dirs
                      (distinctness "part_rel") @
                    both_dirs (distinctness "zpart_loc") @ both_dirs
                      (distinctness "hubcap") @
                    [injectivity "part"; injectivity "zpart";
                     injectivity "hubcap"]) cs;
(* list functions                                                            *)
  Compute.add_thms
    [FILTER; MAP; LENGTH; APPEND; ALL; EX; HD; TL; REVERSE; ZIP; ITLIST; MEM;
                    NOT_CONS_NIL] cs;
(* part.ml                                                                   *)
  Compute.add_thms
 [mem_range; size_part; cat_part; catrev_part; rev_part; rot_part;
  subpart_loc_move;
                    get_spoke; next_hat; get_hat; get_fan1r; get_fan2r;
                    get_fan3r; get_fan1l; get_fan2l;
                    get_fan3l; mirror_part_rec; mirror_part; notPsubset;
                    meet_prel; cmp_part; pcons_s;
                    pcons_; part_update; rlo; rhi; rbounded; prange_of_bounds;
                    meet_range; meet_part;
                    prange_lo; prange_hi; good_rsplit; split_range;
                    gsplit_spoke; gsplit_hat; gsplit_fan1;
                    gsplit_fan2; gsplit_fan3; good_split; ssplit_spoke;
                    ssplit_hat; ssplit_fan1;
                    ssplit_fan2; ssplit_fan3; split_part] cs;
  Compute.add_thms CMP_RANGE_TABLE cs;
(* part_mirror.ml: converse_part                                             *)
  Compute.add_thms
 [cp12_auxA; cp12_auxB; cp12_auxC; conv_part12; cp3_3; cp3_2;
  cp3_1; conv_part3;
                    cp4_aux; conv_part4; conv_part5; converse_part] cs;
(* discharge.ml                                                              *)
  Compute.add_thms
 [drule1; drule2; drule2_P; drule3; drule3_P; drule4; drule4_P; drule5;
  drule6; drule7;
                    drule8; drule9; drule10; drule10_P; drule11; drule12;
                    drule13; drule14; drule15;
                    drule16; drule17; drule18; drule19; drule20; drule21;
                    drule22; drule23; drule24;
                    drule25; drule26; drule27; drule28; drule29; drule30;
                    drule31; drule31_P; drule32;
                    base_drules; sym_drule; symmetrize_drules; the_drules;
                    pick_source_drules;
                    pick_target_drules; sort_drules_rec; sort_drules;
                    the_drule_fork] cs;
(* hubcap.ml                                                                 *)
  Compute.add_thms
    [check_dbound1; check_unfit; check_dbound2; check_2dbound2; incr_nth; nth0;
                    tally_hubcap; hubcap_cover_rec; hubcap_cover; hubcap_rot;
                    hub_subn; hubcap_fit] cs;
(* quiztree.ml                                                               *)
  Compute.add_thms
 [QZT_TRUNCATE_CLAUSES; qzt_proper; isQztHubNode; qzt_get1; qzt_get2; qzt_get3;
                    qarity_of_nat; nat_of_qarity] cs;
(* redpart.ml                                                                *)
  Compute.add_thms
 [zp_zi; zp_pl; zp_pr; zmove; hub_range; zrange_loc; zrange; shift_part;
  zshiftl_aux;
                    zshiftl; zshiftr_aux; zshiftr; zfanL; zfanR; zfanLt;
                    zfanRt; zstepL_loc; zstepL;
                    zstepR_loc; zstepR; zstepLt_loc; zstepLt; zstepRt_loc;
                    zstepRt; topqa; fitqa; popqa;
                    red_pcons; red_popr_spoke; red_popr_hat; red_popl_spoke;
                    red_popl_hat; red_popl_fan1l;
                    red_popl_fan2l; red_popl_fan3l; red_popl_fan1r;
                    red_popl_fan2r; red_popl_fan3r;
                    red_pop_loc; red_pop; fitqzp; red_popqzp; red_qzt_leaf;
                    qzt_getr; red_zpart_cases;
                    red_zpart_step; red_zpart; redpart] cs;
  cs;;

let the_redpart_compset = redpart_compset();;

(* CBV with a timing report                                                  *)
let timed_cbv_conv cs tm =
  let t0 = Sys.time() in
  let th = Compute.CBV_CONV cs tm in
  Printf.printf "REDPART_EVAL: evaluated in %.1f s\n%!" (Sys.time() -. t0);
  th;;

(* ------------------------------------------------------------------------- *)
(* Coq unavoidability.v:33: the four closed boolean evaluations.             *)
(* ------------------------------------------------------------------------- *)

let THE_DBOUND1_CHECK = prove
 (`!n. 5 <= n /\ n <= 8
       ==> check_dbound1 (redpart the_quiz_tree) (the_drule_fork n)
       (pcons_ n) 5`,
  REWRITE_TAC[ARITH_RULE
    `5 <= n /\ n <= 8 <=> n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  CONV_TAC(timed_cbv_conv the_redpart_compset));;

