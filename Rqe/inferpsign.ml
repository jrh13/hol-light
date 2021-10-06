(* ====================================================================== *)
(*  INFERPSIGN                                                            *)
(* ====================================================================== *)

(* ------------------------------------------------------------------------- *)
(* Infer sign of p(x) at points from corresponding qi(x) with pi(x) = 0      *)
(* ------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(*  INFERPSIGN                                                            *)
(* ---------------------------------------------------------------------- *)


let isign_eq_zero thm =
  let __,_,sign = dest_interpsign thm in
    sign = szero_tm;;

let isign_lt_zero thm =
  let __,_,sign = dest_interpsign thm in
    sign = sneg_tm;;

let isign_gt_zero thm =
  let __,_,sign = dest_interpsign thm in
    sign = spos_tm;;

(*
let p_thm,q_thm = ith 1 split_thms
*)
let inferpsign_row vars sgns p_thm q_thm div_thms =
  let pthms = map (BETA_RULE o (PURE_REWRITE_RULE[interpsigns])) (interpsigns_thms2 p_thm) in
  let qthms = map (BETA_RULE o (PURE_REWRITE_RULE[interpsigns])) (interpsigns_thms2 q_thm) in
  let _,set,_ = dest_interpsigns p_thm in
  if can (get_index isign_eq_zero) pthms then (* there's a zero *)
    let ind = get_index isign_eq_zero pthms in
    let pthm = ith ind pthms in
    let qthm = ith ind qthms in
    let div_thm = ith ind div_thms in
    let div_thm' = GEN (hd vars) div_thm in
    let aks,pqr = dest_eq (concl div_thm) in
    let ak,s = dest_mult aks in
    let a,k = dest_pow ak in
    let pq,r = dest_plus pqr in
    let p,q = dest_mult pq in
    let parity_thm = PARITY_CONV k in
    let evenp = fst(dest_comb (concl parity_thm)) = even_tm in
    let sign_thm = FINDSIGN vars sgns a in
    let op,_,_ = get_binop (concl sign_thm) in
    if evenp then
      let nz_thm =
        if op = rlt then MATCH_MP ips_lt_nz_thm sign_thm
        else if op = rgt then MATCH_MP ips_gt_nz_thm sign_thm
        else if op = rneq then sign_thm
        else failwith "inferpsign: 0" in
      let imp_thms =
        CONJUNCTS(ISPEC set (MATCH_MPL[EVEN_DIV_LEM;div_thm';nz_thm;parity_thm])) in
      let _,_,qsign = dest_interpsign qthm in
      let mp_thm =
        if qsign = sneg_tm then ith 0 imp_thms
        else if qsign = spos_tm then ith 1 imp_thms
        else if qsign = szero_tm then ith 2 imp_thms
        else failwith "inferpsign: 1" in
      let final_thm = MATCH_MPL[mp_thm;pthm;qthm] in
        mk_interpsigns (final_thm::pthms)
    else (* k is odd *)
      if op = rgt then (* a > &0 *)
        let imp_thms =
          CONJUNCTS(ISPEC set (MATCH_MPL[GT_DIV_LEM;div_thm';sign_thm])) in
        let _,_,qsign = dest_interpsign qthm in
        let mp_thm =
          if qsign = sneg_tm then ith 0 imp_thms
          else if qsign = spos_tm then ith 1 imp_thms
          else if qsign = szero_tm then ith 2 imp_thms
          else failwith "inferpsign: 1" in
        let final_thm = MATCH_MPL[mp_thm;pthm;qthm] in
          mk_interpsigns (final_thm::pthms)
      else
        failwith "inferpsign: shouldn`t reach this point with an odd power and negative sign!  See PDIVIDES and return the correct div_thm"
  else (* no zero *)
    let p = snd(dest_mult (lhs(concl (hd div_thms)))) in
    let p1 = mk_abs(hd vars,p) in
    let pthm = ISPECL [set;p1] unknown_thm in
      mk_interpsigns (pthm::pthms);;

(* {{{ Doc *)
(*
split_interpsigns
   |- interpsigns
     [p0; p1; p2; q0; q1; q2]
     (\x. x < x1)
     [Pos; Pos; Pos; Neg; Neg; Neg]

  -->

(
   |- interpsigns
     [p0; p1; p2]
     (\x. x < x1)
     [Pos; Pos; Pos]
,
   |- interpsigns
     [q0; q1; q2]
     (\x. x < x1)
     [ Neg; Neg; Neg]
)
*)
(* }}} *)
let split_interpsigns thm =
  let thms = interpsigns_thms2 thm in
  let n = length thms / 2 in
  let l,r = chop_list n thms in
    (mk_interpsigns l,mk_interpsigns r);;

let INFERPSIGN vars sgns mat_thm div_thms =
  let pts,pols,signs = dest_interpmat (concl mat_thm) in
  let n = length (dest_list pols) / 2 in
  let rol_thm,sgn_thm = interpmat_thms mat_thm in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb (concl rol_thm))) in
  let conj_thms = CONJUNCTS(REWRITE_RULE[ALL2;part_thm] sgn_thm) in
  let split_thms = map split_interpsigns conj_thms in
  let conj_thms' = map (fun (x,y) -> inferpsign_row vars sgns x y div_thms) split_thms in
  let all_thm = mk_all2_interpsigns part_thm conj_thms' in
  let mat_thm' = mk_interpmat_thm rol_thm all_thm in
    mat_thm';;

(* ---------------------------------------------------------------------- *)
(*  Opt                                                                   *)
(* ---------------------------------------------------------------------- *)

let MK_REP =
  let rep_tm = `REPLICATE:num -> sign -> sign list` in
  let len_tm = `LENGTH:real list -> num` in
  let one = `1` in
  let two = `2` in
  let unknown = `Unknown` in
  fun pts ->
    let num = mk_binop np (mk_binop nm two (mk_comb(len_tm,pts))) one in
    let len = length (dest_list pts) in
    let num2 = MK_SUC (2 * len + 1) in
    let lthm = ARITH_SIMP_CONV[LENGTH] num in
    let lthm2 = TRANS lthm num2 in
    let lthm3 = AP_THM (AP_TERM rep_tm lthm2) unknown in
      REWRITE_RULE[REPLICATE] lthm3;;

let INSERT_UNKNOWN_COL =
  fun mat_thm p ->
    let pts,_,_ = dest_interpmat (concl mat_thm) in
    let rep_thm = MK_REP pts in
    let mat_thm' = MATCH_MP INFERPSIGN_MATINSERT_THM mat_thm in
    let mat_thm'' = PURE_REWRITE_RULE[MAP2;rep_thm] mat_thm' in
      ISPEC p mat_thm'';;

let REMOVE_QS =
  fun mat_thm ->
    let _,pols,_ = dest_interpmat (concl mat_thm) in
    let len = length (dest_list pols) in
    if not (len mod 2 = 1) then failwith "odd pols?" else
    let mat_thm' = funpow (len / 2) (MATCH_MP REMOVE_LAST) mat_thm in
      REWRITE_RULE[MAP;BUTLAST;NOT_CONS_NIL;TL;HD;] mat_thm';;

let SPLIT_LIST n l ty =
  let l' = dest_list l in
  let l1',l2' = chop_list n l' in
  let l1,l2 = (mk_list(l1',ty),mk_list(l2',ty)) in
  let app_tm = mk_const("APPEND",[ty,aty]) in
  let l3 = mk_comb(mk_comb(app_tm,l1),l2) in
    SYM(REWRITE_CONV[APPEND] l3);;

(*
let thm = asign
*)

let prove_nonzero thm =
  let op,_,_ = get_binop (concl thm) in
  if op = rgt then MATCH_MP ips_gt_nz_thm thm
  else if op = rlt then MATCH_MP ips_lt_nz_thm thm
  else if op = rneq then thm
  else failwith "prove_nonzero: bad op";;

(*
let mat_thm = mat_thm'
let ind = 7
*)


let INFERPT =
  let unknown = `Unknown` in
  let zero = `Zero` in
  let pos = `Pos` in
  let neg = `Neg` in
  let pow = `(pow)` in
  let even_tm = `(EVEN)` in
  let odd_tm = `(ODD)` in
  let rr_ty = `:real -> real` in
  let sl_ty = `:sign list` in
  let s_ty = `:sign` in
  let imat = `interpmat` in
  let rr_length = mk_const("LENGTH",[rr_ty,aty]) in
  let s_length = mk_const("LENGTH",[s_ty,aty]) in
  let sl_length = mk_const("LENGTH",[sl_ty,aty]) in
  let imat = `interpmat` in
  fun vars sgns mat_thm div_thms ind ->
    let pts,pols,signs = dest_interpmat (concl mat_thm) in
    let pols' = dest_list pols in
    let signsl = dest_list signs in
    let signs' = map dest_list signsl in
    let pols_len = length (hd signs') in
    let pols_len2 = pols_len / 2 in
    let pt_sgnl = ith ind signsl in
    let pt_sgns = ith ind signs' in
    let zind = index zero pt_sgns in
    if zind > pols_len2 then mat_thm else (* return if not a zero of a p, only a q *)
    let psgn = ith (pols_len2 + zind) pt_sgns in
    let div_thm = ith (zind - 1) div_thms in
    let a,n = dest_binop pow (fst (dest_binop rm (lhs (concl div_thm)))) in
    let asign = FINDSIGN vars sgns a in
    let op,_,_ = get_binop (concl asign) in
    let par_thm = PARITY_CONV n in
    let par = fst(dest_comb(concl par_thm)) in
    let mp_thm =
      (* note: by def of PDIVIDES, we can`t have
         negative sign and odd power at this point *)
      (* n is even *)
      if par = even_tm then
        if psgn = pos then INFERPSIGN_POS_EVEN
        else if psgn = neg then INFERPSIGN_NEG_EVEN
        else if psgn = zero then INFERPSIGN_ZERO_EVEN
        else failwith "INFERPT: bad sign"
      else (* n is odd *)
        if psgn = pos then INFERPSIGN_POS_ODD_POS
        else if psgn = neg then INFERPSIGN_NEG_ODD_POS
        else if psgn = zero then INFERPSIGN_ZERO_ODD_POS
        else failwith "INFERPT: bad sign" in
    (* pols *)
    let split_pols1 = SPLIT_LIST zind pols rr_ty in
    let _,l2 = chop_list zind pols' in
    let split_pols2 = SPLIT_LIST pols_len2 (mk_list(l2,rr_ty)) rr_ty in
    let s1,t1 = dest_comb (rhs (concl split_pols1)) in
    let split_pols_thm = TRANS split_pols1 (AP_TERM s1 split_pols2) in
    (* pt_sgns *)
    let split_sgns1 = SPLIT_LIST zind pt_sgnl s_ty in
    let _,l3 = chop_list zind pt_sgns in
    let split_sgns2 = SPLIT_LIST pols_len2 (mk_list(l3,s_ty)) s_ty in
    let s2,t2 = dest_comb (rhs (concl split_sgns1)) in
    let split_pt_sgns_thm = TRANS split_sgns1 (AP_TERM s2 split_sgns2) in
    (* sgns *)
    let split_signs = SPLIT_LIST ind signs sl_ty in
    let r1,r3 = dest_comb(rhs (concl split_signs)) in
    let tl_thm = HD_CONV (ONCE_REWRITE_CONV[split_pt_sgns_thm]) r3 in
    let r4,_ = dest_comb (rhs (concl split_signs)) in
    let split_sgns_thm = TRANS split_signs (AP_TERM r4 tl_thm) in
    (* imat *)
    let mat1 = mk_comb(imat,pts) in
    let mat_thm1 = AP_TERM mat1 split_pols_thm in
    let mat_thm2 = MK_COMB(mat_thm1,split_sgns_thm) in
    let mat_thm3 = EQ_MP mat_thm2 mat_thm in
    (* length thms *)
    (* LENGTH ps = LENGTH s1 *)
    let ps = mk_list(tl(dest_list(snd(dest_comb s1))),rr_ty) in
    let ps_len = REWRITE_CONV[LENGTH] (mk_comb(rr_length,ps)) in
    let ss = mk_list(tl(dest_list(snd(dest_comb s2))),s_ty) in
    let ss_len = REWRITE_CONV[LENGTH] (mk_comb(s_length,ss)) in
    let ps_s1_thm = TRANS ps_len (SYM ss_len) in
    (* LENGTH qs = LENGTH s2 *)
    let k1 = tl (fst (chop_list pols_len2 (dest_list t1))) in
    let qs = mk_list(k1,rr_ty) in
    let qs_len = REWRITE_CONV[LENGTH] (mk_comb(rr_length,qs)) in
    let k2 = tl (fst (chop_list pols_len2 (dest_list t2))) in
    let s2s = mk_list(k2,s_ty) in
    let s2s_len = REWRITE_CONV[LENGTH] (mk_comb(s_length,s2s)) in
    let qs_s2_thm = TRANS qs_len (SYM s2s_len) in
    (* ODD (LENGTH sgns) *)
    let _,hdsgns = dest_comb r1 in
    let odd_thm = EQT_ELIM(REWRITE_CONV[LENGTH;ODD;EVEN;NOT_ODD;NOT_EVEN] (mk_comb(odd_tm,mk_comb(sl_length,hdsgns)))) in
    (* a <> 0 *)
    let a_thm =
      if par = even_tm then prove_nonzero asign
      else asign in
    let div_thm' = GEN (hd vars) div_thm in
    (* main *)
    let thm1 = BETA_RULE(MATCH_MPL[mp_thm;mat_thm3;ps_s1_thm;qs_s2_thm;odd_thm]) in
    let thm2 =
      if par = even_tm then MATCH_MPL[thm1;div_thm';a_thm;par_thm]
      else MATCH_MPL[thm1;div_thm';a_thm] in
      REWRITE_RULE[APPEND] thm2;;

(*
let mat_thm = mat_thm'
*)
let INFERPTS vars sgns mat_thm div_thms =
  let pts,_,_ = dest_interpmat (concl mat_thm) in
  let len = 2 * length (dest_list pts) in
  let ods = filter odd (1--len) in
    itlist (fun i matthm -> INFERPT vars sgns matthm div_thms i) ods mat_thm;;


let itvars,itsgns,itmat,itdivs = ref [],ref [],ref TRUTH,ref [];;
(*
let vars,sgns,mat_thm,div_thms = !itvars,!itsgns,!itmat,!itdivs
*)

let INFERPSIGN2 vars sgns mat_thm div_thms =
  itvars := vars;
  itsgns := sgns;
  itmat := mat_thm;
  itdivs := div_thms;
  let _,bod = dest_binop rm (lhs (concl (hd div_thms))) in
  let p = mk_abs(hd vars,bod) in
  let mat_thm' = INSERT_UNKNOWN_COL mat_thm p in
  let mat_thm'' = INFERPTS vars sgns mat_thm' div_thms in
    REMOVE_QS mat_thm'';;


(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let INFERPSIGN vars sgns mat_thm div_thms =
  let start_time = Sys.time() in
  let res = INFERPSIGN vars sgns mat_thm div_thms in
    inferpsign_timer +.= (Sys.time() -. start_time);
    res;;

(*

let l1 = PDIVIDE [`x:real`]
  `&1 + x * (&1 + x * (&1 + x * &1))` `&1 + x * (&2 + x * &3)`;;
let l2 = PDIVIDE [`x:real`]
  `&1 + x * (&1 + x * (&1 + x * &1))` `&2 + x * (-- &3 + x * &1)`;;
let l3 = PDIVIDE [`x:real`]
  `&1 + x * (&1 + x * (&1 + x * &1))` `-- &4 + x * (&0 + x * &1)`;;

let div_thms = [l1;l2;l3];;
let vars = [`x:real`];;
let sgns = [ARITH_RULE `&1 > &0`];;

let mat_thm = ASSUME
  `interpmat [x1; x2; x3; x4; x5]
     [\x. &1 + x * (&2 + x * &3); \x. &2 + x * (-- &3 + x * &1); \x. -- &4 + x * (&0 + x * &1);
      \x. &8 + x * &4; \x. -- &7 + x * &11; \x. &5 + x * &5]
      [[Pos; Pos; Pos; Neg; Neg; Neg];
      [Pos; Pos; Zero; Zero; Neg; Neg];
      [Pos; Pos; Neg; Pos; Neg; Neg];
      [Pos; Pos; Neg; Pos; Neg; Zero];
      [Pos; Pos; Neg; Pos; Neg; Pos];
      [Pos; Pos; Neg; Pos; Zero; Pos];
      [Pos; Pos; Neg; Pos; Pos; Pos];
      [Pos; Zero; Neg; Pos; Pos; Pos];
      [Pos; Neg; Neg; Pos; Pos; Pos];
      [Pos; Zero; Zero; Pos; Pos; Pos];
      [Pos; Pos; Pos; Pos; Pos; Pos]]` ;;

INFERPSIGN vars sgns mat_thm div_thms








*)
