(* ====================================================================== *)
(*  DEDMATRIX                                                             *)
(* ====================================================================== *)

(* ------------------------------------------------------------------------- *)
(* Deduce matrix for p,p1,...,pn from matrix for p',p1,...,pn,q0,...,qn      *)
(* where qi = rem(p,pi) with p0 = p'                                         *)
(* ------------------------------------------------------------------------- *)

let prove_nonconstant =
  let nonconstant_tm = `nonconstant` in 
    fun pdiff_thm normal_thm -> 
      let thm = ONCE_REWRITE_RULE[GSYM pdiff_thm] normal_thm in
      let ret = REWRITE_RULE[GSYM NORMAL_PDIFF] thm in
      let f,_ = strip_comb (concl ret) in
        if not (f = nonconstant_tm) then failwith "prove_nonconstant" else ret;;

let REMOVE_COLUMN1 mat_thm = 
  let mat_thm1 = MATCH_MP REMOVE_COL1 mat_thm in
    REWRITE_RULE[MAP;HD;TL] mat_thm1;;

let APPENDIZE l n = 
  let lty = type_of l in
  let ty = hd(snd(dest_type lty)) in
  let app_tm = mk_const("APPEND",[ty,aty]) in
  let l1,l2 = chop_list n (dest_list l) in
  let app = mk_comb(mk_comb(app_tm,mk_list(l1,ty)),mk_list(l2,ty)) in
    GSYM (REWRITE_CONV[APPEND] app);;

let REMOVE_INFINITIES thm =
  let thm' = MATCH_MP INTERPMAT_TRIO thm in
  let pts,_,sgns = dest_interpmat (concl thm') in
  let p_thm = APPENDIZE pts (length (dest_list pts) - 2) in     
  let pts',_,sgns = dest_interpmat (concl thm') in
  let s_thm = APPENDIZE sgns (length (dest_list sgns) - 5) in     
  let thm'' = MATCH_MP INTERPMAT_TRIO_TL (ONCE_REWRITE_RULE[p_thm;s_thm] thm') in
    REWRITE_RULE[APPEND] thm'';;

let get_dirs = 
  let pos = `Pos` in
  let neg = `Neg` in
  fun lb_deriv ub_deriv -> 
    if lb_deriv = pos && ub_deriv = pos then INFIN_POS_POS
    else if lb_deriv = pos && ub_deriv = neg then INFIN_POS_NEG
    else if lb_deriv = neg && ub_deriv = pos then INFIN_NEG_POS
    else if lb_deriv = neg && ub_deriv = neg then INFIN_NEG_NEG
    else failwith "get_dirs: bad signs";;

let get_sing_dirs = 
  let pos = `Pos` in
  let neg = `Neg` in
  fun lb_deriv ub_deriv -> 
    if lb_deriv = pos && ub_deriv = pos then INFIN_SING_POS_POS
    else if lb_deriv = pos && ub_deriv = neg then INFIN_SING_POS_NEG
    else if lb_deriv = neg && ub_deriv = pos then INFIN_SING_NEG_POS
    else if lb_deriv = neg && ub_deriv = neg then INFIN_SING_NEG_NEG
    else failwith "get_dirs: bad signs";;


let aitvars,aitdiff,aitnorm,aitmat = ref [],ref TRUTH,ref TRUTH,ref TRUTH;;
(*
let vars,diff_thm,normal_thm,mat_thm = !aitvars,!aitdiff,!tnorm,!tmat
let vars,diff_thm,normal_thm,mat_thm = vars, pdiff_thm, normal_thm, mat_thm''
*)
let ADD_INFINITIES = 
  let real_app = `APPEND:real list -> real list -> real list` in 
  let sign_app = `APPEND:(sign list) list -> (sign list) list -> (sign list) list` in
  let imat = `interpmat` in
  let pos = `Pos` in
  let neg = `Neg` in
  let sl_ty = `:sign list` in
  let real_ty = `:real` in
  fun vars diff_thm normal_thm mat_thm -> 
    aitvars := vars;
    aitdiff := diff_thm;
    aitnorm := normal_thm;
    aitmat := mat_thm;
    let nc_thm = prove_nonconstant diff_thm normal_thm in
    let pts,pols,sgns = dest_interpmat (concl mat_thm) in
    let polsl = dest_list pols in
    let p::p'::_ = polsl in
    let p_thm = ABS (hd vars) (POLY_ENLIST_CONV vars (snd(dest_abs p))) in
    let p'_thm = ONCE_REWRITE_RULE[GSYM diff_thm] (ABS (hd vars) (POLY_ENLIST_CONV vars (snd(dest_abs p')))) in
    let pols_thm = REWRITE_CONV[p_thm;p'_thm] pols in 
    let sgnsl = dest_list sgns in
    let sgns_len = length sgnsl in
    let thm1 = 
      if sgns_len = 1 then 
        let sgn = (hd(tl(dest_list (hd sgnsl)))) in
        let mp_thm = 
          if sgn = pos then INFIN_NIL_POS 
          else if sgn = neg then INFIN_NIL_NEG
          else failwith "bad sign in mat" in
        let mat_thm1 = MK_COMB(MK_COMB(AP_TERM imat (REFL pts), pols_thm),REFL sgns) in
        let mat_thm2 = EQ_MP mat_thm1 mat_thm in
          MATCH_MP (MATCH_MP mp_thm mat_thm2) nc_thm
      else if sgns_len = 3 then 
        let lb_deriv = hd (tl (dest_list (hd sgnsl))) in
        let ub_deriv = hd (tl (dest_list (last sgnsl))) in
        let mp_thm = get_sing_dirs lb_deriv ub_deriv in
        let mat_thm1 = MK_COMB(MK_COMB(AP_TERM imat (REFL pts), pols_thm),REFL sgns) in
        let mat_thm2 = EQ_MP mat_thm1 mat_thm in
          MATCH_MP (MATCH_MP mp_thm mat_thm2) nc_thm
      else 
        let s1,s2 = chop_list (sgns_len - 3) sgnsl in
        let s3 = mk_list(s1,sl_ty) in
        let s4 = mk_comb(mk_comb(sign_app,s3),mk_list(s2,sl_ty)) in
        let sgns_thm = prove(mk_eq(sgns,s4),REWRITE_TAC[APPEND]) in
        let mat_thm1 = MK_COMB(MK_COMB(AP_TERM imat (REFL pts), pols_thm),sgns_thm) in
        let mat_thm2 = EQ_MP mat_thm1 mat_thm in 
        let lb_deriv = hd (tl (dest_list (hd sgnsl))) in
        let ub_deriv = hd (tl (dest_list (last sgnsl))) in
        let mp_thm = get_dirs lb_deriv ub_deriv in
          MATCH_MP (MATCH_MP mp_thm mat_thm2) nc_thm in 
    let thm2 = REWRITE_RULE[APPEND;GSYM pols_thm] thm1 in
    let c = concl thm2 in
    let x,bod = dest_exists c in
    let x' = new_var real_ty in
    let bod1 = subst [x',x] bod in
    let assume_thm1 = ASSUME bod1 in
    let x2,bod2 = dest_exists bod1 in
    let x'' = new_var real_ty in  
    let assume_thm2 = ASSUME (subst [x'',x2] bod2) in
      assume_thm2,(x',thm2),(x'',assume_thm1);;


(*
print_timers()
print_times()
reset_timers()
*)


let tvars,tsgns,tdivs,tdiff,tnorm,tcont,tmat,tex = ref [],ref [],ref [], ref TRUTH,ref TRUTH, ref (fun x y -> x), ref TRUTH,  ref [];;
(*
let vars,sgns,div_thms,pdiff_thm,normal_thm,cont,mat_thm,ex_thms = !tvars,!tsgns,!tdivs,!tdiff,!tnorm,!tcont,!tmat,!tex
DEDMATRIX vars sgns div_thms pdiff_thm normal_thm cont mat_thm ex_thms 
*)

let DEDMATRIX vars sgns div_thms pdiff_thm normal_thm cont mat_thm ex_thms = 
  try 
    tvars := vars;
    tsgns := sgns;
    tdivs := div_thms;
    tdiff := pdiff_thm;
    tnorm := normal_thm;
    tmat := mat_thm;
    tex := ex_thms;
    tcont := cont;
    let start_time = Sys.time() in
    let pts,pols,signll = dest_interpmat (concl mat_thm) in
    let mat_thm' = INFERPSIGN vars sgns mat_thm div_thms in
    let mat_thm'' = CONDENSE mat_thm' in
    let mat_thm''',(v1,exthm1),(v2,exthm2) = ADD_INFINITIES vars pdiff_thm normal_thm mat_thm'' in
    let mat_thm4,new_ex_pairs = INFERISIGN vars pdiff_thm mat_thm''' ((v1,exthm1)::(v2,exthm2)::ex_thms) in
    let mat_thm5 = REMOVE_INFINITIES mat_thm4 in 
    let mat_thm6 = REMOVE_COLUMN1 mat_thm5 in
    let mat_thm7 = CONDENSE mat_thm6 in
    (* hack for changing renamed vars *) 
    let mat_thm8 = CONV_RULE (RATOR_CONV (RAND_CONV (LIST_CONV (ALPHA_CONV (hd vars))))) mat_thm7 in
    let ex_pairs = [(v1,exthm1);(v2,exthm2)] @ new_ex_pairs in 
    let cont' mat_thm ex_thms = cont mat_thm (ex_thms @ ex_pairs) in
      cont' mat_thm8 ex_thms
  with (Isign (false_thm,ex_thms)) -> 
    raise (Isign (false_thm,ex_thms)) 
  | Failure x -> failwith ("DEDMATRIX: " ^ x);;

(* {{{ Examples *)

(*


let NOT_NIL_CONV tm = 
  let h,t = dest_cons tm in
    ISPECL [h;t] NOT_CONS_NIL;;

let NORMAL_CONV tm = 
  let normalize_thm = POLY_NORMALIZE_CONV (mk_comb (`normalize`,tm)) in
  let nonnil_thm = NOT_NIL_CONV tm in
  let conj_thm = CONJ normalize_thm nonnil_thm in
    REWRITE_RULE[GSYM normal] conj_thm;;

let vars = [`x:real`];;
let cont a b = a;;
let sgns = [ARITH_RULE `&1 > &0`];;
let normal_thm = NORMAL_CONV `[&1; &2; &3]`;;
let pdiff_thm = POLY_DIFF_CONV `poly_diff [&1; &1; &1; &1]`;;
let ex_thms = [];; 
let _,l1 = PDIVIDES vars sgns `(&1 + x * (&1 + x * (&1 + x * &1)))` `(&1 + x * (&2 + x * &3))`;;
let _,l2 = PDIVIDES vars sgns `(&1 + x * (&1 + x * (&1 + x * &1)))` `(&2 + x * (-- &3 + x * &1))`;;
let _,l3 = PDIVIDES vars sgns `(&1 + x * (&1 + x * (&1 + x * &1)))` `(-- &4 + x * (&0 + x * &1))`;;
let div_thms = [l1;l2;l3];;

let mat_thm = ASSUME 
  `interpmat [x1; x2; x3; x4; x5] 
     [\x. &1 + x * (&2 + x * &3); \x. &2 + x * (-- &3 + x * &1); \x. -- &4 + x * (&0 + x * &1); 
      \x. &8 + x * &4; \x. -- &7 + x * &11; \x. &5 + x * &5]
      [[Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Zero; Zero; Neg; Neg];     
      [Pos; Pos; Neg; Pos; Neg; Neg];     
      [Pos; Zero; Neg; Pos; Neg; Zero];     
      [Pos; Pos; Neg; Pos; Neg; Pos];     
      [Pos; Pos; Zero; Pos; Zero; Pos];     
      [Pos; Pos; Neg; Pos; Pos; Pos];     
      [Pos; Zero; Neg; Pos; Zero; Pos];     
      [Pos; Neg; Neg; Pos; Pos; Pos];     
      [Pos; Zero; Zero; Pos; Pos; Pos];     
      [Pos; Pos; Pos; Pos; Pos; Pos]]` ;;

time (DEDMATRIX vars sgns div_thms pdiff_thm normal_thm (fun x y -> x) mat_thm) []


*)

(* }}} *)


(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let REMOVE_COLUMN1 mat_thm = 
  let start_time = Sys.time() in
  let res = REMOVE_COLUMN1 mat_thm in
    remove_column1_timer +.= (Sys.time() -. start_time);
    res;;

let ADD_INFINITIES vars pdiff_thm normal_thm mat_thm = 
  let start_time = Sys.time() in
  let res = ADD_INFINITIES vars pdiff_thm normal_thm mat_thm in
    add_infinities_timer +.= (Sys.time() -. start_time);
    res;;

let REMOVE_INFINITIES thm = 
  let start_time = Sys.time() in
  let res = REMOVE_INFINITIES thm in
    remove_infinities_timer +.= (Sys.time() -. start_time);
    res;;
