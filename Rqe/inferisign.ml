exception Isign of (thm * ((term * thm) list));;

(* ---------------------------------------------------------------------- *)
(*  Opt                                                                   *)
(* ---------------------------------------------------------------------- *)

let get_mp =
  let unknown = `Unknown` in
  let pos = `Pos` in
  let zero = `Zero` in
  let neg = `Neg` in
    fun upper_sign lower_sign deriv_sign -> 
        (* Pos Pos *)
        if upper_sign = pos && 
           lower_sign = pos && 
           deriv_sign = pos then INFERISIGN_POS_POS_POS
        else if upper_sign = pos && 
           lower_sign = pos && 
           deriv_sign = neg then INFERISIGN_POS_POS_NEG
        (* Pos Neg *)
        else if upper_sign = pos && 
           lower_sign = neg && 
           deriv_sign = pos then INFERISIGN_POS_NEG_POS
        else if upper_sign = pos && 
           lower_sign = neg && 
           deriv_sign = neg then INFERISIGN_POS_NEG_NEG
        (* Pos Zero *)
        else if upper_sign = pos && 
           lower_sign = zero && 
           deriv_sign = pos then INFERISIGN_POS_ZERO_POS
        else if upper_sign = pos && 
           lower_sign = zero && 
           deriv_sign = neg then INFERISIGN_POS_ZERO_NEG
        (* Neg Pos *)
        else if upper_sign = neg && 
           lower_sign = pos && 
           deriv_sign = pos then INFERISIGN_NEG_POS_POS
        else if upper_sign = neg && 
           lower_sign = pos && 
           deriv_sign = neg then INFERISIGN_NEG_POS_NEG
        (* Neg Neg *)
        else if upper_sign = neg && 
           lower_sign = neg && 
           deriv_sign = pos then INFERISIGN_NEG_NEG_POS
        else if upper_sign = neg && 
           lower_sign = neg && 
           deriv_sign = neg then INFERISIGN_NEG_NEG_NEG
        (* Neg Zero *)
        else if upper_sign = neg && 
           lower_sign = zero && 
           deriv_sign = pos then INFERISIGN_NEG_ZERO_POS
        else if upper_sign = neg && 
           lower_sign = zero && 
           deriv_sign = neg then INFERISIGN_NEG_ZERO_NEG
        (* Zero Pos *)
        else if upper_sign = zero && 
           lower_sign = pos && 
           deriv_sign = pos then INFERISIGN_ZERO_POS_POS
        else if upper_sign = zero && 
           lower_sign = pos && 
           deriv_sign = neg then INFERISIGN_ZERO_POS_NEG
        (* Zero Neg *)
        else if upper_sign = zero && 
           lower_sign = neg && 
           deriv_sign = pos then INFERISIGN_ZERO_NEG_POS
        else if upper_sign = zero && 
           lower_sign = neg && 
           deriv_sign = neg then INFERISIGN_ZERO_NEG_NEG
        (* Zero Zero *)
        else if upper_sign = zero && 
           lower_sign = zero && 
           deriv_sign = pos then INFERISIGN_ZERO_ZERO_POS
        else if upper_sign = zero && 
           lower_sign = zero && 
           deriv_sign = neg then INFERISIGN_ZERO_ZERO_NEG
        else failwith "bad signs in thm";;


let tvars,tdiff,tmat,tex = ref [],ref TRUTH,ref TRUTH,ref [];;
(*
  let vars,diff_thm,mat_thm,ex_thms = !tvars,!tdiff,!tmat,!tex
INFERISIGN vars diff_thm mat_thm ex_thms

let vars,diff_thm,mat_thm,ex_thms = vars, pdiff_thm, mat_thm''', ((v1,exthm1)::(v2,exthm2)::ex_thms) 
*)

let rec INFERISIGN =
  let real_app = `APPEND:real list -> real list -> real list` in 
  let sign_app = `APPEND:(sign list) list -> (sign list) list -> (sign list) list` in
  let real_len = `LENGTH:real list -> num` in 
  let sign_len = `LENGTH:(sign list) list -> num` in
  let unknown = `Unknown` in
  let pos = `Pos` in
  let zero = `Zero` in
  let neg = `Neg` in
  let num_mul = `( * ):num -> num -> num` in
  let num_add = `( + ):num -> num -> num` in
  let real_ty = `:real` in
  let one = `1` in
  let two = `2` in
  let f = `F` in
  let imat = `interpmat` in
  let sl_ty = `:sign list` in
  fun vars diff_thm mat_thm ex_thms -> 
    try 
      tvars := vars;
      tdiff := diff_thm;
      tmat := mat_thm; 
      tex := ex_thms; 
      let pts,ps,sgns = dest_interpmat (concl mat_thm) in
      let pts' = dest_list pts in
      if pts' = [] then mat_thm,ex_thms else
      let sgns' = dest_list sgns in
      let sgnl = map dest_list sgns' in
      let i = get_index (fun x -> hd x = unknown) sgnl in
      if i mod 2 = 1 then failwith "bad shifted matrix" else
      let p::p'::_ = dest_list ps in
      let p_thm = ABS (hd vars) (POLY_ENLIST_CONV vars (snd(dest_abs p))) in
      let p'_thm = ONCE_REWRITE_RULE[GSYM diff_thm] (ABS (hd vars) (POLY_ENLIST_CONV vars (snd(dest_abs p')))) in
      let pts1,qts1 = chop_list (i / 2 - 1) pts' in
      let ps_thm = REWRITE_CONV[p_thm;p'_thm] ps in 
      let pts2 = mk_list(pts1,real_ty) in
      let pts3 = mk_comb(mk_comb(real_app,pts2),mk_list(qts1,real_ty)) in
      let pts_thm = prove(mk_eq(pts,pts3),REWRITE_TAC[APPEND]) in
      let sgns1,rgns1 = chop_list (i - 1) sgns' in
      let sgns2 = mk_list(sgns1,sl_ty) in
      let sgns3 = mk_comb(mk_comb(sign_app,sgns2),mk_list(rgns1,sl_ty)) in
      let sgns_thm = prove(mk_eq(sgns,sgns3),REWRITE_TAC[APPEND]) in
      let len1 = mk_comb(sign_len,sgns2) in
      let len2 = mk_binop num_add (mk_binop num_mul two (mk_comb(real_len,pts2))) one in
      let len_thm = prove(mk_eq(len1,len2),REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
      let mat_thm1 = MK_COMB(MK_COMB((AP_TERM imat pts_thm), ps_thm),sgns_thm) in
      let mat_thm2 = EQ_MP mat_thm1 mat_thm in 
      let upper_sign = hd (ith (i - 1) sgnl) in
      let lower_sign = hd (ith (i + 1) sgnl) in
      let deriv_sign = hd (tl (ith i sgnl)) in
      let mp_thm = get_mp upper_sign lower_sign deriv_sign in
      let mat_thm3 = MATCH_MP (MATCH_MP mp_thm mat_thm2) len_thm in 
      let mat_thm4 = REWRITE_RULE[GSYM p_thm;GSYM p'_thm;APPEND] mat_thm3 in
      let c = concl mat_thm4 in
      if c = f then raise (Isign (mat_thm4,ex_thms)) else
      if not (is_exists c) then 
        INFERISIGN vars diff_thm mat_thm4 ex_thms else
      let x,bod = dest_exists c in
      let x' = new_var real_ty in  
      let assume_thm = ASSUME (subst [x',x] bod) in
        INFERISIGN vars diff_thm assume_thm ((x',mat_thm4)::ex_thms)
  with 
    Failure "get_index" -> mat_thm,ex_thms
  | Failure x -> failwith ("INFERISIGN: " ^ x);;

(* 
let vars,diff_thm,mat_thm,ex_thms =  vars,pdiff_thm, mat_thm''',[]

let mat_thm = ASSUME ` interpmat [x_25; x1; x2; x4; x5; x_26]
     [\x. &1 + x * (&1 + x * (&1 + x * &1)); \x. &1 + x * (&2 + x * &3); 
     \x. &2 + x * (-- &3 + x * &1); \x. -- &4 + x * (&0 + x * &1)]
     [[Neg; Pos; Pos; Pos]; 
      [Neg; Pos; Pos; Pos]; 
      [Unknown; Pos; Pos; Pos]; 
      [Pos; Pos; Pos; Zero]; 
      [Unknown; Neg; Pos; Neg]; 
      [Unknown; Neg; Neg; Neg]; 
      [Unknown; Neg; Pos; Neg];
      [Pos; Zero; Zero; Neg]; 
      [Unknown; Pos; Neg; Neg]; 
      [Pos; Pos; Zero; Zero]; 
      [Unknown; Pos; Pos; Pos];
      [Pos; Pos; Pos; Pos]; 
      [Pos; Pos; Pos; Pos]]`

*)


(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let INFERISIGN vars diff_thm mat_thm ex_thms = 
  let start_time = Sys.time() in
  let res = INFERISIGN vars diff_thm mat_thm ex_thms in
    inferisign_timer +.= (Sys.time() -. start_time);
    res;;

(* {{{ Examples *)

(*
let is_thms = isigns_thms'''

let vars,diff_thm,mat_thm =  
[`w:real`; `z:real`; `y:real`; `x:real`],
ASSUME `poly_diff [&0 + y * (&0 + x * &1); &0 + z * -- &1] = [&0 + z * -- &1]`,
ASSUME `interpmat [x_178; x_179]
     [\w. (&0 + y * (&0 + x * &1)) + w * (&0 + z * -- &1); \w. &0 + z * -- &1]
     [[Pos; Neg]; [Pos; Neg]; [Unknown; Neg]; [Neg; Neg]; [Neg; Neg]]`

INFERISIGN vars pdiff_thm mat_thm

let diff
let vars,diff_thm,mat_thm = 



let vars,diff_thm,mat_thm = 
[`x:real`],
ASSUME `poly_diff [&0; &2; &0; &4] = [&2; &0; &12]`,
ASSUME `interpmat [x_79; x_68; x_80]
        [\x. &0 + x * (&2 + x * (&0 + x * &4)); \x. &2 + x * (&0 + x * &12); 
        \x. &4 + x * (&0 + x * &2)]
        [[Neg; Pos; Pos]; [Neg; Pos; Pos]; [Unknown; Pos; Pos]; [Unknown; Pos; Pos]; [Unknown; Pos; Pos]; [Pos; Pos; Pos]; [Pos; Pos; Pos]]`



let mat_thm = mat_thm'''
let diff_thm = pdiff_thm
INFERISIGN vars pdiff_thm mat_thm'''

let diff_thm = POLY_DIFF_CONV `poly_diff [&1; &1; &1; &1]`;;

let vars = [`x:real`]

let mat_thm = ASSUME
  `interpmat 
     [xminf; x1; x4; x5; xinf]
     [\x. &1 + x * (&1 + x * (&1 + x * &1)); \x. &1 + x * (&2 + x * &3); \x. &2 + x * (-- &3 + x * &1); \x. -- &4 + x * (&0 + x * &1)]
     [[Neg; Pos; Pos; Pos];      
      [Neg; Pos; Pos; Pos];      
      [Unknown; Pos; Pos; Pos];  
      [Neg; Pos; Pos; Zero];     
      [Unknown; Pos; Pos; Neg];  
      [Pos; Pos; Zero; Neg];     
      [Unknown; Pos; Neg; Neg];  
      [Pos; Pos; Zero; Zero];    
      [Unknown; Pos; Pos; Pos];  
      [Pos; Pos; Pos; Pos];      
      [Pos; Pos; Pos; Pos]]`;;     

let mat_thm1,_ = INFERISIGN vars diff_thm mat_thm []

*)
(* }}} *)
