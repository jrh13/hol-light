let TRAPOUT cont mat_thm ex_thms fm =
  try
    cont mat_thm ex_thms
  with Isign (false_thm,ex_thms) ->
    let ftm = mk_eq(fm,f_tm) in
    let fthm = CONTR ftm false_thm in
    let ex_thms' = sort (fun x y -> xterm_lt (fst y) (fst x)) ex_thms in
    let fthm' = rev_itlist CHOOSE ex_thms' fthm in
      fthm';;

let get_repeats l =
  let rec get_repeats l seen ind =
    match l with
        [] -> []
      | h::t ->
          if mem h seen then ind::get_repeats t seen (ind + 1)
          else get_repeats t (h::seen) (ind + 1) in
    get_repeats l [] 0;;

let subtract_index l =
  let rec subtract_index l ind =
    match l with
        [] -> []
      | h::t -> (h - ind):: (subtract_index t (ind + 1)) in
    subtract_index l 0;;

(*
subtract_index (get_repeats [1; 2; 1; 2 ; 3])
*)

let remove_column n isigns_thm =
  let thms = interpsigns_thms2 isigns_thm in
  let l,r = chop_list n thms in
  let thms' = l @ tl r in
    mk_interpsigns thms';;

let REMOVE_COLUMN n mat_thm =
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let ints,part,signs = dest_all2 (concl all_thm) in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb part)) in
  let isigns_thms = CONJUNCTS (REWRITE_RULE[ALL2;part_thm] all_thm) in
  let isigns_thms' = map (remove_column n) isigns_thms in
  let all_thm' = mk_all2_interpsigns part_thm isigns_thms' in
  let all_thm'' = REWRITE_RULE[GSYM part_thm] all_thm' in
  let mat_thm' = mk_interpmat_thm rol_thm all_thm'' in
    mat_thm';;

let SETIFY_CONV mat_thm =
  let _,pols,_ = dest_interpmat(concl mat_thm) in
  let pols' = dest_list pols in
  let sols = setify (dest_list pols) in
  let indices = map (fun p -> try index p sols with _ -> failwith "SETIFY: no index") pols' in
  let subtract_cols = subtract_index (get_repeats indices) in
    rev_itlist REMOVE_COLUMN subtract_cols mat_thm;;


(*
SETIFY_CONV
(ASSUME `interpmat [] [(\x. x + &1); (\x. x + &1); (\x. x + &2); (\x. x + &3); (\x. x + &1); (\x. x + &2)][[Pos; Pos; Pos; Pos; Neg; Zero]]`)

*)
(*
let duplicate_column i j isigns_thm =
  let thms = interpsigns_thms2 isigns_thm in
  let col = ith i thms in
  let l,r = chop_list j thms in
  let thms' = l @ (col :: r) in
    mk_interpsigns thms';;

let DUPLICATE_COLUMN i j mat_thm =
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let ints,part,signs = dest_all2 (concl all_thm) in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb part)) in
  let isigns_thms = CONJUNCTS (REWRITE_RULE[ALL2;part_thm] all_thm) in
  let isigns_thms' = map (duplicate_column i j) isigns_thms in
  let all_thm' = mk_all2_interpsigns part_thm isigns_thms' in
  let all_thm'' = REWRITE_RULE[GSYM part_thm] all_thm' in
  let mat_thm' = mk_interpmat_thm rol_thm all_thm'' in
    mat_thm';;
*)

let duplicate_columns new_cols isigns_thm =
  let thms = interpsigns_thms2 isigns_thm in
  let thms' = map (fun i -> el i thms) new_cols in
    mk_interpsigns thms';;

let DUPLICATE_COLUMNS mat_thm ls =
  if ls = [] then if mat_thm = empty_mat then empty_mat else failwith "empty duplication list" else
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let ints,part,signs = dest_all2 (concl all_thm) in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb part)) in
  let isigns_thms = CONJUNCTS (REWRITE_RULE[ALL2;part_thm] all_thm) in
  let isigns_thms' = map (duplicate_columns ls) isigns_thms in
  let all_thm' = mk_all2_interpsigns part_thm isigns_thms' in
  let all_thm'' = REWRITE_RULE[GSYM part_thm] all_thm' in
  let mat_thm' = mk_interpmat_thm rol_thm all_thm'' in
    mat_thm';;


let DUPLICATE_COLUMNS mat_thm ls =
  let start_time = Sys.time() in
  let res = DUPLICATE_COLUMNS mat_thm ls in
    duplicate_columns_timer +.= (Sys.time() -. start_time);
    res;;


let UNMONICIZE_ISIGN vars monic_thm isign_thm =
  let _,_,sign = dest_interpsign isign_thm in
  let const = (fst o dest_mult o lhs o concl) monic_thm in
  let const_thm = SIGN_CONST const in
  let op,_,_ = get_binop (concl const_thm) in
  let mp_thm =
    if op = rgt then
      if sign = spos_tm then gtpos
      else if sign = sneg_tm then gtneg
      else if sign = szero_tm then gtzero
      else failwith "bad sign"
    else if op = rlt then
      if sign = spos_tm then ltpos
      else if sign = sneg_tm then ltneg
      else if sign = szero_tm then ltzero
      else failwith "bad sign"
    else (failwith "bad op") in
  let monic_thm' = GEN (hd vars) monic_thm in
    MATCH_MPL[mp_thm;monic_thm';const_thm;isign_thm];;

let UNMONICIZE_ISIGNS vars monic_thms isigns_thm =
  let isign_thms = interpsigns_thms2 isigns_thm in
  let isign_thms' = map2 (UNMONICIZE_ISIGN vars) monic_thms isign_thms in
    mk_interpsigns isign_thms';;

let UNMONICIZE_MAT vars monic_thms mat_thm =
  if monic_thms = [] then mat_thm else
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let ints,part,signs = dest_all2 (concl all_thm) in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb part)) in
  let consts = map (fst o dest_mult o lhs o concl) monic_thms in
  let isigns_thms = CONJUNCTS (REWRITE_RULE[ALL2;part_thm] all_thm) in
  let isigns_thms' = map (UNMONICIZE_ISIGNS vars monic_thms) isigns_thms in
  let all_thm' = mk_all2_interpsigns part_thm isigns_thms' in
  let all_thm'' = REWRITE_RULE[GSYM part_thm] all_thm' in
  let mat_thm' = mk_interpmat_thm rol_thm all_thm'' in
    mat_thm';;

let UNMONICIZE_MAT vars monic_thms mat_thm =
  let start_time = Sys.time() in
  let res = UNMONICIZE_MAT vars monic_thms mat_thm in
    unmonicize_mat_timer +.= (Sys.time() -. start_time);
    res;;


(* {{{ Examples *)

(*
let vars,monic_thms,mat_thm =
 [], [], empty_mat


let monic_thm = hd monic_thms
length isigns_thms

MONIC_CONV [rx] `&1 + x * (&1 + x * (&1 + x * &7))`

let isign_thm = hd isign_thms

let isigns_thm = hd isigns_thms

    mk_interpsigns [TRUTH];;
let ls = [0;1;2;0;1;2]
 let mat_thm,ls = empty_mat,[]
1,3,

DUPLICATE_COLUMNS
(ASSUME `interpmat [] [(\x. x + &1); (\x. x + &1); (\x. x + &2); (\x. x + &3); (\x. x + &1); (\x. x + &2)][[Pos; Pos; Pos; Pos; Neg; Zero]]`)
[5]

duplicate_columns [] (ASSUME `interpsigns [] (\x. T) []`)
let new_cols, isigns_thm = [],(ASSUME `interpsigns [] (\x. T) []`)

let isigns_thm = hd isigns_thms

*)

(* }}} *)


let SWAP_HEAD_COL_ROW i isigns_thm =
  let s_thms = interpsigns_thms2 isigns_thm in
  let s_thms' = insertat i (hd s_thms) (tl s_thms) in
    mk_interpsigns s_thms';;

let SWAP_HEAD_COL i mat_thm =
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let ints,part,signs = dest_all2 (concl all_thm) in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb part)) in
  let isigns_thms = CONJUNCTS (REWRITE_RULE[ALL2;part_thm] all_thm) in
  let isigns_thms' = map (SWAP_HEAD_COL_ROW i) isigns_thms in
  let all_thm' = mk_all2_interpsigns part_thm isigns_thms' in
    mk_interpmat_thm rol_thm all_thm';;

let SWAP_HEAD_COL i mat_thm =
  let start_time = Sys.time() in
  let res = SWAP_HEAD_COL i mat_thm in
    swap_head_col_timer +.= (Sys.time() -. start_time);
    res;;


let LENGTH_CONV =
  let alength_tm = `LENGTH:(A list) -> num` in
  fun tm ->
    try
      let ty = type_of tm in
      let lty,[cty] = dest_type ty in
        if lty <> "list" then failwith "LENGTH_CONV: not a list" else
        let ltm = mk_comb(inst[cty,aty] alength_tm,tm) in
        let lthm = REWRITE_CONV[LENGTH] ltm in
          MATCH_MP main_lem000 lthm
    with _ -> failwith "LENGTH_CONV";;

let LAST_NZ_CONV =
  let alast_tm = `LAST:(A list) -> A` in
  fun nz_thm tm ->
    try
      let ty = type_of tm in
      let lty,[cty] = dest_type ty in
      if lty <> "list" then failwith "LAST_NZ_CONV: not a list" else
        let ltm = mk_comb(inst[cty,aty] alast_tm,tm) in
        let lthm = REWRITE_CONV[LAST;NOT_CONS_NIL] ltm in
          MATCH_MPL[main_lem001;nz_thm;lthm]
    with _ -> failwith "LAST_NZ_CONV";;

let rec first f l =
  match l with
      [] -> failwith "first"
    | h::t -> if can f h then f h else first f t;;

let NEQ_RULE thm =
  let thms = CONJUNCTS main_lem002 in
    first (C MATCH_MP thm) thms;;

(*
NEQ_CONV (ARITH_RULE `~(&11 <= &2)`)
*)

let NORMAL_LIST_CONV nz_thm tm =
  let nz_thm' = NEQ_RULE nz_thm in
  let len_thm = LENGTH_CONV tm in
  let last_thm = LAST_NZ_CONV nz_thm' tm in
  let cthm = CONJ len_thm last_thm in
    MATCH_EQ_MP (GSYM (REWRITE_RULE[GSYM NEQ] NORMAL_ID)) cthm;;

(*
|- poly_diff [&0; &0; &0 + a * &1] = [&0; &0 + a * &2]
let tm = `poly_diff [&0; &0 + a * &1]`
*)
let pdiff_tm = `poly_diff`;;
let GEN_POLY_DIFF_CONV vars tm =
  let thm1 = POLY_ENLIST_CONV vars tm in
  let l,x = dest_poly (rhs (concl thm1)) in
  let thm2 = CANON_POLY_DIFF_CONV (mk_comb(pdiff_tm,l)) in
  let thm3 = CONV_RULE (RAND_CONV (LIST_CONV (POLYNATE_CONV vars))) thm2 in
    thm3;;

(*
   if \x. p = \x. q, where \x. p is the leading polynomial
   replace p by q in mat_thm,
*)


(*
let peq,mat_thm = !rppeq,!rpmat
*)
let rppeq,rpmat = ref TRUTH,ref TRUTH;;
let REPLACE_POL =
  let imat_tm = `interpmat` in
  fun peq mat_thm ->
    rppeq := peq;
    rpmat := mat_thm;
    let pts,pols,sgnll = dest_interpmat (concl mat_thm) in
    let rep_p = lhs(concl peq) in
    let i = try index rep_p (dest_list pols) with _ -> failwith "REPLACE_POL: index" in
    let thm1 = EL_CONV (fun x -> GEN_REWRITE_CONV I [peq] x) i pols in
      end_itlist (C (curry MK_COMB)) (rev [REFL imat_tm;REFL pts;thm1;REFL sgnll]);;


let REPLACE_POL peq mat_thm =
  let start_time = Sys.time() in
  let res = REPLACE_POL peq mat_thm in
    replace_pol_timer +.= (Sys.time() -. start_time);
    res;;

(* {{{ Examples *)

(*

let peq,mat_thm =
ASSUME  `(\x. &0) =
        (\x. &0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)))`,
ASSUME `interpmat [x_44] [\x. (&0 + b * &1) + x * (&0 + a * &2); \x. &0]
        [[Pos; Zero]; [Zero; Zero]; [Neg; Zero]]`

let peq = ASSUME `(\x. &1 + x * (&1 + x * (&1 + x * &1))) = (\x. &1 + x)`

REPLACE_POL peq mat_thm

is_constant [`y:real`] `&1 + x * -- &1`

let vars,pols,cont,sgns,ex_thms =
[`c:real`; `b:real`; `a:real`],
[`&0 + c * &1`],
(fun x y -> x),
[ASSUME `&0 + b * (&0 + b * -- &1) = &0`;
ASSUME ` &0 + b * (&0 + b * (&0 + a * -- &1)) = &0`;
ASSUME  `&0 + a * (&0 + a * &1) = &0`;ASSUME `&0 + b * &1 = &0`;
ASSUME `&0 + a * &1 = &0`; ASSUME ` &1 > &0`],
[]

*)

(* }}} *)



(* ---------------------------------------------------------------------- *)
(*  Factoring                                                             *)
(* ---------------------------------------------------------------------- *)

let UNFACTOR_ISIGN vars xsign_thm pol isign_thm =
  let x = hd vars in
  let k,pol' = weakfactor x pol in
  if k = 0 then isign_thm else
  let fact_thm = GEN x (GSYM (WEAKFACTOR_CONV x pol)) in
  let par_thm = PARITY_CONV (mk_small_numeral k) in
  let _,_,xsign = dest_interpsign xsign_thm in
  let _,_,psign = dest_interpsign isign_thm in
  let parity,_ = dest_comb (concl par_thm) in
  if xsign = spos_tm then
    let mp_thm =
      if psign = spos_tm then factor_pos_pos
      else if psign = sneg_tm then factor_pos_neg
      else if psign = szero_tm then factor_pos_zero
      else failwith "bad sign" in
      let ret = BETA_RULE(MATCH_MPL[mp_thm;xsign_thm;isign_thm]) in
        MATCH_MP ret fact_thm
  else if xsign = szero_tm then
    let k_thm = prove(mk_neg(mk_eq(mk_small_numeral k,nzero)),ARITH_TAC) in
    let mp_thm =
      if psign = spos_tm then factor_zero_pos
      else if psign = sneg_tm then factor_zero_neg
      else if psign = szero_tm then factor_zero_zero
      else failwith "bad sign" in
      let ret = BETA_RULE(MATCH_MPL[mp_thm;xsign_thm;isign_thm;k_thm]) in
        MATCH_MP ret fact_thm
  else if xsign = sneg_tm && parity = even_tm then
    let k_thm = prove(mk_neg(mk_eq(mk_small_numeral k,nzero)),ARITH_TAC) in
    let mp_thm =
      if psign = spos_tm then factor_neg_even_pos
      else if psign = sneg_tm then factor_neg_even_neg
      else if psign = szero_tm then factor_neg_even_zero
      else failwith "bad sign" in
      let ret = BETA_RULE(MATCH_MPL[mp_thm;xsign_thm;isign_thm;par_thm;k_thm]) in
        MATCH_MP ret fact_thm
  else if xsign = sneg_tm && parity = odd_tm then
    let k_thm = prove(mk_neg(mk_eq(mk_small_numeral k,nzero)),ARITH_TAC) in
    let mp_thm =
      if psign = spos_tm then factor_neg_odd_pos
      else if psign = sneg_tm then factor_neg_odd_neg
      else if psign = szero_tm then factor_neg_odd_zero
      else failwith "bad sign" in
      let ret = BETA_RULE(MATCH_MPL[mp_thm;xsign_thm;isign_thm;par_thm;k_thm]) in
        MATCH_MP ret fact_thm
  else failwith "bad something...";;

(* {{{ Examples *)

(*

let vars,xsign_thm,pol,isign_thm =
[ry;rx],
`interpsign (\x. x < x1) (\x. x) Pos`,
ASSUME `interpsign (\x. x < x_254) (\y. &0 + y * &1) Neg`

`\x. &0 + x * (&4 + x * &6)`,
ASSUME `interpsign (\x. x < x1) (\x. &4 + x * &6) Pos`


let xsign_thm,pol,isign_thm =
ASSUME `interpsign (\x. x < x1) (\x. x) Pos`,
`\x. &0 + x * (&4 + x * &6)`,
ASSUME `interpsign (\x. x < x1) (\x. &4 + x * &6) Pos`


*)

(* }}} *)

let UNFACTOR_ISIGNS vars pols isigns_thm =
  let isign_thms = interpsigns_thms2 isigns_thm in
  let isign_thms' = map2 (UNFACTOR_ISIGN vars (hd isign_thms)) pols (tl isign_thms) in
    mk_interpsigns isign_thms';;

let UNFACTOR_MAT vars pols mat_thm =
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let ints,part,signs = dest_all2 (concl all_thm) in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb part)) in
  let isigns_thms = CONJUNCTS (REWRITE_RULE[ALL2;part_thm] all_thm) in
  let isigns_thms' = map (UNFACTOR_ISIGNS vars pols) isigns_thms in
  let all_thm' = mk_all2_interpsigns part_thm isigns_thms' in
  let all_thm'' = REWRITE_RULE[GSYM part_thm] all_thm' in
  let mat_thm' = mk_interpmat_thm rol_thm all_thm'' in
    mat_thm';;

let UNFACTOR_MAT vars pols mat_thm =
  let start_time = Sys.time() in
  let res = UNFACTOR_MAT vars pols mat_thm in
    unfactor_mat_timer +.= (Sys.time() -. start_time);
    res;;

(* {{{ Examples *)

(*
#untrace UNFACTOR_ISIGN

let isigns_thm = el 0 isigns_thms
UNFACTOR_ISIGNS pols isigns_thm

let isign_thm = el 1 isign_thm

pols
  let isigns_thms' = map (UNFACTOR_ISIGNS pols) isigns_thms in

let xsign_thm = hd isign_thms
let xsign_thm = ASSUME `interpsign (\x. x < x1) (\x. x) Neg`
let isign_thm = hd (tl isign_thms)
let pol = hd pols
let pol = `\x. &0 + x * (&0 + x * (&0 + x * (&0 + y * &1)))`

let isigns_thm = hd isigns_thms
let vars = [rx;ry;rz]


let pols =
  [`\x. &0 + x * (&0 + x * (&0 + y * &1))`; `\x. &0 + x * (&4 + x * &6)`; `\x. &3 + x * (&6 + x * &9)`;
      `\x. &0 + x * (&0 + x * (&0 + x * (&0 + z * &1)))`; `\x. -- &4 + x * (&0 + x * &1)`]

let mat_thm = ASSUME
  `interpmat [x1; x2; x3; x4; x5]
  [\x. x; \x. &0 + y * &1; \x. &4 + x * &6; \x. &3 + x * (&6 + x * &9);
      \x. &0 + z * &1; \x. -- &4 + x * (&0 + x * &1)]
      [[Pos; Pos; Pos; Neg; Neg; Neg];
      [Neg; Pos; Zero; Zero; Neg; Neg];
      [Neg; Pos; Neg; Pos; Neg; Neg];
      [Neg; Pos; Neg; Pos; Neg; Zero];
      [Neg; Pos; Neg; Pos; Neg; Pos];
      [Zero; Pos; Neg; Pos; Zero; Pos];
      [Pos; Pos; Neg; Pos; Pos; Pos];
      [Pos; Zero; Neg; Pos; Pos; Pos];
      [Pos; Neg; Neg; Pos; Pos; Pos];
      [Pos; Zero; Zero; Pos; Pos; Pos];
      [Pos; Pos; Pos; Pos; Pos; Pos]]`

UNFACTOR_MAT pols mat_thm

*)

(* }}} *)

let message_time s f x =
  report s;
  time f x;;


(* ---------------------------------------------------------------------- *)
(*  Matrix                                                                *)
(* ---------------------------------------------------------------------- *)

let matrix_count,splitzero_count,splitsigns_count,monicize_count = ref 0,ref 0,ref 0,ref 0;;
let reset_counts() = matrix_count := 0;splitzero_count := 0;splitsigns_count := 0;monicize_count := 0;;
let print_counts() = !matrix_count,!splitzero_count,!splitsigns_count,!monicize_count;;


(*
let vars,dun,pols,cont,sgns,ex_thms,fm = !szvars,!szdun,!szpols,!szcont,!szsgns,!szex_thms,!szfm
*)


let rec MATRIX vars pols cont sgns ex_thms fm =
  incr matrix_count;
  if pols = [] then TRAPOUT cont empty_mat [] fm else
  if exists (is_constant vars) pols then
    let p = find (is_constant vars) pols in
    let i = try index p pols with _ -> failwith "MATRIX: no such pol" in
    let pols1,pols2 = chop_list i pols in
    let pols' = pols1 @ tl pols2 in
    let cont' = MATINSERT vars i (FINDSIGN vars sgns p) cont in
      MATRIX vars pols' cont' sgns ex_thms fm
  else
    let kqs = map (weakfactor (hd vars)) pols in
      if exists (fun (k,q) -> k <> 0 && not(is_constant vars q)) kqs then
        let pols' = poly_var(hd vars) :: map snd kqs in
        let ks = map fst kqs in
        let cont' mat_thm ex_thms = cont (UNFACTOR_MAT vars pols mat_thm) ex_thms in
          MATRIX vars pols' cont' sgns ex_thms fm
      else
      let d = itlist (max o degree_ vars) pols (-1) in
      let p = find (fun p -> degree_ vars p = d) pols in
      let pl_thm = POLY_ENLIST_CONV vars p in
      let pl = rhs(concl pl_thm) in
      let l,x = dest_poly pl in
      let pdiff_thm = GEN_POLY_DIFF_CONV vars p in
      let p'l = rhs (concl pdiff_thm) in
      let p' = mk_comb(mk_comb(poly_tm,p'l),hd vars) in
      let p'thm = (POLY_DELIST_CONV THENC (POLYNATE_CONV vars)) p' in
      let p'c = rhs (concl p'thm) in
      let hdp' = last (dest_list p'l) in
      let sign_thm = FINDSIGN vars sgns hdp' in
      let normal_thm = NORMAL_LIST_CONV sign_thm p'l in
      let i = try index p pols with _ -> failwith "MATRIX: no such pol1" in
      let qs = let p1,p2 = chop_list i pols in p'c::p1 @ tl p2 in
      let gs,div_thms = unzip (map (PDIVIDES vars sgns p) qs) in
      let cont' mat_thm = cont (SWAP_HEAD_COL i mat_thm) in
      let dedcont mat_thm ex_thms =
        DEDMATRIX vars sgns div_thms pdiff_thm normal_thm cont' mat_thm ex_thms in
        SPLITZERO vars qs gs dedcont sgns ex_thms fm

and SPLITZERO vars dun pols cont sgns ex_thms fm =
  incr splitzero_count;
  match pols with
      [] -> SPLITSIGNS vars [] dun cont sgns ex_thms fm
    | p::ops ->
        if p = rzero then
          let cont' mat_thm ex_thms = MATINSERT vars (length dun) (REFL rzero) cont mat_thm ex_thms in
            SPLITZERO vars dun ops cont' sgns ex_thms fm
        else
          let hp = behead vars p in
          let h = head vars p in
          let nzcont =
            let tmp = SPLITZERO vars (dun@[p]) ops cont in
              fun sgns ex_thms -> tmp sgns ex_thms fm in
          let zcont =
            let tmp = SPLITZERO vars dun (hp :: ops) in
            fun sgns ex_thms ->
              let zthm = FINDSIGN vars sgns h in
              let b_thm = GSYM (BEHEAD vars zthm p) in
              let lam_thm = ABS (hd vars) b_thm in
              let cont' mat_thm ex_thms =
                let mat_thm' = REPLACE_POL (lam_thm) mat_thm in
                let mat_thm'' = MATCH_EQ_MP mat_thm' mat_thm in
                  cont mat_thm'' ex_thms in
                tmp cont' sgns ex_thms fm in
            SPLIT_ZERO (tl vars) sgns (head vars p) zcont nzcont ex_thms

and SPLITSIGNS vars dun pols cont sgns ex_thms fm =
  incr splitsigns_count;
  match pols with
      [] -> MONICIZE vars dun cont sgns ex_thms fm
(*         [] -> MATRIX vars dun cont sgns ex_thms fm *)
    | p::ops ->
        let cont' sgns ex_thms = SPLITSIGNS vars (dun@[p]) ops cont sgns ex_thms fm in
          SPLIT_SIGN (tl vars) sgns (head vars p) cont' cont' ex_thms

and MONICIZE vars pols cont sgns ex_thms fm =
  incr monicize_count;
  let monic_thms = map (MONIC_CONV vars) pols in
  let monic_pols = map (rhs o concl) monic_thms in
  let sols = setify monic_pols in
  let indices = map (fun p -> try index p sols with _ -> failwith "MONICIZE: no such pol") monic_pols in
  let transform mat_thm =
    let mat_thm' = DUPLICATE_COLUMNS mat_thm indices in
(*       mat_thm'  *)
      UNMONICIZE_MAT vars monic_thms mat_thm' in
  let cont' mat_thm ex_thms = cont (transform mat_thm) ex_thms in
    MATRIX vars sols cont' sgns ex_thms fm
;;

(* {{{ Examples *)

(*
let vars,pols,sgns,ex_thms = [],[],[],[]

let mat_thm = mat_thm'
monic_thms

let vars = [rx]
let mat_thm = ASSUME
  `interpmat [x1; x2; x3; x4; x5]
     [(\x. &1 + x * (&2 + x * &3)); (\x. &2 + x * (&4 + x * &6)); \x. &3 + x * (&6 + x * &9); \x. &2 + x * (-- &3 + x * &1); \x. -- &4 + x * (&0 + x * &1); \x. &8 + x * &4]
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
      [Pos; Pos; Pos; Pos; Pos; Pos]]`

let mat_thm = ASSUME
 `interpmat [x1; x2; x3; x4; x5]
  [\x. -- &4 + x * (&0 + x * &1); \x. &2 + x * &1; \x. &2 + x * (-- &3 + x * &1); \x. &1 / &3 + x * (&2 / &3 + x * &1)]
      [[Pos; Pos; Pos; Neg];
      [Pos; Pos; Zero; Zero];
      [Pos; Pos; Neg; Pos];
      [Pos; Pos; Neg; Pos];
      [Pos; Pos; Neg; Pos];
      [Pos; Pos; Neg; Pos];
      [Pos; Pos; Neg; Pos];
      [Pos; Zero; Neg; Pos];
      [Pos; Neg; Neg; Pos];
      [Pos; Zero; Zero; Pos];
      [Pos; Pos; Pos; Pos]]`;;

let vars = [rx]
let pols = [`&1 + x * (&2 + x * &3)`;`&2 + x * (&4 + x * &6)`;`&3 + x * (&6 + x * &9)`; `&2 + x * (-- &3 + x * &1)`;`-- &4 + x * (&0 + x * &1)`;`&8 + x * &4`]


*)
(* }}} *)


(* ---------------------------------------------------------------------- *)
(*  Set up RQE                                                            *)
(* ---------------------------------------------------------------------- *)

let polynomials tm =
  let rec polynomials tm =
    if tm = t_tm || tm = f_tm then []
    else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
      let _,l,r = get_binop tm in polynomials l @ polynomials r
    else if is_neg tm then polynomials (dest_neg tm)
    else if
      can (dest_binop rlt) tm ||
      can (dest_binop rgt) tm ||
      can (dest_binop rle) tm ||
      can (dest_binop rge) tm ||
      can (dest_binop req) tm ||
      can (dest_binop rneq) tm then
        let _,l,_ = get_binop tm in [l]
    else failwith "not a fol atom" in
    setify (polynomials tm);;
(* {{{ Examples *)

(*
let pols = polynomials `(poly [&1; -- &2] x > &0 ==> poly [&1; -- &2] x >= &0 /\ (poly [&8] x = &0)) /\ ~(poly [y] x <= &0)`
*)

(* }}} *)


let BASIC_REAL_QELIM_CONV vars fm =
  let x,bod = dest_exists fm in
  let pols = polynomials bod in
  let cont mat_thm ex_thms =
    let ex_thms' = sort (fun x y -> xterm_lt (fst y) (fst x)) ex_thms in
    let comb_thm = COMBINE_TESTFORMS x mat_thm bod in
    let comb_thm' = rev_itlist CHOOSE ex_thms' comb_thm in
      comb_thm' in
  let ret_thm = SPLITZERO (x::vars) [] pols cont empty_sgns [] fm in
    PURE_REWRITE_RULE[NEQ] ret_thm;;

let REAL_QELIM_CONV fm =
  reset_counts();
  ((LIFT_QELIM_CONV POLYATOM_CONV (EVALC_CONV THENC SIMPLIFY_CONV)
     BASIC_REAL_QELIM_CONV) THENC EVALC_CONV THENC SIMPLIFY_CONV) fm;;

(* ---------------------------------------------------------------------- *)
(*  timers                                                                *)
(* ---------------------------------------------------------------------- *)

