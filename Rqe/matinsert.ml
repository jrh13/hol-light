
let ROWINSERT =
  let lxt = `\x:real. T` in
  fun i const_thm interpsigns_thm -> 
    let isigns_thms = interpsigns_thms2 interpsigns_thm in
    let isigns_thm = hd isigns_thms in
    let set,_,_ = 
      if concl isigns_thm = t_tm then lxt,t_tm,t_tm else 
        dest_interpsign (hd isigns_thms) in
    let const_thm' = MATCH_MP (ISPEC set matinsert_lem0) const_thm in 
    let const_thm'' = PURE_REWRITE_RULE[GSYM interpsign] const_thm' in
    let isigns_thms' = insertat i const_thm'' isigns_thms in 
    let isigns_thms'' = if isigns_thm = TRUTH then butlast isigns_thms' else isigns_thms' in
      mk_interpsigns isigns_thms'';;

let MATINSERT vars i const_thm cont mat_thm =
  let const_thm' = GEN (hd vars) const_thm in
  let rol_thm,all2_thm = interpmat_thms mat_thm in
  let part_thm = PARTITION_LINE_CONV (snd (dest_comb (concl rol_thm))) in
  let isigns_thms = CONJUNCTS(REWRITE_RULE[ALL2;part_thm] all2_thm) in
  let isigns_thms' = map (ROWINSERT i const_thm') isigns_thms in
  let all2_thm' = mk_all2_interpsigns part_thm isigns_thms' in
  let mat_thm' = mk_interpmat_thm rol_thm all2_thm' in
    cont mat_thm';;



(* ---------------------------------------------------------------------- *)
(*  Opt                                                                   *)
(* ---------------------------------------------------------------------- *)

(* OPT FAILED... slightly slower, even with hashtables *)  

let rec mk_suc = 
  let zero = `0` in
  let suc = `SUC` in
  fun n -> 
    match n with 
      0 -> zero 
    | n -> mk_comb(suc,mk_suc (n-1));;

let rec MK_SUC = 
  let f n = prove(mk_eq(mk_small_numeral n,mk_suc n),ARITH_TAC) in
  let size = 100 in
  let range = 0--size in
  let suc_tbl = Hashtbl.create size in
  map2 (Hashtbl.add suc_tbl) range (map f range);
  fun n -> 
    try Hashtbl.find suc_tbl n with _ -> f n;;

let PL_LENGTH = 
  let pl_tm = `partition_line` in
  let len_tm = `LENGTH:(real -> bool) list -> num` in
  fun pts -> 
    let lpts = mk_comb(len_tm,mk_comb(pl_tm,pts)) in
    let lthm = ARITH_SIMP_CONV[PARTITION_LINE_LENGTH;LENGTH] lpts in
    let pts' = snd(dest_eq(concl lthm)) in
    let n = dest_small_numeral pts' in
    let suc_thm = MK_SUC n in
      TRANS lthm suc_thm;;


let rec MK_LT = 
  let f(n1,n2) = prove(mk_binop nle (mk_suc n1) (mk_suc n2),ARITH_TAC) in
  let size1 = 20 in
  let size2 = 20 in
  let range1 = 0--size1 in
  let range2 = 0--size2 in
  let range = filter (fun (x,y) -> x <= y) (allpairs (fun x y -> x,y) range1 range2) in
  let suc_tbl = Hashtbl.create (size1 * size2) in
  map2 (Hashtbl.add suc_tbl) range (map f range);
  fun (n1,n2) -> 
    try Hashtbl.find suc_tbl (n1,n2) with _ -> f(n1,n2);;


(*
let vars,i,const_thm,mat_thm = !ti,!tconst,!tmat
#trace MATINSERT
*)


(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let MATINSERT vars i const_thm cont mat_thm =
  let start_time = Sys.time() in
  let res = MATINSERT vars i const_thm cont mat_thm in
    matinsert_timer +.= (Sys.time() -. start_time);
    res;;



(*

let vars,i,const_thm, cont,mat_thm =
[ry;rx],
0,
ASSUME `-- &1 < &0`,
I,
ASSUME `interpmat [x_24] [\x. &0 + x * &1] [[Neg]; [Zero]; [Pos]]`

MATINSERT vars i const_thm cont mat_thm


let vars,i,const_thm, cont,mat_thm =
[ry;rx],
0,
ASSUME `&0 + x * &1 < &0`,
I,
ASSUME `interpmat [] [\y. &1] [[Pos]]`

MATINSERT vars i const_thm cont mat_thm


let vars,i,const_thm, cont,mat_thm =
[`x:real`; `a:real`; `b:real`; `c:real`],
0,
ASSUME `&0 + a * &2 < &0`,
I,
ASSUME `interpmat [x_408] [\x. (&0 + b * &1) + x * (&0 + a * &2)] [[Pos]; [Zero]; [Neg]]`

MATINSERT vars i const_thm cont mat_thm

*)
