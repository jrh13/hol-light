(* ====================================================================== *)
(*  CONDENSE                                                              *)
(* ====================================================================== *)
(*
let merge_interpsign ord_thm (thm1,thm2,thm3) = 
  let thm1' = BETA_RULE(PURE_REWRITE_RULE[interpsign] thm1) in
  let thm2' = BETA_RULE(PURE_REWRITE_RULE[interpsign] thm2) in 
  let thm3' = BETA_RULE(PURE_REWRITE_RULE[interpsign] thm3) in
  let set1,_,_ = dest_interpsign thm1 in
  let _,s1 = dest_abs set1 in
  let set3,_,_ = dest_interpsign thm3 in
  let _,s3 = dest_abs set3 in
  let gthm = 
    if is_conj s1 && is_conj s3 then gen_thm 
    else if is_conj s1 && not (is_conj s3) then gen_thm_noright 
    else if not (is_conj s1) && is_conj s3 then gen_thm_noleft
    else gen_thm_noboth in
    PURE_REWRITE_RULE[GSYM interpsign] (MATCH_MPL[gthm;ord_thm;thm1';thm2';thm3']);;
*)
(* {{{ Examples *)

(*

length thms
merge_interpsign ord_thm (hd thms)

let thm1,thm2,thm3 = hd thms

let ord_thm = ASSUME `x2 < x3`;;
let thm1 = ASSUME `interpsign (\x. x < x2) [&1; &2; &3] Pos`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Pos`;;
let thm3 = ASSUME `interpsign (\x. x2 < x /\ x < x3) [&1; &2; &3] Pos`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = ASSUME `x1 < x2`;;
let thm1 = ASSUME `interpsign (\x. x1 < x /\ x < x2) [&1; &2; &3] Pos`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Pos`;;
let thm3 = ASSUME `interpsign (\x. x2 < x) [&1; &2; &3] Pos`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = TRUTH;;
let thm1 = ASSUME `interpsign (\x. x < x1) [&1; &2; &3] Pos`;;
let thm2 = ASSUME `interpsign (\x. x = x1) [&1; &2; &3] Pos`;;
let thm3 = ASSUME `interpsign (\x. x1 < x) [&1; &2; &3] Pos`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = ASSUME `x1 < x2 /\ x2 < x3`;;
let thm1 = ASSUME `interpsign (\x. x1 < x /\ x < x2) [&1; &2; &3] Pos`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Pos`;;
let thm3 = ASSUME `interpsign (\x. x2 < x /\ x < x3) [&1; &2; &3] Pos`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = ASSUME `x1 < x3`;;
let thm1 = ASSUME `interpsign (\x. x1 < x /\ x < x2) [&1; &2; &3] Neg`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Neg`;;
let thm3 = ASSUME `interpsign (\x. x2 < x /\ x < x3) [&1; &2; &3] Neg`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = ASSUME `x1 < x3`;;
let thm1 = ASSUME `interpsign (\x. x1 < x /\ x < x2) [&1; &2; &3] Zero`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Zero`;;
let thm3 = ASSUME `interpsign (\x. x2 < x /\ x < x3) [&1; &2; &3] Zero`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = ASSUME `x1 < x3`;;
let thm1 = ASSUME `interpsign (\x. x1 < x /\ x < x2) [&1; &2; &3] Nonzero`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Nonzero`;;
let thm3 = ASSUME `interpsign (\x. x2 < x /\ x < x3) [&1; &2; &3] Nonzero`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;

let ord_thm = ASSUME `x1 < x3`;;
let thm1 = ASSUME `interpsign (\x. x1 < x /\ x < x2) [&1; &2; &3] Unknown`;;
let thm2 = ASSUME `interpsign (\x. x = x2) [&1; &2; &3] Unknown`;;
let thm3 = ASSUME `interpsign (\x. x2 < x /\ x < x3) [&1; &2; &3] Unknown`;;
merge_interpsign ord_thm (thm1,thm2,thm3);;


*)
(* }}} *)
(*
let rec merge_three l1 l2 l3 =
  match l1 with 
      [] -> [] 
    | h::t -> (hd l1,hd l2,hd l3)::merge_three (tl l1) (tl l2) (tl l3);;
*)

(* {{{ Doc *)
(*
  combine_interpsigns
    |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x1 < x /\ x < x2)
      [Unknown; Pos; Pos; Neg]
   |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x = x2)
      [Unknown; Pos; Pos; Neg];
   |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x2 < x /\ x < x3)
      [Unknown; Pos; Pos; Neg];
--> 
   |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x1 < x /\ x < x3)
      [Unknown; Pos; Pos; Neg];
*)
(* }}} *)
(*
let combine_interpsigns ord_thm thm1 thm2 thm3 = 
  let _,_,s1 = dest_interpsigns thm1 in
  let _,_,s2 = dest_interpsigns thm2 in
  let _,_,s3 = dest_interpsigns thm3 in
  if not (s1 = s2) or not (s1 = s3) then failwith "combine_interpsigns: signs not equal" else
  try
    let thms1 = CONJUNCTS(PURE_REWRITE_RULE[interpsigns;ALL2] thm1) in
    let thms2 = CONJUNCTS(PURE_REWRITE_RULE[interpsigns;ALL2] thm2) in
    let thms3 = CONJUNCTS(PURE_REWRITE_RULE[interpsigns;ALL2] thm3) in
    let thms = butlast (merge_three thms1 thms2 thms3) (* ignore the T at end *) in
    let thms' = map (merge_interpsign ord_thm) thms in
      mk_interpsigns thms' 
  with Failure s -> failwith ("combine_interpsigns: " ^ s);;
*)
(* {{{ Examples *)

(*
let thm = combine_interpsigns 
let ord_thm,thm1,thm2,thm3 = ord_thm5 ,ci1 ,ci2 ,ci3


let h1 = combine_interpsigns ord_thm int1 pt int2 in
let thm1,thm2,thm3 = int1,pt,int2

let tmp = (ith 0 thms)
merge_interpsign ord_thm tmp

let thm1 = ASSUME  
     `interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x1 < x /\ x < x2)
      [Unknown; Pos; Pos; Neg]`;;

let thm2 = ASSUME 
   `interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x = x2)
      [Unknown; Pos; Pos; Neg]`;;

let thm3 = ASSUME 
   `interpsigns
     [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x2 < x /\ x < x3)
      [Unknown; Pos; Pos; Neg]`;;

let ord_thm = ASSUME `x1 < x2 /\ x2 < x3`

combine_interpsigns ord_thm thm1 thm2 thm3;;



let thm1 = ASSUME  
     `interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x < x5)
      [Unknown; Pos; Pos; Neg]`;;

let thm2 = ASSUME 
   `interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x = x5)
      [Unknown; Pos; Pos; Neg]`;;

let thm3 = ASSUME 
   `interpsigns
     [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x5 < x /\ x < x6)
      [Unknown; Pos; Pos; Neg]`;;

let ord_thm = ASSUME `x5 < x6`;;

combine_interpsigns ord_thm thm1 thm2 thm3;;


let thm1 = ASSUME  
     `interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x < x6)
      [Unknown; Pos; Pos; Neg]`;;

let thm2 = ASSUME 
   `interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x = x6)
      [Unknown; Pos; Pos; Neg]`;;

let thm3 = ASSUME 
   `interpsigns
     [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x6 < x)
      [Unknown; Pos; Pos; Neg]`;;

let ord_thm = ASSUME `x5 < x6`;;

combine_interpsigns ord_thm thm1 thm2 thm3;;


*)               

(* }}} *)


(* {{{ Doc *)
(*
  get_bounds `\x. x < x1` `\x. x1 < x /\ x < x2`
   --> 
   x1 < x2

  get_bounds `\x. x0 < x < x1` `\x. x1 < x /\ x < x2`
   --> 
   x0 < x1 /\ x1 < x2

  get_bounds `\x. x < x1` `\x. x1 < x`
  -->
  T

*)
(* }}} *)
(*
let get_bounds set1 set2 =
  let _,s1 = dest_abs set1 in
  let _,s2 = dest_abs set2 in
  let c1 = 
    if is_conj s1 then 
      let l,r = dest_conj s1 in
      let l1,l2 = dest_binop rlt l in
      let l3,l4 = dest_binop rlt r in
        mk_binop rlt l1 l4
    else t_tm in
  let c2 = 
    if is_conj s2 then 
      let l,r = dest_conj s2 in
      let l1,l2 = dest_binop rlt l in
      let l3,l4 = dest_binop rlt r in
        mk_binop rlt l1 l4
    else t_tm in
  if c1 = t_tm then c2 
  else if c2 = t_tm then c1 
  else mk_conj (c1,c2);;
*)
(* {{{ Examples *)
(*
  get_bounds `\x. x < x1` `\x. x1 < x /\ x < x2`


  get_bounds `\x. x0 < x /\ x < x1` `\x. x1 < x /\ x < x2`

  get_bounds `\x. x < x1` `\x. x1 < x`
*)
(* }}} *)


(* {{{ Doc *)

(* collect_pts 
   |- interpsigns ... (\x. x < x1) ...
   |- interpsigns ... (\x. x1 < x /\ x < x4) ...
   |- interpsigns ... (\x. x4 < x /\ x < x7) ...
   |- interpsigns ... (\x. x7 < x) ...

 -->
  [x1,x4,x7]
*)

(* }}} *)
(*

let rec collect_pts thms = 
  match thms with
      [] -> [] 
    | h::t -> 
        let rest = collect_pts t in
        let _,set,_ = dest_interpsigns h in  
        let x,b = dest_abs set in
        let bds = 
          if b = t_tm then [] 
          else if is_conj b then
            let l,r = dest_conj b in
              [fst(dest_binop rlt l);snd(dest_binop rlt r)]
          else  
            let _,l,r = get_binop b in
              if x = l then [r] else [l] in
        match rest with
            [] -> bds
          | h::t -> if not (h = (last bds)) then failwith "pts not in order" 
              else if length bds = 2 then hd bds::rest else rest;;
*)
(* {{{ Examples *)

(*

let thms = [ASSUME `interpsigns [\x. &0 + x * &1; \x. &1] (\x. T) [Unknown; Pos]`]
let h::t = [ASSUME `interpsigns [\x. &0 + x * &1; \x. &1] (\x. T) [Unknown; Pos]`]
collect_pts [ASSUME `interpsigns [\x. &0 + x * &1; \x. &1] (\x. T) [Unknown; Pos]`]

let t1 = ASSUME `interpsigns [[&1]] (\x. x < x1) [Pos]`
let t2 = ASSUME `interpsigns [[&1]] (\x. x1 < x /\ x < x4) [Pos]`
let t3 = ASSUME `interpsigns [[&1]] (\x. x4 < x /\ x < x7) [Pos]`
let t4 = ASSUME `interpsigns [[&1]] (\x. x7 < x) [Pos]`

collect_pts [t1;t2;t3;t4]

let t1 = ASSUME `interpsigns [[&1]] (\x. x0 < x /\ x < x1) [Pos]`
let t2 = ASSUME `interpsigns [[&1]] (\x. x1 < x /\ x < x4) [Pos]`
let t3 = ASSUME `interpsigns [[&1]] (\x. x4 < x /\ x < x7) [Pos]`
let t4 = ASSUME `interpsigns [[&1]] (\x. x7 < x) [Pos]`

collect_pts [t1;t2;t3;t4]

let t1 = ASSUME  
      `interpsigns
        [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
        &1]]
        (\x. x < x1)
        [Unknown; Pos; Pos; Pos]`;;

let t2 = ASSUME 
  `interpsigns
         [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
         &1]]
         (\x. x = x1)
         [Neg; Pos; Pos; Zero]`;;

let t3 = ASSUME 
  `interpsigns
         [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
         &1]]
         (\x. x1 < x /\ x < x4)
         [Unknown; Pos; Pos; Neg]`;;

let t4 = ASSUME 
  `interpsigns
         [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
         &1]]
         (\x. x = x4)
         [Pos; Pos; Zero; Neg]`;;

let t5 = ASSUME 
  `interpsigns
         [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
         &1]]
         (\x. x4 < x /\ x < x5)
         [Unknown; Pos; Neg; Neg]`;;

let t6 = ASSUME 
  `interpsigns
         [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
         &1]]
         (\x. x = x5)
         [Pos; Pos; Zero; Zero]`;;

let t7 = ASSUME 
  `interpsigns
         [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; 
         &1]]
         (\x. x5 < x)
         [Unknown; Pos; Pos; Pos]`;;

let thms = [t1;t2;t3;t4;t5;t6;t7]
collect_pts thms

*)
          




(*
combine_identical_lines
      |- real_ordered_list [x1; x2; x3; x4; x5]
      |- ALL2
         (interpsigns [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]])
         (partition_line [x1; x2; x3; x4; x5])
         [[Unknown; Pos; Pos; Pos]; 
x1        [Neg; Pos; Pos; Zero];
          [Unknown; Pos; Pos; Neg]; 
x2        [Unknown; Pos; Pos; Neg]; 
          [Unknown; Pos; Pos; Neg]; 
x3        [Unknown; Pos; Pos; Neg]; 
          [Unknown; Pos; Pos; Neg]; 
x4        [Pos; Pos; Zero; Neg]; 
          [Unknown; Pos; Neg; Neg]; 
x5        [Pos; Pos; Zero; Zero]; 
          [Unknown; Pos; Pos; Pos]]

 -->
  

      |- ALL2
         (interpsigns [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]])
         (partition_line [x1; x4; x5])
         [[Unknown; Pos; Pos; Pos]; 
x1        [Neg; Pos; Pos; Zero];
          [Unknown; Pos; Pos; Neg]; 
x4        [Pos; Pos; Zero; Neg]; 
          [Unknown; Pos; Neg; Neg]; 
x5        [Pos; Pos; Zero; Zero]; 
          [Unknown; Pos; Pos; Pos]]

*)

(* }}} *)

(*
let sublist i j l = 
  let _,r = chop_list i l in
  let l2,r2 = chop_list (j-i+1) r in
    l2;;
*)
(* {{{ Examples *)
(* 
let i,j,l = 1,4,[1;2;3;4;5;6;7]
sublist 1 4 [1;2;3;4;5;6;7]
sublist 2 4 [1;2;3;4;5;6;7]
sublist 1 1 [1;2;3;4;5;6;7]
*)
(* }}} *)

(*
let rec combine ord_thms l = 
  let lem = REWRITE_RULE[AND_IMP_THM] REAL_LT_TRANS in 
  match l with 
      [int] -> [int] 
    | [int1;int2] -> [int1;int2] 
    | int1::pt::int2::rest -> 
        try 
          let _,set1,_ = dest_interpsigns int1 in
          let _,set2,_ = dest_interpsigns int2 in
          let ord_tm = get_bounds set1 set2 in
          if ord_tm = t_tm then
            let h1 = combine_interpsigns TRUTH int1 pt int2 in
              combine ord_thms (h1::rest) 
          else
            let lt,rt = 
              if is_conj ord_tm then
                let c1,c2 = dest_conj ord_tm in
                let l,_ = dest_binop rlt c1 in  
                let _,r = dest_binop rlt c2 in  
                  l,r
              else dest_binop rlt ord_tm in
            let e1 = find (fun x -> lt = fst(dest_binop rlt (concl x))) ord_thms in
            let i1 = index e1 ord_thms in
            let e2 = find (fun x -> rt = snd(dest_binop rlt (concl x))) ord_thms in
            let i2 = index e2 ord_thms in
            let ord_thms' = sublist i1 i2 ord_thms in
            let ord_thm = end_itlist (fun x y -> MATCH_MPL[lem;x;y]) ord_thms' in
            let h1 = combine_interpsigns ord_thm int1 pt int2 in
              combine ord_thms (h1::rest) 
        with 
            Failure "combine_interpsigns: signs not equal" -> 
              int1::pt::(combine ord_thms(int2::rest));;
*)

(*
let combine_identical_lines rol_thm all_thm = 
  let tmp,mat = dest_comb (concl all_thm) in
  let _,line =  dest_comb tmp in
  let _,pts = dest_comb line in
  let part_thm = PARTITION_LINE_CONV pts in
  let thm' = REWRITE_RULE[ALL2;part_thm] all_thm in
  let thms = CONJUNCTS thm' in
  let ord_thms = rol_thms rol_thm in
  let thms' = combine ord_thms thms in
  let pts = collect_pts thms' in
  let part_thm' = PARTITION_LINE_CONV (mk_list (pts,real_ty)) in
    mk_all2_interpsigns part_thm' thms';;
*)
(* {{{ Examples *)

(*
#untrace combine
#trace combine
let int1::pt::int2::rest = snd (chop_list 6 thms)
let int1::pt::int2::rest = snd (chop_list 0 thms)
let int1::pt::int2::rest = snd (chop_list 2 thms)

let l = thms
let int1::pt::int2::rest = l 
combine thms
let rol_thm = ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`
let all_thm = ASSUME 
   `ALL2
         (interpsigns [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]])
         (partition_line [x1; x2; x3; x4; x5])
         [[Unknown; Pos; Pos; Pos]; 
          [Neg; Pos; Pos; Zero];
          [Unknown; Pos; Pos; Neg]; 
          [Unknown; Pos; Pos; Neg]; 
          [Unknown; Pos; Pos; Neg]; 
          [Unknown; Pos; Pos; Neg]; 
          [Unknown; Pos; Pos; Neg]; 
          [Pos; Pos; Zero; Neg]; 
          [Unknown; Pos; Neg; Neg]; 
          [Pos; Pos; Zero; Zero]; 
          [Unknown; Pos; Pos; Pos]]`;;

let all_thm' = combine_identical_lines rol_thm all_thm

*)

(* }}} *)

(* {{{ Doc *)
(*
assumes l2 is a sublist of l1 

list_diff [1;2;3;4] [2;3] --> [1;4]

*)
(* }}} *)
(*
let rec list_diff l1 l2 = 
  match l1 with
      [] -> if l2 = [] then [] else failwith "l2 not a sublist of l1"
    | h::t -> 
        match l2 with
            [] -> l1
          | h'::t' -> if h = h' then list_diff t t'
              else h::list_diff t l2;;
*)
(* {{{ Examples *)
(*
list_diff [1;2;3;4] [2;3]
list_diff [1;2;3;4] [1;3;4]
*)
(* }}} *)

(*
let CONDENSE mat_thm =
  let rol_thm,all_thm = interpmat_thms mat_thm in
  let pts = dest_list (snd (dest_comb (concl rol_thm))) in  
  let all_thm' = combine_identical_lines rol_thm all_thm in
  let _,part,_ = dest_all2 (concl all_thm) in  
  let plist = dest_list (snd (dest_comb part)) in
  let _,part',_ = dest_all2 (concl all_thm') in  
  let plist' = dest_list (snd (dest_comb part')) in
  let rol_thm' = itlist ROL_REMOVE (list_diff plist plist') rol_thm in
  let mat_thm' = mk_interpmat_thm rol_thm' all_thm' in 
    mat_thm';;
*)
(* ---------------------------------------------------------------------- *)
(*  OPT                                                                   *)
(* ---------------------------------------------------------------------- *)

let rec triple_index l = 
  match l with
    [] -> failwith "triple_index"
  | [x] -> failwith "triple_index"
  | [x;y] -> failwith "triple_index"
  | x::y::z::rest -> if x = y && y = z then 0 else 1 + triple_index (y::z::rest);;

let tmp = ref TRUTH;; 
(*
let 
tmp
let mat_thm = !tmp
let mat_thm = mat_thm'
*)
let rec CONDENSE =
  let real_app = `APPEND:real list -> real list -> real list` in 
  let sign_app = `APPEND:(sign list) list -> (sign list) list -> (sign list) list` in
  let real_len = `LENGTH:real list -> num` in 
  let sign_len = `LENGTH:(sign list) list -> num` in
  let num_mul = `( * ):num -> num -> num` in
  let real_ty = `:real` in
  let two = `2` in
  let sl_ty = `:sign list` in
  fun mat_thm -> 
    try 
      tmp := mat_thm; 
      let pts,_,sgns = dest_interpmat (concl mat_thm) in
      let sgnl = dest_list sgns in
      let ptl = dest_list pts in
      let i = triple_index sgnl (* fail here if fully condensed *) in
      if not (i mod 2 = 0) then failwith "misshifted matrix" else
      if i = 0 then 
        if length ptl = 1 then MATCH_MP INTERPMAT_SING mat_thm
        else CONDENSE (MATCH_MP INTERPMAT_TRIO mat_thm) else
      let l,r = chop_list (i - 2) sgnl in 
      let sgn1,sgn2 = mk_list(l,sl_ty),mk_list(r,sl_ty) in
      let sgns' = mk_comb(mk_comb(sign_app,sgn1),sgn2) in 
      let sgn_thm = prove(mk_eq(sgns,sgns'),REWRITE_TAC[APPEND]) in
      let l',r' = chop_list (i / 2 - 1) ptl (* i always even *) in
      let pt1,pt2 = mk_list(l',real_ty),mk_list(r',real_ty) in
      let pts' = mk_comb(mk_comb(real_app,pt1),pt2) in 
      let pt_thm = prove(mk_eq(pts,pts'),REWRITE_TAC[APPEND]) in
      let mat_thm' = ONCE_REWRITE_RULE[sgn_thm;pt_thm] mat_thm in
      let len_thm = prove((mk_eq(mk_comb(sign_len,sgn1),mk_binop num_mul two (mk_comb(real_len,pt1)))),REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
        CONDENSE (REWRITE_RULE[APPEND] 
         (MATCH_MP (MATCH_MP INTERPMAT_TRIO_INNER mat_thm') len_thm))
  with 
    Failure "triple_index" -> mat_thm
  | Failure x -> failwith ("CONDENSE: " ^ x);;


(* {{{ Examples *)

(*

let mat_thm = mat_thm'
CONDENSE mat_thm


let mat_thm = ASSUME 
  `interpmat [x1; x2; x3; x4; x5] 
     [\x. &1 + x * (&2 + x * &3); \x. &2 + x * (-- &3 + x * &1); \x. -- &4 + x * (&0 + x * &1); 
      \x. &8 + x * &4; \x. -- &7 + x * &11; \x. &5 + x * &5]
      [
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Pos; Pos; Pos; Neg; Neg; Neg];     
      [Zero; Pos; Pos; Neg; Neg; Neg];     
      [Neg; Pos; Pos; Neg; Neg; Neg]     
     ]` 


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
      [Pos; Pos; Pos; Pos; Pos; Pos]]` 

let mat_thm' = INFERPSIGN vars sgns mat_thm div_thms 

CONDENSE mat_thm



*)

(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let CONDENSE mat_thm =
  let start_time = Sys.time() in
  let res = CONDENSE mat_thm in  
    condense_timer +.= (Sys.time() -. start_time);
    res;;

