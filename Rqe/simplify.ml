(* ---------------------------------------------------------------------- *)
(*  Simplification                                                        *)
(* ---------------------------------------------------------------------- *)

(*
let psimplify1 fm =
  match fm with
    Not False -> True
  | Not True -> False
  | And(False,q) -> False
  | And(p,False) -> False
  | And(True,q) -> q
  | And(p,True) -> p
  | Or(False,q) -> q
  | Or(p,False) -> p
  | Or(True,q) -> True
  | Or(p,True) -> True
  | Imp(False,q) -> True
  | Imp(True,q) -> q
  | Imp(p,True) -> True
  | Imp(p,False) -> Not p
  | Iff(True,q) -> q
  | Iff(p,True) -> p
  | Iff(False,q) -> Not q
  | Iff(p,False) -> Not p
  | _ -> fm;;
*)


let PSIMPLIFY1_CONV = 
  let nt = `~T` 
  and t = `T`
  and f = `F`
  and nf = `~F` in             
  fun fm ->
  try 
    let fm' = 
      if fm = nt then f
      else if fm = nf then t
      else if is_conj fm then
        let l,r = dest_conj fm in
          if l = f || r = f then f
          else if l = t then r
          else if r = t then l
          else fm
      else if is_disj fm then
        let l,r = dest_disj fm in
          if l = t || r = t then t
          else if l = f then r 
          else if r = f then l 
          else fm
      else if is_imp fm then
        let l,r = dest_imp fm in
          if l = f then t
          else if r = t then t
          else if l = t then r
          else if r = f then mk_neg l
          else fm
      else if is_iff fm then
        let l,r = dest_beq fm in
          if l = f then mk_neg r 
          else if l = t then r
          else if r = t then l 
          else if r = f then mk_neg l 
            else fm
      else failwith "PSIMPLIFY: 0" in  
    let fm'' = mk_eq(fm,fm') in
      prove(fm'',REWRITE_TAC[])
  with _ -> REFL fm;;

(*
let fm = `T /\ T`
PSIMPLIFY1_CONV `T /\ A`

let simplify1 fm =
  match fm with
    Forall(x,p) -> if mem x (fv p) then fm else p
  | Exists(x,p) -> if mem x (fv p) then fm else p
  | _ -> psimplify1 fm;;
*)

let SIMPLIFY1_CONV fm =
  if is_forall fm || is_exists fm then
    let x,p = dest_forall fm in
      if mem x (frees p) then REFL fm 
      else  prove(mk_eq(fm,p),REWRITE_TAC[])
  else PSIMPLIFY1_CONV fm;;

(*
let rec simplify fm =
  match fm with
    Not p -> simplify1 (Not(simplify p))
  | And(p,q) -> simplify1 (And(simplify p,simplify q))
  | Or(p,q) -> simplify1 (Or(simplify p,simplify q))
  | Imp(p,q) -> simplify1 (Imp(simplify p,simplify q))
  | Iff(p,q) -> simplify1 (Iff(simplify p,simplify q))
  | Forall(x,p) -> simplify1(Forall(x,simplify p))
  | Exists(x,p) -> simplify1(Exists(x,simplify p))
  | _ -> fm;;
*)

let rec SIMPLIFY_CONV =
  let not_tm = `(~)`  
  and ex_tm = `(?)` in
  fun fm -> 
  if is_neg fm then 
    let thm1 = SIMPLIFY_CONV (dest_neg fm) in
    let thm2 = AP_TERM not_tm thm1 in
    let l,r = dest_eq (concl thm2) in
    let thm3 = SIMPLIFY1_CONV r in
      TRANS thm2 thm3
  else if is_conj fm || is_disj fm || is_imp fm || is_iff fm then
    let op,l,r = get_binop fm in
    let l_thm = SIMPLIFY_CONV l in
    let r_thm = SIMPLIFY_CONV r in
    let a_thm = (curry MK_COMB) (AP_TERM op l_thm) r_thm in
    let al,ar = dest_eq (concl a_thm) in
    let thm = SIMPLIFY1_CONV ar in
      TRANS a_thm thm
  else if is_forall fm || is_exists fm then
    let x,bod = dest_quant fm in
    let bod_thm = SIMPLIFY_CONV bod in
    let lam_thm = ABS x bod_thm in
    let q_thm = AP_TERM ex_tm lam_thm in
    let l,r = dest_eq (concl q_thm) in
    let thm = SIMPLIFY1_CONV r in
      TRANS q_thm thm
  else REFL fm;;



(*

SIMPLIFY_CONV `T /\ T \/ F`

let operations =
  ["=",(=/); "<",(</); ">",(>/); "<=",(<=/); ">=",(>=/);
   "divides",(fun x y -> mod_num y x =/ Int 0)];;

let evalc_atom at =
  match at with
    R(p,[s;t]) ->
        (try if assoc p operations (dest_numeral s) (dest_numeral t)
             then True else False
         with Failure _ -> Atom at)
  | _ -> Atom at;;

let evalc = onatoms evalc_atom;;
*)

let REAL_LEAF_CONV fm = 
  let op,l,r = get_binop fm in
    if op = rlt then
      REAL_RAT_LT_CONV fm
    else if op = rgt then
      REAL_RAT_GT_CONV fm
    else if op = rle then
      REAL_RAT_LE_CONV fm
    else if op = rge then
      REAL_RAT_GE_CONV fm
    else if op = req then 
      REAL_RAT_EQ_CONV fm
    else failwith "REAL_LEAF_CONV";;

let EVALC_CONV = DEPTH_CONV REAL_LEAF_CONV;;





(*
EVALC_CONV `x < &0 /\ &1 < &2`
(EVALC_CONV THENC SIMPLIFY_CONV) `(&0 + a * &1 = &0) /\
     ((&0 + b * &1 = &0) /\
      ((&0 + c * &1 = &0) /\ T \/
       &0 + c * &1 < &0 /\ F \/
       &0 + c * &1 > &0 /\ F) \/
      &0 + b * &1 < &0 /\ T \/
      &0 + b * &1 > &0 /\ T) \/
     &0 + a * &1 < &0 /\
     ((&0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) = &0) /\ T \/
      &0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) < &0 /\ F \/
      &0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) > &0 /\ T) \/
     &0 + a * &1 > &0 /\
     ((&0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) = &0) /\ T \/
      &0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) < &0 /\ T \/
      &0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) > &0 /\ &1 < &2)`

*)
