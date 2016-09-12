
(* ---------------------------------------------------------------------- *)
(*  PDIVIDES                                                              *)
(* ---------------------------------------------------------------------- *)

let PDIVIDES vars sgns p q = 
  let s_thm = FINDSIGN vars sgns (head vars q) in
  let op,l1,r1 = get_binop (concl s_thm) in
  if op = req then failwith "PDIVIDES : head coefficient is zero" else
  let div_thm = PDIVIDE vars p q in
  let asx,pqr = dest_eq (concl div_thm) in
  let pq,r = dest_plus pqr in
  let p',q' = dest_mult pq in
  let ak,s = dest_mult asx in
  let a,k = dest_pow ak in
  let k' = dest_small_numeral k in
  if op = rgt || even k' then 
      r,div_thm
  else if odd k' && op = rlt then
    let par_thm = PARITY_CONV k in
    let mp_thm = MATCH_MPL[neg_odd_lem;div_thm;par_thm] in
    let mp_thm1 = (CONV_RULE (LAND_CONV (LAND_CONV (LAND_CONV POLY_NEG_CONV)))) mp_thm in
    let mp_thm2 = (CONV_RULE (RAND_CONV (LAND_CONV (LAND_CONV (POLY_NEG_CONV))))) mp_thm1 in
    let mp_thm3 = (CONV_RULE (RAND_CONV (RAND_CONV POLY_NEG_CONV))) mp_thm2 in
    let ret = (snd o dest_plus o rhs o concl) mp_thm3 in 
      ret,mp_thm3
  else if odd k' && op = rneq then  
    let par_thm = PARITY_CONV k in
    let mp_thm = MATCH_MPL[mul_odd_lem;div_thm;par_thm] in
    let mp_thm1 = (CONV_RULE (LAND_CONV (LAND_CONV (LAND_CONV (POLYNATE_CONV vars))))) mp_thm in
    let mp_thm2 = (CONV_RULE (RAND_CONV (LAND_CONV (POLYNATE_CONV vars)))) mp_thm1 in
    let mp_thm3 = (CONV_RULE (RAND_CONV (RAND_CONV (POLY_MUL_CONV vars)))) mp_thm2 in
    let ret = (snd o dest_plus o rhs o concl) mp_thm3 in 
      ret,mp_thm3
  else failwith "PDIVIDES: 1";;

(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let PDIVIDES vars sgns mat_thm div_thms = 
  let start_time = Sys.time() in
  let res = PDIVIDES vars sgns mat_thm div_thms in
    pdivides_timer +.= (Sys.time() -. start_time);
    res;;



(*
PDIVIDES vars sgns p 
let q = (ith 2 qs)


let vars = [`x:real`;`y:real`];;
let sgns = [ARITH_RULE `&1 > &0`;ASSUME  `&0 + y * &1 < &0`];;
let q = rhs(concl (POLYNATE_CONV vars `x * y`));;
let p = rhs(concl (POLYNATE_CONV vars `&1 + y * x * x + x * x * x * &5 * y`));;
PDIVIDE vars p q;;
PDIVIDES vars sgns p q;;

let vars = [`x:real`;`y:real`];;
let sgns = [ARITH_RULE `&1 > &0`;ASSUME  `&0 + y * &1 > &0`];;
let q = rhs(concl (POLYNATE_CONV vars `x * x * y`));;
let p = rhs(concl (POLYNATE_CONV vars `&1 + x * x + x * x * x * y`));;
PDIVIDE vars p q;;
PDIVIDES vars sgns p q;;


let vars = [`x:real`;`y:real`];;
let sgns = [ARITH_RULE `&1 > &0`;ASSUME  `&0 + y * &1 < &0`];;
let q = rhs(concl (POLYNATE_CONV vars `x * x * y`));;
let p = rhs(concl (POLYNATE_CONV vars `&1 + x * x + x * x * x * y`));;
PDIVIDE vars p q;;
PDIVIDES vars sgns p q;;

let vars = [`x:real`;`y:real`];;
let sgns = [ASSUME  `&0 + y * &1 < &0`];;
let q = rhs(concl (POLYNATE_CONV vars `-- x:real`));;
let p = rhs(concl (POLYNATE_CONV vars `x * x * y`));;
PDIVIDE vars p q;;
PDIVIDES vars sgns p q

let vars = [`x:real`;`y:real`];;
let sgns = [ARITH_RULE `&1 > &0`;ASSUME  `&0 + y * &1 <> &0`];;
let q = rhs(concl (POLYNATE_CONV vars `x * x * y`));;
let p = rhs(concl (POLYNATE_CONV vars `&1 + x * x + x * x * x * y`));;
PDIVIDE vars p q;;
PDIVIDES vars sgns p q;;

*)
