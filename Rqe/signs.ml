(* ------------------------------------------------------------------------- *)
(* Find sign of polynomial, using modulo-constant lookup and computation.    *)
(* ------------------------------------------------------------------------- *)

let xterm_lt t1 t2 = 
  try
    let n1,_ = dest_var t1 in
    let n2,_ = dest_var t2 in
    let i1 = String.sub n1 2 (String.length n1 - 2) in
    let i2 = String.sub n2 2 (String.length n2 - 2) in
    let x1 = int_of_string i1 in
    let x2 = int_of_string i2 in
      x1 < x2
  with _ -> failwith "xterm_lt: not an xvar?";;

(*
String.sub n1 2 (String.length n1 - 2)
substring
let t1,t2 = `x_99:real`,`x_100:real`
xterm_sort t1 t2
t1 < t2
*)


let FINDSIGN =
  let p_tm = `p:real`
  and c_tm = `c:real`
  and fth = prove
   (`r (a * b * p) (&0) ==> (a * b = &1) ==> r p (&0)`,
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID]) in
  let rec FINDSIGN vars sgns p =
  try
    try SIGN_CONST p with Failure _ ->
    let mth = MONIC_CONV vars p in
    let p' = rand(concl mth) in
    let pth = find (fun th -> lhand(concl th) = p') sgns in
    let c = lhand(lhand(concl mth)) in
    let c' = term_of_rat(Int 1 // rat_of_term c) in
    let sth = SIGN_CONST c' in
    let rel_c = funpow 2 rator (concl sth) in
    let rel_p = funpow 2 rator (concl pth) in  
    let th1 =
      if rel_p = req then if rel_c = rgt then pth_0g else pth_0l
      else if rel_p = rgt then if rel_c = rgt then pth_gg else pth_gl
      else if rel_p = rlt then if rel_c = rgt then pth_lg else pth_ll 
      else if rel_p = rneq then if rel_c = rgt then pth_nzg else pth_nzl 
      else failwith "FINDSIGN" in
    let th2 = MP (MP (INST [p',p_tm; c',c_tm] th1) pth) sth in
    let th3 = EQ_MP (LAND_CONV(RAND_CONV(K(SYM mth))) (concl th2)) th2 in
    let th4 = MATCH_MP fth th3 in
      MP th4 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th4)))) 
  with Failure _ -> failwith "FINDSIGN" in
    FINDSIGN;;

(*

let vars = [`x:real`;`y:real`]
let p =   `&7 + x * (&11 + x * (&10 + y * &7))`

let sgns = [ASSUME `&1 + x * (&11 / &7 + x * (&10 / &7 + y * &1)) < &0`]  
let sgns = [ASSUME `&1 + x * (&11 / &7 + x * (&10 / &7 + y * &1)) = &0`]  
let sgns = [ASSUME `&1 + x * (&11 / &7 + x * (&10 / &7 + y * &1)) > &0`]  
let sgns = [ASSUME `&1 + x * (&11 / &7 + x * (&10 / &7 + y * &1)) <> &0`]  

FINDSIGN vars sgns p
FINDSIGN vars sgns `-- &1`

*)



(*
ASSERTSIGN [x,y] [] (|- &7 + x * (&11 + x * (&10 + y * -- &7)) < &0

-->

[-- &1 + x * (-- &11 / &7 + x * (-- &10 / &7 + y * &1)) > &0]


ASSERTSIGN [x,y] [] (|- &7 + x * (&11 + x * (&10 + y * &7)) < &0

-->

[&1 + x * (&11 / &7 + x * (&10 / &7 + y * &1)) < &0]

*)


let ASSERTSIGN vars sgns sgn_thm = 
  let op,l,r = get_binop (concl sgn_thm) in
  let p_thm = MONIC_CONV vars l in 
  let _,pl,pr = get_binop (concl p_thm) in
  let c,_ = dest_binop rm pl in
  let c_thm = SIGN_CONST c in  
  let c_op,_,_ = get_binop (concl c_thm) in  
  let sgn_thm' =
    if c_op = rlt && op = rlt then 
      MATCH_MPL[signs_lem01;c_thm;sgn_thm;p_thm]
    else if c_op = rgt && op = rlt then
      MATCH_MPL[signs_lem02;c_thm;sgn_thm;p_thm]
    else if c_op = rlt && op = rgt then
      MATCH_MPL[signs_lem03;c_thm;sgn_thm;p_thm]
    else if c_op = rgt && op = rgt then
      MATCH_MPL[signs_lem04;c_thm;sgn_thm;p_thm]
    else if c_op = rlt && op = req then 
      MATCH_MPL[signs_lem05;c_thm;sgn_thm;p_thm]
    else if c_op = rgt && op = req then
      MATCH_MPL[signs_lem06;c_thm;sgn_thm;p_thm]
    else if c_op = rlt && op = rneq then
      MATCH_MPL[signs_lem07;c_thm;sgn_thm;p_thm]
    else if c_op = rgt && op = rneq then
      MATCH_MPL[signs_lem08;c_thm;sgn_thm;p_thm]
    else failwith "ASSERTSIGN : 0" in
  try 
    let sgn_thm'' = find (fun th -> lhand(concl th) = pr) sgns in
    let op1,l1,r1 = get_binop (concl sgn_thm') in
    let op2,l2,r2 = get_binop (concl sgn_thm'') in
      if (concl sgn_thm') = (concl sgn_thm'') then sgns 
      else if op2 = rneq && (op1 = rlt || op1 = rgt) then sgn_thm'::snd (remove ((=) sgn_thm'') sgns) 
      else failwith "ASSERTSIGN : 1"
  with Failure "find" -> sgn_thm'::sgns;; 
      

      
(*
let k0 = `&7 + x * (&11 + x * (&10 + y * -- &7))` 
MONIC_CONV vars k0
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * -- &7)) < &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) < &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) = &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) <> &0` 
let sgn_thm = k1

ASSERTSIGN vars [ASSUME `&1 + x * (&11 / &7 + x * (&10 / &7 + y * &1)) <> &0`] k1

*)

(* ---------------------------------------------------------------------- *)
(*  Case splitting                                                        *)
(* ---------------------------------------------------------------------- *)



let SPLIT_ZERO vars sgns p cont_z cont_n ex_thms =   
  try 
    let sgn_thm = FINDSIGN vars sgns p in  
    let op,l,r = get_binop (concl sgn_thm) in 
      (if op = req then cont_z else cont_n) sgns ex_thms
  with Failure "FINDSIGN" ->   
    let eq_tm = mk_eq(p,rzero) in 
    let neq_tm = mk_neq(p,rzero) in 
    let or_thm = ISPEC p signs_lem002 in
    (* zero *)  
    let z_thm = cont_z (ASSERTSIGN vars sgns (ASSUME eq_tm)) ex_thms in 
    let z_thm' = DISCH eq_tm z_thm in  
    (* nonzero *)
    let nz_thm = cont_n (ASSERTSIGN vars sgns (ASSUME neq_tm)) ex_thms in 
    let nz_thm' = DISCH neq_tm nz_thm in  
    (* combine *)
    let ret = MATCH_MPL[signs_lem003;or_thm;z_thm';nz_thm'] in
    (* matching problem... must continue by hand *)
    let ldj,rdj = dest_disj (concl ret) in
    let lcj,rcj = dest_conj ldj in
    let a,_ = dest_binop req lcj in
    let p,p1 = dest_beq rcj in
    let _,rcj = dest_conj rdj in
    let p2 = rhs rcj in
    let pull_thm = ISPECL[a;p;p1;p2] PULL_CASES_THM in
    let ret' = MATCH_EQ_MP pull_thm ret in
      ret';;

(*

let ret = MATCH_MPL[lem3;or_thm]
MATCH_MP ret z_thm'

;nz_thm'] in

let vars,sgns,p,cont_z,cont_n,ex_thms = !sz_vars, !sz_sgns, !sz_p,!sz_cont_z, !sz_cont_n ,!sz_ex_thms



    let ret = MATCH_MPL[lem3;or_thm;] 
let mp_thm = MATCH_MPL[lem3;or_thm;] in
let vars, sgns, p,cont_z,  cont_n =  !sz_vars,!sz_sgns,!sz_p,!sz_cont_z,!sz_cont_n

let mp_thm = k1


let t1 = ISPECL[`(?y. &0 + y * (&0 + x * &1) = &0)`;`T`;`T`;`&0 + x * &1`;`T`] t0
MATCH_EQ_MP t1 k1



EQ_MP t1 k1

MATCH_EQ_MP PULL_CASES_THM k1

concl k1 = lhs (concl t1)

MATCH_EQ_MP PULL_CASES_THM k0
let k0 = ASSUME `(&0 + x * &1 = &0) /\ ((?y. &0 + y * (&0 + x * &1) = &0) <=> T) \/
     &0 + x * &1 <> &0 /\
     (&0 + x * &1 > &0 /\ ((?x_1089. &0 + x_1089 * (&0 + x * &1) = &0) <=> T) \/
      &0 + x * &1 < &0 /\ ((?x_1084. &0 + x_1084 * (&0 + x * &1) = &0) <=> T))`;;
let k1 = ASSUME `(&0 + x * &1 = &0) /\ ((?y. &0 + y * (&0 + x * &1) = &0) <=> T) \/
     &0 + x * &1 <> &0 /\
     (&0 + x * &1 > &0 /\ ((?y. &0 + y * (&0 + x * &1) = &0) <=> T) \/
      &0 + x * &1 < &0 /\ ((?y. &0 + y * (&0 + x * &1) = &0) <=> T))`;;

MATCH_MPL[PULL_CASES_THM;!sz_z_thm;!sz_nz_thm] in

let thm1 = ASSUME `(?x_32. (&0 + c * &1) + x_32 * ((&0 + b * &1) + x_32 * (&0 + a * &1)) = &0) <=> T`
let thm2 = 
ASSUME `(&0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) < &0 ==> 
          ((?x. (&0 + c * &1) + x * ((&0 + b * &1) + x * (&0 + a * &1)) = &0) <=> F)) /\
        (&0 + a * ((&0 + b * (&0 + b * -- &1)) + a * (&0 + c * &4)) > &0 ==> 
          ((?x_26. (&0 + c * &1) + x_26 * ((&0 + b * &1) + x_26 * (&0 + a * &1)) = &0) <=> T)) `


MATCH_MPL 

(* let PULL_CASES_THM = prove_by_refinement( *)
(*   `((a = &0) ==> (p <=> p0)) ==> ((a <> &0) ==> (a < &0 ==> (p <=> p1)) /\ (a > &0 ==> (p <=> p2)))  *)
(*     ==> (p <=> ((a = &0) /\ p0) \/ ((a < &0) /\ p1) \/ (a > &0 /\ p2))`, *)
(* (\* {{{ Proof *\)
[
  REWRITE_TAC[NEQ] THEN 
  MAP_EVERY BOOL_CASES_TAC [`p:bool`; `p0:bool`; `p1:bool`; `p2:bool`] THEN
  ASM_REWRITE_TAC[NEQ] THEN TRY REAL_ARITH_TAC
]);;
(\* }}} *\) *)

let PULL_CASES_THM = prove
 (`!a p p0 p1 p2.
((a = &0) /\ (p <=> p0) \/
   (a <> &0) /\ (a > &0 /\ (p <=> p1) \/ a < &0 /\ (p <=> p2))) <=>
   ((p <=> (a = &0) /\ p0 \/ a > &0 /\ p1 \/ a < &0 /\ p2))`,
(* {{{ Proof *)
   REPEAT STRIP_TAC THEN  REWRITE_TAC[NEQ] THEN MAP_EVERY BOOL_CASES_TAC [`p:bool`; `p0:bool`; `p1:bool`; `p2:bool`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
(* }}} *)


let vars, sgns, p, cont_z, cont_n =   
[`x:real`;`y:real`],
 empty_sgns,
`&0 + y * &1`,
(fun x -> (ASSUME `abc > def`,[])),
(fun x -> (ASSUME `sean > steph`,[]))


SPLIT_ZERO vars sgns p cont_z cont_n 

ASSERTSIGN vars empty_sgns (ASSUME `&0 + y * &1 = &0`) ,

let vars = [`x:real`;`y:real`]
let sgns = ASSERTSIGN vars [] (ASSUME `&7 + x * (&11 + x * (&10 + y * -- &7)) <> &0`)
let p = `&7 + x * (&11 + x * (&10 + y * -- &7))` 
let cont_z = hd
let cont_n = hd
SPLIT_ZERO vars sgns p cont_z cont_n


let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) < &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) = &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) <> &0` 
let sgn_thm = k1
ASSERTSIGN vars [] k1
  
*)

let SPLIT_SIGN vars sgns p cont_p cont_n ex_thms =   
  let sgn_thm = try FINDSIGN vars sgns p   
                with Failure "FINDSIGN" ->
                failwith "SPLIT_SIGN: no sign -- should have sign assumption by now" in
  let gt_tm = mk_binop rgt p rzero in 
  let lt_tm = mk_binop rlt p rzero in 
  let op,_,_ = get_binop (concl sgn_thm) in 
  if op = rgt then cont_p sgns ex_thms
  else if op = rlt then cont_n sgns ex_thms
  else if op = req then failwith "SPLIT_SIGN: lead coef is 0"
  else if op = rneq then 
    let or_thm = MATCH_MP signs_lem0002 sgn_thm in
    (* < *)  
    let lt_sgns = ASSERTSIGN vars sgns (ASSUME lt_tm) in
    let lt_thm = cont_n lt_sgns ex_thms in 
    let lt_thm' = DISCH lt_tm lt_thm in  
     (* > *)
    let gt_sgns = ASSERTSIGN vars sgns (ASSUME gt_tm) in
    let gt_thm = cont_p gt_sgns ex_thms in 
    let gt_thm' = DISCH gt_tm gt_thm in  
    (* combine *)
    let ret = MATCH_MPL[signs_lem0003;or_thm;gt_thm';lt_thm'] in  
    (* matching problem... must continue by hand *)
    let ldj,rdj = dest_disj (concl ret) in
    let lcj,rcj = dest_conj ldj in
    let a,_ = dest_binop rgt lcj in
    let p,p1 = dest_beq rcj in
    let _,rcj = dest_conj rdj in
    let p2 = rhs rcj in
    let pull_thm = ISPECL[a;p;p1;p2] PULL_CASES_THM_NZ in
    let ret' = MATCH_EQ_MP (MATCH_MP pull_thm sgn_thm) ret in
      ret'
  else failwith "SPLIT_SIGN: unknown op";;


(*
let vars, sgns, p,cont_p,  cont_n =  !ss_vars,!ss_sgns,!ss_p,!ss_cont_p,!ss_cont_n
[`x`],
[ASSUME `&0 + x * &1 <> &0`; ARITH_RULE ` &1 > &0`],
`&0 + x * &1`

let ss_vars, ss_sgns, ss_p,ss_cont_p, ss_cont_n =  ref [],ref [],ref `T`,ref (fun x -> TRUTH,[]),ref(fun x -> TRUTH,[]);;
  ss_vars := vars;
  ss_sgns := sgns;
  ss_p := p;
  ss_cont_p := cont_p;
  ss_cont_n := cont_n;



let vars, sgns, p, cont_p, cont_n =   
[`x:real`;`y:real`],
ASSERTSIGN vars empty_sgns (ASSUME `&0 + y * &1 <> &0`) ,
`&0 + y * &1`,
(fun x -> (ASSUME `P > def`,[])),
(fun x -> (ASSUME `sean > steph`,[]))

SPLIT_SIGN vars sgns p cont_z cont_n 


let vars = [`x:real`;`y:real`]
let sgns = ASSERTSIGN vars [] (ASSUME `&7 + x * (&11 + x * (&10 + y * -- &7)) <> &0`)
let p = `&7 + x * (&11 + x * (&10 + y * -- &7))` 
let cont_p = hd
let cont_n = hd
SPLIT_SIGN vars sgns p cont_p cont_n

let sgns = ASSERTSIGN vars [] (ASSUME `&7 + x * (&11 + x * (&10 + y * -- &7)) <> &0`)

let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) < &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) = &0` 
let k1 = ASSUME `&7 + x * (&11 + x * (&10 + y * &7)) <> &0` 
let sgn_thm = k1
ASSERTSIGN vars [] k1




*)
