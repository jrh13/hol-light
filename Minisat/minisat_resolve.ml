(*open satCommonTools dimacsTools minisatParse satScript*)

(* functions for replaying minisat proof LCF-style.
   Called from minisatProve.ml after proof log has
   been parsed. *)

(* p is a literal *)
let toVar p =
  if is_neg p
  then rand p
  else p;;

let (NOT_NOT_ELIM,NOT_NOT_CONV) =
  let t = mk_var("t",bool_ty) in
  let NOT_NOT2 = SPEC_ALL NOT_NOT in
  ((fun th -> EQ_MP (INST [rand(rand(concl th)),t] NOT_NOT2) th),
   (fun tm -> INST [rand(rand tm),t] NOT_NOT2));;

let l2hh = function
    h0::h1::t -> (h0,h1,t)
  |  _ -> failwith("Match failure in l2hh");;

(*+1 because minisat var numbers start at 0, dimacsTools at 1*)
let mk_sat_var lfn n =
  let rv = lookup_sat_num (n+1) in
  tryapplyd lfn rv rv;;

let get_var_num lfn v = lookup_sat_var v - 1;;

(* mcth maps clause term t to thm of the form cnf |- t, *)
(*  where t is a clause of the cnf term                 *)
let dualise =
  let pth_and = TAUT `F \/ F <=> F` and pth_not = TAUT `~T <=> F` in
  let rec REFUTE_DISJ tm =
    match tm with
      Comb(Comb(Const("\\/",_) as op,l),r) ->
        TRANS (MK_COMB(AP_TERM op (REFUTE_DISJ l),REFUTE_DISJ r)) pth_and
    | Comb(Const("~",_) as l,r) ->
        TRANS (AP_TERM l (EQT_INTRO(ASSUME r))) pth_not
    | _ ->
        ASSUME(mk_iff(tm,f_tm)) in
  fun lfn -> let INSTANTIATE_ALL_UNDERLYING th =
             let fvs = thm_frees th in
             let tms = map (fun v -> tryapplyd lfn v v) fvs in
             INST (zip tms fvs) th in
             fun mcth t ->
               EQ_MP (INSTANTIATE_ALL_UNDERLYING(REFUTE_DISJ t))
                     (Termmap.find t mcth),t_tm,TRUTH;;


(* convert clause term to dualised thm form on first use *)
let prepareRootClause lfn mcth cl (t,lns) ci =
    let (th,dl,cdef) = dualise lfn mcth t in
    let _ = Array.set cl ci (Root (Rthm (th,lns,dl,cdef))) in
    (th,lns);;

(* will return clause info at index ci *)

exception Fn_get_clause__match;;
exception Fn_get_root_clause__match;;

(* will return clause info at index ci *)
let getRootClause cl ci =
  let res =
    match (Array.get cl ci) with
      Root (Rthm (t,lns,dl,cdef)) -> (t,lns,dl,cdef)
    | _ -> raise Fn_get_root_clause__match in
  res;;

(* will return clause thm at index ci *)

let getClause lfn mcth cl ci =
  let res =
    match (Array.get cl ci) with
      Root (Ll (t,lns)) -> prepareRootClause lfn mcth cl (t,lns) ci
    | Root (Rthm (t,lns,dl,cdef)) -> (t,lns)
    | Chain _ -> raise Fn_get_clause__match
    | Learnt (th,lns) ->  (th,lns)
    | Blank -> raise Fn_get_clause__match in
  res;;

(* ground resolve clauses c0 and c1 on v,
   where v is the only var that occurs with opposite signs in c0 and c1 *)
(* if n0 then v negated in c0 *)
(*   (but remember we are working with dualised clauses) *)
let resolve =
  let pth = UNDISCH(TAUT `F ==> p`) in
  let p = concl pth
  and f_tm = hd(hyp pth) in
  fun v n0 rth0 rth1 ->
    let th0 = DEDUCT_ANTISYM_RULE (INST [v,p] pth) (if n0 then rth0 else rth1)
    and th1 = DEDUCT_ANTISYM_RULE (INST [mk_iff(v,f_tm),p] pth)
                                  (if n0 then rth1 else rth0) in
    EQ_MP th1 th0;;

(* resolve c0 against c1 wrt v *)
let resolveClause lfn mcth cl vi rci (c0i,c1i) =
  let ((rth0,lns0),(rth1,lns1)) = pair_map (getClause lfn mcth cl) (c0i,c1i) in
  let piv = mk_sat_var lfn vi in
  let n0 = mem piv (hyp rth0) in
  let rth  = resolve piv n0 rth0 rth1 in
  let _ = Array.set cl rci (Learnt (rth,lns0)) in
  ();;

let resolveChain lfn mcth cl rci =
    let (nl,lnl) =
      match (Array.get cl rci) with
        Chain (l,ll) -> (l,ll)
      | _            -> failwith("resolveChain") in
    let (vil,cil) = unzip nl in
    let vil = tl vil in (* first pivot var is actually dummy value -1 *)
    let (c0i,c1i,cilt) = l2hh cil in
    let _ = resolveClause lfn mcth cl (List.hd vil) rci (c0i,c1i) in
    let _ =
      List.iter
        (fun (vi,ci) ->
          resolveClause lfn mcth cl vi rci (ci,rci))
        (tl (tl nl)) in
    ();;

(* rth should be A |- F, where A contains all and only *)
(* the root clauses used in the proof                  *)
let unsatProveResolve lfn mcth (cl,sk,srl) =
  let _ = List.iter (resolveChain lfn mcth cl) (List.rev sk) in
  let rth =
    match (Array.get cl (srl-1)) with
      Learnt (th,_) -> th
    | _ -> failwith("unsatProveTrace") in
  rth;;
