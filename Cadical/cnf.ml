(* ========================================================================= *)
(* Tools to put formulas in definitional (Tseitin) CNF form for SAT solvers. *)
(* The temporary variables are implicit for actual proof reconstruction; all *)
(* steps simply use the corresponding expansion directly.                    *)
(* ========================================================================= *)

let exploit_conjunctive_structure = ref true;;

(* ------------------------------------------------------------------------- *)
(* Split up a theorem according to conjuncts, in a general sense.            *)
(* ------------------------------------------------------------------------- *)

let GCONJUNCTS =
  let [pth_ni1; pth_ni2; pth_no1; pth_no2; pth_an1; pth_an2; pth_nn] =
    (map UNDISCH_ALL o CONJUNCTS o TAUT)
    `(~(p ==> q) ==> p) /\
     (~(p ==> q) ==> ~q) /\
     (~(p \/ q) ==> ~p) /\
     (~(p \/ q) ==> ~q) /\
     (p /\ q ==> p) /\
     (p /\ q ==> q) /\
     (~ ~p ==> p)` in
  let p_tm = concl pth_an1 and q_tm = concl pth_an2 in
  let rec GCONJUNCTS th acc =
    match (concl th) with
      Comb(Const("~",_),Comb(Comb(Const("==>",_),p),q)) ->
       GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_ni1))
                  (GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_ni2))
                              acc)
    | Comb(Const("~",_),Comb(Comb(Const("\\/",_),p),q)) ->
       GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_no1))
                  (GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_no2))
                              acc)
    | Comb(Comb(Const("/\\",_),p),q) ->
       GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_an1))
                  (GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_an2))
                              acc)
    | Comb(Const("~",_),Comb(Const("~",_),p)) ->
          GCONJUNCTS (PROVE_HYP th (INST [p,p_tm] pth_nn)) acc
    | _ -> th::acc in
  fun th -> GCONJUNCTS th [];;

(* ------------------------------------------------------------------------- *)
(* Generate fresh variable names (could just use genvars).                   *)
(* ------------------------------------------------------------------------- *)

let propvar i = mk_var("x"^string_of_int i,bool_ty);;

(* ------------------------------------------------------------------------- *)
(* Set up the basic definitional arrangement.                                *)
(* ------------------------------------------------------------------------- *)

let rec localdefs tm (n,defs,lfn) =
  if is_neg tm then
    let n1,v1,defs1,lfn1 = localdefs (rand tm) (n,defs,lfn) in
    let tm' = mk_neg v1 in
    try (n1,apply defs1 tm',defs1,lfn1) with Failure _ ->
    let n2 = n1 + 1 in
    let v2 = propvar n2 in
    n2,v2,(tm' |-> v2) defs1,(v2 |-> tm) lfn1
  else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
    let n1,v1,defs1,lfn1 = localdefs (lhand tm) (n,defs,lfn) in
    let n2,v2,defs2,lfn2 = localdefs (rand tm) (n1,defs1,lfn1) in
    let tm' = mk_comb(mk_comb(rator(rator tm),v1),v2) in
    try (n2,apply defs2 tm',defs2,lfn2) with Failure _ ->
    let n3 = n2 + 1 in
    let v3 = propvar n3 in
    n3,v3,(tm' |-> v3) defs2,(v3 |-> tm) lfn2
  else try (n,apply defs tm,defs,lfn) with Failure _ ->
       let n1 = n + 1 in
       let v1 = propvar n1 in
       n1,v1,(tm |-> v1) defs,(v1 |-> tm) lfn;;

(* ------------------------------------------------------------------------- *)
(* Just translate to fresh variables, but otherwise leave unchanged.         *)
(* ------------------------------------------------------------------------- *)

let rec transvar (n,tm,vdefs,lfn) =
  if is_neg tm then
    let n1,tm1,vdefs1,lfn1 = transvar (n,rand tm,vdefs,lfn) in
    n1,mk_comb(rator tm,tm1),vdefs1,lfn1
  else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
    let n1,tm1,vdefs1,lfn1 = transvar (n,lhand tm,vdefs,lfn) in
    let n2,tm2,vdefs2,lfn2 = transvar (n1,rand tm,vdefs1,lfn1) in
    n2,mk_comb(mk_comb(rator(rator tm),tm1),tm2),vdefs2,lfn2
  else try n,apply vdefs tm,vdefs,lfn with Failure _ ->
       let n1 = n + 1 in
       let v1 = propvar n1 in
       n1,v1,(tm |-> v1) vdefs,(v1 |-> tm) lfn;;

(* ------------------------------------------------------------------------- *)
(* Determine if a term is (strictly) clausal, i.e. is a conjunction of       *)
(* disjunctions of literals, all of which are right-associated.              *)
(* ------------------------------------------------------------------------- *)

let is_atom tm =
  match tm with
    Comb(Comb(Const("/\\",_),l),r)
  | Comb(Comb(Const("\\/",_),l),r)
  | Comb(Comb(Const("==>",_),l),r)
  | Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r)
        -> false
  | Comb(Const("~",_),l) -> false
  | _ -> true;;

let is_literal tm =
  match tm with
    Comb(Const("~",_),t) -> is_atom t
  | _ -> is_atom tm;;

let rec is_clausal tm =
  match tm with
    Comb(Comb(Const("\\/",_),l),r) -> is_literal l && is_clausal r
  | _ -> is_literal tm;;

let rec is_strictcnf tm =
  match tm with
    Comb(Comb(Const("/\\",_),l),r) -> is_clausal l && is_strictcnf r
  | _ -> is_clausal tm;;

(* ------------------------------------------------------------------------- *)
(* Now do the definitional arrangement but not wastefully at the top.        *)
(* ------------------------------------------------------------------------- *)

let definitionalize =
  let transform_imp =
    let pth = TAUT `(p ==> q) <=> ~p \/ q` in
    let ptm = rand(concl pth) in
    let p_tm = rand(lhand ptm) and q_tm = rand ptm in
    fun th -> let ip,q = dest_comb(concl th) in
              let p = rand ip in
              EQ_MP (INST [p,p_tm; q,q_tm] pth) th
  and transform_iff_1 =
    let pth = UNDISCH(TAUT `(p <=> q) ==> (p \/ ~q)`) in
    let ptm = concl pth in
    let p_tm = lhand ptm and q_tm = rand(rand ptm) in
    fun th -> let ip,q = dest_comb(concl th) in
              let p = rand ip in
              PROVE_HYP th (INST [p,p_tm; q,q_tm] pth)
  and transform_iff_2 =
    let pth = UNDISCH(TAUT `(p <=> q) ==> (~p \/ q)`) in
    let ptm = concl pth in
    let p_tm = rand(lhand ptm) and q_tm = rand ptm in
    fun th -> let ip,q = dest_comb(concl th) in
              let p = rand ip in
              PROVE_HYP th (INST [p,p_tm; q,q_tm] pth) in
  let definitionalize th (n,tops,defs,lfn) =
    let t = concl th in
    if is_clausal t then
      let n',v,defs',lfn' = transvar (n,t,defs,lfn) in
      (n',(v,th)::tops,defs',lfn')
    else if is_neg t then
       let n1,v1,defs1,lfn1 = localdefs (rand t) (n,defs,lfn) in
       (n1,(mk_neg v1,th)::tops,defs1,lfn1)
    else if is_disj t then
      let n1,v1,defs1,lfn1 = localdefs (lhand t) (n,defs,lfn) in
      let n2,v2,defs2,lfn2 = localdefs (rand t) (n1,defs1,lfn1) in
      (n2,(mk_disj(v1,v2),th)::tops,defs2,lfn2)
    else if is_imp t then
      let n1,v1,defs1,lfn1 = localdefs (lhand t) (n,defs,lfn) in
      let n2,v2,defs2,lfn2 = localdefs (rand t) (n1,defs1,lfn1) in
      (n2,(mk_disj(mk_neg v1,v2),transform_imp th)::tops,defs2,lfn2)
    else if is_iff t then
      let n1,v1,defs1,lfn1 = localdefs (lhand t) (n,defs,lfn) in
      let n2,v2,defs2,lfn2 = localdefs (rand t) (n1,defs1,lfn1) in
      (n2,(mk_disj(v1,mk_neg v2),transform_iff_1 th)::
          (mk_disj(mk_neg v1,v2),transform_iff_2 th)::tops,defs2,lfn2)
    else
      let n',v,defs',lfn' = localdefs t (n,defs,lfn) in
      (n',(v,th)::tops,defs',lfn') in
  definitionalize;;
