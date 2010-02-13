(* ---------------------------------------------------------------------- *)
(*  Labels                                                                *)
(* ---------------------------------------------------------------------- *)

let labels_flag = ref false;;

let LABEL_ALL_TAC:tactic =
 let mk_label avoid =
  let rec mk_one_label i avoid  =
    let label = "Z-"^(string_of_int i) in
      if not(mem label avoid) then label else mk_one_label (i+1) avoid in
    mk_one_label 0 avoid in
 let update_label i asl =
  let rec f_at_i f j =
    function [] -> []
      | a::b -> if (j=0) then (f a)::b else a::(f_at_i f (j-1) b) in
  let avoid = map fst asl in
  let current = el i avoid in
  let new_label = mk_label avoid in
  if (String.length current > 0) then asl else
    f_at_i (fun (_,y) -> (new_label,y) ) i asl in
  fun (asl,w) ->
    let aslp = ref asl in
    (for i=0 to ((length asl)-1) do (aslp := update_label i !aslp) done;
    (ALL_TAC (!aslp,w)));;

let e tac = refine(by(VALID
   (if !labels_flag then (tac THEN LABEL_ALL_TAC) else tac)));;


(* ---------------------------------------------------------------------- *)
(*  Refinement                                                            *)
(* ---------------------------------------------------------------------- *)


let prove_by_refinement(t,(tacl:tactic list)) =
  let gstate = mk_goalstate ([],t) in
  let _,sgs,just = rev_itlist
    (fun tac gs -> by
       (if !labels_flag then (tac THEN LABEL_ALL_TAC) else tac) gs)
     tacl gstate in
  let th = if sgs = [] then just null_inst []
  else failwith "BY_REFINEMENT_PROOF: Unsolved goals" in
  let t' = concl th in
  if t' = t then th else
  try EQ_MP (ALPHA t' t) th
  with Failure _ -> failwith "prove_by_refinement: generated wrong theorem";;

(* ---------------------------------------------------------------------- *)
(*  Term Type Inference Tactics                                                         *)
(* ---------------------------------------------------------------------- *)

let exclude_list = ref
["=";"FINITE";"COND";"@";"!";"?";"UNION";"DELETE";"CARD";"swap";"IN"];;
(* exclude is needed because polymorphic operators were causing problems *)

let get_var_list tm =
  let rec get_var_list tm =
    match tm with
        Var(name,ty) -> [name,ty]
      | Const(name,ty) -> [name,ty]
      | Abs(bv,bod) -> union (get_var_list bv) (get_var_list bod)
      | Comb(s,t) ->  union (get_var_list s) (get_var_list t) in
    filter (fun x -> not (mem (fst x) !exclude_list)) (get_var_list tm);;


let rec auto_theta new_type old_type =
  let tyvar_prefix = "?" in
  let is_generated ty_name =
    let first_char = hd(explode ty_name) in
      if first_char = tyvar_prefix then true else false in
  match new_type with
      Tyvar(ns) ->
        (match old_type with
             Tyvar(os) ->
               if is_generated ns then [old_type,new_type] else []
           | Tyapp (old_name,old_list) -> [old_type,new_type])
    | Tyapp(new_ty_op,new_ty_list) ->
        (match old_type with
             Tyvar _ -> []
           | Tyapp (old_ty_op,old_ty_list) ->
               if new_ty_op = old_ty_op then
                 itlist2 (fun newt oldt b -> union (auto_theta newt oldt) b)
                   new_ty_list old_ty_list []
               else []);;

let rec auto_theta_list newl oldl =
  match newl with
      [] -> []
    | (h::t) ->
        let head_list =
          (try
            let new_name,new_type = h in
            let old_type = assoc new_name oldl in
              (auto_theta new_type old_type)
          with Failure _ -> []) in
          union head_list (auto_theta_list t oldl);;


let auto_type new_tm old_tm =
  let old_list = get_var_list old_tm in
  let new_list = get_var_list new_tm in
  let theta = auto_theta_list new_list old_list in
    inst theta new_tm;;

let rec auto_type_list tm tml =
  match tml with
      [] -> tm
    | (h::t) -> auto_type_list (auto_type tm h) t;;

let auto_type_goal tm (asl,w) =
  let thm_list = snd(unzip asl) in
  let term_list = map (fun x -> snd (dest_thm x)) thm_list in
    auto_type_list tm ([w] @ term_list);;

let TYPE_TAC (f:term->tactic) tm =
  function (asl,w) as g ->
    let typed_term = auto_type_goal tm g in
      f typed_term g;;

let TYPE_TACL (f:term list -> tactic) tml =
  function (asl,w) as g ->
    let typed_terms = map (C auto_type_goal g) tml in
      f typed_terms g;;

(* ---------------------------------------------------------------------- *)
(*  Unfiled                                                               *)
(* ---------------------------------------------------------------------- *)

let CLAIM t =
  TYPE_TAC (C SUBGOAL_THEN MP_TAC) t;;

let lem = TAUT `(a = b) <=> (a ==> b) /\ (b ==> a)`;;
let MATCH_EQ_MP t1 t2 =
  try EQ_MP t1 t2 with Failure _ ->
  let k1 = (SPEC_ALL (PURE_REWRITE_RULE[lem] t1)) in
  let left,right = CONJUNCT1 k1,CONJUNCT2 k1 in
  try MATCH_MP left t2 with Failure _ ->
  try MATCH_MP right t2 with Failure _ ->
    failwith "MATCH_EQ_MP";;

let MATCH_EQ_MP_TAC thm =
  let t1,t2 = EQ_IMP_RULE (SPEC_ALL thm) in
  MATCH_MP_TAC t1 ORELSE MATCH_MP_TAC t2;;


let rec REPEAT_N_CONV n conv =
  if n = 0 then ALL_CONV else conv THENC (REPEAT_N_CONV (n-1) conv);;

let rec REPEAT_N n tac =
  if n = 0 then ALL_TAC else tac THEN REPEAT_N (n-1) tac;;

let dest_goal g =
  let (asms,conc) = g in (asms:(string * thm) list),(conc:term);;

let DISJ_LCASE g =
  let _,c = dest_goal g in
  let l,r = dest_disj c in
  let thm = ISPEC l EXCLUDED_MIDDLE in
    (DISJ_CASES_TAC thm THENL [
      DISJ1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISJ2_TAC
    ]) g;;

let DISJ_RCASE g =
  let _,c = dest_goal g in
  let l,r = dest_disj c in
  let thm = ISPEC r EXCLUDED_MIDDLE in
    (DISJ_CASES_TAC thm THENL [
      DISJ2_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISJ1_TAC
    ]) g;;

let CASES_ON tm =
  let ty,_ = dest_type (type_of tm) in
    match ty with
        "num" ->
          DISJ_CASES_TAC (SPEC tm num_CASES) THENL
          [
            POP_ASSUM SUBST1_TAC;
            POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM SUBST1_TAC
          ]
      | "bool" ->
          DISJ_CASES_TAC (SPEC tm EXCLUDED_MIDDLE)
      | _ -> failwith "not a case type";;


let CASES_ON t = TYPE_TAC CASES_ON t;;

let EXISTS_TAC t = TYPE_TAC EXISTS_TAC t;;

let REWRITE_ASSUMS thl = RULE_ASSUM_TAC (REWRITE_RULE thl);;
let ONCE_REWRITE_ASSUMS thl = RULE_ASSUM_TAC (ONCE_REWRITE_RULE thl);;
let REWRITE_ALL thl = REWRITE_ASSUMS thl THEN REWRITE_TAC thl;;
let USE_IASSUM n =
  USE_THEN ("Z-" ^ string_of_int n);;

let PROVE_ASSUM_ANTECEDENT_TAC n =
  fun ((asl,w) as g) ->
    let assum = assoc ("Z-" ^ string_of_int n) asl in
    let ant,_ = dest_imp (concl assum) in
      SUBGOAL_THEN ant (fun x -> (USE_IASSUM n (fun y-> ASSUME_TAC (MATCH_MP y x)))) g;;

let FALSE_ANTECEDENT_TAC =
  fun ((asl,w) as g) ->
    let l,r = dest_imp w in
    (SUBGOAL_THEN (mk_neg l) (fun x -> REWRITE_TAC[x])) g;;


let REWRITE_ASSUMS thl = RULE_ASSUM_TAC (REWRITE_RULE thl);;
let ONCE_REWRITE_ASSUMS thl = RULE_ASSUM_TAC (ONCE_REWRITE_RULE thl);;

let REWRITE_ALL_TAC l = REWRITE_ASSUMS l THEN REWRITE_TAC l;;

let rec MATCH_MPL thms =
  match thms with
      [thm] -> thm
    | impl::ant::rest ->
        MATCH_MPL ((MATCH_MP impl ant)::rest);;

let rec MATCH_EQ_MPL thms =
  match thms with
      [thm] -> thm
    | impl::ant::rest ->
        MATCH_EQ_MPL ((MATCH_EQ_MP impl ant)::rest);;


(*
MATCH_MPL [ASSUME `a ==> b ==> c ==> d`;ASSUME `a:bool`;ASSUME `b:bool`;ASSUME `c:bool`] ;;
*)


let (USE_ASSUM_LIST: string list -> thm_tactic -> tactic) =
  fun l ttac ((asl,w) as g) ->
    try
      let l' = assoc_list l asl in
      let l'' = map ttac l' in
        (EVERY l'') g
    with Failure _ -> failwith "USE_ASSUM_LIST";;

let (KEEP: string list -> tactic) =
  fun l (asl,w) ->
    try
      let asl' = filter (fun x -> mem (fst x) l) asl in
        ALL_TAC  (asl',w)
    with Failure _ -> failwith "USE_ASSUM_LIST";;


let PROVE_THM_ANTECEDENT_TAC thm =
  let ant,cons = dest_imp (concl thm) in
  SUBGOAL_THEN ant (fun x -> MP_TAC (MATCH_MP thm x));;

let MOVE_TO_FRONT s =
  fun (asl,w) ->
    let k,asl' = remove (fun x -> fst x = s) asl in
      ALL_TAC (k::asl',w);;

let IGNORE x = ALL_TAC;;

let CCONTR_TAC =
  MATCH_MP_TAC (TAUT `(~x ==> F) ==> x`) THEN STRIP_TAC;;

let DISCH_ASS = DISCH_THEN (fun x -> ASSUME_TAC x THEN MP_TAC x);;

let pgoal() =
  !current_goalstack;;
