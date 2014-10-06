(* ========================================================================= *)
(*                                                                           *)
(*   Quantum optics library: utilities.                                      *)
(*                                                                           *)
(*    (c) Copyright, Mohamed Yousri Mahmoud, Vincent Aravantinos, 2012-2013  *)
(*                   Hardware Verification Group,                            *)
(*                   Concordia University                                    *)
(*                                                                           *)
(*           Contact: <mosolim@ece.concordia.ca>, <vincent@ece.concordia.ca> *)
(*                                                                           *)
(* Last update: Feb 27, 2013                                                 *)
(*                                                                           *)
(* ========================================================================= *)

needs "Library/q.ml";;

let EQ_TO_IMP = TAUT `!P Q. (P <=> Q) <=> (P ==> Q) /\ (Q==>P)`;;
let EQ_NOT =  TAUT `!P Q.(~P <=> ~Q) <=> (P <=> Q)`;;
let LET_DEFS = CONJ LET_DEF LET_END_DEF;;

module Pa =
  struct
    include Pa
    let COMPLEX_FIELD = call_with_interface prioritize_complex COMPLEX_FIELD;;
    let SIMPLE_COMPLEX_ARITH =
      call_with_interface prioritize_complex SIMPLE_COMPLEX_ARITH;
  end;;

let HINT_EXISTS_TAC (hs,c as g) =
   let hs = map snd hs in
   let v,c' = dest_exists c in
   let vs,c' = strip_exists c' in
   let hyp_match c h =
     ignore (check (not o exists (C mem vs) o frees) c);
     term_match (subtract (frees c) [v]) c (concl h), h
   in
   let (_,subs,_),h = tryfind (C tryfind hs o hyp_match) (binops `/\` c') in
   let witness =
     match subs with
       |[] -> v
       |[t,u] when u = v -> t
       |_ -> failwith "HINT_EXISTS_TAC not applicable"
   in
   (EXISTS_TAC witness THEN REWRITE_TAC hs) g;;

let GEN_PURE_MP_REWR_TAC sel th =
  let PART_MATCH =
    let concl = snd o dest_imp in
    let body = snd o strip_forall o concl in
    try PART_MATCH (lhs o body) th
    with _ ->
      let f1 = PART_MATCH concl th and f2 = PART_MATCH body th in
      fun t -> try f1 t with _ -> f2 t
  in
  fun (_,c as g) ->
    let th = ref TRUTH in
    let match_term t = try th := PART_MATCH t; true with _ -> false in
    ignore (find_term match_term (sel c));
    let _,big_th = EQ_IMP_RULE (ONCE_REWRITE_CONV[UNDISCH (SPEC_ALL !th)] c) in
    let mp_th = (GEN_ALL o ONCE_REWRITE_RULE[IMP_IMP] o DISCH_ALL) big_th in
    MATCH_MP_TAC mp_th g;;

let PURE_MP_REWR_TAC = GEN_PURE_MP_REWR_TAC I;;

let GEN_MP_REWR_TAC s x =
  GEN_PURE_MP_REWR_TAC s x THEN TRY HINT_EXISTS_TAC THEN ASM_REWRITE_TAC[];;

let MP_REWR_TAC = GEN_MP_REWR_TAC I;;

let MP_REWRITE_TAC = MAP_EVERY MP_REWR_TAC;;

let CASES_REWRITE_TAC th (_,c as g) =
  let PART_MATCH =
    let concl = snd o dest_imp in
    let body = snd o strip_forall o concl in
    try PART_MATCH (lhs o body) th
    with _ ->
      let f1 = PART_MATCH concl th and f2 = PART_MATCH body th in
      fun t -> try f1 t with _ -> f2 t
  in
  let th = ref TRUTH in
  ignore (find_term (fun t -> try th := PART_MATCH t; true with _ -> false) c);
  (ASM_CASES_TAC (lhand (concl !th)) THENL [
    POP_ASSUM (fun x -> REWRITE_TAC[MP !th x] THEN ASSUME_TAC x);
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[NOT_CLAUSES])]) g;;

let wrap f x = f [x];;

let CONJS xs = end_itlist CONJ xs;;

let rec simp_horn_conv =
  let fact (x,y) = if x = [] then y else fail () in
  let rec tl = function [] -> [] | _::xs -> xs in
  fun l ->
    let fixpoint = ref true in
    let l' =
      rev_itlist (fun (hs,cs) (dones,todos) ->
        let facts = flat (mapfilter fact (dones@todos)) in
        let f = filter (not o C mem facts) in
        let hs' = f hs in
        let cs' = filter (not o C mem hs') (f cs) in
        if not (hs' = hs) or not (cs' = cs) then fixpoint := false;
        if (cs' = [] && cs <> [])
        then (dones,tl todos)
        else ((hs',cs')::dones),tl todos)
      l ([],tl l)
    in
    if !fixpoint then l else simp_horn_conv (fst l');;

let horns_of_term =
  let strip_conj = binops `(/\)` in
  fun t -> map (fun t ->
    try
      let h,c = dest_imp t in
      strip_conj h,strip_conj c
    with _ -> [],[t]) (strip_conj t);;

let term_of_horns =
  let term_of_horn = function
    |[],cs -> list_mk_conj cs
    |_,[] -> `T`
    |hs,cs -> mk_imp (list_mk_conj hs,list_mk_conj cs)
  in
  list_mk_conj o map term_of_horn;;

let SIMP_HORN_CONV t =
  TAUT (mk_eq (t,((term_of_horns o simp_horn_conv o horns_of_term) t)));;

let SIMP_HORN_TAC =
  ASSUM_LIST (fun xs ->
    TRY (fun g -> (MP_TAC (CONJS xs) THEN REWRITE_TAC[IMP_IMP]) g)
    THEN CONV_TAC (TOP_DEPTH_CONV (CHANGED_CONV SIMP_HORN_CONV))
    THEN REWRITE_TAC xs);;

let rec fixpoint f x =
  let y = f x in
  if y = x then y else fixpoint f y;;

let gimp_imp =
  let rec self vars premisses t =
    try
      let v,b = dest_forall t in
      self (v::vars) premisses b
    with _ ->
      try
        let p,c = dest_imp t in
        self vars (p::premisses) c
      with _ ->
        let body =
          match premisses with
          |[] -> t
          |_::_ -> mk_imp(list_mk_conj (rev premisses),t)
        in
        list_mk_forall(rev vars,body)
  in
  self [] [];;

let GIMP_IMP_CONV t = MESON[](mk_eq(t,gimp_imp t));;

let GIMP_IMP = CONV_RULE GIMP_IMP_CONV;;

let MATCH_TRANS thm1 thm2 =
  GEN_ALL (DISCH_ALL (MATCH_MP thm2 (UNDISCH (SPEC_ALL thm1))));;

let GCONV_TAC = CONV_TAC o DEPTH_CONV o CHANGED_CONV;;

let LET_RULE thm = REWRITE_RULE[LET_DEF;LET_END_DEF] thm;;
let LET_RULE_L l thm = REWRITE_RULE([LET_DEF;LET_END_DEF]@l) thm;;
let SPEC_V (x,v) thm = (Pa.SPEC v o Pa.GEN x  o SPEC_ALL) thm;;
