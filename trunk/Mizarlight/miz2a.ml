(* ========================================================================= *)
(* Mizar Light II                                                            *)
(*                                                                           *)
(*                   Freek Wiedijk, University of Nijmegen                   *)
(* ========================================================================= *)

type mterm = string;;

let parse_context_term s env =
  let ptm,l = (parse_preterm o lex o explode) s in
  if l = [] then
   (term_of_preterm o retypecheck
     (map ((fun (s,ty) -> s,pretype_of_type ty) o dest_var) env)) ptm
  else failwith "Unexpected junk after term";;

let goal_frees (asl,w as g) =
  frees (itlist (curry mk_imp) (map (concl o snd) asl) w);;

let (parse_mterm: mterm -> goal -> term) =
  let ttm = mk_var("thesis",bool_ty) in
  let atm = mk_var("antecedent",bool_ty) in
  let otm = mk_var("opposite",bool_ty) in
  fun s (asl,w as g) ->
    let ant = try fst (dest_imp w) with Failure _ -> atm in
    let opp = try dest_neg w with Failure _ -> mk_neg w in
    let t =
     (subst [w,ttm; ant,atm; opp,otm]
       (parse_context_term s ((goal_frees g) @ [ttm; atm; otm]))) in
    try
      let lhs = lhand (concl (snd (hd asl))) in
      let itm = mk_var("...",type_of lhs) in
      subst [lhs,itm] t
    with Failure _ -> t;;

type stepinfo =
  (goal -> term) option * int option *
  (goal -> thm list) * (thm list -> tactic);;

type step = (stepinfo -> tactic) * stepinfo;;

let TRY' tac thl = TRY (tac thl);;

let (then'_) = fun tac1 tac2 thl -> tac1 thl THEN tac2 thl;;

let standard_prover = TRY' (REWRITE_TAC THEN' MESON_TAC);;
let sketch_prover = K CHEAT_TAC;;
let current_prover = ref standard_prover;;

let (default_stepinfo: (goal -> term) option -> stepinfo) =
  fun t -> t,None,
    (map snd o filter ((=) "=" o fst) o fst),
    (fun thl -> !current_prover thl);;

let ((st'): step -> (goal -> term)  -> step) =
  fun (tac,(t,l,thl,just)) t' -> (tac,(Some t',l,thl,just));;

let (st) = fun stp -> (st') stp o parse_mterm;;

let (((at)): step -> int -> step) =
  fun (tac,(t,l,thl,just)) l' -> (tac,(t,Some l',thl,just));;

let (((from)): step -> int list -> step) =
  fun (tac,(t,l,thl,just)) ll -> (tac,(t,l,
    (fun (asl,_ as g) -> thl g @
      let n = length asl in
      map
        (fun l ->
          if l < 0 then snd (el ((n - l - 1) mod n) asl)
            else assoc (string_of_int l) asl)
        ll),
    just));;

let so x = fun y -> x y from [-1];;

let (((by)): step -> thm list -> step) =
  fun (tac,(t,l,thl,just)) thl' -> (tac,(t,l,(fun g -> thl g @ thl'),just));;

let (((using)): step -> (thm list -> tactic) -> step) =
  fun (tac,(t,l,thl,just)) just' -> (tac,(t,l,thl,just' THEN' just));;

let (step: step -> tactic) = fun (f,x) -> f x;;

let (steps: step list -> tactic) =
  fun stpl ->
    itlist (fun tac1 tac2 -> tac1 THENL [tac2]) (map step stpl) ALL_TAC;;

let (tactics: tactic list -> step) =
  fun tacl -> ((K (itlist ((THEN)) tacl ALL_TAC)),
    default_stepinfo None);;

let (theorem': (goal -> term) -> step list -> thm) =
  let g = ([],`T`) in
  fun t stpl -> prove(t g,steps stpl);;

let (((proof)): step -> step list -> step) =
  fun (tac,(t,l,thl,just)) prf -> (tac,(t,l,thl,K (steps prf)));;

let (N_ASSUME_TAC: int option -> thm_tactic) =
  fun l th (asl,_ as g) ->
    match l with
      None -> ASSUME_TAC th g
    | Some n ->
        warn (n >= 0 && length asl <> n) "*** out of sequence label ***";
        LABEL_TAC (if n < 0 then "=" else string_of_int n) th g;;

let (per: step -> step list list -> step) =
  let F = `F` in
  fun (_,(_,_,thl,just)) cases ->
    (fun (_,_,thl',just') g ->
       let tx (t',_,_,_) =
         match t' with None -> failwith "per" | Some t -> t g in
       let dj = itlist (curry mk_disj)
         (map (tx o snd o hd) cases) F in
       (SUBGOAL_THEN dj
          (EVERY_TCL (map (fun case -> let _,l,_,_ = snd (hd case) in
            (DISJ_CASES_THEN2 (N_ASSUME_TAC l))) cases) CONTR_TAC) THENL
        ([(just' THEN' just) ((thl' g) @ (thl g))] @
           map (steps o tl) cases)) g),
    (None,None,(K []),(K ALL_TAC));;

let (cases: step) =
  (fun _ -> failwith "cases"),default_stepinfo None;;

let (suppose': (goal -> term) -> step) =
  fun t -> (fun _ -> failwith "suppose"),default_stepinfo (Some t);;

let (consider': (goal -> term) list -> step) =
  let T = `T` in
  fun tl' ->
  (fun (t',l,thl,just) (asl,w as g) ->
    let tl = map (fun t' -> t' g) tl' in
    let g' = ((asl @ (map (fun t -> ("",REFL t)) tl)),w) in
    let ex = itlist (curry mk_exists) tl
      (match t' with
         None -> failwith "consider"
       | Some t -> t g') in
    (SUBGOAL_THEN ex
       ((EVERY_TCL (map X_CHOOSE_THEN tl)) (N_ASSUME_TAC l)) THENL
     [just (thl g); ALL_TAC]) g),
  default_stepinfo (Some
    (fun g -> end_itlist (curry mk_conj)
      (map (fun t' -> let t = t' g in mk_eq(t,t)) tl')));;

let (take': (goal -> term) list -> step) =
  fun tl ->
    (fun _ g -> (MAP_EVERY EXISTS_TAC o map (fun t -> t g)) tl g),
    default_stepinfo None;;

let (assume': (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
         None -> failwith "assume"
       | Some t ->
           (DISJ_CASES_THEN2
              (fun th -> REWRITE_TAC[th] THEN
                 N_ASSUME_TAC l th)
              (fun th -> just ((REWRITE_RULE[] th)::(thl g)))
            (SPEC (t g) EXCLUDED_MIDDLE)) g),
    default_stepinfo (Some t);;

let (have': (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
         None -> failwith "have"
       | Some t ->
           (SUBGOAL_THEN (t g) (N_ASSUME_TAC l) THENL
            [just (thl g); ALL_TAC]) g),
    default_stepinfo (Some t);;

let (thus': (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
         None -> failwith "thus"
       | Some t ->
           (SUBGOAL_THEN (t g) ASSUME_TAC THENL
            [just (thl g);
             POP_ASSUM (fun th ->
               N_ASSUME_TAC l th THEN
               EVERY (map (fun th -> REWRITE_TAC[EQT_INTRO th])
                 (CONJUNCTS th)))])
           g),
    default_stepinfo (Some t);;

let (fix': (goal -> term) list -> step) =
  fun tl ->
    (fun _ g -> (MAP_EVERY X_GEN_TAC o (map (fun t -> t g))) tl g),
    default_stepinfo None;;

let (set': (goal -> term) -> step) =
  fun t ->
    let stp =
      (fun (t',l,_,_) g ->
       match t' with
         None -> failwith "set"
       | Some t ->
           let eq = t g in
           let lhs,rhs = dest_eq eq in
           let lv,largs = strip_comb lhs in
           let rtm = list_mk_abs(largs,rhs) in
           let ex = mk_exists(lv,mk_eq(lv,rtm)) in
           (SUBGOAL_THEN ex (X_CHOOSE_THEN lv
              (fun th -> (N_ASSUME_TAC l) (prove(eq,REWRITE_TAC[th])))) THENL
            [REWRITE_TAC[EXISTS_REFL];
             ALL_TAC]) g),
      default_stepinfo (Some t) in
    stp at -1;;

let theorem = theorem' o parse_mterm;;
let suppose = suppose' o parse_mterm;;
let consider = consider' o map parse_mterm;;
let take = take' o map parse_mterm;;
let assume = assume' o parse_mterm;;
let have = have' o parse_mterm;;
let thus = thus' o parse_mterm;;
let fix = fix' o map parse_mterm;;
let set = set' o parse_mterm;;

let iff prfs = tactics [EQ_TAC THENL map steps prfs];;

let (otherwise: ('a -> step) -> ('a -> step)) =
  fun stp x ->
    let tac,si = stp x in
    ((fun (t,l,thl,just) g ->
       REFUTE_THEN (fun th ->
         tac (t,l,K ([REWRITE_RULE[] th] @ thl g),just)) g),
     si);;

let (thesis:mterm) = "thesis";;
let (antecedent:mterm) = "antecedent";;
let (opposite:mterm) = "opposite";;
let (contradiction:mterm) = "F";;

let hence = so thus;;
let qed = hence thesis;;

let h = g o parse_term;;
let f = e o step;;
let ff = e o steps;;
let ee = e o EVERY;;
let fp = f o (fun x -> x proof []);;

let GOAL_HERE = tactics [GOAL_TAC];;
