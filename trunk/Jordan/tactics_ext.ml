(* This file is in severe need of a rewrite! *)

unambiguous_interface();;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* A printer that reverses the assumption list *)
(* ------------------------------------------------------------------------- *)

(*

   Objective version of HOL-light uses (rev asl) in the method print_goal.
   This means that the numbers printed next to the assumptions
   are the reverse of the numbering in the list.

   I want it the opposite way.
   This reverses the numbering on the assumption list,
   so that the printed numbers match the list order.

   To use, type
   #install_printer print_rev_goal;;
   #install_printer print_rev_goalstack;;

   To restore HOL-light defaults, type
   #install_printer print_goal;;
   #install_printer print_goalstack;;

*)

let (print_rev_goal:goal->unit) =
  fun (asl,w) ->
    print_newline();
    if asl <> [] then (print_hyps 0 (asl); print_newline()) else ();
    print_qterm w; print_newline();;

let (print_rev_goalstate:int->goalstate->unit) =
  fun k gs -> let (_,gl,_) = gs in
              let n = length gl in
              let s = if n = 0 then "No subgoals" else
                        (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
                     ^" ("^(string_of_int n)^" total)" in
              print_string s; print_newline();
              if gl = [] then () else
              do_list (print_rev_goal o C el gl) (rev(0--(k-1)));;

let (print_rev_goalstack:goalstack->unit) =
  fun l ->
    if l = [] then print_string "Empty goalstack"
    else if tl l = [] then
      let (_,gl,_ as gs) = hd l in
      print_rev_goalstate 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_rev_goalstate p' gs;;

#install_printer print_rev_goal;;
#install_printer print_rev_goalstack;;




(* ------------------------------------------------------------------ *)
(* SOME EASY TACTICS *)
(* ------------------------------------------------------------------ *)

let TAUT_TAC t = (MATCH_MP_TAC (TAUT t));;

let REP_GEN_TAC = REPEAT GEN_TAC;;

let SUBGOAL_TAC t = SUBGOAL_THEN t MP_TAC;;

let DISCH_ALL_TAC = REP_GEN_TAC THEN
  let tac = TAUT_TAC `(b ==> a==> c) ==> (a /\ b ==> c)` in
  (REPEAT ((REPEAT tac) THEN DISCH_TAC)) THEN LABEL_ALL_TAC;;

(* ------------------------------------------------------------------ *)
(* TACTICS BY NUMBER. These are probably best avoided.
   NB:
   The numbering is that in the asm list -- not the printed numbers!  *)
(* ------------------------------------------------------------------ *)

let (UNDISCH_EL_TAC:int -> tactic) =
 fun i (asl,w) ->
   try let sthm,asl' = (el i asl),(drop i asl) in
        let tm = concl (snd (el i asl)) in
       let thm = snd sthm in
       null_meta,[asl',mk_imp(tm,w)],
       fun i [th] -> MP th (INSTANTIATE_ALL i thm)
   with Failure _ -> failwith "UNDISCH_EL_TAC";;

(* remove hypotheses by number *)
let rec (POPL_TAC:int list ->tactic) =
  let (POP_TAC:int->tactic) =
    fun i -> (UNDISCH_EL_TAC i) THEN (TAUT_TAC `B ==> (A==>B)`) in
  let renumber i =
    map(fun j -> if j<=i then j else (j-1)) in
  function [] -> ALL_TAC |
      (i::b) -> (POP_TAC i) THEN (POPL_TAC (renumber i b));;

let rec (UNDISCH_LIST:int list -> tactic) =
  let renumber i =
    map(fun j -> if j<=i then j else (j-1)) in
  function [] -> ALL_TAC |
      (i::b) -> (UNDISCH_EL_TAC i) THEN (UNDISCH_LIST (renumber i b));;

(* ------------------------------------------------------------------ *)
(*   Transformations of Hypothesis List by LABELS                     *)
(* ------------------------------------------------------------------ *)

type goalthm = goal -> thm;;

let (HYP_INT:int->goalthm) =
     fun i->
     fun ((asl,_):goal) ->
     snd (el i asl);;

let (HYP:string->goalthm) =
  fun s (asl,w) ->
    try assoc s asl
      with Failure _ -> assoc ("Z-"^s) asl;;

let (THM:thm->goalthm) =
     fun thm ->
     fun (_:goal) -> thm;;

let (H_RULER: (thm list->thm->thm)->(goalthm list)-> goalthm -> tactic) =
     fun rule gthl gthm ->
     fun ((asl,w) as g:goal) ->
     let thl =  map (fun x-> (x g)) gthl in
     let th = rule thl  (gthm g) in
     ASSUME_TAC th g;;

(* The next few term rules into goal_rules *)
(* H_type (x:type) should return an object
   similar to x but with thms made into goalthms *)

let (H_RULE_LIST: (thm list->thm->thm)->(goalthm list)-> goalthm -> goalthm) =
     fun rule gthl gthm g ->
     let thl =  map (fun x-> (x g)) gthl in
     rule thl  (gthm g);;

let H_RULE2 (rule:thm->thm->thm) =
  fun gthm1 gthm2 -> H_RULE_LIST (fun thl th -> rule (hd thl) th) [gthm1] gthm2;;

let H_RULE (rule:thm->thm) =  fun gthm -> H_RULE_LIST (fun _ th -> rule th) [] gthm;;

let (H_TTAC : thm_tactic -> goalthm -> tactic ) =
  fun ttac gthm g -> (ttac (gthm g) g);;

let H_ASSUME_TAC = H_TTAC ASSUME_TAC;;
let INPUT = fun gth -> (H_ASSUME_TAC gth) THEN LABEL_ALL_TAC;;

let H_VAL2 (rule:thm->thm->thm) =
  fun gthm1 gthm2 -> H_RULER (fun thl th -> rule (hd thl) th) [gthm1] gthm2;;

let H_CONJ = H_VAL2(CONJ);;
let H_MATCH_MP = H_VAL2(MATCH_MP);;

let H_REWRITE_RULE gthml gth = H_RULER REWRITE_RULE gthml gth;;
let H_ONCE_REWRITE_RULE gthml gth = H_RULER ONCE_REWRITE_RULE gthml gth;;
let H_SIMP_RULE = H_RULER SIMP_RULE;;

let H_VAL (rule:thm->thm) = fun gthm -> H_RULER (fun _ th -> rule th) [] gthm;;
let H = H_VAL;;

let H_CONJUNCT1 = H_VAL CONJUNCT1;;
let H_CONJUNCT2 = H_VAL CONJUNCT2;;
let H_EQT_INTRO = H_VAL EQT_INTRO;;
let H_EQT_ELIM  = H_VAL EQT_ELIM;;
let H_SPEC = fun t -> H_VAL(SPEC t);;
let H_GEN = fun t -> H_VAL(GEN t);;
let H_DISJ1 = C (fun t -> H_VAL ((C DISJ1) t));;
let H_DISJ2 =  (fun t -> H_VAL (( DISJ2) t));;
  (* beware! One is inverted here. *)
let H_NOT_ELIM = H_VAL (NOT_ELIM);;
let H_NOT_INTRO = H_VAL (NOT_INTRO);;
let H_EQF_ELIM = H_VAL (EQF_ELIM);;
let H_EQF_INTRO = H_VAL (EQF_INTRO);;
let (&&&) = H_RULE2 CONJ;;

let (H_UNDISCH_TAC:goalthm -> tactic) =
  fun gthm g ->
    let tm = concl(gthm g) in
    UNDISCH_TAC tm g;;



(* let upgs tac gs = by tac gs;; *)

let (thm_op:goalthm->goalthm->goalthm) =
  fun gt1 gt2 g ->
    if (is_eq (snd (strip_forall (concl (gt1 g)))))
    then REWRITE_RULE[gt1 g] (gt2 g) else
    MATCH_MP (gt1 g) (gt2 g);;

let (COMBO:goalthm list-> goalthm) =
  fun gthl -> end_itlist thm_op gthl;;

let INPUT_COMBO = INPUT o COMBO;;

