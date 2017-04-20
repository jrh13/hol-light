(******************************************************************************)
(* FILE          : environment.ml                                             *)
(* DESCRIPTION   : Environment of definitions and pre-proved theorems for use *)
(*                 in automation.                                             *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 8th May 1991                                               *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 12th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

let my_gen_terms = ref ([]:term list);;
let bm_steps = ref (0,0);;


let rec GSPEC th =
  let wl,w = dest_thm th in
  if is_forall w then
      GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
  else th;;

let LIST_CONJ = end_itlist CONJ ;;

let rec CONJ_LIST n th =
  try if n=1 then [th] else (CONJUNCT1 th)::(CONJ_LIST (n-1) (CONJUNCT2 th))
  with Failure _ -> failwith "CONJ_LIST";;

(*----------------------------------------------------------------------------*)
(* Reference variable to hold the defining theorems for operators currently   *)
(* defined within the system. Each definition is stored as a triple. The      *)
(* first component is the name of the operator. The second is the number of   *)
(* the recursive argument. If the operator is not defined recursively, this   *)
(* number is zero. The third component is a list of pairs of type constructor *)
(* names and the theorems that define the behaviour of the operator for each  *)
(* constructor. If the operator is not recursive, the constructor names are   *)
(* empty (null) strings.                                                      *)
(*----------------------------------------------------------------------------*)

let system_defs = ref ([] : (string * (int * (string * thm) list)) list);;

(*----------------------------------------------------------------------------*)
(* new_def : thm -> void                                                      *)
(*                                                                            *)
(* Make a new definition available. Checks that theorem has no hypotheses,    *)
(* then splits it into conjuncts. The variables for each conjunct are         *)
(* specialised and then the conjuncts are made into equations.                *)
(*                                                                            *)
(* For each equation, a triple is obtained, consisting of the name of the     *)
(* function on the LHS, the number of the recursive argument, and the name of *)
(* the constructor used in that argument. This process fails if the LHS is    *)
(* not an application of a constant (possibly to zero arguments), or if more  *)
(* than one of the arguments is anything other than a variable. The argument  *)
(* that is not a variable must be an application of a constructor. If the     *)
(* function is not recursive, the argument number returned is zero.           *)
(*                                                                            *)
(* Having obtained a triple for each equation, a check is made that the first *)
(* two components are the same for each equation. Then, the equations are     *)
(* saved together with constructor names for each, and the name of the        *)
(* operator being defined, and the number of the recursive argument.          *)
(*----------------------------------------------------------------------------*)

let new_def th =
try 
 (let make_into_eqn th =
     let tm = concl th
     in  if (is_eq tm) then th
         else if (is_neg tm) then EQF_INTRO th
         else EQT_INTRO th
  and get_constructor th =
     let tm = lhs (concl th)
     in  let (f,args) = strip_comb tm
     in  let name = fst (dest_const f)
     in  let bools = number_list (map is_var args)
     in  let i = itlist (fun (b,i) n -> if ((not b) && (n = 0)) then i
                                   else if b then n else failwith "") bools 0
     in  if (i = 0)
         then ((name,i),"")
         else ((name,i),fst (dest_const (fst (strip_comb (el (i-1) args)))))
  in  let ([],tm) = dest_thm th
  in  let ths = CONJ_LIST (length (conj_list tm)) th
  in  let ths' = map SPEC_ALL ths
  in  let eqs = map make_into_eqn ths'
  in  let constructs = map get_constructor eqs
  in  let (xl,yl) = hashI setify (List.split constructs)
  in  let (name,i) = if (length xl = 1) then (hd xl) else failwith ""
  in  system_defs := (name,(i,List.combine yl eqs))::(!system_defs)
 ) with Failure _ -> failwith "new_def";;

(*----------------------------------------------------------------------------*)
(* defs : void -> thm list list                                               *)
(*                                                                            *)
(* Returns a list of lists of theorems currently being used as definitions.   *)
(* Each list in the list is for one operator.                                 *)
(*----------------------------------------------------------------------------*)

let defs () = map ((map snd) o snd o snd) (!system_defs);;
let defs_names () = map fst (!system_defs);;

(*----------------------------------------------------------------------------*)
(* get_def : string -> (string # int # (string # thm) list)                   *)
(*                                                                            *)
(* Function to obtain the definition information of a named operator.         *)
(*----------------------------------------------------------------------------*)

let get_def name = try ( assoc name (!system_defs) ) with Failure _ -> failwith "get_def";;

(*----------------------------------------------------------------------------*)
(* Reference variable for a list of theorems currently proved in the system.  *)
(* These theorems are available to the automatic proof procedures for use as  *)
(* rewrite rules. The elements of the list are actually pairs of theorems.    *)
(* The first theorem is that specified by the user. The second is an          *)
(* equivalent theorem in a standard form.                                     *)
(*----------------------------------------------------------------------------*)

let system_rewrites = ref ([] : (thm * thm) list);;

(*----------------------------------------------------------------------------*)
(* CONJ_IMP_IMP_IMP = |- x /\ y ==> z = x ==> y ==> z                         *)
(*----------------------------------------------------------------------------*)

let CONJ_IMP_IMP_IMP =
 prove
  (`((x /\ y) ==> z) = (x ==> (y ==> z))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   BOOL_CASES_TAC `z:bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* CONJ_UNDISCH : thm -> thm                                                  *)
(*                                                                            *)
(* Undischarges the conjuncts of the antecedant of an implication.            *)
(* e.g. |- x /\ (y /\ z) /\ w ==> x  --->  x, y /\ z, w |- x                  *)
(*                                                                            *)
(* Has to check for negations, because UNDISCH processes them when we don't   *)
(* want it to.                                                                *)
(*----------------------------------------------------------------------------*)

let rec CONJ_UNDISCH th =
try
 (let th' = CONV_RULE (REWR_CONV CONJ_IMP_IMP_IMP) th
  in  let th'' = UNDISCH th'
  in  CONJ_UNDISCH th'')
 with Failure _ -> try (if not (is_neg (concl th)) then UNDISCH th else failwith "")
 with Failure _ -> failwith "CONJ_UNDISCH";;

(*----------------------------------------------------------------------------*)
(* new_rewrite_rule : thm -> void                                             *)
(*                                                                            *)
(* Make a new rewrite rule available. Checks that theorem has no hypotheses.  *)
(* The theorem is saved together with an equivalent theorem in a standard     *)
(* form. Theorems are fully generalized, then specialized with unique         *)
(* variable names (genvars), and then standardized as follows:                *)
(*                                                                            *)
(*    |- (h1 /\ ... /\ hn) ==> (l = r)  --->  h1, ..., hn |- l = r            *)
(*    |- (h1 /\ ... /\ hn) ==> ~b       --->  h1, ..., hn |- b = F            *)
(*    |- (h1 /\ ... /\ hn) ==> b        --->  h1, ..., hn |- b = T            *)
(*    |- l = r                          --->  |- l = r                        *)
(*    |- ~b                             --->  |- b = F                        *)
(*    |- b                              --->  |- b = T                        *)
(*                                                                            *)
(* A conjunction of rules may be given. The function will treat each conjunct *)
(* in the theorem as a separate rule.                                         *)
(*----------------------------------------------------------------------------*)

let rec new_rewrite_rule th =
try (if (is_conj (concl th))
  then (map new_rewrite_rule (CONJUNCTS th); ())
  else let ([],tm) = dest_thm th
  in  let th' = GSPEC (GEN_ALL th)
  in  let th'' = try (CONJ_UNDISCH th') with Failure _ -> th'
  in  let tm'' = concl th''
  in  let th''' =
         (if (is_eq tm'') then th''
         else if (is_neg tm'') then EQF_INTRO th''
         else EQT_INTRO th'')
  in system_rewrites := (th,th''')::(!system_rewrites)
 ) with Failure _ -> failwith "new_rewrite_rule";;

(*----------------------------------------------------------------------------*)
(* rewrite_rules : void -> thm list                                           *)
(*                                                                            *)
(* Returns the list of theorems currently being used as rewrites, in the form *)
(* they were originally given by the user.                                    *)
(*----------------------------------------------------------------------------*)

let rewrite_rules () = map fst (!system_rewrites);;

(*----------------------------------------------------------------------------*)
(* Reference variable to hold the generalisation lemmas currently known to    *)
(* the system.                                                                *)
(*----------------------------------------------------------------------------*)

let system_gen_lemmas = ref ([] : thm list);;

(*----------------------------------------------------------------------------*)
(* new_gen_lemma : thm -> void                                                *)
(*                                                                            *)
(* Make a new generalisation lemma available.                                 *)
(* Checks that the theorem has no hypotheses.                                 *)
(*----------------------------------------------------------------------------*)

let new_gen_lemma th =
   if ((hyp th) = [])
   then system_gen_lemmas := th::(!system_gen_lemmas)
   else failwith "new_gen_lemma";;

(*----------------------------------------------------------------------------*)
(* gen_lemmas : void -> thm list                                              *)
(*                                                                            *)
(* Returns the list of theorems currently being used as                       *)
(* generalisation lemmas.                                                     *)
(*----------------------------------------------------------------------------*)

let gen_lemmas () = !system_gen_lemmas;;



(*----------------------------------------------------------------------------*)
(* max_var_depth : term -> int                                                *)
(*                                                                            *)
(* Returns the maximum depth of any variable in a term.                       *)
(* eg. max_var_depth  `PRE (a + SUC c)` = 4                                   *)
(*     max_var_depth  `a` = 1                                                 *)
(*     max_var_depth  `PRE (5 + SUC 2)` = 0                                   *)
(*     max_var_depth  `PRE (a + SUC 2)` = 3                                   *)
(*----------------------------------------------------------------------------*)
(* This is primarily used to limit non-termination. If max_var_depth exceeds  *)
(* a limit the system will fail.                                              *)
(* The algorithm is simple:                                                   *)
(* if constant,numeral,etc then 0                                             *)
(* else if variable then 1                                                    *)
(* else if definition,constructor,accessor then                               *)
(*         if (max_var_depth of arguments) > 0 then result + 1                *)
(*         else 0                                                             *)
(* else if any other combination then max_var_depth of arguments              *)
(*----------------------------------------------------------------------------*)


let rec max_var_depth tm =
  if (is_var tm) then 1
  else if ((is_numeral tm) 
	     || (is_const tm) 
	     || (is_T tm) || (is_F tm)) then 0
  else try 
    let (f,args) = strip_comb tm in
    let fn = (fst o dest_const) f in
    let l = flat [defs_names();all_constructors();all_accessors()] in
    if (mem fn l) then
      let x = itlist max (map max_var_depth args) 0 in
      if (x>0) then x+1 else 0
    else itlist max (map max_var_depth args) 0
  with Failure _ -> 0;;
