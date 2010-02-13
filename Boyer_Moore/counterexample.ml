(******************************************************************************)
(* FILE          : counterexample.ml                                          *)
(* DESCRIPTION   : Simple counterexample checker                              *)
(*                 Based on ideas and suggestions from S. Wilson              *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* Reference of how many examples will be tried on each check.                *)
(* Set to 0 to turn off counterexample checker.                               *)
(*----------------------------------------------------------------------------*)

let counter_check_num = ref 5;;

let counter_checks t =
  counter_check_num := t;;


(*----------------------------------------------------------------------------*)
(* Reference to count how many counterexamples were found during a proof.     *)
(*----------------------------------------------------------------------------*)

let counterexamples = ref 0;;

let inc_counterexamples () = counterexamples := !counterexamples + 1 ; ();;


(*----------------------------------------------------------------------------*)
(* inst_type                                                                  *)
(*----------------------------------------------------------------------------*)
(* Hacky function to instantiate types.                                       *)
(* I'm surprised there is no such function in HOL Light (or perhaps I just    *)
(* haven't found it yet?).                                                    *)
(*----------------------------------------------------------------------------*)
(* Creates a variable of the given type. Instantiates the term using "inst"   *)
(* then returns the type of the resulting term.                               *)
(*----------------------------------------------------------------------------*)

let inst_type : (hol_type * hol_type) list -> hol_type -> hol_type =
  fun ins ty ->
    let tm = mk_var ("x",ty) in
    let itm = inst ins tm in
    type_of itm;;


(*----------------------------------------------------------------------------*)
(* shell_type_match                                                           *)
(*----------------------------------------------------------------------------*)
(* Does a deep search to check if a type can be properly grounded to a        *)
(* combination of types defined in the shell.                                 *)
(* Returns the type instantiation pairs to make it happen.                    *)
(* Variable types are instantiated by `:num`.                                 *)
(*----------------------------------------------------------------------------*)
(* If the type is an instance of a type constructor (is_type) then it is      *)
(* split. The name of the constructor is looked up in the system shells list. *)
(* The arguments are checked recursively.                                     *)
(* If it's not an instance of a  type constructor, we try to replace it by    *)
(* `:num`.                                                                    *)
(*----------------------------------------------------------------------------*)

let rec shell_type_match : hol_type -> (hol_type * hol_type) list =
  fun ty ->
    if (is_type ty) then
      let tys,tyargs = dest_type ty in
      let info = try sys_shell_info tys
	  with Failure _ -> failwith ("No shell defined for type '" ^ 
				    (string_of_type ty) ^ "'") in
      itlist union (map shell_type_match tyargs) []
    else
       try type_match ty `:num` [] 
	with Failure _ -> failwith ("Unknown type '" ^ 
				    (string_of_type ty) ^ "' that doesn't match 'num'!");;


(*----------------------------------------------------------------------------*)
(* HL_rewrite_ground_term : term -> term                                      *)
(*                                                                            *) 
(* Uses HOL Light's REWRITE_CONV to rewrite a ground term.                    *)
(* The function and accessor definitions are used as rewrite rules.           *)
(* This reduces valid expressions to `T`.                                     *)
(*----------------------------------------------------------------------------*)

let HL_rewrite_ground_term tm =
(* ((proof_print_newline) o (proof_print_term) o (proof_print_string "Checking:")) tm ;*)
  if (frees tm = []) then 
(*    let rules = (union ((flat o defs) ()) (all_accessor_thms ())) *)
(* let rules = (union (rewrite_rules ()) (all_accessor_thms ())) *)
    let numred = try (rhs o concl o NUM_REDUCE_CONV) tm with Failure _ -> tm in
    if (is_T numred) then numred else
    let rew = REWRITE_CONV (union (rewrite_rules ()) (all_accessor_thms ())) 
    in (rhs o concl o rew) tm
  else failwith ("rewrite_ground_term: free vars in term: " ^ (string_of_term tm));;



let HL_rewrite_ground_term' tm =
  if (frees tm = []) then 
(*    let rules = (union ((flat o defs) ()) (all_accessor_thms ())) *)
    let rules = (union ((flat o defs) ()) (all_accessor_thms ())) in
    let arith_rules = [PRE;ADD;MULT;EXP;EVEN;ODD;LE;LT;GE;GT;SUB] in
(* Need to apply preprocessing similar to add_def in environment.ml *)
    let rew = REWRITE_CONV (ARITH :: (subtract rules arith_rules))
    in (rhs o concl o rew) tm
  else failwith ("rewrite_ground_term: free vars in term: " ^ (string_of_term tm));;

(*----------------------------------------------------------------------------*)
(* random_example : int -> hol_type -> term                                   *)
(*----------------------------------------------------------------------------*)
(* Creates a random example of a given type.                                  *)
(* The first argument is a maximum depth so as to control the size of the     *)
(* example.                                                                   *)
(*----------------------------------------------------------------------------*)
(* Uses "shell_type_match" in order to ground the type to a combination of    *)
(* types defined as shells. Therefore, all variable types are instantiated to *)
(* `:num`.                                                                    *)
(* Instantiates the arg_types of the shell for each constructor, then uses    *)
(* mk_cons_type to create proper types for the constructors. Having those and *)
(* by using mk_mconst creates the constructors as terms.                      *)
(* random_example is called recursively for every constructor argument, while *)
(* decreasing the maxdepth to ensure termination.                             *)
(* If maxdepth is reached, we just pick randomly one of the base              *)
(* constructors.                                                              *)
(*----------------------------------------------------------------------------*)
(* NOTE: The current version can still afford  a few optimisations.           *)
(* eg. The preprocessing so as to ground the given type should only happen    *)
(* once.                                                                      *)
(* NOTE: We could optimise this function further by accommodating the         *)
(* constructors as terms (rather than or in addition to strings) within the   *)
(* shell.                                                                     *)
(*----------------------------------------------------------------------------*)

let random_example : int -> hol_type -> term =
  let rec random_example': int->int->hol_type->term =
    fun origdepth maxdepth ty ->
      let tyi = shell_type_match ty in
      let ty' = inst_type tyi ty in
      let tystr,typarams = dest_type ty' in
      let sinfo = sys_shell_info tystr in
      let ocons = shell_constructors sinfo in
      let sh_arg_types = shell_arg_types sinfo in
      
      let arg_type_pairs = zip sh_arg_types typarams in
      let arg_types_matches = try
	itlist (fun (x,y) l -> type_match x y l) arg_type_pairs tyi 
      with Failure _ -> failwith "Shell argument types cannot be matched." in
      
      let mk_cons_type = fun arglist ->
	List.fold_left (fun ty i -> mk_type ("fun",[i;ty])) ty' (rev arglist) in
      let inst_cons = map (fun x,y,_ -> x,map (inst_type arg_types_matches) y) ocons in
      let mk_cons = fun x,y ->
	try let n = num_of_string x in (mk_numeral n),y 
	with Failure _ ->  mk_mconst(x,(mk_cons_type y)),y in
      let cons = map mk_cons inst_cons in

      let terminal_filter = fun (_,l) -> (l=[]) in
      let tcons,ntcons = partition terminal_filter cons in

      if (maxdepth > 1) then
	let prob = 200/((maxdepth-1)*3) in
(*	let newdepth = origdepth / (length cons) in*)
	let newdepth = maxdepth - 1 in
	let selcons = if ((Random.int 100) <= prob) then tcons else ntcons in
	let cconstm,cconsargs = List.nth selcons (Random.int (length selcons)) in
	let args = (map (random_example' origdepth newdepth) cconsargs) in
	List.fold_left (fun x y ->  mk_comb (x,y)) cconstm args
      else
	(fst o hd) tcons
  in fun maxdepth ty -> random_example' maxdepth maxdepth ty;;
       
(*	print_string "*" ; print_term cconstm ; print_string "*" ; print_type (type_of cconstm); print_newline (); *)
(* 	map (fun x -> print_term x ; print_string ":" ; print_type (type_of x); print_newline()) args ; *)
(* 	print_newline (); *)


let random_grounding maxdepth tm =
  let vars = frees tm in
  let types = map type_of vars in
  let examples = map (random_example maxdepth) types in
  let pairs = zip vars examples in
  let insts = map (fun v,e -> term_match [] v e) pairs in
  itlist instantiate insts tm;;


let counter_check_once maxdepth tm =
  let tm' = random_grounding maxdepth tm in
  let tm'' = HL_rewrite_ground_term tm' in 
  if (is_T(tm'')) then true else let junk = 
  warn (!proof_printing) ("Found counterexample for " ^ string_of_term(tm) ^ " : " ^ string_of_term(tm')) in
  inc_counterexamples() ; false;; 

let rec counter_check_n maxdepth n tm =
  if (n<=0) then true
  else if (counter_check_once maxdepth tm) then counter_check_n maxdepth (n-1) tm
  else false;;

let counter_check maxdepth tm = 
  counter_check_n maxdepth !counter_check_num tm;;
