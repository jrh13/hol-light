(******************************************************************************)
(* FILE          : generalize.ml                                              *)
(* DESCRIPTION   : Generalization.                                            *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 21st June 1991                                             *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 12th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* is_generalizable : string list -> term -> bool                             *)
(*                                                                            *)
(* Function to determine whether or not a term has the correct properties to  *)
(* be generalizable. It takes a list of accessor function names as its first  *)
(* argument. This is for efficiency. It could compute them itself, but if an  *)
(* external function is going to call is_generalizable many times it is       *)
(* better for the external function to compute the list of accessors.         *)
(*----------------------------------------------------------------------------*)

let is_generalizable accessors tm =
   not ((is_var tm) ||
        (is_explicit_value_template tm) ||
        (is_eq tm) ||
        (try(mem ((fst o dest_const o fst o strip_comb) tm) accessors) 
with Failure _ -> false));;

(*----------------------------------------------------------------------------*)
(* generalizable_subterms : string list -> term -> term list                  *)
(*                                                                            *)
(* Computes the generalizable subterms of a literal, given a list of accessor *)
(* function names.                                                            *)
(*----------------------------------------------------------------------------*)

let generalizable_subterms accessors tm =
 try (setify (find_bm_terms (is_generalizable accessors) tm)
 ) with Failure _ -> failwith "generalizable_subterms";;

(*----------------------------------------------------------------------------*)
(* minimal_common_subterms : term list -> term list                           *)
(*                                                                            *)
(* Given a list of terms, this function removes from the list any term that   *)
(* has one of the other terms as a proper subterm. It also eliminates any     *)
(* duplicates.                                                                *)
(*----------------------------------------------------------------------------*)

let minimal_common_subterms tml =
   let tml' = setify tml
   in  filter
        (fun tm ->  not (exists (fun tm' -> (is_subterm tm' tm) && (not (tm' = tm))) tml'))
         tml';;

(*----------------------------------------------------------------------------*)
(* to_be_generalized : term -> term list -> term -> bool                      *)
(*                                                                            *)
(* This function decides whether a subterm of a literal should be generalized.*)
(* It takes a literal, a list of other literals, and a subterm of the literal *)
(* as arguments. The subterm should be generalized if it occurs in one of the *)
(* other literals, or if the literal is an equality and it occurs on both     *)
(* sides, or if the literal is the negation of an equality and the subterm    *)
(* occurs on both sides.                                                      *)
(*----------------------------------------------------------------------------*)

let to_be_generalized tm tml gen =
 try (let (l,r) = dest_eq (dest_neg tm)
  in  if ((is_subterm gen l) && (is_subterm gen r))
      then true
      else failwith "") with Failure _ ->
 try (let (l,r) = dest_eq tm
  in  if ((is_subterm gen l) && (is_subterm gen r))
      then true
      else failwith "") with Failure _ ->
 (exists (is_subterm gen) tml);;

(*----------------------------------------------------------------------------*)
(* terms_to_be_generalized : term -> term list                                *)
(*                                                                            *)
(* Given a clause, this function determines the subterms of the clause that   *)
(* are to be generalized. For each literal, the function computes the         *)
(* generalizable subterms. It then filters out those subterms that are not to *)
(* be generalized. It only looks at the remaining literals when doing this,   *)
(* not at those already processed. This is legitimate because if the subterm  *)
(* occurs in a previous literal, it would have already been added to the main *)
(* list of subterms that should be generalized. Before returning this main    *)
(* list, the function removes any non-minimal common subterms. This operation *)
(* also removes any duplicates.                                               *)
(*----------------------------------------------------------------------------*)

let terms_to_be_generalized tm =
   let accessors = (all_accessors ())
(* @ (all_constructors()) *)
   in  let rec terms_to_be_generalized' tml =
          if (tml = [])
          then []
          else let h::t = tml
               in  let gens = generalizable_subterms accessors h
               in  let gens' = filter (to_be_generalized h t) gens
               in  gens' @ (terms_to_be_generalized' t)
   in  minimal_common_subterms (terms_to_be_generalized' (disj_list tm));;

(*----------------------------------------------------------------------------*)
(* distinct_var : term list -> type -> term                                   *)
(*                                                                            *)
(* Function to generate a sensibly-named variable of a specified type.        *)
(* Variables that the new variable must be distinct from can be specified in  *)
(* the first argument. The new variable will be named according to the first  *)
(* letter of the top-level constructor in the specified type, or if the type  *)
(* is a simple polymorphic type, the name `x' is used. The actual name will   *)
(* be this name followed by zero or more apostrophes.                         *)
(*----------------------------------------------------------------------------*)

let distinct_var vars ty =
   let letter = try((hd o explode o fst o dest_type) ty) with Failure _ -> "x"
   in  variant vars (mk_var (letter,ty));;

(*----------------------------------------------------------------------------*)
(* distinct_vars : term list -> type list -> term list                        *)
(*                                                                            *)
(* Generates new variables using `distinct_var' for each of the types in the  *)
(* given list. The function ensures that each of the new variables are        *)
(* distinct from each other, as well as from the argument list of variables.  *)
(*----------------------------------------------------------------------------*)

let rec distinct_vars vars tyl =
   if (tyl = [])
   then []
   else let var = distinct_var vars (hd tyl)
        in  var::(distinct_vars (var::vars) (tl tyl));;

(*----------------------------------------------------------------------------*)
(* apply_gen_lemma : term -> thm -> thm                                       *)
(*                                                                            *)
(* Given a term to be generalized and a generalization lemma, this function   *)
(* tries to apply the lemma to the term. The result, if successful, is a      *)
(* specialization of the lemma.                                               *)
(*                                                                            *)
(* The function checks that the lemma has no hypotheses, and then extracts a  *)
(* list of subterms of the conclusion that match the given term and contain   *)
(* all the free variables of the conclusion. The second condition prevents    *)
(* new variables being introduced into the goal clause. The ordering of the   *)
(* subterms in the list is dependent on the implementation of `find_terms',   *)
(* but probably doesn't matter anyway, because the function tries each of     *)
(* them until it finds one that is acceptable.                                *)
(*                                                                            *)
(* Each subterm is tried as follows. A matching between the subterm and the   *)
(* term to be generalized is obtained. This is used to instantiate the lemma. *)
(* The function then checks that when the conclusion of this new theorem is   *)
(* generalized (by replacing the term to be generalized with a variable), the *)
(* function symbol of the term to be generalized no longer appears in it.     *)
(*----------------------------------------------------------------------------*)

let apply_gen_lemma tm th =
try
 (let apply_gen_lemma' subtm =
     (let (_,tm_bind,ty_bind) = term_match [] subtm tm
     in  let (insts,vars) = List.split tm_bind
     in  let th' = ((SPECL insts) o (GENL vars) o (INST_TYPE ty_bind)) th
     in  let gen_conc = subst [(genvar (type_of tm),tm)] (concl th')
         and f = fst (strip_comb tm)
         in  if (is_subterm f gen_conc)
             then failwith ""
             else th')
  in  let ([],conc) = dest_thm th
  in  let conc_vars = frees conc
  in  let good_subterm subtm =
         ((can (term_match [] subtm) tm) && ((subtract conc_vars (frees subtm)) = []))
  in  let subtms = rev (find_terms good_subterm conc)
  in  tryfind apply_gen_lemma' subtms
 ) with Failure _ -> failwith "apply_gen_lemma";;

(*----------------------------------------------------------------------------*)
(* applicable_gen_lemmas : term list -> thm list                              *)
(*                                                                            *)
(* Computes instantiations of generalization lemmas applicable to a list of   *)
(* terms, the terms to be generalized.                                        *)
(*----------------------------------------------------------------------------*)

let applicable_gen_lemmas tml =
   flat (map (fun tm -> mapfilter (apply_gen_lemma tm) (gen_lemmas ())) tml);;

(*----------------------------------------------------------------------------*)
(* generalize_heuristic : (term # bool) -> ((term # bool) list # proof)       *)
(*                                                                            *)
(* Generalization heuristic.                                                  *)
(*                                                                            *)
(* This function first computes the terms to be generalized in a clause. It   *)
(* fails if there are none. It then obtains a list of instantiated            *)
(* generalization lemmas for these terms. Each of these lemmas is transformed *)
(* to a theorem of the form |- x = F. If the original lemma was a negation,   *)
(* x is the argument of the negation. Otherwise x is the negation of the      *)
(* original lemma.                                                            *)
(*                                                                            *)
(* The negated lemmas are added to the clause, and the result is generalized  *)
(* by replacing each of the terms to be generalized by new distinct           *)
(* variables. This generalized clause is returned together with a proof of    *)
(* the original clause from it.                                               *)
(*                                                                            *)
(* The proof begins by specializing the variables that were used to replace   *)
(* the generalized terms. The theorem is then of the form:                    *)
(*                                                                            *)
(*    |- lemma1 \/ lemma2 \/ ... \/ lemman \/ original_clause            (1)  *)
(*                                                                            *)
(* We have a theorem |- lemmai = F for each i between 1 and n. Consider the   *)
(* first of these. From it, the following theorem can be obtained:            *)
(*                                                                            *)
(*    |- lemma1 \/ lemma2 \/ ... \/ lemman \/ original_clause =               *)
(*          F   \/ lemma2 \/ ... \/ lemman \/ original_clause                 *)
(*                                                                            *)
(* Simplifying using |- F \/ x = x, this gives:                               *)
(*                                                                            *)
(*    |- lemma1 \/ lemma2 \/ ... \/ lemman \/ original_clause =               *)
(*                 lemma2 \/ ... \/ lemman \/ original_clause                 *)
(*                                                                            *)
(* From this theorem and (1), we obtain:                                      *)
(*                                                                            *)
(*    |- lemma2 \/ ... \/ lemman \/ original_clause                           *)
(*                                                                            *)
(* Having repeated this process for each of the lemmas, the proof eventually  *)
(* returns a theorem for the original clause, i.e. |- original_clause.        *)
(*----------------------------------------------------------------------------*)

let generalize_heuristic (tm,(ind:bool)) =
try
 (let NEGATE th =
     let ([],tm) = dest_thm th
     in  if (is_neg tm)
         then EQF_INTRO th
         else EQF_INTRO
                 (CONV_RULE
                     (REWR_CONV
                         (SYM (SPEC_ALL (hd (CONJUNCTS NOT_CLAUSES))))) th)
  and ELIM_LEMMA lemma th =
     let rest = snd (dest_disj (concl th))
     in  EQ_MP (CONV_RULE (RAND_CONV (REWR_CONV F_OR))
                          (AP_THM (AP_TERM `(\/)` lemma) rest)) th
  in  let gen_terms = check (fun l ->  not (l = [])) (terms_to_be_generalized tm)
  in  let lemmas = map NEGATE (applicable_gen_lemmas gen_terms)
  in  let tm' = itlist (curry mk_disj) (map (lhs o concl) lemmas) tm
  in  let new_vars = distinct_vars (frees tm') (map type_of gen_terms)
  in  let tm'' = subst (lcombinep (new_vars,gen_terms)) tm'
  in  let countercheck = try counter_check 5 tm'' with Failure _ -> 
    warn true "Could not generate counter example!" ; true
  in if (countercheck = true) then let proof th'' =
         let th' = SPECL gen_terms (GENL new_vars th'')
         in  rev_itlist ELIM_LEMMA lemmas th'
  in   (proof_print_string_l "-> Generalize Heuristic"() ; my_gen_terms := tm''::!my_gen_terms ; ([(tm'',ind)],apply_fproof "generalize_heuristic" (proof o hd) [tm'']))
  else failwith "Counter example failure!"
 ) with Failure _ -> failwith "generalize_heuristic";;


(* Implementation of Aderhold's Generalization techniques: *)

let is_constructor_eq constructor v tm  =
 try (
let (a,b) = dest_eq tm
in let cand_c = ( if ( v = a ) then b
                    else if ( v = b ) then a
                    else failwith "" )
in let cand_name = (fst o dest_const o fst o strip_comb) cand_c
in constructor = cand_name
(* then cand_name else failwith ""*)
) with Failure _ -> false;;


let is_constructor_neq constructor v tm  =
 try (
let tm' = dest_neg tm
in let (a,b) = dest_eq tm'
in let cand_c = ( if ( v = a ) then b
                    else if ( v = b ) then a
                    else failwith "" )
in let cand_name = (fst o dest_const o fst o strip_comb) cand_c
in constructor = cand_name
) with Failure _ -> false;;


let infer_constructor v tm =
try (
     print_term v;print_string " XXX ";print_term tm;print_newline();
     let v_ty = (fst o dest_type) (type_of v)
     in let clist = map fst3 ((shell_constructors o sys_shell_info) v_ty)
     in let conjs = conj_list tm
     in let check_constructor_eq c v tms =
            let res = map (is_constructor_eq c v) tms 
            in if (mem true res) then true
                                 else false
     in let check_constructor_neq c v tms =
            let res = map (is_constructor_neq c v) tms 
            in if (mem true res) then true
                                 else false
     in let check_constructor c all_constr v tms =
            if (check_constructor_eq c v tms) then true
            else let constrs = subtract all_constr [c]
                 in let res = map (fun c -> check_constructor_neq c v tms) constrs
                 in if (mem false res) then false
                                       else true
     in let res = map (fun c -> check_constructor c clist v conjs) clist
     in let reslist = List.combine res clist
     in assoc true reslist
) with Failure _ -> failwith "infer_constructor";;

let get_rec_pos_of_fun f = 
try (
     (fst o get_def o fst o dest_const) f
    ) with Failure _ -> 0;;

let rec is_in_rec_pos subtm tm =
    let (op,args) = strip_comb tm
          in try ( 
               let rec_argn = get_rec_pos_of_fun op
               in if ( (el (rec_argn - 1) args) = subtm ) 
                     then true
                     else failwith ""
                ) with Failure _ -> mem true (map (is_in_rec_pos subtm) args) ;;

let is_var_in_rec_pos v tm =
try (
     if (not (is_var v)) then false
     else if (not (mem v (frees tm))) then false
     else is_in_rec_pos v tm
) with Failure _ -> false;;

let eliminateSelectors tm =
try (
    let vars = frees tm 
    in let vars' = filter (not o (fun v -> is_var_in_rec_pos v tm )) vars
    in if (vars' = []) then tm
       else let rec find_candidate vars tm =
                if ( vars = [] ) then failwith "find_candidate"
                else let var = (hd vars) in try ( (var,infer_constructor var tm) ) 
                                            with Failure _ -> find_candidate (tl vars) tm 
            in let (var,constr) = find_candidate vars' tm
            in let v_ty = (fst o dest_type) (type_of var)
            in let s_info = sys_shell_info v_ty
            in let new_vars = distinct_vars vars (shell_constructor_arg_types constr s_info)
            in let new_subtm = list_mk_icomb constr new_vars
            in let new_tm = subst [new_subtm,var] tm
            in (snd o dest_eq o concl) (REWRITE_CONV (map snd (shell_constructor_accessors constr s_info)) new_tm)
) with Failure _ -> failwith "eliminateSelectors";;


let all_variables =
  let rec vars(acc,tm) =
    if is_var tm then tm::acc
    else if is_const tm then acc
    else if is_abs tm then
      let v,bod = dest_abs tm in
      vars(v::acc,bod)
    else
      let l,r = dest_comb tm in
      vars(vars(acc,r),l) in
  fun tm -> vars([],tm);;

let all_equations =
  let rec eqs(acc,tm) =
    if is_eq tm then tm::acc
    else if is_var tm then acc
    else if is_const tm then acc
    else if is_abs tm then
      let v,bod = dest_abs tm in
      eqs(acc,bod)
    else
      let l,r = dest_comb tm in
      eqs(eqs(acc,r),l) in
  fun tm -> eqs([],tm);;

let rec contains_any tm args =
    if is_var tm then false
    else if is_numeral tm then false
    else if is_const tm then mem ((fst o dest_const) tm) args
    else if is_abs tm then
      let v,bod = dest_abs tm in
      contains_any v args
    else
      let l,r = dest_comb tm in
      (contains_any l args) || (contains_any r args);;

let is_rec_type tm = try( mem ((fst o dest_type o type_of) tm) (shells()) ) with Failure _ -> false;;

let is_generalizable_subterm bad tm =
    (is_rec_type tm) &&
    not ( (is_var tm) || 
          (is_const tm) ||
          (is_numeral tm) ||
          (contains_any tm bad) );; 

(*----------------------------------------------------------------------------*)
(* A set S of terms is called a suitable proposal for some formula phi if each*)
(* t' in S is a generalizable subterm of phi and if there is some t' in S that*)
(* occurs at least twice in phi.                                              *)
(* Here gens is assumed to be the generalizable subterms of phi as found by   *)
(* find_bm_terms. This means that it will contain t' as many times as it was  *)
(* found in phi. Therefore, the occurences of t' in gens are equivalent to its*) 
(* occurences in phi.                                                         *)
(*----------------------------------------------------------------------------*)

let is_suitable_proposal s phi gens =
    ( forall (fun tm -> mem tm gens) s ) && (exists (fun tm -> lcount tm gens > 1) s);;


let checksuitableeq = ref false;; (* equation criterion *)
let newisgen = ref true;; (* Use Aderhold's (true) or Boulton's (false) is_generalizable for terms *)

let is_eq_suitable t eq =
    if (not !checksuitableeq) then true
    else if (not (is_eq eq)) then false
    else let l,r = dest_eq eq in
    if ((is_subterm t r) && (is_subterm t l)) then true 
    else length(find_bm_terms ((=) t) eq) > 1;;
       

let generateProposals tm phi =
    let rec generateProposals' bad tm phi gens =
        let p = [] in
        if (is_eq tm) 
        then let (t1,t2) = dest_eq tm
          in let p1 = (generateProposals' bad t1 phi gens)
          in let p1' = if (is_suitable_proposal [t1] phi gens) then p1@[[t1]] else p1
          in let p = p @ filter (exists (fun t -> is_eq_suitable t tm)) p1'
          in let p2 = (generateProposals' bad t2 phi gens)
          in let p2' = if (is_suitable_proposal [t2] phi gens) then p2@[[t2]] else p2
          in p @ filter (exists (fun t -> is_eq_suitable t tm)) p2'
        else if (is_comb tm)
        then let (op,args) = strip_comb tm
          in let recpos = get_rec_pos_of_fun op
          in let s = if (recpos > 0) then [el (recpos-1) args] else []
          in let p = if (is_suitable_proposal s phi gens) then p@[s] else p
          in p @ flat (map (fun tm -> generateProposals' bad tm phi gens) args)
        else p
    in let bad = (all_accessors()) @ (all_constructors())
    in let gens = if (!newisgen) then find_bm_terms (is_generalizable_subterm bad) phi
                  else find_bm_terms (is_generalizable bad) phi
    in generateProposals' bad tm phi gens;;

let proposal_induction_test s phi =
    let newvars = distinct_vars (frees phi) (map (type_of) s)
    in let subs = List.combine newvars s
    in let newterm = subst subs phi
    in let (unfl,fl) = possible_inductions newterm
    in if (exists (fun v -> (mem v (unfl@fl)) ) newvars ) then true else false;;

let get_proposal_term_occs s phi =
    let gens = find_bm_terms (fun tm -> true) phi
    in let scount = map (fun tm -> lcount tm gens) s
    in itlist (+) scount 0;;

let organizeProposals s phi =
    let stest = map (fun prop -> (prop,proposal_induction_test prop phi)) s
    in let indok = filter (((=) true) o snd) stest
    in let s' = if (indok = []) then (proof_print_string_l "Weak Generalization" (map fst stest)) else (map fst indok)
    in if (length s' = 1) then hd s'
    else let scounted = (rev o sort_on_snd) (map (fun prop -> (prop,lcount prop s')) s')
    in let smax = (snd o hd) scounted
    in let s'' = map fst (filter (((=) smax) o snd) scounted)
    in if (length s'' = 1) then hd s''
    else let soccscounted = (rev o sort_on_snd) (map (fun prop -> (prop,get_proposal_term_occs prop phi)) s'')
    in (fst o hd) soccscounted;;

let generalizeCommonSubterms tm =
    let props = generateProposals tm tm
    in if (props = []) then failwith ""
    else let s = organizeProposals props tm
    in let newvars = distinct_vars (frees tm) (map type_of s)
    in let varcomb = List.combine newvars s
    in (subst varcomb tm,varcomb);;

let rec separate f v v' allrpos tm =
    let replace tm v v' rpos =
        if (not rpos) then tm
        else if (tm = v) then v'
        else (separate f v v' allrpos tm)
    in if (is_comb tm) then ( 
         let (op,args) = strip_comb tm
         in let recpos = get_rec_pos_of_fun op
         in if ((allrpos) && not (op = `(=)`)) 
            then (list_mk_comb (op,(map (fun (t,i) -> replace t v v' ((i = recpos) || (recpos = 0))) (number_list args))))
            else if (op = `(=)`) 
                 then (list_mk_comb(op,[replace (hd args) v v' true;replace ((hd o tl) args) v v' true]))
            else if (op = f) 
                 then (list_mk_comb (op,(map (fun (t,i) -> replace t v v' (i = recpos)) (number_list args))))
            else (list_mk_comb (op,(map (separate f v v' allrpos) args)))
         )
       else tm;;


let rec generalized_apart_successfully v v' tm tm' =
    if (tm' = v') then true
    else if (is_eq tm) then ( let (tm1,tm2) = dest_eq tm 
                           in let (tm1',tm2') = dest_eq tm'
                           in (generalized_apart_successfully v v' tm1 tm1') 
                            && (generalized_apart_successfully v v' tm2 tm2') )           
    else ( let av = all_variables tm
           in let av' = all_variables tm'
           in let varsub = List.combine av av'
           in ((mem (v,v') varsub) && (mem v av'))  );;

let useful_apart_generalization v v' tm gen =
    let eqssub = List.combine (all_equations tm) (all_equations gen)
    in let eqsok = forall (fun (x,y) -> (x=y) || (generalized_apart_successfully v v' x y)) eqssub
    in let countercheck = try counter_check 5 gen with Failure s -> 
    warn true ("Could not generate counter example: " ^ s) ; true
    in eqsok && (generalized_apart_successfully v v' tm gen) && countercheck;;

let generalize_apart tm =
    let is_fun tm = (try( mem ((fst o dest_const o fst o strip_comb) tm) (defs_names ()) ) with Failure _ -> false)
    in let fs = find_bm_terms is_fun tm
    in let dfs = map strip_comb fs
    in let find_f (op,args) dfs = (
           let r = get_rec_pos_of_fun op
           in let arg_filter args args' = 
                 (let v = el (r-1) args
                  in (is_var v) && (mem v (snd (remove_el r args'))))
           in let match_filter (op',args') =
                  ((op' = op) && (arg_filter args args'))
           in can (find match_filter) dfs )
    in let (f,args) = try( find (fun (op,args) -> find_f (op,args) dfs) dfs ) with Failure _ -> failwith ""
    in let v = el ((get_rec_pos_of_fun f) -1) args
    in let v' = distinct_var (frees tm) (type_of v)
	    (*distinct_var (flat (map frees args)) (type_of v)*)
    in let gen = separate f v v' false tm
    in if (useful_apart_generalization v v' tm gen) then (gen,[v',v])
       else let pcs = map fst dfs
            in let restpcs = subtract pcs [f]
            in let recposs = map get_rec_pos_of_fun restpcs
            in let recpos = try (find ((<) 0) recposs) with Failure _ -> 0
            in let gen = if (forall (fun x -> (x = 0) || (x = recpos)) recposs) 
                         then separate f v v' true tm
                         else failwith "not same recpos for all functions"
            in if (useful_apart_generalization v v' tm gen) then (gen,[v',v])
            else failwith "failed";;

(*----------------------------------------------------------------------------*)
(* Reference flag to check if a term has already been generalized so as to    *)
(* avoid multiple proposal generalization because of the waterfall loop.      *)
(*----------------------------------------------------------------------------*)
let checkgen = ref true;;

let generalize_heuristic_aderhold (tm,(ind:bool)) =
if (mem tm !my_gen_terms && !checkgen) then failwith ""
else 
try
 (let ELIM_LEMMA lemma th =
     let rest = snd (dest_disj (concl th))
     in  EQ_MP (CONV_RULE (RAND_CONV (REWR_CONV F_OR))
                          (AP_THM (AP_TERM `(\/)` lemma) rest)) th
  in let (tm',subs) = try( generalize_apart tm ) with Failure _ -> (tm,[])
  in let (new_ap_vars,gen_ap_terms) = List.split subs
  in let (tm'',subs) = try( generalizeCommonSubterms tm' ) with Failure _ -> (tm',[])
  in if (tm = tm'') then failwith ""
  else let (new_vars,gen_terms) = List.split subs 
  in let lemmas = []
  in  let countercheck = try counter_check 5 tm'' with Failure s -> 
    warn true ("Could not generate counter example: " ^ s) ; true
      in if (countercheck = true) then let proof th'' =
      let th' = ((SPECL gen_ap_terms) o (GENL new_ap_vars) o
		    (SPECL gen_terms) o (GENL new_vars)) th''
         in  rev_itlist ELIM_LEMMA lemmas th'
  in   (proof_print_string_l "-> Generalize Heuristic"() ; my_gen_terms := tm''::!my_gen_terms ; ([(tm'',ind)],apply_fproof "generalize_heuristic_aderhold" (proof o hd) [tm'']))
  else failwith "Counter example failure!"
 ) with Failure _ -> failwith "generalize_heuristic";;


let generalize_heuristic_ext (tm,(ind:bool)) =
if (mem tm !my_gen_terms && !checkgen) then failwith ""
else 
try
 (let ELIM_LEMMA lemma th =
     let rest = snd (dest_disj (concl th))
     in  EQ_MP (CONV_RULE (RAND_CONV (REWR_CONV F_OR))
                          (AP_THM (AP_TERM `(\/)` lemma) rest)) th
  in  let lemmas = []
  in let (tm',subs) = try( generalize_apart tm ) with Failure _ -> (tm,[])
  in let (new_ap_vars,gen_ap_terms) = List.split subs
  in let gen_terms = terms_to_be_generalized tm'
  in let _ = check (fun l ->  not (l = [])) (gen_ap_terms@gen_terms) 
  in  let new_vars = distinct_vars (frees tm') (map type_of gen_terms)
  in  let tm'' = subst (lcombinep (new_vars,gen_terms)) tm'
  in  let countercheck = try counter_check 5 tm'' with Failure _ -> 
    warn true "Could not generate counter example!" ; true
  in if (countercheck = true) then let proof th'' =
     let th' = ((SPECL gen_ap_terms) o (GENL new_ap_vars) o
       (SPECL gen_terms) o (GENL new_vars)) th''
         in rev_itlist ELIM_LEMMA lemmas th'
  in   (proof_print_string_l "-> Generalize Heuristic"() ; my_gen_terms := tm''::!my_gen_terms ; ([(tm'',ind)],apply_fproof "generalize_heuristic_ext" (proof o hd) [tm'']))
  else failwith "Counter example failure!"
 ) with Failure _ -> failwith "generalize_heuristic";;
