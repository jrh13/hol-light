(******************************************************************************)
(* FILE          : waterfall.ml                                               *)
(* DESCRIPTION   : `Waterfall' of heuristics. Clauses pour over.              *)
(*                 Some evaporate. Others collect in a pool to be cleaned up. *)
(*                 Heuristics that act on a clause send the new clauses to    *)
(*                 the top of the waterfall.                                  *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 9th May 1991                                               *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 12th August 1992                                           *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

(*============================================================================*)
(* Some auxiliary functions                                                   *)
(*============================================================================*)


(*----------------------------------------------------------------------------*)
(* proves : thm -> term -> bool                                               *)
(*                                                                            *)
(* Returns true if and only if the theorem proves the term without making any *)
(* assumptions.                                                               *)
(*----------------------------------------------------------------------------*)

let proves th tm =
   (let (hyp,concl) = dest_thm th
    in  (hyp = []) && (concl = tm));;

(*----------------------------------------------------------------------------*)
(* apply_proof : proof -> term list -> proof                                  *)
(*                                                                            *)
(* Converts a proof into a new proof that checks that the theorems it is      *)
(* given have no hypotheses and have conclusions equal to the specified       *)
(* terms. Used to make a proof robust.                                        *)
(*----------------------------------------------------------------------------*)

let apply_proof f tms ths =
try
   (if (itlist (fun (tm,th) b -> (proves th tm) && b) (List.combine tms ths) true)
    then (f ths)
    else failwith ""
   ) with Failure _ -> failwith "apply_proof";;

(*============================================================================*)
(* The `waterfall' for heuristics                                             *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* proof_printing : bool                                                      *)
(*                                                                            *)
(* Assignable variable. If true, clauses are printed as they are `poured'     *)
(* over the waterfall.                                                        *)
(*----------------------------------------------------------------------------*)

let proof_printing = ref false;;

(*----------------------------------------------------------------------------*)
(* proof_printer : bool -> bool                                               *)
(*                                                                            *)
(* Function for setting the flag that controls the printing of clauses as     *)
(* are `poured' over the waterfall.                                           *)
(*----------------------------------------------------------------------------*)

let proof_printer state =
   let old_state = !proof_printing
   in  proof_printing := state; old_state;;

(*----------------------------------------------------------------------------*)
(* proof_print_depth : int                                                    *)
(*                                                                            *)
(* Assignable variable. A number indicating the `depth' of the proof and more *)
(* practically the number of spaces printed before a term.                    *)
(*----------------------------------------------------------------------------*)

let proof_print_depth = ref 0;;

(*----------------------------------------------------------------------------*)
(* inc_print_depth : * -> *                                                   *)
(*                                                                            *)
(* Identity function that has the side-effect of incrementing the             *)
(* print_proof_depth.                                                         *)
(*----------------------------------------------------------------------------*)

let inc_print_depth x = (proof_print_depth := !proof_print_depth + 1; x);;

(*----------------------------------------------------------------------------*)
(* dec_print_depth : * -> *                                                   *)
(*                                                                            *)
(* Identity function that has the side-effect of decrementing the             *)
(* print_proof_depth.                                                         *)
(*----------------------------------------------------------------------------*)

let dec_print_depth x =
   if (!proof_print_depth < 1)
   then (proof_print_depth := 0; x)
   else (proof_print_depth := !proof_print_depth - 1; x);;

(*----------------------------------------------------------------------------*)
(* proof_print_term : term -> term                                            *)
(*                                                                            *)
(* Identity function on terms that has the side effect of printing the term   *)
(* if the `proof_printing' flag is set to true.                               *)
(*----------------------------------------------------------------------------*)

let proof_print_term tm =
   if !proof_printing
   then (print_string (implode (replicate " " !proof_print_depth));
         print_term tm; print_newline () ; tm)
   else tm;;

let proof_print_thm thm =
   if !proof_printing
   then ( print_thm thm; print_newline (); print_newline());;

let proof_print_tmi (tm,i) =
   if !proof_printing
   then ( proof_print_term tm; print_string " ("; print_bool i; print_string ")"; (tm,i) )
   else (tm,i);;


(*
let proof_print_clause cl =
   if !proof_printing
   then (
         match cl with  
         | Clause_proved thm -> (print_thm thm; print_newline (); cl)
         | _ -> cl
        )
   else cl;;
*)
(*----------------------------------------------------------------------------*)
(* proof_print_newline : * -> *                                               *)
(*                                                                            *)
(* Identity function that has the side effect of printing a newline if the    *)
(* `proof_printing' flag is set to true.                                      *)
(*----------------------------------------------------------------------------*)

let proof_print_newline x =
   if !proof_printing
   then (print_newline (); x)
   else x;;

let proof_print_string s x =
   if !proof_printing
   then (print_string s; x)
   else x;;

let proof_print_string_l s x =
   if !proof_printing
   then (print_string s; print_newline (); x)
   else x;;

(*----------------------------------------------------------------------------*)
(* Recursive type for holding partly processed clauses.                       *)
(*                                                                            *)
(* A clause is either still to be proved, has been proved, or can be proved   *)
(* once sub-clauses have been. A clause that is still to be proved carries a  *)
(* flag indicating whether or not it is an induction step.                    *)
(*----------------------------------------------------------------------------*)

type clause_tree = Clause of (term * bool)
                    | Clause_proved of thm
                    | Clause_split of clause_tree list * (thm list -> thm);;

let rec proof_print_clausetree cl =
   if !proof_printing
   then ( proof_print_string_l "Clause tree:" (); match cl with
   | Clause (tm,bool) -> (print_term tm; print_newline ())
   | Clause_proved thm -> (print_thm thm; print_newline())
   | Clause_split (tlist,proof) -> (print_string "Split -> "; print_int (length tlist); print_newline () ;
                                    let void = map proof_print_clausetree tlist in () ));;

(*----------------------------------------------------------------------------*)
(* waterfall : ((term # bool) -> ((term # bool) list # proof)) list ->        *)
(*             (term # bool) ->                                               *)
(*             clause_tree                                                    *)
(*                                                                            *)
(* `Waterfall' of heuristics. Takes a list of heuristics and a term as        *)
(* arguments. Each heuristic should fail if it can do nothing with its input. *)
(* Otherwise the heuristic should return a list of new clauses to be proved   *)
(* together with a proof of the original clause from these new clauses.       *)
(*                                                                            *)
(* Clauses that are not processed by any of the heuristics are placed in a    *)
(* leaf node of the tree, to be proved later. The heuristics are attempted in *)
(* turn. If a heuristic returns an empty list of new clauses, the proof is    *)
(* applied to an empty list, and the resultant theorem is placed in the tree  *)
(* as a leaf node. Otherwise, the tree is split, and each of the new clauses  *)
(* is passed to ALL of the heuristics.                                        *)
(*----------------------------------------------------------------------------*)

let nth_tail n l = if (n > length l) then [] 
                   else let rec repeattl l i = 
                                   if ( i = 0 ) then l 
                                   else tl (repeattl l (i-1)) 
                        in repeattl l n;;


let rec waterfall heuristics tmi =
   bm_steps :=  hashI ((+) 1) !bm_steps;
   let rec flow_on_down rest_of_heuristics tmi =
      if (is_F (fst tmi)) then (failwith "cannot prove")
      else if (rest_of_heuristics = []) then (Clause tmi)
      else try ((let (tms,f) = hd rest_of_heuristics tmi
              in if (tms = []) then (proof_print_string "Proven:" (); proof_print_thm (f []) ; Clause_proved (f []))
                 else  if ((tl tms) = []) then
                     (Clause_split ([waterfall heuristics (hd tms)],f))
                  else Clause_split
                        ((dec_print_depth o
                          map (waterfall heuristics o proof_print_newline) o
                          inc_print_depth) tms,
                         f))
           )with Failure s -> (if (s = "cannot prove")
                then failwith s
                else (flow_on_down (tl rest_of_heuristics) tmi)
           )
   in flow_on_down heuristics (proof_print_tmi tmi);;


let rec filtered_waterfall heuristics warehouse tmi =
   bm_steps :=  hashI ((+) 1) !bm_steps;
   if (max_var_depth (fst tmi) > 12) then let void = (warn true "Reached maximum depth!") in failwith "cannot prove"
   else
   let heurn = try (assoc (fst tmi) warehouse) with Failure _ -> 0 in
   let warehouse = (if (heurn > 0) then 
     let void = proof_print_string ("Warehouse kicking in! Skipping " ^ string_of_int(heurn) ^ " heuristic(s)") () ; in
     let void = proof_print_newline () in
     (List.remove_assoc (fst tmi) warehouse) else (warehouse)) in
   let rec flow_on_down rest_of_heuristics tmi it =
      if (is_F (fst tmi)) then (failwith "cannot prove")
      else let rest_of_heuristics = nth_tail heurn rest_of_heuristics in
         if (rest_of_heuristics = []) then (Clause tmi)
         else try (let (tms,f) = hd rest_of_heuristics tmi
              in if (tms = []) then (proof_print_string "Proven:" (); proof_print_thm (f []) ; Clause_proved (f []))
                 else if ((tl tms) = []) then Clause_split ([filtered_waterfall heuristics (((fst tmi),it)::warehouse) (hd tms)],f)
                                    else Clause_split
                                           ((dec_print_depth o
                                             map (filtered_waterfall heuristics (((fst tmi),it)::warehouse) o proof_print_newline) o
                                             inc_print_depth) tms,
                                             f) 
             )with Failure s -> (
                  if (s = "cannot prove")
                  then failwith s
                  else (flow_on_down (tl rest_of_heuristics) tmi (it+1))
           )
   in flow_on_down heuristics ((hashI proof_print_term) tmi) 1;;

(* in
                 let fringe = fringe_of_clause_tree restree in
                 if (fringe = []) then restree
                 else ( waterfall_warehouse := ((fst tmi),it)::(!waterfall_warehouse) ; restree ) *)


(*----------------------------------------------------------------------------*)
(* fringe_of_clause_tree : clause_tree -> (term # bool) list                  *)
(*                                                                            *)
(* Computes the fringe of a clause_tree, including in the resultant list only *)
(* those clauses that remain to be proved.                                    *)
(*----------------------------------------------------------------------------*)

let rec fringe_of_clause_tree tree =
   match tree with
    | (Clause tmi) -> [tmi]
    | (Clause_proved _) -> []
    | (Clause_split (trees,_)) -> (flat (map fringe_of_clause_tree trees));;

(*----------------------------------------------------------------------------*)
(* prove_clause_tree : clause_tree -> proof                                   *)
(*                                                                            *)
(* Given a clause_tree, returns a proof that if given theorems for the        *)
(* unproved clauses in the tree, returns a theorem for the clause at the root *)
(* of the tree. The list of theorems must be in the same order as the clauses *)
(* appear in the fringe of the tree.                                          *)
(*----------------------------------------------------------------------------*)

let prove_clause_tree tree ths =
try(
   let rec prove_clause_trees trees ths =
      if (trees = []) then ([],ths)
      else let (th,ths') = prove_clause_tree' (hd trees) ths
           in  let (thl,ths'') = prove_clause_trees (tl trees) ths'
           in  (th::thl,ths'')
   and prove_clause_tree' tree ths =
      match tree with
       | (Clause (tm,_)) ->
            (let th = hd ths
             in  if (proves th tm)
                 then (th,tl ths)
                 else failwith "prove_clause_tree")
       | (Clause_proved th) -> (th,ths)
       | (Clause_split (trees,f)) ->
            (let (thl,ths') = prove_clause_trees trees ths
             in  (f thl,ths'))
   in (let (th,[]) = (prove_clause_tree' tree ths) in th)
    ) with Failure _ -> failwith "prove_clause_tree";;

(*============================================================================*)
(* Eliminating instances in the `pool' of clauses remaining to be proved      *)
(*                                                                            *)
(* Constructing partial orderings is probably overkill. It may only be        *)
(* necessary to split the clauses into two sets, one of most general clauses  *)
(* and the rest. This would still be computationally intensive, but it would  *)
(* avoid comparing two clauses that are both instances of some other clause.  *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* inst_of : term -> term -> thm -> thm                                       *)
(*                                                                            *)
(* Takes two terms and computes whether the first is an instance of the       *)
(* second. If this is the case, a proof of the first term from the second     *)
(* (assuming they are formulae) is returned. Otherwise the function fails.    *)
(*----------------------------------------------------------------------------*)

let inst_of tm patt =
try(
   (let (_,tm_bind,ty_bind) = term_match [] patt tm
    in  let (insts,vars) = List.split tm_bind
    in  let f = (SPECL insts) o (GENL vars) o (INST_TYPE ty_bind)
    in  fun th -> apply_proof (f o hd) [patt] [th] 
   )) with Failure _ -> failwith "inst_of";;

(*----------------------------------------------------------------------------*)
(* Recursive datatype for a partial ordering of terms using the               *)
(* `is an instance of' relation.                                              *)let proof_print_thm thm =
   if !proof_printing
   then ( print_thm thm; print_newline (); print_newline());;

(*                                                                            *)
(* The leaf nodes of the tree are terms that have no instances. The other     *)
(* nodes have a list of instance trees and proofs of each instance from the   *)
(* term at that node.                                                         *)
(*                                                                            *)
(* Each term carries a number along with it. This is used to keep track of    *)
(* where the term came from in a list. The idea is to take the fringe of a    *)
(* clause tree, number the elements, then form partial orderings so that      *)
(* only the most general theorems have to be proved.                          *)
(*----------------------------------------------------------------------------*)

type inst_tree = No_insts of (term * int)
                  | Insts of (term * int * (inst_tree * (thm -> thm)) list);;

(*----------------------------------------------------------------------------*)
(* insert_into_inst_tree : (term # int) -> inst_tree -> inst_tree             *)
(* insert_into_inst_trees : (term # int # (thm -> thm)) ->                    *)
(*                          (inst_tree # (thm -> thm)) list ->                *)
(*                          (inst_tree # (thm -> thm)) list                   *)
(*                                                                            *)
(* Mutually recursive functions for constructing partial orderings, ordered   *)
(* by `is an instance of' relation. The algorithm is grossly inefficient.     *)
(* Structures are repeatedly destroyed and rebuilt. Reference variables       *)
(* should be used for efficiency.                                             *)
(*                                                                            *)
(* Inserting into a single tree:                                              *)
(*                                                                            *)
(* If tm' is an instance of tm, tm is put in the root node, with the old tree *)
(* as its single child. If tm is not an instance of tm', the function fails.  *)
(* Assume now that tm is an instance of tm'. If the tree is a leaf, it is     *)
(* made into a branch and tm is inserted as the one and only child. If the    *)
(* tree is a branch, an attempt is made to insert tm in the list of           *)
(* sub-trees. If this fails, tm is added as a leaf to the list of instances.  *)
(* Note that if tm is not an instance of tm', then it cannot be an instance   *)
(* of the instances of tm'.                                                   *)
(*                                                                            *)
(* Inserting into a list of trees:                                            *)
(*                                                                            *)
(* The list of trees carry proofs with them. The list is split into those     *)
(* whose root is an instance of tm, and those whose root is not. The proof    *)
(* associated with a tree that is an instance is replaced by a proof of the   *)
(* term from tm. If the list of trees that are instances is non-empty, they   *)
(* are made children of a node containing tm, and this new tree is added to   *)
(* the list of trees that are n't instances. If tm has instances in the list, *)
(* it cannot be the case that tm is an instance of one of the other trees in  *)
(* the list, for the trees in a list must be unrelated.                       *)
(*                                                                            *)
(* If there are no instances of tm in the list of trees, an attempt is made   *)
(* to insert tm into the list. If it is unrelated to all of the trees, this   *)
(* attempt fails, in which case tm is made into a leaf and added to the list. *)
(*----------------------------------------------------------------------------*)

let rec insert_into_inst_tree (tm,n) tree =
   match tree with
    | (No_insts (tm',n')) ->
         (try ( (let f = inst_of tm' tm
            in  Insts (tm,n,[No_insts (tm',n'),f]))
         ) with Failure _ -> try( let f = inst_of tm tm' 
            in  Insts (tm',n',[No_insts (tm,n),f])) with Failure _ -> failwith "insert_into_inst_tree"
         )
    | (Insts (tm',n',insts)) ->
         (try (let f = inst_of tm' tm
            in  Insts (tm,n,[Insts (tm',n',insts),f]))
         with Failure _ -> try(let f = inst_of tm tm'
            in  try( Insts (tm',n',insert_into_inst_trees (tm,n,f) insts))
                with Failure _ -> (Insts (tm',n',(No_insts (tm,n),f)::insts))
                )
            with Failure _ -> failwith "insert_into_inst_tree" )
and insert_into_inst_trees (tm,n,f) insts =
   let rec instances (tm,n) insts =
      if (insts = [])
      then ([],[])
      else let (not_instl,instl) = instances (tm,n) (tl insts)
           and (h,f) = hd insts
           in  let (tm',n') =
                  match h with
                          | (No_insts (tm',n')) -> (tm',n')
                          | (Insts (tm',n',_)) -> (tm',n')
               in  (try( (let f' = inst_of tm' tm
                      in  (not_instl,(h,f')::instl))
                   ) with Failure _ -> ((h,f)::not_instl,instl)
                   )
   and insert_into_inst_trees' (tm,n) trees =
      if (trees = [])
      then failwith "insert_into_inst_trees'"
      else (try( ((insert_into_inst_tree (tm,n) (hd trees))::(tl trees))
           ) with Failure _ -> ((hd trees)::(insert_into_inst_trees' (tm,n) (tl trees)))
           )
   in  let (not_instl,instl) = instances (tm,n) insts
   in  if (instl = [])
       then try( (lcombinep o (hashI (insert_into_inst_trees' (tm,n)))) (List.split insts)
            ) with Failure _ -> ((No_insts (tm,n),f)::insts)
       else (Insts (tm,n,instl),f)::not_instl;;

(*----------------------------------------------------------------------------*)
(* mk_inst_trees : (term # int) list -> inst_tree list                        *)
(*                                                                            *)
(* Constructs a partial ordering of terms under the `is an instance of'       *)
(* relation from a list of numbered terms.                                    *)
(*                                                                            *)
(* A dummy proof is passed to the call of insert_into_inst_trees. The result  *)
(* of the call has a proof associated with the root of each tree. These       *)
(* proofs are dummies and so are discarded before the final result is         *)
(* returned.                                                                  *)
(*----------------------------------------------------------------------------*)

let mk_inst_trees tmnl =
   let rec mk_inst_trees' insts tmnl =
      if (tmnl = [])
      then insts
      else let (tm,n) = hd tmnl
           in  mk_inst_trees'
                  (insert_into_inst_trees (tm,n,I) insts) (tl tmnl)
   in map fst (mk_inst_trees' [] tmnl);;

(*----------------------------------------------------------------------------*)
(* roots_of_inst_trees : inst_tree list -> term list                          *)
(*                                                                            *)
(* Computes the terms at the roots of a list of partial orderings.            *)
(*----------------------------------------------------------------------------*)

let rec roots_of_inst_trees trees =
   if (trees = [])
   then []
   else let tm =
           match (hd trees) with
            | (No_insts (tm,_)) -> tm
            | (Insts (tm,_,_)) -> tm
        in  tm::(roots_of_inst_trees (tl trees));;

(*----------------------------------------------------------------------------*)
(* prove_inst_tree : inst_tree -> thm -> (thm # int) list                     *)
(*                                                                            *)
(* Given a partial ordering of terms and a theorem for its root, returns a    *)
(* list of theorems for the terms in the tree.                                *)
(*----------------------------------------------------------------------------*)

let rec prove_inst_tree tree th =
   match tree with
    | (No_insts (tm,n)) ->
         (if (proves th tm) then [(th,n)] else failwith "prove_inst_tree")
    | (Insts (tm,n,insts)) ->
         (if (proves th tm)
          then (th,n)::(flat (map (fun (tr,f) -> prove_inst_tree tr (f th)) insts))
          else failwith "prove_inst_tree");;

(*----------------------------------------------------------------------------*)
(* prove_inst_trees : inst_tree list -> thm list -> thm list                  *)
(*                                                                            *)
(* Given a list of partial orderings of terms and a list of theorems for      *)
(* their roots, returns a sorted list of theorems for the terms in the trees. *)
(* The sorting is done based on the integer labels attached to each term in   *)
(* the trees.                                                                 *)
(*----------------------------------------------------------------------------*)

let prove_inst_trees trees ths =
   try ( map fst
    (sort_on_snd (flat (map (uncurry prove_inst_tree) (lcombinep (trees,ths)))))
   ) with Failure _ -> failwith "prove_inst_trees";;

(*----------------------------------------------------------------------------*)
(* prove_pool : conv -> term list -> thm list                                 *)
(*                                                                            *)
(* Attempts to prove the pool of clauses left over from the waterfall, by     *)
(* applying the conversion, conv, to the most general clauses.                *)
(*----------------------------------------------------------------------------*)

let prove_pool conv tml =
   let tmnl = number_list tml
   in  let trees = mk_inst_trees tmnl
   in  let most_gen_terms = roots_of_inst_trees trees
   in  let ths = map conv most_gen_terms
   in  prove_inst_trees trees ths;;

(*============================================================================*)
(* Boyer-Moore prover                                                         *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* WATERFALL : ((term # bool) -> ((term # bool) list # proof)) list ->        *)
(*             ((term # bool) -> ((term # bool) list # proof)) ->             *)
(*             (term # bool) ->                                               *)
(*             thm                                                            *)
(*                                                                            *)
(* Boyer-Moore style automatic proof procedure. Takes a list of heuristics,   *)
(* and a single heuristic that does induction, as arguments. The result is a  *)
(* function that, given a term and a Boolean, attempts to prove the term. The *)
(* Boolean is used to indicate whether the term is the step of an induction.  *)
(* It will normally be set to false for an external call.                     *)
(*----------------------------------------------------------------------------*)

let rec WATERFALL heuristics induction  (tm,(ind:bool)) =
   let conv tm =
      proof_print_string "Doing induction on:" () ;  bm_steps :=  hash ((+) 1) ((+) 1) !bm_steps ; 
      let void = proof_print_term tm ; proof_print_newline ()
      in let (tmil,proof) = induction (tm,false)
      in  dec_print_depth
             (proof
                 (map (WATERFALL heuristics induction) (inc_print_depth tmil))) 
   in  let void = proof_print_newline ()
   in  let tree = waterfall heuristics (tm,ind)
   in  let tmil = fringe_of_clause_tree tree
   in  let thl = prove_pool conv (map fst tmil)
   in  prove_clause_tree tree thl;;


let rec FILTERED_WATERFALL heuristics induction warehouse (tm,(ind:bool)) =
  let conv tm =
(*    let constr_check = ind && not((find_bm_terms (fun t -> count_constructors t > 5) tm) = []) in *)
    let constr_check = (max_var_depth tm > 12) in
    if (constr_check) then let void = (warn true "Reached maximum depth!") in failwith "cannot prove"
    else
      let heurn = try (assoc tm warehouse) with Failure _ -> 0 in
      let warehouse = (if (heurn > 0) then (List.remove_assoc tm warehouse) else (warehouse)) in
      if (heurn > length heuristics) then ( warn true "Induction loop detected."; failwith "cannot prove" )
      else
        proof_print_string "Doing induction on:" ();  bm_steps :=  hash ((+) 1) ((+) 1) !bm_steps ;
      let void = proof_print_term tm ; proof_print_newline () in
      let (tmil,proof) = induction (tm,false)
      in  dec_print_depth
        (proof
           (map (FILTERED_WATERFALL heuristics induction ((tm,(length heuristics) + 1)::warehouse)) (inc_print_depth tmil))) 
  in  let void = proof_print_newline ()
  in  let tree = filtered_waterfall heuristics [] (tm,ind)
(*   in  let void = proof_print_clausetree tree *)
  in  let tmil = fringe_of_clause_tree tree
  in  let thl = prove_pool conv (map fst tmil)
  in  prove_clause_tree tree thl;;

(*============================================================================*)
(* Some sample heuristics                                                     *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* conjuncts_heuristic : (term # bool) -> ((term # bool) list # proof)        *)
(*                                                                            *)
(* `Heuristic' for splitting a conjunction into a list of conjuncts.          *)
(* Right conjuncts are split recursively.                                     *)
(* Fails if the argument term is not a conjunction.                           *)
(*----------------------------------------------------------------------------*)

let conjuncts_heuristic (tm,(i:bool)) =
   let tms = conj_list tm
   in  if (length tms = 1)
       then failwith "conjuncts_heuristic"
       else (map (fun tm -> (tm,i)) tms,apply_proof LIST_CONJ tms);;

(*----------------------------------------------------------------------------*)
(* refl_heuristic : (term # bool) -> ((term # bool) list # proof)             *)
(*                                                                            *)
(* `Heuristic' for proving that terms of the form "x = x" are true. Fails if  *)
(* the argument term is not of this form. Otherwise it returns an empty list  *)
(* of new clauses, and a proof of the original term.                          *)
(*----------------------------------------------------------------------------*)

let refl_heuristic (tm,(i:bool)) =
   try(if (lhs tm = rhs tm)
    then (([]:(term * bool) list),apply_proof (fun ths -> REFL (lhs tm)) [])
    else failwith ""
   ) with Failure _ -> failwith "refl_heuristic";;

(*----------------------------------------------------------------------------*)
(* clausal_form_heuristic : (term # bool) -> ((term # bool) list # proof)     *)
(*                                                                            *)
(* `Heuristic' that tests a term to see if it is in clausal form, and if not  *)
(* converts it to clausal form and returns the resulting clauses as new       *)
(* `goals'. It is critical for efficiency that the normalization is only done *)
(* if the term is not in clausal form. Note that the functions `conjuncts'    *)
(* and `disjuncts' are not used for the testing because they split trees of   *)
(* conjuncts (disjuncts) rather than simply `linear' con(dis)junctions.       *)
(* If the term is in clausal form, but is not a single clause, it is split    *)
(* into single clauses. If the term is in clausal form but contains Boolean   *)
(* constants, the normalizer is applied to it. A single new goal will be      *)
(* produced in this case unless the result of the normalization was true.     *)
(*----------------------------------------------------------------------------*)

let clausal_form_heuristic (tm,(i:bool)) =
try (let is_atom tm =
     (not (has_boolean_args_and_result tm)) || (is_var tm) || (is_const tm)
  in  let is_literal tm =
         (is_atom tm) || ((is_neg tm) && (try (is_atom (rand tm)) with Failure _ -> false))
  in  let is_clause tm = forall is_literal (disj_list tm)
  in let result_string = fun tms -> let s = length tms 
    in let plural = if (s=1) then "" else "s" 
    in ("-> Clausal Form Heuristic (" ^ string_of_int(s) ^ " clause" ^ plural ^ ")")
  in  if (forall is_clause (conj_list tm)) &
         (not (free_in `T` tm)) && (not (free_in `F` tm))
      then if (is_conj tm)
           then let tms = conj_list tm
                in  (proof_print_string_l (result_string tms) () ;
                     (map (fun tm -> (tm,i)) tms,apply_proof LIST_CONJ tms))
          else failwith ""
      else let th = CLAUSAL_FORM_CONV tm
           in  let tm' = rhs (concl th)
           in  if (is_T tm')
               then  (proof_print_string_l "-> Clausal Form Heuristic" () ; ([],apply_proof (fun _ -> EQT_ELIM th) []))
               else let tms = conj_list tm'
                    in   (proof_print_string_l (result_string tms) () ; 
                          (map (fun tm -> (tm,i)) tms,
                         apply_proof ((EQ_MP (SYM th)) o LIST_CONJ) tms))
 ) with Failure _ -> failwith "clausal_form_heuristic";;

let meson_heuristic (tm,(i:bool)) =
   try( let meth = MESON (rewrite_rules()) tm in
    (([]:(term * bool) list),apply_proof (fun ths -> meth) [])
   ) with Failure _ -> failwith "meson_heuristic";;

let taut_heuristic (tm,(i:bool)) =
   try( let tautthm = TAUT tm in  (proof_print_string_l "-> Tautology Heuristic" () ;
    (([]:(term * bool) list),apply_proof (fun ths -> tautthm) []))
   ) with Failure _ -> failwith "taut_heuristic";;

let setify_heuristic (tm,(i:bool)) =
try (
  if (not (is_disj tm)) then failwith ""
  else
  let tms = disj_list tm
  in let tms' = setify tms
  in let tm' = list_mk_disj tms'
  in  if ((length tms) = (length tms')) then failwith ""
      else let th = TAUT (mk_imp (tm',tm))
      in (proof_print_string_l "-> Setify Heuristic" () ;
      ([tm',i],apply_proof ((MP th) o hd) [tm']))
 )
 with Failure _ -> failwith "setify_heuristic";;

