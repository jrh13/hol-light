(******************************************************************************)
(* FILE          : irrelevance.ml                                             *)
(* DESCRIPTION   : Eliminating irrelevance.                                   *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 25th June 1991                                             *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 12th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : 2008                                                       *)
(******************************************************************************)

let DISJ_IMP =
  let pth = TAUT`!t1 t2. t1 \/ t2 ==> ~t1 ==> t2` in
  fun th ->
    try let a,b = dest_disj(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "DISJ_IMP";;

let IMP_ELIM =
  let pth = TAUT`!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2` in
  fun th ->
    try let a,b = dest_imp(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "IMP_ELIM";;

(*----------------------------------------------------------------------------*)
(* partition_literals : (term # int) list -> (term # int) list list           *)
(*                                                                            *)
(* Function to partition a list of numbered terms into lists that share       *)
(* variables. A term in one partition has no variables in common with any     *)
(* term in one of the other partitions. Within a partition the terms are      *)
(* ordered as they were in the input list.                                    *)
(*                                                                            *)
(* The function begins by putting every term in a separate partition. It then *)
(* tries to merge the first partition with one of the others. Two partitions  *)
(* can be merged if they have at least one variable in common. If a merge can *)
(* be done, the process is repeated for the new head of the partition list.   *)
(* This continues until a merge cannot take place (this causes a failure in   *)
(* `merge_partitions' due to an attempt to split an empty list into a head    *)
(* and a tail). When this happens, the head partition is separated from the   *)
(* others because it cannot have any variables in common with the others. The *)
(* entire process is repeated for the remaining partitions. This goes on      *)
(* until the list is exhausted.                                               *)
(*                                                                            *)
(* When as much merging as possible has been done, the terms within each      *)
(* partition are sorted based on the number they are paired with.             *)
(*----------------------------------------------------------------------------*)

let partition_literals tmnl =
   let rec merge_partitions partition partitions =
      if (partitions = []) then failwith "merge_partitions"
      else let h::t = partitions
      in  if ((intersect ((freesl o map fst) partition)
                              ((freesl o map fst) h)) = [])
          then h::(merge_partitions partition t)
          else (partition @ h)::t
   and repeated_merge partitions =
      if (partitions = [])
      then []
      else let h::t = partitions
           in try repeated_merge (merge_partitions h t)
            with Failure _ ->  h::(repeated_merge t)
   in map sort_on_snd (repeated_merge (map (fun tmn -> [tmn]) tmnl));;

(*----------------------------------------------------------------------------*)
(* contains_recursive_fun : term list -> bool                                 *)
(*                                                                            *)
(* Determines whether a list of terms (a partition) mentions a recursive      *)
(* function. A constant that does not have a definition in the environment is *)
(* taken to be non-recursive.                                                 *)
(*----------------------------------------------------------------------------*)

let contains_recursive_fun tml =
   let consts = flat (mapfilter (find_terms is_const) tml)
   in  let names = setify (map (fst o dest_const) consts)
   in  exists (fun name -> not (try ((fst o get_def) name = 0) with Failure _ -> true)) names;;

(*----------------------------------------------------------------------------*)
(* is_singleton_rec_app : term list -> bool                                   *)
(*                                                                            *)
(* Returns true if the list of terms (a partition) given as argument is a     *)
(* single literal whose atom is of the form (f v1 ... vn) where f is a        *)
(* recursive function and the vi are distinct variables.                      *)
(*----------------------------------------------------------------------------*)

let is_singleton_rec_app tml =
try  (
  match (tml) with
  | [tm] ->
      let tm' = if (is_neg tm) then (rand tm) else tm
  in  let (f,args) = strip_comb tm'
  in  let name = fst (dest_const f)
  in  (not ((fst o get_def) name = 0)) &&
      (forall is_var args) &&
      (distinct args)
  | _ -> false
 ) with Failure _ -> false;;

(*----------------------------------------------------------------------------*)
(* merge_numbered_lists : ( # int) list -> ( # int) list -> ( # int) list  *)
(*                                                                            *)
(* Merges two numbered lists. The lists must be in increasing order by the    *)
(* number, and no number may appear more than once in a list or appear in     *)
(* both lists. The result will then be ordered by the numbers.                *)
(*----------------------------------------------------------------------------*)

let rec merge_numbered_lists xnl1 xnl2 =
   if (xnl1 = []) then xnl2
   else if (xnl2 = []) then xnl1
   else let ((x1,n1)::t1) = xnl1
        and ((x2,n2)::t2) = xnl2
        in  if (n1 < n2)
            then (x1,n1)::(merge_numbered_lists t1 xnl2)
            else (x2,n2)::(merge_numbered_lists xnl1 t2);;

(*----------------------------------------------------------------------------*)
(* find_irrelevant_literals : term -> ((term # int) list # (term # int) list) *)
(*                                                                            *)
(* Given a clause, this function produces two lists of term/integer pairs.    *)
(* The first list is of literals deemed to be irrelevant. The second list is  *)
(* the remaining literals. The number with each literal is its position in    *)
(* the original clause.                                                       *)
(*----------------------------------------------------------------------------*)

let find_irrelevant_literals tm =
   let can_be_falsified tmnl =
      let tml = map fst tmnl
      in  (not (contains_recursive_fun tml)) || (is_singleton_rec_app tml)
   and tmnll = partition_literals (number_list (disj_list tm))
   in  let (irrels,rels) = partition can_be_falsified tmnll
   in  (itlist merge_numbered_lists irrels [],
        itlist merge_numbered_lists rels []);;

(*----------------------------------------------------------------------------*)
(* DISJ_UNDISCH : thm -> thm                                                  *)
(*                                                                            *)
(*     A |- x \/ y                                                            *)
(*    -------------  DISJ_UNDISCH                                             *)
(*     A, ~x |- y                                                             *)
(*----------------------------------------------------------------------------*)

let DISJ_UNDISCH th = try UNDISCH (DISJ_IMP th) with Failure _ -> failwith "DISJ_UNDISCH";;

(*----------------------------------------------------------------------------*)
(* DISJ_DISCH : term -> thm -> thm                                            *)
(*                                                                            *)
(*     A, ~x |- y                                                             *)
(*    -------------  DISJ_DISCH "x:bool"                                      *)
(*     A |- x \/ y                                                            *)
(*----------------------------------------------------------------------------*)

let DISJ_DISCH tm th =
try
 (CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV NOT_NOT_NORM)))
     (IMP_ELIM (DISCH (mk_neg tm) th))
 ) with Failure _ -> failwith "DISJ_DISCH";;

(*----------------------------------------------------------------------------*)
(* BUILD_DISJ : ((term # int) list # (term # int) list) -> thm -> thm         *)
(*                                                                            *)
(* Function to build a disjunctive theorem from another theorem that has as   *)
(* its conclusion a subset of the disjuncts. The first argument is a pair of  *)
(* term/integer lists. Each list contains literals (disjuncts) and their      *)
(* position within the required result. The first list is of those disjuncts  *)
(* not in the theorem. The second list is of disjuncts in the theorem. Both   *)
(* lists are assumed to be ordered by their numbers (increasing order).       *)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*    BUILD_DISJ ([("x2",2);("x5",5);("x6",6)],[("x1",1);("x3",3);("x4",4)])  *)
(*               |- x1 \/ x3 \/ x4                                            *)
(*                                                                            *)
(* The required result is:                                                    *)
(*                                                                            *)
(*    |- x1 \/ x2 \/ x3 \/ x4 \/ x5 \/ x6                                     *)
(*                                                                            *)
(* The first step is to undischarge all the disjuncts except for the last:    *)
(*                                                                            *)
(*    ~x1, ~x3 |- x4                                                          *)
(*                                                                            *)
(* The disjuncts not in the theorem, and which are to come after x4, are now  *)
(* `added' to the theorem. (Note that we have to undischarge all but the last *)
(* disjunct in order to get the correct associativity of OR (\/) at this      *)
(* stage):                                                                    *)
(*                                                                            *)
(*    ~x1, ~x3 |- x4 \/ x5 \/ x6                                              *)
(*                                                                            *)
(* We now repeatedly either discharge one of the assumptions, or add a        *)
(* disjunct from the `outs' list, according to the values of the numbers      *)
(* associated with the terms:                                                 *)
(*                                                                            *)
(*    ~x1 |- x3 \/ x4 \/ x5 \/ x6                                             *)
(*                                                                            *)
(*    ~x1 |- x2 \/ x3 \/ x4 \/ x5 \/ x6                                       *)
(*                                                                            *)
(*    |- x1 \/ x2 \/ x3 \/ x4 \/ x5 \/ x6                                     *)
(*----------------------------------------------------------------------------*)

let BUILD_DISJ (outs,ins) inth =
try (let rec rebuild rev_outs rev_ins th =
     if (rev_ins = [])
     then if (rev_outs = [])
          then th
          else rebuild (tl rev_outs) rev_ins (DISJ2 (fst (hd rev_outs)) th)
     else if (rev_outs = [])
          then rebuild rev_outs (tl rev_ins) (DISJ_DISCH (fst (hd rev_ins)) th)
          else let (inh::int) = rev_ins
               and (outh::outt) = rev_outs
               in  if (snd inh > snd outh)
                   then rebuild rev_outs int (DISJ_DISCH (fst inh) th)
                   else rebuild outt rev_ins (DISJ2 (fst outh) th)
  in  let last_in = snd (last ins)
  in  let (under_outs,over_outs) = partition (fun (_,n) -> n > last_in) outs
  in  let over_ins = butlast ins
  in  let th1 = funpow (length over_ins) DISJ_UNDISCH inth
  in  let th2 = try (DISJ1 th1 (list_mk_disj (map fst under_outs))) with Failure _ -> th1
  in  rebuild (rev over_outs) (rev over_ins) th2
 ) with Failure _ -> failwith "BUILD_DISJ";;

(*----------------------------------------------------------------------------*)
(* irrelevance_heuristic : (term # bool) -> ((term # bool) list # proof)      *)
(*                                                                            *)
(* Heuristic for eliminating irrelevant literals. The function splits the     *)
(* literals into two sets: those that are irrelevant and those that are not.  *)
(* If there are no relevant terms left, the heuristic fails in a way that     *)
(* indicates the conjecture cannot be proved. If there are no irrelevant      *)
(* literals, the function fails indicating that it cannot do anything with    *)
(* the clause. In all other circumstances the function returns a new clause   *)
(* consisting of only the relevant literals, together with a proof of the     *)
(* original clause from this new clause.                                      *)
(*----------------------------------------------------------------------------*)

let irrelevance_heuristic (tm,(ind:bool)) =
   let (outs,ins) = find_irrelevant_literals tm
   in  if (ins = []) then failwith "cannot prove"
       else if (outs = []) then failwith "irrelevance_heuristic"
       else let tm' = list_mk_disj (map fst ins)
            and proof = BUILD_DISJ (outs,ins)
            in  (proof_print_string_l "-> Irrelevance Heuristic" () ;  ([(tm',ind)],apply_proof (proof o hd) [tm']));;
