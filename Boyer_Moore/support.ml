(******************************************************************************)
(* FILE          : support.ml                                                 *)
(* DESCRIPTION   : Miscellaneous supporting definitions for Boyer-Moore       *)
(*                 style prover in HOL.                                       *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 6th June 1991                                              *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 21st June 1991                                             *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : 2008                                                       *)
(******************************************************************************)

let SUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar o type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq o concl) eqs) in
  let ths = map (ASSUME o mk_eq) (zip gvs rs) in
  let th1 = ASSUME gpat in
  let th2 = SUBS ths th1 in
  let th3 = itlist DISCH (map concl ths) (DISCH gpat th2) in
  let th4 = INST (zip ls gvs) th3 in
  MP (rev_itlist (C MP) eqs th4) th;;

let SUBST_CONV thvars template tm =
  let thms,vars = unzip thvars in
  let gvs = map (genvar o type_of) vars in
  let gtemplate = subst (zip gvs vars) template in
  SUBST (zip thms gvs) (mk_eq(template,gtemplate)) (REFL tm);;

let CONTRAPOS =
  let a = `a:bool` and b = `b:bool` in
  let pth = ITAUT `(a ==> b) ==> (~b ==> ~a)` in
  fun th ->
    try let P,Q = dest_imp(concl th) in
        MP (INST [P,a; Q,b] pth) th
    with Failure _ -> failwith "CONTRAPOS";;

let NOT_EQ_SYM =
  let pth = GENL [`a:A`; `b:A`]
    (CONTRAPOS(DISCH_ALL(SYM(ASSUME`a:A = b`))))
  and aty = `:A` in
  fun th -> try let l,r = dest_eq(dest_neg(concl th)) in
                MP (SPECL [r; l] (INST_TYPE [type_of l,aty] pth)) th
            with Failure _ -> failwith "NOT_EQ_SYM";;


let hash f g (x,y) = (f x,g y);;
let hashI f (x,y) = hash f I (x,y);;

let fst3 (x,_,_) = x;;
let snd3 (_,x,_) = x;;
let thd3 (_,_,x) = x;;

let lcombinep (x,y) = List.combine x y;;
let lcount x l = length ( filter ((=) x) l );;


let list_mk_imp (tms,tm) = 
     if (tms = []) then tm
     else try itlist (fun p q -> mk_imp (p,q)) tms tm with Failure _ -> failwith "list_mk_imp";;

let INDUCT_TAC_ thm = MATCH_MP_TAC thm THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC] ;;

(*--------------------------------------------------------------------------*)
(* distinct : ''a list -> bool                                              *)
(*                                                                          *)
(* Checks whether the elements of a list are all distinct.                  *)
(*--------------------------------------------------------------------------*)

let rec distinct x = 
     if (x = []) then true
     else not (mem (hd x) (tl x)) && distinct (tl x);;


(*----------------------------------------------------------------------------*)
(* Discriminator functions for T (true) and F (false)                         *)
(*----------------------------------------------------------------------------*)

let is_T = let T = `T` in fun tm -> tm = T
and is_F = let F = `F` in fun tm -> tm = F;;

(*--------------------------------------------------------------------------*)
(* conj_list : term -> term list                                            *)
(*                                                                          *)
(* Splits a conjunction into conjuncts. Only recursively splits the right   *)
(* conjunct.                                                                *)
(*--------------------------------------------------------------------------*)

let rec conj_list tm =
   try(
   let (tm1,tm2) = dest_conj tm
   in  tm1::(conj_list tm2)
   ) with Failure _ -> [tm];;

(*--------------------------------------------------------------------------*)
(* disj_list : term -> term list                                            *)
(*                                                                          *)
(* Splits a disjunction into disjuncts. Only recursively splits the right   *)
(* disjunct.                                                                *)
(*--------------------------------------------------------------------------*)

let rec disj_list tm =
   try(
   let (tm1,tm2) = dest_disj tm
   in  tm1::(disj_list tm2)
  ) with Failure _ -> [tm];;

(*----------------------------------------------------------------------------*)
(* number_list : * list -> ( * # int) list                                     *)
(*                                                                            *)
(* Numbers a list of elements,                                                *)
(* e.g. [`a`;`b`;`c`] ---> [(`a`,1);(`b`,2);(`c`,3)].                         *)
(*----------------------------------------------------------------------------*)

let number_list l =
   let rec number_list' n l =
      if ( l = [] ) then []
      else (hd l,n)::(number_list' (n + 1) (tl l))
   in number_list' 1 l;;

(*----------------------------------------------------------------------------*)
(* insert_on_snd : ( * # int) -> ( * # int) list -> ( * # int) list              *)
(*                                                                            *)
(* Insert a numbered element into an ordered list,                            *)
(* e.g. insert_on_snd (`c`,3) [(`a`,1);(`b`,2);(`d`,4)] --->                  *)
(*      [(`a`,1); (`b`,2); (`c`,3); (`d`,4)]                                  *)
(*----------------------------------------------------------------------------*)

let rec insert_on_snd (x,n) l =
   if (l = [])
   then [(x,n)]
   else let h = hd l
        in  if (n < snd h)
            then (x,n)::l
            else h::(insert_on_snd (x,n) (tl l));;

(*----------------------------------------------------------------------------*)
(* sort_on_snd : ( * # int) list -> ( * # int) list                             *)
(*                                                                            *)
(* Sort a list of pairs, of which the second component is an integer,         *)
(* e.g. sort_on_snd [(`c`,3);(`d`,4);(`a`,1);(`b`,2)] --->                    *)
(*      [(`a`,1); (`b`,2); (`c`,3); (`d`,4)]                                  *)
(*----------------------------------------------------------------------------*)

let rec sort_on_snd l =
   if (l = [])
   then []
   else (insert_on_snd (hd l) (sort_on_snd (tl l)));;

(*----------------------------------------------------------------------------*)
(* conj_list : term -> term list                                              *)
(*                                                                            *)
(* Splits a conjunction into conjuncts. Only recursively splits the right     *)
(* conjunct.                                                                  *)
(*----------------------------------------------------------------------------*)

let rec conj_list tm =
   try 
      (let (tm1,tm2) = dest_conj tm
       in  tm1::(conj_list tm2))
   with Failure _ -> [tm];;

(*----------------------------------------------------------------------------*)
(* disj_list : term -> term list                                              *)
(*                                                                            *)
(* Splits a disjunction into disjuncts. Only recursively splits the right     *)
(* disjunct.                                                                  *)
(*----------------------------------------------------------------------------*)

let rec disj_list tm =
   try
      (let (tm1,tm2) = dest_disj tm
       in  tm1::(disj_list tm2))
   with Failure _ -> [tm];;

(*----------------------------------------------------------------------------*)
(* find_bm_terms : (term -> bool) -> term -> term list                        *)
(*                                                                            *)
(* Function to find all subterms in a term that satisfy a given predicate p,  *)
(* breaking down terms as if they were Boyer-Moore logic expressions.         *)
(* In particular, the operator of a function application is only processed if *)
(* it is of zero arity, i.e. there are no arguments.                          *)
(*----------------------------------------------------------------------------*)

let find_bm_terms p tm =
 try 
   (let rec accum tml p tm =
     let tml' = if (p tm) then (tm::tml) else tml
     in ( let args = snd (strip_comb tm)
            in ( try ( rev_itlist (fun tm tml -> accum tml p tm) args tml' ) with Failure _ -> tml' ) )
      in accum [] p tm
 ) with Failure _ -> failwith "find_bm_terms";;

(*----------------------------------------------------------------------------*)
(* remove_el : int -> * list -> ( * # * list)                                 *)
(*                                                                            *)
(* Removes a specified (by numerical position) element from a list.           *)
(*----------------------------------------------------------------------------*)

let rec remove_el n l =
   if ((l = []) || (n < 1))
   then failwith "remove_el"
   else if (n = 1)
        then (hd l,tl l)
        else let (x,l') = remove_el (n - 1) (tl l)
             in  (x,(hd l)::l');;

