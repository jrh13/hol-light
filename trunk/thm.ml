(* ========================================================================= *)
(* Abstract type of theorems and primitive inference rules.                  *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

let rator tm =
  match tm with
    Comb(l,r) -> l
  | _ -> failwith "rator: Not a combination";;

let rand tm =
  match tm with
    Comb(l,r) -> r
  | _ -> failwith "rand: Not a combination";;

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

let dest_eq tm =
  match tm with
    Comb(Comb(Const("=",_),l),r) -> l,r
  | _ -> failwith "dest_eq";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)

let term_remove t l = filter (fun t' -> not(aconv t t')) l;;

let rec term_union l1 l2 =
  match l1 with
    [] -> l2
  | (h::t) -> let subun = term_union t l2 in
              if exists (aconv h) subun then subun else h::subun;;

(* ------------------------------------------------------------------------- *)
(* The abstract type of theorems.                                            *)
(* ------------------------------------------------------------------------- *)

module type Hol_thm_primitives =
  sig type thm
  val dest_thm : thm -> term list * term
  val hyp : thm -> term list
  val concl : thm -> term
  val REFL : term -> thm
  val TRANS : thm -> thm -> thm
  val MK_COMB : thm * thm -> thm
  val ABS : term -> thm -> thm
  val BETA : term -> thm
  val ASSUME : term -> thm
  val EQ_MP : thm -> thm -> thm
  val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
  val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
  val INST : (term * term) list -> thm -> thm
  val axioms : unit -> thm list
  val new_axiom : term -> thm
  val new_basic_definition : term -> thm
  val new_basic_type_definition : string -> string * string -> thm -> thm * thm
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_thm_primitives = struct

  type thm = Sequent of (term list * term)

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],mk_eq(tm,tm))

  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb(Comb(Const("=",_),l),m1),Comb(Comb(Const("=",_),m2),r)
        when aconv m1 m2 -> Sequent(term_union asl1 asl2,mk_eq(l,r))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2)
        -> Sequent(term_union asl1 asl2,mk_eq(mk_comb(l1,l2),mk_comb(r1,r2)))
     | _ -> failwith "MK_COMB"

  let ABS v (Sequent(asl,c)) =
    match c with
      Comb(Comb(Const("=",_),l),r) ->
        if exists (vfree_in v) asl
        then failwith "ABS: variable is free in assumptions"
        else Sequent(asl,mk_eq(mk_abs(v,l),mk_abs(v,r)))
    | _ -> failwith "ABS: not an equation"

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when arg = v -> Sequent([],mk_eq(tm,bod))
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if type_of tm = bool_ty then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when aconv l c
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',mk_eq(c1,c2))

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fn = inst theta in
    Sequent(map inst_fn asl,inst_fn c)

  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(map inst_fun asl,inst_fun c)

(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if fst(dest_type(type_of tm)) = "bool" then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)

  let new_basic_definition tm =
    let l,r = dest_eq tm in
    let cname,ty = dest_var l in
    if not(freesin [] r) then failwith "new_definition: term not closed" else
    if not (subset (type_vars_in_term r) (tyvars ty))
    then failwith "new_definition: Type variables not reflected in constant"
    else
      let c = new_constant(cname,ty); mk_const(cname,[]) in
      Sequent([],mk_eq(c,r))

(* ------------------------------------------------------------------------- *)
(* Handling of type definitions.                                             *)
(*                                                                           *)
(* This function now involves no logical constants beyond equality.          *)
(*                                                                           *)
(*             |- P t                                                        *)
(*    ---------------------------                                            *)
(*        |- abs(rep a) = a                                                  *)
(*     |- P r = (rep(abs r) = r)                                             *)
(*                                                                           *)
(* Where "abs" and "rep" are new constants with the nominated names.         *)
(* ------------------------------------------------------------------------- *)

  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = mk_type(tyname,tyvars)
    and rty = type_of x in
    let abs = new_constant(absname,mk_fun_ty rty aty); mk_const(absname,[])
    and rep = new_constant(repname,mk_fun_ty aty rty); mk_const(repname,[]) in
    let a = mk_var("a",aty) and r = mk_var("r",rty) in
    Sequent([],mk_eq(mk_comb(abs,mk_comb(rep,a)),a)),
    Sequent([],mk_eq(mk_comb(P,r),mk_eq(mk_comb(rep,mk_comb(abs,r)),r)))

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;
