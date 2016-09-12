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

let dest_eq tm =
  match tm with
    Comb(Comb(Const("=",_),l),r) -> l,r
  | _ -> failwith "dest_eq";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)

  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2 as tp)::oenv -> if Pervasives.compare x1 t1 = 0
                             then if Pervasives.compare x2 t2 = 0
                                  then 0 else -1
                             else if Pervasives.compare x2 t2 = 0 then 1
                             else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && env = [] then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> Pervasives.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Pervasives.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l

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

  val equals_thm : thm -> thm -> bool
  val le_thm : thm -> thm -> bool
  val less_thm : thm -> thm -> bool

  val proof_of : thm -> proof
  val substitute_proof : thm -> proof -> thm
  val save_thm : string -> thm -> thm
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_thm_primitives = struct

  type thm = Sequent of (term list * term * proof)

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c,_)) = (asl,c)

  let hyp (Sequent(asl,c,_)) = asl

  let concl (Sequent(asl,c,_)) = c

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],mk_eq (tm, tm), proof_REFL tm)

  let TRANS (Sequent(asl1,c1,p1)) (Sequent(asl2,c2,p2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),l) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,mk_comb (eql, r),proof_TRANS (p1,p2))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

    let MK_COMB(Sequent(asl1,c1,p1),Sequent(asl2,c2,p2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of l1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of l2) = 0
             -> Sequent(term_union asl1 asl2,
                        mk_eq (mk_comb (l1, l2), mk_comb(r1, r2)),
                        proof_MK_COMB (p1,p2))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c,p)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,mk_eq (mk_abs (v, l), mk_abs (v, r)),proof_ABS v p)
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> Sequent([],mk_eq (tm, bod), proof_BETA tm)
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],tm, proof_ASSUME tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq,p1)) (Sequent(asl2,c,p2)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r, proof_EQ_MP p1 p2)
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1,p1)) (Sequent(asl2,c2,p2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',mk_eq (c1, c2),
            proof_DEDUCT_ANTISYM_RULE (p1,c1) (p2,c2))

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c,p)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c, proof_INST_TYPE theta p)

  let INST theta (Sequent(asl,c,p)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c, proof_INST theta p)

(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let axname = new_axiom_name "" in
      let p = proof_new_axiom (axname) tm in
      let th = Sequent([],tm,p) in
      (the_axioms := th::(!the_axioms);
       save_proof axname p (Some tm);
       th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)

  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),(Var(cname,ty) as l)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); mk_const (cname, []) in
        let p = proof_new_definition cname ty r in
        let concl = mk_eq (c, r) in
        save_proof ("DEF_"^cname) p (Some concl);
             let dth = Sequent([],concl,p) in
             the_definitions := dth::(!the_definitions); dth
    | _ -> failwith "new_basic_definition"

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

  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c,p)) =
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
    let absty = mk_type("fun",[rty;aty]) and repty = mk_type("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); mk_const(absname,[]))
    and rep = (new_constant(repname,repty); mk_const(repname,[])) in
    let a = mk_var("a",aty) and r = mk_var("r",rty) in
    let ax1 = mk_eq (mk_comb(abs,mk_comb(rep,a)), a) in
    let ax2 = mk_eq (mk_comb(P,r),
                          mk_eq (mk_comb(rep,mk_comb(abs,r)), r)) in
    let tp = proof_new_basic_type_definition tyname (absname, repname) (P,x) p in
    let tname = "TYDEF_"^tyname in
    save_proof tname tp None;
    Sequent([],ax1,proof_CONJUNCT1 tp),
    Sequent([],ax2,proof_CONJUNCT2 tp)

(* ------------------------------------------------------------------------- *)
(* Dealing with proof objects.                                               *)
(* ------------------------------------------------------------------------- *)

  let substitute_proof =
    if use_extended_proofobjects then
      fun (Sequent (asl, c, p)) pnew -> Sequent (asl, c, pnew)
    else
      fun th p -> th;;

  let equals_thm (Sequent (p1,c1,_)) (Sequent (p2,c2,_)) =
    (p1 = p2) && (c1 = c2)

  let le_thm (Sequent (p1,c1,_)) (Sequent (p2,c2,_)) = (p1, c1) <= (p2, c2)

  let less_thm (Sequent (p1, c1,_)) (Sequent (p2, c2,_)) = (p1, c1) < (p2, c2)

  let proof_of (Sequent(_,_,p)) = p

  let save_thm name th =
    (save_proof name (proof_of th) (Some (concl th)); th)

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;
