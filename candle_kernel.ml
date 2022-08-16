(*
  In lieu of writing 'open Kernel;;'
*)

let aty = Kernel.mk_vartype "A";;
let bool_ty = Kernel.mk_type ("bool", []);;

let mk_vartype = Kernel.mk_vartype;;
let is_type = Kernel.is_type;;
let is_vartype = Kernel.is_vartype;;
let type_subst = Kernel.type_subst;;
let is_var = Kernel.is_var;;
let is_const = Kernel.is_const;;
let is_abs = Kernel.is_abs;;
let is_comb = Kernel.is_comb;;
let mk_var = Kernel.mk_var;;
let vfree_in = Kernel.call_vfree_in;;
let freesin = Kernel.call_freesin;;
let frees = Kernel.call_frees;;
let freesl = Kernel.freesl;;
let tyvars = Kernel.call_tyvars;;
let type_vars_in_term = Kernel.call_type_vars_in_term;;
let variant = Kernel.call_variant;;
let dest_thm = Kernel.dest_thm;;
let hyp = Kernel.hyp;;
let concl = Kernel.concl;;
let dest_type = Kernel.dest_type;;
let dest_vartype = Kernel.dest_vartype;;
let dest_var = Kernel.dest_var;;
let dest_const = Kernel.dest_const;;
let dest_comb = Kernel.dest_comb;;
let dest_abs = Kernel.dest_abs;;
let rator = Kernel.rator;;
let rand = Kernel.rand;;
let dest_eq = Kernel.dest_eq;;
let mk_abs = Kernel.mk_abs;;
let get_type_arity = Kernel.get_type_arity;;
let mk_type = Kernel.mk_type;;
let type_of = Kernel.call_type_of;;
let get_const_type = Kernel.get_const_type;;
let mk_comb = Kernel.mk_comb;;
let mk_const = Kernel.mk_const;;
let new_constant = Kernel.new_constant;;
let new_type = Kernel.new_type;;
let EQ_MP = Kernel.EQ_MP;;
let ASSUME = Kernel.ASSUME;;
let new_axiom = Kernel.new_axiom;;
let vsubst = Kernel.vsubst;;
let inst = Kernel.inst;;
let REFL = Kernel.REFL;;
let TRANS = Kernel.TRANS;;
let MK_COMB = Kernel.MK_COMB;;
let ABS = Kernel.ABS;;
let BETA = Kernel.BETA;;
let DEDUCT_ANTISYM_RULE = Kernel.DEDUCT_ANTISYM_RULE;;
let new_specification = Kernel.new_specification;;
let new_basic_definition = Kernel.new_basic_definition;;
let INST_TYPE = Kernel.INST_TYPE;;
let INST = Kernel.INST;;

let new_basic_type_definition tyname (absname,repname) th =
  Kernel.new_basic_type_definition (tyname, (absname, (repname, th)));;

let axioms = Kernel.axioms;;
let types = Kernel.types;;
let constants = Kernel.constants;;
let print_thm = Kernel.print_thm;;

let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

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

(* -------------------------------------------------------------------------
 * Term and type comparison
 * ------------------------------------------------------------------------- *)

module Type = struct
  let rec compare ty1 ty2 =
    match ty1, ty2 with
    | Tyvar x1, Tyvar x2 -> String.compare x1 x2
    | Tyvar _, Tyapp _ -> Less
    | Tyapp (x1,a1), Tyapp (x2,a2) ->
        Pair.compare String.compare (List.compare compare) (x1,a1) (x2,a2)
    | Tyapp _, Tyvar _ -> Greater
  ;;
  let (<) ty1 ty2 = compare ty1 ty2 = Less
  ;;
  let (<=) ty1 ty2 = compare ty1 ty2 <> Greater
  ;;
end;;

module Term = struct
  let rec compare t1 t2 =
    match t1, t2 with
    | Var (x1,ty1), Var (x2,ty2) ->
        Pair.compare String.compare Type.compare (x1,ty1) (x2,ty2)
    | Var _, _ -> Less
    | Const (x1,ty1), Const (x2,ty2) ->
        Pair.compare String.compare Type.compare (x1,ty1) (x2,ty2)
    | Const _, Var _ -> Greater
    | Const _, _ -> Less
    | Comb (s1,s2), Comb (t1,t2) ->
        Pair.compare compare compare (s1,s2) (t1,t2)
    | Comb _, Var _ -> Greater
    | Comb _, Const _ -> Greater
    | Comb _, Abs _ -> Less
    | Abs (s1,s2), Abs (t1,t2) ->
        Pair.compare compare compare (s1,s2) (t1,t2)
    | Abs _, _ -> Greater
  ;;
  let (<) t1 t2 = compare t1 t2 = Less
  ;;
  let (<=) t1 t2 = compare t1 t2 <> Greater
  ;;
end;;

module Thm = struct
  let compare th1 th2 =
    Pair.compare (List.compare Term.compare) Term.compare
                 (dest_thm th1)
                 (dest_thm th2)
  ;;
  let (<) th1 th2 = compare th1 th2 = Less
  ;;
  let (<=) th1 th2 = compare th1 th2 <> Greater
  ;;
end;;

let rec ordav env x1 x2 =
  match env with
  | [] -> Term.compare x1 x2
  | (t1,t2)::env ->
      if Term.compare x1 t1 = Equal then
        if Term.compare x2 t2 = Equal then
          Equal
        else
          Less
      else if Term.compare x2 t2 = Equal then
        Greater
      else
        ordav env x1 x2
;;

let rec orda env t1 t2 =
  if List.null env && t1 = t2 then Equal else
    match t1, t2 with
    | Var (_,_), Var (_,_) -> ordav env t1 t2
    | Const (_,_), Const (_,_) -> Term.compare t1 t2
    | Comb (s1, t1), Comb (s2, t2) ->
        let c = orda env s1 s2 in
        if c <> Equal then c else orda env t1 t2
    | Abs (s1, t1), Abs (s2, t2) ->
        let c = Type.compare (type_of s1) (type_of s2) in
        if c <> Equal then c else orda ((s1,s2)::env) t1 t2
    | Var (_,_), _ -> Less
    | _, Var (_,_) -> Greater
    | Const (_,_), _ -> Less
    | _, Const (_,_) -> Greater
    | Comb (_,_), _ -> Less
    | _, Comb (_,_) -> Greater
;;

let alphaorder = orda []
;;


(* -------------------------------------------------------------------------
 * Fixes to the Kernel interface
 * ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = Equal;;

let tyvars t = List.map mk_vartype (tyvars t);;
let type_vars_in_term t = List.map mk_vartype (type_vars_in_term t);;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;

