(* ========================================================================= *)
(* Abstract type of HOL name-carrying terms and manipulation functions.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

module type Hol_term_primitives =
  sig type term = private
    Var of string * hol_type
  | Const of string * hol_type
  | Comb of term * term
  | Abs of term * term
  val constants : unit -> (string * hol_type) list
  val get_const_type : string -> hol_type
  val new_constant : string * hol_type -> unit
  val type_of : term -> hol_type
  val aconv : term -> term -> bool
  val is_var : term -> bool
  val is_const : term -> bool
  val is_abs : term -> bool
  val is_comb : term -> bool
  val mk_var : string * hol_type -> term
  val mk_const : string * (hol_type * hol_type) list -> term
  val mk_abs : term * term -> term
  val mk_comb : term * term -> term
  val dest_var : term -> string * hol_type
  val dest_const : term -> string * hol_type
  val dest_comb : term -> term * term
  val dest_abs : term -> term * term
  val frees : term -> term list
  val freesl : term list -> term list
  val freesin : term list -> term -> bool
  val vfree_in : term -> term -> bool
  val type_vars_in_term : term -> hol_type list
  val variant : term list -> term -> term
  val vsubst : (term * term) list -> term -> term
  val inst : (hol_type * hol_type) list -> term -> term
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Term : Hol_term_primitives = struct

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)

  let the_term_constants =
     ref ["=",  mk_fun_ty aty (mk_fun_ty aty bool_ty)]

(* ------------------------------------------------------------------------- *)
(* Return all the defined constants with generic types.                      *)
(* ------------------------------------------------------------------------- *)

  let constants() = !the_term_constants

(* ------------------------------------------------------------------------- *)
(* Gets type of constant if it succeeds.                                     *)
(* ------------------------------------------------------------------------- *)

  let get_const_type s = assoc s (!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new constant.                                                   *)
(* ------------------------------------------------------------------------- *)

  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Finds the type of a term (assumes it is well-typed).                      *)
(* ------------------------------------------------------------------------- *)

  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> hd(tl(snd(dest_type(type_of s))))
    | Abs(Var(_,ty),t) -> mk_fun_ty ty (type_of t)

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

  let aconv =
    let rec alphavars env tm1 tm2 =
      match env with
        [] -> tm1 = tm2
      | (t1,t2)::oenv ->
            (t1 = tm1 & t2 = tm2) or
            (t1 <> tm1 & t2 <> tm2 & alphavars oenv tm1 tm2) in
    let rec raconv env tm1 tm2 =
      (tm1 == tm2 & env = []) or
      match (tm1,tm2) with
        Var(_,_),Var(_,_) -> alphavars env tm1 tm2
      | Const(_,_),Const(_,_) -> tm1 = tm2
      | Comb(s1,t1),Comb(s2,t2) -> raconv env s1 s2 & raconv env t1 t2
      | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
                ty1 = ty2 & raconv ((x1,x2)::env) t1 t2
      | _ -> false in
    fun tm1 tm2 -> raconv [] tm1 tm2

(* ------------------------------------------------------------------------- *)
(* Primitive discriminators.                                                 *)
(* ------------------------------------------------------------------------- *)

  let is_var = function (Var(_,_)) -> true | _ -> false

  let is_const = function (Const(_,_)) -> true | _ -> false

  let is_abs = function (Abs(_,_)) -> true | _ -> false

  let is_comb = function (Comb(_,_)) -> true | _ -> false

(* ------------------------------------------------------------------------- *)
(* Primitive constructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"

  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when ty = type_of a -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"

(* ------------------------------------------------------------------------- *)
(* Primitive destructors.                                                    *)
(* ------------------------------------------------------------------------- *)

  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"

(* ------------------------------------------------------------------------- *)
(* Finds the variables free in a term (list of terms).                       *)
(* ------------------------------------------------------------------------- *)

  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)

  let freesl tml = itlist (union o frees) tml []

(* ------------------------------------------------------------------------- *)
(* Whether all free variables in a term appear in a list.                    *)
(* ------------------------------------------------------------------------- *)

  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s & freesin acc t

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv & vfree_in v bod
    | Comb(s,t) -> vfree_in v s or vfree_in v t
    | _ -> tm = v

(* ------------------------------------------------------------------------- *)
(* Finds the type variables (free) in a term.                                *)
(* ------------------------------------------------------------------------- *)

  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)

(* ------------------------------------------------------------------------- *)
(* For name-carrying syntax, we need this early.                             *)
(* ------------------------------------------------------------------------- *)

  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

(* ------------------------------------------------------------------------- *)
(* Substitution primitive (substitution for variables only!)                 *)
(* ------------------------------------------------------------------------- *)

  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s & t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t & vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (fun (t,x) -> type_of t = snd(dest_var x)) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"

(* ------------------------------------------------------------------------- *)
(* Type instantiation primitive.                                             *)
(* ------------------------------------------------------------------------- *)

  exception Clash of term

  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if rev_assocd tm' env tm = tm then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f & x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y & t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin
end;;

include Term;;
