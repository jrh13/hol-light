(* ========================================================================= *)
(* Create search database from OCaml / modify search database dynamically.   *)
(*                                                                           *)
(* This file assigns to "theorems", which is a list of name-theorem pairs.   *)
(* The core system already has such a database set up. Use this file if you  *)
(* want to update the database beyond the core, so you can search it.        *)
(*                                                                           *)
(* The trickery to get at the OCaml environment is due to Roland Zumkeller   *)
(* and Michael Farber. It works by copying some internal data structures and *)
(* casting into the copy using Obj.magic.                                    *)
(* ========================================================================= *)

module Ocaml_typing = struct

type dummy

(* ------------------------------------------------------------------------- *)
(* Basic data structures copied from OCaml. May be version-dependent.        *)
(* ------------------------------------------------------------------------- *)

type label = int

(*** from typing/ident.ml: ***)

module Ident = struct

type t = { stamp: int; name: string; mutable flags: int }

type 'a tbl =
    Empty
  | Node of 'a tbl * 'a data * 'a tbl * int

and 'a data =
  { ident: t;
    data: 'a;
    previous: 'a data option }

end

(*** from typing/path.ml: ***)

module Path = struct

type t =
    Pident of Ident.t
  | Pdot of t * string * int
  | Papply of t * t

end

(*** from typing/types.ml: ***)

module Types = struct

open Asttypes

type type_expr =
  { mutable desc: type_desc;
    mutable level: dummy;
    mutable id: dummy }

and type_desc =
    Tvar of string option
  | Tarrow of label * type_expr * type_expr * commutable
  | Ttuple of type_expr list
  | Tconstr of Path.t * type_expr list * abbrev_memo ref
  | Tobject of type_expr * (Path.t * type_expr list) option ref
  | Tfield of string * field_kind * type_expr * type_expr
  | Tnil
  | Tlink of type_expr
  | Tsubst of type_expr         (* for copying *)
  | Tvariant of dummy
  | Tunivar of string option
  | Tpoly of type_expr * type_expr list
  | Tpackage of Path.t * dummy * type_expr list

and abbrev_memo =
    Mnil
  | Mcons of private_flag * Path.t * type_expr * type_expr * abbrev_memo
  | Mlink of abbrev_memo ref

and field_kind =
    Fvar of field_kind option ref
  | Fpresent
  | Fabsent

and commutable =
    Cok
  | Cunknown
  | Clink of commutable ref

type value_description =
  { val_type: type_expr;                (* Type of the value *)
    val_kind: dummy;
    val_loc: dummy;
    val_attributes: dummy
 }

type module_type =
    Tmty_ident of dummy
  | Tmty_signature of signature
  | Tmty_functor of dummy * dummy * dummy
  | Tmty_alias of dummy

and signature = signature_item list

and signature_item =
    Tsig_value of Ident.t * value_description
  | Tsig_type of dummy * dummy * dummy
  | Tsig_typext of dummy * dummy * dummy
  | Tsig_module of Ident.t * module_declaration * dummy
  | Tsig_modtype of dummy * dummy
  | Tsig_class of dummy * dummy * dummy
  | Tsig_class_type of dummy * dummy * dummy

and module_declaration =
  {
    md_type: module_type;
    md_attributes: dummy;
    md_loc: dummy;
  }

end


(*** from typing/env.ml: ***)

module Env = struct

open Types

module Envtbl =
  struct
    (* A table indexed by identifier, with an extra slot to record usage. *)
    type 'a t = ('a * bool ref) Ident.tbl
end;;

type env_t = {
  values: (dummy * value_description) Envtbl.t;
  constrs: dummy;
  labels: dummy;
  types: dummy;
  modules: (dummy * module_declaration) Envtbl.t;
  modtypes: dummy;
  components: dummy;
  classes: dummy;
  cltypes: dummy;
  functor_args: dummy;
  summary: dummy;
  local_constraints: dummy;
  gadt_instances: dummy;
  flags: dummy
}

end

(* ------------------------------------------------------------------------- *)
(* End of basic data structures copied from OCaml.                           *)
(* ------------------------------------------------------------------------- *)

open Ident
open Types
open Env
open Path

(* Iterate over the entries of a table. *)

let rec iter_tbl (f : Ident.t -> 'a -> unit) = function
  | Empty -> ()
  | Node (t1,d,t2,_) ->
      f d.ident d.data;
      iter_tbl f t1;
      iter_tbl f t2;;

(* If the given type is simple return its name, otherwise None. *)

let rec get_simple_type = function
  | Tlink { desc = Tconstr (Pident p,[],_) } -> Some p.name
  | Tlink { desc = d } -> get_simple_type d
  | _ -> None;;

let iter_values (p : Ident.t -> bool) (f : string -> string option -> unit) env =
  let rec iter_val pfx i vd =
    if p i then f (pfx ^ i.name) (get_simple_type vd.val_type.desc)
  and iter_mod pfx i md =
    if p i then match md.md_type with
        Tmty_signature sg ->
          let pfx' = pfx ^ i.name ^ "." in
          List.iter (function
            | Tsig_value  (i',vd)   -> iter_val pfx' i' vd
            | Tsig_module (i',md,_) -> iter_mod pfx' i' md
            | _ -> ()) sg
      | _ -> ()

  in
    iter_tbl (fun i ((_,vd),_) -> iter_val "" i vd) env.values;
    iter_tbl (fun i ((_,md),_) -> iter_mod "" i md) env.modules

end

(* Execute any OCaml expression given as a string. *)

let exec = ignore o Toploop.execute_phrase false Format.std_formatter
  o !Toploop.parse_toplevel_phrase o Lexing.from_string

(* Evaluate any OCaml expression given as a string. *)

let eval n =
  exec ("let buf__ = ( " ^ n ^ " );;");
  Obj.magic (Toploop.getvalue "buf__")

(* Register all theorems added since the last update. *)

let update_database =
  let lastStamp = ref 0
  and currentStamp = ref 0
  and thms = Hashtbl.create 5000 in

  let ident_new i =
    let s = i.Ocaml_typing.Ident.stamp in
    if s > !lastStamp then
      ((if s > !currentStamp then currentStamp := s); true)
    else false in

  let register_value name ty =
    if name <> "buf__" then
      (if ty = Some "thm"
       then Hashtbl.replace thms name (eval name)
       else Hashtbl.remove thms name) in

  fun () ->
    let env = Obj.magic !Toploop.toplevel_env in
    Ocaml_typing.iter_values ident_new register_value env;
    lastStamp := !currentStamp;
    theorems := Hashtbl.fold (fun s t l -> (s,t)::l) thms []

(* ------------------------------------------------------------------------- *)
(* Put an assignment of a theorem database in the named file.                *)
(* ------------------------------------------------------------------------- *)

let make_database_assignment filename =
  update_database();
  (let allnames = uniq(sort (<) (map fst (!theorems))) in
   let names = subtract allnames ["it"] in
   let entries = map (fun n -> "\""^n^"\","^n) names in
   let text = "needs \"help.ml\";;\n\n"^
              "theorems :=\n[\n"^
              end_itlist (fun a b -> a^";\n"^b) entries^"\n];;\n" in
   file_of_string filename text);;

(* ------------------------------------------------------------------------- *)
(* Search (automatically updates)                                            *)
(* ------------------------------------------------------------------------- *)

let search =
  let rec immediatesublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> h1 = h2 && immediatesublist t1 t2 in
  let rec sublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> immediatesublist l1 l2 || sublist l1 t2 in
  let exists_subterm_satisfying p (n,th) = can (find_term p) (concl th)
  and name_contains s (n,th) = sublist (explode s) (explode n) in
  let rec filterpred tm =
    match tm with
      Comb(Var("<omit this pattern>",_),t) -> not o filterpred t
    | Comb(Var("<match theorem name>",_),Var(pat,_)) -> name_contains pat
    | Comb(Var("<match aconv>",_),pat) -> exists_subterm_satisfying (aconv pat)
    | pat -> exists_subterm_satisfying (can (term_match [] pat)) in
  fun pats ->
    update_database();
    let triv,nontriv = partition is_var pats in
    (if triv <> [] then
      warn true
         ("Ignoring plain variables in search: "^
          end_itlist (fun s t -> s^", "^t) (map (fst o dest_var) triv))
     else ());
    (if nontriv = [] && triv <> [] then []
     else sort (increasing fst)
               (itlist (filter o filterpred) pats (!theorems)));;

(* ------------------------------------------------------------------------- *)
(* Update to bring things back to current state.                             *)
(* ------------------------------------------------------------------------- *)

update_database();;
