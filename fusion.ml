(* ========================================================================= *)
(* Complete HOL kernel of types, terms and theorems.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "lib.ml";;

(* Environment dependencies *)

let getenv_default var default =
  try
    Sys.getenv var
  with Not_found ->
    (print_endline ("Environment variable " ^ var ^ " not set. Using default value: " ^ default);
    default);;

let MAXTMS = getenv_default "MAXTMS" "1000000000";;
let MAXPS = getenv_default "MAXPS" "1000000000";;
let clean_ts_at_saved = false;;
let clean_ths_at_saved = true;;


#load "unix.cma";;
let poutc = open_out "proofs";;
let foutc = open_out "facts.lst";;
let stop_recording () = close_out poutc; close_out foutc;;

let rec outl = function
  [] -> ()
| (h :: t) -> try
    output_string poutc h; List.fold_left
      (fun () e -> output_char poutc ' '; output_string poutc e) () t
    with Sys_error _ -> ();;

module type Hol_kernel =
  sig
      type hol_type = private
        Tyvar of string
      | Tyapp of string *  hol_type list

      type term = private
        Var of string * hol_type
      | Const of string * hol_type
      | Comb of term * term
      | Abs of term * term

      type thm

      val types: unit -> (string * int)list
      val get_type_arity : string -> int
      val new_type : (string * int) -> unit
      val mk_type: (string * hol_type list) -> hol_type
      val mk_vartype : string -> hol_type
      val dest_type : hol_type -> (string * hol_type list)
      val dest_vartype : hol_type -> string
      val is_type : hol_type -> bool
      val is_vartype : hol_type -> bool
      val tyvars : hol_type -> hol_type list
      val type_subst : (hol_type * hol_type)list -> hol_type -> hol_type
      val bool_ty : hol_type
      val aty : hol_type

      val constants : unit -> (string * hol_type) list
      val get_const_type : string -> hol_type
      val new_constant : string * hol_type -> unit
      val type_of : term -> hol_type
      val alphaorder : term -> term -> int
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
      val rand: term -> term
      val rator: term -> term
      val dest_eq: term -> term * term

      val dest_thm : thm -> term list * term
      val hyp : thm -> term list
      val concl : thm -> term
      val pr : thm -> int
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
      val definitions : unit -> thm list
      val new_basic_definition : term -> thm
      val new_basic_type_definition :
              string -> string * string -> thm -> thm * thm
      val tag_intermediate_step : string -> thm -> unit
      val empty_cache : unit -> unit
      (* val dump_theorems: unit -> unit *)
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_kernel = struct

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term

  type thm = Sequent of (term list * term * int)


  (* PROOFRECORDING BEGIN *)

  let thms = Hashtbl.create 20000;;

(*
  let dump_theorems() =
    Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) thms;;
    let ts2 = List.filter (fun (s,_) -> not (Hashtbl.mem store s)) !thms in
    let ts3 = List.filter (fun (s,_) -> s <> "ARITH") ts2 in
    let oc = open_out "theorems" in
    output_value oc (List.map (fun a, b -> a, dest_thm b) ts3); close_out oc;;
*)

(*
  let inc = open_in "theorems";;
  let l = ((input_value inc) : ((string * (term list * term)) list));;
  close_in inc;;
  List.iter (fun (n,t) -> Hashtbl.replace thms t (n, 0)) l;;
  print_endline ("Read in: " ^ string_of_int (Hashtbl.length thms));;
*)

  module Fm = Map.Make(struct type t = float let compare = compare end);;
  module Tys = Map.Make(struct type t = hol_type let compare = compare end);;
  module Tms = Map.Make(struct type t = term let compare = compare end);;
  module Ps = Map.Make(struct type t = (term list * term) let compare = compare end);;

  let ty_no = ref 0;;
  let tys = ref Tys.empty;;

  let rec out_type ty =
    try
      Tys.find ty !tys
    with Not_found ->
      match ty with
        Tyvar t ->
          incr ty_no; tys := Tys.add ty !ty_no !tys;
          output_char poutc 't'; output_string poutc t; output_char poutc '\n';
          !ty_no
      | Tyapp (id, tl) ->
          let tln = map out_type tl in
          incr ty_no; tys := Tys.add ty !ty_no !tys;
          output_char poutc 'a'; output_string poutc id; output_char poutc ' ';
            outl (map string_of_int tln); output_char poutc '\n';
          !ty_no;;

  let tm_no = ref 0;;
  let tms = ref Tms.empty;;
  let tms_prio = ref Fm.empty;;
  let tms_size = ref 0;;
  let tms_maxsize = ref (int_of_string MAXTMS);;
  let tm_lookup tm =
    let (ret, oldtime) = Tms.find tm !tms in
    let newtime = Unix.gettimeofday () in
    tms := Tms.add tm (ret, newtime) !tms;
    tms_prio := Fm.add newtime tm (Fm.remove oldtime !tms_prio);
    ret;;

  let tm_delete () =
    let (time, tm) = Fm.min_binding !tms_prio in
    tms := Tms.remove tm !tms;
    tms_prio := Fm.remove time !tms_prio;
    decr tms_size; ();;

  let tm_add tm no =
    while (!tms_size > !tms_maxsize) do tm_delete (); done;
    let newtime = Unix.gettimeofday () in
    tms := Tms.add tm (no, newtime) (!tms);
    tms_prio := Fm.add newtime tm (!tms_prio);
    incr tms_size; ();;

  (*
  let inst_const (n, ty) =
    let gty = get_const_type n in
    let inst = type_match gty ty [] in
    let rinst = map (fun (a, b) -> (b, a)) inst in
    let tvs = tyvars gty in
    map (fun x -> assoc x rinst) tvs
    ;;*)

  let rec out_term tm =
    try
      tm_lookup tm
    with Not_found ->
      let outc = output_char poutc and out = output_string poutc in
      match tm with
        Var (name, ty) ->
          let ty = out_type ty in
          incr tm_no; tm_add tm !tm_no;
          outc 'v'; out name; outc ' '; out (string_of_int ty); outc '\n';
          !tm_no
      | Const (name, ty) ->
          let ty = out_type ty in
          incr tm_no; tm_add tm !tm_no;
          outc 'c'; out name; outc ' '; out (string_of_int ty); outc '\n';
          !tm_no
      | Comb (f, a) ->
          let f = out_term f and a = out_term a in
          incr tm_no; tm_add tm !tm_no;
          outc 'f'; out (string_of_int f); outc ' '; out (string_of_int a); outc '\n';
          !tm_no
      | Abs (x, a) ->
          let x = out_term x and a = out_term a in
          incr tm_no; tm_add tm !tm_no;
          outc 'l'; out (string_of_int x); outc ' '; out (string_of_int a); outc '\n';
          !tm_no
  ;;

  let prf_no = ref 0;;
  let outt tag ss tys tms pfs =
    let tys = map out_type tys and
        tms = map out_term tms in
    try
      output_char poutc tag;
      outl (ss @ (map string_of_int tys)
             @ (map string_of_int tms)
             @ (map string_of_int pfs));
      output_char poutc '\n'
    with Sys_error _ -> ()
  ;;

  let ps = ref Ps.empty;;
  let ps_prio = ref Fm.empty;;
  let ps_size = ref 0;;
  let ps_maxsize = ref (int_of_string MAXPS);;

  let p_lookup p =
    let (ret, oldtime) = Ps.find p !ps in
    let newtime = Unix.gettimeofday () in
    ps := Ps.add p (ret, newtime) !ps;
    ps_prio := Fm.add newtime p (Fm.remove oldtime !ps_prio);
    ret;;

  let p_delete () =
    let (time, p) = Fm.min_binding !ps_prio in
    ps := Ps.remove p !ps;
    ps_prio := Fm.remove time !ps_prio;
    decr ps_size; ();;

  let p_add p no =
    while (!ps_size > !ps_maxsize) do p_delete (); done;
    let newtime = Unix.gettimeofday () in
    ps := Ps.add p (no, newtime) (!ps);
    ps_prio := Fm.add newtime p (!ps_prio);
    incr ps_size; ();;

  let mk_prff f = incr prf_no; f (); !prf_no;;

  let chk_mk_prff f th =
    try p_lookup th
    with Not_found ->
    try
      let (name, i) = Hashtbl.find thms th in
      if i > 0 then i else
      let i = mk_prff f in
      (ps := Ps.empty; ps_prio := Fm.empty; ps_size := 0;
       (*    Hashtbl.replace thms th (name, i);*)
       Hashtbl.remove thms th;
      (try output_string foutc (name ^ " " ^ string_of_int i ^ "\n"); flush foutc with Sys_error _ -> ());
      i)
    with Not_found ->
      mk_prff (fun () -> f (); p_add th !prf_no);;

  let mk_prf t l1 l2 l3 l4 _ = mk_prff (fun () -> outt t l1 l2 l3 l4);;
  let chk_mk_prf t l1 l2 l3 l4 th = chk_mk_prff (fun () -> outt t l1 l2 l3 l4) th;;
  let proof_REFL t th = chk_mk_prf 'R' [] [] [t] [] th;;
  let proof_TRANS (p, q) th = chk_mk_prf 'T' [] [] [] [p; q] th;;
  let proof_MK_COMB (p, q) th = chk_mk_prf 'C' [] [] [] [p; q] th;;
  let proof_ABS x p th = chk_mk_prf 'L' [] [] [x] [p] th;;
  let proof_BETA t th = chk_mk_prf 'B' [] [] [t] [] th;;
  let proof_ASSUME t th = chk_mk_prf 'H' [] [] [t] [] th;;
  let proof_EQ_MP p q th = chk_mk_prf 'E' [] [] [] [p; q] th;;
  let proof_DEDUCT_ANTISYM_RULE (p1,t1) (p2,t2) th =
    chk_mk_prf 'D' [] [] [] [p1; p2] th;;
  let rec explode_subst = function
    [] -> []
  | ((y,x)::rest) -> x::y::(explode_subst rest);;
  let proof_INST_TYPE s p th = chk_mk_prf 'Q' [] (explode_subst s) [] [p] th;;
  let proof_INST s p th = chk_mk_prf 'S' [] [] (explode_subst s) [p] th;;

  let global_ax_counter = ref 0;;
  let new_axiom_name n = incr global_ax_counter; ("hidden_AXIOM_" ^ n ^ "_" ^ string_of_int(!global_ax_counter));;
  let proof_new_axiom axname t th = chk_mk_prf 'A' [axname] [] [t] [] th;;
  let proof_new_definition cname ty t th =
    chk_mk_prf 'F' [cname] [] [t] [] th;;
  let proof_new_basic_type_definition tyname (absname, repname) (pt,tt) p th =
    chk_mk_prf 'Y' [tyname; absname; repname] [] [pt; tt] [p] th;;
  let proof_CONJUNCT1 p th = chk_mk_prf '1' [] [] [] [p] th;;
  let proof_CONJUNCT2 p th = chk_mk_prf '2' [] [] [] [p] th;;

  (* Possibly includes existing thm steps *)
  let intermediate_tags = Hashtbl.create 1000000;;

  let empty_cache () = ps := Ps.empty; ps_prio := Fm.empty; ps_size := 0;;

  let save_proof name p th =
    Hashtbl.replace thms th (name, p);
    if clean_ths_at_saved then empty_cache ();
    if clean_ts_at_saved then (
      tms := Tms.empty; tms_prio := Fm.empty; tms_size := 0;
    );
    (try output_string foutc (name ^ " " ^ string_of_int p ^ "\n"); flush foutc with Sys_error _ -> ());;

  let tag_intermediate_step note (Sequent (_, _, p)) =
    if List.mem note (Hashtbl.find_all intermediate_tags p) then () else begin
      Hashtbl.add intermediate_tags p note;
      if note <> "!" then empty_cache ();
      try output_string foutc (">>> " ^ note ^ " " ^ string_of_int p ^ "\n"); flush foutc with Sys_error _ -> ()
    end;;

(* PROOFRECORDING END *)

(* ------------------------------------------------------------------------- *)
(* List of current type constants with their arities.                        *)
(*                                                                           *)
(* Initially we just have the boolean type and the function space            *)
(* constructor. Later on we add as primitive the type of individuals.        *)
(* All other new types result from definitional extension.                   *)
(* ------------------------------------------------------------------------- *)

  let the_type_constants = ref ["bool",0; "fun",2]

(* ------------------------------------------------------------------------- *)
(* Return all the defined types.                                             *)
(* ------------------------------------------------------------------------- *)

  let types() = !the_type_constants

(* ------------------------------------------------------------------------- *)
(* Lookup function for type constants. Returns arity if it succeeds.         *)
(* ------------------------------------------------------------------------- *)

  let get_type_arity s = assoc s (!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new type.                                                       *)
(* ------------------------------------------------------------------------- *)

  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Basic type constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)

(* ------------------------------------------------------------------------- *)
(* Basic type destructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s

(* ------------------------------------------------------------------------- *)
(* Basic type discriminators.                                                *)
(* ------------------------------------------------------------------------- *)

  let is_type = can dest_type

  let is_vartype = can dest_vartype

(* ------------------------------------------------------------------------- *)
(* Return the type variables in a type and in a list of types.               *)
(* ------------------------------------------------------------------------- *)

  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]

(* ------------------------------------------------------------------------- *)
(* Substitute types for type variables.                                      *)
(*                                                                           *)
(* NB: non-variables in subst list are just ignored (a check would be        *)
(* repeated many times), as are repetitions (first possibility is taken).    *)
(* ------------------------------------------------------------------------- *)

  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty

  let bool_ty = Tyapp("bool",[])

  let aty = Tyvar "A"

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)

  let the_term_constants =
     ref ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])])]

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
    | Comb(s,_) -> (match type_of s with Tyapp("fun",[dty;rty]) -> rty)
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])

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
      Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of a) = 0
        -> Comb(f,a)
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
    | Comb(s,t) -> freesin acc s && freesin acc t

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | _ -> Pervasives.compare tm v = 0

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
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t && vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (function (t,Var(_,y)) -> Pervasives.compare (type_of t) y = 0
                        | _ -> false) theta
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
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq"

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)

  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2)::oenv -> if Pervasives.compare x1 t1 = 0
                       then if Pervasives.compare x2 t2 = 0
                            then 0 else -1
                       else if Pervasives.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
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
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c,_)) = (asl,c)

  let hyp (Sequent(asl,c,_)) = asl

  let concl (Sequent(asl,c,_)) = c

  let pr (Sequent(asl,c,p)) = p

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    let eq = safe_mk_eq tm tm in
    Sequent([],eq,proof_REFL tm ([], eq))

  let TRANS (Sequent(asl1,c1,p1)) (Sequent(asl2,c2,p2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 ->
          let (a, g) = (term_union asl1 asl2,Comb(eql,r)) in
          Sequent (a, g, proof_TRANS (p1, p2) (a, g))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1,p1),Sequent(asl2,c2,p2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of r2) = 0
             -> let (a, g) = (term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2))) in
                Sequent (a, g, proof_MK_COMB (p1, p2) (a,g))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c,p)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> let eq = safe_mk_eq (Abs(v,l)) (Abs(v,r)) in
            Sequent (asl,eq,proof_ABS v p (asl,eq))
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> let eq = safe_mk_eq tm bod in
           Sequent([],eq,proof_BETA tm ([], eq))
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      Sequent([tm],tm,proof_ASSUME tm ([tm], tm))
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq,p1)) (Sequent(asl2,c,p2)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> let t = term_union asl1 asl2 in
           Sequent(t,r,proof_EQ_MP p1 p2 (t,r))
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1,p1)) (Sequent(asl2,c2,p2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    let (a,g) = (term_union asl1' asl2',safe_mk_eq c1 c2) in
    Sequent (a, g, proof_DEDUCT_ANTISYM_RULE (p1,c1) (p2,c2) (a, g))

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c,p)) =
    let inst_fn = inst theta in
    let (a, g) = (term_image inst_fn asl,inst_fn c) in
    Sequent(a,g, proof_INST_TYPE theta p (a,g))

  let INST theta (Sequent(asl,c,p)) =
    let inst_fun = vsubst theta in
    let (a, g) = (term_image inst_fun asl,inst_fun c) in
    Sequent(a, g, proof_INST theta p (a,g))

(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let axname = new_axiom_name "" in
      let p = proof_new_axiom axname tm ([], tm) in
      let th = Sequent([],tm,p) in
       (the_axioms := th::(!the_axioms);
        save_proof axname p ([], tm); th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)

  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),Var(cname,ty)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(cname,ty) in
             let concl = safe_mk_eq c r in
             let p = proof_new_definition cname ty r ([], concl) in
             let dth = Sequent([],concl, p) in
             save_proof ("hidden_DEF_"^cname) p ([], concl);
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
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(absname,absty))
    and rep = (new_constant(repname,repty); Const(repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    let ax1 = safe_mk_eq (Comb(abs,mk_comb(rep,a))) a
    and ax2 = safe_mk_eq (Comb(P,r)) (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r) in
    let mk_binary s =
      let c = mk_const(s,[]) in
      fun (l,r) -> try mk_comb(mk_comb(c,l),r)
                   with Failure _ -> failwith "tydef_mk_binary"
    in
    let axc = mk_binary "/\\" (ax1, ax2) in
    let tp = proof_new_basic_type_definition tyname (absname, repname) (P,x) p ([], axc) in
    let p1 = proof_CONJUNCT1 tp ([], ax1) in
    let p2 = proof_CONJUNCT2 tp ([], ax2) in
    save_proof ("hidden_TYDEF_" ^ tyname) tp ([], axc);
    (Sequent([],ax1,p1), Sequent([],ax2,p2));;

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;

let store_name n f a = let thm = f a in (tag_intermediate_step n thm; thm);;
let store_namea n f a1 a2 = let thm = f a1 a2 in (tag_intermediate_step n thm; thm);;
let store_name2 n1 n2 f a = let t1, t2 = f a in (tag_intermediate_step n1 t1; tag_intermediate_step n2 t2; t1, t2);;
let store_name3 n1 n2 n3 f a = let t1, t2, t3 = f a in (tag_intermediate_step n1 t1; tag_intermediate_step n2 t2; tag_intermediate_step n3 t3; t1, t2, t3);;
let store_name2a n1 n2 f a1 a2 a3 a4 = let t1, t2 = f a1 a2 a3 a4 in (tag_intermediate_step n1 t1; tag_intermediate_step n2 t2; t1, t2);;
