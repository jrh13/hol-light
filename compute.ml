(* ========================================================================== *)
(*       Call-by-value reduction of terms similar to ML computation.          *)
(*                  Translated from HOL4 computeLib                           *)
(*                                                                            *)
(*                 (c) Copyright Alexey Solovyev 2018                         *)
(*                   (c) Copyright Bruno Barras 2000                          *)
(*                                                                            *)
(*        Distributed under the same license as HOL Light.                    *)
(* ========================================================================== *)

needs "pair.ml";;

module type Compute_sig = sig
  type compset

  val monitoring : (term -> bool) option ref
  val stoppers : (term -> bool) option ref

  val new_compset : thm list -> compset
  val bool_compset : unit -> compset
  val basic_compset : unit -> compset

  val add_thms : thm list -> compset -> unit
  val add_conv : term * int * conv -> compset -> unit
  val set_skip : compset -> term -> int option -> unit

  val scrub_const : compset -> term -> unit
  val scrub_thms : thm list -> compset -> unit

  val lazyfy_thm : thm -> thm
  val strictify_thm : thm -> thm

  val CBV_CONV : compset -> term -> thm
  val WEAK_CBV_CONV : compset -> term -> thm

  val the_compset : compset
  val add_funs : thm list -> unit
  val add_convs : (term * int * conv) list -> unit

  val del_consts : term list -> unit
  val del_funs : thm list -> unit

  val EVAL_CONV : conv
  val EVAL_RULE : thm -> thm
  val EVAL_TAC : tactic

  val RESTR_EVAL_CONV : term list -> conv
  val RESTR_EVAL_RULE : term list -> thm -> thm
  val RESTR_EVAL_TAC : term list -> tactic

  val OR : term list -> term -> bool

  type 'a fterm
  type db
  type transform = Conversion of (term -> thm * db fterm) | Rrules of thm list

  val listItems : compset -> (string * transform list) list
end;;

(* TODO Restore to original position once a binary with cakeml#1316
   included is available *)

type ('a, 'b, 'c) stack =
    Ztop
  | Zrator of 'a * ('a, 'b, 'c) stack
  | Zrand of 'b * ('a, 'b, 'c) stack
  | Zabs of 'c * ('a, 'b, 'c) stack;;

type pattern =
    Pvar of int
  | Papp of term * pattern list;;

type 'a cst_rec = Cst_rec of
  (* head: *) term *
  (* args: *) (term * 'a fterm) list *
  (* rws: *) 'a *
  (* skip: *) int option

and 'a clos_rec = Clos_rec of
  (* env: *) 'a fterm list *
  (* term: *) 'a dterm

and 'a fterm =
    Fconst of 'a cst_rec
  | Neutr
  | Clos of 'a clos_rec

(*---------------------------------------------------------------------------
 * An alternative representation of terms, with all information needed:
 * - they are real de Bruijn terms, so that abstraction destruction is in
 *   constant time.
 * - application is n-ary (slight optimization)
 * - we forget the names of variables
 * - constants are tagged with the set of rewrites that apply to it.
 *   It's a reference since dterm is used to represent rhs of rewrites,
 *   and fixpoints equations add rewrites for a constant that appear in the
 *   rhs.
 *---------------------------------------------------------------------------*)

and 'a dterm =
    Bv of int
  | Fv
  | Cst of term * ('a * int option) ref
  | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
  | Dabs of 'a dterm;;
(* Invariant: the first arg of App never is an App. *)


type action =
    Rewrite of rewrite list
  | Conv of (term -> thm * db fterm)

and try_rec = Try_rec of
  (* hcst: *) term *
  (* rws: *) action *
  (* tail: *) db


and db =
    End_db
  | Try of try_rec
  | Need_arg of db

and rewrite_rec = Rewrite_rec of
  (* cst: *) term *         (* constant which the rule applies to *)
  (* lhs: *) pattern list * (* patterns = constant args in lhs of thm *)
  (* npv: *) int *          (* number of distinct pat vars in lhs *)
  (* rhs: *) db dterm *
  (* thm: *) thm            (* thm we use for rewriting *)


and rewrite =
    Rw of rewrite_rec;;

type cbv_stack =
  ((thm->thm->thm) * (thm * db fterm),
   (thm->thm->thm) * bool * (thm * db fterm),
   (thm->thm)) stack;;

module Compute = struct

let with_flag (flag, b) f x =
  let fval = !flag in
  let () = flag := b in
  let res = try f x with e -> (flag := fval; raise e) in
  flag := fval; res;;

let RIGHT_BETA th =
  try TRANS th (BETA_CONV (rhs (concl th)))
  with _ -> failwith "RIGHT_BETA";;

let RIGHT_ETA thm =
  try TRANS thm (ETA_CONV (rhs (concl thm)))
  with _ -> failwith "RIGHT_ETA";;

let MK_comb th =
  let rator, rand = dest_comb (rhs (concl th)) in
  let mka th1 th2 = TRANS th (MK_COMB (th1, th2)) in
  (REFL rator, REFL rand, mka);;

let MK_abs th =
  let bvar, body = dest_abs (rhs (concl th)) in
  (bvar, REFL body, fun th1 -> TRANS th (ABS bvar th1));;

let rec BODY_CONJUNCTS th =
  if is_forall (concl th) then
    BODY_CONJUNCTS (SPEC_ALL th)
  else if is_conj (concl th) then
    BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
  else [th];;

(*** compute_rules.sml ***)

exception Dead_code of string;;

let rhs_concl = rand o concl;;
let refl_thm = REFL;;
let trans_thm = TRANS;;
let beta_thm = RIGHT_BETA;;
let evaluate th = th;;

let try_eta thm = try RIGHT_ETA thm with _ -> thm;;

(*---------------------------------------------------------------------------
 * Precondition: f(arg) is a closure corresponding to b.
 * Given   (arg,(|- M = (a b), Stk)),
 * returns (|- a = a, (<fun>,(|- b = b, f(arg)))::Stk)
 * where   <fun> =  (|- a = a' , |- b = b') |-> |- M = (a' b')
 *---------------------------------------------------------------------------*)

let push_in_stk f arg (th, stk) =
  let (tha, thb, mka) = MK_comb th in
  (tha, Zrator ((mka, (thb, f arg)), stk));;

let push_skip_stk f arg (th, stk) =
  let (tha, thb, mka) = MK_comb th in
  (tha, Zrand ((C mka, true, (thb, f arg)), stk));;

let push_lam_in_stk (th, stk) =
  let (_, thb, mkl) = MK_abs th in
  (thb, Zabs (try_eta o mkl, stk));;

(*---------------------------------------------------------------------------
  Does conversions between
                              FUNIFY
    |- (c t_1 .. t_n x) = M    --->   |- (c t_1 .. t_n) = \x. M
                               <---
                             UNFUNIFY
   In UNFUNIFY, we must avoid choosing an x that appears free in t_1..t_n.
 ---------------------------------------------------------------------------*)

let FUNIFY thm =
  try
    let x = rand (lhs (concl thm)) in
    CONV_RULE (RATOR_CONV (RAND_CONV (CHANGED_CONV (PURE_REWRITE_CONV[ETA_AX])))) (ABS x thm)
  with _ -> failwith "FUNIFY";;

let UNFUNIFY thm =
  try
    let lhs, rhs = dest_eq (concl thm) in
    let x = variant (frees lhs) (fst (dest_abs rhs)) in
    CONV_RULE (RAND_CONV BETA_CONV) (AP_THM thm x)
  with _ -> failwith "UNFUNIFY";;

let repeat_on_conj f thm =
  let rec iter th = try iter (f th) with _ -> th in
  end_itlist CONJ (List.map iter (BODY_CONJUNCTS thm));;

let lazyfy_thm = repeat_on_conj FUNIFY;;
let strictify_thm = repeat_on_conj UNFUNIFY;;

(* Ensures a theorem is an equality. *)
let eq_intro thm =
  if is_eq (concl thm) then thm else
  if is_neg (concl thm) then EQF_INTRO thm
  else EQT_INTRO thm;;

(*** clauses.sml ***)

(*---------------------------------------------------------------------------
 * Checking that a given thm is a reduction rule we can handle:
 *         (c p1...pn) = rhs
 * with p1...pn  either a const applied to patterns or a free variable.
 *---------------------------------------------------------------------------*)

let check_arg_form trm =
  let rec chk t stk free =
    if is_comb t then
      let rator, rand = dest_comb t in
      let free', pat1 = chk rand [] free in
      chk rator (pat1 :: stk) free'
    else if is_var t then
      if stk = [] then
        let newi = List.length free in
        try (free, Pvar (newi - index t free - 1))
        with _ -> (t :: free, Pvar newi)
      else
        failwith ("check_arg_form: " ^ fst (dest_var t) ^ " occurs as a variable on lhs")
    else if is_const t then
      (free, Papp (t, List.rev stk))
    else
      failwith ("check_arg_form: lambda abstraction not allowed on lhs: `"
        ^ (string_of_term trm) ^ "`")
  in
  match chk trm [] [] with
    | (fv, Papp (head, args)) -> (List.rev fv, head, args)
    | _ -> failwith "check_arg_form: ill-formed lhs";;

(*---------------------------------------------------------------------------
 * CLOS denotes a delayed substitution (closure).
 * CST denotes an applied constant. Its first argument is the head constant;
 *   the second is the list of its arguments (we keep both the term and its
 *   abstract representation); the last one is the set of rewrites that
 *   still have a chance to be used, ie. those with a lhs wider than the
 *   number of applied args.
 * NEUTR is a slight improvement of CST with an empty list of rewrites, so
 *   that arguments of a variable are immediatly strongly reduced.
 *---------------------------------------------------------------------------*)

let appl = function
  | App (a, l1), arg -> App (a, arg :: l1)
  | t, arg -> App (t, [arg]);;

(*---------------------------------------------------------------------------
 * Type variable instantiation in dterm. Make it tail-recursive ?
 *---------------------------------------------------------------------------*)

let inst_type_dterm = function
  | [], v -> v
  | tysub, v ->
    let rec tyi_dt = function
      | Cst (c, dbsk) -> Cst (inst tysub c, dbsk)
      | App (h, l) -> App (tyi_dt h, map tyi_dt l)
      | Dabs v -> Dabs (tyi_dt v)
      | v -> v in
    tyi_dt v;;

let rec add_in_db = function
  | (n, cst, act, End_db) ->
      funpow n (fun a -> Need_arg a) (Try (Try_rec (cst, act, End_db)))
  | (0, cst, (Rewrite nrws as act), Try (Try_rec (hcst, (Rewrite rws as rw), tail))) ->
    if cst = hcst then Try (Try_rec (hcst, (Rewrite (nrws @ rws)), tail))
    else Try (Try_rec (hcst, rw, (add_in_db (0, cst, act, tail))))
  | (n, cst, act, Try (Try_rec (hcst, rws, tail))) ->
    Try (Try_rec (hcst, rws, (add_in_db(n, cst, act, tail))))
  | (0, cst, act, db) ->
    Try (Try_rec (cst, act, db))
  | (n, cst, act, Need_arg tail) ->
    Need_arg (add_in_db(n - 1, cst, act, tail));;

let key_of (Rw (Rewrite_rec (cst, lhs, _, _, _))) =
  let name, _ = dest_const cst in
  (name, length lhs, cst);;

let is_skip = function
  | (_, Fconst (Cst_rec (_, args, _, Some n))) -> n <= List.length args
  | _ -> false;;

let partition_skip skip args =
  match skip with
  | Some n ->
    let len = List.length args in
    if n <= len then
      chop_list (len - n) args
    else
      ([], args)
  | None -> ([], args);;

(*---------------------------------------------------------------------------
 * equation database
 * We should try to factorize the rules (cf discrimination nets)
 * Rules are packed according to their head constant, and then sorted
 * according to the width of their lhs.
 *---------------------------------------------------------------------------*)

type compset =
    Rws of ((string, (db * int option) ref) Hashtable.hashtable);;

let empty_rws () = Rws (Hashtable.empty 100 string_hash String.compare);;

let assoc_clause (Rws rws) cst =
  match Hashtable.lookup rws cst with
  | None ->
     let mt = ref (End_db, None) in
     Hashtable.insert rws cst mt;
     mt
  | Some r -> r;;

let add_in_db_upd rws (name, arity, hcst) act =
  let rl = assoc_clause rws name in
  let db, sk = !rl in
  rl := add_in_db (arity, hcst, act, db), sk;;

let set_skip_name (Rws htbl as rws) p sk =
  let rl = assoc_clause rws p in
  let db, _ = !rl in
  rl := db, sk;;

let scrub_const (Rws htbl) c =
  let name, _ = dest_const c in
  Hashtable.delete htbl name;;

let from_term (rws, env, t) =
  let rec down (env, t, c) =
    match t with
    | Var _ -> up ((try Bv (index t env) with _ -> Fv), c)
    | Const (name, _) -> up (Cst (t, assoc_clause rws name), c)
    | Comb (rator, rand) -> down (env, rator, Zrator ((env, rand), c))
    | Abs (bvar, body) -> down (bvar :: env, body, Zabs ((), c))

  and up = function
    | dt, Ztop -> dt
    | dt, Zrator ((env, arg), c) -> down (env, arg, Zrand(dt, c))
    | dt, Zrand (dr, c) -> up (appl (dr, dt), c)
    | dt, Zabs (_, c) -> up (Dabs dt, c)
  in
  down (env, t, Ztop);;

(*---------------------------------------------------------------------------
 * Note: if the list of free variables of the lhs was empty, we could
 * evaluate (weak reduction) the rhs now. This implies that the
 * theorems must be added in dependencies order.
 *---------------------------------------------------------------------------*)

let mk_rewrite rws eq_thm =
  let lhs, rhs = dest_eq (concl eq_thm) in
  let fv, cst, pats = check_arg_form lhs in
  let gen_thm = itlist GEN fv eq_thm in
  let rhsc = from_term (rws, rev fv, rhs) in
  Rw (Rewrite_rec (
    (* cst = *) cst,
    (* lhs = *) pats,
    (* npv = *) length fv,
    (* rhs = *) rhsc,
    (* thm = *) gen_thm
  ));;

let unsuitable th =
  let l, r = dest_eq (concl th) in
  can (term_match [] l) r;;

let enter_thm rws thm0 =
  let thm = eq_intro thm0 in
  if unsuitable thm then ()
  else
    let rw = mk_rewrite rws thm in
    add_in_db_upd rws (key_of rw) (Rewrite [rw]);;

let add_thms lthm rws =
  List.app (List.app (enter_thm rws) o BODY_CONJUNCTS) lthm;;

let add_extern (cst, arity, fconv) rws =
  let name, _ = dest_const cst in
  add_in_db_upd rws (name, arity, cst) (Conv fconv);;

let new_rws () =
  let rws = empty_rws () in
  add_thms [REFL_CLAUSE] rws;
  rws;;

let from_list lthm =
  let rws = new_rws() in
  add_thms lthm rws;
  rws;;

let scrub_thms lthm rws =
  let tmlist = map (concl o hd o BODY_CONJUNCTS) lthm in
  let clist = map (fst o strip_comb o lhs o snd o strip_forall) tmlist in
  List.app (scrub_const rws) clist;;


(*---------------------------------------------------------------------------*)
(* Support for analysis of compsets                                          *)
(*---------------------------------------------------------------------------*)

let rws_of (Rws htbl) =
  let dblist =
    List.map (fun (_, v) -> let (db, _) = !v in db) (Hashtable.toAscList htbl) in
  let rec get_actions db =
    match db with
    | End_db -> []
    | Need_arg db' -> get_actions db'
    | Try (Try_rec (hcst, rws, tail)) ->
      (hcst, rws) :: get_actions tail in
  let actionlist = List.concat (List.map get_actions dblist) in
  let dest (Rw (Rewrite_rec (_, _, _, _, thm))) = thm in
  let dest_action = function
    | hcst, Rewrite rws -> (hcst, map dest rws)
    | hcst, Conv _ -> (hcst, []) in
  let rwlist = List.map dest_action actionlist in
  rwlist;;

type transform =
    Conversion of (term -> thm * db fterm)
  | Rrules of thm list;;

(*---------------------------------------------------------------------------*)
(* Compute the "attachments" for each element of the compset. Fortunately,   *)
(* it seems that the insertion of an attachment into a compset also makes    *)
(* insertions for the constants mentioned in the rhs of the rewrite.         *)
(* Otherwise, one would have to do a transitive closure sort of construction *)
(* to make all the dependencies explicit.                                    *)
(*---------------------------------------------------------------------------*)

let deplist (Rws htbl) =
  let dblist =
    List.map (fun (s, v) -> let (db, _) = !v in (s, db)) (Hashtable.toAscList htbl) in
  let rec get_actions db =
    match db with
    | End_db -> []
    | Need_arg db' -> get_actions db'
    | Try (Try_rec (hcst, rws, tail)) ->
      rws :: get_actions tail in
  let actionlist = List.map (fun (s, db) -> s, get_actions db) dblist in
  let dest (Rw (Rewrite_rec (_, _, _, _, thm))) = thm in
  let dest_action = function
    | Rewrite rws -> Rrules (map dest rws)
    | Conv ecnv -> Conversion ecnv in
  let rwlist = List.map (fun (s, act) -> s, map dest_action act) actionlist in
  rwlist;;


(*** equations.sml ***)

(*---------------------------------------------------------------------------
 * The First order matching functions.
 *
 * We do not consider general non-linear patterns. We could try (requires a
 * more elaborate conversion algorithm, and it makes matching and reduction
 * mutually dependent).
 *---------------------------------------------------------------------------*)
exception No_match;;

let match_const (bds, tbds) pc c =
  let name, ty = dest_const pc in
  let name', ty' = dest_const c in
  if name = name' then
    try bds, type_match ty ty' tbds with _ -> raise No_match
  else raise No_match;;

(*---------------------------------------------------------------------------
 * Match pattern variable number var with term arg.
 * We do not need to match types, because pattern variables appear as argument
 * of a constant which has already been matched succesfully.
 *---------------------------------------------------------------------------*)

let match_var (bds, tbds) var arg =
  let _ = match bds.(var) with
  | Some (tm, _) -> if aconv tm (fst arg) then () else raise No_match
  | None -> Array.update bds (var) (Some arg) in
  (bds, tbds);;

(*---------------------------------------------------------------------------
 * Tries to match a list of pattern to a list of arguments.
 * We assume that we already checked the lengths (probably a good short-cut)
 *
 * Returns a list of bindings that extend the ones given as
 * argument (bds), or a No_match exception.
 *---------------------------------------------------------------------------*)

let rec match_list bds pats args =
  match (pats, args) with
    | pat :: pats, arg :: args ->
      match_list (match_solve bds pat arg) pats args
    | [], [] -> bds
    | _ -> raise (Dead_code "match_list")

and match_solve bds pat arg =
  match (pat, arg) with
  | Pvar var, arg -> match_var bds var arg
  | Papp (phead, pargs), (_, Fconst (Cst_rec (head, args, _, _))) ->
    if length pargs = length args then
      match_list (match_const bds phead head) pargs args
    else
      raise No_match
  | _ -> raise No_match;;

(*---------------------------------------------------------------------------
 * Try a sequence of rewrite rules. No attempt to factorize patterns!
 *---------------------------------------------------------------------------*)

type 'a rule_inst = Rule_inst of (
  (* rule: *) rewrite *
  (* inst: *) ((term * 'a fterm) option array * (hol_type * hol_type) list)
);;

let try_rwn ibds lt =
  let rec try_rec = function
    | [] -> raise No_match
    | (Rw (Rewrite_rec (_, lhs, npv, _, _)) as rw) :: rwn ->
      let env = Array.array npv None in
      try Rule_inst (rw, match_list (env, ibds) lhs lt)
      with No_match -> try_rec rwn
  in
  try_rec;;

(*---------------------------------------------------------------------------
 * Instantiating the rule according to the output of the matching.
 *---------------------------------------------------------------------------*)

let comb_ct cst arg =
  match cst with
  | Cst_rec (head, args, Need_arg tail, skip) ->
    Fconst (Cst_rec (head, arg :: args, tail, skip))
  | Cst_rec (head, args, End_db, skip) ->
    Fconst (Cst_rec (head, arg :: args, End_db, skip))
  | Cst_rec (_, _, Try _, _) ->
    raise (Dead_code "comb_ct: yet rules to try");;

let mk_clos (env, t) =
  match t with
  | Cst (hc, r) ->
     let (db, b) = !r in
     Fconst (Cst_rec (hc, [], db, b))
  | Bv i -> List.nth env i
  | Fv -> Neutr
  | _ -> Clos (Clos_rec (env, t));;

(*---------------------------------------------------------------------------
 * It is probably this code that can be improved the most
 *---------------------------------------------------------------------------*)

let inst_one_var (thm, lv) = function
  | Some (tm, v) -> SPEC tm thm, v :: lv
  | None -> raise (Dead_code "inst_rw");;

let inst_rw (th, monitoring, rule_inst) =
  let Rule_inst (rule, inst) = rule_inst in
  let (Rw (Rewrite_rec (_, _, _, rhs, thm))) = rule in
  let (bds, tysub) = inst in
  let tirhs = inst_type_dterm (tysub, rhs) in
  let tithm = INST_TYPE tysub thm in
  let spec_thm, venv = Array.foldl (flip inst_one_var) (tithm, []) bds in
  let () = if monitoring then print_term (concl spec_thm) in
  trans_thm th spec_thm, mk_clos (venv, tirhs);;

let monitoring = ref (None: (term -> bool) option);;
let stoppers = ref (None: (term -> bool) option);;

(*---------------------------------------------------------------------------
 * Reducing a constant
 *---------------------------------------------------------------------------*)

let rec reduce_cst = function
  | th, Cst_rec (head, args, Try (Try_rec (hcst, Rewrite rls, tail)), skip) ->
   (try
      let () = match !stoppers with None -> () | Some p -> if p head then raise No_match else () in
      let _, _, tytheta = try term_match [] hcst head with _ -> raise No_match in
      let rule_inst = try_rwn tytheta args rls in
      let mon = match !monitoring with None -> false | Some f -> f head in
      let insted = inst_rw (th, mon, rule_inst) in
        (true, insted)
    with No_match ->
      reduce_cst (th, Cst_rec (head, args, tail, skip)))
  | th, Cst_rec (head, args, Try (Try_rec (hcst, Conv fconv, tail)), skip) ->
   (try
      let thm, ft = fconv (rhs_concl th) in
        (true, (trans_thm th thm, ft))
    with _ ->
      reduce_cst (th, Cst_rec (head, args, tail, skip)))
  | th, cst -> (false, (th, Fconst cst));;


(*** computeLib.sml ***)

let auto_import_definitions = ref true;;

(* re-exporting types from clauses *)

let new_compset = from_list;;
let listItems = deplist;;

let rec stack_out = function
  | th, Ztop -> th
  | th, Zrator ((mka, (thb, _)), ctx) -> stack_out (mka th thb, ctx)
  | th, Zrand ((mka, _, (tha, _)), ctx) -> stack_out (mka tha th, ctx)
  | th, Zabs (mkl, ctx) -> stack_out (mkl th, ctx);;

let initial_state rws t =
  ((refl_thm t, mk_clos ([], from_term (rws, [], t))), (Ztop: cbv_stack));;

(*---------------------------------------------------------------------------
 * [cbv_wk (rws,(th,cl),stk)] puts the closure cl (useful information about
 * the rhs of th) in head normal form (weak reduction). It returns either
 * a closure which term is an abstraction, in a context other than Zappl,
 * a variable applied to strongly reduced arguments, or a constant
 * applied to weakly reduced arguments which does not match any rewriting
 * rule.
 *
 * - substitution is propagated through applications.
 * - if the rhs is an abstraction and there is one arg on the stack,
 *   this means we found a beta redex. mka rebuilds the application of
 *   the function to its argument, and Beta does the actual beta step.
 * - for an applied constant, we look for a rewrite matching it.
 *   If we found one, then we apply the instantiated rule, and go on.
 *   Otherwise, we try to rebuild the thm.
 * - for an already strongly normalized term or an unapplied abstraction,
 *   we try to rebuild the thm.
 *---------------------------------------------------------------------------*)

let rec cbv_wk = function
  | (th, Clos (Clos_rec (env, App (a, args)))), stk ->
    let tha, stka = rev_itlist (push_in_stk (curry mk_clos env)) args (th, stk) in
    cbv_wk ((tha, mk_clos (env, a)), stka)
  | (th, Clos (Clos_rec (env, Dabs body))), Zrator ((mka, (thb, cl)), s') ->
    cbv_wk ((beta_thm (mka th thb), mk_clos (cl :: env, body)), s')
  | (th, Fconst cargs), stk ->
    let reduced, clos = reduce_cst (th, cargs) in
    if reduced then cbv_wk (clos, stk) else cbv_up (clos, stk)
  | clos, stk -> cbv_up (clos, stk)

(*---------------------------------------------------------------------------
 * Tries to rebuild the thm, knowing that the closure has been weakly
 * normalized, until it finds term still to reduce, or if a strong reduction
 * may be required.
 *  - if we are done with a Rator, we start reducing the Rand
 *  - if we are done with the Rand of a const, we rebuild the application
 *    and look if it created a redex
 *  - an application to a NEUTR can be rebuilt only if the argument has been
 *    strongly reduced, which we now for sure only if itself is a NEUTR.
 *---------------------------------------------------------------------------*)

and cbv_up = function
  | hcl, Zrator ((mka, clos), ctx) ->
    let new_state = clos, Zrand ((mka, false, hcl), ctx) in
    if is_skip hcl then cbv_up new_state else cbv_wk new_state
  | (thb, v), Zrand ((mka, false, (th, Fconst cargs)), stk) ->
    cbv_wk ((mka th thb, comb_ct cargs (rhs_concl thb, v)), stk)
  | (thb, Neutr), Zrand ((mka, false, (th, Neutr)), stk) ->
    cbv_up ((mka th thb, Neutr), stk)
  | clos, stk -> clos, stk;;

(*---------------------------------------------------------------------------
 * [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 * precondition: the closure should be the output of cbv_wk
 *---------------------------------------------------------------------------*)

let rec strong = function
  | (th, Clos (Clos_rec (env, Dabs t))), stk ->
    let thb, stk' = push_lam_in_stk (th, stk) in
    strong (cbv_wk ((thb, mk_clos (Neutr :: env, t)), stk'))
  | (_, Clos _), stk ->
    raise (Dead_code "strong")
  | (th, Fconst (Cst_rec (_, args, _, skip))), stk ->
    let argssk, argsrd = partition_skip skip args in
    let th', stk' = rev_itlist (push_skip_stk snd) argssk (th, stk) in
    let th'', stk'' = rev_itlist (push_in_stk snd) argsrd (th', stk') in
    strong_up (th'', stk'')
  | (th, Neutr), stk -> strong_up (th, stk)

and strong_up = function
  | th, Ztop -> th
  | th, Zrand ((mka, false, (tha, Neutr)), ctx) ->
    strong (cbv_wk ((mka tha th, Neutr), ctx))
  | th, Zrand ((mka, false, clos), ctx) ->
    raise (Dead_code "strong_up")
  | th, Zrator ((mka, clos), ctx) ->
    strong (cbv_wk (clos, Zrand ((mka, true, (th, Neutr)), ctx)))
  | th, Zrand ((mka, true, (tha, _)), ctx) ->
    strong_up (mka tha th, ctx)
  | th, Zabs (mkl, ctx) ->
    strong_up (mkl th, ctx);;

(*---------------------------------------------------------------------------
 * [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *---------------------------------------------------------------------------*)

let CBV_CONV rws = evaluate o strong o cbv_wk o initial_state rws;;

(*---------------------------------------------------------------------------
 * WEAK_CBV_CONV is the same as CBV_CONV except that it does not reduce
 * under abstractions, and reduce weakly the arguments of constants.
 * Reduction whenever we reach a state where a strong reduction is needed.
 *---------------------------------------------------------------------------*)

let WEAK_CBV_CONV rws =
  evaluate
  o (fun ((th, _), stk) -> stack_out (th, stk))
  o cbv_wk
  o initial_state rws;;

(*---------------------------------------------------------------------------
 * Adding an arbitrary conv
 *---------------------------------------------------------------------------*)

let extern_of_conv rws conv tm =
  let thm = conv tm in
  thm, mk_clos ([], from_term (rws, [], rhs (concl thm)));;

let add_conv (cst, arity, conv) rws =
  add_extern (cst, arity, extern_of_conv rws conv) rws;;

let set_skip compset c opt =
  try
    let name, _ = dest_const c in
    set_skip_name compset name opt
  with _ -> failwith "set_skip";;


(*---------------------------------------------------------------------------
       Support for a global compset.
 ---------------------------------------------------------------------------*)

let bool_redns =
  strictify_thm LET_DEF
  :: List.map lazyfy_thm
    [COND_CLAUSES; COND_ID; NOT_CLAUSES;
     AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES];;

let bool_compset () =
  let base = from_list bool_redns in
  let () = set_skip base `COND: bool -> A -> A -> A` None in
  (* Invoke set_skip again with last parameter set to Some 1 to stop CBV_CONV
     looking at conditionals' branches before the guard is fully true or false
  *)
  base;;

let basic_compset () =
  let basic_rws0 = basic_rewrites() in
  (* Remove rewrite rules that cause the "lambda abstraction not allowed in
     lhs" error. *)
  let lhs_lambda_rules = map SPEC_ALL [SELECT_REFL;FORALL_SIMP;EXISTS_SIMP] in
  let basic_rws = List.filter (fun th ->
    not (mem th lhs_lambda_rules)) basic_rws0 in
  let cs = new_compset (List.map lazyfy_thm basic_rws) in
  List.app (fun (_,(pat,the_conv)) ->
    let cst,args = strip_comb pat in
    add_conv (cst,length args,the_conv) cs) (basic_convs());
  add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  set_skip cs `COND: bool -> A -> A -> A` None;
  (* Invoke set_skip again with last parameter set to Some 1 to stop CBV_CONV
     looking at conditionals' branches before the guard is fully true or false
  *)
  cs;;

let the_compset = bool_compset();;

let add_funs = C add_thms the_compset;;
let add_convs = List.app (C add_conv the_compset);;

let del_consts = List.app (scrub_const the_compset);;
let del_funs = C scrub_thms the_compset;;

let EVAL_CONV = CBV_CONV the_compset;;
let EVAL_RULE = CONV_RULE EVAL_CONV;;
let EVAL_TAC = CONV_TAC EVAL_CONV;;

let same_const c1 c2 = fst (dest_const c1) = fst (dest_const c2);;

let rec OR = function
  | [] -> K false
  | [x] -> same_const x
  | h :: t -> fun x -> same_const h x || OR t x;;

let RESTR_EVAL_CONV clist =
  with_flag (stoppers, Some (OR clist)) EVAL_CONV;;

let RESTR_EVAL_TAC = CONV_TAC o RESTR_EVAL_CONV;;
let RESTR_EVAL_RULE = CONV_RULE o RESTR_EVAL_CONV;;

end;;
