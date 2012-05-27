(* ====================================================== *)
(*               Squolem proof reconstruction             *)
(*          (c) Copyright, Ondřej Kunčar 2010-11          *)
(* ====================================================== *)


set_jrh_lexer;;

let show_progress = ref false;;
let show_timing = ref false;;
let delete_qbf_tempfiles = ref true;;

type quantifier = Existential of term | Universal of term;;

let make_variable index =
  if index <= 0 then failwith "Variable of index 0 or lesser is not allowed"
  else mk_var ("v_"^(string_of_int index), bool_ty)
;;

let make_literal index =
  if index < 0 then mk_neg (make_variable (-index))
  else make_variable index
;;

let destroy_variable var =
  let var_string = string_of_term var in
  int_of_string (String.sub var_string 2 (String.length var_string -2))
;;

let destroy_literal lit =
  match is_neg lit with
  true -> - destroy_variable (dest_neg lit)
  | false -> destroy_variable lit
;;

let get_quant_var quantifier =
  match quantifier with
    Existential t -> t
    | Universal t -> t
;;

let has_quant tm =
        Pervasives.(||) (is_exists tm) (is_forall tm)
;;

let dest_quant tm =
        if is_exists tm then dest_exists tm
        else dest_forall tm
;;

module type Qbfcontextsig =
sig
  type variables = (int,unit) Hashtbl.t;;
  type extensions = (int,term) Hashtbl.t;;

  type quantifiers = quantifier list;;
  type aux_variables = int list;;
  type q_levels = int array;;
  type context = {
    (** all variables, i.e, variables in a formula and auxiliary variables from extensions *)
    variables:variables;
    extensions:extensions;
    mutable aux_variables:aux_variables;
    (** quantifiers prefix in bottom-up ordering *)
    mutable quantifiers:quantifiers;
    mutable q_levels:q_levels;
                mutable q_ordered_levels:q_levels };;

  val create_context : int -> context
  (** quantifiers must be in bottom-up ordering *)
  val set_quantifiers : context -> quantifiers -> unit
  val check_variable : context -> int -> unit
  val check_fresh_variable : context -> int -> unit
  val add_universal_variable : context -> int -> unit
  val add_existential_variable : context -> int -> unit
  val add_extension : context -> int -> term -> unit
  val add_conclusion_eq : context -> int -> term -> unit
  val get_extensions : context -> (term * term) list
        val get_extension : context -> int -> term
  val get_quantifiers : context -> quantifiers
  val get_aux_variables : context -> aux_variables
  val make_quantifiers_levels : context -> unit
        val make_ordered_quantifiers_levels : context -> unit
        val lt_levels : context  -> int -> int -> bool
        val lt_ordered_levels : context  -> int -> int -> bool
end;;

module Qbfcontext : Qbfcontextsig =
struct
  type variables = (int,unit) Hashtbl.t;;
  type extensions = (int,term) Hashtbl.t;;

  type quantifiers = quantifier list;;
  type aux_variables = int list;;
  type q_levels = int array;;
  type context = {
                variables:variables;
                extensions:extensions;
                mutable aux_variables:aux_variables;
                mutable quantifiers:quantifiers;
                mutable q_levels:q_levels;
                mutable q_ordered_levels:q_levels
        };;

  let create_context var_count =
    { variables = Hashtbl.create (2*var_count);
                        extensions = Hashtbl.create var_count;
                        aux_variables = [];
                        quantifiers = [];
                        q_levels = Array.make 0 0;
                        q_ordered_levels = Array.make 0 0 }
  ;;

  let set_quantifiers context quants =
    context.quantifiers <- quants
  ;;

  let check_variable context var_index =
    if not (Hashtbl.mem context.variables var_index) then failwith ((string_of_int var_index)^" is undefined variable")
  ;;

  let check_fresh_variable context var_index =
    if Hashtbl.mem context.variables var_index then failwith ((string_of_int var_index)^" is not a fresh variable")
  ;;

  let add_universal_variable context var_index =
    check_fresh_variable context var_index;
    Hashtbl.add context.variables var_index ()
  ;;

  let add_existential_variable context var_index =
    check_fresh_variable context var_index;
    Hashtbl.add context.variables var_index ();
    Hashtbl.add context.extensions var_index `T`
  ;;

        let add_aux_variable context var_index =
    check_fresh_variable context var_index;
    Hashtbl.add context.variables var_index ();
    context.aux_variables <- var_index::context.aux_variables
  ;;

  let add_aux_quantifier context var_index free_variables =
    let quantifier = Existential (make_variable var_index) in
    let rec remove_from_list l ls =
      match ls with
      [] -> []
      | l'::ls' when l'=l -> ls'
      | l'::ls'-> l'::remove_from_list l ls'
    in
    let rec insert_quantifier quantifiers free_variables =
      match free_variables with
      [] -> quantifier::quantifiers
      | _ -> match quantifiers with
        q::qs -> q::(insert_quantifier qs (remove_from_list (get_quant_var q) free_variables))
        | [] -> failwith "add_aux_quantifier: logic error"
    in
    context.quantifiers <- List.rev ((insert_quantifier (List.rev context.quantifiers) free_variables))
  ;;

  let add_extension context var_index formula =
    add_aux_variable context var_index;
    add_aux_quantifier context var_index (variables formula);
    Hashtbl.add context.extensions var_index formula
  ;;

  let add_conclusion_eq context var_index formula =
    Hashtbl.replace context.extensions var_index formula
  ;;

        let get_extension context var_index =
                Hashtbl.find context.extensions var_index
        ;;

  let get_extensions context =
    Hashtbl.fold (fun f s l -> (make_variable f,s)::l) context.extensions []
  ;;

  let get_quantifiers context =
    context.quantifiers
  ;;

  let get_aux_variables context =
    context.aux_variables
  ;;

        let make_quantifiers_levels_inter context =
    let quantifiers = context.quantifiers in
                let rec loop arr quants level =
      match quants with
      [] -> arr
      | q::qs ->
                                arr.(((destroy_variable o get_quant_var) q) - 1) <- level;
                                loop arr qs (level - 1)
    in
    let arr = Array.make (List.length quantifiers) 0 in
    let arr' = loop arr quantifiers (List.length quantifiers) in
    arr'
  ;;

  let make_quantifiers_levels context =
    context.q_levels <- make_quantifiers_levels_inter context
  ;;

        let make_ordered_quantifiers_levels context =
    context.q_ordered_levels <- make_quantifiers_levels_inter context
  ;;

  let lt_levels context v1 v2 =
    context.q_levels.(v1-1) < context.q_levels.(v2-1)
  ;;

        let lt_ordered_levels context v1 v2 =
    context.q_ordered_levels.(v1-1) < context.q_ordered_levels.(v2-1)
  ;;

end;;

 open Qbfcontext;;

let rec strip_quantifiers tm =
  if is_forall tm then
    let (var,tm') = dest_forall tm in
    let (q',body) = (strip_quantifiers tm') in
    ((Universal var)::q',body)
  else if is_exists tm then
    let (var,tm') = dest_exists tm in
    let (q',body) = (strip_quantifiers tm') in
    ((Existential var)::q',body)
  else ([],tm)
;;

(** strip quantifiers in bottom-up ordering *)
let strip_quantifiers_r tm =
  let rec loop tm acc =
    if is_forall tm then
      let (var,tm') = dest_forall tm in
      loop tm' ((Universal var)::acc)
    else if is_exists tm then
      let (var,tm') = dest_exists tm in
      loop tm' ((Existential var)::acc)
    else (acc,tm)
  in loop tm []
;;

(** strip quantifiers in bottom-up ordering *)
let strip_quantifiers_rx tm =
  let rec loop tm acc =
    if is_forall tm then
      let (var,tm') = dest_forall tm in
      loop tm' ((true, var)::acc)
    else if is_exists tm then
      let (var,tm') = dest_exists tm in
      loop tm' ((false, var)::acc)
    else (acc,tm)
  in loop tm []
;;

let quantifiers_fold_left exist_fn universal_fn thm quantifiers =
  let quant_fn thm quantifier =
    match quantifier with
    Universal var -> universal_fn var thm
    | Existential var -> exist_fn var thm
  in
  List.fold_left quant_fn thm quantifiers
;;

let is_negated lit_ind = lit_ind < 0;;

let read_index token_stream =
  let index_token = Stream.next token_stream in
    match index_token with
      Genlex.Int index -> index
      | _ -> failwith "Bad index of variable"
;;

let var = abs;;

let read_extension_ite context new_var_index token_stream =
  let x_v_i = read_index token_stream in
  let y_v_i = read_index token_stream in
  let z_v_i = read_index token_stream in
  check_variable context (var x_v_i);
  check_variable context (var y_v_i);
  check_variable context (var z_v_i);
  let x_v = make_literal x_v_i in
  let y_v = make_literal y_v_i in
  let z_v = make_literal z_v_i in
  let formula = mk_disj (mk_conj (x_v,y_v),mk_conj(mk_neg x_v,z_v)) in
  add_extension context new_var_index formula;
;;

let read_extension_and context new_var_index token_stream =
  let rec read_conjucts context token_stream =
    let lit_ind = read_index token_stream in
    if lit_ind = 0 then []
    else
    begin
      check_variable context (var lit_ind);
      (make_literal lit_ind)::(read_conjucts context token_stream)
    end
  in
  let conjucts = read_conjucts context token_stream in
  let conjucts' = match conjucts with
    [] -> `T`
    | _ -> list_mk_conj conjucts
  in
  add_extension context new_var_index conjucts';
;;

let read_extension_line context token_stream =
  let new_var_index = read_index token_stream in
  let extension_type = Stream.next token_stream in
  match extension_type with
    Genlex.Kwd "I" -> read_extension_ite context new_var_index token_stream
    | Genlex.Kwd "A" -> read_extension_and context new_var_index token_stream
    | _ -> failwith "Unknown type of extension line"
;;

let read_header context token_stream =
  match Stream.next token_stream with
    Genlex.Kwd "QBCertificate" -> ()
    | _ -> failwith "Missing header"
;;

let read_resolution_line context token_stream =
  failwith "Resolution line: not yet implemented!";
()
;;

let rec read_equalities context token_stream =
  try
    let exist_var_i = read_index token_stream in
    check_variable context exist_var_i;
    let extension_var_i = read_index token_stream in
    check_variable context (var extension_var_i);
    let extension_var = make_literal extension_var_i in
    add_conclusion_eq context exist_var_i extension_var;
    read_equalities context token_stream
  with Stream.Failure -> ()
;;

let read_conlude_line context token_stream =
  match Stream.next token_stream with
  Genlex.Kwd "VALID" -> read_equalities context token_stream
  | Genlex.Kwd "INVALID" -> failwith "INVALID formula: not yet implemted!"
  | _ -> failwith "Unknown type of conclusion"
;;

let read_certificate context token_stream =
  read_header context token_stream;
  let rec read_line context token_stream =
    match Stream.next token_stream with
    Genlex.Kwd "E" -> read_extension_line context token_stream; read_line context token_stream
    | Genlex.Kwd "R" -> read_resolution_line context token_stream; read_line context token_stream
    | Genlex.Kwd "CONCLUDE" -> read_conlude_line context token_stream
    | _ -> failwith "Unknown type of line"
  in
  read_line context token_stream
;;

let PROPAGATE_FORALL =
  let MONO_FORALL_B = (UNDISCH o prove)
   (`(!x:bool. A x ==> B x) ==> (!) A ==> (!) B`,
    STRIP_TAC THEN
    GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    ASM_MESON_TAC[]) in
  let a_tm = rand(lhand(concl MONO_FORALL_B))
  and b_tm = rand(rand(concl MONO_FORALL_B))
  and h_tm = hd(hyp MONO_FORALL_B) in
  fun v1 ->
     let ath = GEN_ALPHA_CONV v1 h_tm in
     let atm = rand(concl ath) in
     let pth = PROVE_HYP (EQ_MP (SYM ath) (ASSUME atm)) MONO_FORALL_B in
     fun thm ->
       let tm = concl thm in
       let ip,q = dest_comb tm in
       let i,p = dest_comb ip in
       let pabs = mk_abs(v1,p)
       and qabs = mk_abs(v1,q) in
       let th1 = AP_TERM i (BETA(mk_comb(pabs,v1))) in
       let th2 = MK_COMB(th1,BETA(mk_comb(qabs,v1))) in
       let th3 = GEN v1 (EQ_MP (SYM th2) thm) in
       let th4 = INST [pabs,a_tm; qabs,b_tm] pth in
       PROVE_HYP th3 th4;;

let PROPAGATE_RIGHT =
  let MONO_EXISTS_RIGHT_B = (UNDISCH o prove)
   (`(A ==> B(x:bool)) ==> A ==> (?) B`,
    ASM_CASES_TAC `A:bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    MESON_TAC[]) in
  let a_tm = lhand(concl MONO_EXISTS_RIGHT_B)
  and b_tm = rand(rand(concl MONO_EXISTS_RIGHT_B))
  and h_tm = hd(hyp MONO_EXISTS_RIGHT_B) in
  let x_tm = rand(rand h_tm) in
  fun v thm ->
    let tm = concl thm in
    let ip,q = dest_comb tm in
    let qabs = mk_abs(v,q) in
    let th1 = AP_TERM ip (BETA(mk_comb(qabs,v))) in
    let th2 = EQ_MP (SYM th1) thm in
    let th3 = INST [rand ip,a_tm; qabs,b_tm; v,x_tm] MONO_EXISTS_RIGHT_B in
    PROVE_HYP th2 th3;;

let PROPAGATE_LEFT =
  let MONO_EXISTS_LEFT_B = (UNDISCH o prove)
   (`(!x:bool. A x ==> B) ==> (?) A ==> B`,
    ASM_CASES_TAC `B:bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM ETA_AX] THEN
    MESON_TAC[]) in
  let a_tm = rand(lhand(concl MONO_EXISTS_LEFT_B))
  and b_tm = rand(concl MONO_EXISTS_LEFT_B)
  and h_tm = hd(hyp MONO_EXISTS_LEFT_B) in
  fun v ->
     let ath = GEN_ALPHA_CONV v h_tm in
     let atm = rand(concl ath) in
     let pth = PROVE_HYP (EQ_MP (SYM ath) (ASSUME atm)) MONO_EXISTS_LEFT_B in
     fun thm ->
       let tm = concl thm in
       let ip,q = dest_comb tm in
       let i,p = dest_comb ip in
       let pabs = mk_abs(v,p) in
       let th1 = AP_THM (AP_TERM i (BETA(mk_comb(pabs,v)))) q in
       let th2 = GEN v (EQ_MP (SYM th1) thm) in
       let th3 = INST [pabs,a_tm; q,b_tm] pth in
       PROVE_HYP th2 th3;;

let PROPAGATE_QUANTIFIERS_R thm ext_quants quants =
        let rec propagate_both thm ext_quants quants =
                match (ext_quants,quants) with
                        | ((Universal v1)::ext_quantss,(Universal v2)::quantss) ->
                                propagate_both (PROPAGATE_FORALL v1 thm) ext_quantss quantss
                        | (_,_) -> (thm,ext_quants,quants)
        in
        let rec propagate_right thm quants =
                match quants with
                        | (Existential v)::quantss ->
                                propagate_right (PROPAGATE_RIGHT v thm) quantss
                        | _ -> (thm,quants)
        in
        let rec propagate_left thm ext_quants =
                match ext_quants with
                        | (Existential v)::ext_quantss ->
                                propagate_left (PROPAGATE_LEFT v thm) ext_quantss
                        | _ -> (thm,ext_quants)
        in
        let rec propagate thm ext_quants quants =
                match (ext_quants,quants) with
                        | ([],[]) -> thm
                        | (_,((Existential _)::_)) ->
                                let (thm',quants') = propagate_right thm quants in
                                let (thm'',ext_quants') = propagate_left thm' ext_quants in
                                propagate thm'' ext_quants' quants'
                        | (((Existential _)::_),_) ->
                                let (thm',ext_quants') = propagate_left thm ext_quants in
                                propagate thm' ext_quants' quants
                        | ((Universal _)::_,(Universal _)::_) ->
                                let (thm',ext_quants',quants') = propagate_both thm ext_quants quants in
                                propagate thm' ext_quants' quants'
                        | _ -> failwith "PROPAGATE_QUANTIFIERS_R: logic error"
        in
        propagate thm ext_quants quants
;;

let order_quantifiers context =
        let add_var vertices graph var_index =
                Gr.add_vertex graph (make_vertex var_index);
                let extension_vars = variables (get_extension context var_index) in
                let add_ext_var ext_var =
                        let ext_var_index = destroy_variable ext_var in
                        if Hashtbl.mem vertices ext_var_index then
                                Gr.add_edge graph (make_vertex ext_var_index) (make_vertex var_index)
                in
                List.iter add_ext_var extension_vars
        in
        let rec is_sorted var_index_list =
                let is_sorted_var var_index =
                        let extension_vars = variables (get_extension context var_index) in
                        List.fold_left (fun ret var -> ret && lt_levels context (destroy_variable var) var_index) true extension_vars
                in
                match var_index_list with
                [] -> true
                | var::vars -> if is_sorted_var var then is_sorted vars
                                                                         else false
        in
        (** exists is in up-bottom ordering *)
        let rec order_exists quantifiers exists =
                let order_exists' tail =
                        if is_sorted exists then
                                List.fold_left (fun tail var_index -> (Existential (make_variable var_index))::tail) tail exists
                        else
                                let graph = Gr.create () in
                                let vertices = Hashtbl.create (List.length exists) in
                                List.iter (fun var -> Hashtbl.add vertices var ()) exists;
                                List.iter (fun var -> add_var vertices graph var) exists;
                                Topo.fold (fun vertex tail -> (Existential (make_variable (dest_vertex vertex)))::tail) graph tail
                in
                match quantifiers with
                [] -> order_exists' []
                | (Universal v)::qs -> order_exists' ((Universal v)::order qs)
                | (Existential v)::qs ->
                        order_exists qs ((destroy_variable v)::exists)
        and
        order quantifiers =
                match quantifiers with
                [] -> []
                | (Universal v)::qs -> (Universal v)::order qs
                | (Existential v)::qs ->
                        order_exists ((Existential v)::qs) []
        in
        set_quantifiers context (order (get_quantifiers context));
        make_ordered_quantifiers_levels context
;;

let match_time = ref 0.0;;
let lift_time = ref 0.0;;
let gen_time = ref 0.0;;
let test_time = ref 0.0;;


let timex label f x =
  if not (!show_timing) then f x else
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      report("CPU time (user): "^(string_of_float(finish_time -. start_time))^" ("^label^")");
      result
  with e ->
      let finish_time = Sys.time() in
      Format.print_string("Failed after (user) CPU time of "^
                          (string_of_float(finish_time -. start_time))^" ("^label^")"^": ");
      raise e;;

let my_time f x time_var =
  if not (!show_timing) then f x else
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      time_var := !time_var +. (finish_time -. start_time);
      result
  with e ->
      let finish_time = Sys.time() in
      time_var := !time_var +. (finish_time -. start_time);
      raise e;;

let report_time label time_var =
        if !show_timing then
                report("CPU time (user): "^(string_of_float(!time_var))^" ("^label^")");
;;

let FORALL_SIMP2 = prove
 (`t = (!x:bool. t)`,
  ITAUT_TAC);;

let ADD_MISSING_UNIVERSALS th quants =
        let rec add_u quants tm =
                match quants with
                        | [] -> REFL tm
                        | q::qs ->
                                match q with
                                        | Existential _ -> BINDER_CONV (add_u qs) tm
                                        | Universal v ->
                                                if Pervasives.(||) (not (has_quant tm)) (Pervasives.compare ((fst o dest_quant) tm) v != 0) then
                                                        let renamed_rewr = EQ_MP (ONCE_DEPTH_CONV (ALPHA_CONV v) (concl FORALL_SIMP2)) FORALL_SIMP2 in
                                                        (PURE_ONCE_REWRITE_CONV [renamed_rewr] THENC BINDER_CONV (add_u qs)) tm
                                                else
                                                        BINDER_CONV (add_u qs) tm
        in
        EQ_MP (add_u (rev quants) (concl th)) th
;;

let AX_UXU = (UNDISCH o prove)
 (`(!x:bool. p x /\ q ==> r x) ==> (!) p /\ q ==> (!) r`,
  let AX_UXU = MESON [] `(!x:bool. ((A x /\ B)==>C x))==>(((!x:bool. A x) /\ B)==> !x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_UXU) THEN REWRITE_TAC[ETA_AX])
and AX_EXE = (UNDISCH o prove)
 (`(!x:bool. p x /\ q ==> r x) ==> (?) p /\ q ==> (?) r`,
  let AX_EXE = MESON [] `(!x:bool. ((A x /\ B)==>C x))==>(((?x:bool. A x) /\ B)==> ?x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_EXE) THEN REWRITE_TAC[ETA_AX]);;

let LIFT_LEFT ax =
  let p_tm = rand(lhand(lhand(concl ax)))
  and q_tm = rand(lhand(concl ax))
  and r_tm = rand(rand(concl ax))
  and h_tm = hd(hyp ax) in
  fun var ->
    let ath = GEN_ALPHA_CONV var h_tm in
    let atm = rand(concl ath) in
    let ax' = PROVE_HYP (EQ_MP (SYM ath) (ASSUME atm)) ax in
    fun th ->
      let tm = concl th in
      let ipq,r = dest_comb tm in
      let i,pq = dest_comb ipq in
      let ap,q = dest_comb pq in
      let a,p = dest_comb ap in
      let pabs = mk_abs(var,p)
      and rabs = mk_abs(var,r) in
      let th1 = AP_THM (AP_TERM a (BETA(mk_comb(pabs,var)))) q in
      let th2 = MK_COMB(AP_TERM i th1,BETA(mk_comb(rabs,var))) in
      let th3 = GEN var (EQ_MP (SYM th2) th) in
      let th4 = INST [pabs,p_tm; q,q_tm; rabs,r_tm] ax' in
      PROVE_HYP th3 th4;;

let AX_XUU = (UNDISCH o prove)
 (`(!x:bool. p /\ q x ==> r x) ==> p /\ (!) q ==> (!) r`,
  let AX_XUU = MESON [] `(!x:bool. ((A /\ B x)==>C x))==>((A /\ !x:bool. B x)==> !x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_XUU) THEN REWRITE_TAC[ETA_AX])
and AX_XEE = (UNDISCH o prove)
 (`(!x:bool. p /\ q x ==> r x) ==> p /\ (?) q ==> (?) r`,
  let AX_XEE = MESON [] `(!x:bool. ((A /\ B x)==>C x))==>((A /\ ?x:bool. B x)==> ?x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_XEE) THEN REWRITE_TAC[ETA_AX]);;

let LIFT_RIGHT ax =
  let p_tm = lhand(lhand(concl ax))
  and q_tm = rand(rand(lhand(concl ax)))
  and r_tm = rand(rand(concl ax))
  and h_tm = hd(hyp ax) in
  fun var ->
    let ath = GEN_ALPHA_CONV var h_tm in
    let atm = rand(concl ath) in
    let ax' = PROVE_HYP (EQ_MP (SYM ath) (ASSUME atm)) ax in
    fun th ->
      let tm = concl th in
      let ipq,r = dest_comb tm in
      let i,pq = dest_comb ipq in
      let ap,q = dest_comb pq in
      let a,p = dest_comb ap in
      let qabs = mk_abs(var,q)
      and rabs = mk_abs(var,r) in
      let th1 = AP_TERM ap (BETA(mk_comb(qabs,var))) in
      let th2 = MK_COMB(AP_TERM i th1,BETA(mk_comb(rabs,var))) in
      let th3 = GEN var (EQ_MP (SYM th2) th) in
      let th4 = INST [p,p_tm; qabs,q_tm; rabs,r_tm] ax' in
      PROVE_HYP th3 th4;;

let AX_UUU = (UNDISCH o prove)
 (`(!x:bool. p x /\ q x ==> r x) ==> (!) p /\ (!) q ==> (!) r`,
  let AX_UUU = MESON [] `(!x:bool. ((A x /\ B x)==>C x))==>(((!x:bool. A x) /\ !x:bool. B x)==> !x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_UUU) THEN REWRITE_TAC[ETA_AX])
and AX_EUE = (UNDISCH o prove)
 (`(!x:bool. p x /\ q x ==> r x) ==> (?) p /\ (!) q ==> (?) r`,
  let AX_EUE = MESON [] `(!x:bool. ((A x /\ B x)==>C x))==>(((?x:bool. A x) /\ !x:bool. B x)==> ?x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_EUE) THEN REWRITE_TAC[ETA_AX])
and AX_UEE = (UNDISCH o prove)
 (`(!x:bool. p x /\ q x ==> r x) ==> (!) p /\ (?) q ==> (?) r`,
  let AX_UEE = MESON [] `(!x:bool. ((A x /\ B x)==>C x))==>(((!x:bool. A x) /\ ?x:bool. B x)==> ?x:bool. C x)` in
  DISCH_THEN(MP_TAC o MATCH_MP AX_UEE) THEN REWRITE_TAC[ETA_AX]);;

let LIFT_BOTH ax =
  let p_tm = rand(lhand(lhand(concl ax)))
  and q_tm = rand(rand(lhand(concl ax)))
  and r_tm = rand(rand(concl ax))
  and h_tm = hd(hyp ax) in
  fun var ->
    let ath = GEN_ALPHA_CONV var h_tm in
    let atm = rand(concl ath) in
    let ax' = PROVE_HYP (EQ_MP (SYM ath) (ASSUME atm)) ax in
    fun th ->
      let tm = concl th in
      let ipq,r = dest_comb tm in
      let i,pq = dest_comb ipq in
      let ap,q = dest_comb pq in
      let a,p = dest_comb ap in
      let pabs = mk_abs(var,p)
      and qabs = mk_abs(var,q)
      and rabs = mk_abs(var,r) in
      let th0 = AP_TERM a (BETA(mk_comb(pabs,var))) in
      let th1 = MK_COMB(th0,BETA(mk_comb(qabs,var))) in
      let th2 = MK_COMB(AP_TERM i th1,BETA(mk_comb(rabs,var))) in
      let th3 = GEN var (EQ_MP (SYM th2) th) in
      let th4 = INST [pabs,p_tm; qabs,q_tm; rabs,r_tm] ax' in
      PROVE_HYP th3 th4;;

let solve_quantifiers context conjuction =
        let solve_right_quantifier thm quant2 =
                match quant2 with
                        | Universal v2 -> LIFT_RIGHT AX_XUU v2 thm
                        | Existential v2 -> LIFT_RIGHT AX_XEE v2 thm
        in
        let solve_left_quantifier thm quant1 =
                match quant1 with
                        | Universal v1 -> LIFT_LEFT AX_UXU v1 thm
                        | Existential v1 -> LIFT_LEFT AX_EXE v1 thm
        in
        let solve_both_quantifiers thm quant1 quant2 =
    match (quant1,quant2) with
            (Universal v1, Universal v2) -> LIFT_BOTH AX_UUU v1 thm
            | (Existential v1, Universal v2) -> LIFT_BOTH AX_EUE v1 thm
            | (Universal v1, Existential v2) -> LIFT_BOTH AX_UEE v1 thm
            | _ -> failwith "Logic error in solve_quantifier"
  in
        let rec loop thm quants1 quants2 =
                match (quants1,quants2) with
                        | ([],[]) -> thm
                        | (qs1,[]) -> List.fold_left solve_left_quantifier thm qs1
                        | ([],qs2) -> List.fold_left solve_right_quantifier thm qs2
                        | (quant1::qs1,quant2::qs2) ->
                                let quant_var1 = get_quant_var quant1 in
                                let quant_var2 = get_quant_var quant2 in
                                if quant_var1 = quant_var2 then
                                        let thm' = solve_both_quantifiers thm quant1 quant2 in
                                        loop thm' qs1 qs2
                                else
                                        if lt_ordered_levels context (destroy_variable quant_var1) (destroy_variable quant_var2) then
                                                let thm' = solve_right_quantifier thm quant2 in
                                                loop thm' (quant1::qs1) qs2
                                        else
                                                let thm' = solve_left_quantifier thm quant1 in
                                                loop thm' qs1 (quant2::qs2)
        in
        let conclusion = concl conjuction in
  let (conj1,conj2) = dest_conj conclusion in
  let (quants1,body1) = strip_quantifiers_r conj1 in
  let (quants2,body2) = strip_quantifiers_r conj2 in

  let rew_thm = loop (DISCH_ALL (ASSUME (mk_conj (body1,body2)))) quants1 quants2 in
        (*print_thm rew_thm;
        print_newline ();
        print_thm conjuction;
        print_newline ();*)
  my_time (MP rew_thm) conjuction match_time
;;

let make_quantified_model_equality =
  let pth = MESON[] `?x:bool. x = t` in
  let t_tm = rand(body(rand(concl pth))) in
  fun quantifier_data (exist_var,right_side) ->
    let free_vars = frees right_side in
    let n = quantifier_data exist_var in
    let quants =  sort (decreasing quantifier_data)
                       (filter (fun v -> quantifier_data v > n) free_vars) in
    let exist_eq_thm = INST[right_side,t_tm] (CONV_RULE(GEN_ALPHA_CONV exist_var) pth) in
    let ret = GENL quants exist_eq_thm in
          (* print_thm ret;
          print_endline ""; *)
          ret
;;

let construct_model context equalities =
  match equalities with
  [] -> `T`
  | (eq::eqs) -> List.fold_left (C (curry mk_conj)) eq eqs
;;

let construct_model_thm context equalities =
  let eq_length = List.length equalities in
  let progress = ref 1 in
  let print_progress () =
          print_endline ((string_of_int o int_of_float) (((float_of_int !progress)/.(float_of_int eq_length))*.100.0))
  in
  let construct model eq =

          let ret = solve_quantifiers context (CONJ eq model) in

          if !show_progress then
          begin
                  progress := !progress + 1;
                  print_progress ();
          end;
          ret
  in
  let rec construct_recursively eqs =
    match eqs with
      [] -> failwith "Sanity check failure"
    | [e] -> e
    | [e1;e2] -> construct e1 e2
    | _ -> let n = length eqs in
           let eqs1,eqs2 = chop_list (length eqs / 2) eqs in
           construct (construct_recursively eqs1) (construct_recursively eqs2)
  in
  if equalities = [] then quantifiers_fold_left SIMPLE_EXISTS GEN TRUTH (get_quantifiers context)
  else PURE_REWRITE_RULE[GSYM CONJ_ASSOC] (construct_recursively equalities);;

let make_model context =
  let model_equalities = get_extensions context in
        let model = construct_model context (List.map mk_eq model_equalities) in
        let quantifier_list = map (function Universal v -> v | Existential v -> v)
                                  (get_quantifiers context) in
        let quantifier_table = itlist2 (|->) quantifier_list (1--length quantifier_list) undefined in
        let quantifier_data = apply quantifier_table in
        let quantified_equalities = timex "make_quantified_equalities" (List.map (make_quantified_model_equality quantifier_data)) model_equalities in
  let model_thm =
                match_time := 0.0;
                lift_time := 0.0;
                gen_time := 0.0;
                test_time := 0.0;
                print_endline ("Number of extensions: "^ (string_of_int (List.length model_equalities)));
                let ret = timex "construct_model_thm" (construct_model_thm context) quantified_equalities in
                report_time "lift" lift_time;
                report_time "match" match_time;
                report_time "gen" gen_time;
                report_time "test" test_time;
                ret
        in
  (*let model_thm = construct_model_thm context (List.map (make_quantified_model_equality context) model_equalities) in*)
        (model, model_thm)
;;

let check_and_preprocess context formula =
  match frees formula with
  [ _ ] -> failwith "Formula has free variables"
  | _ ->
    let nnf_thm = NNF_CONV formula in
    let prenex_thm = TRANS nnf_thm (PRENEX_CONV (rhs (concl nnf_thm))) in
    let cnf_thm = TRANS prenex_thm (CNF_CONV (rhs (concl prenex_thm))) in

    let rec check_and_made_rename formula index rename =
      let rename_quantifier constr destr add_fresh_variable =
        let (var,destr_formula) = destr formula in
        if type_of var <> bool_ty then failwith ((string_of_term var)^" is not of bool type");
        add_fresh_variable context index;
        let formula2 = check_and_made_rename destr_formula (index+1) ((make_variable index,var)::rename) in
        constr (make_variable index,formula2)
      in
      if is_forall formula then rename_quantifier mk_forall dest_forall add_universal_variable
      else if is_exists formula then rename_quantifier mk_exists dest_exists add_existential_variable
      else
        vsubst rename formula
    in
    let prenex_formula = rhs (concl cnf_thm) in
    let ret = TRANS cnf_thm (ALPHA prenex_formula (check_and_made_rename prenex_formula 1 [])) in
    let (quantifiers',_) = strip_quantifiers_r (rhs (concl ret)) in
    set_quantifiers context quantifiers';
    ret
;;

let get_temp_file () =
  Filename.open_temp_file "qbf" ""
;;

let split_disjuncts body =
 List.fold_right
  (fun c d ->  (disjuncts c) :: d)
  (conjuncts body) []
;;

let string_of_literal lit =
  string_of_int (destroy_literal lit);
;;

type prefix = Exists of term list | Forall of term list;;

let rec strip_quantifiers_as_prefix formula =
  if is_forall formula then
    let (quants,formula') = strip_forall formula in
    let (quants',body) = strip_quantifiers_as_prefix formula' in
    ((Forall quants)::quants',body)
  else if is_exists formula then
    let (quants,formula') = strip_exists formula in
    let (quants',body) = strip_quantifiers_as_prefix formula' in
    ((Exists quants)::quants',body)
  else
    ([],formula)
;;

let make_input context formula var_count =
  let (file_name,file_stream) = get_temp_file () in
  try
    let (quantifiers_list, body) = strip_quantifiers_as_prefix formula in
    let clause_count = length(conjuncts body) in


    let disjuncts_list = split_disjuncts body in

    let out s = output_string file_stream s in
    let formula_string = Str.global_replace (Str.regexp_string "\n") "\nc " (string_of_term formula) in
    out "c "; out formula_string;out "\n";
    out "c\n";
    out "p cnf ";
    out (string_of_int var_count); out " ";
    out (string_of_int clause_count); out "\n";

    let print_quantifiers q =
      let print_vars q =
        List.iter (fun var -> (out(string_of_literal var); out " ")) q;
        out "0\n"
      in
      match q with
      Exists vars -> out "e "; print_vars vars
      | Forall vars -> out "a "; print_vars vars
    in

    List.iter
      (fun q ->  print_quantifiers q)
      quantifiers_list;

    List.iter
      (fun l -> (List.iter (fun lit ->
        (out(string_of_literal lit); out " ")) l;
                  out "0\n"))
      disjuncts_list;
    close_out file_stream;
    file_name
  with x ->
    close_out file_stream;
    raise x
;;

let execute_squolem input_file_name =
  let exec_name = "squolem2 -c " ^ input_file_name in
  let _ = Sys.command exec_name in
  input_file_name ^ ".qbc"
;;

let parse_certificate context certificate_file_name =
  let file_channel = Pervasives.open_in certificate_file_name in
  let token_stream = (Genlex.make_lexer ["I";"A";"QBCertificate";"VALID";"INVALID";"E";"R";"CONCLUDE"] (Stream.of_channel file_channel)) in
  read_certificate context token_stream

let print_model context =
  let (model, model_thm) = make_model context in
  print_endline (string_of_term model);
  print_endline (string_of_thm model_thm)
;;

let print_quantifiers context =
        let print_quantifier quant =
                match quant with
                        Existential v -> print_string "E "; print_term v; print_string " "
                        | Universal v -> print_string "F "; print_term v; print_string " "
        in
        List.iter print_quantifier (get_quantifiers context);
        print_newline ()
;;

let ZSAT_PROVE' =
  let ASSOC_EQ_CONV th =
    let assoc_canon = ASSOC_CONV th in
    fun tm -> let l,r = dest_eq tm in
              TRANS (assoc_canon l) (SYM(assoc_canon r)) in
  let opacs = [`\/`,ASSOC_EQ_CONV DISJ_ASSOC;
               `/\`,ASSOC_EQ_CONV CONJ_ASSOC;
               `<=>`,ASSOC_EQ_CONV(TAUT `(t1 <=> t2 <=> t3) <=> ((t1 <=> t2) <=> t3)`)] in
  let rec ASSOC_BALANCE_CONV tm =
    match tm with
      Comb(Comb(op,l),r) when can (assoc op) opacs ->
        let tms = striplist (dest_binop op) tm in
        let n = length tms in
        if n <= 1 then failwith "sanity check failure" else
        if n = 2 then BINOP_CONV ASSOC_BALANCE_CONV tm else
        let tms1,tms2 = chop_list (n / 2) tms in
        let tm1 = list_mk_binop op tms1
        and tm2 = list_mk_binop op tms2 in
        let th = assoc op opacs (mk_eq(tm,mk_binop op tm1 tm2)) in
        CONV_RULE (RAND_CONV (BINOP_CONV ASSOC_BALANCE_CONV)) th
    | _ -> REFL tm in
  let conv = DEPTH_BINOP_CONV `(/\)` (NNFC_CONV THENC CNF_CONV) in
  fun tm -> let th = COMB2_CONV (RAND_CONV conv) ASSOC_BALANCE_CONV tm in
            let tm' = rand(concl th) in
            EQ_MP (SYM th) (ZSAT_PROVE tm');;

let build_proof context prenex_thm =
  let formula = rhs (concl prenex_thm) in
  let (quants,formula_body) = strip_quantifiers_r formula in
  timex "make_q_levels" make_quantifiers_levels context;
        (*print_quantifiers context;*)
        timex "order_qs" order_quantifiers context;
        (*print_quantifiers context;*)
  let (model, model_thm) = timex "make_model" make_model context in
  let sat_formula = mk_imp (model,formula_body) in
  let proved_sat_formula = timex "sat" ZSAT_PROVE' sat_formula in
  let q_propagated_formula = timex "propagate" (PROPAGATE_QUANTIFIERS_R proved_sat_formula (get_quantifiers context)) quants in
  let (model_quantifiers,_) = strip_quantifiers_r (concl model_thm) in
        let proved_formula =
                if List.length model_quantifiers != List.length (get_quantifiers context) then
                        MP q_propagated_formula (timex "add_missing" (ADD_MISSING_UNIVERSALS model_thm) (get_quantifiers context))
                else
                        (*MP q_propagated_formula model_thm*)
                        MP q_propagated_formula (timex "add_missing" (ADD_MISSING_UNIVERSALS model_thm) (get_quantifiers context))
        in
  EQ_MP (GSYM prenex_thm) proved_formula
;;

let prove_qbf formula =
  let var_count = length (variables formula) in
  let context = create_context var_count in
  let prenex_thm = timex "prep" (check_and_preprocess context) formula in
  let input_file_name = timex "make_input" (make_input context (rand (concl prenex_thm))) var_count in
  let output_file_name = timex "ex_squolem" execute_squolem input_file_name in
  let _ = timex "parse_cert" (parse_certificate context) output_file_name in
  let thm = timex "build_proof" (build_proof context) prenex_thm in
  (if !delete_qbf_tempfiles
   then (Sys.remove input_file_name; Sys.remove output_file_name)
   else ());
 thm
;;

let prove_all_qbf dir =
        let filter_array f a =
                let l = Array.to_list a in
                let ll = List.filter f l in
                Array.of_list ll
        in
  let raw_files = Sys.readdir dir in
        let files = filter_array (fun name -> Filename.check_suffix name ".qdimacs") raw_files in
  let run_prover file_name =
    let name = Filename.chop_suffix file_name ".qdimacs" in
    print_endline name;
    let formula = readQDimacs (dir^"/"^file_name) in
    let formula_thm = prove_qbf formula in
    (name,formula_thm)
  in
  Array.map run_prover files
;;
