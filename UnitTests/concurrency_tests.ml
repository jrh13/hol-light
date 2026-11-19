(* ========================================================================= *)
(*                 HOL LIGHT unit tests: several OCaml 5 domains             *)
(*                                                                           *)
(* Domains of one process prove theorems, evaluate, print, make fresh        *)
(* variables and make definitions, types and axioms at the same time; the    *)
(* results must be those of one domain. Built on OCaml 5 only (see the       *)
(* Makefile). The number of domains is HOL_TEST_DOMAINS, by default 4.       *)
(* ========================================================================= *)

let failures = ref [];;
let failures_lock = Mutex.create ();;

let fail_test msg =
  Mutex.lock failures_lock;
  failures := msg :: !failures;
  Mutex.unlock failures_lock;;

let check name cond = if not cond then fail_test name;;

let ndomains =
  try max 2 (int_of_string (Sys.getenv "HOL_TEST_DOMAINS"))
  with _ -> 4;;

(* Run f d on domains d = 0, ..., ndomains-1 at once, and return the         *)
(* results; an exception on a domain is recorded as a failure.               *)

let on_all_domains name (f:int->'a) : 'a option list =
  let run d () =
    (* A large minor heap: every minor collection stops all domains *)
    Gc.set { (Gc.get ()) with Gc.minor_heap_size = 4 * 1024 * 1024 };
    try Some (f d) with e ->
      fail_test (Printf.sprintf "%s: domain %d: %s" name d
                   (Printexc.to_string e));
      None in
  List.map Domain.join (List.init ndomains (fun d -> Domain.spawn (run d)));;

(* ------------------------------------------------------------------------- *)
(* Proofs, printing and fresh variables.                                     *)
(* ------------------------------------------------------------------------- *)

let meson_goal = `!x y z. x <= y /\ y <= z ==> x <= z + 0`;;
let fol_goal =
  `(!x:A. P x ==> Q x) /\ (!x. Q x ==> R x) ==> (!x. P x ==> R x)`;;
let arith_goal = `!a b. (a + b) * (a + b) = a * a + 2 * a * b + b * b`;;
let rewrite_tm = `(x:num) + 0 + y * 1`;;
let printed_tm = `!n. n + SUC m = SUC (n + m)`;;
let printed = string_of_term printed_tm;;

(* The CoP provers clear and refill their clause tables on every call, so    *)
(* the domains give them different goals.                                    *)

let cop_goals =
  [| fol_goal,[];
     `!x y z. x <= y /\ y <= z ==> x <= z`,[LE_TRANS];
     `(!x:B. f (f x) = x) ==> !y. ?x. f x = y`,[] |];;

let rounds = 15;;

let prove_and_print d =
  let names = ref [] in
  let cop_goal,cop_ths = cop_goals.(d mod Array.length cop_goals) in
  for i = 1 to rounds do
    let th1 = prove(meson_goal, MESON_TAC[LE_TRANS; ADD_CLAUSES]) in
    check "MESON result" (concl th1 = meson_goal);
    let th2 = prove(fol_goal, MESON_TAC[]) in
    check "first-order MESON result" (concl th2 = fol_goal);
    let th3 = ARITH_RULE arith_goal in
    check "ARITH_RULE result" (concl th3 = arith_goal);
    let th4 = REWRITE_CONV[ADD_CLAUSES; MULT_CLAUSES] rewrite_tm in
    check "REWRITE_CONV result" (rhs(concl th4) = `x + y`);
    let th5 = prove(fol_goal, METIS_TAC[]) in
    check "METIS result" (concl th5 = fol_goal);
    let th6 = prove(cop_goal, LEANCOP_TAC cop_ths) in
    check "LEANCOP result" (concl th6 = cop_goal);
    let th7 = prove(cop_goal, NANOCOP_TAC cop_ths) in
    check "NANOCOP result" (concl th7 = cop_goal);
    check "parsed term" (`!n. n + SUC m = SUC (n + m)` = printed_tm);
    check "string_of_term" (string_of_term printed_tm = printed);
    names := fst(dest_var(genvar `:num`)) :: !names
  done;
  !names;;

let genvar_names = on_all_domains "proofs" prove_and_print;;

let () =
  let all = List.concat (List.map (function Some l -> l | None -> [])
                                  genvar_names) in
  check "genvar: a name was given twice"
    (List.length (setify all) = List.length all);
  check "METIS changed type_invention_warning" !type_invention_warning;;

(* Simplification with conversions that the main domain makes and the        *)
(* others use first: their simpsets hold facts that are found on first use.  *)

let shared_convs =
  let fillers = map (fun i -> ASSUME(mk_eq(mk_var("x"^string_of_int i,`:num`),
                                           `0`))) (1--100) in
  Array.init 100 (fun _ ->
    SIMP_CONV (fillers @ [LT_TRANS; ASSUME `a < b`; ASSUME `b < c`]));;

let _ = on_all_domains "shared simpsets" (fun d ->
  Array.iter
    (fun cv -> check "SIMP_CONV result" (rand(concl(cv `a < c`)) = `T`))
    shared_convs);;

(* ------------------------------------------------------------------------- *)
(* Evaluation: RESTR_EVAL_CONV on domain 0 must not restrict EVAL_CONV on    *)
(* the other domains.                                                        *)
(* ------------------------------------------------------------------------- *)

let eval_tm = `(T /\ T) \/ F`;;
let restricted_tm = `T /\ T`;;
let neval = 1000;;

let eval_const d i =
  mk_const(Printf.sprintf "concurrency_test_eval_%d_%d" d i,[]);;

let () =
  for d = 0 to ndomains - 1 do
    for i = 1 to neval do
      new_constant(Printf.sprintf "concurrency_test_eval_%d_%d" d i,bool_ty)
    done
  done;
  let size () = List.length (Compute.listItems Compute.the_compset) in
  let before = size () in
  ignore(Compute.EVAL_CONV (mk_conj(eval_const 0 1,`T`)));
  check "EVAL_CONV added an entry to the compset" (size () = before);;

(* Evaluation still uses rules for a constant that were added after the      *)
(* rules that mention it.                                                    *)

let () =
  let g = new_definition `concurrency_test_g x = ~x` in
  let f = new_definition `concurrency_test_f x = concurrency_test_g x` in
  let cs = Compute.bool_compset () in
  Compute.add_thms [f] cs;
  Compute.add_thms [g] cs;
  check "CBV_CONV: rules added later are not used"
    (rhs(concl(Compute.CBV_CONV cs `concurrency_test_f T`)) = `F`);;

let _ = on_all_domains "evaluation" (fun d ->
  for i = 1 to 2000 do
    if d = 0 then
      check "RESTR_EVAL_CONV result"
        (rhs(concl(Compute.RESTR_EVAL_CONV [`(/\)`] eval_tm)) = restricted_tm)
    else
      check "EVAL_CONV result: restricted by another domain"
        (rhs(concl(Compute.EVAL_CONV eval_tm)) = `T`)
  done;
  for i = 1 to neval do
    let c = eval_const d i in
    check "EVAL_CONV result on a new constant"
      (rhs(concl(Compute.EVAL_CONV (mk_conj(c,`T`)))) = c)
  done);;

(* ------------------------------------------------------------------------- *)
(* Definitions from several domains.                                         *)
(* ------------------------------------------------------------------------- *)

let ndefs = 25;;

let count_constant c =
  List.length (List.filter (fun (s,_) -> s = c) (constants()));;

let defs_before = List.length (definitions());;

let _ = on_all_domains "definitions" (fun d ->
  for i = 1 to ndefs do
    let c = Printf.sprintf "concurrency_test_%d_%d" d i in
    let tm = mk_eq(mk_var(c,`:num`),mk_small_numeral i) in
    ignore(new_definition tm)
  done);;

let () =
  for d = 0 to ndomains - 1 do
    for i = 1 to ndefs do
      let c = Printf.sprintf "concurrency_test_%d_%d" d i in
      check ("constant missing or twice: "^c) (count_constant c = 1)
    done
  done;
  check "definitions(): an update was lost"
    (List.length (definitions()) = defs_before + ndomains * ndefs);;

(* Benign redefinitions: each domain makes again the definitions of the      *)
(* next one, now that the constants exist; all must be accepted as benign,   *)
(* with the theorems of the first time, which needs that no domain lost an   *)
(* entry of the table that new_definition keeps.                             *)

let firsts = Array.init ndomains (fun d -> Array.init ndefs (fun i ->
  let c = Printf.sprintf "concurrency_test_%d_%d" d (i + 1) in
  try concl(SPEC_ALL(assoc c (map (fun th -> fst(dest_const(lhs(concl th))),th)
                                   (definitions()))))
  with Failure _ -> (fail_test ("definitions(): no definition of "^c); `T`)));;

let _ = on_all_domains "benign redefinitions" (fun d ->
  let d' = (d + 1) mod ndomains in
  for i = 1 to ndefs do
    let c = Printf.sprintf "concurrency_test_%d_%d" d' i in
    let th = new_definition (mk_eq(mk_const(c,[]),mk_small_numeral i)) in
    check "benign redefinition: a different theorem"
      (concl th = firsts.(d').(i - 1))
  done);;

let () =
  for d = 0 to ndomains - 1 do
    for i = 1 to ndefs do
      let c = Printf.sprintf "concurrency_test_%d_%d" d i in
      check ("constant defined twice: "^c) (count_constant c = 1)
    done
  done;;

(* Different definitions of one name: one is made, the others rejected.      *)

let conflict_wins = Atomic.make 0;;

let _ = on_all_domains "conflicting definitions" (fun d ->
  let tm = mk_eq(`concurrency_test_conflict:num`,mk_small_numeral d) in
  try ignore(new_definition tm); Atomic.incr conflict_wins
  with Failure _ -> ());;

let () =
  check "conflicting definitions: not exactly one made"
    (Atomic.get conflict_wins = 1);
  check "conflicting definitions: constant missing or twice"
    (count_constant "concurrency_test_conflict" = 1);;

(* ------------------------------------------------------------------------- *)
(* Inductive types, type definitions, recursive functions and inductive      *)
(* relations from several domains, each made twice: the second time must be  *)
(* a benign redefinition.                                                    *)
(* ------------------------------------------------------------------------- *)

let ntypes = 3;;

let count_type t =
  List.length (List.filter (fun (s,_) -> s = t) (types()));;

let nonempty = prove(`?n. n < 2`, EXISTS_TAC `0` THEN ARITH_TAC);;

let _ = on_all_domains "types" (fun d ->
  for i = 1 to ntypes do
    let t = Printf.sprintf "concurrency_test_ty_%d_%d" d i in
    let spec = Printf.sprintf "%s = CTA_%d_%d | CTB_%d_%d num %s"
                 t d i d i t in
    let ith,rth = define_type spec in
    let ith',rth' = define_type spec in
    check "define_type: redefinition not benign"
      (equals_thm ith ith' && equals_thm rth rth');
    let n = Printf.sprintf "concurrency_test_tydef_%d_%d" d i in
    let th = new_type_definition n ("mk_"^n,"dest_"^n) nonempty in
    let th' = new_type_definition n ("mk_"^n,"dest_"^n) nonempty in
    check "new_type_definition: redefinition not benign" (equals_thm th th');
    (* Parsed again for the second time, when the constant exists.         *)
    let f = Printf.sprintf "concurrency_test_fn_%d_%d" d i in
    let fdef () = parse_term (Printf.sprintf "%s x = x + %d" f i) in
    let th = define (fdef ()) in
    let th' = define (fdef ()) in
    check "define: redefinition not benign" (equals_thm th th');
    let r = Printf.sprintf "concurrency_test_rel_%d_%d" d i in
    let rdef () = parse_term
      (Printf.sprintf "%s 0 /\\ (!n. %s n ==> %s (n + %d))" r r r i) in
    let r1,r2,r3 = new_inductive_definition (rdef ()) in
    let r1',r2',r3' = new_inductive_definition (rdef ()) in
    check "new_inductive_definition: redefinition not benign"
      (equals_thm r1 r1' && equals_thm r2 r2' && equals_thm r3 r3')
  done);;

let () =
  for d = 0 to ndomains - 1 do
    for i = 1 to ntypes do
      List.iter
        (fun t -> check ("type missing or twice: "^t) (count_type t = 1))
        [Printf.sprintf "concurrency_test_ty_%d_%d" d i;
         Printf.sprintf "concurrency_test_tydef_%d_%d" d i]
    done
  done;;

(* ------------------------------------------------------------------------- *)
(* Axioms from several domains: none may be lost, or check_axioms would      *)
(* not list it.                                                              *)
(* ------------------------------------------------------------------------- *)

let naxioms = 25;;
let axioms_before = List.length (axioms());;

let new_axioms = on_all_domains "axioms" (fun d ->
  List.map (fun i ->
    let p = mk_var(Printf.sprintf "concurrency_test_ax_%d_%d" d i,bool_ty) in
    new_axiom (mk_iff(p,p))) (1--naxioms));;

let () =
  let ax = axioms() in
  check "axioms(): an update was lost"
    (List.length ax = axioms_before + ndomains * naxioms);
  List.iter (function
      Some ths -> check "axioms(): an axiom is not listed"
                    (forall (fun th -> exists (equals_thm th) ax) ths)
    | None -> ())
    new_axioms;;

(* ------------------------------------------------------------------------- *)
(* Summary.                                                                  *)
(* ------------------------------------------------------------------------- *)

(if !failures = [] then
   Printf.printf "OK: concurrency tests passed on %d domains\n" ndomains
 else
  (List.iter (fun m -> Printf.printf "FAILED: %s\n" m)
     (setify !failures);
   exit 1));;
