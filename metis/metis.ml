(* ------------------------------------------------------------------------- *)
(* Metis prover.                                                             *)
(* ------------------------------------------------------------------------- *)

let metisverb = ref false;;

loads "metis/portable.ml";;
loads "metis/real.ml";;
loads "metis/math.ml";;

(* Inline the Useful module here, as it's used almost everywhere in Metis: *)

(* ------------------------------------------------------------------------- *)
(* Exceptions.                                                               *)
(* ------------------------------------------------------------------------- *)

exception Error of string;;

exception Bug of string;;

let total f x = try Some (f x) with Error _ -> None;;

let isSome = function
    (Some _) -> true
  | None -> false
;;

let can f x = isSome (total f x);;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let cComb f x y = f y x;;

let iComb x = x;;

let kComb x y = x;;

let sComb f g x = f x (g x);;

let wComb f x = f x x;;

let rec funpow n f x =
  match n with
  | 0 -> x
  | _ -> funpow (n - 1) f (f x);;

let exp m =
  let rec f x y z =
    match y with
    | 0 -> z
    | _ -> f (m (x,x)) (Int.div y 2) (if y mod 2 = 0 then z else m (z,x)) in
  f;;

(* ------------------------------------------------------------------------- *)
(* Pairs.                                                                    *)
(* ------------------------------------------------------------------------- *)

let pair x y = (x,y);;

let swap (x,y) = (y,x);;

let curry f x y = f (x,y);;

let uncurry f (x,y) = f x y;;

(* ------------------------------------------------------------------------- *)
(* State transformers.                                                       *)
(* ------------------------------------------------------------------------- *)

let return (* : 'a -> 's -> 'a * 's *) = pair;;

let bind f (g (* : 'a -> 's -> 'b * 's *)) x = uncurry g (f x);;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

let revCompare cmp x y =
  match cmp x y with Less -> Greater | Equal -> Equal | Greater -> Less;;

let prodCompare xCmp yCmp (x1,y1) (x2,y2) =
  match xCmp x1 x2 with
  | Less -> Less
  | Equal -> yCmp y1 y2
  | Greater -> Greater;;

let lexCompare cmp =
  let rec lex x y =
    match x,y with
    | ([],[]) -> Equal
    | ([], _ :: _) -> Less
    | (_ :: _, []) -> Greater
    | (x :: xs, y :: ys) ->
        match cmp x y with
        | Less -> Less
        | Equal -> lex xs ys
        | Greater -> Greater in
  lex
;;

let boolCompare x y =
  match x,y with
  | (false,true) -> Less
  | (true,false) -> Greater
  | _ -> Equal;;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

let rec first f = function
  | [] -> None
  | x::xs -> match f x with None -> first f xs | s -> s;;

let rec maps (f (* : 'a -> 's -> 'b * 's *)) = function
  | [] -> return []
  | x :: xs ->
    bind (f x) (fun y -> bind (maps f xs) (fun ys -> return (y :: ys)));;

let zipWith f =
  let rec z l = function
    | ([], []) -> l
    | (x :: xs, y :: ys) -> z (f x y :: l) (xs, ys)
    | _ -> raise (Error "zipWith: lists different lengths") in
  fun xs -> fun ys -> List.rev (z [] (xs, ys))
;;

let zip xs ys = zipWith pair xs ys;;

let unzip ab =
  let inc (x,y) (xs,ys) = (x :: xs, y :: ys) in
  List.foldl inc ([],[]) (List.rev ab);;

let enumerate l = fst (maps (fun x m -> ((m, x), m + 1)) l 0);;

let revDivide l =
  let rec revDiv acc = function
    | (l, 0) -> (acc,l)
    | ([], _) -> raise Subscript
    | (h :: t, n) -> revDiv (h :: acc) (t, n - 1) in
  fun n -> revDiv [] (l, n);;

let divide l n = let (a,b) = revDivide l n in (List.rev a, b);;

let updateNth (n,x) l =
  let (a,b) = revDivide l n in
  match b with [] -> raise Subscript | (_ :: t) -> rev_append a (x :: t)
;;

let deleteNth n l =
  let (a,b) = revDivide l n in
  match b with [] -> raise Subscript | (_ :: t) -> rev_append a t
;;

(* ------------------------------------------------------------------------- *)
(* Sets implemented with lists.                                              *)
(* ------------------------------------------------------------------------- *)

let mem x l = List.exists (fun y -> x = y) l;;

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

let mkPrefix p s = p ^ s

let stripSuffix pred s =
  let rec strip pos =
    if pos < 0 then "" else
    if pred (s.[pos]) then strip (pos - 1)
    else String.substring s 0 (pos + 1) in
  strip (String.size s - 1);;

(* ------------------------------------------------------------------------- *)
(* Sorting and searching.                                                    *)
(* ------------------------------------------------------------------------- *)

let sort cmp = List.sort (fun x y -> cmp x y = Less);;

let sortMap f cmp = function
  | [] -> []
  | ([_] as l) -> l
  | xs ->
      let ncmp (m,_) (n,_) = cmp m n in
      let nxs = List.map (fun x -> (f x, x)) xs in
      let nys = List.sort (fun x y -> ncmp x y = Less) nxs in
      List.map snd nys
;;

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

let rec interval m = function
  | 0 -> []
  | len -> m :: interval (m + 1) (len - 1);;

let divides = function
  | (_, 0) -> true
  | (0, _) -> false
  | (a, b) -> b mod (abs a) = 0;;
let divides = curry divides;;

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

let generator = ref 0;;

let newIntThunk () =
  let n = !generator in
  generator := n + 1;
  n
;;

let newIntsThunk k () =
  let n = !generator in
  generator := n + k;
  interval n k
;;

let newInt () = newIntThunk ();;

let newInts k =
  if k <= 0 then []
  else (newIntsThunk k) ();;

(* The rest of Metis follows: *)

loads "metis/pmap.ml";;
loads "metis/pset.ml";;
loads "metis/mmap.ml";;
loads "metis/mset.ml";;
loads "metis/sharing.ml";;
loads "metis/heap.ml";;
loads "metis/name.ml";;
loads "metis/name_arity.ml";;
loads "metis/term.ml";;
loads "metis/substitute.ml";;
loads "metis/atom.ml";;
loads "metis/formula.ml";;
loads "metis/literal.ml";;
loads "metis/thm.ml";;
loads "metis/proof.ml";;
loads "metis/rule.ml";;
loads "metis/model.ml";;
loads "metis/term_net.ml";;
loads "metis/atom_net.ml";;
loads "metis/literal_net.ml";;
loads "metis/subsume.ml";;
loads "metis/knuth_bendix.ml";;
loads "metis/rewrite.ml";;
loads "metis/units.ml";;
loads "metis/clause.ml";;
loads "metis/active.ml";;
loads "metis/waiting.ml";;

(*
loads "metis/resolution.ml";;
loads "metis/loop.ml";;
loads "metis/metis_debug.ml";;
loads "metis/preterm.ml";;
loads "metis/metis_mapping.ml";;
loads "metis/metis_path.ml";;
loads "metis/metis_unify.ml";;
loads "metis/metis_rules.ml";;
loads "metis/metis_reconstruct2.ml";;
loads "metis/metis_generate.ml";;
*)
(* ========================================================================= *)
(* Main Metis module.                                                        *)
(* ========================================================================= *)

(*
module Metis = struct

(*
open Metis_prover
*)

(* ------------------------------------------------------------------------- *)
(* Some parameters controlling Metis behaviour.                              *)
(* ------------------------------------------------------------------------- *)

let split_limit = ref 0;; (* Limit of case splits before Metis proper  *)

(* ----------------------------------------------------------------------- *)
(* Basic HOL Metis procedure.                                              *)
(* ----------------------------------------------------------------------- *)

(* Debugging tactic. *)
let PRINT_TAC g = print_goal g; ALL_TAC g
let PRINT_ID_TAC s g = print_endline s; PRINT_TAC g

(* Slightly modified tactic from meson.ml. *)
let FOL_PREPARE_TAC ths =
  (* We start with a single goal: P. *)
  REFUTE_THEN ASSUME_TAC THEN
  (*PRINT_ID_TAC "refuted" THEN*)
  (*   0 [`~P`]

     `F`
   *)
  Meson.POLY_ASSUME_TAC (map GEN_ALL ths) THEN
  (*PRINT_ID_TAC "poly_assumed" THEN*)
  (*   0 [`~P`]
       1 [th1]
       ...
       n [thn]

     `F`
  *)
  W(MAP_EVERY(UNDISCH_TAC o concl o snd) o fst) THEN
  (* `~P ==> th1 ==> ... ==> thn ==> F` *)
  SELECT_ELIM_TAC THEN
  (* eliminate "select terms", e.g. Hilbert operators *)
  W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  (*PRINT_ID_TAC "all-quantified" THEN*)
  (* MAP_EVERY is mapM for tactics
     I believe that this all-quantifies all free variables in the goal *)
  CONV_TAC(PRESIMP_CONV THENC
           TOP_DEPTH_CONV BETA_CONV THENC
           LAMBDA_ELIM_CONV THENC
           CONDS_CELIM_CONV THENC
           Meson.QUANT_BOOL_CONV) THEN
  (*PRINT_ID_TAC "converted" THEN*)
  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  (* remove outermost all-quantifiers (GEN_TAC) and implications (DISCH_TAC),
     moving them into assumptions *)
  REFUTE_THEN ASSUME_TAC THEN
  (* move conclusion negated into assumptions, replace goal by `F`*)
  RULE_ASSUM_TAC(CONV_RULE(NNF_CONV THENC SKOLEM_CONV)) THEN
  (* transform assumptions to NNF and skolemize *)
  REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
  (* remove existentials at the front *)
  ASM_FOL_TAC THEN
  (* fix function arities, e.g. f(x) and f(x,y) become I f x and I (I f x) y *)
  Meson.SPLIT_TAC (!split_limit) THEN
  RULE_ASSUM_TAC(CONV_RULE(PRENEX_CONV THENC WEAK_CNF_CONV)) THEN
  RULE_ASSUM_TAC(repeat
   (fun th -> SPEC(genvar(type_of(fst(dest_forall(concl th))))) th)) THEN
  (* destroy all-quantifiers and replace quantified variables by fresh ones *)
  REPEAT (FIRST_X_ASSUM (Meson.CONJUNCTS_THEN' ASSUME_TAC)) THEN
  (* make every conjunction a separate assumption *)
  RULE_ASSUM_TAC(CONV_RULE(ASSOC_CONV DISJ_ASSOC))
  (* associate disjunctions to the right *)
  (*THEN PRINT_ID_TAC "before Metis"*)

let without_warnings f =
  let tiv = !type_invention_warning in
  let reset () = type_invention_warning := tiv in
  type_invention_warning := false;
  try let y = f () in reset (); y
  with e -> (reset(); raise e)

let SIMPLE_METIS_REFUTE ths =
  Meson.clear_contrapos_cache();
  (* TODO: Metis currently uses randomness to search for proof --
     we should make that deterministic for proof reconstruction! *)
  Random.init 0;
  let rules = Metis_generate.metis_of_clauses ths in
  if !metisverb then
  begin
    Format.printf "Original ths:\n%!";
    List.iter (Format.printf "%s\n%!" o string_of_thm) ths
  end;
  let res = Loop.run rules in
  if !metisverb then Thm.print_proof res;
  let ths = map (CONV_RULE DISJ_CANON_CONV) ths in
  let proof = without_warnings (fun () -> Metis_reconstruct2.hol_of_thm ths res) in
  if !metisverb then
  begin
    Format.printf "ths:\n%!";
    List.iter (fun t -> print_thm t; Format.printf "\n%!") ths;
    Format.printf "Metis theorem:\n%!";
    print_thm proof;
    Format.printf "Metis end.\n%!";
  end;
  let allhyps = List.concat (List.map hyp ths) in
  assert (forall (fun h -> mem h allhyps) (hyp proof));
  assert (concl proof = `F`);
  proof

let PURE_METIS_TAC g =
  Meson.reset_vars(); Meson.reset_consts();
  (FIRST_ASSUM CONTR_TAC ORELSE
   W(ACCEPT_TAC o SIMPLE_METIS_REFUTE o map snd o fst)) g

let GEN_METIS_TAC ths =
  FOL_PREPARE_TAC ths THEN PURE_METIS_TAC

end (* struct Metis *)
;;

(* ========================================================================= *)
(* Basic Metis refutation procedure and parametrized tactic.                 *)
(* ========================================================================= *)

let ASM_METIS_TAC = Metis.GEN_METIS_TAC;;

let METIS_TAC ths = POP_ASSUM_LIST(K ALL_TAC) THEN ASM_METIS_TAC ths;;

let METIS ths tm = prove(tm,METIS_TAC ths);;
*)

