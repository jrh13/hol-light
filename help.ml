(* ========================================================================= *)
(* Simple online help system, based on old HOL88 one.                        *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

let help_path = ref ["$/Help"];;

let help s =
  let funny_filenames =
   ["++", ".joinparsers";
    "||", ".orparser";
    ">>", ".pipeparser";
    "|=>", ".singlefun";
    "--", ".upto";
    "|->", ".valmod";
    "insert'", "insert_prime";
    "mem'", "mem_prime";
    "subtract'", "subtract_prime";
    "union'", "union_prime";
    "unions'", "unions_prime";
    "ALPHA", "ALPHA_UPPERCASE";
    "CHOOSE", "CHOOSE_UPPERCASE";
    "CONJUNCTS", "CONJUNCTS_UPPERCASE";
    "EXISTS", "EXISTS_UPPERCASE";
    "INSTANTIATE", "INSTANTIATE_UPPERCASE";
    "INST", "INST_UPPERCASE";
    "MK_BINOP", "MK_BINOP_UPPERCASE";
    "MK_COMB", "MK_COMB_UPPERCASE";
    "MK_CONJ", "MK_CONJ_UPPERCASE";
    "MK_DISJ", "MK_DISJ_UPPERCASE";
    "MK_EXISTS", "MK_EXISTS_UPPERCASE";
    "MK_FORALL", "MK_FORALL_UPPERCASE";
    "REPEAT", "REPEAT_UPPERCASE"] in
  let true_path = map hol_expand_directory (!help_path) in
  let raw_listing =
    map (fun s -> String.sub s 0 (String.length s - 4))
        (itlist (fun a l -> Array.to_list (Sys.readdir a) @ l) true_path []) in
  let mod_listing =
    map fst funny_filenames @
    subtract raw_listing (map snd funny_filenames) in
  let edit_distance s1 s2 =
    let l1 = String.length s1 and l2 = String.length s2 in
    let a = Array.make_matrix (l1 + 1) (l2 + 1) 0 in
    for i = 1 to l1 do a.(i).(0) <- i done;
    for j = 1 to l2 do a.(0).(j) <- j done;
    for i = 1 to l1 do
      for j = 1 to l2 do
        let cost = if String.get s1 (i-1) = String.get s2 (j-1) then 0 else 1 in
        a.(i).(j) <- min (min a.(i-1).(j) a.(i).(j-1) + 1)
                         (a.(i-1).(j-1) + cost)
      done
    done;
    a.(l1).(l2) in
  let closeness s s' =
    s',2.0 *. float_of_int
        (edit_distance (String.uppercase s) (String.uppercase s')) /.
        float_of_int(String.length s + String.length s') in
  let guess s =
    let guesses = mergesort(increasing snd) (map (closeness s) mod_listing) in
    map fst (fst(chop_list 3 guesses)) in
  Format.print_string
   "-------------------------------------------------------------------\n";
  Format.print_flush();
  (if mem s mod_listing then
    let fn = assocd s funny_filenames s ^".doc" in
    let file = file_on_path true_path fn
    and script = file_on_path [!hol_dir] "doc-to-help.sed" in
    ignore(Sys.command("sed -f "^script^" "^file))
   else
    let guesses = map
     (fun s -> "help \""^String.escaped s^"\";;\n") (guess s) in
    (Format.print_string o end_itlist(^))
     (["No help found for \""; String.escaped s; "\"; did you mean:\n\n"] @
      guesses @ ["\n?\n"]));
  Format.print_string
   "--------------------------------------------------------------------\n";
  Format.print_flush();;

(* ------------------------------------------------------------------------- *)
(* Set up a theorem database, but leave contents clear for now.              *)
(* ------------------------------------------------------------------------- *)

let theorems = ref([]:(string*thm)list);;

(* ------------------------------------------------------------------------- *)
(* Some hacky term modifiers to encode searches.                             *)
(* ------------------------------------------------------------------------- *)

let omit t = mk_comb(mk_var("<omit this pattern>",W mk_fun_ty (type_of t)),t);;

let exactly t = mk_comb(mk_var("<match aconv>",W mk_fun_ty (type_of t)),t);;

let name s = mk_comb(mk_var("<match theorem name>",W mk_fun_ty aty),
                     mk_var(s,aty));;

(* ------------------------------------------------------------------------- *)
(* The main search function.                                                 *)
(* ------------------------------------------------------------------------- *)

let search =
  let rec immediatesublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> h1 = h2 & immediatesublist t1 t2 in
  let rec sublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> immediatesublist l1 l2 or sublist l1 t2 in
  let exists_subterm_satisfying p (n,th) = can (find_term p) (concl th)
  and name_contains s (n,th) = sublist (explode s) (explode n) in
  let rec filterpred tm =
    match tm with
      Comb(Var("<omit this pattern>",_),t) -> not o filterpred t
    | Comb(Var("<match theorem name>",_),Var(pat,_)) -> name_contains pat
    | Comb(Var("<match aconv>",_),pat) -> exists_subterm_satisfying (aconv pat)
    | pat -> exists_subterm_satisfying (can (term_match [] pat)) in
  fun pats ->
    let triv,nontriv = partition is_var pats in
    (if triv <> [] then
      warn true
         ("Ignoring plain variables in search: "^
          end_itlist (fun s t -> s^", "^t) (map (fst o dest_var) triv))
     else ());
    (if nontriv = [] & triv <> [] then []
     else itlist (filter o filterpred) pats (!theorems));;
