(* ========================================================================= *)
(* Reading and writing DIMACS ".cnf" files and converting to and from HOL.   *)
(*                                                                           *)
(* This does not rigorously enforce many of the syntactic restrictions and   *)
(* in particular it completely ignores the "p" line (or many "p" lines)      *)
(* specifying the number of variables and clauses. It also doesn't do any    *)
(* analysis of the clauses to rule out tautologies etc.                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Equivalents of "conjuncts" and "length o conjuncts" but tail recursive.   *)
(* ------------------------------------------------------------------------- *)

let list_conjuncts =
  let rec aux acc tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),t) -> aux (l::acc) t
    | _ -> tm::acc in
  fun tm -> rev(aux [] tm);;

let rec count_conjuncts n tm =
  match tm with
    Comb(Comb(Const("/\\",_),_),t) -> count_conjuncts (n+1) t
  | _ -> n;;

(* ------------------------------------------------------------------------- *)
(* Parsing and processing.                                                   *)
(* ------------------------------------------------------------------------- *)

let stripcomments s =
  match String.index_opt s 'c' with
    Some i -> String.sub s 0 i
  | None -> s;;

let process_lines f p fname =
  let fd =
    try open_in fname
    with Sys_error _ -> failwith("read_dimacs: can't open "^fname) in
  let rec suck_lines acc =
    let l = try [input_line fd] with End_of_file -> [] in
    if l = [] then rev_itlist (@) acc [] else
    let y = f(hd l) in
    suck_lines (if p y then y::acc else acc) in
  let data = suck_lines [] in
  (close_in fd; data);;

let rec parse_clauses acc cur l =
  match l with
    ""::t -> parse_clauses  acc cur t
  | "0"::t -> parse_clauses (rev cur::acc) [] t
  | n::t -> parse_clauses acc (int_of_string n::cur) t
  | [] -> rev acc;;

(* ------------------------------------------------------------------------- *)
(* Reading and writing betweeen DIMACS file and int list list in OCaml       *)
(* ------------------------------------------------------------------------- *)

let read_dimacs fname =
  let l = process_lines
           (String.split_on_char ' ' o
            String.map (function '\t' -> ' ' | c -> c) o stripcomments)
           (function "p"::_ -> false | _ -> true) fname in
  parse_clauses [] [] l;;

let write_dimacs =
  let string_of_clause cl =
    itlist (fun t s -> string_of_int t ^ " " ^ s) cl "0\n" in
  fun fname cls ->
    let fd =
      try open_out fname
      with Sys_error _ -> failwith("write_dimacs: can't open "^fname) in
    let n = rev_itlist (rev_itlist (max o abs)) cls 0
    and m = rev_itlist (fun _ n -> n + 1) cls 0 in
    (output_string fd ("p cnf "^string_of_int n^" "^string_of_int m^"\n");
     do_list (output_string fd o string_of_clause) cls;
     close_out fd);;

(* ------------------------------------------------------------------------- *)
(* Translation between HOL terms and int list list, with variable mappings.  *)
(* ------------------------------------------------------------------------- *)

let clauses_of_term vmap tm =
  let cnf_of_literal t =
    match t with
      Comb(Const("~",_),s) -> -(vmap s)
    | _ -> vmap t in
  map (map cnf_of_literal o disjuncts) (list_conjuncts tm);;

let term_of_literal amap n =
   if n < 0 then mk_neg(amap (-n)) else amap n;;

let term_of_clause =
  let false_tm = `F` in
  fun amap ->
    let rec aux tm l =
      match l with
        h::t -> aux (mk_disj(term_of_literal amap h,tm)) t
      | [] -> tm in
    fun l ->
      match rev l with
        [] -> false_tm
      | h::t -> aux (term_of_literal amap h) t;;

let term_of_clauses =
  let true_tm = `T` in
  fun amap ->
    let rec aux tm l =
      match l with
        h::t -> aux (mk_conj(term_of_clause amap h,tm)) t
      | [] -> tm in
    fun l ->
      match rev l with
        [] -> true_tm
      | h::t -> aux (term_of_clause amap h) t;;

(* ------------------------------------------------------------------------- *)
(* Composite function not directly creating the int list list and picking a  *)
(* default numbering of the atoms from the call to "atoms".                  *)
(* ------------------------------------------------------------------------- *)

let dimacs_of_hol fname tm =
  let m = count_conjuncts 1 tm in
  let ats = atoms tm in
  let n = length ats in
  let _,vmap =
    rev_itlist (fun a (n,f) -> (n+1,(a |-> n) f)) ats (1,undefined) in
  let cnf_of_literal t =
    match t with
      Comb(Const("~",_),s) -> -(apply vmap s)
    | _ -> apply vmap t in
  let string_of_clause cl =
   itlist (fun t s -> string_of_int(cnf_of_literal t) ^ " " ^ s)
          (disjuncts cl) "0\n" in
  let fd =
    try open_out fname
    with Sys_error _ -> failwith("dimacs_of_hol: can't open "^fname) in
  (output_string fd ("p cnf "^string_of_int n^" "^string_of_int m^"\n");
   do_list (output_string fd o string_of_clause) (list_conjuncts tm);
   close_out fd);;
