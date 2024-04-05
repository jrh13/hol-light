
(*open satCommonTools;;*)

(* translation from terms to DIMACS cnf and back  *)

(* mapping from HOL variable names to DIMACS  variable numbers
   is stored in a global assignable (i.e. reference) variable sat_var_map.
   The type of sat_var_map is (int * (term * int) map) ref and
   the integer first component is the next available number
   (i.e. it is one plus the number of elements in the map)
   in th second component (t,n), if n<0 then the literal represented
   is ~t (the stored t is never negated)
*)

(*
  initialise sat_var_map to integer 1 paired with the empty map
 (in DIMACS  variable numbering starts from 1 because 0
  is the clause separator)
*)

let sat_var_map = ref(1, Termmap.empty)
let sat_var_arr = ref(Array.make 0 t_tm) (* varnum->+ve lit. *)

(*
 Reinitialise sat_var_map.
 Needs to be done for each translation of a term to DIMACS
 as numbers must be an initial segment of 1,2,3,...
 (otherwise grasp, zchaff etc may crash)
*)

(*+1 'cos var numbers start at 1*)
let initSatVarMap var_count =
  (sat_var_map := (1, Termmap.empty);
   sat_var_arr := Array.make (var_count+1) t_tm)


(*
 Lookup the var number corresponding to a +ve literal s, possibly extending sat_var_map
*)

let lookup_sat_var s =
  let (c,svm) = !sat_var_map in
  snd (try Termmap.find s svm with
    Not_found ->
      let svm' = Termmap.add s (s,c) svm in
      let _    = (sat_var_map := (c+1,svm')) in
      let _    =
        try (Array.set (!sat_var_arr) c s)
        with Invalid_argument _  ->
          failwith ("lookup_sat_varError: "^(string_of_term s)^"::"^(string_of_int c)^"\n") in
      (t_tm,c))


(*
 Lookup the +ve lit corresponding to a var number
*)
let lookup_sat_num n =
  try (Array.get (!sat_var_arr) n)
  with Invalid_argument _ ->
    failwith ("lookup_sat_numError: "^(string_of_int n)^"\n")


(*
 Show sat_var_map as a list of its elements
*)

let showSatVarMap () =
 let (c,st) = !sat_var_map in
  (c, List.map snd (tm_listItems st))

(*
 Print a term showing types
*)

let all_string_of_term t =
  ((string_of_term) t^" : "^(string_of_type (type_of t)))

let print_all_term t =
  print_string (all_string_of_term t);;

(*
 Convert a literal to a (bool * integer) pair, where
 the boolean is true iff the literal is negated,
 if necessary extend sat_var_map
*)

exception Lit_to_int_err of string

let literalToInt t =
  let (sign,v) =
      if is_neg t
      then
        let t1 = dest_neg t in
        if type_of t1 = bool_ty
        then (true, t1)
        else raise (Lit_to_int_err (all_string_of_term t))
      else
        if type_of t = bool_ty
        then (false, t)
        else raise (Lit_to_int_err (all_string_of_term t)) in
  let v_num = lookup_sat_var v in
  (sign, v_num)

(*
 Convert an integer (a possibly negated var number) to a literal,
 raising lookup_sat_numError if the absolute value of
 the integer isn't in sat_var_map
*)
let intToLiteral n =
    let t = lookup_sat_num (abs n) in
    if n>=0 then t else mk_neg t

(*
 termToDimacs t
 checks t is CNF of the form
  ``(v11 \/ ... \/ v1p) /\ (v21 \/ ... \/ v2q) /\ ... /\ (vr1 \/ ... \/vrt)``
 where vij is a literal, i.e. a boolean variable or a negated
 boolean variable.
 If t is such a CNF then termToDimacs t returns a list of lists of integers
 [[n11,...,n1p],[n21,...,n2q], ... , [nr1,...,nrt]]
 If vij is a boolean variable ``v`` then nij is the entry
 for v in sat_var_map. If vij is ``~v``, then nij is the negation
 of the entry for v in sat_var_map
 N.B. Definition of termToDimacs processes last clause first,
      so variables are not numbered in the left-to-right order.
      Not clear if this matters.
*)

let termToDimacs t =
 List.fold_right
  (fun c d ->  (List.map literalToInt (disjuncts c)) :: d)
  (conjuncts t) []

(* Test data
val t1 = ``x:bool``;
val t2 = ``~x``;
val t3 = ``x \/ y \/ ~z \/ w``;
val t4 = ``(x \/ y \/ ~z \/ w) /\ (~w \/ ~x \/ y)``;
val t5 = ``(x \/ y \/ ~z \/ w) /\ !x. (~w \/ ~x \/ y)``;
val t6 = ``(x \/ y \/ ~z \/ w) /\ (~w)``;
val t7 = ``(x \/ y \/ ~z \/ w) /\ (~w) /\ (w \/ x) /\ (p /\ q /\ r)``;
*)

(*
 reference containing prefix used to make variables from numbers
 when reading DIMACS
*)

let prefix = ref "v"

(*
 intToPrefixedLiteral n = ``(!prefix)n``
 intToPrefixedLiteral (~n) = ``~(!prefix)n``
*)

let intToPrefixedLiteral n =
 if n >= 0
  then mk_var(((!prefix) ^ (string_of_int n)), bool_ty)
  else mk_neg(mk_var((!prefix) ^ (string_of_int(abs n)), bool_ty))

(*
 buildClause [n1,...,np] builds
 ``(!prefix)np /\ ... /\ (!prefix)n1``
 Raises exception Empty on the empty list
*)

let buildClause l =
 List.fold_left
  (fun t n -> mk_disj(intToPrefixedLiteral n, t))
  (intToPrefixedLiteral (hd l))
  (tl l)

(*
 dimacsToTerm l
 converts a list of integers
 [n11,...,n1p,0,n21,...,n2q,0, ... , 0,nr1,...,nrt,0]
 into a term in CNF of the form
  ``(v11 \/ ... \/ v1p) /\ (v21 \/ ... \/ v2q) /\ ... /\ (vr1 \/ ... \/vrt)``
 where vij is a literal, i.e. a boolean variable or a negated boolena variable.
 If nij is non-negative then vij is ``(!prefix)nij``;
 If nij is negative ~mij then vij is ``~(!prefix)mij``;
*)

(* dimacsToTerm_aux splits off one clause, dimacsToTerm iterates it *)
let rec dimacsToTerm_aux acc = function
 [] -> (buildClause acc,[])
 | (0::l) -> (buildClause acc,l)
 | (x::l) -> dimacsToTerm_aux (x::acc) l

let rec dimacsToTerm l =
 let (t,l1) = dimacsToTerm_aux [] l in
 if List.length l1 = 0
 then t
 else mk_conj(t, dimacsToTerm l1)

(*
 Convert (true,n) to "-n" and (false,n) to "n"
*)

let literalToString b n =
  if b
  then ("-" ^ (string_of_int n))
  else string_of_int n

(*
 termToDimacsFile t
 converts t to DIMACS  and then writes out a
 file into the temporary directory.
 the name of the temporary file (without extension ".cnf") is returned.
*)

(*
 Refererence containing name of temporary file used
 for last invocation of a SAT solver
*)

let tmp_name = ref "undefined"

let termToDimacsFile fname t var_count =
  let clause_count = List.length(conjuncts t) in
  let _            = initSatVarMap var_count in
  let dlist        = termToDimacs t in
  let tmp          = Filename.temp_file "sat" "" in
  let tmpname      =
    match fname with
      (Some fname) -> fname^".cnf"
    | None ->  tmp^".cnf" in
  let outstr       = open_out tmpname in
  let out s        = output_string outstr s in
  let res = (out "c File "; out tmpname; out " generated by HolSatLib\n";
             out "c\n";
             out "p cnf ";
             out (string_of_int var_count); out " ";
             out (string_of_int clause_count); out "\n";
             List.iter
                (fun l -> (List.iter (fun (x,y) ->
                  (out(literalToString x y); out " ")) l;
                           out "\n0\n"))
               dlist;
             close_out outstr;
             tmp_name := tmp;
             match fname with
               (Some _) ->  tmpname
             | None -> tmp) in
  res;;

(*
 readDimacs filename
 reads a DIMACS  file called filename and returns
 a term in CNF in which each number n in the DIMACS file
 is a boolean variable (!prefix)n
 Code below by Ken Larsen (replaces earlier implementation by MJCG)
*)
exception Read_dimacs_error;;

let rec dropLine ins =
  match Stream.peek ins with
    Some '\n' -> Stream.junk ins
  | Some _    -> (Stream.junk ins; dropLine ins)
  | None      -> raise Read_dimacs_error

let rec stripPreamble ins =
  match Stream.peek ins with
    Some 'c' -> (dropLine ins; stripPreamble ins)
  | Some 'p' -> (dropLine ins; stripPreamble ins)
  | Some _   -> Some ()
  | None     -> None

let rec getIntClause lex acc =
  match
    (try Stream.next lex with
      Stream.Failure -> Genlex.Kwd "EOF" (* EOF *))
  with
    (Genlex.Int 0)     -> Some acc
  | (Genlex.Int i)     -> getIntClause lex (i::acc)
  | (Genlex.Kwd "EOF") ->
      if List.length acc = 0
      then None
      else Some acc
   |  _                 -> raise Read_dimacs_error


(* This implementation is inspired by
   (and hopefully faithful to) dimacsToTerm.
*)
let getTerms lex =
  let rec loop acc =
    match getIntClause lex [] with
      Some ns -> loop (mk_conj(buildClause ns, acc))
    | None    -> Some acc in
  match getIntClause lex [] with
    Some ns -> loop (buildClause ns)
  | None    -> None

let readTerms ins =
  match stripPreamble ins with
    Some _ ->
      let lex = (Genlex.make_lexer ["EOF"] ins) in
      getTerms lex
  | None     -> None

let readDimacs filename =
 (*let val fullfilename = Path.mkAbsolute(filename, FileSys.getDir())*)
  let inf          = open_in filename in
  let ins          = Stream.of_channel inf in
  let term         = readTerms ins in
  (close_in inf;
   match term with Some t -> t | None -> raise Read_dimacs_error)

