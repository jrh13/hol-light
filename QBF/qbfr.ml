(* Code for reading QDicams.        *)
(* Based on Minisat/dimacs_tools.ml *)
(* from HOL Light distribution.     *)


exception Read_dimacs_error;;

let prefix = ref "v_"

let intToPrefixedLiteral n =
 if n >= 0 
  then mk_var(((!prefix) ^ (string_of_int n)), bool_ty)
  else mk_neg(mk_var((!prefix) ^ (string_of_int(abs n)), bool_ty))

let buildClause l =
 List.fold_left 
  (fun t n -> mk_disj(intToPrefixedLiteral n, t))
  (intToPrefixedLiteral (hd l))
  (tl l) 

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

let rec getIntClause2 lex acc = 
  match Stream.next lex with
    (Genlex.Int 0)     -> acc
  | (Genlex.Int i)     -> i::(getIntClause2 lex acc)
  | _ -> raise Read_dimacs_error 
  
let getTerms lex start_acc =
  let rec loop acc =
    match getIntClause lex [] with
      Some ns -> loop (mk_conj(buildClause ns,acc))
    | None    -> Some acc in
  match getIntClause lex start_acc with
    Some ns -> loop (buildClause ns)
  | None    -> None

type qs = Qe of int list | Qa of int list;;

let read_quant lex = 
  let rec loop acc =
  match Stream.next lex with
    Genlex.Kwd "e" -> 
      let vars = getIntClause2 lex [] in
      let (acc',var) = loop acc in
      ((Qe vars)::acc',var)
    | Genlex.Kwd "a" -> 
      let vars = getIntClause2 lex [] in
      let (acc',var) = loop acc in
      ((Qa vars)::acc',var)
    | Genlex.Int i -> (acc,i)
    | _ -> raise Read_dimacs_error 
  in
  loop []

let var_map l =
   List.map intToPrefixedLiteral l

let add_quantifiers quant body =
  List.fold_right (fun quants b -> match quants with
				   Qa l -> list_mk_forall (var_map l,b)
				   | Qe l -> list_mk_exists (var_map l,b)
		  )
    quant body

let readTerms ins = 
  match stripPreamble ins with
    Some _ -> 
      let lex = (Genlex.make_lexer ["EOF";"e";"a"] ins) in 
      let (quant,var) = read_quant lex in
      ( match getTerms lex [var] with
	Some body -> Some (add_quantifiers quant body)
	| None -> None )
  | None     -> None

let readQDimacs filename =
  let inf          = open_in filename in
  let ins          = Stream.of_channel inf in
  let term         = readTerms ins in
  (close_in inf; 
   match term with Some t -> t | None -> raise Read_dimacs_error)
    