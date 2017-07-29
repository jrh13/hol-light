(******************************************************************************)
(* FILE          : shells.ml                                                  *)
(* DESCRIPTION   : Vague approximation in ML to Boyer-Moore "shell" principle *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 8th May 1991                                               *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 12th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* ML datatype for holding information about a recursive logical type.        *)
(*----------------------------------------------------------------------------*)

type constructor_info =
   string *               (* Constructor name   *)
   hol_type list *        (* Argument types     *)
   (string * thm) list;;   (* Accessor functions *)


type shell_info =
   {arg_types : hol_type list;     (* Argument types for type constructor *)
    constructors :
       constructor_info list;      (* Constructors for the type           *)
   (* axiom : thm;                   (* Type axiom                          *)*)
    induct : thm;                  (* Induction theorem                   *)
    cases : thm;                   (* Cases theorem                       *)
    distinct : thm list;           (* Constructors distinct               *)
    one_one : thm list;            (* Constructors one-one                *)
    struct_conv : conv -> conv};; 

type shell = Shell of string * shell_info;;

(*----------------------------------------------------------------------------*)
(* Reference variable holding the currently defined system shells.            *)
(*----------------------------------------------------------------------------*)

let system_shells = ref ([]:shell list);;

(*----------------------------------------------------------------------------*)
(* Function to find the details of a named shell from a list of shells.       *)
(*----------------------------------------------------------------------------*)

let rec shell_info (shl:shell list) name =
   if (shl = [])
   then failwith "shell_info"
   else match (hd shl) with Shell (sh_name,info) ->
            (if (sh_name = name)
               then info
               else shell_info (tl shl) name);;

(*----------------------------------------------------------------------------*)
(* Function to find the details of a named shell from the shells currently    *)
(* defined in the system.                                                     *)
(*----------------------------------------------------------------------------*)

let sys_shell_info name = shell_info !system_shells name;;

(*----------------------------------------------------------------------------*)
(* Functions to extract the components of shell information.                  *)
(*----------------------------------------------------------------------------*)
let shell_constructors info = info.constructors;;
let shell_accessor_thms info = 
  ((map snd) o flat o (map  thd3) o shell_constructors) info;;
let shell_arg_types info = info.arg_types;;

(*
let shell_arg_types info = fst info
and shell_constructors info = (fst o snd) info
and shell_axiom info = (fst o snd o snd) info
and shell_induct info = (fst o snd o snd o snd) info
and shell_cases info = (fst o snd o snd o snd o snd) info
and shell_distinct info = (fst o snd o snd o snd o snd o snd) info
and shell_one_one info = (fst o snd o snd o snd o snd o snd o snd) info
and shell_struct_conv info = (snd o snd o snd o snd o snd o snd o snd) info;;
*)

(*----------------------------------------------------------------------------*)
(* Function to extract details of a named constructor from shell information. *)
(*----------------------------------------------------------------------------*)

let shell_constructor name (info:shell_info) =
   let rec shell_constructor' name triples =
      if (triples = [])
      then failwith "shell_constructor"
      else let (con_name,arg_types,accessors) = (hd triples)
      in if (con_name = name)
           then (arg_types,accessors)
           else shell_constructor' name (tl triples)
   in shell_constructor' name (info.constructors);;

(*----------------------------------------------------------------------------*)
(* Functions to extract the argument types and the accessor functions for a   *)
(* particular constructor. The source is a set of shell information.          *)
(*----------------------------------------------------------------------------*)

let shell_constructor_arg_types name info =
   fst (shell_constructor name info)
and shell_constructor_accessors name info =
   snd (shell_constructor name info);;

(*----------------------------------------------------------------------------*)
(* shells : void -> string list                                               *)
(*                                                                            *)
(* Function to compute the names of the currently defined system shells.      *)
(*----------------------------------------------------------------------------*)

let shells () =
   let rec shells' shl =
      if (shl = [])
      then []
      else match (hd shl) with (Shell (name,_)) -> (name::(shells' (tl shl)))
   in shells' !system_shells;;

(*----------------------------------------------------------------------------*)
(* all_constructors : void -> string list                                     *)
(*                                                                            *)
(* Returns a list of all the shell constructors (and bottom values) available *)
(* in the system.                                                             *)
(*----------------------------------------------------------------------------*)

let all_constructors () =
 flat (map (map fst3 o shell_constructors o sys_shell_info) (shells ()));;

(*----------------------------------------------------------------------------*)
(* all_accessors : void -> string list                                        *)
(*                                                                            *)
(* Returns a list of all the shell accessors available in the system.         *)
(*----------------------------------------------------------------------------*)

let all_accessors () =
   flat (map (flat o map (map fst o thd3) o shell_constructors o
              sys_shell_info) (shells ()));;

let all_accessor_thms () =
  flat (map (shell_accessor_thms o sys_shell_info) (shells ()));;

(*----------------------------------------------------------------------------*)
(* `Shell' for natural numbers.                                               *)
(*----------------------------------------------------------------------------*)

let num_shell =
     let (*axiom = num_Axiom
         and*) induct = num_INDUCTION
         and cases = num_CASES
         and distinct = [NOT_SUC]
         and one_one = [SUC_INJ]
(*         and pre = PRE *)
     in  Shell
            ("num",
             {arg_types = [];
              constructors =
                 [("0",[],[]);("SUC",[`:num`],[("PRE",CONJUNCT2 PRE)])];
              (*axiom = axiom;*)
              induct = induct;
              cases = cases;
              distinct = distinct;
              one_one = one_one;
              struct_conv = ONE_STEP_RECTY_EQ_CONV
                               (induct,distinct,one_one)});;

(*----------------------------------------------------------------------------*)
(* `Shell' for lists.                                                         *)
(*----------------------------------------------------------------------------*)

let list_shell =
   let (*axiom = new_axiom `!x f. ?!fn1. (fn1 [] = x) /\ (!h t. fn1 (CONS h t) = f (fn1 t) h t)`
(* |- !x f. ?!fn1. (fn1 [] = x) /\ (!h t. fn1 (CONS h t) = f (fn1 t) h t) *)
       and *) induct = list_INDUCT
       and cases = list_CASES
       and distinct = [NOT_CONS_NIL]
       and one_one = [CONS_11]
   in  Shell
          ("list",
           {arg_types = [`:'a`];
            constructors =
               [("NIL",[],[]);
                ("CONS",
                 [`:'a`;`:('a)list`],[("HD",HD);("TL",TL)])];
            (* axiom = axiom; *)
            induct = induct;
            cases = cases;
            distinct = distinct;
            one_one = one_one;
            struct_conv = ONE_STEP_RECTY_EQ_CONV
                             (induct,distinct,one_one)});;

(*----------------------------------------------------------------------------*)
(* Set-up the system shell to reflect the basic HOL system.                   *)
(*----------------------------------------------------------------------------*)

system_shells := [list_shell;num_shell];;

(*----------------------------------------------------------------------------*)
(* define_shell : string -> string -> (string # string list) list -> void     *)
(*                                                                            *)
(* Function for defining a new HOL type together with accessor functions, and *)
(* making a new Boyer-Moore shell from these definitions. If the type already *)
(* exists the function attempts to load the corresponding theorems from the   *)
(* current theory hierarchy and use them to make the shell.                   *)
(*                                                                            *)
(* The first two arguments correspond to the arguments taken by `define_type' *)
(* and the third argument defines the accessor functions. This is a list of   *)
(* constructor names each with names of accessors. The function assumes that  *)
(* there are no accessors for a constructor that doesn't appear in the list,  *)
(* so it is not necessary to include an entry for a nullary constructor. For  *)
(* other constructors there must be one accessor name for each argument and   *)
(* they should be given in the correct order. The function ignores any item   *)
(* in the list with a constructor name that does not belong to the type.      *)
(*                                                                            *)
(* The constructor and accessor names must all be distinct and must not be    *)
(* the names of existing constants.                                           *)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*    define_shell `sexp` `sexp = Nil | Atom * | Cons sexp sexp`              *)
(*       [(`Atom`,[`Tok`]);(`Cons`,[`Car`;`Cdr`])];;                          *)
(*                                                                            *)
(* This results in the following theorems being stored in the current theory  *)
(* (or these are the theorems the function would expect to find in the theory *)
(* hierarchy if the type already exists):                                     *)
(*                                                                            *)
(*    sexp               (type axiom)                                         *)
(*    sexp_Induct        (induction theorem)                                  *)
(*    sexp_one_one       (injectivity of constructors)                        *)
(*    sexp_distinct      (distinctness of constructors)                       *)
(*    sexp_cases         (cases theorem)                                      *)
(*                                                                            *)
(* The following definitions for the accessor functions are also stored:      *)
(*                                                                            *)
(*    Tok                |- !x. Tok(Atom x) = x                               *)
(*    Car                |- !s1 s2. Car(Cons s1 s2) = s1                      *)
(*    Cdr                |- !s1 s2. Cdr(Cons s1 s2) = s2                      *)
(*                                                                            *)
(* In certain cases the distinctness or injectivity theorems may not exist,   *)
(* when nothing is saved for them.                                            *)
(*                                                                            *)
(* Finally, a new Boyer-Moore shell is added based on the definitions and     *)
(* theorems.                                                                  *)
(*----------------------------------------------------------------------------*)
(*
let define_shell name syntax accessors =
   let find_theory s =
      letrec f s l =
         if (null l)
         then failwith `find_theory`
         else if can (theorem (hd l)) s
              then hd l
              else f s (tl l)
      in f s (ancestry ())
   in
   let mk_def_eq (name,comb,arg) =
      let ty = mk_type(`fun`,[type_of comb;type_of arg])
      in  mk_eq(mk_comb(mk_var(name,ty),comb),arg)
   in
   let define_accessor axiom (name,tm) =
      (name,new_recursive_definition false axiom name tm)
   in
   let define_accessors axiom (comb,specs) =
      map (\(name,arg). define_accessor axiom (name,mk_def_eq (name,comb,arg)))
          specs
   in
   if (mem name (shells ()))
   then failwith `define_shell -- shell already exists`
   else
   let defined = is_type name
   in  let theory =
          if defined
          then (find_theory name ?
                failwith (`define_shell -- no axiom found for type ` ^ name))
          else current_theory ()
   in  let name_Axiom =
          if defined
          then theorem theory name
          else define_type name syntax
   in  let name_Induct =
          if defined
          then theorem theory (name ^ `_Induct`)
          else save_thm((name ^ `_Induct`),prove_induction_thm name_Axiom)
       and name_one_ones =
          if defined
          then (CONJUNCTS (theorem theory (name ^ `_one_one`))
                ?\s if (can prove_constructors_one_one name_Axiom)
                    then failwith s
                    else [])
          else ((CONJUNCTS o save_thm)
                   ((name ^ `_one_one`),prove_constructors_one_one name_Axiom)
                ? [])
       and name_distincts =
          if defined
          then (CONJUNCTS (theorem theory (name ^ `_distinct`))
                ?\s if (can prove_constructors_distinct name_Axiom)
                    then failwith s
                    else [])
          else ((CONJUNCTS o save_thm)
                  ((name ^ `_distinct`),prove_constructors_distinct name_Axiom)
                ? [])
   in  let name_cases =
          if defined
          then theorem theory (name ^ `_cases`)
          else save_thm((name ^ `_cases`),prove_cases_thm name_Induct)
   in  let ty = (type_of o fst o dest_forall o concl) name_cases
   in  let ty_args = snd (dest_type ty)
   in  let cases = (disjuncts o snd o dest_forall o concl) name_cases
   in  let combs = map (rhs o snd o strip_exists) cases
   in  let constrs_and_args = map (((fst o dest_const) # I) o strip_comb) combs
   in  let (constrs,arg_types) =
          split (map (I # (map type_of)) constrs_and_args)
   in  let acc_specs =
          map (\(c,args). combine((snd (assoc c accessors) ? []),args)
                  ? failwith
                       (`define_shell -- ` ^
                        `incorrect number of accessors for constructor ` ^ c))
              constrs_and_args
   in  let acc_defs =
          if defined
          then map (map ((\acc. (acc,definition theory acc)) o fst)) acc_specs
          else map (define_accessors name_Axiom) (combine (combs,acc_specs))
   in  let name_shell =
          Shell (name,ty_args,combine(constrs,combine(arg_types,acc_defs)),
                 name_Axiom,name_Induct,name_cases,
                 name_distincts,name_one_ones,
                 ONE_STEP_RECTY_EQ_CONV
                    (name_Induct,name_distincts,name_one_ones))
   in  do (system_shells := name_shell.system_shells);;
*)
