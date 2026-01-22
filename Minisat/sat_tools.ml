
(*open dimacsTools;;*)

(* Functions for parsing the DIMACS-compliant output of SAT solvers,
   This is generic. Parser for minisat proof log is in minisatParse.ml  *)

(*
** Use Binaryset to encode mapping between HOL variable names
** and DIMACS  variable numbers as a set of string*int pairs.
*)

(*
** substringContains s ss
** tests whether substring ss contains string s
*)

let substringContains s ss =
  let re = Str.regexp_string s in
  match
    (try Str.search_forward re ss 0 with
      Not_found -> -1) with
    -1 -> false
  | _  -> true


(*
** parseSat (s1,s2) ss
** returns a list of numbers corresponding to the tokenised
** substring of ss (tokenised wrt Char.isSpace) that starts immediately
** after the first occurrence of s1 and ends just before the first
** occurrence of s2 that is after the first occurrence of s1
*)

let parseSat (s1,s2) ss =
  let p1 = Str.search_forward (Str.regexp s1) ss 0 in
  let p2 = Str.search_backward (Str.regexp s2) ss (String.length ss) in
  let ss1 = Str.string_before ss p2 in
  let ss2 = Str.string_after ss1 (p1+String.length s1) in
  let ssl = Str.split (Str.regexp "[ \n\t\r]") ss2 in
  List.map int_of_string ssl


(*
** invokeSat solver t
** invokes solver on t and returns SOME s (where s is the satisfying instance
** as a string of integers) or NONE, if unsatisfiable
*)

(*
** Reference containing last command used to invoke a SAT solver
*)

let sat_command = ref "undef"

(*
** Test for success of the result of Process.system
** N.B. isSuccess expected to primitive in next release of
** Moscow ML, and Process.status will lose eqtype status
*)

let satdir = "";;

(* if fname is NONE, then use a temp file, otherwise assume fname.cnf alredy exists*)
let invokeSat sat_solver fname t vc =
  let {name=name;
       url=url;
       executable=executable;
       good_exit=good_exit;
       notime_run=notime_run;
       time_run=time_run;
       only_true=only_true;
       failure_string=failure_string;
       start_string=start_string;
       end_string=end_string} = sat_solver in
  let var_count  =
    match vc with
      Some n -> n |
      None -> List.length(variables t) in
  let tmp        =
    match fname with
      Some fnm ->
        (initSatVarMap var_count;
         ignore (termToDimacs t); (*FIXME: this regenerates sat_var_map:
                                    better to save/load it*)
         fnm)
    | None     -> termToDimacsFile None t var_count in
  let infile     = tmp ^ ".cnf" in
  let outfile    = tmp ^ "." ^ name in
  let ex         = Filename.concat satdir executable in
  let run_cmd    = notime_run ex (infile,outfile) in
  let _          = (sat_command := run_cmd) in
  let code       = Sys.command run_cmd in
  let _          =
    if ((name = "minisat") || (name = "minisatp") || (code = good_exit))
    then ()
    else print_string("Warning:\n Failure signalled by\n " ^ run_cmd ^ "\n") in
  let ins        = open_in outfile in
  let sat_res    = input_all ins in
  let _          = close_in ins in
  let result     = substringContains failure_string sat_res in
  if result
  then None
  else
    let model1 = parseSat(start_string,end_string) sat_res in
    let model2 =
      if only_true
      then model1
        @
          (List.map
             (fun n -> 0-n)
             (subtract (List.map snd (snd(showSatVarMap()))) model1))
      else model1 in
    Some (List.map intToLiteral model2)


(*
** satOracle sat_solver t
** invokes sat_solver on t and returns a theorem tagged by the solver name
** of the form |- (l1 /\ ... ln) ==> t (satisfied with literals l1,...,ln)
** or |- ~t (failure)
*)

let satOracle sat_solver t =
  let res = invokeSat sat_solver None t None in
  match res with
    Some l -> mk_thm ([], mk_imp(list_mk_conj l, t))
  | None   -> mk_thm ([], mk_neg t)

(*
** satProve sat_solver t
** invokes sat_solver on t and if a model is found then
** then it is verified using proof in HOL and a theorem
** |- (l1 /\ ... /\ ln) ==> t is returned
** (where l1,...,ln are the literals making up the model);
** Raises satProveError if no model is found.
** Raises satCheckError if the found model is bogus
*)

(*
** satCheck [l1,...,ln] t
** attempts to prove (l1 /\ ... /\ ln) ==> t
** if it succeeds then the theorem is returned, else
** exception satCheckError is raised
*)

let EQT_Imp1 = TAUT `!b. b ==> (b<=>T)`
let EQF_Imp1 = TAUT `!b. (~b) ==> (b<=>F)`
let EQT_Imp2 = TAUT `!b. (b<=>T) ==> b`;;

exception Sat_check_error

let satCheck model t =
 try
   let mtm  = list_mk_conj model in
   let th1  = ASSUME mtm in
   let thl  = List.map
       (fun th ->
         if is_neg(concl th)
         then MP (SPEC (dest_neg(concl th)) EQF_Imp1) th
         else MP (SPEC (concl th) EQT_Imp1) th)
       (CONJUNCTS th1) in
   let th3 = SUBS_CONV thl t in
   let th4 = CONV_RULE(RAND_CONV(REWRITE_CONV[])) th3 in
   let th5 = MP (SPEC t EQT_Imp2) th4 in
   DISCH mtm th5
 with
   Sys.Break -> raise Sys.Break
 | _         -> raise Sat_check_error;;

exception Sat_prove_error

(* old interface by MJCG. assumes t is in cnf; only for finding SAT *)
let satProve sat_solver t  =
 match invokeSat sat_solver None t None with
   Some model -> satCheck model t
 | None       -> raise Sat_prove_error

