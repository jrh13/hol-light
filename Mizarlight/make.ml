(* ========================================================================= *)
(*            "Mizar Light" by Freek Wiedijk.                                *)
(*                                                                           *)
(*        http://www.cs.ru.nl/~freek/mizar/miz.pdf                           *)
(* ========================================================================= *)

exception Innergoal of goal;;

let (GOAL_TAC:tactic) = fun gl -> raise(Innergoal gl);;

let e tac =
  try refine(by(VALID tac))
  with Innergoal gl ->
       let oldgoalstack = !current_goalstack in
       current_goalstack := (mk_goalstate gl)::oldgoalstack;
       !current_goalstack;;

(* ------------------------------------------------------------------------- *)
(* Set up more infix operators.                                              *)
(* ------------------------------------------------------------------------- *)

Topdirs.dir_directory (!hol_dir);;

Toploop.load_file Format.std_formatter
 (Filename.concat (!hol_dir) "Mizarlight/pa_f.cmo");;

List.iter (fun s -> Hashtbl.add (Pa_j.ht) s true)
 ["st'";"st";"at";"from";"by";"using";"proof"; "THEN'"];;

(* ------------------------------------------------------------------------- *)
(* Mizar Light.                                                              *)
(* ------------------------------------------------------------------------- *)

loadt "Mizarlight/miz2a.ml";;

(* ------------------------------------------------------------------------- *)
(* Projective duality proof in Mizar Light.                                  *)
(* ------------------------------------------------------------------------- *)

loadt "Mizarlight/duality.ml";;

(* ------------------------------------------------------------------------- *)
(* A prover more closely approximating Mizar's own.                          *)
(* ------------------------------------------------------------------------- *)

loadt "Examples/holby.ml";;

(* ------------------------------------------------------------------------- *)
(* A version of the duality proof based on that.                             *)
(* ------------------------------------------------------------------------- *)

loadt "Mizarlight/duality_holby.ml";;
