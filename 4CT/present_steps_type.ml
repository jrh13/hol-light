(* ========================================================================= *)
(* 4CT/present_steps_type.ml                                                 *)
(*                                                                           *)
(* The OCaml type of the presentation script steps, shared by                *)
(* presentations_data.ml (the data) and present_eval.ml (the interpreter),   *)
(* kept in its own file so that reloading the interpreter does not redefine  *)
(* the type under the data.  (HOL Light's camlp5 lexer reserves              *)
(* all-uppercase identifiers for values like THEN, so the constructors need  *)
(* a lowercase letter.)                                                      *)
(* ========================================================================= *)

type ploc = Spoke | Hat | Fan1 | Fan2 | Fan3;;

type hcitem = Hc1 of int * int | Hc2 of int * int * int;;

type pstep =
    Pcase of string * ploc * int * int * bool
  | Reducible
  | Hubcap of hcitem list
  | Similar of string * int * bool;;
