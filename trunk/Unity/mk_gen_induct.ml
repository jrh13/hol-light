(* -*- Emacs Mode: sml -*- *)

(*---------------------------------------------------------------------------*)
(*
   File:         mk_gen_induct.sml

   Description:  This file proves the theorem of general induction on natural
                 numbers by using the theorem of primitive recursion.

   Author:       (c) Copyright 1990-2008 by Flemming Andersen
                 Modified by John Harrison to just pick up num_WF instead
   Date:         June 7. 1990
   Last Update:  January 18, 2008
*)
(*---------------------------------------------------------------------------*)

(*
        !P. (!(m:num). (!n. n < m ==> (P n)) ==> (P m)) ==> (!m. P m)
*)
let GEN_INDUCT_thm = prove_thm
  ("GEN_INDUCT_thm",
   (`!P. (!(m:num). (!n. n < m ==> (P n)) ==> (P m)) ==> (!m. P m)`),
    MATCH_ACCEPT_TAC num_WF);;

(* Emacs editor information
|  Local variables:
|  mode:sml
|  sml-prog-name:"hol90"
|  End:
*)
