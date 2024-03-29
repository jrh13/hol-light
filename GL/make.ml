(* ========================================================================= *)
(* Proof of the modal completeness of the provability logic GL.              *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/rstc.ml";;

loadt "GL/misc.ml";;           (* Miscellanea                               *)
loadt "GL/modal.ml";;          (* Syntax and semantics of modal logic       *)
loadt "GL/gl.ml";;             (* Axiomatics of GL provability logic        *)
loadt "GL/completeness.ml";;   (* Proof of the modal completeness of GL     *)
loadt "GL/k4lr.ml";;           (* Alternative axiomatization for GL         *)
needs "GL/decid.ml";;          (* Semidecision procedure for GL.            *)
