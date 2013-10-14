prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Some additional mathematical background.                                  *)
(* ------------------------------------------------------------------------- *)

loadt "Library/rstc.ml";;
loadt "Library/prime.ml";;

(* ------------------------------------------------------------------------- *)
(* The basics of first order logic and our inference system.                 *)
(* ------------------------------------------------------------------------- *)

loadt "Arithmetic/fol.ml";;

(* ------------------------------------------------------------------------- *)
(* The incompleteness results.                                               *)
(* ------------------------------------------------------------------------- *)

loadt "Arithmetic/definability.ml";;
loadt "Arithmetic/tarski.ml";;
loadt "Arithmetic/arithprov.ml";;
loadt "Arithmetic/godel.ml";;

(* ------------------------------------------------------------------------- *)
(* Sigma-1 completeness of Robinson arithmetic.                              *)
(* ------------------------------------------------------------------------- *)

loadt "Arithmetic/derived.ml";;
loadt "Arithmetic/sigmacomplete.ml";;
