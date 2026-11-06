(* ========================================================================= *)
(* Sieve/base.ml                                                             *)
(*                                                                           *)
(* The HOL Light libraries below Sieve/: complex analysis                    *)
(* (Multivariate/cauchy.ml), Library/multiplicative.ml, the prime number     *)
(* theorem (100/pnt.ml), Dirichlet's theorem (100/dirichlet.ml),             *)
(* Schnirelmann's theorem (Examples/schnirelmann.ml) and Szemeredi's theorem *)
(* (Library/szemeredi.ml, which loads 100/bertrand.ml).                      *)
(*                                                                           *)
(* The files of Sieve/ are written for the parse priorities left by          *)
(* Multivariate/cauchy.ml: complex before real before num for the            *)
(* arithmetic operators.  Each of them sets these priorities after its       *)
(* needs lines (prioritize_num(); prioritize_complex()), so that it parses   *)
(* the same whatever was loaded or prioritized before it.                    *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Library/multiplicative.ml";;
needs "100/pnt.ml";;
needs "100/dirichlet.ml";;
needs "Examples/schnirelmann.ml";;
needs "Library/szemeredi.ml";;
