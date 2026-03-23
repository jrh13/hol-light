(* ========================================================================= *)
(* Probability theory library for HOL Light.                                 *)
(*                                                                           *)
(* A systematic theory of probability based on typed probability measure     *)
(* spaces, following Williams "Probability with Martingales".                *)
(*                                                                           *)
(* Main results: Central Limit Theorem, Laws of Large Numbers (weak and      *)
(* strong), Fair Games Theorem (Doob optional stopping), Borel-Cantelli      *)
(* lemmas, martingale convergence, Azuma-Hoeffding inequality.               *)
(* ========================================================================= *)

(* Library dependencies *)
needs "100/inclusion_exclusion.ml";;
needs "Library/card.ml";;
needs "Multivariate/realanalysis.ml";;
needs "100/fourier.ml";;

(* Foundations *)
loadt "Probability/measure.ml";;
loadt "Probability/random_variables.ml";;
loadt "Probability/independence.ml";;
loadt "Probability/expectation.ml";;

(* Martingale theory *)
loadt "Probability/martingales.ml";;
loadt "Probability/martingale_convergence.ml";;

(* Characteristic functions and simple CLT *)
loadt "Probability/characteristic_functions.ml";;

(* Central Limit Theorem for integrable RVs *)
loadt "Probability/clt.ml";;
