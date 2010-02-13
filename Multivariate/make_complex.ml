(* ========================================================================= *)
(* Theory of multivariate calculus in Euclidean space.                       *)
(* ========================================================================= *)

loadt "Library/card.ml";;               (* For countable set theorems.      *)
loadt "Library/permutations.ml";;       (* For determinants                 *)
loadt "Multivariate/misc.ml";;          (* Background stuff                 *)
loadt "Library/products.ml";;           (* For determinants and integrals   *)
loadt "Library/floor.ml";;              (* Useful here and there            *)
loadt "Library/binomial.ml";;           (* For Leibniz deriv formula etc.   *)
loadt "Library/iter.ml";;               (* n-fold iteration of function     *)

(* ------------------------------------------------------------------------- *)
(* The main core theory.                                                     *)
(* ------------------------------------------------------------------------- *)

loadt "Multivariate/vectors.ml";;       (* Basic vectors, linear algebra    *)
loadt "Multivariate/determinants.ml";;  (* Determinant and trace            *)
loadt "Multivariate/topology.ml";;      (* Basic topological notions        *)
loadt "Multivariate/convex.ml";;        (* Convex sets and functions        *)
loadt "Multivariate/polytope.ml";;      (* Faces, polytopes, polyhedra etc. *)
loadt "Multivariate/dimension.ml";;     (* Dimensional theorems             *)
loadt "Multivariate/derivatives.ml";;   (* Derivatives                      *)

(* ------------------------------------------------------------------------- *)
(* Work in progress.                                                         *)
(* ------------------------------------------------------------------------- *)

loadt "Multivariate/clifford.ml";;      (* Geometric (Clifford) algebra     *)
loadt "Multivariate/integration.ml";;   (* Integration                      *)
loadt "Multivariate/measure.ml";;       (* Lebesgue measure                 *)

(* ------------------------------------------------------------------------- *)
(* Complex numbers (as R^2) and complex analysis.                            *)
(* ------------------------------------------------------------------------- *)

loadt "Multivariate/complexes.ml";;       (* Complex numbers                *)
loadt "Multivariate/canal.ml";;           (* Complex analysis               *)
loadt "Multivariate/transcendentals.ml";; (* Real & complex transcendentals *)
loadt "Multivariate/realanalysis.ml";;    (* Some analytical stuff on R     *)
loadt "Multivariate/cauchy.ml";;          (* Complex line integrals         *)

(* ------------------------------------------------------------------------- *)
(* Updated database, for convenience where dynamic updating doesn't work.    *)
(* ------------------------------------------------------------------------- *)

loadt "Multivariate/complex_database.ml";;
