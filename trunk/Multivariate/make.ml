(* ========================================================================= *)
(* Theory of multivariate calculus in Euclidean space.                       *)
(* ========================================================================= *)

loadt "Library/card.ml";;               (* For countable set theorems.      *)
loadt "Library/permutations.ml";;       (* For determinants                 *)
loadt "Library/products.ml";;           (* For determinants and integrals   *)
loadt "Library/floor.ml";;              (* Useful here and there            *)
loadt "Multivariate/misc.ml";;          (* Background stuff                 *)
loadt "Library/iter.ml";;               (* n-fold iteration of function     *)

(* ------------------------------------------------------------------------- *)
(* The main core theory.                                                     *)
(* ------------------------------------------------------------------------- *)

loadt "Multivariate/metric.ml";;        (* General topology, metric spaces  *)
loadt "Multivariate/vectors.ml";;       (* Basic vectors, linear algebra    *)
loadt "Multivariate/determinants.ml";;  (* Determinant and trace            *)
loadt "Multivariate/topology.ml";;      (* Topology of R^n and much else    *)
loadt "Multivariate/convex.ml";;        (* Convex sets and functions        *)
loadt "Multivariate/paths.ml";;         (* Paths, simple connectedness etc. *)
loadt "Multivariate/polytope.ml";;      (* Faces, polytopes, polyhedra etc. *)
loadt "Multivariate/degree.ml";;        (* Brouwer degree, retracts etc.    *)
loadt "Multivariate/derivatives.ml";;   (* Derivatives                      *)
loadt "Multivariate/clifford.ml";;      (* Geometric (Clifford) algebra     *)
loadt "Multivariate/integration.ml";;   (* Integration                      *)
loadt "Multivariate/measure.ml";;       (* Lebesgue measure                 *)

(* ------------------------------------------------------------------------- *)
(* Updated database, for convenience where dynamic updating doesn't work.    *)
(* ------------------------------------------------------------------------- *)

loadt "Multivariate/multivariate_database.ml";;
