(* ========================================================================= *)
(* Sieve/make.ml                                                             *)
(*                                                                           *)
(* Sieve methods and their applications to the primes: the beta-sieve and    *)
(* the Jurkat-Richert theorem, Selberg's sieve, Brun's sieve, and Chen's     *)
(* theorem in its Goldbach and twin prime forms, with the analytic input     *)
(* behind it (Dirichlet characters and L-functions, Siegel's theorem, the    *)
(* zero-free region, Siegel-Walfisz, the large sieve and                     *)
(* Bombieri-Vinogradov); the prime number theorem for arithmetic             *)
(* progressions, Brun-Titchmarsh, Erdos's covering congruences, Romanov, the *)
(* Titchmarsh divisor problem, Hardy-Ramanujan; bounded gaps between primes  *)
(* (Maynard-Tao); Vinogradov's three primes theorem and Goldbach for almost  *)
(* all even numbers; Waring's problem (Hardy-Littlewood, Hilbert); Linnik's  *)
(* least quadratic nonresidue, Barban-Davenport-Halberstam, Hua's five prime *)
(* squares, n^2 + 1 = P4 and P3; three-term progressions of primes           *)
(* (van der Corput) and the Green-Tao theorem.  README.md describes the      *)
(* results, the files and the sources.                                       *)
(*                                                                           *)
(* With the directory containing Sieve on the load path (HOL Light's default *)
(* load_path is ["."; "$"]: install Sieve under the HOL Light root, or start *)
(* HOL Light in the directory containing it) and an unlimited stack          *)
(* (ulimit -s unlimited),                                                    *)
(*                                                                           *)
(*   loadt "Sieve/make.ml";;                                                 *)
(*                                                                           *)
(* loads Sieve/base.ml (Multivariate/cauchy.ml and the other libraries below *)
(* Sieve/) and all the developments; nothing beyond the three standard       *)
(* axioms is used.  Any file can also be loaded on its own with its          *)
(* prerequisites, e.g. needs "Sieve/chen.ml";;.                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Chen's theorem and the sieve framework; the classical corollaries.        *)
(* ------------------------------------------------------------------------- *)

needs "Sieve/chen.ml";;
needs "Sieve/pnt_ap.ml";;
needs "Sieve/brun_titchmarsh.ml";;
needs "Sieve/erdos_covering.ml";;
needs "Sieve/romanov.ml";;
needs "Sieve/titchmarsh.ml";;
needs "Sieve/hardy_ramanujan.ml";;
needs "Sieve/chen_shift.ml";;

(* ------------------------------------------------------------------------- *)
(* Bounded gaps, Vinogradov, Goldbach for almost all even numbers, Waring,   *)
(* Linnik, Barban-Davenport-Halberstam, Hua, n^2 + 1.                        *)
(* ------------------------------------------------------------------------- *)

needs "Sieve/bounded_gaps.ml";;
needs "Sieve/vinogradov.ml";;
needs "Sieve/goldbach_almost.ml";;
needs "Sieve/chen_distinct.ml";;
needs "Sieve/waring.ml";;
needs "Sieve/linnik.ml";;
needs "Sieve/bdh.ml";;
needs "Sieve/hua.ml";;
needs "Sieve/square_plus_one.ml";;
needs "Sieve/square_plus_one_p3.ml";;

(* ------------------------------------------------------------------------- *)
(* Progressions of primes: van der Corput, the Green-Tao majorant, the       *)
(* transference and the relative Szemeredi theorem, Green-Tao.               *)
(* ------------------------------------------------------------------------- *)

needs "Sieve/van_der_corput.ml";;
needs "Sieve/gt_majorant.ml";;
needs "Sieve/gt_density.ml";;
needs "Sieve/gt_transfer.ml";;
needs "Sieve/gt_green_tao.ml";;
