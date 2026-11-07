(* ========================================================================= *)
(* Number fields as conjugate vectors: the definitions.                      *)
(*                                                                           *)
(* Purpose: a number field of degree n is given by a monic integer           *)
(* polynomial f(z) = sum_{i=0..n} c i z^i = prod_{k=1..n} (z - r k) all of   *)
(* whose roots have degree n (no non-zero integer polynomial of degree < n   *)
(* vanishes at any r k), i.e. f is irreducible over Q. An element of the     *)
(* order Z[theta], theta = r 1, is represented by its conjugate vector       *)
(* k |-> P(r k), k IN 1..n, for an integer polynomial P; only the values on  *)
(* 1..n matter.                                                              *)
(*                                                                           *)
(* Main results: the definitions nf_data (the data n c r), nf_order (the     *)
(* order Z[theta]) and nf_unit (units of the order); the norm of an element  *)
(* is the product cproduct(1..n) of its conjugates; NF_DATA_1_IN (the index  *)
(* 1 of the first conjugate r 1 = theta lies in 1..n).                       *)
(*                                                                           *)
(* Uses: Multivariate/complex_algebra.ml (cproduct); no other Baker file.    *)
(* ========================================================================= *)

needs "Multivariate/complex_algebra.ml";;

prioritize_real();;
prioritize_num();;

let nf_data = new_definition
 `nf_data n (c:num->real) (r:num->complex) <=>
    1 <= n /\ (!i. integer(c i)) /\ c n = &1 /\
    (!z. vsum(0..n) (\i. Cx(c i) * z pow i) = cproduct(1..n) (\k. z - r k)) /\
    (!k m b. k IN 1..n /\ m < n /\ (!i. integer(b i)) /\
             vsum(0..m) (\i. Cx(b i) * r k pow i) = Cx(&0)
             ==> !i. i <= m ==> b i = &0)`;;

let nf_order = new_definition
 `nf_order n (r:num->complex) (a:num->complex) <=>
    ?d p. (!i. integer(p i)) /\
          !k. k IN 1..n ==> a k = vsum(0..d) (\i. Cx(p i) * r k pow i)`;;

let nf_unit = new_definition
 `nf_unit n (r:num->complex) (a:num->complex) <=>
    nf_order n r a /\
    ?b. nf_order n r b /\ !k. k IN 1..n ==> a k * b k = Cx(&1)`;;

(* ------------------------------------------------------------------------- *)
(* The first conjugate r 1 = theta always exists.                            *)
(* ------------------------------------------------------------------------- *)

let NF_DATA_1_IN = prove
 (`!n c r. nf_data n c r ==> 1 IN 1..n`,
  SIMP_TAC[nf_data; IN_NUMSEG; LE_REFL]);;
