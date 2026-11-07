(* ========================================================================= *)
(* Two logarithms, the Laurent bound for algebraic numbers: elements,        *)
(* algebraic integers and pair heights in a number field.                    *)
(*                                                                           *)
(* Purpose: for a number field K = Q(r 1) given by nf_data n c r             *)
(* (Baker/nf_defs.ml; vectors of conjugates indexed by 1..n): nf_elem n r a  *)
(* (a is the vector of conjugates of an element of K: some non-zero integer  *)
(* multiple d a is, at every conjugate, one integer polynomial of degree < n *)
(* in r k), nf_alg_int n r a (moreover a 1 is an algebraic integer), and the *)
(* archimedean height of a chosen pair of conjugate vectors,                 *)
(*   nf_proj_height n be ga = (1/n) sum_(k = 1..n) log max(|be k|, |ga k|),  *)
(* which takes the place of the absolute logarithmic height of               *)
(* x = be 1 / ga 1 in the bounds of the algebraic case.                      *)
(* For algebraic-integer coordinates with ga 1 nonzero, this archimedean     *)
(* quantity bounds that height from above. It depends on the chosen pair:    *)
(* scaling both coordinates need not preserve it.                            *)
(*                                                                           *)
(* Main results: the definitions nf_elem, nf_alg_int, nf_proj_height.        *)
(*                                                                           *)
(* Uses: Baker/algint.ml (algebraic_integer).                                *)
(*                                                                           *)
(* The definitions are used by Baker/ant_bridge_nf.ml, by the Laurent bound  *)
(* for algebraic numbers (section 13) and by Baker/classno_nf.ml             *)
(* (section 15).                                                             *)
(* ========================================================================= *)

needs "Baker/algint.ml";;

prioritize_real();;
prioritize_num();;

let nf_elem = new_definition
 `nf_elem n (r:num->complex) (a:num->complex) <=>
    ?d p. integer d /\ ~(d = &0) /\ (!i. integer(p i)) /\
          !k. k IN 1..n
              ==> Cx d * a k = vsum(0..n - 1) (\i. Cx(p i) * r k pow i)`;;

let nf_alg_int = new_definition
 `nf_alg_int n (r:num->complex) (a:num->complex) <=>
    nf_elem n r a /\ algebraic_integer(a 1)`;;

let nf_proj_height = new_definition
 `nf_proj_height n (be:num->complex) (ga:num->complex) =
    sum(1..n) (\k. log(max (norm(be k)) (norm(ga k)))) / &n`;;
