(* ========================================================================= *)
(* Class number two: the definitions.                                        *)
(*                                                                           *)
(* Purpose: the definitions of Baker/make.ml section 22 (the                 *)
(* imaginary quadratic fields of class number two; Baker, Transcendental     *)
(* Number Theory, Ch. 5, sec. 5): the cyclotomic unit of a real quadratic    *)
(* field and the Kronecker symbol of the discriminant -4d.                   *)
(*                                                                           *)
(*  - cyclo_unit q: the cyclotomic unit prod_a sin(pi a / q)^(-chi_q(a)) of  *)
(*    the real quadratic field of discriminant q (q = 1 mod 4 squarefree),   *)
(*    so that |L(1, chi_q)| = |log(cyclo_unit q)| / sqrt q by                *)
(*    CLASSNO_L1_EVEN (it is eps_q^(2 h(q)), which is never needed).         *)
(*  - kchar4 d m: the Kronecker symbol (-4d / m) for odd m (0 for even m),   *)
(*    the character of the discriminant -4d (d = 1, 2 mod 4 squarefree).     *)
(*                                                                           *)
(* The general binary quadratic forms and their representation numbers       *)
(* (qform, qform_rep; the principal form prin_form d is                      *)
(* qform 1 1 ((d + 1) DIV 4)) are in Baker/classno_defs.ml; the lattice      *)
(* terms and slices of a general form twisted by a real character at real s  *)
(* (qform_term, qform_slice, at s = 1 for the limit formula) and the kernel  *)
(* qform_kernel of the error of the limit formula are in                     *)
(* Baker/classno_chardefs.ml, since the general form machinery loads in      *)
(* section 15.                                                               *)
(*                                                                           *)
(* Main results: the definitions cyclo_unit, kchar4.                         *)
(*                                                                           *)
(* Uses: Baker/classno_chardefs.ml (qchar), Library/jacobi.ml (jacobi).      *)
(* ========================================================================= *)

needs "Baker/classno_chardefs.ml";;

prioritize_real();;
prioritize_num();;

let cyclo_unit = new_definition
 `cyclo_unit (q:num) =
    exp(--sum(1..q - 1) (\a. qchar q a * log(sin(pi * &a / &q))))`;;

let kchar4 = new_definition
 `kchar4 (d:num) (m:num) =
    if EVEN m then &0
    else --(&1) pow ((m - 1) DIV 2) * real_of_int(jacobi(d,m))`;;
