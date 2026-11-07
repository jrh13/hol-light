(* ========================================================================= *)
(* The class number one problem: real characters and the lattice sums of a   *)
(* binary quadratic form (definitions).                                      *)
(*                                                                           *)
(* Purpose: qchar m n is the Jacobi symbol (n | m) = jacobi(n, m) of         *)
(* Library/jacobi.ml as a real number (for odd m a real Dirichlet character  *)
(* modulo m, QCHAR_DIRICHLET of Baker/classno_series.ml); zeta_coprime k is  *)
(* zeta_k(2), the sum over n >= 1 coprime to k of 1 / n^2. For a general     *)
(* form F = (a,b,c) (qform of Baker/classno_defs.ml) qform_term k a b c s x  *)
(* y is the term chi_k(F(x,y)) / F(x,y)^s of the lattice sum (F^s by rpow)   *)
(* and qform_slice k a b c s y is the slice S_y(s), the sum over all         *)
(* integers x of these terms (paired as x = n, x = -n-1). The limit formula  *)
(* works at s = 1, where the term is chi_k(F(x,y)) / F(x,y) (QFORM_TERM_1);  *)
(* the slices of the principal form prin_form d are those of the form        *)
(* (1, 1, (d + 1) DIV 4) (QFORM_PRIN). qform_kernel                          *)
(* x = x (1 + x) / (1 - x)^3 is the shape of the error of the limit formula. *)
(*                                                                           *)
(* Main results: the definitions qchar, zeta_coprime, qform_term,            *)
(* qform_slice, qform_kernel; QFORM_TERM_1, QCHAR_1.                         *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (qform); Library/jacobi.ml (jacobi);          *)
(* Multivariate/transcendentals.ml (rpow).                                   *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "Multivariate/transcendentals.ml";;
needs "Baker/classno_defs.ml";;

prioritize_real();;
prioritize_num();;

(* The real quadratic characters n -> (n | m) (Jacobi symbol, m odd).        *)

let qchar = new_definition
 `qchar (m:num) (n:num) = real_of_int(jacobi(n,m))`;;

(* zeta_k(2) = sum over x >= 1 coprime to k of 1 / x^2.                      *)

let zeta_coprime = new_definition
 `zeta_coprime (k:num) =
    real_infsum (from 1)
      (\n. if coprime(n,k) then inv((&n:real) pow 2) else &0)`;;

(* The terms chi_k(F(x,y)) / F(x,y)^s of a general form F = (a,b,c) at       *)
(* real s (F(x,y)^s by rpow), their slices S_y(s), and the kernel            *)
(* x (1 + x) / (1 - x)^3 of the error of the limit formula.                  *)

let qform_term = new_definition
 `qform_term (k:num) (a:int) (b:int) (c:int) (s:real) (x:int) (y:int) =
    qchar k (num_of_int(qform a b c x y)) /
    real_of_int(qform a b c x y) rpow s`;;

let qform_slice = new_definition
 `qform_slice (k:num) (a:int) (b:int) (c:int) (s:real) (y:num) =
    real_infsum (from 0)
      (\n. qform_term k a b c s (&n) (&y) +
           qform_term k a b c s (--(&n) - &1) (&y))`;;

let qform_kernel = new_definition
 `qform_kernel (x:real) = x * (&1 + x) / (&1 - x) pow 3`;;

(* The terms at s = 1.                                                       *)

let QFORM_TERM_1 = prove
 (`!k a b c x y.
     qform_term k a b c (&1) x y =
     qchar k (num_of_int(qform a b c x y)) / real_of_int(qform a b c x y)`,
  REWRITE_TAC[qform_term; RPOW_POW; REAL_POW_1]);;

let QCHAR_1 = prove
 (`!q. qchar q 1 = &1`,
  REWRITE_TAC[qchar; JACOBI_1; int_of_num_th]);;
