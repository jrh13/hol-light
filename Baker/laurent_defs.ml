(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the definitions of the                 *)
(* numeric layer.                                                            *)
(*                                                                           *)
(* Purpose: the closed forms of M. Laurent, Linear forms in two logarithms   *)
(* and interpolation determinants II, Acta Arith. 133 (2008), Theorem 2 at   *)
(* mu = 1, with lam = log rho and H = h / lam + 1: laurent_omega H and       *)
(* laurent_theta H (omega and theta of Laurent), the constants               *)
(* laurent_C rho h a1 a2 and laurent_Cp rho h a1 a2 (C and C prime of        *)
(* Laurent), the bound                                                       *)
(*   laurent_bound rho h a1 a2 = C (h + lam)^2 a1 a2 + sqrt(omega theta)     *)
(*                               (h + lam) + log(C prime (h + lam)^2 a1 a2)  *)
(* of Theorem 2 (log |Lambda| >= - laurent_bound), and                       *)
(* laurent_main D rho b1 b2 a1 a2 K L R S, the main inequality of the        *)
(* interpolation determinant method at mu = 1 (condition (2) of Laurent      *)
(* Theorem 1 with our lower-order terms) for the integer parameters K, L, R, *)
(* S and a degree D.                                                         *)
(*                                                                           *)
(* Main results: the definitions laurent_omega, laurent_theta, laurent_C,    *)
(* laurent_Cp, laurent_bound, laurent_main.                                  *)
(*                                                                           *)
(* Uses: Multivariate/transcendentals.ml (log).                              *)
(*                                                                           *)
(* Baker/make_laurent.ml loads sections 1, 9 and 10 alone.                   *)
(* ========================================================================= *)

needs "Multivariate/transcendentals.ml";;

prioritize_real();;
prioritize_num();;

let laurent_omega = new_definition
 `laurent_omega H = &2 * (&1 + sqrt(&1 + inv(&4 * H pow 2)))`;;

let laurent_theta = new_definition
 `laurent_theta H = sqrt(&1 + inv(&4 * H pow 2)) + inv(&2 * H)`;;

let laurent_C = new_definition
 `laurent_C rho h a1 a2 =
    let lam = log rho in
    let H = h / lam + &1 in
    let om = laurent_omega H in
    let th = laurent_theta H in
    inv(lam pow 3) *
    (om / &6 +
     sqrt(om pow 2 / &9 +
          &8 * lam * sqrt(sqrt(om pow 5 * th)) / (&3 * sqrt(a1 * a2) * sqrt H) +
          &4 / &3 * (inv a1 + inv a2) * lam * om / H) / &2) pow 2`;;

let laurent_Cp = new_definition
 `laurent_Cp rho h a1 a2 =
    let lam = log rho in
    let H = h / lam + &1 in
    sqrt(laurent_C rho h a1 a2 * laurent_omega H * laurent_theta H /
         lam pow 3)`;;

let laurent_bound = new_definition
 `laurent_bound rho h a1 a2 =
    let lam = log rho in
    let H = h / lam + &1 in
    laurent_C rho h a1 a2 * (h + lam) pow 2 * a1 * a2 +
    sqrt(laurent_omega H * laurent_theta H) * (h + lam) +
    log(laurent_Cp rho h a1 a2 * (h + lam) pow 2 * a1 * a2)`;;

let laurent_main = new_definition
 `laurent_main D rho b1 b2 a1 a2 K L R S <=>
    &2 * log(&2) + &2 * &D / &(K * L) * log(&(FACT(K * L))) +
    &D * ((&K - &1) * log(&((R - 1) * b2 + (S - 1) * b1) / &2) -
          &2 / &K * sum(1..K - 1) (\k. log(&(FACT k)))) +
    (&1 / &4 - &(K * L) / (&12 * &R * &S)) * &L * (&R * a1 + &S * a2)
    < &K * (&L - &1) * log rho`;;
