(* =========================================================== *)
(* OCaml univariate functions                                  *)
(* Author: Thomas C. Hales                                     *)
(* Date: 2011-08-21                                            *)
(* =========================================================== *)

(* port of univariate.cc
   a univariate represents a function u:real->real.
   its first derivative du:real->real
   and its second derivative ddu;real->real.

   For example, if the function is x |-> x,
   its derivative is x |-> 1,
   and second derivative is x |-> 0,
   which is implemented as ux1.

   We give a few other examples, sqrt,  1/x, atan.

 *)

needs "verifier/interval_m/interval.ml";;

module Univariate = struct

open Interval_types;;
open Interval;;

let eval uni x  = function
  | 0 -> uni.u x
  | 1 -> uni.du x
  | _ -> uni.ddu x;;

let mk_univariate (u1,du1,ddu1) = { u = u1; du = du1; ddu = ddu1; };;

let raise_zero x = bounded_from_zero x or  raise Unstable ;;

(* here are a couple of examples *)

let ux1 =
  mk_univariate(
    (fun x -> x),
    (fun x -> one),
    (fun x-> zero)
  );;

let usqrt =
  let ( / ) = idiv in
  let ( * ) = imul in
    mk_univariate(
      isqrt,

      (fun x ->
        let _ = raise_zero x in
          one / (two * isqrt x)),

      (fun x ->
         let _ = raise_zero x in
           ineg (one / ((two * isqrt x) * (two * x))))
);;

let uinv =
  let ( / ) = idiv in
  let ( * ) = imul in
    mk_univariate(
      (fun x ->
         let _ = raise_zero x in
           one / x),

      (fun x ->
         let _ = raise_zero x in
           ineg (one / ( x * x))),

      (fun x ->
         let _ = raise_zero x in
            two / ( x * (x * x)))
    );;

let uatan =
  let ( / ) = idiv in
  let ( * ) = imul in
  let ( + ) = iadd in
    mk_univariate(
      iatan,

      (fun x ->
         one / (one + x * x)),

      (fun x ->
         let t = one / (one + x * x) in
           (ineg two * x) * (t * t))
    );;


let uacos =
  let ( / ) = idiv in
  let ( * ) = imul in
  let ( - ) = isub in
    mk_univariate(
      iacos,
      (fun x ->
         ineg (one / isqrt (one - x * x))),
      (fun x ->
         let t = one - x * x in
         ineg (x / isqrt (t * t * t)))
    );;

end;;
