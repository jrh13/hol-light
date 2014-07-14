(* =========================================================== *)
(* Declaration of types and exceptions                         *)
(* Author: Thomas C. Hales                                     *)
(* Date: 2011-08-21                                            *)
(* =========================================================== *)

module Interval_types = struct

exception Unstable;;  (* generally thrown when there is a divide by zero *)

exception Fatal;;  (* generally indicates an uncorrected bug *)

(* represents a closed interval [lo,hi] of the real line *)

type interval = {
  lo : float;
  hi : float;
};;

(* represents a function u:real->real, its derivative du, and 2nd derivative *)

type univariate = {
  u : interval -> interval;
  du : interval -> interval;
  ddu : interval -> interval;
};;

(* represents the value f of function of six variables at some point y.
   and the value df of its six partial derivatives, evaluated at the same point y.
   The length of the list df should always be 8.
*)

type line = {
  f : interval;
  df : (interval) list;
};;

(*
  represents approximation data for a function f on a rectangular domain [x,z].
  l gives the value and partial derivatives of f at some point y in the domain.
  dd gives interval bounds on the second derivatives over the entire domain.
  w i is an upper bound on widths (z i - y i) and (y i - x i).
*)

type taylor_interval = {
  l : line;
  w : float list;
  dd : interval list list;
};;


end;;
