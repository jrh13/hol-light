(* =========================================================== *)
(* OCaml interval arithmetic                                   *)
(* Author: Thomas C. Hales                                     *)
(* Date: 2011-08-21                                            *)
(* =========================================================== *)

(* port of interval.cc,

This file gives a simple implementation of interval arithmetic,
together with the basic arithmetic operations on intervals.

It has been incompletely implemented.

For now, I am not implementing directed roundings.
However, McLaughlin implemented directed rounding several years ago:
See http://perso.ens-lyon.fr/nathalie.revol/mpfi.html
 ~/Library/McLaughlinOCAML/ocaml/src/extensions/ocaml-mpfi/

 *)

needs "verifier/interval_m/types.ml";;

module Interval = struct

open Interval_types;;

let mk_interval (a,b) = { lo = a; hi = b; };;

let string_of_interval x = Printf.sprintf "[%f;%f]" x.lo x.hi;;

(* let izero = mk_interval(0.0,0.0);; *)
let zero = mk_interval(0.0,0.0);;
let one = mk_interval(1.0,1.0);;
let two = mk_interval(2.0,2.0);;
let four = mk_interval(4.0,4.0);;

let is_zero x =(x.lo=0.0)&&(x.hi=0.0);;

let pos x = if (x.lo >= 0.0) then x else
   mk_interval(0.0,   if (x.hi < 0.0) then 0.0 else x.hi );;

let imax (x,y) = let t=max x.hi y.hi in mk_interval(t,t);;

let imin (x,y) = let t = min x.lo y.lo in mk_interval(t,t);;

let imin3(x,y,z) = imin(x,imin(y,z));;

let imax3(x,y,z) = imax(x,imax(y,z));;

let imax4(w,x,y,z) = imax(imax(w,x),imax(y,z));;

let sup x = x.hi;;

let inf x = x.lo;;

let iabs x = max x.hi (~-. (x.lo));;

let ilt x y = (x.hi < y.lo);;

let igt x y = (x.lo > y.hi);;

let ieq x y = (x.lo = y.lo && x.hi = y.hi);;

(* need rounding modes -- BUG *)


(* start of bug section *)

let up() = (  (* bug *) );;
let down() = ( (* bug *) );;
let nearest() = ( (* bug *) );;
let upadd x y = ( x +. y);;  (* bug *)
let upmul x y = (x *. y);;
let updiv x y = (x /. y);;
let upsub x y = (x -. y);;
let downadd x y = (x +. y);;
let downmul x y = (x *. y);;
let downdiv x y = (x /. y);;
let downsub x y = (x -. y);;

(* end of bug section *)

let interval_of_string =
  let dbl_min =1.0e-300 in
    fun (s1,s2) ->
      let ( - ) = (down(); downsub) in
      let lo = float_of_string s1 - dbl_min in
      let ( + ) = (up(); upadd) in
      let hi = float_of_string s2 + dbl_min in
        mk_interval(lo,hi);;

let interval_of_single s = interval_of_string (s,s);;

let ineg x = mk_interval(~-. (x.hi), ~-. (x.lo));;

let iadd x y = mk_interval((down(); downadd x.lo  y.lo), (up(); upadd x.hi y.hi));;

let slowcases x y =
  if (x.lo >= 0.0) then
    (if (y.lo >= 0.0) then (x.lo,y.lo,x.hi,y.hi)
    else if (y.hi <= 0.0) then (x.hi,y.lo,x.lo,y.hi ) else (x.hi,y.lo,x.hi,y.hi))
  else if (x.hi <= 0.0) then
    (if (y.hi <= 0.0) then (x.hi,y.hi,x.lo,y.lo)
     else if (y.lo >= 0.0) then (x.lo,y.hi,x.hi,y.lo) else (x.lo,y.hi,x.lo,y.lo))
  else
    (if (y.lo >=0.0) then (x.lo,y.hi,x.hi,y.hi)
     else if (y.hi <=0.0) then (x.hi,y.lo,x.lo,y.lo)
     else (let lo = (down(); min (downmul x.hi  y.lo) (downmul x.lo  y.hi)) in
           let hi = (up(); max (upmul x.hi  y.hi) (upmul x.lo  y.lo)) in (lo,1.0,hi,1.0)));;

let slowmul x y =
  let (xlo,ylo,xhi,yhi) = slowcases x y in
  mk_interval((down(); downmul xlo  ylo),(up(); upmul xhi  yhi));;

let  _ =
  let test_slowmul x y =
    let all = [x.lo *. y.lo; x.hi *. y.lo; x.lo *. y.hi; x.hi *. y.hi] in
    let m = end_itlist min all in
    let M = end_itlist max all in
      ( mk_interval(m,M) = slowmul x  y) in
  let xs = map mk_interval [(~-. 7.0, ~-. 5.0);(~-. 3.0,9.0);(11.0,13.0)] in
  let ys = map mk_interval [(~-. 16.0, ~-. 14.0);(~-. 10.0,12.0); (18.0,22.0)] in
  let test i j = test_slowmul (List.nth xs i) (List.nth ys j) or
    failwith (Printf.sprintf "%d %d" i j) in
    for  i=0 to 2 do
      for j= 0 to 2 do
        let _ = test i j in ();
      done; done;;

let imul x y = if (x.lo > 0.0 && y.lo > 0.0) then
  mk_interval((down(); downmul x.lo  y.lo, (up(); upmul x.hi  y.hi))) else slowmul x y;;

let isub x y = mk_interval((down();downsub x.lo  y.hi),(up(); upsub x.hi  y.lo));;

let isqrt   =
  let sqrt = Pervasives.sqrt in
    fun x -> mk_interval(
  (if (x.lo <= 0.0) then 0.0 else (down(); sqrt(x.lo))),
  (if (x.hi <= 0.0) then 0.0 else (up(); sqrt(x.hi))));;

let iatan x =
  let _ = nearest() in
    mk_interval((down(); atan x.lo),(up(); atan x.hi));;

let iacos x =
  let _ = nearest() in
    mk_interval((down(); acos x.hi),(up(); acos x.lo));;

let combine x y = mk_interval(inf(imin(x,y)),sup(imax(x,y)));;

let rand01 =
  let random_int_seed = 81757 in
  let _ = Random.init(random_int_seed) in
    fun _ -> Random.float(1.0);;

let bounded_from_zero  =
  let  dbl_epsilon = 1.0e-8 in
    fun x-> (x.hi < ~-. dbl_epsilon or  x.lo > dbl_epsilon);;

let idiv x y = if (bounded_from_zero y) then
                     imul x  (mk_interval((down(); downdiv 1.0 y.hi),(up(); updiv 1.0 y.lo)))
                   else raise Unstable;;

(* overload arithmetic ops *)

(*
let (+) = iadd;;
let (-) = isub;;
let (/) = idiv;;
let (~-) = ineg;;
*)

end;;
