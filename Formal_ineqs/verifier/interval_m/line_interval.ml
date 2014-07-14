(* =========================================================== *)
(* OCaml linear approximation of functions                     *)
(* Author: Thomas C. Hales                                     *)
(* Date: 2011-08-21                                            *)
(* =========================================================== *)

(* port of lineInterval.cc.
   Only the top section has been translated.  The rest should be
   automatically generated from HOL Light specs.

   This impements basic operations on the type line,
   such as addition and scalar multiplication.

 *)

needs "verifier/interval_m/interval.ml";;

module Line_interval = struct

open Interval_types;;
open List;;
open Interval;;


(* general utilities *)
  let iter8 = 0--7;;

  let table f = map f iter8;;

  let table2 f = map (fun i -> map (fun j-> f i j) iter8) iter8;;

  let rth m x i  = if (i >=0) && (i < m) then List.nth x i else
                      failwith (Printf.sprintf "index %d not in 0..%d" i (m-1));;

  let mth x i =  if (i >=0) && (i < 8) then List.nth x i else
                      failwith (Printf.sprintf "index %d not in 0..8" i );;

  let mth2 a i j = mth (mth a i) j;;

  let maxl xs = end_itlist max xs;;

  let minl xs = end_itlist min xs;;

(* line interval proper *)

let partial line i = mth line.df i ;;

let mk_line(f1,df1) = { f = f1; df =df1};;

let line_zero =
  let z = zero in
  mk_line(z,replicate z 8);;

let line_unit =
  mk_line(one,replicate zero 8);;

let lmul =
  let ( * ) = imul in
  let ( + ) = iadd in
  fun a b -> mk_line ( a.f * b.f, map (fun i -> a.f * mth b.df i + b.f * mth a.df i) iter8);;

let smul =
  let ( * ) = imul in
  fun a b -> mk_line ( a.f * b, map (fun x -> x * b) a.df);;

let ldiv =
  let one = mk_interval(1.0,1.0) in
  let ( * ) = imul in
  let ( - ) = isub in
  let ( / ) = idiv in
  fun b a ->
    let r = one/a.f in
    let f = b.f * r in
    let r2 = r * r in
    mk_line ( f, map (fun i -> ((mth b.df i) * a.f - (mth a.df i) * b.f)* r2) iter8);;

let ladd =
  let ( + ) = iadd in
    fun b a ->
      mk_line(b.f + a.f, map (fun i -> mth b.df i + mth a.df i) iter8);;

let lsub =
  let ( - ) = isub in
    fun b a ->
      mk_line(b.f - a.f, map (fun i -> mth b.df i - mth a.df i) iter8);;

let lneg =
  let ineg = ineg in
    fun a ->
      mk_line(ineg a.f, map ineg a.df);;

let lsqrt =
  let one = mk_interval(1.0,1.0) in
  let two = mk_interval(2.0,2.0) in
  let ( * ) = imul in
  let ( / ) = idiv in
  fun a ->
    let f = isqrt a.f in
    let rs = one / (two * f) in
      mk_line(f, map (fun i -> mth a.df i * rs) iter8);;

let latan = (* arctan (a/b) *)
  let one = mk_interval(1.0,1.0) in
  let ( * ) = imul in
  let ( + ) = iadd in
  let ( - ) = isub in
  let ( / ) = idiv in
  fun a b ->
    let f = iatan (a.f/b.f) in
    let rden = one/ (a.f * a.f + b.f * b.f) in
      mk_line(f, map (fun i -> rden * (mth a.df i * b.f - mth b.df i * a.f)) iter8);;


 end;;
