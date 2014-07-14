(* =========================================================== *)
(* OCaml taylor intervals                                      *)
(* Author: Thomas C. Hales                                     *)
(* Date: 2011-08-21                                            *)
(* Modified: Alexey Solovyev, 2012-10-27                       *)
(* =========================================================== *)

(* port of taylor functions, taylor interval *)

(*
The first part of the file implements basic operations on type taylor_interval.

Then a type tfunction is defined that represents a twice continuously
differentiable function of six variables.  It can be evaluated, which
is the taylor_interval data associated with it.

Sometimes a tfunction f is used to represent an inequality f < 0.
(See recurse.hl.
*)

needs "verifier/interval_m/line_interval.ml";;
needs "verifier/interval_m/univariate.ml";;

module Taylor = struct

open Interval_types;;
open Interval;;
open Univariate;;
open Line_interval;;


(* general utilities *)

let m8_sum =
  let ( + ) = iadd in
    fun dd1 dd2 ->
      let r8_sum (x,y) = table (fun i -> mth x i + mth y i)  in
        map r8_sum (zip dd1 dd2);;

let center_form(x,z) =
  let ( + ) , ( - ), ( / ) = up(); upadd,upsub,updiv in
  let y = table (fun i -> if (mth x i=mth z i) then mth x i else (mth x i + mth z i)/ 2.0)  in
  let w = table (fun i -> max (mth z i - mth y i) (mth y i - mth x i))  in
  let _ = (minl w >= 0.0) or failwith "centerform" in
     (y,w);;

(* start with taylor interval operations *)

let make_taylor_interval (l1,w1,dd1) = {l = l1; w = w1; dd=dd1;};;

let ti_add (ti1,ti2) =
  let _ = (ti1.w = ti2.w) or failwith ("width mismatch in ti") in
    make_taylor_interval( ladd ti1.l ti2.l,ti1.w, m8_sum ti1.dd ti2.dd);;

let ti_scale (ti,t) =
   make_taylor_interval( smul ti.l t,ti.w,  table2 (fun i j ->  imul (mth2 ti.dd i j) t));;



let taylor_error ti =
  let ( + ), ( * ) , ( / )= up(); upadd, upmul, updiv in
  let dot_abs_row r = List.fold_left2 (fun a b c -> a + b * iabs c) 0.0 ti.w r in
  let dots = map dot_abs_row (ti.dd) in
    (List.fold_left2 (fun a b c -> a + b * c) 0.0 ti.w dots) / 2.0;;
(*  (end_itlist ( + ) p) / 2.0 ;; *)

let upper_bound ti =
  let e = taylor_error ti in
  let ( + ), ( * ) = up(); upadd, upmul in
  let t = ti.l.f.hi + e in
    t + List.fold_left2 (fun a b c -> a + b * iabs c) 0.0 ti.w ti.l.df;;

let lower_bound ti =
  let e = taylor_error ti in
  let ( + ), ( * ),(- ) = down(); downadd,downmul,downsub in
  let t = ti.l.f.lo - e in
    t + List.fold_left2 (fun a b c -> a + ( ~-. b) * iabs c) 0.0 ti.w ti.l.df;;

let upper_partial ti i =
  let ( + ), ( * ) =   up(); upadd,upmul in
    let err = List.fold_left2 (fun a b c -> a + b*(max c.hi (~-. (c.lo))))
      0.0 ti.w (mth ti.dd i) in
      err + Interval.sup ( mth ti.l.df i);;

let lower_partial ti i =
  let ( + ), ( * ), ( - ) = down();downadd,downmul,downsub in
    let err = List.fold_left2 (fun a b c -> a + b * min c.lo (~-. (c.hi)))
      0.0 ti.w (mth ti.dd i) in
      Interval.inf ( mth ti.l.df i) + err;;


let ti_mul (ti1,ti2) =
  let _ = (ti1.w = ti2.w) or failwith ("ti_mul: width mismatch in ti") in
  let line = lmul ti1.l ti2.l in
  let f1_int =
    let lo, hi = lower_bound ti1, upper_bound ti1 in mk_interval (lo, hi) in
  let f2_int =
    let lo, hi = lower_bound ti2, upper_bound ti2 in mk_interval (lo, hi) in
  let d1_ints = table (fun i -> mk_interval (lower_partial ti1 i, upper_partial ti1 i)) in
  let d2_ints = table (fun i -> mk_interval (lower_partial ti2 i, upper_partial ti2 i)) in
  let dd = table2 (fun i j ->
                     let ( + ), ( * ) = iadd, imul in
                       mth2 ti1.dd i j * f2_int + mth d1_ints i * mth d2_ints j +
                         mth d1_ints j * mth d2_ints i + f1_int * mth2 ti2.dd i j) in
    make_taylor_interval(line, ti1.w, dd);;



(* primitive A *)

type primitiveA = {
  f_df : int -> float list -> float list -> interval;
  hfn : float list -> line;
  second : float list -> float list -> interval list list;
};;

let make_primitiveA (f,h1,s1) = {f_df = f; hfn = h1; second = s1; };;

let unitA =
  let zero2 = table2 (fun i j -> zero) in
    make_primitiveA (
      (fun i x z -> if i = 0 then one else zero),
      (fun y -> line_unit),
      (fun x z -> zero2)
);;

let evalf4A pA w x y z =
  make_taylor_interval(
    pA.hfn y,
    w,
    pA.second x z
  );;

let line_estimateA pA y = pA.hfn y;;

(* primitive U *)

type primitiveU = {
  slot: int;
  uv: univariate;
};;

let mk_primitiveU s1 uv1 =
  let _ = (s1 < 8) or failwith (Printf.sprintf "slot %d" s1) in
    { slot = s1; uv = uv1; };;

let line_estimateU p y =
  let y0 = mth y p.slot in
  let t = mk_interval(y0,y0) in
  let d = table (fun i -> if (i=p.slot) then eval p.uv t 1 else zero)  in
    mk_line (    eval p.uv t 0,    d  );;

let evalf4U =
  let row0 = table (fun i -> zero)  in
    fun p w x y z ->
      let t = mk_interval(mth x p.slot,mth z p.slot) in
      let row_slot = table  (fun i -> if (i=p.slot) then eval p.uv t 2 else zero)  in
      let dd = table (fun i -> if (i=p.slot) then row_slot else row0)  in
      make_taylor_interval(
        line_estimateU p y,
        w,
        dd
      );;

type tfunction =
  | Prim_a of primitiveA
  | Uni of primitiveU
  | Plus of tfunction * tfunction
  | Product of tfunction * tfunction
  | Scale of tfunction * interval
  | Uni_compose of univariate * tfunction
  | Composite of tfunction *  (* F(g1,g2,g3,g4,g5,g6,g7,g8) *)
      tfunction *tfunction *tfunction *
      tfunction *tfunction *tfunction *
      tfunction *tfunction;;

let unit = Prim_a unitA;;

let x1 = Uni (mk_primitiveU 0 ux1);;
let x2 = Uni (mk_primitiveU 1 ux1);;
let x3 = Uni (mk_primitiveU 2 ux1);;
let x4 = Uni (mk_primitiveU 3 ux1);;
let x5 = Uni (mk_primitiveU 4 ux1);;
let x6 = Uni (mk_primitiveU 5 ux1);;


let x1x2 =
  let tab2 = table2 (fun i j -> if (i+j=1) then one else zero) in
    Prim_a (make_primitiveA(
              (fun i x z ->
                 let x1 = mk_interval (mth x 0, mth z 0) in
                 let x2 = mk_interval (mth x 1, mth z 1) in
                   if i = 0 then imul x1 x2
                   else if i = 1 then x2
                   else if i = 2 then x1
                   else zero),
              (fun y ->
                 let u1 = mth y 0 in
                 let u2 = mth y 1 in
                 let x1 = mk_interval(u1,u1) in
                 let x2 = mk_interval(u2,u2) in
                   mk_line(
                     imul x1 x2,
                     table (fun i -> if i=0 then x2 else if i=1 then x1 else zero)
                   )),
              (fun x z -> tab2)));;

let tf_product tf1 tf2 = Composite(x1x2,tf1,tf2,unit,unit,unit,unit,unit,unit);;


(* This is one of the most difficult functions in the interval code.
   It uses the chain rule to compute the second partial derivatives with
   respect to x(i) x(j), of a function composition

   F(x1,...,x6) = f(g1(x1,...x6),g2(x1,...x6),...,g6(x1,...x6)).

   (F i j) = sum {k m} (f k m) (gk i) (gm j)     + sum {r} (f r) (gr i j).

   Fast performance of this function is very important, especially
   when many of the functions g* are constant.
   There is a bit of imperative programming here, in computing the sums.

   Note that ( + ) and ( * ) have different types in various subsections.
*)

let eval_composite =
  let rest = () in
  let  sparse_table h f = filter h (List.flatten (table2 f)) in
    fun hdr p1 p2 p3 p4 p5 p6 p7 p8 w ->
      let p = [p1;p2;p3;p4;p5;p6;p7;p8] in
        (* wide and narrow ranges of p *)
      let (aw,bw) = map (lower_bound) p, map (upper_bound) p  in
      let (a,b) = map (fun p -> p.l.f.lo) p, map (fun p -> p.l.f.hi) p in
        (* wide and narrow widths from a to b *)
      let (u,wu,wf) =
        let ( + ),( - ),( / ) = up();upadd,upsub,updiv in
        let u = table (fun i -> (mth a i + mth b i) / 2.0)  in
        let wu = table (fun i -> max (mth bw i - mth u i) (mth u i - mth aw i))  in
        let wf = table (fun i -> max (mth b i - mth u i) (mth u i - mth a i))  in
          (u,wu,wf) in
      let (fu:taylor_interval) = hdr wu aw u bw in
      let fpy =
        let t = make_taylor_interval(fu.l,wf,fu.dd) in
          mk_line (
            mk_interval(lower_bound t, upper_bound t),
            table (fun i -> mk_interval(lower_partial t i,upper_partial t i))  ) in
        (* use chain rule imperatively to compute narrow first derivative *)
      let df_tmp = Array.create 8 zero in
      let ( + ) = iadd in
      let ( * ) = imul in
      let _ = for j=0 to 7 do
        let dfj = mth fpy.df j in
          if is_zero dfj then rest
          else for i=0 to 7 do
            let r = mth (mth p j).l.df i in
              if (is_zero r) then rest else df_tmp.(i) <- df_tmp.(i) + dfj * r;
          done;
      done in
      let lin = mk_line (       fpy.f, Array.to_list df_tmp ) in
        (* second derivative init *)
      let fW_partial = table (fun i -> mk_interval(lower_partial fu i,upper_partial fu i)) in
      let pW_partial = sparse_table (fun (_,_,z) ->not (is_zero z))
        (fun k i -> (k,i,(mk_interval(lower_partial (mth p k) i,upper_partial (mth p k) i)))) in
        (* chain rule 4-nested loop!, but flattened with sparse table *)
      let dcw = Array.make_matrix 8 8 zero in
      let _ = for i=0 to 7 do for j=0 to 7 do for k=0 to 7 do
        if (is_zero (mth2 (mth p k).dd i j)) then rest
        else dcw.(i).(j) <- dcw.(i).(j) + mth fW_partial k * mth2 ((mth p k).dd) i j ;
      done; done; done in
      let len = List.length pW_partial in
      let _ = for ki = 0 to len-1 do
        let (k,i,rki) = List.nth pW_partial ki in
          for mj=0 to len-1 do
            let (m,j,rmj) = List.nth pW_partial mj in
(*            Report.report (Printf.sprintf "k i m j rki rmj fuddkm = %d %d %d %d %f %f %f" k i m j rki.lo rmj.lo (mth2 fu.dd k m).lo); *)
              dcw.(i).(j) <- dcw.(i).(j) +  mth2 fu.dd k m * rki * rmj; (* innermost loop *)
          done; done in
      let dcw_list =  map Array.to_list (Array.to_list dcw) in
        make_taylor_interval(lin,w,dcw_list);;

let rec evalf4 tf w x y z = match tf with
  | Prim_a p -> evalf4A p w x y z
  | Uni p -> evalf4U p w x y z
  | Plus (tf1,tf2) -> ti_add(evalf4 tf1 w x y z, evalf4 tf2 w x y z)
  | Product (tf1,tf2) -> ti_mul(evalf4 tf1 w x y z, evalf4 tf2 w x y z)
  | Composite(h,g1,g2,g3,g4,g5,g6,g7,g8) ->
      let [p1;p2;p3;p4;p5;p6;p7;p8] = map (fun t-> evalf4 t w x y z) [g1;g2;g3;g4;g5;g6;g7;g8] in
        eval_composite (evalf4 h) p1 p2 p3 p4 p5 p6 p7 p8 w
  | Scale (tf,t) -> ti_scale ((evalf4 tf w x y z),t)
  | Uni_compose (uf,tf) ->
      let ti = evalf4 tf w x y z in
      let fy = ti.l.f in
      let u_fy = uf.u fy in
      let du_fy = uf.du fy in
      let line =
        let ( * ) = imul in
          mk_line (u_fy, table (fun i -> du_fy * mth ti.l.df i)) in
      let fx = mk_interval (lower_bound ti, upper_bound ti) in
      let dfx = table (fun i -> mk_interval (lower_partial ti i, upper_partial ti i)) in
      let du_fx = uf.du fx in
      let ddu_fx = uf.ddu fx in
      let dd = table2 (fun i j ->
                         let ( + ), ( * ) = iadd, imul in
                           (ddu_fx * mth dfx j) * mth dfx i + du_fx * mth2 ti.dd j i) in
        make_taylor_interval(line, w, dd);;



(*      evalf4 (Composite(Uni (mk_primitiveU 0 uf),tf,unit,unit,unit,unit,unit,unit,unit)) w x y z;; *)

let evalf tf x z =
  let (y,w) = center_form (x,z) in
    evalf4 tf w x y z;;


(* Evaluates a function (i = 0) and its first derivatives (i = 1, 2, ...) at the given interval *)
let rec evalf0 tf i x z = match tf with
  | Prim_a p -> p.f_df i x z
  | Uni p ->
      let int = mk_interval (mth x p.slot, mth z p.slot) in
        if i = 0 then eval p.uv int 0
        else if i = p.slot + 1 then eval p.uv int 1
        else zero
  | Plus (tf1, tf2) -> iadd (evalf0 tf1 i x z) (evalf0 tf2 i x z)
  | Product (tf1, tf2) ->
      let itf1, itf2 = evalf0 tf1 0 x z, evalf0 tf2 0 x z in
        if i = 0 then imul itf1 itf2
        else
          let i_df1, i_df2 = evalf0 tf1 i x z, evalf0 tf2 i x z in
            iadd (imul i_df1 itf2) (imul itf1 i_df2)
  | Scale (tf, t) -> imul (evalf0 tf i x z) t
  | Uni_compose (uf, tf) ->
      let itf = evalf0 tf 0 x z in
        if i = 0 then eval uf itf 0
        else
          let i_df = evalf0 tf i x z in
            imul (eval uf itf 1) i_df
  | Composite (h,g1,g2,g3,g4,g5,g6,g7,g8) ->
      let gs = [g1;g2;g3;g4;g5;g6;g7;g8] in
      let ps = map (fun t -> let int = evalf0 t 0 x z in int.lo, int.hi) gs in
      let x', z' = unzip ps in
        if i = 0 then evalf0 h 0 x' z'
        else
          let dhs = table (fun j -> evalf0 h (j + 1) x' z') in
          let dgs = map (fun t -> evalf0 t i x z) gs in
          let ( + ), ( * ) = iadd, imul in
            itlist2 (fun a b c -> a * b + c) dhs dgs zero;;


(*
let line_estimate_composite =
  let ( + ) = iadd in
  let ( * ) = imul in
    fun h p1 p2 p3 p4 p5 p6 p7 p8 ->
      let p =  [p1;p2;p3;p4;p5;p6;p7;p8] in
      let (a,b) = map (fun p -> p.f.lo) p, map (fun p -> p.f.hi) p in
      let fN = evalf h a b in
      let fN_partial = table (fun i -> mk_interval(lower_partial fN i,upper_partial fN i)) in
      let pN_partial =table2(fun i j-> (mth (mth p i).df j)) in
      let cN_partial2 = table2 (fun i j -> mth fN_partial j * mth2 pN_partial j i) in
      let cN_partial = map (end_itlist ( + )) cN_partial2 in
        mk_line ( fN.l.f, cN_partial );;

let rec line_estimate tf y = match tf with
  | Prim_a p -> line_estimateA p y
  | Uni p -> line_estimateU p y
  | Plus (p,q) -> ladd (line_estimate p y) (line_estimate q y)
  | Scale (p,t) -> smul (line_estimate p y) t
  | Uni_compose (uf,tf) ->
      line_estimate (Composite(Uni { slot=0; uv=uf; },tf,unit,unit,unit,unit,unit,unit,unit)) y
  | Composite(h,g1,g2,g3,g4,g5,g6,g7,g8) ->
      let [p1;p2;p3;p4;p5;p6;p7;p8] = map (fun t-> line_estimate t y) [g1;g2;g3;g4;g5;g6;g7;g8] in
        line_estimate_composite h p1 p2 p3 p4 p5 p6 p7 p8;;
*)

end;;
