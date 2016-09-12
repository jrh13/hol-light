(* ====================================================================== *)
(*  Signs                                                                 *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(*  Datatype                                                              *)
(* ---------------------------------------------------------------------- *)

let sign_INDUCT,sign_RECURSION = define_type
  "sign = Zero | Pos | Neg | Nonzero | Unknown";;

let SIGN_CASES = prove_by_refinement(
  `!s. (s = Pos) \/ (s = Neg) \/ (s = Zero) \/ (s = Nonzero) \/ (s = Unknown)`,
(* {{{ Proof *)
[
  MATCH_MP_TAC sign_INDUCT;
  REWRITE_TAC[];
]);;
(* }}} *)

let szero_tm,spos_tm,sneg_tm,snonz_tm,sunk_tm = `Zero`,`Pos`,`Neg`,`Nonzero`,`Unknown`;;

(* ------------------------------------------------------------------------- *)
(* Intepretation of signs.                                                   *)
(* ------------------------------------------------------------------------- *)

(* An interpretation of the sign of a polynomial over a set. *)
let interpsign = new_recursive_definition sign_RECURSION
  `(interpsign set ply Zero = (!x:real. set x ==> (ply x = &0))) /\
   (interpsign set ply Pos  = (!x. set x ==> (ply x > &0))) /\
   (interpsign set ply Neg  = (!x. set x ==> (ply x < &0))) /\
   (interpsign set ply Nonzero  = (!x. set x ==> (ply x <> &0))) /\
   (interpsign set ply Unknown = (!x. set x ==> (ply x = ply x)))`;;


let interpsign_tm = `interpsign`;;
let dest_interpsign interpthm =
  let int,[set;poly;sign] = strip_ncomb 3 (concl interpthm) in
    if not (int = interpsign_tm) then
      failwith "not an interpsign"
    else
      set,poly,sign;;

(*
let k0 = prove_by_refinement(
  `interpsign (\x. x = &10) (\x. -- &10 + x * &1) Zero`,[
  REWRITE_TAC[interpsign;poly];
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC
]);;

*)

(* A version for one set but multiple polynomials *)
let interpsigns = new_definition
  `interpsigns polyl set signl = ALL2 (interpsign set) polyl signl`;;

let t0 = TAUT `a /\ T <=> a`;;
let interpsigns_thms interpthm =
  let ret = map BETA_RULE(
    CONJUNCTS (PURE_REWRITE_RULE[interpsign;interpsigns;ALL2;t0] interpthm)) in
    ret;;

(* keep interpsign *)
let interpsigns_thms2 interpthm =
  CONJUNCTS (PURE_REWRITE_RULE[interpsigns;ALL2;t0] interpthm);;

let interpsigns_tm = `interpsigns`;;
let dest_interpsigns interpthm =
  let int,[polys;set;signs] = strip_ncomb 3 (concl interpthm) in
    if not (int = interpsigns_tm) then
      failwith "not an interpsigns"
    else
      polys,set,signs;;


let interp_sing = prove(
  `interpsign set p s = interpsigns [p] set [s]`,
  REWRITE_TAC[interpsigns;ALL2]);;

let interp_doub = prove(
  `interpsigns [p1] set [s1] ==> interpsigns pl set sl ==>
     interpsigns (CONS p1 pl) set (CONS s1 sl)`,
  ASM_MESON_TAC[interpsigns;ALL2]);;

let mk_interpsigns thms =
  let thms' = map (PURE_REWRITE_RULE[interp_sing]) thms in
    end_itlist (fun t1 t2 -> MATCH_MPL [interp_doub;t1;t2]) thms';;


(*

let t0 = ASSUME `interpsign s1 p1 Zero`;;
let t1 = ASSUME `interpsign s1 p2 Pos`;;
let t2 = ASSUME `interpsign s1 p3 Neg`;;

mk_interpsigns [t0;t1;t2];;
map (PURE_REWRITE_RULE[interp_sing])  [t0;t1;t2];;
*)


(*
let k0 = prove_by_refinement(
  `interpsigns [(\x. &1 + x * &1); (\x. &2 + x * &3)] (\x. x = (-- &1)) [Zero; Neg]`,
[
  REWRITE_TAC[interpsigns;ALL2;interpsign;poly];
  REAL_ARITH_TAC
]);;
*)

(* ---------------------------------------------------------------------- *)
(*  Partition line                                                        *)
(* ---------------------------------------------------------------------- *)


let partition_line = new_recursive_definition list_RECURSION
  `(partition_line [] = [(\x. T)]) /\
   (partition_line (CONS h t) =
      if t = [] then [(\x. x < h); (\x. x = h); (\x. h < x)] else
        APPEND [(\x. x < h); (\x. x = h); (\x. h < x /\ x < HD t)]
                (TL (partition_line t)))`;;

(*
let ex0 = prove(
  `partition_line [&1] = [(\x. x < &1); (\x. x = &1); (\x. &1 < x)]`,
    REWRITE_TAC[partition_line])

let ex1 = prove(
  `partition_line [&1; &2] =
    [(\x. x < &1); (\x. x = &1); (\x. &1 < x /\ x < &2); (\x. x = &2); (\x. &2 < x)]`,
    REWRITE_TAC[partition_line;APPEND;COND_CLAUSES;NOT_CONS_NIL;TL;HD]);;
*)


let make_partition_list =
  let lxt = `\x:real. T`
  and htm = `h:real`
  and h1tm = `h1:real`
  and h2tm = `h2:real`
  and x_lt_h = `(\x. x < h)`
  and x_eq_h = `(\x:real. x = h)`
  and h_lt_x = `(\x. h < x)`
  and x_lt_h1 = `(\x. x < h1)`
  and x_eq_h1 = `(\x:real. x = h1)`
  and x_h1_h2 = `(\x. h1 < x /\ x < h2)` in
  let rec make_partition_list ps =
    match ps with
      [] -> [lxt]
    | [h] -> map (subst [h,htm]) [x_lt_h; x_eq_h;h_lt_x]
    | h1::h2::t -> (map (subst [(h1,h1tm);(h2,h2tm)])
       [x_lt_h1; x_eq_h1;x_h1_h2]) @ tl (make_partition_list (h2::t)) in
    make_partition_list;;


(*
make_partition_list [`&1`;`&2`]
*)

(* partition a line based on a list of points
   this is just a compact representation of a list of terms
*)
let part_line_tm = `partition_line`;;
let real_bool_ty = `:real->bool`;;
let PARTITION_LINE_CONV pts =
  let ptm = mk_comb (part_line_tm,pts) in
  let ltm = mk_list ((make_partition_list (dest_list pts)),real_bool_ty) in
  let tm = mk_eq (ptm,ltm) in
    prove(tm,REWRITE_TAC [partition_line;APPEND;COND_CLAUSES;NOT_CONS_NIL;TL;HD]);;

(*
PARTITION_LINE_CONV `[]:real list`
PARTITION_LINE_CONV `[&1; &2]`
PARTITION_LINE_CONV `[&2; &1]`
PARTITION_LINE_CONV `[a:real; b]`
*)


(* an interpretation of a sign matrix
   arguments are a list of points, a list of polynomials, and a sign matrix
   the points form an ordered list (smallest first),
   each zero of each polynomial must appear among the list of points
   and finally, the sign matrix corresponds to the correct sign for the polynomial
   in the region represented by the set.
*)
let interpmat = new_definition
  `interpmat ptl polyl signll <=>
    real_ordered_list ptl /\
    ALL2 (interpsigns polyl) (partition_line ptl) signll`;;

let interpmat_tm = `interpmat`;;
let dest_interpmat =
  let imat_tm = interpmat_tm in
  fun tm ->
    let sc,args = strip_comb tm in
      if not (sc = imat_tm) then failwith "dest_interpmat: not an interpmat term" else
      let [ptl;polyl;signll] = args in
        ptl,polyl,signll;;

let interpmat_thms thm =
  let [rol_thm;interpsigns_thm] = CONJUNCTS (PURE_REWRITE_RULE[interpmat] thm) in
    rol_thm,interpsigns_thm;;

let mk_interpmat_thm rol_thm =
    fun all_thm ->
      let ret = REWRITE_RULE[GSYM interpmat] (CONJ rol_thm all_thm) in
      let l,_ = strip_comb (concl ret) in
        if not (l = interpmat_tm) then failwith "mk_interpmat" else ret;;

(*
let rol_thm = rol_thm'''
let all_thm = all_thm''
*)

(* {{{ Doc *)

(*
mk_all2_interpsigns

|- partition_line [x1; x2; x3; x4; x5] =
     [(\x. x < x1); (\x. x = x1); (\x. x1 < x /\ x < x2); (\x. x = x2);
     (\x. x2 < x /\ x < x3); (\x. x = x3); (\x. x3 < x /\ x < x4); (\x. x = x4);
     (\x. x4 < x /\ x < x5); (\x. x = x5); (\x. x5 < x)]

[
 |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x < x1)
      [Unknown; Pos; Pos; Pos]
 .
 .
 .
 .

 |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x = x5)
      [Pos; Pos; Zero; Zero]

 |- interpsigns
      [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]]
      (\x. x5 < x)
      [Unknown; Pos; Pos; Pos]
]

-->

  |- ALL2 (interpsigns [[&1; &1; &1; &1]; [&1; &2; &3]; [&2; -- &3; &1]; [-- &4; &0; &1]])
        (partition_line [x1;x2;x3;x4;x5])
        [[Unknown; Pos; Pos; Pos];...; [Pos; Pos; Zero; Zero]; [Unknown; Pos; Pos; Pos]]

*)

(* }}} *)

let all2_thm0 = GEN_ALL(EQT_ELIM(hd (CONJUNCTS ALL2)));;
let all2_thm = GEN_ALL (REWRITE_RULE[AND_IMP_THM] (fst (EQ_IMP_RULE (GSYM (last (CONJUNCTS ALL2))))));;

let mk_all2_interpsigns part_thm is_thms =
  let is_tm = fst(dest_comb(fst (dest_comb (concl (hd is_thms))))) in
  let all2_thm0' = ISPEC is_tm all2_thm0 in (* it`s having trouble matching *)
  let ret = itlist (fun x -> fun y -> MATCH_MPL[all2_thm;x;y]) is_thms all2_thm0' in
    REWRITE_RULE[GSYM part_thm] ret;;

let dest_all2 tm =
  let a2,l = strip_comb tm in
    if fst(dest_const a2) = "ALL2" then
      let [a1;a2;a3] = l in
        a1,a2,a3
    else
      failwith "dest_all2: not an ALL2";;

(* ---------------------------------------------------------------------- *)
(*  Sets                                                                  *)
(* ---------------------------------------------------------------------- *)

let is_interval set =
  try
    let x,bod = dest_abs set in
    if is_conj bod then
      let l,r = dest_conj bod in
        can (dest_binop rlt) l && can (dest_binop rlt) r
    else can (dest_binop rlt) bod
  with _ -> false;;

(*
is_interval `\x. &4 < x /\ x < &5`;;
is_interval `\x. x = &4`;;
*)

let is_point set =
  try
    let x,bod = dest_abs set in
    if is_eq bod then true else false
  with _ -> false;;

(*
is_point `\x. x = &5`
is_point `\x. x = y:real`
*)

(* ---------------------------------------------------------------------- *)
(*  We generate new var names                                             *)
(* ---------------------------------------------------------------------- *)

let new_var,reset_vars =
  let id = ref 0 in
  let pre = "x_" in
  let new_var ty =
    id := !id + 1;
    mk_var (pre ^ (string_of_int !id),ty) in
  let reset_vars () =
    id := 0 in
    new_var,reset_vars;;
