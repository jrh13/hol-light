(* ========================================================================= *)
(* Grobner basis algorithm.                                                  *)
(* ========================================================================= *)

needs "Complex/complexnumbers.ml";;
needs "Complex/quelim.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Utility functions.                                                        *)
(* ------------------------------------------------------------------------- *)

let allpairs f l1 l2 =
  itlist ((@) o C map l2 o f) l1 [];;

let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

let sort ord =
  let rec mergepairs l1 l2 =
    match (l1,l2) with
        ([s],[]) -> s
      | (l,[]) -> mergepairs [] l
      | (l,[s1]) -> mergepairs (s1::l) []
      | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;

(* ------------------------------------------------------------------------- *)
(* Type for recording history, i.e. how a polynomial was obtained.           *)
(* ------------------------------------------------------------------------- *)

type history =
   Start of int
 | Mmul of (num * (int list)) * history
 | Add of history * history;;

(* ------------------------------------------------------------------------- *)
(* Conversion of leaves, i.e. variables and constant rational constants.     *)
(* ------------------------------------------------------------------------- *)

let grob_var vars tm =
  let res = map (fun i -> if i = tm then 1 else 0) vars in
  if exists (fun x -> x <> 0) res then [Num.num_of_int 1,res] else failwith "grob_var";;

let grob_const =
  let cx_tm = `Cx` in
  fun vars tm ->
    try let l,r = dest_comb tm in
        if l = cx_tm then
          let x = rat_of_term r in
          if x =/ Num.num_of_int 0 then [] else [x,map (fun v -> 0) vars]
        else failwith ""
    with Failure _ -> failwith "grob_const";;

(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt =
  let rec lexorder l1 l2 =
    match (l1,l2) with
        [],[] -> false
      | (x1::o1,x2::o2) -> x1 > x2 || x1 = x2 && lexorder o1 o2
      | _ -> failwith "morder: inconsistent monomial lengths" in
  fun m1 m2 -> let n1 = itlist (+) m1 0
               and n2 = itlist (+) m2 0 in
               n1 < n2 || n1 = n2 && lexorder m1 m2;;

let morder_le m1 m2 = morder_lt m1 m2 || (m1 = m2);;

let morder_gt m1 m2 = morder_lt m2 m1;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical polynomials.                                      *)
(* ------------------------------------------------------------------------- *)

let grob_neg = map (fun (c,m) -> (minus_num c,m));;

let rec grob_add l1 l2 =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
        if m1 = m2 then
          let c = c1+/c2 and rest = grob_add o1 o2 in
          if c =/ Num.num_of_int 0 then rest else (c,m1)::rest
        else if morder_lt m2 m1 then (c1,m1)::(grob_add o1 l2)
        else (c2,m2)::(grob_add l1 o2);;

let grob_sub l1 l2 = grob_add l1 (grob_neg l2);;

let grob_mmul (c1,m1) (c2,m2) = (c1*/c2,map2 (+) m1 m2);;

let rec grob_cmul cm pol = map (grob_mmul cm) pol;;

let rec grob_mul l1 l2 =
  match l1 with
    [] -> []
  | (h1::t1) -> grob_add (grob_cmul h1 l2) (grob_mul t1 l2);;

let rec grob_pow vars l n =
  if n < 0 then failwith "grob_pow: negative power"
  else if n = 0 then [Num.num_of_int 1,map (fun v -> 0) vars]
  else grob_mul l (grob_pow vars l (n - 1));;

(* ------------------------------------------------------------------------- *)
(* Monomial division operation.                                              *)
(* ------------------------------------------------------------------------- *)

let mdiv (c1,m1) (c2,m2) =
  (c1//c2,
   map2 (fun n1 n2 -> if n1 < n2 then failwith "mdiv" else n1-n2) m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Lowest common multiple of two monomials.                                  *)
(* ------------------------------------------------------------------------- *)

let mlcm (c1,m1) (c2,m2) = (Num.num_of_int 1,map2 max m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 cm (pol,hpol) =
  match pol with
    [] -> failwith "reduce1"
  | cm1::cms -> try let (c,m) = mdiv cm cm1 in
                    (grob_cmul (minus_num c,m) cms,
                     Mmul((minus_num c,m),hpol))
                with Failure _ -> failwith "reduce1";;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb cm basis = tryfind (fun p -> reduce1 cm p) basis;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce basis (pol,hist) =
  match pol with
    [] -> (pol,hist)
  | cm::ptl -> try let q,hnew = reduceb cm basis in
                   reduce basis (grob_add q ptl,Add(hnew,hist))
               with Failure _ ->
                   let q,hist' = reduce basis (ptl,hist) in
                   cm::q,hist';;

(* ------------------------------------------------------------------------- *)
(* Check for orthogonality w.r.t. LCM.                                       *)
(* ------------------------------------------------------------------------- *)

let orthogonal l p1 p2 =
  snd l = snd(grob_mmul (hd p1) (hd p2));;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly cm ph1 ph2 =
  match (ph1,ph2) with
    ([],h),p -> ([],h)
  | p,([],h) -> ([],h)
  | (cm1::ptl1,his1),(cm2::ptl2,his2) ->
        (grob_sub (grob_cmul (mdiv cm cm1) ptl1)
                  (grob_cmul (mdiv cm cm2) ptl2),
         Add(Mmul(mdiv cm cm1,his1),
             Mmul(mdiv (minus_num(fst cm),snd cm) cm2,his2)));;

(* ------------------------------------------------------------------------- *)
(* Make a polynomial monic.                                                  *)
(* ------------------------------------------------------------------------- *)

let monic (pol,hist) =
  if pol = [] then (pol,hist) else
  let c',m' = hd pol in
  (map (fun (c,m) -> (c//c',m)) pol,
   Mmul((Num.num_of_int 1 // c',map (K 0) m'),hist));;

(* ------------------------------------------------------------------------- *)
(* The most popular heuristic is to order critical pairs by LCM monomial.    *)
(* ------------------------------------------------------------------------- *)

let forder ((c1,m1),_) ((c2,m2),_) = morder_lt m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Stupid stuff forced on us by lack of equality test on num type.           *)
(* ------------------------------------------------------------------------- *)

let rec poly_lt p q =
  match (p,q) with
    p,[] -> false
  | [],q -> true
  | (c1,m1)::o1,(c2,m2)::o2 ->
        c1 </ c2 ||
        c1 =/ c2 && (m1 < m2 || m1 = m2 && poly_lt o1 o2);;

let align ((p,hp),(q,hq)) =
  if poly_lt p q then ((p,hp),(q,hq)) else ((q,hq),(p,hp));;

let poly_eq p1 p2 =
  forall2 (fun (c1,m1) (c2,m2) -> c1 =/ c2 && m1 = m2) p1 p2;;

let memx ((p1,h1),(p2,h2)) ppairs =
  not (exists (fun ((q1,_),(q2,_)) -> poly_eq p1 q1 && poly_eq p2 q2) ppairs);;

(* ------------------------------------------------------------------------- *)
(* Buchberger's second criterion.                                            *)
(* ------------------------------------------------------------------------- *)

let criterion2 basis (lcm,((p1,h1),(p2,h2))) opairs =
  exists (fun g -> not(poly_eq (fst g) p1) && not(poly_eq (fst g) p2) &&
                   can (mdiv lcm) (hd(fst g)) &&
                   not(memx (align(g,(p1,h1))) (map snd opairs)) &&
                   not(memx (align(g,(p2,h2))) (map snd opairs))) basis;;

(* ------------------------------------------------------------------------- *)
(* Test for hitting constant polynomial.                                     *)
(* ------------------------------------------------------------------------- *)

let constant_poly p =
  length p = 1 && forall ((=) 0) (snd(hd p));;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec grobner histories basis pairs =
  print_string(string_of_int(length basis)^" basis elements and "^
               string_of_int(length pairs)^" critical pairs");
  print_newline();
  match pairs with
    [] -> rev histories,basis
  | (l,(p1,p2))::opairs ->
        let (sp,hist) = monic (reduce basis (spoly l p1 p2)) in
        if sp = [] || criterion2 basis (l,(p1,p2)) opairs
        then grobner histories basis opairs else
        let sph = sp,Start(length histories) in
        if constant_poly sp
        then grobner ((sp,hist)::histories) (sph::basis) [] else
        let rawcps =
          map (fun p -> mlcm (hd(fst p)) (hd sp),align(p,sph)) basis in
        let newcps = filter
          (fun (l,(p,q)) -> not(orthogonal l (fst p) (fst q))) rawcps in
        grobner ((sp,hist)::histories) (sph::basis)
                (merge forder opairs (sort forder newcps));;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner pols =
  let npols = map2 (fun p n -> p,Start n) pols (0--(length pols - 1)) in
  let phists = filter (fun (p,_) -> p <> []) npols in
  let bas0 = map monic phists in
  let bas = map2 (fun (p,h) n -> p,Start n) bas0
                 ((length bas0)--(2 * length bas0 - 1)) in
  let prs0 = allpairs (fun x y -> x,y) bas bas in
  let prs1 = filter (fun ((x,_),(y,_)) -> poly_lt x y) prs0 in
  let prs2 = map (fun (p,q) -> mlcm (hd(fst p)) (hd(fst q)),(p,q)) prs1 in
  let prs3 = filter (fun (l,(p,q)) -> not(orthogonal l (fst p) (fst q))) prs2 in
  grobner (rev bas0 @ rev phists) bas (mergesort forder prs3);;

(* ------------------------------------------------------------------------- *)
(* Alternative orthography.                                                  *)
(* ------------------------------------------------------------------------- *)

let gr'o'bner = groebner;;

(* ------------------------------------------------------------------------- *)
(* Conversion from HOL term.                                                 *)
(* ------------------------------------------------------------------------- *)

let grobify_term =
  let neg_tm = `(--):complex->complex`
  and add_tm = `(+):complex->complex->complex`
  and sub_tm = `(-):complex->complex->complex`
  and mul_tm = `(*):complex->complex->complex`
  and pow_tm = `(pow):complex->num->complex` in
  let rec grobify_term vars tm =
    try grob_var vars tm with Failure _ ->
    try grob_const vars tm with Failure _ ->
    let lop,r = dest_comb tm in
    if lop = neg_tm then grob_neg(grobify_term vars r) else
    let op,l = dest_comb lop in
    if op = pow_tm then
      grob_pow vars (grobify_term vars l) (dest_small_numeral r)
    else
     (if op = add_tm then grob_add else if op = sub_tm then grob_sub
      else if op = mul_tm then grob_mul else failwith "unknown term")
     (grobify_term vars l) (grobify_term vars r) in
  fun vars tm ->
    try grobify_term vars tm with Failure _ -> failwith "grobify_term";;

let grobvars =
  let neg_tm = `(--):complex->complex`
  and add_tm = `(+):complex->complex->complex`
  and sub_tm = `(-):complex->complex->complex`
  and mul_tm = `(*):complex->complex->complex`
  and pow_tm = `(pow):complex->num->complex` in
  let rec grobvars tm acc =
    if is_complex_const tm then acc
    else if not (is_comb tm) then tm::acc else
    let lop,r = dest_comb tm in
    if lop = neg_tm then grobvars r acc
    else if not (is_comb lop) then tm::acc else
    let op,l = dest_comb lop in
    if op = pow_tm then grobvars l acc
    else if op = mul_tm || op = sub_tm || op = add_tm
    then grobvars l (grobvars r acc)
    else tm::acc in
  fun tm -> setify(grobvars tm []);;

let grobify_equations =
  let zero_tm = `Cx(&0)`
  and sub_tm = `(-):complex->complex->complex`
  and complex_ty = `:complex` in
  let grobify_equation vars tm =
  let l,r = dest_eq tm in
    if r <> zero_tm then grobify_term vars (mk_comb(mk_comb(sub_tm,l),r))
    else grobify_term vars l in
  fun tm ->
    let cjs = conjuncts tm in
    let rawvars = itlist
       (fun eq acc -> let l,r = dest_eq eq in
                     union (union (grobvars l) (grobvars r)) acc) cjs [] in
    let vars = sort (fun x y -> x < y) rawvars in
    vars,map(grobify_equation vars) cjs;;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let string_of_monomial vars (c,m) =
  let xns = filter (fun (x,y) -> y <> 0) (map2 (fun x y -> x,y) vars m) in
  let xnstrs = map
    (fun (x,n) -> x^(if n = 1 then "" else "^"^(string_of_int n))) xns in
  if xns = [] then Num.string_of_num c else
  let basstr = if c =/ Num.num_of_int 1 then "" else (Num.string_of_num c)^" * " in
  basstr ^ end_itlist (fun s t -> s^" * "^t) xnstrs;;

let string_of_polynomial vars l =
  if l = [] then "0" else
  end_itlist (fun s t -> s^" + "^t) (map (string_of_monomial vars) l);;

(* ------------------------------------------------------------------------- *)
(* Resolve a proof.                                                          *)
(* ------------------------------------------------------------------------- *)

let rec resolve_proof vars prf =
  match prf with
    Start n ->
        [n,[Num.num_of_int 1,map (K 0) vars]]
  | Mmul(pol,lin) ->
        let lis = resolve_proof vars lin in
        map (fun (n,p) -> n,grob_cmul pol p) lis
  | Add(lin1,lin2) ->
        let lis1 = resolve_proof vars lin1
        and lis2 = resolve_proof vars lin2 in
        let dom = setify(union (map fst lis1) (map fst lis2)) in
        map (fun n -> let a = try assoc n lis1 with Failure _ -> []
                      and b = try assoc n lis2 with Failure _ -> [] in
                      n,grob_add a b) dom;;

(* ------------------------------------------------------------------------- *)
(* Convert a polynomial back to HOL.                                         *)
(* ------------------------------------------------------------------------- *)

let holify_polynomial =
  let complex_ty = `:complex`
  and pow_tm = `(pow):complex->num->complex`
  and mk_mul = mk_binop `(*):complex->complex->complex`
  and mk_add = mk_binop `(+):complex->complex->complex`
  and zero_tm = `Cx(&0)`
  and add_tm = `(+):complex->complex->complex`
  and mul_tm = `(*):complex->complex->complex`
  and complex_term_of_rat = curry mk_comb `Cx` o term_of_rat in
  let holify_varpow (v,n) =
    if n = 1 then v
    else list_mk_comb(pow_tm,[v;mk_small_numeral n]) in
  let holify_monomial vars (c,m) =
    let xps = map holify_varpow (filter (fun (_,n) -> n <> 0) (zip vars m)) in
    end_itlist mk_mul (complex_term_of_rat c :: xps) in
  let holify_polynomial vars p =
    if p = [] then zero_tm
    else end_itlist mk_add (map (holify_monomial vars) p) in
  holify_polynomial;;

(* ------------------------------------------------------------------------- *)
(* Recursively find the set of basis elements involved.                      *)
(* ------------------------------------------------------------------------- *)

let dependencies =
  let rec dependencies prf acc =
    match prf with
      Start n -> n::acc
    | Mmul(pol,lin) -> dependencies lin acc
    | Add(lin1,lin2) -> dependencies lin1 (dependencies lin2 acc) in
  fun prf -> setify(dependencies prf []);;

let rec involved deps sofar todo =
  match todo with
    [] -> sort (<) sofar
  | (h::hs) ->
        if mem h sofar then involved deps sofar hs
        else involved deps (h::sofar) (el h deps @ hs);;

(* ------------------------------------------------------------------------- *)
(* Refute a conjunction of equations in HOL.                                 *)
(* ------------------------------------------------------------------------- *)

let GROBNER_REFUTE =
  let add_tm = `(+):complex->complex->complex`
  and mul_tm = `(*):complex->complex->complex` in
  let APPLY_pth = MATCH_MP(SIMPLE_COMPLEX_ARITH
    `(x = y) ==> (x + Cx(--(&1)) * (y + Cx(&1)) = Cx(&0)) ==> F`)
  and MK_ADD th1 th2 = MK_COMB(AP_TERM add_tm th1,th2) in
  let rec holify_lincombs vars cjs prfs =
    match prfs with
      [] -> cjs
    | (p::ps) ->
        if p = [] then holify_lincombs vars (cjs @ [TRUTH]) ps else
        let holis = map (fun (n,q) -> n,holify_polynomial vars q) p in
        let ths =
          map (fun (n,m) -> AP_TERM (mk_comb(mul_tm,m)) (el n cjs)) holis in
        let th = CONV_RULE(BINOP_CONV COMPLEX_POLY_CONV)
                          (end_itlist MK_ADD ths) in
        holify_lincombs vars (cjs @ [th]) ps in
  fun tm ->
    let vars,pols = grobify_equations tm in
    let (prfs,gb) = groebner pols in
    let (_,prf) =
      find (fun (p,h) -> length p = 1 && forall ((=)0) (snd(hd p))) gb in
    let deps = map (dependencies o snd) prfs
    and depl = dependencies prf in
    let need = involved deps [] depl in
    let pprfs =
      map2 (fun p n -> if mem n need then resolve_proof vars (snd p) else [])
           prfs (0--(length prfs - 1))
    and ppr = resolve_proof vars prf in
    let ths = CONJUNCTS(ASSUME tm) in
    let th = last
     (holify_lincombs vars ths (snd(chop_list(length ths) (pprfs @ [ppr])))) in
    CONV_RULE COMPLEX_RAT_EQ_CONV th;;

(* ------------------------------------------------------------------------- *)
(* Overall conversion.                                                       *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_ARITH =
  let pth0 = SIMPLE_COMPLEX_ARITH `(x = y) <=> (x - y = Cx(&0))`
  and pth1 = prove
   (`!x. ~(x = Cx(&0)) <=> ?z. z * x + Cx(&1) = Cx(&0)`,
    CONV_TAC(time FULL_COMPLEX_QUELIM_CONV))
  and pth2a = prove
   (`!x y u v. ~(x = y) \/ ~(u = v) <=>
                ?w z. w * (x - y) + z * (u - v) + Cx(&1) = Cx(&0)`,
    CONV_TAC(time FULL_COMPLEX_QUELIM_CONV))
  and pth2b = prove
   (`!x y. ~(x = y) <=> ?z. z * (x - y) + Cx(&1) = Cx(&0)`,
    CONV_TAC(time FULL_COMPLEX_QUELIM_CONV))
  and pth3 = TAUT `(p ==> F) ==> (~q <=> p) ==> q` in
  let GEN_PRENEX_CONV =
    GEN_REWRITE_CONV REDEPTH_CONV
     [AND_FORALL_THM;
      LEFT_AND_FORALL_THM;
      RIGHT_AND_FORALL_THM;
      LEFT_OR_FORALL_THM;
      RIGHT_OR_FORALL_THM;
      OR_EXISTS_THM;
      LEFT_OR_EXISTS_THM;
      RIGHT_OR_EXISTS_THM;
      LEFT_AND_EXISTS_THM;
      RIGHT_AND_EXISTS_THM] in
  let INITIAL_CONV =
    NNF_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth1] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth2a] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth2b] THENC
    ONCE_DEPTH_CONV(GEN_REWRITE_CONV I [pth0] o
                    check ((<>) `Cx(&0)` o rand)) THENC
    GEN_PRENEX_CONV THENC
    DNF_CONV in
  fun tm ->
    let avs = frees tm in
    let tm' = list_mk_forall(avs,tm) in
    let th1 = INITIAL_CONV(mk_neg tm') in
    let evs,bod = strip_exists(rand(concl th1)) in
    if is_forall bod then failwith "COMPLEX_ARITH: non-universal formula" else
    let djs = disjuncts bod in
    let th2 = end_itlist SIMPLE_DISJ_CASES(map GROBNER_REFUTE djs) in
    let th3 = itlist SIMPLE_CHOOSE evs th2 in
    SPECL avs (MATCH_MP (MATCH_MP pth3 (DISCH_ALL th3)) th1);;
