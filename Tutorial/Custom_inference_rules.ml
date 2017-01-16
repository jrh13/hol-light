let near_ring_axioms =
  `(!x. 0 + x = x) /\
   (!x. neg x + x = 0) /\
   (!x y z. (x + y) + z = x + y + z) /\
   (!x y z. (x * y) * z = x * y * z) /\
   (!x y z. (x + y) * z = (x * z) + (y * z))`;;

(**** Works eventually but takes a very long time
MESON[]
 `(!x. 0 + x = x) /\
  (!x. neg x + x = 0) /\
  (!x y z. (x + y) + z = x + y + z) /\
  (!x y z. (x * y) * z = x * y * z) /\
  (!x y z. (x + y) * z = (x * z) + (y * z))
  ==> !a. 0 * a = 0`;;
 ****)

let is_realvar w x = is_var x && not(mem x w);;

let rec real_strip w tm =
  if mem tm w then tm,[] else
  let l,r = dest_comb tm in
  let f,args = real_strip w l in f,args@[r];;

let weight lis (f,n) (g,m) =
  let i = index f lis and j = index g lis in
  i > j || i = j && n > m;;

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
                       else h1 = h2 && lexord ord t1 t2
  | _ -> false;;

let rec lpo_gt w s t =
  if is_realvar w t then not(s = t) && mem t (frees s)
  else if is_realvar w s || is_abs s || is_abs t then false else
  let f,fargs = real_strip w s and g,gargs = real_strip w t in
  exists (fun si -> lpo_ge w si t) fargs ||
        forall (lpo_gt w s) gargs &&
        (f = g && lexord (lpo_gt w) fargs gargs ||
         weight w (f,length fargs) (g,length gargs))
and lpo_ge w s t = (s = t) || lpo_gt w s t;;

let rec istriv w env x t =
  if is_realvar w t then t = x || defined env t && istriv w env x (apply env t)
  else if is_const t then false else
  let f,args = strip_comb t in
  exists (istriv w env x) args && failwith "cyclic";;

let rec unify w env tp =
  match tp with
   ((Var(_,_) as x),t) | (t,(Var(_,_) as x)) when not(mem x w) ->
        if defined env x then unify w env (apply env x,t)
        else if istriv w env x t then env else (x|->t) env
  | (Comb(f,x),Comb(g,y)) -> unify w (unify w env (x,y)) (f,g)
  | (s,t) -> if s = t then env else failwith "unify: not unifiable";;

let fullunify w (s,t) =
  let env = unify w undefined (s,t) in
  let th = map (fun (x,t) -> (t,x)) (graph env) in
  let rec subs t =
    let t' = vsubst th t in
    if t' = t then t else subs t' in
  map (fun (t,x) -> (subs t,x)) th;;

let rec listcases fn rfn lis acc =
  match lis with
    [] -> acc
  | h::t -> fn h (fun i h' -> rfn i (h'::map REFL t)) @
            listcases fn (fun i t' -> rfn i (REFL h::t')) t acc;;

let LIST_MK_COMB f ths = rev_itlist (fun s t -> MK_COMB(t,s)) ths (REFL f);;

let rec overlaps w th tm rfn =
  let l,r = dest_eq(concl th) in
  if not (is_comb tm) then [] else
  let f,args = strip_comb tm in
  listcases (overlaps w th) (fun i a -> rfn i (LIST_MK_COMB f a)) args
            (try [rfn (fullunify w (l,tm)) th] with Failure _ -> []);;

let crit1 w eq1 eq2 =
  let l1,r1 = dest_eq(concl eq1)
  and l2,r2 = dest_eq(concl eq2) in
  overlaps w eq1 l2 (fun i th -> TRANS (SYM(INST i th)) (INST i eq2));;

let fixvariables s th =
  let fvs = subtract (frees(concl th)) (freesl(hyp th)) in
  let gvs = map2 (fun v n -> mk_var(s^string_of_int n,type_of v))
                 fvs (1--length fvs) in
  INST (zip gvs fvs) th;;

let renamepair (th1,th2) = fixvariables "x" th1,fixvariables "y" th2;;

let critical_pairs w tha thb =
  let th1,th2 = renamepair (tha,thb) in crit1 w th1 th2 @ crit1 w th2 th1;;

let normalize_and_orient w eqs th =
  let th' = GEN_REWRITE_RULE TOP_DEPTH_CONV eqs th in
  let s',t' = dest_eq(concl th') in
  if lpo_ge w s' t' then th' else if lpo_ge w t' s' then SYM th'
  else failwith "Can't orient equation";;

let status(eqs,crs) eqs0 =
  if eqs = eqs0 && (length crs) mod 1000 <> 0 then () else
  (print_string(string_of_int(length eqs)^" equations and "^
                string_of_int(length crs)^" pending critical pairs");
   print_newline());;

let left_reducible eqs eq =
  can (CHANGED_CONV(GEN_REWRITE_CONV (LAND_CONV o ONCE_DEPTH_CONV) eqs))
      (concl eq);;

let rec complete w (eqs,crits) =
  match crits with
    (eq::ocrits) ->
        let trip =
          try let eq' = normalize_and_orient w eqs eq in
              let s',t' = dest_eq(concl eq') in
              if s' = t' then (eqs,ocrits) else
              let crits',eqs' = partition(left_reducible [eq']) eqs in
              let eqs'' = eq'::eqs' in
              eqs'',
              ocrits @ crits' @ itlist ((@) o critical_pairs w eq') eqs'' []
          with Failure _ ->
              if exists (can (normalize_and_orient w eqs)) ocrits
              then (eqs,ocrits@[eq])
              else failwith "complete: no orientable equations" in
        status trip eqs; complete w trip
  | [] -> eqs;;

let complete_equations wts eqs =
  let eqs' = map (normalize_and_orient wts []) eqs in
  complete wts ([],eqs');;

complete_equations [`1`; `( * ):num->num->num`; `i:num->num`]
  [SPEC_ALL(ASSUME `!a b. i(a) * a * b = b`)];;

complete_equations [`c:A`; `f:A->A`]
 (map SPEC_ALL (CONJUNCTS (ASSUME
   `((f(f(f(f(f c))))) = c:A) /\ (f(f(f c)) = c)`)));;

let eqs = map SPEC_ALL (CONJUNCTS (ASSUME
  `(!x. 1 * x = x) /\ (!x. i(x) * x = 1) /\
   (!x y z. (x * y) * z = x * y * z)`)) in
map concl (complete_equations [`1`; `( * ):num->num->num`; `i:num->num`] eqs);;

let COMPLETE_TAC w th =
  let eqs = map SPEC_ALL (CONJUNCTS(SPEC_ALL th)) in
  let eqs' = complete_equations w eqs in
  MAP_EVERY (ASSUME_TAC o GEN_ALL) eqs';;

g `(!x. 1 * x = x) /\
   (!x. i(x) * x = 1) /\
   (!x y z. (x * y) * z = x * y * z)
   ==> !x y. i(y) * i(i(i(x * i(y)))) * x = 1`;;

e (DISCH_THEN(COMPLETE_TAC [`1`; `( * ):num->num->num`; `i:num->num`]));;
e(ASM_REWRITE_TAC[]);;

g `(!x. 0 + x = x) /\
     (!x. neg x + x = 0) /\
     (!x y z. (x + y) + z = x + y + z) /\
     (!x y z. (x * y) * z = x * y * z) /\
     (!x y z. (x + y) * z = (x * z) + (y * z))
     ==> (neg 0  * (x * y + z + neg(neg(w + z))) + neg(neg b + neg a) =
          a + b)`;;

e (DISCH_THEN(COMPLETE_TAC
     [`0`; `(+):num->num->num`; `neg:num->num`; `( * ):num->num->num`]));;
e(ASM_REWRITE_TAC[]);;

(**** Could have done this instead
e (DISCH_THEN(COMPLETE_TAC
      [`0`; `(+):num->num->num`; `( * ):num->num->num`; `neg:num->num`]));;
****)
