needs "Tutorial/Vectors.ml";;

let points =
[((0, -1), (0, -1), (2, 0)); ((0, -1), (0, 0), (2, 0));
 ((0, -1), (0, 1), (2, 0)); ((0, -1), (2, 0), (0, -1));
 ((0, -1), (2, 0), (0, 0)); ((0, -1), (2, 0), (0, 1));
 ((0, 0), (0, -1), (2, 0)); ((0, 0), (0, 0), (2, 0));
 ((0, 0), (0, 1), (2, 0)); ((0, 0), (2, 0), (-2, 0));
 ((0, 0), (2, 0), (0, -1)); ((0, 0), (2, 0), (0, 0));
 ((0, 0), (2, 0), (0, 1)); ((0, 0), (2, 0), (2, 0));
 ((0, 1), (0, -1), (2, 0)); ((0, 1), (0, 0), (2, 0));
 ((0, 1), (0, 1), (2, 0)); ((0, 1), (2, 0), (0, -1));
 ((0, 1), (2, 0), (0, 0)); ((0, 1), (2, 0), (0, 1));
 ((2, 0), (-2, 0), (0, 0)); ((2, 0), (0, -1), (0, -1));
 ((2, 0), (0, -1), (0, 0)); ((2, 0), (0, -1), (0, 1));
 ((2, 0), (0, 0), (-2, 0)); ((2, 0), (0, 0), (0, -1));
 ((2, 0), (0, 0), (0, 0)); ((2, 0), (0, 0), (0, 1));
 ((2, 0), (0, 0), (2, 0)); ((2, 0), (0, 1), (0, -1));
 ((2, 0), (0, 1), (0, 0)); ((2, 0), (0, 1), (0, 1));
 ((2, 0), (2, 0), (0, 0))];;

let ortho =
  let mult (x1,y1) (x2,y2) = (x1 * x2 + 2 * y1 * y2,x1 * y2 + y1 * x2)
  and add (x1,y1) (x2,y2) = (x1 + x2,y1 + y2) in
  let dot (x1,y1,z1) (x2,y2,z2) =
    end_itlist add [mult x1 x2; mult y1 y2; mult z1 z2] in
  fun (v1,v2) -> dot v1 v2 = (0,0);;

let opairs = filter ortho (allpairs (fun a b -> a,b) points points);;

let otrips = filter (fun (a,b,c) -> ortho(a,b) && ortho(a,c))
                    (allpairs (fun a (b,c) -> a,b,c) points opairs);;

let hol_of_value =
  let tm0 = `&0` and tm1 = `&2` and tm2 = `-- &2`
  and tm3 = `sqrt(&2)` and tm4 = `--sqrt(&2)` in
  function 0,0 -> tm0 | 2,0 -> tm1 | -2,0 -> tm2 | 0,1 -> tm3 | 0,-1 -> tm4;;

let hol_of_point =
  let ptm = `vector:(real)list->real^3` in
  fun (x,y,z) -> mk_comb(ptm,mk_flist(map hol_of_value [x;y;z]));;

let SQRT_2_POW = prove
 (`sqrt(&2) pow 2 = &2`,
  SIMP_TAC[SQRT_POW_2; REAL_POS]);;

let PROVE_NONTRIVIAL =
  let ptm = `~(x :real^3 = vec 0)` and xtm = `x:real^3` in
  fun x -> prove(vsubst [hol_of_point x,xtm] ptm,
                 GEN_REWRITE_TAC RAND_CONV [VECTOR_ZERO] THEN
                 MP_TAC SQRT_2_POW THEN CONV_TAC REAL_RING);;

let PROVE_ORTHOGONAL =
  let ptm = `orthogonal:real^3->real^3->bool` in
  fun (x,y) ->
   prove(list_mk_comb(ptm,[hol_of_point x;hol_of_point y]),
         ONCE_REWRITE_TAC[ORTHOGONAL_VECTOR] THEN
         MP_TAC SQRT_2_POW THEN CONV_TAC REAL_RING);;

let ppoint = let p = `P:real^3->bool` in fun v -> mk_comb(p,hol_of_point v);;

let DEDUCE_POINT_TAC pts =
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC (map hol_of_point pts) THEN
  ASM_REWRITE_TAC[];;

let rec KOCHEN_SPECKER_TAC set_0 set_1 =
  if intersect set_0 set_1 <> [] then
    let p = ppoint(hd(intersect set_0 set_1)) in
    let th1 = ASSUME(mk_neg p) and th2 = ASSUME p in
    ACCEPT_TAC(EQ_MP (EQF_INTRO th1) th2)
  else
    let prf_1 = filter (fun (a,b) -> mem a set_0) opairs
    and prf_0 = filter (fun (a,b,c) -> mem a set_1 && mem b set_1) otrips in
    let new_1 = map snd prf_1 and new_0 = map (fun (a,b,c) -> c) prf_0 in
    let set_0' = union new_0 set_0 and set_1' = union new_1 set_1 in
    let del_0 = subtract set_0' set_0 and del_1 = subtract set_1' set_1 in
    if del_0 <> [] || del_1 <> [] then
       let prv_0 x =
         let a,b,_ = find (fun (a,b,c) -> c = x) prf_0 in DEDUCE_POINT_TAC [a;b]
       and prv_1 x =
         let a,_ = find (fun (a,c) -> c = x) prf_1 in DEDUCE_POINT_TAC [a] in
      let newuns = list_mk_conj
        (map ppoint del_1 @ map (mk_neg o ppoint) del_0)
      and tacs = map prv_1 del_1 @ map prv_0 del_0 in
      SUBGOAL_THEN newuns STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL tacs; ALL_TAC] THEN
      KOCHEN_SPECKER_TAC set_0' set_1'
    else
      let v = find (fun i -> not(mem i set_0) && not(mem i set_1)) points in
      ASM_CASES_TAC (ppoint v) THENL
       [KOCHEN_SPECKER_TAC set_0 (v::set_1);
        KOCHEN_SPECKER_TAC (v::set_0) set_1];;

let KOCHEN_SPECKER_LEMMA = prove
 (`!P. (!x y:real^3. ~(x = vec 0) /\ ~(y = vec 0) /\ orthogonal x y /\
                     ~(P x) ==> P y) /\
       (!x y z. ~(x = vec 0) /\ ~(y = vec 0) /\ ~(z = vec 0) /\
                orthogonal x y /\ orthogonal x z /\ orthogonal y z /\
                P x /\ P y ==> ~(P z))
       ==> F`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (ASSUME_TAC o PROVE_NONTRIVIAL) points THEN
  MAP_EVERY (ASSUME_TAC o PROVE_ORTHOGONAL) opairs THEN
  KOCHEN_SPECKER_TAC [] []);;

let NONTRIVIAL_CROSS = prove
 (`!x y. orthogonal x y /\ ~(x = vec 0) /\ ~(y = vec 0)
         ==> ~(x cross y = vec 0)`,
  REWRITE_TAC[GSYM DOT_EQ_0] THEN VEC3_TAC);;

let KOCHEN_SPECKER_PARADOX = prove
 (`~(?spin:real^3->num.
        !x y z. ~(x = vec 0) /\ ~(y = vec 0) /\ ~(z = vec 0) /\
                orthogonal x y /\ orthogonal x z /\ orthogonal y z
                ==> (spin x = 0) /\ (spin y = 1) /\ (spin z = 1) \/
                    (spin x = 1) /\ (spin y = 0) /\ (spin z = 1) \/
                    (spin x = 1) /\ (spin y = 1) /\ (spin z = 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x:real^3. spin(x) = 1` KOCHEN_SPECKER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  POP_ASSUM MP_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`; NONTRIVIAL_CROSS; ORTHOGONAL_CROSS]);;
