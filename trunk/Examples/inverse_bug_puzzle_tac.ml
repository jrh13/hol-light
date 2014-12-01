(* ========================================================================= *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* Proof of the Bug Puzzle conjecture of the HOL Light tutorial: Any two     *)
(* triples of points in the plane with the same oriented area can be         *)
(* connected in 5 moves or less (FivemovesOrLess).  Much of the code is      *)
(* due to John Harrison: a proof (NOTENOUGH_4) showing this is the best      *)
(* possible result; an early version of Noncollinear_2Span; the              *)
(* definition of move, which defines a closed subset                         *)
(*       {(A,B,C,A',B',C') | move (A,B,C) (A',B',C')} of R^6 x R^6,          *)
(* i.e. the zero set of a continuous function; FivemovesOrLess_STRONG,       *)
(* which handles the degenerate case (collinear or non-distinct triples),    *)
(* giving a satisfying answer using this "closed" definition of move.        *)
(*                                                                           *)
(* The mathematical proofs are essentially due to Tom Hales.  The code       *)
(* tries to mix declarative and procedural proof styles, using ideas due     *)
(* to John Harrison (section 12.1 "Towards more readable proofs" of the      *)
(* HOL Light tutorial), Freek Wiedijk (arxiv.org/pdf/1201.3601 "A            *)
(* Synthesis of the Procedural and Declarative Styles of Interactive         *)
(* Theorem Proving"), Marco Maggesi, who wrote the tactic constructs         *)
(* INTRO_TAC & HYP, which goes well with the older SUBGOAL_TAC, and Petros   *)
(* Papapanagiotou, coauthor of IsabelleLight, who wrote BuildExist below, a  *)
(* a crucial part of consider.                                               *)
(* ========================================================================= *)

needs "Multivariate/determinants.ml";;

new_type_abbrev("triple",`:real^2#real^2#real^2`);;

let so = fun tac -> FIRST_ASSUM MP_TAC THEN tac;;

let BuildExist x t =
  let try_type tp tm =
    try inst (type_match (type_of tm) tp []) tm
    with Failure _ -> tm in

  (* Check if two variables match allowing only type instantiations: *)
  let vars_match tm1 tm2 =
    let inst = try term_match [] tm1 tm2 with Failure _ -> [],[tm2,tm1],[] in
      match inst with
        [],[],_ -> tm2
      | _  -> failwith "vars_match: no match" in

  (* Find the type of a matching variable in t. *)
  let tp = try type_of (tryfind (vars_match x) (frees t))
  with Failure _ ->
  warn true ("BuildExist: `" ^ string_of_term x ^ "` not be found in
  `" ^ string_of_term t ^ "`") ;
  type_of x in
  (* Try to force x to type tp. *)
  let x' = try_type tp x in
  mk_exists (x',t);;

let consider vars_SuchThat t prfs lab =
  (* Functions ident and parse_using borrowed from HYP in tactics.ml *)
  let ident = function
      Ident s::rest when isalnum s -> s,rest
    | _ -> raise Noparse in
  let parse_using = many ident in
  let rec findSuchThat = function
      n -> if String.sub vars_SuchThat n 9 = "such that" then n
      else findSuchThat (n + 1) in
  let n = findSuchThat 1 in
  let vars = String.sub vars_SuchThat 0 (n - 1) in
  let xl = map parse_term ((fst o parse_using o lex o explode) vars) in
  let tm = itlist BuildExist xl t in
  match prfs with
    p::ps -> (warn (ps <> []) "consider: additional subproofs ignored";
    SUBGOAL_THEN tm (DESTRUCT_TAC ("@" ^ vars ^ "." ^ lab))
    THENL [p; ALL_TAC])
  | [] -> failwith "consider: no subproof given";;

let cases sDestruct disjthm tac =
  SUBGOAL_TAC "" disjthm tac THEN FIRST_X_ASSUM
  (DESTRUCT_TAC sDestruct);;

let raa lab t tac = SUBGOAL_THEN (mk_imp(t, `F`)) (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac];;

let VEC2_TAC =
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_2; SUM_2; DIMINDEX_2; VECTOR_2;
           vector_add; vec; dot; orthogonal; basis;
           vector_neg; vector_sub; vector_mul; ARITH] THEN
  CONV_TAC REAL_RING;;

let COLLINEAR_3_2Dzero = prove
 (`!y z:real^2. collinear{vec 0,y,z} <=>
                  z$1 * y$2 = y$1 * z$2`,
  REWRITE_TAC[COLLINEAR_3_2D] THEN VEC2_TAC);;

let Noncollinear_3ImpliesDistinct = prove
  (`~collinear {a,b,c}  ==>  ~(a = b) /\ ~(a = c) /\ ~(b = c)`,
  MESON_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_REFL]);;

let collinearSymmetry = prove
(`collinear {A,B,C}
         ==> collinear {A,C,B} /\ collinear {B,A,C} /\
             collinear {B,C,A} /\ collinear {C,A,B} /\ collinear {C,B,A}`,
  MESON_TAC[SET_RULE `{A,C,B} SUBSET {A,B,C} /\  {B,A,C} SUBSET {A,B,C} /\
  {B,C,A} SUBSET {A,B,C} /\  {C,A,B} SUBSET {A,B,C} /\  {C,B,A} SUBSET {A,B,C}`;
  COLLINEAR_SUBSET]);;

let Noncollinear_2Span = prove
 (`!u v w:real^2. ~collinear  {vec 0,v,w} ==> ? s t. s % v + t % w = u`,
  INTRO_TAC "!u v w; H1" THEN
  SUBGOAL_TAC "H1'" `~(v$1 * w$2 - (w:real^2)$1 * (v:real^2)$2 = &0)`
  [HYP MESON_TAC "H1" [COLLINEAR_3_2Dzero; REAL_SUB_0]] THEN
  consider "M such that"
  `M = transp(vector[v:real^2;w:real^2]):real^2^2` [MESON_TAC[]] "Mexists" THEN
  SUBGOAL_TAC "MatMult" `~(det (M:real^2^2) = &0) /\
  (! x. (M ** x)$1 = (v:real^2)$1 * x$1 + (w:real^2)$1 * x$2  /\
  (M ** x)$2 = v$2 * x$1 + w$2 * x$2)`
  [HYP SIMP_TAC "H1' Mexists" [matrix_vector_mul; DIMINDEX_2; SUM_2;
  TRANSP_COMPONENT; VECTOR_2; LAMBDA_BETA; ARITH; CART_EQ; FORALL_2; DET_2] THEN VEC2_TAC] THEN
  consider "x such that" `(M:real^2^2) ** (x:real^2) = u`
  [so (MESON_TAC [ARITH_RULE `~(r < n)  /\  r <= MIN n n  ==>  r = n`;
  DET_EQ_0_RANK; RANK_BOUND; MATRIX_FULL_LINEAR_EQUATIONS])] "xDef" THEN
  MAP_EVERY EXISTS_TAC [`(x:real^2)$1`; `(x:real^2)$2`] THEN SUBGOAL_TAC ""
  `(x:real^2)$1 * (v:real^2)$1 + (x:real^2)$2 * (w:real^2)$1 = (u:real^2)$1  /\
  x$1 * v$2 + x$2 * w$2 = u$2` [HYP MESON_TAC "MatMult xDef" [REAL_MUL_SYM]]
  THEN so (SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_2; SUM_2; DIMINDEX_2; VECTOR_2; vector_add; vector_mul; ARITH]));;

let oriented_area = new_definition
  `oriented_area (a:real^2,b:real^2,c:real^2) =
  ((b$1 - a$1) * (c$2 - a$2) - (c$1 - a$1) * (b$2 - a$2)) / &2`;;

let oriented_areaSymmetry = prove
 (`oriented_area (A,B,C) = oriented_area(A',B',C')  ==>
  oriented_area (B,C,A) = oriented_area (B',C',A')  /\
  oriented_area (C,A,B) = oriented_area (C',A',B')  /\
  oriented_area (A,C,B) = oriented_area (A',C',B')  /\
  oriented_area (B,A,C) = oriented_area (B',A',C')  /\
  oriented_area (C,B,A) = oriented_area (C',B',A')`,
  REWRITE_TAC[oriented_area] THEN VEC2_TAC);;

let move = new_definition
  `!A B C A' B' C':real^2. move (A,B,C) (A',B',C') <=>
  (B = B' /\ C = C' /\ collinear {vec 0,C - B,A' - A} \/
  A = A' /\ C = C' /\ collinear {vec 0,C - A,B' - B} \/
  A = A' /\ B = B' /\ collinear {vec 0,B - A,C' - C})`;;

let moveInvariant = prove
  (`!p p'. move p p' ==> oriented_area p = oriented_area p'`,
  REWRITE_TAC[FORALL_PAIR_THM; move; oriented_area; COLLINEAR_LEMMA;  vector_mul] THEN VEC2_TAC);;

let reachable = new_definition
  `!p p'.
  reachable p p' <=> ?n. ?s.
  s 0 = p /\ s n = p' /\
  (!m. 0 <= m /\ m < n ==> move (s m) (s (SUC m)))`;;

let reachableN = new_definition
  `!p p'. !n.
  reachableN p p' n <=> ?s.
  s 0 = p /\ s n = p' /\
  (!m. 0 <= m /\ m < n ==> move (s m) (s (SUC m)))`;;

let ReachLemma = prove
 (`!p p'. reachable p p'  <=>  ?n.  reachableN p p' n`,
  REWRITE_TAC[reachable; reachableN]);;

let reachableN_CLAUSES = prove
 (`! p p'. (reachableN p p' 0  <=>  p = p') /\
  ! n. reachableN p p' (SUC n)  <=>  ? q. reachableN p q n  /\ move q p'`,
  INTRO_TAC "!p p'" THEN
  consider "s0 such that" `s0 =  \m:num. p':triple` [MESON_TAC[]] "s0exists" THEN
  SUBGOAL_TAC "0CLAUSE" `reachableN p p' 0  <=>  p = p'`
  [HYP MESON_TAC "s0exists" [LE_0; reachableN; LT]] THEN SUBGOAL_TAC "Imp1"
  `! n. reachableN p p' (SUC n)  ==>  ? q. reachableN p q n  /\ move q p'`
  [INTRO_TAC "!n; H1" THEN
  consider "s such that"
  `s 0 = p /\ s (SUC n) = p' /\ !m. m < SUC n ==> move (s m) (s (SUC m))`
  [HYP MESON_TAC "H1" [LE_0; reachableN]] "sDef" THEN
  consider "q such that" `q:triple = s n` [MESON_TAC[]]  "qDef" THEN
  HYP MESON_TAC "sDef qDef" [LE_0; reachableN; LT]] THEN SUBGOAL_TAC "Imp2"
  `!n. (? q. reachableN p q n  /\ move q p')  ==>  reachableN p p' (SUC n)`
  [INTRO_TAC "!n" THEN REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  INTRO_TAC "!q; nReach; move_qp'" THEN
  consider "s such that"
  `s 0 = p /\ s n = q /\ !m. m < n ==> move (s m) (s (SUC m))`
  [HYP MESON_TAC "nReach" [reachableN; LT; LE_0]] "sDef" THEN
  REWRITE_TAC[reachableN; LT; LE_0] THEN
  EXISTS_TAC `\m. if m < SUC n then s m else p':triple` THEN
  HYP MESON_TAC "sDef move_qp'" [LT_0; LT_REFL; LT; LT_SUC]] THEN
  HYP MESON_TAC "0CLAUSE Imp1 Imp2" []);;

let reachableInvariant = prove
 (`!p p'. reachable p p'  ==>  oriented_area p = oriented_area p'`,
  SIMP_TAC[ReachLemma; LEFT_IMP_EXISTS_THM; SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_MESON_TAC[reachableN_CLAUSES; moveInvariant]);;

let move2Cond = new_definition
  `! A B A' B':real^2. move2Cond A B A' B'  <=>
  ~collinear {B,A,A'} /\ ~collinear {A',B,B'}   \/
  ~collinear {A,B,B'} /\ ~collinear {B',A,A'}`;;

let reachableN_One = prove
 (`reachableN P0 P1 1 <=> move P0 P1`,
  MESON_TAC[ONE; reachableN; reachableN_CLAUSES]);;

let reachableN_Two = prove
 (`reachableN P0 P2 2 <=> ?P1. move P0 P1 /\ move P1 P2`,
  MESON_TAC[TWO; reachableN_One; reachableN_CLAUSES]);;

let reachableN_Three = prove
 (`reachableN P0 P3 3  <=>  ?P1 P2. move P0 P1 /\ move P1 P2 /\ move P2 P3`,
  MESON_TAC[ARITH_RULE `3 = SUC 2`; reachableN_Two; reachableN_CLAUSES]);;

let reachableN_Four = prove
 (`reachableN P0 P4 4  <=>  ?P1 P2 P3. move P0 P1 /\ move P1 P2 /\
  move P2 P3 /\ move P3 P4`,
  MESON_TAC[ARITH_RULE `4 = SUC 3`; reachableN_Three; reachableN_CLAUSES]);;

let reachableN_Five = prove
 (`reachableN P0 P5 5  <=>  ?P1 P2 P3 P4. move P0 P1 /\ move P1 P2 /\
  move P2 P3 /\ move P3 P4 /\ move P4 P5`,
  REWRITE_TAC[ARITH_RULE `5 = SUC 4`; reachableN_CLAUSES] THEN
  MESON_TAC[reachableN_Four]);;

let moveSymmetry = prove
 (`move (A,B,C) (A',B',C') ==>
  move (B,C,A) (B',C',A') /\ move (C,A,B) (C',A',B') /\
  move (A,C,B) (A',C',B') /\ move (B,A,C) (B',A',C') /\ move (C,B,A) (C',B',A')`,
  SUBGOAL_TAC "" `!A B C A':real^2. collinear {vec 0, C - B, A' - A}
  ==> collinear {vec 0, B - C, A' - A}`
  [REWRITE_TAC[COLLINEAR_3_2Dzero] THEN VEC2_TAC] THEN
  so (REWRITE_TAC[move]) THEN MESON_TAC[]);;

let reachableNSymmetry = prove
 (`! n. ! A B C A' B' C'. reachableN (A,B,C) (A',B',C') n  ==>
reachableN (B,C,A) (B',C',A') n  /\  reachableN (C,A,B) (C',A',B') n /\
reachableN (A,C,B) (A',C',B') n  /\  reachableN (B,A,C) (B',A',C') n /\
reachableN (C,B,A) (C',B',A') n`,
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[reachableN_CLAUSES] THEN
  SIMP_TAC[PAIR_EQ] THEN
  INTRO_TAC "!n;nStep; !A B C A' B' C'" THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`X:real^2`; `Y:real^2`; `Z:real^2`] THEN
  INTRO_TAC "XYZexists" THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`(Y,Z,X):triple`; `(Z,X,Y):triple`;
  `(X,Z,Y):triple`; `(Y,X,Z):triple`; `(Z,Y,X):triple`] THEN
  HYP SIMP_TAC "nStep XYZexists" [moveSymmetry]);;

let ORIENTED_AREA_COLLINEAR_CONG = prove
 (`! A B C A' B' C.
        oriented_area (A,B,C) = oriented_area (A',B',C')
        ==> (collinear {A,B,C} <=> collinear {A',B',C'})`,
  REWRITE_TAC[COLLINEAR_3_2D; oriented_area] THEN CONV_TAC REAL_RING);;

let Basic2move_THM = prove
 (`! A B C A'. ~collinear {A,B,C} /\ ~collinear {B,A,A'} ==>
  ?X. move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)`,
  INTRO_TAC "!A B C A'; H1 H2" THEN SUBGOAL_TAC "add0vector_mul"
  `!r. r % ((A:real^2) - B) = (--r) % (B - A)  /\
  r % (A - B) = r % (A - B) + &0 % (C - B)` [VEC2_TAC] THEN
  SUBGOAL_TAC "H2'" `~ ? r. A' - (A:real^2) = r % (A - B)`
  [so (HYP MESON_TAC "H2" [COLLINEAR_3; COLLINEAR_LEMMA])] THEN
  consider "r t such that" `A' - (A:real^2) = r % (A - B) + t % (C - B)`
  [HYP MESON_TAC "H1" [COLLINEAR_3; Noncollinear_2Span]] "rExists" THEN
  SUBGOAL_TAC "tNonzero" `~(t = &0)`
  [so (HYP MESON_TAC "add0vector_mul H2'" [])] THEN
  consider "s X such that" `s = r / t  /\  X:real^2 = C + s % (A - B)`
  [HYP MESON_TAC "rExists" []] "Xexists" THEN
  SUBGOAL_TAC "" `A' - (A:real^2) = (t * s) % (A - B) + t % (C - B)`
  [so (HYP MESON_TAC "rExists tNonzero" [REAL_DIV_LMUL])] THEN SUBGOAL_TAC ""
  `A' - (A:real^2) = t % (X - B) /\ X - C = (-- s) % (B - (A:real^2))`
  [(so (HYP REWRITE_TAC "Xexists" [])) THEN VEC2_TAC] THEN SUBGOAL_TAC ""
  `collinear {vec 0,B - (A:real^2),X - C}  /\  collinear {vec 0,X - B,A' - A}`
  [so (HYP MESON_TAC "" [COLLINEAR_LEMMA])] THEN so (MESON_TAC [move]));;

let FourStepMoveAB = prove
 (`!A B C A' B'. ~collinear {A,B,C} ==>
  ~collinear {B,A,A'} /\ ~collinear {A',B,B'} ==>
  ? X Y. move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)  /\
  move (A',B,X) (A',B,Y)  /\  move (A',B,Y) (A',B',Y)`,
  INTRO_TAC "!A B C A' B'; H1; H2" THEN
  consider "X such that" `move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)`
  [HYP MESON_TAC "H1 H2" [Basic2move_THM]]"ABX" THEN
  SUBGOAL_TAC "" `~collinear {(A:real^2),B,X} /\ ~collinear {A',B,X}`
  [so (HYP MESON_TAC "H1" [moveInvariant; ORIENTED_AREA_COLLINEAR_CONG])]
  THEN SUBGOAL_TAC "" `~collinear {(B:real^2),A',X}`
  [so (MESON_TAC [collinearSymmetry])] THEN
  consider "Y such that" `move (B,A',X) (B,A',Y)  /\  move (B,A',Y) (B',A',Y)`
  [so (HYP MESON_TAC "H2" [Basic2move_THM])]  "BA'Y" THEN
  SUBGOAL_TAC "" `move (A',B,X) (A',B,Y)  /\  move (A',B,Y) (A',B',Y)`
  [HYP MESON_TAC "BA'Y" [moveSymmetry]] THEN so (HYP MESON_TAC "ABX" []));;

let FourStepMoveABBAreach = prove
 (`!A B C A' B'. ~collinear {A,B,C} /\ move2Cond A B A' B' ==>
  ? Y. reachableN (A,B,C) (A',B',Y) 4`,
  INTRO_TAC "!A B C A' B'; H1 H2" THEN
  cases "Case1 | Case2"
  `~collinear {B,(A:real^2),A'} /\ ~collinear {A',B,B'}  \/
  ~collinear {A,B,B'} /\ ~collinear {B',A,A'}`
  [HYP MESON_TAC "H2" [move2Cond]]
  THENL
  [so (HYP MESON_TAC "H1" [FourStepMoveAB; reachableN_Four]);
  SUBGOAL_TAC "" `~collinear {B,(A:real^2),C}`
  [HYP MESON_TAC "H1" [collinearSymmetry]]] THEN
  SUBGOAL_TAC "" `~collinear {B,(A:real^2),C}`
  [HYP MESON_TAC "H1" [collinearSymmetry]] THEN
  consider "X Y such that"
  `move (B,A,C) (B,A,X)  /\  move (B,A,X) (B',A,X)  /\
  move (B',A,X) (B',A,Y)  /\  move (B',A,Y) (B',A',Y)`
  [so (HYP MESON_TAC "Case2" [FourStepMoveAB])] "BAX" THEN
  HYP MESON_TAC "BAX" [moveSymmetry; reachableN_Four]);;

let NotMove2ImpliesCollinear = prove
 (`!A B C A' B' C'. ~collinear {A,B,C} /\ ~collinear {A',B',C'} /\
  ~(A = A') /\ ~(B = B') /\ ~move2Cond A B A' B' ==>
  collinear {A,B,A',B'}`,
  INTRO_TAC "!A B C A' B' C'; H1 H1' H2 H2' H3" THEN
  SUBGOAL_TAC "Distinct" `~((A:real^2) = B) /\ ~((A':real^2) = B')`
  [HYP MESON_TAC "H1 H1'" [Noncollinear_3ImpliesDistinct]] THEN
  SUBGOAL_TAC "set4symmetry" `{(A:real^2),B,A',B'} SUBSET {A,A',B,B'}  /\
  {A,B,A',B'} SUBSET {B,B',A',A}  /\  {A,B,A',B'} SUBSET {A',B',B,A}` [SET_TAC[]] THEN
  cases "Case1 | Case2 | Case3 | Case4"
  `collinear {B,(A:real^2),A'} /\ collinear {A,B,B'}  \/
  collinear {B,A,A'} /\ collinear {B',A,A'}  \/
  collinear {A',B,B'} /\ collinear {A,B,B'}  \/
  collinear {A',B,B'} /\ collinear {B',A,A'}`
  [HYP MESON_TAC "H3" [move2Cond]] THEN
  so (HYP MESON_TAC "Distinct H2 H2' set4symmetry"
  [collinearSymmetry; COLLINEAR_4_3; COLLINEAR_SUBSET]));;

let DistinctImplies2moveable = prove
 (`!A B C A' B' C'. ~collinear {A,B,C} /\ ~collinear {A',B',C'} /\
  ~(A = A') /\ ~(B = B') /\ ~(C = C')  ==>
  move2Cond A B A' B' \/ move2Cond B C B' C'`,
  INTRO_TAC "!A B C A' B' C'; H1 H1' H2a H2b H2c" THEN SUBGOAL_TAC "3subset4"
  `{(A:real^2),B,B'} SUBSET {A,B,A',B'} /\ {B,B',C} SUBSET {B,C,B',C'}`
  [SET_TAC[]] THEN
  raa "Con" `~move2Cond A B A' B'  /\
  ~move2Cond B C B' C'` (HYP MESON_TAC "Con" []) THEN
  SUBGOAL_TAC "" `collinear {(A:real^2),B,A',B'} /\ collinear {B,C,B',C'}`
  [so (HYP MESON_TAC "H1 H1' H2a H2b H2c" [collinearSymmetry; NotMove2ImpliesCollinear])]
  THEN SUBGOAL_TAC "" `collinear {(A:real^2),B,C}`
  [so (HYP MESON_TAC "3subset4 H2a H2b H2c" [COLLINEAR_SUBSET; COLLINEAR_3_TRANS])]
  THEN so (HYP MESON_TAC "H1 H1'" []));;

let SameCdiffAB = prove
 (`!A B C A' B' C'.  ~collinear {A,B,C} /\ ~collinear {A',B',C'} ==>
 C = C' /\ ~(A = A') /\ ~(B = B') ==>
  ? Y. reachableN (A,B,C) (Y,B',C') 2  \/ reachableN (A,B,C) (A',B',Y) 4`,
  INTRO_TAC "!A B C A' B' C'; H1; H2" THEN SUBGOAL_TAC "easy_set"
  `{B,B',(A:real^2)} SUBSET {A,B,A',B'}  /\  {A,B,C} SUBSET {B,B',A,C}` [SET_TAC[]]  THEN
  cases "Ncol | move | col_Nmove"
  `~collinear {C,B,B'}  \/
  move2Cond A B A' B'  \/
  collinear {C,B,B'} /\ ~move2Cond A B A' B'`
  [MESON_TAC[]] THENL
  [consider "X such that" `move (B,C,A) (B,C,X) /\ move (B,C,X) (B',C',X)`
  [so (HYP MESON_TAC "easy_set H1 H2" [collinearSymmetry; Basic2move_THM])] "BCX"
  THEN HYP MESON_TAC "BCX" [reachableN_Two; reachableNSymmetry];
  so (HYP MESON_TAC "H1" [FourStepMoveABBAreach]);
  SUBGOAL_TAC "" `collinear {(B:real^2),B',A} /\ collinear {B,B',C}`
  [so (HYP MESON_TAC "H1 H2 easy_set"
  [NotMove2ImpliesCollinear; COLLINEAR_SUBSET; collinearSymmetry])]  THEN
  so (HYP MESON_TAC "H2 easy_set H1" [COLLINEAR_4_3; COLLINEAR_SUBSET])]);;

let FourMovesToCorrectTwo = prove
 (`!A B C A' B' C'. ~collinear {A,B,C} /\ ~collinear {A',B',C'} ==>
  ? n. n < 5 /\ ? Y. reachableN (A,B,C) (A',B',Y) n  \/
  reachableN (A,B,C) (A',Y,C') n  \/ reachableN (A,B,C) (Y,B',C') n`,
  INTRO_TAC "!A B C A' B' C'; H1" THEN
  SUBGOAL_TAC "H1'" `~collinear {B,C,(A:real^2)} /\
  ~collinear{B',C',(A':real^2)} /\ ~collinear {C,A,B} /\ ~collinear {C',A',B'}`
  [HYP MESON_TAC "H1" [collinearSymmetry]]   THEN
  SUBGOAL_TAC "easy_arith" `0 < 5 /\ 2 < 5 /\ 3 < 5 /\ 4 < 5` [ARITH_TAC] THEN
  cases "case01 | case2 | case3"
  `((A:real^2) = A' /\ (B:real^2) = B' /\ (C:real^2) = C'  \/
  A = A' /\ B = B' /\ ~(C = C')  \/  A = A' /\ ~(B = B') /\ C = C' \/
  ~(A = A') /\ B = B' /\ C = C')  \/
  (A = A' /\ ~(B = B') /\ ~(C = C')  \/
  ~(A = A') /\ B = B' /\ ~(C = C')  \/  ~(A = A') /\ ~(B = B') /\ C = C')  \/
  ~(A = A') /\ ~(B = B') /\ ~(C = C')`
  [MESON_TAC []] THENL
  [so (HYP MESON_TAC "easy_arith" [reachableN_CLAUSES]);
  so (HYP MESON_TAC "H1 H1' easy_arith" [SameCdiffAB; reachableNSymmetry]);
  EXISTS_TAC `4` THEN HYP SIMP_TAC "easy_arith" [] THEN
  so (HYP MESON_TAC "H1  H1'" [DistinctImplies2moveable; FourStepMoveABBAreach;
  reachableNSymmetry; reachableN_Four])]);;

let CorrectFinalPoint = prove
 (`oriented_area (A,B,C) = oriented_area (A,B,C') ==>
  move (A,B,C) (A,B,C')`,
  REWRITE_TAC [move; oriented_area; COLLINEAR_3_2Dzero]  THEN VEC2_TAC);;

let FiveMovesOrLess = prove
 (`!A B C A' B' C'. ~collinear {A,B,C} ==>
  oriented_area (A,B,C) = oriented_area (A',B',C') ==>
  ? n. n <= 5 /\ reachableN (A,B,C) (A',B',C') n`,
  INTRO_TAC "!A B C A' B' C'; H1; H2"  THEN
  SUBGOAL_TAC "H1'" `~collinear {(A':real^2),B',C'}`
  [HYP MESON_TAC "H1 H2" [ORIENTED_AREA_COLLINEAR_CONG]]  THEN
  SUBGOAL_TAC "Distinct" `~((A:real^2) = B) /\ ~(A = C) /\ ~(B = C) /\
  ~((A':real^2) = B') /\ ~(A' = C') /\ ~(B' = C')`
  [so (HYP MESON_TAC "H1" [Noncollinear_3ImpliesDistinct])]  THEN
  consider "n Y such that"
  `n < 5 /\ (reachableN (A,B,C) (A',B',Y) n \/
  reachableN (A,B,C) (A',Y,C') n \/ reachableN (A,B,C) (Y,B',C') n)`
  [HYP MESON_TAC "H1 H1'" [FourMovesToCorrectTwo]] "2Correct" THEN
  cases "A'B'Y | A'YC' | YB'C'"
  `reachableN (A,B,C) (A',B',Y) n  \/
  reachableN (A,B,C) (A',Y,C') n  \/
  reachableN (A,B,C) (Y,B',C') n` [HYP MESON_TAC "2Correct" []] THENL
  [SUBGOAL_TAC "" `oriented_area (A',B',Y) = oriented_area (A',B',C')`
  [so (HYP MESON_TAC "H2" [ReachLemma; reachableInvariant])]  THEN
  SUBGOAL_TAC "" `move (A',B',Y) (A',B',C')`
  [so (HYP MESON_TAC "Distinct" [CorrectFinalPoint])]  THEN
  so (HYP MESON_TAC "A'B'Y 2Correct" [reachableN_CLAUSES; LE_SUC_LT]);
  SUBGOAL_TAC "" `oriented_area (A',C',Y) = oriented_area (A',C',B')`
  [so (HYP MESON_TAC "H2" [ReachLemma; reachableInvariant; oriented_areaSymmetry])]
  THEN SUBGOAL_TAC "" `move (A',Y,C') (A',B',C')`
  [so (HYP MESON_TAC "Distinct" [CorrectFinalPoint; moveSymmetry])]  THEN
  so (HYP MESON_TAC "A'YC' 2Correct" [reachableN_CLAUSES; LE_SUC_LT]);
SUBGOAL_TAC "" `oriented_area (B',C',Y) = oriented_area (B',C',A')`
  [so (HYP MESON_TAC "H2" [ReachLemma; reachableInvariant; oriented_areaSymmetry])]
  THEN SUBGOAL_TAC "" `move (Y,B',C') (A',B',C')`
  [so (HYP MESON_TAC "Distinct" [CorrectFinalPoint; moveSymmetry])]  THEN
  so (HYP MESON_TAC "YB'C' 2Correct" [reachableN_CLAUSES; LE_SUC_LT])]);;

let NOTENOUGH_4 = prove
 (`?p0 p4. oriented_area p0 = oriented_area p4 /\ ~reachableN p0 p4 4`,
  consider "p0 p4 such that"
  `p0:triple = vector [&0;&0],vector [&0;&1],vector [&1;&0]  /\
  p4:triple = vector [&1;&1],vector [&1;&2],vector [&2;&1]`
  [MESON_TAC []] "p04Def" THEN
  SUBGOAL_TAC "equal_areas" `oriented_area p0 = oriented_area p4`
  [HYP REWRITE_TAC "p04Def" [oriented_area] THEN VEC2_TAC] THEN
  SUBGOAL_TAC "" `~reachableN p0 p4 4`
  [HYP REWRITE_TAC "p04Def" [reachableN_Four; NOT_EXISTS_THM; FORALL_PAIR_THM;  move; COLLINEAR_3_2Dzero; FORALL_VECTOR_2] THEN VEC2_TAC] THEN
  so (HYP MESON_TAC "equal_areas" []));;

let FiveMovesOrLess_STRONG = prove
 (`!A B C A' B' C'.
  oriented_area (A,B,C) = oriented_area (A',B',C') ==>
  ?n. n <= 5 /\ reachableN (A,B,C) (A',B',C') n`,
  INTRO_TAC "!A B C A' B' C'; H1" THEN
  SUBGOAL_TAC "EZcollinear"
  `(!X Y:real^2. collinear {X,Y,Y}) /\
  (!A B A'. move (A,B,B) (A',B,B))  /\
  !A B C B'. (collinear {A,B,C} /\ collinear {A,B',C}  ==>
  move (A,B,C) (A,B',C))`
  [REWRITE_TAC[move; COLLINEAR_3_2D] THEN VEC2_TAC] THEN
  cases "ABCncol | ABCcol"
  `~collinear {(A:real^2),B,C}  \/  collinear {A,B,C}`
  [MESON_TAC []] THENL
  [so (HYP MESON_TAC "H1" [FiveMovesOrLess]);
  SUBGOAL_TAC "A'B'C'col" `collinear {(A':real^2),B',C'}`
  [so (HYP MESON_TAC "H1" [ORIENTED_AREA_COLLINEAR_CONG])] THEN
  consider "P1 P2 P3 P4 such that"
  `P1:triple = A,C,C  /\  P2:triple = B',C,C  /\  P3 = B',B',C  /\
  P4:triple = B',B',C'` [MESON_TAC []] "P1234exist" THEN
  SUBGOAL_TAC "" `move (A,B,C) (P1:triple)  /\  move P1 P2  /\
  move P2 P3  /\  move P3 P4  /\  move P4 (A',B',C')`
  [HYP MESON_TAC "ABCcol A'B'C'col EZcollinear P1234exist"
  [collinearSymmetry; moveSymmetry]] THEN
  so (MESON_TAC [reachableN_Five; LE_REFL])]);;
