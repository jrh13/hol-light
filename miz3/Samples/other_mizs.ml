(* ======== Examples/mizar.ml ============================================== *)

hide_constant "<=";;

horizon := 0;;

let KNASTER_TARSKI = thm `;
  let (<=) be A->A->bool;
  thus !f. (!x y. x <= y /\ y <= x ==> (x = y)) /\
      (!x y z. x <= y /\ y <= z ==> x <= z) /\
      (!x y. x <= y ==> f x <= f y) /\
      (!X. ?s. (!x. x IN X ==> s <= x) /\
                 (!s'. (!x. x IN X ==> s' <= x) ==> s' <= s))
      ==> ?x. f x = x
  proof
    let f be A->A;
    exec DISCH_THEN (LABEL_TAC "L");
    !x y. x <= y /\ y <= x ==> (x = y) [antisymmetry] by L;
    !x y z. x <= y /\ y <= z ==> x <= z [transitivity] by L;
    !x y. x <= y ==> f x <= f y [monotonicity] by L;
    !X. ?s:A. (!x. x IN X ==> s <= x) /\
              (!s'. (!x. x IN X ==> s' <= x) ==> s' <= s) [least_upper_bound]
      by L;
    set Y = {b | f b <= b} [Y_def];
    !b. b IN Y <=> f b <= b [Y_thm] by ALL_TAC,Y_def,IN_ELIM_THM,BETA_THM;
    consider a such that
      (!x. x IN Y ==> a <= x) /\
      (!a'. (!x. x IN Y ==> a' <= x) ==> a' <= a) [lub] by least_upper_bound;
    take a;
    !b. b IN Y ==> f a <= b
    proof
      let b be A;
      assume b IN Y [b_in_Y];
      f b <= b [L0] by -,Y_thm;
      a <= b by b_in_Y,lub;
      f a <= f b by -,monotonicity;
      thus f a <= b by -,L0,transitivity;
    end;
    f(a) <= a [Part1] by -,lub;
    f(f(a)) <= f(a) by -,monotonicity;
    f(a) IN Y by -,Y_thm;
    a <= f(a) by -,lub;
  qed by -,Part1,antisymmetry`;;

unhide_constant "<=";;

(* ======== Mizarlight/duality.ml ========================================== *)

parse_as_infix("ON",(11,"right"));;

hide_constant "ON";;

let projective = new_definition
 `projective((ON):Point->Line->bool) <=>
        (!p p'. ~(p = p') ==> ?!l. p ON l /\ p' ON l) /\
        (!l l'. ?p. p ON l /\ p ON l') /\
        (?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                    ~(?l. p ON l /\ p' ON l /\ p'' ON l)) /\
        (!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                        p ON l /\ p' ON l /\ p'' ON l)`;;

horizon := 1;;

let LEMMA_1 = thm `;
  !(ON):Point->Line->bool. projective(ON) ==> !p. ?l. p ON l
proof
  let (ON) be Point->Line->bool;
  assume projective(ON) [0];
  !p p'. ~(p = p') ==> ?!l. p ON l /\ p' ON l [1] by 0,projective;
  ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
             ~(?l. p ON l /\ p' ON l /\ p'' ON l) [3] by 0,projective;
  let p be Point;
  consider q q' such that ~(q = q':Point);
  ~(p = q) \/ ~(p = q');
  consider l such that p ON l by 1;
  take l;
qed`;;

let LEMMA_2 = thm `;
  !(ON):Point->Line->bool. projective(ON)
   ==> !p1 p2 q l l1 l2.
     p1 ON l /\ p2 ON l /\ p1 ON l1 /\ p2 ON l2 /\ q ON l2 /\
     ~(q ON l) /\ ~(p1 = p2) ==> ~(l1 = l2)
proof
  let (ON) be Point->Line->bool;
  assume projective(ON) [0];
  !p p'. ~(p = p') ==> ?!l. p ON l /\ p' ON l [1] by 0,projective;
// here qed already works
  let p1 p2 q be Point;
  let l l1 l2 be Line;
  assume p1 ON l [5];
  assume p2 ON l [6];
  assume p1 ON l1 [7];
  assume p2 ON l2 [9];
  assume q ON l2 [10];
  assume ~(q ON l) [11];
  assume ~(p1 = p2) [12];
  assume l1 = l2 [13];
  p1 ON l2 by 7;
  l = l2 by 1,5,6,9,12;
  thus F by 10,11;
end`;;

let PROJECTIVE_DUALITY = thm `;
  !(ON):Point->Line->bool. projective(ON) ==> projective (\l p. p ON l)
proof
  let (ON) be Point->Line->bool;
  assume projective(ON) [0];
  !p p'. ~(p = p') ==> ?!l. p ON l /\ p' ON l [1] by 0,projective;
  !l l'. ?p. p ON l /\ p ON l' [2] by 0,projective;
  ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
             ~(?l. p ON l /\ p' ON l /\ p'' ON l) [3] by 0,projective;
  !l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                 p ON l /\ p' ON l /\ p'' ON l [4] by 0,projective;
// dual of axiom 1
  !l1 l2. ~(l1 = l2) ==> ?!p. p ON l1 /\ p ON l2 [5]
  proof
    let l1 l2 be Line;
    assume ~(l1 = l2) [6];
    consider p such that p ON l1 /\ p ON l2 [7] by 2;
    !p'. p' ON l1 /\ p' ON l2 ==> (p' = p)
    proof
      let p' be Point;
      assume p' ON l1 /\ p' ON l2 [8];
      assume ~(p' = p);
      l1 = l2 by 1,7,8;
      thus F by 6;
    end;
  qed by 7;
// dual of axiom 2
  !p1 p2. ?l. p1 ON l /\ p2 ON l [9]
  proof
    let p1 p2 be Point;
    cases;
    suppose p1 = p2;
    qed by 0,LEMMA_1;
    suppose ~(p1 = p2);
    qed by 1;
  end;
// dual of axiom 3
  ?l1 l2 l3. ~(l1 = l2) /\ ~(l2 = l3) /\ ~(l1 = l3) /\
             ~(?p. p ON l1 /\ p ON l2 /\ p ON l3) [10]
  proof
    consider p1 p2 p3 such that
      ~(p1 = p2) /\ ~(p2 = p3) /\ ~(p1 = p3) /\
      ~(?l. p1 ON l /\ p2 ON l /\ p3 ON l) [11] by 3;
    ~(p1 = p3) by 11;
    ?!l1. p1 ON l1 /\ p3 ON l1 by 1;  // ADDED STEP
    consider l1 such that p1 ON l1 /\ p3 ON l1 /\
      !l'. p1 ON l' /\ p3 ON l' ==> (l1 = l') [12];
    ~(p2 = p3) by 11;
    ?!l2. p2 ON l2 /\ p3 ON l2 by 1;  // ADDED STEP
    consider l2 such that p2 ON l2 /\ p3 ON l2 /\
      !l'. p2 ON l' /\ p3 ON l' ==> (l2 = l') [13];
    ~(p1 = p2) by 11;
    ?!l3. p1 ON l3 /\ p2 ON l3 by 1;  // ADDED STEP
    consider l3 such that p1 ON l3 /\ p2 ON l3 /\
      !l'. p1 ON l' /\ p2 ON l' ==> (l3 = l') [14];
    take l1; take l2; take l3;
    thus ~(l1 = l2) /\ ~(l2 = l3) /\ ~(l1 = l3) [15] by 11,12,13,14;
    assume ?q. q ON l1 /\ q ON l2 /\ q ON l3;
    consider q such that q ON l1 /\ q ON l2 /\ q ON l3;
    (p1 = q) /\ (p2 = q) /\ (p3 = q) by 5,12,13,14,15;
    thus F by 11;
  end;
// dual of axiom 4
  !p0. ?l0 L1 L2. ~(l0 = L1) /\ ~(L1 = L2) /\ ~(l0 = L2) /\
                  p0 ON l0 /\ p0 ON L1 /\ p0 ON L2
  proof
    let p0 be Point;
    consider l0 such that p0 ON l0 [16] by 0,LEMMA_1;
    consider p such that ~(p = p0) /\ p ON l0 [17] by 4;
    consider q such that ~(q ON l0) [18] by 3;
    consider l1 such that p ON l1 /\ q ON l1 [19] by 1,16;
    consider r such that r ON l1 /\ ~(r = p) /\ ~(r = q) [20]
    proof
      consider r1 r2 r3 such that
        ~(r1 = r2) /\ ~(r2 = r3) /\ ~(r1 = r3) /\
       r1 ON l1 /\ r2 ON l1 /\ r3 ON l1 [21] by 4;
      ~(r1 = p) /\ ~(r1 = q) \/
      ~(r2 = p) /\ ~(r2 = q) \/
      ~(r3 = p) /\ ~(r3 = q);
    qed by 21;
    ~(p0 ON l1) [22]
    proof
      assume p0 ON l1;
      l1 = l0 by 1,16,17,19;
    qed by 18,19;
    ~(p0 = r) by 20;
    consider L1 such that r ON L1 /\ p0 ON L1 [23] by 1;
    consider L2 such that q ON L2 /\ p0 ON L2 [24] by 1,16,18;
    take l0; take L1; take L2;
    thus ~(l0 = L1) by 0,17,19,20,22,23,LEMMA_2;
    thus ~(L1 = L2) by 0,19,20,22,23,24,LEMMA_2;
    thus ~(l0 = L2) by 18,24;
    thus p0 ON l0 /\ p0 ON L2 /\ p0 ON L1 by 16,24,23;
  end;
qed by REWRITE_TAC,5,9,10,projective`;;

unhide_constant "ON";;

(* ======== Mizarlight/duality_holby.ml ==================================== *)

horizon := 1;;

let Line_INDUCT,Line_RECURSION = define_type
 "fano_Line = Line_1 | Line_2 | Line_3 | Line_4 |
              Line_5 | Line_6 | Line_7";;

let Point_INDUCT,Point_RECURSION = define_type
 "fano_Point = Point_1 | Point_2 | Point_3 | Point_4 |
               Point_5 | Point_6 | Point_7";;

let Point_DISTINCT = distinctness "fano_Point";;

let Line_DISTINCT = distinctness "fano_Line";;

let fano_incidence =
  [1,1; 1,2; 1,3; 2,1; 2,4; 2,5; 3,1; 3,6; 3,7; 4,2; 4,4;
   4,6; 5,2; 5,5; 5,7; 6,3; 6,4; 6,7; 7,3; 7,5; 7,6];;

let fano_point i = mk_const("Point_"^string_of_int i,[])
and fano_line i = mk_const("Line_"^string_of_int i,[]);;

let fano_clause (i,j) =
  let p = `p:fano_Point` and l = `l:fano_Line` in
  mk_conj(mk_eq(p,fano_point i),mk_eq(l,fano_line j));;

let ON = new_definition
 (mk_eq(`((ON):fano_Point->fano_Line->bool) p l`,
        list_mk_disj(map fano_clause fano_incidence)));;

let ON_CLAUSES = prove
 (list_mk_conj(allpairs
    (fun i j -> mk_eq(list_mk_comb(`(ON)`,[fano_point i; fano_line j]),
                      if mem (i,j) fano_incidence then `T` else `F`))
    (1--7) (1--7)),
  REWRITE_TAC[ON; Line_DISTINCT; Point_DISTINCT]);;

let FORALL_POINT = thm `;
  !P. (!p. P p) <=> P Point_1 /\ P Point_2 /\ P Point_3 /\ P Point_4 /\
                    P Point_5 /\ P Point_6 /\ P Point_7
    by Point_INDUCT`;;

let EXISTS_POINT = thm `;
  !P. (?p. P p) <=> P Point_1 \/ P Point_2 \/ P Point_3 \/ P Point_4 \/
                    P Point_5 \/ P Point_6 \/ P Point_7
proof
  let P be fano_Point->bool;
  ~(?p. P p) <=> ~(P Point_1 \/ P Point_2 \/ P Point_3 \/ P Point_4 \/
                   P Point_5 \/ P Point_6 \/ P Point_7)
    by REWRITE_TAC,DE_MORGAN_THM,NOT_EXISTS_THM,FORALL_POINT;
qed`;;

let FORALL_LINE = thm `;
  !P. (!p. P p) <=> P Line_1 /\ P Line_2 /\ P Line_3 /\ P Line_4 /\
                    P Line_5 /\ P Line_6 /\ P Line_7
    by Line_INDUCT`;;

let EXISTS_LINE = thm `;
  !P. (?p. P p) <=> P Line_1 \/ P Line_2 \/ P Line_3 \/ P Line_4 \/
                    P Line_5 \/ P Line_6 \/ P Line_7
proof
  let P be fano_Line->bool;
  ~(?p. P p) <=> ~(P Line_1 \/ P Line_2 \/ P Line_3 \/ P Line_4 \/
                   P Line_5 \/ P Line_6 \/ P Line_7)
    by REWRITE_TAC,DE_MORGAN_THM,NOT_EXISTS_THM,FORALL_LINE;
qed;`;;

let FANO_TAC =
  GEN_REWRITE_TAC DEPTH_CONV
   [FORALL_POINT; EXISTS_LINE; EXISTS_POINT; FORALL_LINE] THEN
  GEN_REWRITE_TAC DEPTH_CONV
   (basic_rewrites() @ [ON_CLAUSES; Point_DISTINCT; Line_DISTINCT]);;

let AXIOM_1 = thm `;
  !p p'. ~(p = p') ==> ?l. p ON l /\ p' ON l /\
                           !l'. p ON l' /\ p' ON l' ==> (l' = l)
    by TIMED_TAC 3 FANO_TAC`;;

let AXIOM_2 = thm `;
  !l l'. ?p. p ON l /\ p ON l' by FANO_TAC`;;

let AXIOM_3 = thm `;
  ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
             ~(?l. p ON l /\ p' ON l /\ p'' ON l)
    by TIMED_TAC 2 FANO_TAC`;;

let AXIOM_4 = thm `;
  !l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                 p ON l /\ p' ON l /\ p'' ON l
    by TIMED_TAC 3 FANO_TAC`;;

let AXIOM_1' = thm `;
  !p p' l l'. ~(p = p') /\ p ON l /\ p' ON l /\ p ON l' /\ p' ON l'
              ==> (l' = l)
proof
  let p p' be fano_Point;
  let l l' be fano_Line;
  assume ~(p = p') /\ p ON l /\ p' ON l /\ p ON l' /\ p' ON l' [1];
  consider l1 such that p ON l1 /\ p' ON l1 /\
                        !l'. p ON l' /\ p' ON l' ==> (l' = l1) [2]
    by 1,AXIOM_1;
  l = l1 by 1,2;
    .= l' by 1,2;
qed`;;

let LEMMA_1' = thm `;
  !O. ?l. O ON l
proof
  consider p p' p'' such that
    ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p ON l /\ p' ON l /\ p'' ON l) [1] by AXIOM_3;
  let O be fano_Point;
  ~(p = O) \/ ~(p' = O) by 1;
  consider P such that ~(P = O) [2];
  consider l such that O ON l /\ P ON l /\
    !l'. O ON l' /\ P ON l' ==> (l' = l) [3] by 2,AXIOM_1;
  thus ?l. O ON l by 3;
end`;;

let DUAL_1 = thm `;
  !l l'. ~(l = l') ==> ?p. p ON l /\ p ON l' /\
         !p'. p' ON l /\ p' ON l' ==> (p' = p)
proof
  assume ~thesis;
  consider l l' such that ~(l = l') /\ !p. p ON l /\ p ON l'
                          ==> ?p'. p' ON l /\ p' ON l' /\ ~(p' = p) [1];
  consider p such that p ON l /\ p ON l' [2] by AXIOM_2;
  consider p' such that p' ON l /\ p' ON l' /\ ~(p' = p) [3] by 1,2;
  thus F by 1,2,AXIOM_1';
end`;;

let DUAL_2 = thm `;
  !p p'. ?l. p ON l /\ p' ON l
proof
  let p p' be fano_Point;
  ?l. p ON l [1] by LEMMA_1';
  (p = p') \/
    ?l. p ON l /\ p' ON l /\
        !l'. p ON l' /\ p' ON l' ==> (l' = l) by AXIOM_1;
qed by 1`;;

let DUAL_3 = thm `;
  ?l1 l2 l3. ~(l1 = l2) /\ ~(l2 = l3) /\ ~(l1 = l3) /\
             ~(?p. p ON l1 /\ p ON l2 /\ p ON l3)
proof
  consider p1 p2 p3 such that
    ~(p1 = p2) /\ ~(p2 = p3) /\ ~(p1 = p3) /\
    ~(?l. p1 ON l /\ p2 ON l /\ p3 ON l) [1] by AXIOM_3;
  consider l1 such that p1 ON l1 /\ p3 ON l1 [2] by DUAL_2;
  consider l2 such that p2 ON l2 /\ p3 ON l2 [3] by DUAL_2;
  consider l3 such that p1 ON l3 /\ p2 ON l3 [4] by DUAL_2;
  take l1; take l2; take l3;
  thus ~(l1 = l2) /\ ~(l2 = l3) /\ ~(l1 = l3) [5] by 1,2,3,4;
  assume ~thesis;
  consider q such that q ON l1 /\ q ON l2 /\ q ON l3 [6];
  consider q' such that q' ON l1 /\ q' ON l3 /\
    !p'. p' ON l1 /\ p' ON l3 ==> (p' = q') [7] by 5,DUAL_1;
  q = q' by 6,7;
    .= p1 by 2,4,7;
  thus F by 1,3,6;
end`;;

let DUAL_4 = thm `;
  !O. ?OP OQ OR. ~(OP = OQ) /\ ~(OQ = OR) /\ ~(OP = OR) /\
                 O ON OP /\ O ON OQ /\ O ON OR
proof
  let O be fano_Point;
  consider OP such that O ON OP [1] by LEMMA_1';
  consider p p' p'' such that
    ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p ON OP /\ p' ON OP /\ p'' ON OP [2] by AXIOM_4;
  ~(p = O) \/ ~(p' = O) by 2;
  consider P such that ~(P = O) /\ P ON OP [3] by 2;
  consider q q' q'' such that
    ~(q = q') /\ ~(q' = q'') /\ ~(q = q'') /\
    ~(?l. q ON l /\ q' ON l /\ q'' ON l) [4] by AXIOM_3;
  ~(q ON OP) \/ ~(q' ON OP) \/ ~(q'' ON OP) by 4;
  consider Q such that ~(Q ON OP) [5];
  consider l such that P ON l /\ Q ON l [6] by DUAL_2;
  consider r r' r'' such that
  ~(r = r') /\ ~(r' = r'') /\ ~(r = r'') /\
  r ON l /\ r' ON l /\ r'' ON l [7] by AXIOM_4;
  ((r = P) \/ (r = Q) \/ ~(r = P) /\ ~(r = Q)) /\
  ((r' = P) \/ (r' = Q) \/ ~(r' = P) /\ ~(r' = Q));
  consider R such that R ON l /\ ~(R = P) /\ ~(R = Q) [8] by 7;
  consider OQ such that O ON OQ /\ Q ON OQ [9] by DUAL_2;
  consider OR such that O ON OR /\ R ON OR [10] by DUAL_2;
  take OP; take OQ; take OR;
  ~(O ON l) by 1,3,5,6,AXIOM_1';
  thus ~(OP = OQ) /\ ~(OQ = OR) /\ ~(OP = OR) /\
       O ON OP /\ O ON OQ /\ O ON OR by 1,3,5,6,8,9,10,AXIOM_1';
end`;;

(* ======== Tutorial/Changing_proof_style.ml =============================== *)

horizon := 1;;

let NSQRT_2_4 = thm `;
  !p q. p * p = 2 * q * q ==> q = 0
proof
  !p. (!m. m < p ==> (!q. m * m = 2 * q * q ==> q = 0))
      ==> (!q. p * p = 2 * q * q ==> q = 0)
  proof
    let p be num;
    assume !m. m < p ==> !q. m * m = 2 * q * q ==> q = 0 [A];
    let q be num;
    assume p * p = 2 * q * q [B];
    EVEN(p * p) <=> EVEN(2 * q * q);
    EVEN(p) by TIMED_TAC 2 o MESON_TAC,ARITH,EVEN_MULT;
//  "EVEN 2 by CONV_TAC o HOL_BY,ARITH;" takes over a minute...
    consider m such that p = 2 * m [C] by EVEN_EXISTS;
    cases by ARITH_TAC;
    suppose q < p;
      q * q = 2 * m * m ==> m = 0 by A;
    qed by NUM_RING,B,C;
    suppose p <= q;
      p * p <= q * q by LE_MULT2;
      q * q = 0 by ARITH_TAC,B;
    qed by NUM_RING;
  end;
qed by MATCH_MP_TAC,num_WF`;;

