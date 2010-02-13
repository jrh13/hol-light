(* ========================================================================= *)
(* Mizar Light proof of duality in projective geometry.                      *)
(* ========================================================================= *)

let holby_prover =
  fun ths (asl,w as gl) -> ACCEPT_TAC(HOL_BY ths w) gl;;

current_prover := holby_prover;;

(* ------------------------------------------------------------------------- *)
(* To avoid adding any axioms, pick a simple model: the Fano plane.          *)
(* ------------------------------------------------------------------------- *)

let Line_INDUCT,Line_RECURSION = define_type
 "Line = Line_1 | Line_2 | Line_3 | Line_4 |
         Line_5 | Line_6 | Line_7";;

let Point_INDUCT,Point_RECURSION = define_type
 "Point = Point_1 | Point_2 | Point_3 | Point_4 |
          Point_5 | Point_6 | Point_7";;

let Point_DISTINCT = distinctness "Point";;

let Line_DISTINCT = distinctness "Line";;

let fano_incidence =
  [1,1; 1,2; 1,3; 2,1; 2,4; 2,5; 3,1; 3,6; 3,7; 4,2; 4,4;
   4,6; 5,2; 5,5; 5,7; 6,3; 6,4; 6,7; 7,3; 7,5; 7,6];;

let fano_point i = mk_const("Point_"^string_of_int i,[])
and fano_line i = mk_const("Line_"^string_of_int i,[]);;

let p = `p:Point` and l = `l:Line` ;;

let fano_clause (i,j) =
  mk_conj(mk_eq(p,fano_point i),mk_eq(l,fano_line j));;

(* ------------------------------------------------------------------------- *)
(* Define the incidence relation "ON" from "fano_incidence"                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("ON",(11,"right"));;

let ON = new_definition
 (mk_eq(`((ON):Point->Line->bool) p l`,
        list_mk_disj(map fano_clause fano_incidence)));;

(* ------------------------------------------------------------------------- *)
(* Also produce a more convenient case-by-case rewrite.                      *)
(* ------------------------------------------------------------------------- *)

let ON_CLAUSES = prove
 (list_mk_conj(allpairs
    (fun i j -> mk_eq(list_mk_comb(`(ON)`,[fano_point i; fano_line j]),
                      if mem (i,j) fano_incidence then `T` else `F`))
    (1--7) (1--7)),
  REWRITE_TAC[ON; Line_DISTINCT; Point_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* Case analysis theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let FORALL_POINT = prove
 (`(!p. P p) <=> P Point_1 /\ P Point_2 /\ P Point_3 /\ P Point_4 /\
                 P Point_5 /\ P Point_6 /\ P Point_7`,
  EQ_TAC THEN REWRITE_TAC[Point_INDUCT] THEN SIMP_TAC[]);;

let EXISTS_POINT = prove
 (`(?p. P p) <=> P Point_1 \/ P Point_2 \/ P Point_3 \/ P Point_4 \/
                 P Point_5 \/ P Point_6 \/ P Point_7`,
  MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_POINT]);;

let FORALL_LINE = prove
 (`(!p. P p) <=> P Line_1 /\ P Line_2 /\ P Line_3 /\ P Line_4 /\
                 P Line_5 /\ P Line_6 /\ P Line_7`,
  EQ_TAC THEN REWRITE_TAC[Line_INDUCT] THEN SIMP_TAC[]);;

let EXISTS_LINE = prove
 (`(?p. P p) <=> P Line_1 \/ P Line_2 \/ P Line_3 \/ P Line_4 \/
                 P Line_5 \/ P Line_6 \/ P Line_7`,
  MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_LINE]);;

(* ------------------------------------------------------------------------- *)
(* Hence prove the axioms by a naive case split (a bit slow but easy).       *)
(* ------------------------------------------------------------------------- *)

let FANO_TAC =
  GEN_REWRITE_TAC DEPTH_CONV
   [FORALL_POINT; EXISTS_LINE; EXISTS_POINT; FORALL_LINE] THEN
  GEN_REWRITE_TAC DEPTH_CONV
   (basic_rewrites() @ [ON_CLAUSES; Point_DISTINCT; Line_DISTINCT]);;

let AXIOM_1 = time prove
 (`!p p'. ~(p = p') ==> ?l. p ON l /\ p' ON l /\
     !l'. p ON l' /\ p' ON l' ==> (l' = l)`,
  FANO_TAC);;

let AXIOM_2 = time prove
 (`!l l'. ?p. p ON l /\ p ON l'`,
  FANO_TAC);;

let AXIOM_3 = time prove
 (`?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p ON l /\ p' ON l /\ p'' ON l)`,
  FANO_TAC);;

let AXIOM_4 = time prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p ON l /\ p' ON l /\ p'' ON l`,
  FANO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Now the interesting bit.                                                  *)
(* ------------------------------------------------------------------------- *)

let AXIOM_1' = theorem
 "!p p' l l'. ~(p = p') /\\ p ON l /\\ p' ON l /\\ p ON l' /\\ p' ON l'
    ==> (l' = l)"
 [fix ["p:Point"; "p':Point"; "l:Line"; "l':Line"];
  assume "~(p = p') /\\ p ON l /\\ p' ON l /\\ p ON l' /\\ p' ON l'" at 1;
  consider ["l1:Line"] st "p ON l1 /\\ p' ON l1 /\\
    !l'. p ON l' /\\ p' ON l' ==> (l' = l1)" from [1] by [AXIOM_1] at 2;
  have "l = l1" from [1;2];
  so have "... = l'" from [1;2];
  qed];;

let LEMMA_1 = theorem
 "!O. ?l. O ON l"
 [consider ["p:Point"; "p':Point"; "p'':Point"] st
   "~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
     ~(?l. p ON l /\\ p' ON l /\\ p'' ON l)" by [AXIOM_3] at 1;
  fix ["O:Point"];
  have "~(p = O) \/ ~(p' = O)" from [1];
  so consider ["P:Point"] st "~(P = O)" at 2;
  consider ["l:Line"] st "O ON l /\\ P ON l /\\
    !l'. O ON l' /\\ P ON l' ==> (l' = l)" from [2] by [AXIOM_1] at 3;
  thus "?l. O ON l" from [3]];;

let DUAL_1 = theorem
 "!l l'. ~(l = l') ==> ?p. p ON l /\\ p ON l' /\\
    !p'. p' ON l /\\ p' ON l' ==> (p' = p)"
 [otherwise consider ["l:Line"; "l':Line"] st
   "~(l = l') /\\ !p. p ON l /\\ p ON l'
     ==> ?p'. p' ON l /\\ p' ON l' /\\ ~(p' = p)" at 1;
  consider ["p:Point"] st "p ON l /\\ p ON l'" by [AXIOM_2] at 2;
  consider ["p':Point"] st "p' ON l /\\ p' ON l' /\\ ~(p' = p)" from [1;2] at 3;
  hence contradiction from [1;2] by [AXIOM_1']];;

let DUAL_2 = theorem
 "!p p'. ?l. p ON l /\\ p' ON l"
 [fix ["p:Point"; "p':Point"];
  have "?l. p ON l" by [LEMMA_1] at 1;
  have "(p = p') \/
    ?l. p ON l /\\ p' ON l /\\
      !l'. p ON l' /\\ p' ON l' ==> (l' = l)" by [AXIOM_1];
  hence thesis from [1]];;

let DUAL_3 = theorem
 "?l1 l2 l3. ~(l1 = l2) /\\ ~(l2 = l3) /\\ ~(l1 = l3) /\\
    ~(?p. p ON l1 /\\ p ON l2 /\\ p ON l3)"
 [consider ["p1:Point"; "p2:Point"; "p3:Point"] st
   "~(p1 = p2) /\\ ~(p2 = p3) /\\ ~(p1 = p3) /\\
      ~(?l. p1 ON l /\\ p2 ON l /\\ p3 ON l)" by [AXIOM_3] at 1;
  consider ["l1:Line"] st "p1 ON l1 /\\ p3 ON l1" by [DUAL_2] at 2;
  consider ["l2:Line"] st "p2 ON l2 /\\ p3 ON l2" by [DUAL_2] at 3;
  consider ["l3:Line"] st "p1 ON l3 /\\ p2 ON l3" by [DUAL_2] at 4;
  take ["l1"; "l2"; "l3"];
  thus "~(l1 = l2) /\\ ~(l2 = l3) /\\ ~(l1 = l3)" from [1;2;3;4] at 5;
  otherwise consider ["q:Point"] st "q ON l1 /\\ q ON l2 /\\ q ON l3" at 6;
  consider ["q':Point"] st "q' ON l1 /\\ q' ON l3 /\\
    !p'. p' ON l1 /\\ p' ON l3 ==> (p' = q')" from [5] by [DUAL_1] at 7;
  have "q = q'" from [6;7];
  so have "... = p1" from [2;4;7];
  hence contradiction from [1;3;6]];;

let DUAL_4 = theorem
 "!O. ?OP OQ OR. ~(OP = OQ) /\\ ~(OQ = OR) /\\ ~(OP = OR) /\\
    O ON OP /\\ O ON OQ /\\ O ON OR"
 [fix ["O:Point"];
  consider ["OP:Line"] st "O ON OP" by [LEMMA_1] at 1;
  consider ["p:Point"; "p':Point"; "p'':Point"] st
   "~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
      p ON OP /\\ p' ON OP /\\ p'' ON OP" by [AXIOM_4] at 2;
  have "~(p = O) \/ ~(p' = O)" from [2];
  so consider ["P:Point"] st "~(P = O) /\\ P ON OP" from [2] at 3;
  consider ["q:Point"; "q':Point"; "q'':Point"] st
   "~(q = q') /\\ ~(q' = q'') /\\ ~(q = q'') /\\
      ~(?l. q ON l /\\ q' ON l /\\ q'' ON l)" by [AXIOM_3] at 4;
  have "~(q ON OP) \/ ~(q' ON OP) \/ ~(q'' ON OP)" from [4];
  so consider ["Q:Point"] st "~(Q ON OP)" at 5;
  consider ["l:Line"] st "P ON l /\\ Q ON l" by [DUAL_2] at 6;
  consider ["r:Point"; "r':Point"; "r'':Point"] st
   "~(r = r') /\\ ~(r' = r'') /\\ ~(r = r'') /\\
      r ON l /\\ r' ON l /\\ r'' ON l" by [AXIOM_4] at 7;
  have "((r = P) \/ (r = Q) \/ ~(r = P) /\\ ~(r = Q)) /\\
    ((r' = P) \/ (r' = Q) \/ ~(r' = P) /\\ ~(r' = Q))";
  so consider ["R:Point"] st "R ON l /\\ ~(R = P) /\\ ~(R = Q)" from [7] at 8;
  consider ["OQ:Line"] st "O ON OQ /\\ Q ON OQ" by [DUAL_2] at 9;
  consider ["OR:Line"] st "O ON OR /\\ R ON OR" by [DUAL_2] at 10;
  take ["OP"; "OQ"; "OR"];
  have "~(O ON l)" from [1;3;5;6] by [AXIOM_1'];
  hence "~(OP = OQ) /\\ ~(OQ = OR) /\\ ~(OP = OR) /\\
    O ON OP /\\ O ON OQ /\\ O ON OR" from [1;3;5;6;8;9;10] by [AXIOM_1']];;
