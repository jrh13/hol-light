let line_INDUCT,line_RECURSION = define_type
 "line = Line_1 | Line_2 | Line_3 | Line_4 |
         Line_5 | Line_6 | Line_7";;

let point_INDUCT,point_RECURSION = define_type
 "point = Point_1 | Point_2 | Point_3 | Point_4 |
          Point_5 | Point_6 | Point_7";;

let fano_incidence =
  [1,1; 1,2; 1,3; 2,1; 2,4; 2,5; 3,1; 3,6; 3,7; 4,2; 4,4;
   4,6; 5,2; 5,5; 5,7; 6,3; 6,4; 6,7; 7,3; 7,5; 7,6];;

let fano_point i = mk_const("Point_"^string_of_int i,[]);;
let fano_line i = mk_const("Line_"^string_of_int i,[]);;
let p = `p:point` and l = `l:line` ;;

let fano_clause (i,j) = mk_conj(mk_eq(p,fano_point i),mk_eq(l,fano_line j));;

parse_as_infix("ON",(11,"right"));;

let ON = new_definition
 (mk_eq(`((ON):point->line->bool) p l`,
        list_mk_disj(map fano_clause fano_incidence)));;

let ON_CLAUSES = prove
 (list_mk_conj(allpairs
    (fun i j -> mk_eq(mk_comb(mk_comb(`(ON)`,fano_point i),fano_line j),
                      if mem (i,j) fano_incidence then `T` else `F`))
    (1--7) (1--7)),
  REWRITE_TAC[ON; distinctness "line"; distinctness "point"]);;

let FORALL_POINT = prove
 (`(!p. P p) <=> P Point_1 /\ P Point_2 /\ P Point_3 /\ P Point_4 /\
                 P Point_5 /\ P Point_6 /\ P Point_7`,
  EQ_TAC THENL [SIMP_TAC[]; REWRITE_TAC[point_INDUCT]]);;

let FORALL_LINE = prove
 (`(!p. P p) <=> P Line_1 /\ P Line_2 /\ P Line_3 /\ P Line_4 /\
                 P Line_5 /\ P Line_6 /\ P Line_7`,
  EQ_TAC THENL [SIMP_TAC[]; REWRITE_TAC[line_INDUCT]]);;

let EXISTS_POINT = prove
 (`(?p. P p) <=> P Point_1 \/ P Point_2 \/ P Point_3 \/ P Point_4 \/
                 P Point_5 \/ P Point_6 \/ P Point_7`,
  MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_POINT]);;

let EXISTS_LINE = prove
 (`(?p. P p) <=> P Line_1 \/ P Line_2 \/ P Line_3 \/ P Line_4 \/
                 P Line_5 \/ P Line_6 \/ P Line_7`,
  MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_LINE]);;

let FANO_TAC =
  GEN_REWRITE_TAC DEPTH_CONV
   [FORALL_POINT; EXISTS_LINE; EXISTS_POINT; FORALL_LINE] THEN
  GEN_REWRITE_TAC DEPTH_CONV
   (basic_rewrites() @
    [ON_CLAUSES; distinctness "point"; distinctness "line"]);;

let FANO_RULE tm = prove(tm,FANO_TAC);;

let AXIOM_1 = FANO_RULE
`!p p'. ~(p = p') ==> ?l. p ON l /\ p' ON l /\
                          !l'. p ON l' /\ p' ON l' ==> l' = l`;;

let AXIOM_2 = FANO_RULE
 `!l l'. ?p. p ON l /\ p ON l'`;;

let AXIOM_3 = FANO_RULE
 `?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
             ~(?l. p ON l /\ p' ON l /\ p'' ON l)`;;

let AXIOM_4 = FANO_RULE
  `!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                  p ON l /\ p' ON l /\ p'' ON l`;;
