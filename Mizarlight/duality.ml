(* ========================================================================= *)
(* Mizar Light proof of duality in projective geometry.                      *)
(* ========================================================================= *)

current_prover := standard_prover;;

(* ------------------------------------------------------------------------- *)
(* Axioms for projective geometry.                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("ON",(11,"right"));;

let projective = new_definition
 `projective((ON):Point->Line->bool) <=>
        (!p p'. ~(p = p') ==> ?!l. p ON l /\ p' ON l) /\
        (!l l'. ?p. p ON l /\ p ON l') /\
        (?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                    ~(?l. p ON l /\ p' ON l /\ p'' ON l)) /\
        (!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                        p ON l /\ p' ON l /\ p'' ON l)`;;

(* ------------------------------------------------------------------------- *)
(* To get round extreme slowness of MESON for one situation.                 *)
(* ------------------------------------------------------------------------- *)

let USE_PROJ_TAC [prth; proj_def] =
  REWRITE_TAC[REWRITE_RULE[proj_def] prth];;

(* ------------------------------------------------------------------------- *)
(* The main result, via two lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1 = theorem
 "!(ON):Point->Line->bool. projective(ON) ==> !p. ?l. p ON l"
 [fix ["(ON):Point->Line->bool"];
  assume "projective(ON)" at 0;
  have "!p p'. ~(p = p') ==> ?!l. p ON l /\\ p' ON l"
    at 1 from [0] by [projective] using USE_PROJ_TAC;
  have "?p p' p''. ~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
                    ~(?l. p ON l /\\ p' ON l /\\ p'' ON l)"
    at 3 from [0] by [projective] using USE_PROJ_TAC;
  fix ["p:Point"];
  consider ["q:Point"; "q':Point"] st "~(q = q')" from [3];
  so have "~(p = q) \/ ~(p = q')";
  so consider ["l:Line"] st "p ON l" from [1];
  take ["l"];
  qed];;

let LEMMA_2 = theorem
 "!(ON):Point->Line->bool. projective(ON)
   ==> !p1 p2 q l l1 l2.
     p1 ON l /\\ p2 ON l /\\ p1 ON l1 /\\ p2 ON l2 /\\ q ON l2 /\\
     ~(q ON l) /\\ ~(p1 = p2) ==> ~(l1 = l2)"
 [fix ["(ON):Point->Line->bool"];
  assume "projective(ON)" at 0;
  have "!p p'. ~(p = p') ==> ?!l. p ON l /\\ p' ON l"
    at 1 from [0] by [projective] using USE_PROJ_TAC;
  fix ["p1:Point"; "p2:Point"; "q:Point"; "l:Line"; "l1:Line"; "l2:Line"];
  assume "p1 ON l" at 5;
  assume "p2 ON l" at 6;
  assume "p1 ON l1" at 7;
  assume "p2 ON l2" at 9;
  assume "q ON l2" at 10;
  assume "~(q ON l)" at 11;
  assume "~(p1 = p2)" at 12;
  assume "l1 = l2" at 13;
  so have "p1 ON l2" from [7];
  so have "l = l2" from [1;5;6;9;12];
  hence contradiction from [10;11]];;

let PROJECTIVE_DUALITY = theorem
 "!(ON):Point->Line->bool. projective(ON) ==> projective (\l p. p ON l)"
 [fix ["(ON):Point->Line->bool"];
  assume "projective(ON)" at 0;
  have "!p p'. ~(p = p') ==> ?!l. p ON l /\\ p' ON l"
    at 1 from [0] by [projective] using USE_PROJ_TAC;
  have "!l l'. ?p. p ON l /\\ p ON l'"
    at 2 from [0] by [projective] using USE_PROJ_TAC;
  have "?p p' p''. ~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
                    ~(?l. p ON l /\\ p' ON l /\\ p'' ON l)"
    at 3 from [0] by [projective] using USE_PROJ_TAC;
  have "!l. ?p p' p''. ~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
                        p ON l /\\ p' ON l /\\ p'' ON l"
    at 4 from [0] by [projective] using USE_PROJ_TAC;
(* dual of axiom 1 *)
  have "!l1 l2. ~(l1 = l2) ==> ?!p. p ON l1 /\\ p ON l2" at 5
  proof
   [fix ["l1:Line"; "l2:Line"];
    assume "~(l1 = l2)" at 6;
    consider ["p:Point"] st "p ON l1 /\\ p ON l2" at 7 from [2];
    have "!p'. p' ON l1 /\\ p' ON l2 ==> (p' = p)"
    proof
     [fix ["p':Point"];
      assume "p' ON l1 /\\ p' ON l2" at 8;
      assume "~(p' = p)";
      so have "l1 = l2" from [1;7;8];
      hence contradiction from [6]];
    qed from [7]];
(* dual of axiom 2 *)
  have "!p1 p2. ?l. p1 ON l /\\ p2 ON l" at 9
  proof
   [fix ["p1:Point"; "p2:Point"];
    per cases
     [[suppose "p1 = p2";
       qed from [0] by [LEMMA_1]];
      [suppose "~(p1 = p2)";
       qed from [1]]]];
(* dual of axiom 3 *)
  have "?l1 l2 l3. ~(l1 = l2) /\\ ~(l2 = l3) /\\ ~(l1 = l3) /\\
                    ~(?p. p ON l1 /\\ p ON l2 /\\ p ON l3)" at 10
  proof
   [consider ["p1:Point"; "p2:Point"; "p3:Point"] st
      "~(p1 = p2) /\\ ~(p2 = p3) /\\ ~(p1 = p3) /\\
                    ~(?l. p1 ON l /\\ p2 ON l /\\ p3 ON l)" from [3] at 11;
    have "~(p1 = p3)" from [11];
    so consider ["l1:Line"] st "p1 ON l1 /\\ p3 ON l1 /\\
        !l'. p1 ON l' /\\ p3 ON l' ==> (l1 = l')" from [1] at 12;
    have "~(p2 = p3)" from [11];
    so consider ["l2:Line"] st "p2 ON l2 /\\ p3 ON l2 /\\
        !l'. p2 ON l' /\\ p3 ON l' ==> (l2 = l')" from [1] at 13;
    have "~(p1 = p2)" from [11];
    so consider ["l3:Line"] st "p1 ON l3 /\\ p2 ON l3 /\\
        !l'. p1 ON l' /\\ p2 ON l' ==> (l3 = l')" from [1] at 14;
    take ["l1"; "l2"; "l3"];
    thus "~(l1 = l2) /\\ ~(l2 = l3) /\\ ~(l1 = l3)" from [11;12;13;14] at 15;
    assume "?q. q ON l1 /\\ q ON l2 /\\ q ON l3";
    so consider ["q:Point"] st "q ON l1 /\\ q ON l2 /\\ q ON l3";
    so have "(p1 = q) /\\ (p2 = q) /\\ (p3 = q)" from [5;12;13;14;15];
    hence contradiction from [11]];
(* dual of axiom 4 *)
  have "!p0. ?l0 L1 L2. ~(l0 = L1) /\\ ~(L1 = L2) /\\ ~(l0 = L2) /\\
                        p0 ON l0 /\\ p0 ON L1 /\\ p0 ON L2"
  proof
   [fix ["p0:Point"];
    consider ["l0:Line"] st "p0 ON l0" from [0] by [LEMMA_1] at 16;
    consider ["p:Point"] st "~(p = p0) /\\ p ON l0" from [4] at 17;
    consider ["q:Point"] st "~(q ON l0)" from [3] at 18;
    so consider ["l1:Line"] st "p ON l1 /\\ q ON l1" from [1;16] at 19;
    consider ["r:Point"] st "r ON l1 /\\ ~(r = p) /\\ ~(r = q)" at 20
    proof
     [consider ["r1:Point"; "r2:Point"; "r3:Point"] st
       "~(r1 = r2) /\\ ~(r2 = r3) /\\ ~(r1 = r3) /\\
                        r1 ON l1 /\\ r2 ON l1 /\\ r3 ON l1" from [4] at 21;
      so have "~(r1 = p) /\\ ~(r1 = q) \/
        ~(r2 = p) /\\ ~(r2 = q) \/
        ~(r3 = p) /\\ ~(r3 = q)";
      qed from [21]];
    have "~(p0 ON l1)" at 22
    proof
     [assume "p0 ON l1";
      so have "l1 = l0" from [1;16;17;19];
      qed from [18;19]];
    so have "~(p0 = r)" from [20];
    so consider ["L1:Line"] st "r ON L1 /\\ p0 ON L1" from [1] at 23;
    consider ["L2:Line"] st "q ON L2 /\\ p0 ON L2" from [1;16;18] at 24;
    take ["l0"; "L1"; "L2"];
    thus "~(l0 = L1)" from [0;17;19;20;22;23] by [LEMMA_2];
    thus "~(L1 = L2)" from [0;19;20;22;23;24] by [LEMMA_2];
    thus "~(l0 = L2)" from [18;24];
    thus "p0 ON l0 /\\ p0 ON L2 /\\ p0 ON L1" from [16;24;23]];
  qed from [5;9;10] by [projective]];;

current_prover := sketch_prover;;

let PROJECTIVE_DUALITY = theorem
 "!(ON):Point->Line->bool. projective(ON) = projective (\l p. p ON l)"
 [have "!(ON):Point->Line->bool. projective(ON) ==> projective (\l p. p ON l)"
  proof
   [fix ["(ON):Point->Line->bool"];
    assume "projective(ON)";
    have "!p p'. ~(p = p') ==> ?!l. p ON l /\\ p' ON l" at 1;
    have "!l l'. ?p. p ON l /\\ p ON l'" at 2;
    have "?p p' p''. ~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
                     ~(?l. p ON l /\\ p' ON l /\\ p'' ON l)" at 3;
    have "!l. ?p p' p''. ~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
                         p ON l /\\ p' ON l /\\ p'' ON l" at 4;
  (* dual of axiom 1 *)
    have "!l1 l2. ~(l1 = l2) ==> ?!p. p ON l1 /\\ p ON l2"
    proof
     [fix ["l1:Line"; "l2:Line"];
      otherwise have "?p p'. ~(l1 = l2) /\\ ~(p = p') /\\
        p ON l1 /\\ p' ON l1 /\\ p ON l2 /\\ p' ON l2";
      so have "l1 = l2" from [1];
      hence contradiction];
  (* dual of axiom 2 *)
    have "!p1 p2. ?l. p1 ON l /\\ p2 ON l"
    proof
     [fix ["p1:Point"; "p2:Point"];
      qed from [1]];
  (* dual of axiom 3 *)
    have "?l1 l2 l3. ~(l1 = l2) /\\ ~(l2 = l3) /\\ ~(l1 = l3) /\\
                     ~(?p. p ON l1 /\\ p ON l2 /\\ p ON l3)"
    proof
     [consider ["p1:Point"; "p2:Point"; "p3:Point"] st
        "~(p1 = p2) /\\ ~(p2 = p3) /\\ ~(p1 = p3) /\\
         ~(?l. p1 ON l /\\ p2 ON l /\\ p3 ON l)" from [3];
      consider ["l1:Line"] st "p1 ON l1 /\\ p3 ON l1 /\\
         !l'. p1 ON l' /\\ p3 ON l' ==> (l1 = l')" from [1];
      consider ["l2:Line"] st "p2 ON l2 /\\ p3 ON l2 /\\
         !l'. p2 ON l' /\\ p3 ON l' ==> (l2 = l')" from [1];
      consider ["l3:Line"] st "p1 ON l3 /\\ p2 ON l3 /\\
         !l'. p1 ON l' /\\ p2 ON l' ==> (l3 = l')" from [1];
      take ["l1"; "l2"; "l3"];
      thus "~(l1 = l2) /\\ ~(l2 = l3) /\\ ~(l1 = l3)";
      assume "?q. q ON l1 /\\ q ON l2 /\\ q ON l3";
      so consider ["q:Point"] st "q ON l1 /\\ q ON l2 /\\ q ON l3";
      have "(q = p1) \/ (q = p2) \/ (q = p3)";
      so have "p1 ON l2 \/ p2 ON l1 \/ p3 ON l3";
      hence contradiction];
  (* dual of axiom 4 *)
    have "!O. ?OP OQ OR. ~(OP = OQ) /\\ ~(OQ = OR) /\\ ~(OP = OR) /\\
                         O ON OP /\\ O ON OQ /\\ O ON OR"
    proof
     [fix ["O:Point"];
      consider ["OP:Line"] st "O ON OP";
      consider ["P:Point"] st "~(P = O) /\\ P ON OP";
      have "?Q:Point. ~(Q ON OP)"
      proof
       [otherwise have "!Q:Point. Q ON OP";
        so have "~(?p p' p''. ~(p = p') /\\ ~(p' = p'') /\\ ~(p = p'') /\\
                    ~(?l. p ON l /\\ p' ON l /\\ p'' ON l))";
        hence contradiction from [3]];
      so consider ["Q:Point"] st "~(Q ON OP)";
      consider ["l:Line"] st "P ON l /\\ Q ON l" from [1];
      consider ["R:Point"] st "R ON l /\\ ~(R = P) /\\ ~(R = Q)" from [4];
      have "~(P = Q) /\\ ~(R = P) /\\ ~(R = Q)";
      consider ["OQ:Line"] st "O ON OQ /\\ Q ON OQ";
      consider ["OR:Line"] st "O ON OR /\\ R ON OR";
      take ["OP"; "OQ"; "OR"];
      thus "~(OP = OQ)"
      proof
       [otherwise have "OP = OQ";
        hence contradiction];
      thus "~(OQ = OR)";
      thus "~(OP = OR)";
      thus "O ON OP /\\ O ON OQ /\\ O ON OR"];
    qed];
  have "!(ON):Point->Line->bool. projective (\l p. p ON l) ==> projective(ON)";
  qed];;

