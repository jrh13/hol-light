let string_INDUCT,string_RECURSION = define_type
 "string = String num";;

parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(15,"right"));;
parse_as_infix("-->",(14,"right"));;
parse_as_infix("<->",(13,"right"));;

parse_as_prefix "Not";;
parse_as_prefix "Box";;
parse_as_prefix "Diamond";;

let form_INDUCT,form_RECURSION = define_type
 "form = False
       | True
       | Atom string
       | Not form
       | && form form
       | || form form
       | --> form form
       | <-> form form
       | Box form
       | Diamond form";;

let holds = define
 `(holds (W,R) V False w <=> F) /\
  (holds (W,R) V True w <=> T) /\
  (holds (W,R) V (Atom a) w <=> V a w) /\
  (holds (W,R) V (Not p) w <=> ~(holds (W,R) V p w)) /\
  (holds (W,R) V (p && q) w <=> holds (W,R) V p w /\ holds (W,R) V q w) /\
  (holds (W,R) V (p || q) w <=> holds (W,R) V p w \/ holds (W,R) V q w) /\
  (holds (W,R) V (p --> q) w <=> holds (W,R) V p w ==> holds (W,R) V q w) /\
  (holds (W,R) V (p <-> q) w <=> holds (W,R) V p w <=> holds (W,R) V q w) /\
  (holds (W,R) V (Box p) w <=>
        !w'. w' IN W /\ R w w' ==> holds (W,R) V p w') /\
  (holds (W,R) V (Diamond p) w <=>
        ?w'. w' IN W /\ R w w' /\ holds (W,R) V p w')`;;

let holds_in = new_definition
 `holds_in (W,R) p = !V w. w IN W ==> holds (W,R) V p w`;;

parse_as_infix("|=",(11,"right"));;

let valid = new_definition
 `L |= p <=> !f. L f ==> holds_in f p`;;

let S4 = new_definition
 `S4(W,R) <=> ~(W = {}) /\ (!x y. R x y ==> x IN W /\ y IN W) /\
              (!x. x IN W ==> R x x) /\
              (!x y z. R x y /\ R y z ==> R x z)`;;

let LTL = new_definition
 `LTL(W,R) <=> (W = UNIV) /\ !x y:num. R x y <=> x <= y`;;

let GL = new_definition
 `GL(W,R) <=> ~(W = {}) /\ (!x y. R x y ==> x IN W /\ y IN W) /\
              WF(\x y. R y x) /\ (!x y z:num. R x y /\ R y z ==> R x z)`;;

let MODAL_TAC =
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds] THEN MESON_TAC[];;

let MODAL_RULE tm = prove(tm,MODAL_TAC);;

let TAUT_1 = MODAL_RULE `L |= Box True`;;
let TAUT_2 = MODAL_RULE `L |= Box(A --> B) --> Box A --> Box B`;;
let TAUT_3 = MODAL_RULE `L |= Diamond(A --> B) --> Box A --> Diamond B`;;
let TAUT_4 = MODAL_RULE `L |= Box(A --> B) --> Diamond A --> Diamond B`;;
let TAUT_5 = MODAL_RULE `L |= Box(A && B) --> Box A && Box B`;;
let TAUT_6 = MODAL_RULE `L |= Diamond(A || B) --> Diamond A || Diamond B`;;

let HOLDS_FORALL_LEMMA = prove
 (`!W R P. (!A V. P(holds (W,R) V A)) <=> (!p:W->bool. P p)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN GEN_TAC; SIMP_TAC[]] THEN
  POP_ASSUM(MP_TAC o SPECL [`Atom a`; `\a:string. (p:W->bool)`]) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[holds] THEN REWRITE_TAC[ETA_AX]);;

let MODAL_SCHEMA_TAC =
  REWRITE_TAC[holds_in; holds] THEN MP_TAC HOLDS_FORALL_LEMMA THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]);;

let MODAL_REFL = prove
 (`!W R. (!w:W. w IN W ==> R w w) <=> !A. holds_in (W,R) (Box A --> A)`,
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let MODAL_TRANS = prove
 (`!W R. (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                       R w w' /\ R w' w'' ==> R w w'') <=>
         (!A. holds_in (W,R) (Box A --> Box(Box A)))`,
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let MODAL_SERIAL = prove
 (`!W R. (!w:W. w IN W ==> ?w'. w' IN W /\ R w w') <=>
         (!A. holds_in (W,R) (Box A --> Diamond A))`,
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let MODAL_SYM = prove
 (`!W R. (!w w':W. w IN W /\ w' IN W /\ R w w' ==> R w' w) <=>
         (!A. holds_in (W,R) (A --> Box(Diamond A)))`,
  MODAL_SCHEMA_TAC THEN EQ_TAC THENL [MESON_TAC[]; REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\v:W. v = w`; `w:W`]) THEN ASM_MESON_TAC[]);;

let MODAL_WFTRANS = prove
 (`!W R. (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
         WF(\x y. x IN W /\ y IN W /\ R y x) <=>
         (!A. holds_in (W,R) (Box(Box A --> A) --> Box A))`,
  MODAL_SCHEMA_TAC THEN REWRITE_TAC[WF_IND] THEN EQ_TAC THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC;
    X_GEN_TAC `w:W` THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\v:W. v IN W /\ R w v /\ !w''. w'' IN W /\ R v w'' ==> R w w''`; `w:W`]);
    X_GEN_TAC `P:W->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\x:W. !w:W. x IN W /\ R w x ==> P x`) THEN
    MATCH_MP_TAC MONO_FORALL] THEN
  ASM_MESON_TAC[]);;
