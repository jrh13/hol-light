let fix ts = MAP_EVERY X_GEN_TAC ts;;

let assume lab t =
  DISCH_THEN(fun th -> if concl th = t then LABEL_TAC lab th
                       else failwith "assume");;

let we're finished tac = tac;;

let suffices_to_prove q tac = SUBGOAL_THEN q (fun th -> MP_TAC th THEN tac);;

let note(lab,t) tac =
  SUBGOAL_THEN t MP_TAC THENL [tac; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC lab th);;

let have t = note("",t);;

let cases (lab,t) tac =
  SUBGOAL_THEN t MP_TAC THENL [tac; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (LABEL_TAC lab));;

let consider (x,lab,t) tac =
  let tm = mk_exists(x,t) in
  SUBGOAL_THEN tm (X_CHOOSE_THEN x (LABEL_TAC lab)) THENL [tac; ALL_TAC];;

let trivial = MESON_TAC[];;
let algebra = CONV_TAC NUM_RING;;
let arithmetic = ARITH_TAC;;

let by labs tac = MAP_EVERY (fun l -> USE_THEN l MP_TAC) labs THEN tac;;

let using ths tac = MAP_EVERY MP_TAC ths THEN tac;;

let so constr arg tac = constr arg (FIRST_ASSUM MP_TAC THEN tac);;

let NSQRT_2 = prove
 (`!p q. p * p = 2 * q * q ==> q = 0`,
  suffices_to_prove
   `!p. (!m. m < p ==> (!q. m * m = 2 * q * q ==> q = 0))
        ==> (!q. p * p = 2 * q * q ==> q = 0)`
   (MATCH_ACCEPT_TAC num_WF) THEN
  fix [`p:num`] THEN
  assume("A") `!m. m < p ==> !q. m * m = 2 * q * q ==> q = 0` THEN
  fix [`q:num`] THEN
  assume("B") `p * p = 2 * q * q` THEN
  so have `EVEN(p * p) <=> EVEN(2 * q * q)` (trivial) THEN
  so have `EVEN(p)` (using [ARITH; EVEN_MULT] trivial) THEN
  so consider (`m:num`,"C",`p = 2 * m`) (using [EVEN_EXISTS] trivial) THEN
  cases ("D",`q < p \/ p <= q`) (arithmetic) THENL
   [so have `q * q = 2 * m * m ==> m = 0` (by ["A"] trivial) THEN
    so we're finished (by ["B"; "C"] algebra);

    so have `p * p <= q * q` (using [LE_MULT2] trivial) THEN
    so have `q * q = 0` (by ["B"] arithmetic) THEN
    so we're finished (algebra)]);;
