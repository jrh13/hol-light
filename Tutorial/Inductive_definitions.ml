(* ------------------------------------------------------------------------- *)
(* Bug puzzle.                                                               *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let move = new_definition
 `move ((ax,ay),(bx,by),(cx,cy)) ((ax',ay'),(bx',by'),(cx',cy')) <=>
        (?a. ax' = ax + a * (cx - bx) /\ ay' = ay + a * (cy - by) /\
             bx' = bx /\ by' = by /\ cx' = cx /\ cy' = cy) \/
        (?b. bx' = bx + b * (ax - cx) /\ by' = by + b * (ay - cy) /\
             ax' = ax /\ ay' = ay /\ cx' = cx /\ cy' = cy) \/
        (?c. ax' = ax /\ ay' = ay /\ bx' = bx /\ by' = by /\
             cx' = cx + c * (bx - ax) /\ cy' = cy + c * (by - ay))`;;

let reachable_RULES,reachable_INDUCT,reachable_CASES =
 new_inductive_definition
  `(!p. reachable p p) /\
   (!p q r. move p q /\ reachable q r ==> reachable p r)`;;

let oriented_area = new_definition
 `oriented_area ((ax,ay),(bx,by),(cx,cy)) =
      ((bx - ax) * (cy - ay) - (cx - ax) * (by - ay)) / &2`;;

let MOVE_INVARIANT = prove
 (`!p p'. move p p' ==> oriented_area p = oriented_area p'`,
  REWRITE_TAC[FORALL_PAIR_THM; move; oriented_area] THEN CONV_TAC REAL_RING);;

let REACHABLE_INVARIANT = prove
 (`!p p'. reachable p p' ==> oriented_area p = oriented_area p'`,
  MATCH_MP_TAC reachable_INDUCT THEN MESON_TAC[MOVE_INVARIANT]);;

let IMPOSSIBILITY_B = prove
 (`~(reachable ((&0,&0),(&3,&0),(&0,&3)) ((&1,&2),(&2,&5),(-- &2,&3)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((&1,&2),(-- &2,&3),(&2,&5)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((&2,&5),(&1,&2),(-- &2,&3)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((&2,&5),(-- &2,&3),(&1,&2)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((-- &2,&3),(&1,&2),(&2,&5)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((-- &2,&3),(&2,&5),(&1,&2)))`,
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP REACHABLE_INVARIANT) THEN
  REWRITE_TAC[oriented_area] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Verification of a simple concurrent program.                              *)
(* ------------------------------------------------------------------------- *)

let init = new_definition
 `init (x,y,pc1,pc2,sem) <=>
        pc1 = 10 /\ pc2 = 10 /\ x = 0 /\ y = 0 /\ sem = 1`;;

let trans = new_definition
 `trans (x,y,pc1,pc2,sem) (x',y',pc1',pc2',sem') <=>
        pc1 = 10 /\ sem > 0 /\ pc1' = 20 /\ sem' = sem - 1 /\
                   (x',y',pc2') = (x,y,pc2) \/
        pc2 = 10 /\ sem > 0 /\ pc2' = 20 /\ sem' = sem - 1 /\
                   (x',y',pc1') = (x,y,pc1) \/
        pc1 = 20 /\ pc1' = 30 /\ x' = x + 1 /\
                   (y',pc2',sem') = (y,pc2,sem) \/
        pc2 = 20 /\ pc2' = 30 /\ y' = y + 1 /\ x' = x /\
                   pc1' = pc1 /\ sem' = sem \/
        pc1 = 30 /\ pc1' = 10 /\ sem' = sem + 1 /\
                   (x',y',pc2') = (x,y,pc2) \/
        pc2 = 30 /\ pc2' = 10 /\ sem' = sem + 1 /\
                   (x',y',pc1') = (x,y,pc1)`;;

let mutex = new_definition
 `mutex (x,y,pc1,pc2,sem) <=> pc1 = 10 \/ pc2 = 10`;;

let indinv = new_definition
 `indinv (x:num,y:num,pc1,pc2,sem) <=>
        sem + (if pc1 = 10 then 0 else 1) + (if pc2 = 10 then 0 else 1) = 1`;;

needs "Library/rstc.ml";;

let INDUCTIVE_INVARIANT = prove
 (`!init invariant transition P.
        (!s. init s ==> invariant s) /\
        (!s s'. invariant s /\ transition s s' ==> invariant s') /\
        (!s. invariant s ==> P s)
        ==> !s s':A. init s /\ RTC transition s s' ==> P s'`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`transition:A->A->bool`;
    `\s s':A. invariant s ==> invariant s'`] RTC_INDUCT) THEN
  MESON_TAC[]);;

let MUTEX = prove
 (`!s s'. init s /\ RTC trans s s' ==> mutex s'`,
  MATCH_MP_TAC INDUCTIVE_INVARIANT THEN EXISTS_TAC `indinv` THEN
  REWRITE_TAC[init; trans; indinv; mutex; FORALL_PAIR_THM; PAIR_EQ] THEN
  ARITH_TAC);;
