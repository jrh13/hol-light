(* ========================================================================= *)
(* HOL basics                                                                *)
(* ========================================================================= *)

ARITH_RULE
 `(a * x + b * y + a * y) EXP 3 + (b * x) EXP 3 +
  (a * x + b * y + b * x) EXP 3 + (a * y) EXP 3 =
  (a * x + a * y + b * x) EXP 3 + (b * y) EXP 3 +
  (a * y + b * y + b * x) EXP 3 + (a * x) EXP 3`;;

(* ========================================================================= *)
(* Propositional logic                                                       *)
(* ========================================================================= *)

TAUT
 `(~input_a ==> (internal <=> T)) /\
  (~input_b ==> (output <=> internal)) /\
  (input_a ==> (output <=> F)) /\
  (input_b ==> (output <=> F))
  ==> (output <=> ~(input_a \/ input_b))`;;

TAUT
`(i1 /\ i2 <=> a) /\
 (i1 /\ i3 <=> b) /\
 (i2 /\ i3 <=> c) /\
 (i1 /\ c <=> d) /\
 (m /\ r <=> e) /\
 (m /\ w <=> f) /\
 (n /\ w <=> g) /\
 (p /\ w <=> h) /\
 (q /\ w <=> i) /\
 (s /\ x <=> j) /\
 (t /\ x <=> k) /\
 (v /\ x <=> l) /\
 (i1 \/ i2 <=> m) /\
 (i1 \/ i3 <=> n) /\
 (i1 \/ q <=> p) /\
 (i2 \/ i3 <=> q) /\
 (i3 \/ a <=> r) /\
 (a \/ w <=> s) /\
 (b \/ w <=> t) /\
 (d \/ h <=> u) /\
 (c \/ w <=> v) /\
 (~e <=> w) /\
 (~u <=> x) /\
 (i \/ l <=> o1) /\
 (g \/ k <=> o2) /\
 (f \/ j <=> o3)
 ==> (o1 <=> ~i1) /\ (o2 <=> ~i2) /\ (o3 <=> ~i3)`;;

(* ========================================================================= *)
(* Abstractions and quantifiers                                              *)
(* ========================================================================= *)

MESON[]
 `((?x. !y. P(x) <=> P(y)) <=> ((?x. Q(x)) <=> (!y. Q(y)))) <=>
  ((?x. !y. Q(x) <=> Q(y)) <=> ((?x. P(x)) <=> (!y. P(y))))`;;

MESON[]
`(!x y z. P x y /\ P y z ==> P x z) /\
 (!x y z. Q x y /\ Q y z ==> Q x z) /\
 (!x y. P x y ==> P y x) /\
 (!x y. P x y \/ Q x y)
 ==> (!x y. P x y) \/ (!x y. Q x y)`;;

let ewd1062 = MESON[]
 `(!x. x <= x) /\
  (!x y z. x <= y /\ y <= z ==> x <= z) /\
  (!x y. f(x) <= y <=> x <= g(y))
  ==> (!x y. x <= y ==> f(x) <= f(y)) /\
      (!x y. x <= y ==> g(x) <= g(y))`;;

let ewd1062 = MESON[]
 `(!x. R x x) /\
  (!x y z. R x y /\ R y z ==> R x z) /\
  (!x y. R (f x) y <=> R x (g y))
  ==> (!x y. R x y ==> R (f x) (f y)) /\
      (!x y. R x y ==> R (g x) (g y))`;;

MESON[] `(?!x. g(f x) = x) <=> (?!y. f(g y) = y)`;;

MESON [ADD_ASSOC; ADD_SYM] `m + (n + p) = n + (m + p)`;;

(* ========================================================================= *)
(* Tactics and tacticals                                                     *)
(* ========================================================================= *)

g `2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`;;
e DISCH_TAC;;
b();;
e(CONV_TAC(REWRITE_CONV[LE_ANTISYM]));;
e(SIMP_TAC[]);;
e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e DISCH_TAC;;
e(ASM_REWRITE_TAC[]);;
e(CONV_TAC ARITH_RULE);;
let trivial = top_thm();;

g `2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`;;
e(CONV_TAC(REWRITE_CONV[LE_ANTISYM]));;
e(SIMP_TAC[]);;
e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e DISCH_TAC;;
e(ASM_REWRITE_TAC[]);;
e(CONV_TAC ARITH_RULE);;
let trivial = top_thm();;

g `2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`;;
e(CONV_TAC(REWRITE_CONV[LE_ANTISYM]) THEN
  SIMP_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_RULE);;
let trivial = top_thm();;

let trivial = prove
 (`2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`,
  CONV_TAC(REWRITE_CONV[LE_ANTISYM]) THEN
  SIMP_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_RULE);;

let trivial = prove
 (`!x y:real. &0 < x * y ==> (&0 < x <=> &0 < y)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`--x`; `y:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`x:real`; `--y`] REAL_LE_MUL) THEN REAL_ARITH_TAC);;

let trivial = prove
 (`!x y:real. &0 < x * y ==> (&0 < x <=> &0 < y)`,
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`--x`; `y:real`] REAL_LE_MUL) THEN REAL_ARITH_TAC);;

let SUM_OF_NUMBERS = prove
 (`!n. nsum(1..n) (\i. i) = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let SUM_OF_SQUARES = prove
 (`!n. nsum(1..n) (\i. i * i) = (n * (n + 1) * (2 * n + 1)) DIV 6`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let SUM_OF_CUBES = prove
 (`!n. nsum(1..n) (\i. i*i*i) = (n * n * (n + 1) * (n + 1)) DIV 4`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

(* ========================================================================= *)
(* HOL's number systems                                                      *)
(* ========================================================================= *)

REAL_ARITH `!x y:real. (abs(x) - abs(y)) <= abs(x - y)`;;

INT_ARITH
 `!a b a' b' D:int.
     (a pow 2 - D * b pow 2) * (a' pow 2 - D * b' pow 2) =
     (a * a' + D * b * b') pow 2 - D * (a * b' + a' * b) pow 2`;;

REAL_ARITH
 `!x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11:real.
        x3 = abs(x2) - x1 /\
        x4 = abs(x3) - x2 /\
        x5 = abs(x4) - x3 /\
        x6 = abs(x5) - x4 /\
        x7 = abs(x6) - x5 /\
        x8 = abs(x7) - x6 /\
        x9 = abs(x8) - x7 /\
        x10 = abs(x9) - x8 /\
        x11 = abs(x10) - x9
        ==> x1 = x10 /\ x2 = x11`;;

REAL_ARITH `!x y:real. x < y ==> x < (x + y) / &2 /\ (x + y) / &2 < y`;;

REAL_ARITH
 `((x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 2) =
  ((&1 / &6) * ((x1 + x2) pow 4 + (x1 + x3) pow 4 + (x1 + x4) pow 4 +
                (x2 + x3) pow 4 + (x2 + x4) pow 4 + (x3 + x4) pow 4) +
   (&1 / &6) * ((x1 - x2) pow 4 + (x1 - x3) pow 4 + (x1 - x4) pow 4 +
                (x2 - x3) pow 4 + (x2 - x4) pow 4 + (x3 - x4) pow 4))`;;

ARITH_RULE `x < 2 ==> 2 * x + 1 < 4`;;

(**** Fails
ARITH_RULE `~(2 * m + 1 = 2 * n)`;;
 ****)

ARITH_RULE `x < 2 EXP 30 ==> (429496730 * x) DIV (2 EXP 32) = x DIV 10`;;

(**** Fails
ARITH_RULE `x <= 2 EXP 30 ==> (429496730 * x) DIV (2 EXP 32) = x DIV 10`;;
 ****)

(**** Fails
ARITH_RULE `1 <= x /\ 1 <= y ==> 1 <= x * y`;;
 ****)

(**** Fails
REAL_ARITH `!x y:real. x = y ==> x * y = y pow 2`;;
 ****)

prioritize_real();;

REAL_RING
  `s = (a + b + c) / &2
   ==> s * (s - b) * (s - c) + s * (s - c) * (s - a) +
       s * (s - a) * (s - b) - (s - a) * (s - b) * (s - c) =
       a * b * c`;;

REAL_RING `a pow 2 = &2 /\ x pow 2 + a * x + &1 = &0 ==> x pow 4 + &1 = &0`;;

REAL_RING
 `(a * x pow 2 + b * x + c = &0) /\
  (a * y pow 2 + b * y + c = &0) /\
  ~(x = y)
  ==> (a * x * y = c) /\ (a * (x + y) + b = &0)`;;

REAL_RING
 `p = (&3 * a1 - a2 pow 2) / &3 /\
  q = (&9 * a1 * a2 - &27 * a0 - &2 * a2 pow 3) / &27 /\
  x = z + a2 / &3 /\
  x * w = w pow 2 - p / &3
  ==> (z pow 3 + a2 * z pow 2 + a1 * z + a0 = &0 <=>
       if p = &0 then x pow 3 = q
       else (w pow 3) pow 2 - q * (w pow 3) - p pow 3 / &27 = &0)`;;

REAL_FIELD `&0 < x ==> &1 / x - &1 / (&1 + x) = &1 / (x * (&1 + x))`;;

REAL_FIELD
`s pow 2 = b pow 2 - &4 * a * c
 ==> (a * x pow 2 + b * x + c = &0 <=>
      if a = &0 then
         if b = &0 then
            if c = &0 then T else F
         else x = --c / b
      else x = (--b + s) / (&2 * a) \/ x = (--b + --s) / (&2 * a))`;;

(**** This needs an external SDP solver to assist with proof

needs "Examples/sos.ml";;

SOS_RULE `1 <= x /\ 1 <= y ==> 1 <= x * y`;;

REAL_SOS
 `!a1 a2 a3 a4:real.
      &0 <= a1 /\ &0 <= a2 /\ &0 <= a3 /\ &0 <= a4
      ==> a1 pow 2 +
          ((a1 + a2) / &2) pow 2 +
          ((a1 + a2 + a3) / &3) pow 2 +
          ((a1 + a2 + a3 + a4) / &4) pow 2
         <= &4 * (a1 pow 2 + a2 pow 2 + a3 pow 2 + a4 pow 2)`;;

REAL_SOS
 `!a b c:real.
      a >= &0 /\ b >= &0 /\ c >= &0
      ==> &3 / &2 * (b + c) * (a + c) * (a + b) <=
          a * (a + c) * (a + b) +
          b * (b + c) * (a + b) +
          c * (b + c) * (a + c)`;;

SOS_CONV `&2 * x pow 4 + &2 * x pow 3 * y - x pow 2 * y pow 2 + &5 * y pow 4`;;

PURE_SOS
`x pow 4 + &2 * x pow 2 * z + x pow 2 - &2 * x * y * z +
          &2 * y pow 2 * z pow 2 + &2 * y * z pow 2 + &2 * z pow 2 - &2 * x +
          &2 *  y * z + &1 >= &0`;;

*****)

needs "Examples/cooper.ml";;

COOPER_RULE `ODD n ==> 2 * n DIV 2 < n`;;

COOPER_RULE `!n. n >= 8 ==> ?a b. n = 3 * a + 5 * b`;;

needs "Rqe/make.ml";;

REAL_QELIM_CONV `!x. &0 <= x ==> ?y. y pow 2 = x`;;

(* ========================================================================= *)
(* Inductive definitions                                                     *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(* Wellfounded induction                                                     *)
(* ========================================================================= *)

let NSQRT_2 = prove
 (`!p q. p * p = 2 * q * q ==> q = 0`,
  MATCH_MP_TAC num_WF THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_MULT; ARITH] THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `m:num`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE
   `q < 2 * m ==> q * q = 2 * m * m ==> m = 0 <=>
    (2 * m) * 2 * m = 2 * q * q ==> 2 * m <= q`] THEN
  ASM_MESON_TAC[LE_MULT2; MULT_EQ_0; ARITH_RULE `2 * x <= x <=> x = 0`]);;

(* ========================================================================= *)
(* Changing proof style                                                      *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(* Recursive definitions                                                     *)
(* ========================================================================= *)

let fib = define
 `fib n = if n = 0 \/ n = 1 then 1 else fib(n - 1) + fib(n - 2)`;;

let fib2 = define
 `(fib2 0 = 1) /\
  (fib2 1 = 1) /\
  (fib2 (n + 2) = fib2(n) + fib2(n + 1))`;;

let halve = define `halve (2 * n) = n`;;

let unknown = define `unknown n = unknown(n + 1)`;;

define
 `!n. collatz(n) = if n <= 1 then n
                   else if EVEN(n) then collatz(n DIV 2)
                   else collatz(3 * n + 1)`;;

let fusc_def = define
 `(fusc (2 * n) = if n = 0 then 0 else fusc(n)) /\
  (fusc (2 * n + 1) = if n = 0 then 1 else fusc(n) + fusc(n + 1))`;;

let fusc = prove
 (`fusc 0 = 0 /\
   fusc 1 = 1 /\
   fusc (2 * n) = fusc(n) /\
   fusc (2 * n + 1) = fusc(n) + fusc(n + 1)`,
  REWRITE_TAC[fusc_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(INST [`0`,`n:num`] fusc_def) THEN ARITH_TAC);;

let binom = define
 `(!n. binom(n,0) = 1) /\
  (!k. binom(0,SUC(k)) = 0) /\
  (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_LT = prove
 (`!n k. n < k ==> (binom(n,k) = 0)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC[binom; ARITH; LT_SUC; LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < k ==> n < SUC(k)`; ARITH]);;

let BINOM_REFL = prove
 (`!n. binom(n,n) = 1`,
  INDUCT_TAC THEN ASM_SIMP_TAC[binom; BINOM_LT; LT; ARITH]);;

let BINOM_FACT = prove
 (`!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES; binom] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; FACT; binom] THEN CONV_TAC NUM_RING);;

let BINOMIAL_THEOREM = prove
 (`!n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP] THEN
  REWRITE_TAC[NSUM_SING_NUMSEG; binom; SUB_REFL; EXP; MULT_CLAUSES] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; ADD1; ARITH_RULE `0 <= n + 1`; NSUM_OFFSET] THEN
  ASM_REWRITE_TAC[EXP; binom; GSYM ADD1; GSYM NSUM_LMUL] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; NSUM_ADD_NUMSEG; MULT_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC(ARITH_RULE `a = e /\ b = c + d ==> a + b = c + d + e`) THEN
  CONJ_TAC THENL [REWRITE_TAC[MULT_AC; SUB_SUC]; REWRITE_TAC[GSYM EXP]] THEN
  SIMP_TAC[ADD1; SYM(REWRITE_CONV[NSUM_OFFSET]`nsum(m+1..n+1) (\i. f i)`)] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; GSYM ADD1; LE_SUC; LE_0] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0] THEN
  SIMP_TAC[BINOM_LT; LT; MULT_CLAUSES; ADD_CLAUSES; SUB_0; EXP; binom] THEN
  SIMP_TAC[ARITH; ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; EXP] THEN
  REWRITE_TAC[MULT_AC]);;

(* ========================================================================= *)
(* Sets and functions                                                        *)
(* ========================================================================= *)

let SURJECTIVE_IFF_RIGHT_INVERSE = prove
 (`(!y. ?x. g x = y) <=> (?f. g o f = I)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; I_DEF] THEN MESON_TAC[]);;

let INJECTIVE_IFF_LEFT_INVERSE = prove
 (`(!x y. f x = f y ==> x = y) <=> (?g. g o f = I)`,
  let lemma = MESON[]
   `(!x x'. f x = f x' ==> x = x') <=> (!y:B. ?u:A. !x. f x = y ==> u = x)` in
  REWRITE_TAC[lemma; FUN_EQ_THM; o_DEF; I_DEF] THEN MESON_TAC[]);;

let cantor = new_definition
 `cantor(x,y) = ((x + y) EXP 2 + 3 * x + y) DIV 2`;;

(**** Needs external SDP solver

needs "Examples/sos.ml";;

let CANTOR_LEMMA = prove
 (`cantor(x,y) = cantor(x',y') ==> x + y = x' + y'`,
  REWRITE_TAC[cantor] THEN CONV_TAC SOS_RULE);;

****)

let CANTOR_LEMMA_LEMMA = prove
 (`x + y < x' + y' ==> cantor(x,y) < cantor(x',y')`,
  REWRITE_TAC[ARITH_RULE `x + y < z <=> x + y + 1 <= z`] THEN DISCH_TAC THEN
  REWRITE_TAC[cantor; ARITH_RULE `3 * x + y = (x + y) + 2 * x`] THEN
  MATCH_MP_TAC(ARITH_RULE `x + 2 <= y ==> x DIV 2 < y DIV 2`) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(x + y + 1) EXP 2 + (x + y + 1)` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a:num <= b /\ c <= d ==> a + c <= b + d + e`) THEN
  ASM_SIMP_TAC[EXP_2; LE_MULT2]);;

let CANTOR_LEMMA = prove
 (`cantor(x,y) = cantor(x',y') ==> x + y = x' + y'`,
  MESON_TAC[LT_CASES; LT_REFL; CANTOR_LEMMA_LEMMA]);;

let CANTOR_INJ = prove
 (`!w z. cantor w = cantor z ==> w = z`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC(MATCH_MP CANTOR_LEMMA th)) THEN
  ASM_REWRITE_TAC[cantor; ARITH_RULE `3 * x + y = (x + y) + 2 * x`] THEN
  REWRITE_TAC[ARITH_RULE `(a + b + 2 * x) DIV 2 = (a + b) DIV 2 + x`] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let CANTOR_THM = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  REWRITE_TAC[INJECTIVE_IFF_LEFT_INVERSE; FUN_EQ_THM; I_DEF; o_DEF] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* Inductive datatypes                                                       *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(* Semantics of programming languages                                        *)
(* ========================================================================= *)

let string_INDUCT,string_RECURSION =
  define_type "string = String (int list)";;

let expression_INDUCT,expression_RECURSION = define_type
"expression = Literal num
            | Variable string
            | Plus expression expression
            | Times expression expression";;

let command_INDUCT,command_RECURSION = define_type
  "command = Assign string expression
           | Sequence command command
           | If expression command command
           | While expression command";;

parse_as_infix(";;",(18,"right"));;
parse_as_infix(":=",(20,"right"));;
override_interface(";;",`Sequence`);;
override_interface(":=",`Assign`);;
overload_interface("+",`Plus`);;
overload_interface("*",`Times`);;

let value = define
 `(value (Literal n) s = n) /\
  (value (Variable x) s = s(x)) /\
  (value (e1 + e2) s = value e1 s + value e2 s) /\
  (value (e1 * e2) s = value e1 s * value e2 s)`;;

let sem_RULES,sem_INDUCT,sem_CASES = new_inductive_definition
  `(!x e s s'. s'(x) = value e s /\ (!y. ~(y = x) ==> s'(y) = s(y))
               ==> sem (x := e) s s') /\
   (!c1 c2 s s' s''. sem(c1) s s' /\ sem(c2) s' s'' ==> sem(c1 ;; c2) s s'') /\
   (!e c1 c2 s s'. ~(value e s = 0) /\ sem(c1) s s' ==> sem(If e c1 c2) s s') /\
   (!e c1 c2 s s'. value e s = 0 /\ sem(c2) s s' ==> sem(If e c1 c2) s s') /\
   (!e c s. value e s = 0 ==> sem(While e c) s s) /\
   (!e c s s' s''. ~(value e s = 0) /\ sem(c) s s' /\ sem(While e c) s' s''
                   ==> sem(While e c) s s'')`;;

(**** Fails
  define
   `sem(While e c) s s' <=> if value e s = 0 then (s' = s)
                            else ?s''. sem c s s'' /\ sem(While e c) s'' s'`;;
****)

let DETERMINISM = prove
 (`!c s s' s''. sem c s s' /\ sem c s s'' ==> (s' = s'')`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC sem_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[sem_CASES] THEN
  REWRITE_TAC[distinctness "command"; injectivity "command"] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

let wlp = new_definition
 `wlp c q s <=> !s'. sem c s s' ==> q s'`;;

let terminates = new_definition
 `terminates c s <=> ?s'. sem c s s'`;;

let wp = new_definition
 `wp c q s <=> terminates c s /\ wlp c q s`;;

let WP_TOTAL = prove
 (`!c. (wp c EMPTY = EMPTY)`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; EMPTY] THEN MESON_TAC[]);;

let WP_MONOTONIC = prove
 (`q SUBSET r ==> wp c q SUBSET wp c r`,
  REWRITE_TAC[SUBSET; IN; wp; wlp; terminates] THEN MESON_TAC[]);;

let WP_DISJUNCTIVE = prove
 (`(wp c p) UNION (wp c q) = wp c (p UNION q)`,
  REWRITE_TAC[FUN_EQ_THM; IN; wp; wlp; IN_ELIM_THM; UNION; terminates] THEN
  MESON_TAC[DETERMINISM]);;

let WP_SEQ = prove
 (`!c1 c2 q. wp (c1 ;; c2) = wp c1 o wp c2`,
  REWRITE_TAC[wp; wlp; terminates; FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sem_CASES] THEN
  REWRITE_TAC[injectivity "command"; distinctness "command"] THEN
  MESON_TAC[DETERMINISM]);;

let correct = new_definition
 `correct p c q <=> p SUBSET (wp c q)`;;

let CORRECT_PRESTRENGTH = prove
 (`!p p' c q. p SUBSET p' /\ correct p' c q ==> correct p c q`,
  REWRITE_TAC[correct; SUBSET_TRANS]);;

let CORRECT_POSTWEAK = prove
 (`!p c q q'. correct p c q' /\ q' SUBSET q ==> correct p c q`,
  REWRITE_TAC[correct] THEN MESON_TAC[WP_MONOTONIC; SUBSET_TRANS]);;

let CORRECT_SEQ = prove
 (`!p q r c1 c2.
        correct p c1 r /\ correct r c2 q ==> correct p (c1 ;; c2) q`,
  REWRITE_TAC[correct; WP_SEQ; o_THM] THEN
  MESON_TAC[WP_MONOTONIC; SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Need a fresh HOL session here; now doing shallow embedding.               *)
(* ------------------------------------------------------------------------- *)

let assign = new_definition
  `Assign (f:S->S) (q:S->bool) = q o f`;;

parse_as_infix(";;",(18,"right"));;

let sequence = new_definition
 `(c1:(S->bool)->(S->bool)) ;; (c2:(S->bool)->(S->bool)) = c1 o c2`;;

let if_def = new_definition
 `If e (c:(S->bool)->(S->bool)) q = {s | if e s then c q s else q s}`;;

let ite_def = new_definition
 `Ite e (c1:(S->bool)->(S->bool)) c2 q =
    {s | if e s then c1 q s else c2 q s}`;;

let while_RULES,while_INDUCT,while_CASES = new_inductive_definition
         `!q s. If e (c ;; while e c) q s ==> while e c q s`;;

let while_def = new_definition
 `While e c q =
    {s | !w. (!s:S. (if e(s) then c w s else q s) ==> w s) ==> w s}`;;

let monotonic = new_definition
 `monotonic c <=> !q q'. q SUBSET q' ==> (c q) SUBSET (c q')`;;

let MONOTONIC_ASSIGN = prove
 (`monotonic (Assign f)`,
  SIMP_TAC[monotonic; assign; SUBSET; o_THM; IN]);;

let MONOTONIC_IF = prove
 (`monotonic c ==> monotonic (If e c)`,
  REWRITE_TAC[monotonic; if_def] THEN SET_TAC[]);;

let MONOTONIC_ITE = prove
 (`monotonic c1 /\ monotonic c2 ==> monotonic (Ite e c1 c2)`,
  REWRITE_TAC[monotonic; ite_def] THEN SET_TAC[]);;

let MONOTONIC_SEQ = prove
 (`monotonic c1 /\ monotonic c2 ==> monotonic (c1 ;; c2)`,
  REWRITE_TAC[monotonic; sequence; o_THM] THEN SET_TAC[]);;

let MONOTONIC_WHILE = prove
 (`monotonic c ==> monotonic(While e c)`,
  REWRITE_TAC[monotonic; while_def] THEN SET_TAC[]);;

let WHILE_THM = prove
 (`!e c q:S->bool.
    monotonic c
    ==> (!s. If e (c ;; While e c) q s ==> While e c q s) /\
        (!w'. (!s. If e (c ;; (\q. w')) q s ==> w' s)
              ==> (!a. While e c q a ==> w' a)) /\
        (!s. While e c q s <=> If e (c ;; While e c) q s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (MP_TAC o GEN_ALL o DISCH_ALL o derive_nonschematic_inductive_relations)
   `!s:S. (if e s then c w s else q s) ==> w s` THEN
  REWRITE_TAC[if_def; sequence; o_THM; IN_ELIM_THM; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; while_def; IN_ELIM_THM] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[monotonic] THEN SET_TAC[]);;

let WHILE_FIX = prove
 (`!e c. monotonic c ==> (While e c = If e (c ;; While e c))`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WHILE_THM]);;

let correct = new_definition
 `correct p c q <=> p SUBSET (c q)`;;

let CORRECT_PRESTRENGTH = prove
 (`!p p' c q. p SUBSET p' /\ correct p' c q ==> correct p c q`,
  REWRITE_TAC[correct; SUBSET_TRANS]);;

let CORRECT_POSTWEAK = prove
 (`!p c q q'. monotonic c /\ correct p c q' /\ q' SUBSET q ==> correct p c q`,
  REWRITE_TAC[correct; monotonic] THEN SET_TAC[]);;

let CORRECT_ASSIGN = prove
 (`!p f q. (p SUBSET (q o f)) ==> correct p (Assign f) q`,
  REWRITE_TAC[correct; assign]);;

let CORRECT_SEQ = prove
 (`!p q r c1 c2.
        monotonic c1 /\ correct p c1 r /\ correct r c2 q
        ==> correct p (c1 ;; c2) q`,
  REWRITE_TAC[correct; sequence; monotonic; o_THM] THEN SET_TAC[]);;

let CORRECT_ITE = prove
 (`!p e c1 c2 q.
       correct (p INTER e) c1 q /\ correct (p INTER (UNIV DIFF e)) c2 q
       ==> correct p (Ite e c1 c2) q`,
  REWRITE_TAC[correct; ite_def] THEN SET_TAC[]);;

let CORRECT_IF = prove
 (`!p e c q.
       correct (p INTER e) c q /\ p INTER (UNIV DIFF e) SUBSET q
       ==> correct p (If e c) q`,
  REWRITE_TAC[correct; if_def] THEN SET_TAC[]);;

let CORRECT_WHILE = prove
 (`!(<<) p c q e invariant.
      monotonic c /\
      WF(<<) /\
      p SUBSET invariant /\
      (UNIV DIFF e) INTER invariant SUBSET q /\
      (!X:S. correct (invariant INTER e INTER (\s. X = s)) c
                     (invariant INTER (\s. s << X)))
      ==> correct p (While e c) q`,
  REWRITE_TAC[correct; SUBSET; IN_INTER; IN_UNIV; IN_DIFF; IN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:S. invariant s ==> While e c q s` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[WF_IND]) THEN
  X_GEN_TAC `s:S` THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WHILE_FIX th]) THEN
  REWRITE_TAC[if_def; sequence; o_THM; IN_ELIM_THM] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:S`; `s:S`]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [monotonic]) THEN
  REWRITE_TAC[SUBSET; IN; RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[INTER; IN_ELIM_THM; IN]);;

let assert_def = new_definition
 `assert (p:S->bool) (q:S->bool) = q`;;

let variant_def = new_definition
 `variant ((<<):S->S->bool) (q:S->bool) = q`;;

let CORRECT_SEQ_VC = prove
 (`!p q r c1 c2.
        monotonic c1 /\ correct p c1 r /\ correct r c2 q
        ==> correct p (c1 ;; assert r ;; c2) q`,
  REWRITE_TAC[correct; sequence; monotonic; assert_def; o_THM] THEN SET_TAC[]);;

let CORRECT_WHILE_VC = prove
 (`!(<<) p c q e invariant.
      monotonic c /\
      WF(<<) /\
      p SUBSET invariant /\
      (UNIV DIFF e) INTER invariant SUBSET q /\
      (!X:S. correct (invariant INTER e INTER (\s. X = s)) c
                     (invariant INTER (\s. s << X)))
      ==> correct p (While e (assert invariant ;; variant(<<) ;; c)) q`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sequence; variant_def; assert_def; o_DEF; ETA_AX] THEN
  ASM_MESON_TAC[CORRECT_WHILE]);;

let MONOTONIC_ASSERT = prove
 (`monotonic (assert p)`,
  REWRITE_TAC[assert_def; monotonic]);;

let MONOTONIC_VARIANT = prove
 (`monotonic (variant p)`,
  REWRITE_TAC[variant_def; monotonic]);;

let MONO_TAC =
  REPEAT(MATCH_MP_TAC MONOTONIC_WHILE ORELSE
         (MAP_FIRST MATCH_MP_TAC
           [MONOTONIC_SEQ; MONOTONIC_IF; MONOTONIC_ITE] THEN CONJ_TAC)) THEN
  MAP_FIRST MATCH_ACCEPT_TAC
   [MONOTONIC_ASSIGN; MONOTONIC_ASSERT; MONOTONIC_VARIANT];;

let VC_TAC =
  FIRST
   [MATCH_MP_TAC CORRECT_SEQ_VC THEN CONJ_TAC THENL [MONO_TAC; CONJ_TAC];
    MATCH_MP_TAC CORRECT_ITE THEN CONJ_TAC;
    MATCH_MP_TAC CORRECT_IF THEN CONJ_TAC;
    MATCH_MP_TAC CORRECT_WHILE_VC THEN REPEAT CONJ_TAC THENL
     [MONO_TAC; TRY(MATCH_ACCEPT_TAC WF_MEASURE); ALL_TAC; ALL_TAC;
      REWRITE_TAC[FORALL_PAIR_THM; MEASURE] THEN REPEAT GEN_TAC];
    MATCH_MP_TAC CORRECT_ASSIGN];;

needs "Library/prime.ml";;

(* ------------------------------------------------------------------------- *)
(* x = m, y = n;                                                             *)
(* while (!(x == 0 || y == 0))                                               *)
(*  { if (x < y) y = y - x;                                                  *)
(*    else x = x - y;                                                        *)
(*  }                                                                        *)
(* if (x == 0) x = y;                                                        *)
(* ------------------------------------------------------------------------- *)

g `correct
    (\(m,n,x,y). T)
    (Assign (\(m,n,x,y). m,n,m,n) ;;         // x,y := m,n
     assert (\(m,n,x,y). x = m /\ y = n) ;;
     While (\(m,n,x,y). ~(x = 0 \/ y = 0))
      (assert (\(m,n,x,y). gcd(x,y) = gcd(m,n)) ;;
       variant(MEASURE(\(m,n,x,y). x + y)) ;;
       Ite (\(m,n,x,y). x < y)
           (Assign (\(m,n,x,y). m,n,x,y - x))
           (Assign (\(m,n,x,y). m,n,x - y,y))) ;;
     assert (\(m,n,x,y). (x = 0 \/ y = 0) /\ gcd(x,y) = gcd(m,n)) ;;
     If (\(m,n,x,y). x = 0) (Assign (\(m,n,x,y). (m,n,y,y))))
  (\(m,n,x,y). gcd(m,n) = x)`;;

e(REPEAT VC_TAC);;

b();;
e(REPEAT VC_TAC THEN REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:num`; `y:num`] THEN
  REWRITE_TAC[IN; INTER; UNIV; DIFF; o_DEF; IN_ELIM_THM; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[]);;

e(SIMP_TAC[GCD_SUB; LT_IMP_LE]);;
e ARITH_TAC;;

e(SIMP_TAC[GCD_SUB; NOT_LT] THEN ARITH_TAC);;

e(MESON_TAC[GCD_0]);;

e(MESON_TAC[GCD_0; GCD_SYM]);;

parse_as_infix("refines",(12,"right"));;

let refines = new_definition
 `c2 refines c1 <=> !q. c1(q) SUBSET c2(q)`;;

let REFINES_REFL = prove
 (`!c. c refines c`,
  REWRITE_TAC[refines; SUBSET_REFL]);;

let REFINES_TRANS = prove
 (`!c1 c2 c3. c3 refines c2 /\ c2 refines c1 ==> c3 refines c1`,
  REWRITE_TAC[refines] THEN MESON_TAC[SUBSET_TRANS]);;

let REFINES_CORRECT = prove
 (`correct p c1 q /\ c2 refines c1 ==> correct p c2 q`,
  REWRITE_TAC[correct; refines] THEN MESON_TAC[SUBSET_TRANS]);;

let REFINES_WHILE = prove
 (`c' refines c ==> While e c' refines While e c`,
  REWRITE_TAC[refines; while_def; SUBSET; IN_ELIM_THM; IN] THEN MESON_TAC[]);;

let specification = new_definition
 `specification(p,q) r = if q SUBSET r then p else {}`;;

let REFINES_SPECIFICATION = prove
 (`c refines specification(p,q) ==> correct p c q`,
  REWRITE_TAC[specification; correct; refines] THEN
  MESON_TAC[SUBSET_REFL; SUBSET_EMPTY]);;

(* ========================================================================= *)
(* Number theory                                                             *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;
needs "Library/binomial.ml";;

prioritize_num();;

let FERMAT_PRIME_CONV n =
  let tm = subst [mk_small_numeral n,`x:num`] `prime(2 EXP (2 EXP x) + 1)` in
  (RAND_CONV NUM_REDUCE_CONV THENC PRIME_CONV) tm;;

FERMAT_PRIME_CONV 0;;
FERMAT_PRIME_CONV 1;;
FERMAT_PRIME_CONV 2;;
FERMAT_PRIME_CONV 3;;
FERMAT_PRIME_CONV 4;;
FERMAT_PRIME_CONV 5;;
FERMAT_PRIME_CONV 6;;
FERMAT_PRIME_CONV 7;;
FERMAT_PRIME_CONV 8;;

let CONG_TRIVIAL = prove
 (`!x y. n divides x /\ n divides y ==> (x == y) (mod n)`,
  MESON_TAC[CONG_0; CONG_SYM; CONG_TRANS]);;

let LITTLE_CHECK_CONV tm =
  EQT_ELIM((RATOR_CONV(LAND_CONV NUM_EXP_CONV) THENC CONG_CONV) tm);;

LITTLE_CHECK_CONV `(9 EXP 8 == 9) (mod 3)`;;
LITTLE_CHECK_CONV `(9 EXP 3 == 9) (mod 3)`;;
LITTLE_CHECK_CONV `(10 EXP 7 == 10) (mod 7)`;;
LITTLE_CHECK_CONV `(2 EXP 7 == 2) (mod 7)`;;
LITTLE_CHECK_CONV `(777 EXP 13 == 777) (mod 13)`;;

let DIVIDES_FACT_PRIME = prove
 (`!p. prime p ==> !n. p divides (FACT n) <=> p <= n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[FACT; LE] THENL
   [ASM_MESON_TAC[DIVIDES_ONE; PRIME_0; PRIME_1];
    ASM_MESON_TAC[PRIME_DIVPROD_EQ; DIVIDES_LE; NOT_SUC; DIVIDES_REFL;
                  ARITH_RULE `~(p <= n) /\ p <= SUC n ==> p = SUC n`]]);;

let DIVIDES_BINOM_PRIME = prove
 (`!n p. prime p /\ 0 < n /\ n < p ==> p divides binom(p,n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(AP_TERM `(divides) p` (SPECL [`p - n`; `n:num`] BINOM_FACT)) THEN
  ASM_SIMP_TAC[DIVIDES_FACT_PRIME; PRIME_DIVPROD_EQ; SUB_ADD; LT_IMP_LE] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT; LT_REFL] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n /\ n < p ==> p - n < p`]);;

let DIVIDES_NSUM = prove
 (`!m n. (!i. m <= i /\ i <= n ==> p divides f(i)) ==> p divides nsum(m..n) f`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN
  ASM_MESON_TAC[LE; LE_TRANS; DIVIDES_0; DIVIDES_ADD; LE_REFL]);;

let FLT_LEMMA = prove
 (`!p a b. prime p ==> ((a + b) EXP p == a EXP p + b EXP p) (mod p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BINOMIAL_THEOREM] THEN
  SUBGOAL_THEN `1 <= p /\ 0 < p` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0; ARITH; NSUM_CLAUSES_RIGHT] THEN
  REWRITE_TAC[SUB_0; SUB_REFL; EXP; binom; BINOM_REFL; MULT_CLAUSES] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a + b = (b + 0) + a`] THEN
  REPEAT(MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL]) THEN
  REWRITE_TAC[CONG_0] THEN MATCH_MP_TAC DIVIDES_NSUM THEN
  ASM_MESON_TAC[DIVIDES_RMUL; DIVIDES_BINOM_PRIME; ARITH_RULE
   `0 < p /\ 1 <= i /\ i <= p - 1 ==> 0 < i /\ i < p`]);;

let FERMAT_LITTLE = prove
 (`!p a. prime p ==> (a EXP p == a) (mod p)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [ASM_MESON_TAC[EXP_EQ_0; CONG_REFL; PRIME_0];
    ASM_MESON_TAC[ADD1; FLT_LEMMA; EXP_ONE; CONG_ADD; CONG_TRANS; CONG_REFL]]);;

let FERMAT_LITTLE_COPRIME = prove
 (`!p a. prime p /\ coprime(a,p) ==> (a EXP (p - 1) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
  EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ; ARITH_RULE `~(p = 0) ==> SUC(p - 1) = p`] THEN
  ASM_SIMP_TAC[FERMAT_LITTLE; MULT_CLAUSES]);;

let FERMAT_LITTLE_VARIANT = prove
 (`!p a. prime p ==> (a EXP (1 + m * (p - 1)) == a) (mod p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o SPEC `a:num` o MATCH_MP PRIME_COPRIME_STRONG)
  THENL [ASM_MESON_TAC[CONG_TRIVIAL; ADD_AC; ADD1; DIVIDES_REXP_SUC];
         ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = a * 1`] THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN MATCH_MP_TAC CONG_MULT THEN
  REWRITE_TAC[GSYM EXP_EXP; CONG_REFL] THEN
  ASM_MESON_TAC[COPRIME_SYM; COPRIME_EXP; PHI_PRIME; FERMAT_LITTLE_COPRIME]);;

let RSA = prove
 (`prime p /\ prime q /\ ~(p = q) /\
   (d * e == 1) (mod ((p - 1) * (q - 1))) /\
   plaintext < p * q /\ (ciphertext = (plaintext EXP e) MOD (p * q))
   ==> (plaintext = (ciphertext EXP d) MOD (p * q))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_EXP_MOD; MULT_EQ_0; PRIME_IMP_NZ; EXP_EXP] THEN
  SUBGOAL_THEN `(plaintext == plaintext EXP (e * d)) (mod (p * q))` MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[CONG; MULT_EQ_0; PRIME_IMP_NZ; MOD_LT]] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [CONG_TO_1]) THENL
   [ASM_MESON_TAC[MULT_EQ_1; ARITH_RULE `p - 1 = 1 <=> p = 2`]; ALL_TAC] THEN
  MATCH_MP_TAC CONG_CHINESE THEN ASM_SIMP_TAC[DISTINCT_PRIME_COPRIME] THEN
  ASM_MESON_TAC[FERMAT_LITTLE_VARIANT; MULT_AC; CONG_SYM]);;

(* ========================================================================= *)
(* Real analysis                                                             *)
(* ========================================================================= *)

needs "Library/analysis.ml";;
needs "Library/transc.ml";;

let cheb = define
 `(!x. cheb 0 x = &1) /\
  (!x. cheb 1 x = x) /\
  (!n x. cheb (n + 2) x = &2 * x * cheb (n + 1) x - cheb n x)`;;

let CHEB_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;

let CHEB_COS = prove
 (`!n x. cheb n (cos x) = cos(&n * x)`,
  MATCH_MP_TAC CHEB_INDUCT THEN
  REWRITE_TAC[cheb; REAL_MUL_LZERO; REAL_MUL_LID; COS_0] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_MUL_LID; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[COS_ADD; COS_DOUBLE; SIN_DOUBLE] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let CHEB_RIPPLE = prove
 (`!x. abs(x) <= &1 ==> abs(cheb n x) <= &1`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
  MESON_TAC[CHEB_COS; ACS_COS; COS_BOUNDS]);;

let NUM_ADD2_CONV =
  let add_tm = `(+):num->num->num`
  and two_tm = `2` in
  fun tm ->
    let m = mk_numeral(dest_numeral tm -/ Int 2) in
    let tm' = mk_comb(mk_comb(add_tm,m),two_tm) in
    SYM(NUM_ADD_CONV tm');;

let CHEB_CONV =
  let [pth0;pth1;pth2] = CONJUNCTS cheb in
  let rec conv tm =
   (GEN_REWRITE_CONV I [pth0; pth1] ORELSEC
    (LAND_CONV NUM_ADD2_CONV THENC
     GEN_REWRITE_CONV I [pth2] THENC
     COMB2_CONV
      (funpow 3 RAND_CONV ((LAND_CONV NUM_ADD_CONV) THENC conv))
      conv THENC
     REAL_POLY_CONV)) tm in
  conv;;

CHEB_CONV `cheb 8 x`;;

let CHEB_2N1 = prove
 (`!n x. ((x - &1) * (cheb (2 * n + 1) x - &1) =
          (cheb (n + 1) x - cheb n x) pow 2) /\
         (&2 * (x pow 2 - &1) * (cheb (2 * n + 2) x - &1) =
          (cheb (n + 2) x - cheb n x) pow 2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC CHEB_INDUCT THEN REWRITE_TAC[ARITH; cheb; CHEB_2; CHEB_3] THEN
  REPEAT(CHANGED_TAC
   (REWRITE_TAC[GSYM ADD_ASSOC; LEFT_ADD_DISTRIB; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `n + 5 = (n + 3) + 2`;
                ARITH_RULE `n + 4 = (n + 2) + 2`;
                ARITH_RULE `n + 3 = (n + 1) + 2`;

                cheb])) THEN
  CONV_TAC REAL_RING);;

let IVT_LEMMA1 = prove
 (`!f. (!x. f contl x)
       ==> !x y. f(x) <= &0 /\ &0 <= f(y) ==> ?x. f(x) = &0`,
  ASM_MESON_TAC[IVT; IVT2; REAL_LE_TOTAL]);;

let IVT_LEMMA2 = prove
 (`!f. (!x. f contl x) /\ (?x. f(x) <= x) /\ (?y. y <= f(y)) ==> ?x. f(x) = x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `\x. f x - x` IVT_LEMMA1) THEN
  ASM_SIMP_TAC[CONT_SUB; CONT_X] THEN
  SIMP_TAC[REAL_LE_SUB_LADD; REAL_LE_SUB_RADD; REAL_SUB_0; REAL_ADD_LID] THEN
  ASM_MESON_TAC[]);;

let SARKOVSKII_TRIVIAL = prove
 (`!f:real->real. (!x. f contl x) /\ (?x. f(f(f(x))) = x) ==> ?x. f(x) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_LEMMA2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC
   (MESON[] `P x \/ P (f x) \/ P (f(f x)) ==> ?x:real. P x`) THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Embedding of logics                                                       *)
(* ========================================================================= *)

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

(* ------------------------------------------------------------------------- *)
(* Need a fresh HOL session here: doing shallow embedding.                   *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "Not";;
parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(15,"right"));;
parse_as_infix("-->",(14,"right"));;
parse_as_infix("<->",(13,"right"));;

let false_def = define `False = \t:num. F`;;
let true_def = define `True = \t:num. T`;;
let not_def = define `Not p = \t:num. ~(p t)`;;
let and_def = define `p && q = \t:num. p t /\ q t`;;
let or_def = define `p || q = \t:num. p t \/ q t`;;
let imp_def = define `p --> q = \t:num. p t ==> q t`;;
let iff_def = define `p <-> q = \t:num. p t <=> q t`;;

let forever = define `forever p = \t:num. !t'. t <= t' ==> p t'`;;
let sometime = define `sometime p = \t:num. ?t'. t <= t' /\ p t'`;;

let next = define `next p = \t:num. p(t + 1)`;;

parse_as_infix("until",(17,"right"));;

let until = define
  `p until q =
    \t:num. ?t'. t <= t' /\ (!t''. t <= t'' /\ t'' < t' ==> p t'') /\ q t'`;;

(* ========================================================================= *)
(* HOL as a functional programming language                                  *)
(* ========================================================================= *)

type ite = False | True | Atomic of int | Ite of ite*ite*ite;;

let rec norm e =
  match e with
    Ite(False,y,z) -> norm z
  | Ite(True,y,z) -> norm y
  | Ite(Atomic i,y,z) -> Ite(Atomic i,norm y,norm z)
  | Ite(Ite(u,v,w),y,z) -> norm(Ite(u,Ite(v,y,z),Ite(w,y,z)))
  | _ -> e;;

let ite_INDUCT,ite_RECURSION = define_type
 "ite = False | True | Atomic num | Ite ite ite ite";;

let eth = prove_general_recursive_function_exists
 `?norm. (norm False = False) /\
         (norm True = True) /\
         (!i. norm (Atomic i) = Atomic i) /\
         (!y z. norm (Ite False y z) = norm z) /\
         (!y z. norm (Ite True y z) = norm y) /\
         (!i y z. norm (Ite (Atomic i) y z) =
                    Ite (Atomic i) (norm y) (norm z)) /\
         (!u v w y z. norm (Ite (Ite u v w) y z) =
                        norm (Ite u (Ite v y z) (Ite w y z)))`;;

let sizeof = define
 `(sizeof False = 1) /\
  (sizeof True = 1) /\
  (sizeof(Atomic i) = 1) /\
  (sizeof(Ite x y z) = sizeof x * (1 + sizeof y + sizeof z))`;;

let eth' =
  let th = prove
   (hd(hyp eth),
    EXISTS_TAC `MEASURE sizeof` THEN
    REWRITE_TAC[WF_MEASURE; MEASURE_LE; MEASURE; sizeof] THEN ARITH_TAC) in
  PROVE_HYP th eth;;

let norm = new_specification ["norm"] eth';;

let SIZEOF_INDUCT = REWRITE_RULE[WF_IND; MEASURE]  (ISPEC`sizeof` WF_MEASURE);;

let SIZEOF_NZ = prove
 (`!e. ~(sizeof e = 0)`,
  MATCH_MP_TAC ite_INDUCT THEN SIMP_TAC[sizeof; ADD_EQ_0; MULT_EQ_0; ARITH]);;

let ITE_INDUCT = prove
 (`!P. P False /\
       P True /\
       (!i. P(Atomic i)) /\
       (!y z. P z ==> P(Ite False y z)) /\
       (!y z. P y ==> P(Ite True y z)) /\
       (!i y z. P y /\ P z ==> P (Ite (Atomic i) y z)) /\
       (!u v w x y z. P(Ite u (Ite v y z) (Ite w y z))
                      ==> P(Ite (Ite u v w) y z))
       ==> !e. P e`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SIZEOF_INDUCT THEN
  MATCH_MP_TAC ite_INDUCT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ite_INDUCT THEN POP_ASSUM_LIST
   (fun ths -> REPEAT STRIP_TAC THEN FIRST(mapfilter MATCH_MP_TAC ths)) THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[sizeof] THEN TRY ARITH_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_AC; ADD_AC; LT_ADD_LCANCEL] THEN
  REWRITE_TAC[ADD_ASSOC; LT_ADD_RCANCEL] THEN
  MATCH_MP_TAC(ARITH_RULE `~(b = 0) /\ ~(c = 0) ==> a < (b + a) + c`) THEN
  REWRITE_TAC[MULT_EQ_0; SIZEOF_NZ]);;

let normalized = define
 `(normalized False <=> T) /\
  (normalized True <=> T) /\
  (normalized(Atomic a) <=> T) /\
  (normalized(Ite False x y) <=> F) /\
  (normalized(Ite True x y) <=> F) /\
  (normalized(Ite (Atomic a) x y) <=> normalized x /\ normalized y) /\
  (normalized(Ite (Ite u v w) x y) <=> F)`;;

let NORMALIZED_NORM = prove
 (`!e. normalized(norm e)`,
  MATCH_MP_TAC ITE_INDUCT THEN REWRITE_TAC[norm; normalized]);;

let NORMALIZED_INDUCT = prove
 (`P False /\
   P True /\
   (!i. P (Atomic i)) /\
   (!i x y. P x /\ P y ==> P (Ite (Atomic i) x y))
   ==> !e. normalized e ==> P e`,
  STRIP_TAC THEN MATCH_MP_TAC ite_INDUCT THEN ASM_REWRITE_TAC[normalized] THEN
  MATCH_MP_TAC ite_INDUCT THEN ASM_MESON_TAC[normalized]);;

let holds = define
 `(holds v False <=> F) /\
  (holds v True <=> T) /\
  (holds v (Atomic i) <=> v(i)) /\
  (holds v (Ite b x y) <=> if holds v b then holds v x else holds v y)`;;

let HOLDS_NORM = prove
 (`!e v. holds v (norm e) <=> holds v e`,
  MATCH_MP_TAC ITE_INDUCT THEN SIMP_TAC[holds; norm] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let taut = define
 `(taut (t,f) False <=> F) /\
  (taut (t,f) True <=> T) /\
  (taut (t,f) (Atomic i) <=> MEM i t) /\
  (taut (t,f) (Ite (Atomic i) x y) <=>
      if MEM i t then taut (t,f) x
      else if MEM i f then taut (t,f) y
      else taut (CONS i t,f) x /\ taut (t,CONS i f) y)`;;

let tautology = define `tautology e = taut([],[]) (norm e)`;;

let NORMALIZED_TAUT = prove
 (`!e. normalized e
       ==> !f t. (!a. ~(MEM a t /\ MEM a f))
                 ==> (taut (t,f) e <=>
                      !v. (!a. MEM a t ==> v(a)) /\ (!a. MEM a f ==> ~v(a))
                          ==> holds v e)`,
  MATCH_MP_TAC NORMALIZED_INDUCT THEN REWRITE_TAC[holds; taut] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `\a:num. MEM a t` THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC; DISCH_THEN MATCH_MP_TAC] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[])] THEN
  ASM_SIMP_TAC[MEM; RIGHT_OR_DISTRIB; LEFT_OR_DISTRIB;
               MESON[] `(!a. ~(MEM a t /\ a = i)) <=> ~(MEM i t)`;
               MESON[] `(!a. ~(a = i /\ MEM a f)) <=> ~(MEM i f)`] THEN
  ASM_REWRITE_TAC[AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  MESON_TAC[]);;

let TAUTOLOGY = prove
 (`!e. tautology e <=> !v. holds v e`,
  MESON_TAC[tautology; HOLDS_NORM; NORMALIZED_TAUT; MEM; NORMALIZED_NORM]);;

let HOLDS_BACK = prove
 (`!v. (F <=> holds v False) /\
       (T <=> holds v True) /\
       (!i. v i <=> holds v (Atomic i)) /\
       (!p. ~holds v p <=> holds v (Ite p False True)) /\
       (!p q. (holds v p /\ holds v q) <=> holds v (Ite p q False)) /\
       (!p q. (holds v p \/ holds v q) <=> holds v (Ite p True q)) /\
       (!p q. (holds v p <=> holds v q) <=>
                   holds v (Ite p q (Ite q False True))) /\
       (!p q. holds v p ==> holds v q <=> holds v (Ite p q True))`,
  REWRITE_TAC[holds] THEN CONV_TAC TAUT);;

let COND_CONV = GEN_REWRITE_CONV I [COND_CLAUSES];;
let AND_CONV = GEN_REWRITE_CONV I [TAUT `(F /\ a <=> F) /\ (T /\ a <=> a)`];;
let OR_CONV = GEN_REWRITE_CONV I [TAUT `(F \/ a <=> a) /\ (T \/ a <=> T)`];;

let rec COMPUTE_DEPTH_CONV conv tm =
  if is_cond tm then
   (RATOR_CONV(LAND_CONV(COMPUTE_DEPTH_CONV conv)) THENC
    COND_CONV THENC
    COMPUTE_DEPTH_CONV conv) tm
  else if is_conj tm then
   (LAND_CONV (COMPUTE_DEPTH_CONV conv) THENC
    AND_CONV THENC
    COMPUTE_DEPTH_CONV conv) tm
  else if is_disj tm then
   (LAND_CONV (COMPUTE_DEPTH_CONV conv) THENC
    OR_CONV THENC
    COMPUTE_DEPTH_CONV conv) tm
  else
   (SUB_CONV (COMPUTE_DEPTH_CONV conv) THENC
    TRY_CONV(conv THENC COMPUTE_DEPTH_CONV conv)) tm;;

g `!v. v 1 \/ v 2 \/ v 3 \/ v 4 \/ v 5 \/ v 6 \/
       ~v 1 \/ ~v 2 \/ ~v 3 \/ ~v 4 \/ ~v 5 \/ ~v 6`;;

e(MP_TAC HOLDS_BACK THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`v:num->bool`,`v:num->bool`) THEN
  REWRITE_TAC[GSYM TAUTOLOGY; tautology]);;

time e (GEN_REWRITE_TAC COMPUTE_DEPTH_CONV [norm; taut; MEM; ARITH_EQ]);;

ignore(b()); time e (REWRITE_TAC[norm; taut; MEM; ARITH_EQ]);;

(* ========================================================================= *)
(* Vectors                                                                   *)
(* ========================================================================= *)

needs "Multivariate/vectors.ml";;

needs "Examples/solovay.ml";;

g `orthogonal (A - B) (C - B)
   ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`;;

e SOLOVAY_VECTOR_TAC;;
e(CONV_TAC REAL_RING);;

g`!x y:real^N. x dot y <= norm x * norm y`;;
e SOLOVAY_VECTOR_TAC;;

(**** Needs external SDP solver
needs "Examples/sos.ml";;

e(CONV_TAC REAL_SOS);;

let EXAMPLE_0 = prove
 (`!a x y:real^N. (y - x) dot (a - y) >= &0 ==> norm(y - a) <= norm(x - a)`,
  SOLOVAY_VECTOR_TAC THEN CONV_TAC REAL_SOS);;
****)

needs "Rqe/make.ml";;
let EXAMPLE_10 = prove
 (`!x:real^N y.
        x dot y > &0
        ==> ?u. &0 < u /\
                !v. &0 < v /\ v <= u ==> norm(v % y - x) < norm x`,
  SOLOVAY_VECTOR_TAC THEN
  W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  CONV_TAC REAL_QELIM_CONV);;

let FORALL_3 = prove
 (`(!i. 1 <= i /\ i <= 3 ==> P i) <=> P 1 /\ P 2 /\ P 3`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> (i = 1) \/ (i = 2) \/ (i = 3)`]);;

let SUM_3 = prove
 (`!t. sum(1..3) t = t(1) + t(2) + t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let VECTOR_3 = prove
 (`(vector [x;y;z] :real^3)$1 = x /\
   (vector [x;y;z] :real^3)$2 = y /\
   (vector [x;y;z] :real^3)$3 = z`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_3; LENGTH; ARITH] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; EL; HD; TL]);;

let DOT_VECTOR = prove
 (`(vector [x1;y1;z1] :real^3) dot (vector [x2;y2;z2]) =
       x1 * x2 + y1 * y2 + z1 * z2`,
  REWRITE_TAC[dot; DIMINDEX_3; SUM_3; VECTOR_3]);;

let VECTOR_ZERO = prove
 (`(vector [x;y;z] :real^3 = vec 0) <=> x = &0 /\ y = &0 /\ z = &0`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_3; ARITH]);;

let ORTHOGONAL_VECTOR = prove
 (`orthogonal (vector [x1;y1;z1] :real^3) (vector [x2;y2;z2]) =
        (x1 * x2 + y1 * y2 + z1 * z2 = &0)`,
  REWRITE_TAC[orthogonal; DOT_VECTOR]);;

parse_as_infix("cross",(20,"right"));;

let cross = new_definition
 `(a:real^3) cross (b:real^3) =
    vector [a$2 * b$3 - a$3 * b$2;
            a$3 * b$1 - a$1 * b$3;
            a$1 * b$2 - a$2 * b$1] :real^3`;;

let VEC3_TAC =
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_3; SUM_3; DIMINDEX_3; VECTOR_3;
           vector_add; vec; dot; cross; orthogonal; basis; ARITH] THEN
  CONV_TAC REAL_RING;;

let VEC3_RULE tm = prove(tm,VEC3_TAC);;

let ORTHOGONAL_CROSS = VEC3_RULE
 `!x y. orthogonal (x cross y) x /\ orthogonal (x cross y) y /\
        orthogonal x (x cross y) /\ orthogonal y (x cross y)`;;

let LEMMA_0 = VEC3_RULE
 `~(basis 1 :real^3 = vec 0) /\
  ~(basis 2 :real^3 = vec 0) /\
  ~(basis 3 :real^3 = vec 0)`;;

let LEMMA_1 = VEC3_RULE `!u v. u dot (u cross v) = &0`;;

let LEMMA_2 = VEC3_RULE `!u v. v dot (u cross v) = &0`;;

let LEMMA_3 = VEC3_RULE `!u:real^3. vec 0 dot u = &0`;;

let LEMMA_4 = VEC3_RULE `!u:real^3. u dot vec 0 = &0`;;

let LEMMA_5 = VEC3_RULE `!x. x cross x = vec 0`;;

let LEMMA_6 = VEC3_RULE
 `!u. ~(u = vec 0)
      ==> ~(u cross basis 1 = vec 0) \/
          ~(u cross basis 2 = vec 0) \/
          ~(u cross basis 3 = vec 0)`;;

let LEMMA_7 = VEC3_RULE
 `!u v w. (u cross v = vec 0) ==> (u dot (v cross w) = &0)`;;

let NORMAL_EXISTS = prove
 (`!u v:real^3. ?w. ~(w = vec 0) /\ orthogonal u w /\ orthogonal v w`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`u:real^3 = vec 0`; `v:real^3 = vec 0`; `u cross v = vec 0`] THEN
  ASM_REWRITE_TAC[orthogonal] THEN
  ASM_MESON_TAC[LEMMA_0; LEMMA_1; LEMMA_2; LEMMA_3; LEMMA_4;
                LEMMA_5; LEMMA_6; LEMMA_7]);;

(* ========================================================================= *)
(* Custom tactics                                                            *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(* Defining new types                                                        *)
(* ========================================================================= *)

let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir")
 (MESON[LEMMA_0] `?x:real^3. ~(x = vec 0)`);;

parse_as_infix("||",(11,"right"));;
parse_as_infix("_|_",(11,"right"));;

let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;

let pardir = new_definition
 `x || y <=> (dest_dir x) cross (dest_dir y) = vec 0`;;

let DIRECTION_CLAUSES = prove
 (`((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`,
  MESON_TAC[direction_tybij]);;

let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let DIRECTION_AXIOM_1 = prove
 (`!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real^3`; `p':real^3`] NORMAL_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;

let DIRECTION_AXIOM_2 = prove
 (`!l l'. ?p. p _|_ l /\ p _|_ l'`,
  REWRITE_TAC[perpdir; DIRECTION_CLAUSES] THEN
  MESON_TAC[NORMAL_EXISTS; ORTHOGONAL_SYM]);;

let DIRECTION_AXIOM_3 = prove
 (`?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN
  MAP_EVERY (fun t -> EXISTS_TAC t THEN REWRITE_TAC[LEMMA_0])
   [`basis 1 :real^3`; `basis 2 : real^3`; `basis 3 :real^3`] THEN
  VEC3_TAC);;

let CROSS_0 = VEC3_RULE `x cross vec 0 = vec 0 /\ vec 0 cross x = vec 0`;;

let DIRECTION_AXIOM_4_WEAK = prove
 (`!l. ?p p'. ~(p || p') /\ p _|_ l /\ p' _|_ l`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 2) l /\
    ~((l cross basis 1) cross (l cross basis 2) = vec 0) \/
    orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 1) cross (l cross basis 3) = vec 0) \/
    orthogonal (l cross basis 2) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 2) cross (l cross basis 3) = vec 0)`
  MP_TAC THENL [POP_ASSUM MP_TAC THEN VEC3_TAC; MESON_TAC[CROSS_0]]);;

let ORTHOGONAL_COMBINE = prove
 (`!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `a + b:real^3` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;

let DIRECTION_AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l`,
  MESON_TAC[DIRECTION_AXIOM_4_WEAK; ORTHOGONAL_COMBINE]);;

let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;

let PERPDIR_WELLDEF = prove
 (`!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;

let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;

let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;

let point_tybij = new_type_definition "point" ("mk_point","dest_point")
 (prove(`?x:line. T`,REWRITE_TAC[]));;

parse_as_infix("on",(11,"right"));;

let on = new_definition `p on l <=> perpl (dest_point p) l`;;

let POINT_CLAUSES = prove
 (`((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))`,
  MESON_TAC[point_tybij]);;

let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;

let AXIOM_1 = prove
 (`!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)`,
  POINT_TAC LINE_AXIOM_1);;

let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;

let AXIOM_3 = prove
 (`?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)`,
  POINT_TAC LINE_AXIOM_3);;

let AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`,
  POINT_TAC LINE_AXIOM_4);;

(* ========================================================================= *)
(* Custom inference rules                                                    *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(* Linking external tools                                                    *)
(* ========================================================================= *)

let maximas e =
  let filename = Filename.temp_file "maxima" ".out" in
  let s =
    "echo 'linel:10000; display2d:false;" ^ e ^
    ";' | maxima | grep '^(%o3)' | sed -e 's/^(%o3) //' >" ^
    filename in
  if Sys.command s <> 0 then failwith "maxima" else
  let fd = Pervasives.open_in filename in
  let data = input_line fd in
  close_in fd; Sys.remove filename; data;;

prioritize_real();;
let maxima_ops = ["+",`(+)`; "-",`(-)`; "*",`( * )`;  "/",`(/)`; "^",`(pow)`];;
let maxima_funs = ["sin",`sin`; "cos",`cos`];;

let mk_uneg = curry mk_comb `(--)`;;

let dest_uneg =
  let ntm = `(--)` in
  fun tm -> let op,t = dest_comb tm in
            if op = ntm then t else failwith "dest_uneg";;

let mk_pow = let f = mk_binop `(pow)` in fun x y -> f x (rand y);;
let mk_realvar = let real_ty = `:real` in fun x -> mk_var(x,real_ty);;

let rec string_of_hol tm =
  if is_ratconst tm then "("^string_of_num(rat_of_term tm)^")"
  else if is_numeral tm then string_of_num(dest_numeral tm)
  else if is_var tm then fst(dest_var tm)
  else if can dest_uneg tm then "-(" ^ string_of_hol(rand tm) ^ ")" else
  let lop,r = dest_comb tm in
  try let op,l = dest_comb lop in
      "("^string_of_hol l^" "^ rev_assoc op maxima_ops^" "^string_of_hol r^")"
  with Failure _ -> rev_assoc lop maxima_funs ^ "(" ^ string_of_hol r ^ ")";;

string_of_hol `(x + sin(-- &2 * x)) pow 2 - cos(x - &22 / &7)`;;

let lexe s = map (function Resword s -> s | Ident s -> s) (lex(explode s));;

let parse_bracketed prs inp =
  match prs inp with
    ast,")"::rst -> ast,rst
  | _ -> failwith "Closing bracket expected";;

let rec parse_ginfix op opup sof prs inp =
  match prs inp with
    e1,hop::rst when hop = op -> parse_ginfix op opup (opup sof e1) prs rst
  | e1,rest -> sof e1,rest;;

let parse_general_infix op =
  let opcon = if op = "^" then mk_pow else mk_binop (assoc op maxima_ops) in
  let constr = if op <> "^" && snd(get_infix_status op) = "right"
               then fun f e1 e2 -> f(opcon e1 e2)
               else fun f e1 e2 -> opcon(f e1) e2 in
  parse_ginfix op constr (fun x -> x);;

let rec parse_atomic_expression inp =
  match inp with
   [] -> failwith "expression expected"
  | "(" :: rest -> parse_bracketed parse_expression rest
  | s :: rest when forall isnum (explode s) ->
        term_of_rat(num_of_string s),rest
  | s :: "(" :: rest when forall isalnum (explode s) ->
        let e,rst = parse_bracketed parse_expression rest in
        mk_comb(assoc s maxima_funs,e),rst
  | s :: rest when forall isalnum (explode s) -> mk_realvar s,rest
and parse_exp inp = parse_general_infix "^" parse_atomic_expression inp
and parse_neg inp =
  match inp with
   | "-" :: rest -> let e,rst = parse_neg rest in mk_uneg e,rst
   | _ -> parse_exp inp
and parse_expression inp =
  itlist parse_general_infix (map fst maxima_ops) parse_neg inp;;

let hol_of_string = fst o parse_expression o lexe;;

hol_of_string "sin(x) - cos(-(- - 1 + x))";;

let FACTOR_CONV tm =
  let s = "factor("^string_of_hol tm^")" in
  let tm' = hol_of_string(maximas s) in
  REAL_RING(mk_eq(tm,tm'));;

FACTOR_CONV `&1234567890`;;

FACTOR_CONV `x pow 6 - &1`;;

FACTOR_CONV `r * (r * x * (&1 - x)) * (&1 - r * x * (&1 - x)) - x`;;

let ANTIDERIV_CONV tm =
  let x,bod = dest_abs tm in
  let s = "integrate("^string_of_hol bod^","^fst(dest_var x)^")" in
  let tm' = mk_abs(x,hol_of_string(maximas s)) in
  let th1 = CONV_RULE (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)
                      (SPEC x (DIFF_CONV tm')) in
  let th2 = REAL_RING(mk_eq(lhand(concl th1),bod)) in
  GEN x (GEN_REWRITE_RULE LAND_CONV [th2] th1);;

ANTIDERIV_CONV `\x. (x + &5) pow 2 + &77 * x`;;

ANTIDERIV_CONV `\x. sin(x) + x pow 11`;;

(**** This one fails
ANTIDERIV_CONV `\x. sin(x) pow 3`;;
 ****)

let SIN_N_CLAUSES = prove
 (`(sin(&(NUMERAL(BIT0 n)) * x) =
    &2 * sin(&(NUMERAL n) * x) * cos(&(NUMERAL n) * x)) /\
   (sin(&(NUMERAL(BIT1 n)) * x) =
        sin(&(NUMERAL(BIT0 n)) * x) * cos(x) +
        sin(x) * cos(&(NUMERAL(BIT0 n)) * x)) /\
   (cos(&(NUMERAL(BIT0 n)) * x) =
        cos(&(NUMERAL n) * x) pow 2 - sin(&(NUMERAL n) * x) pow 2) /\
   (cos(&(NUMERAL(BIT1 n)) * x) =
        cos(&(NUMERAL(BIT0 n)) * x) * cos(x) -
        sin(x) * sin(&(NUMERAL(BIT0 n)) * x))`,
  REWRITE_TAC[REAL_MUL_2; REAL_POW_2] THEN
  REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SIN_ADD; COS_ADD; REAL_MUL_LID] THEN
  CONV_TAC REAL_RING);;

let TRIG_IDENT_TAC x =
  REWRITE_TAC[SIN_N_CLAUSES; SIN_ADD; COS_ADD] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SIN_0; COS_0; REAL_MUL_RZERO] THEN
  MP_TAC(SPEC x SIN_CIRCLE) THEN CONV_TAC REAL_RING;;

let ANTIDERIV_CONV tm =
  let x,bod = dest_abs tm in
  let s = "expand(integrate("^string_of_hol bod^","^fst(dest_var x)^"))" in
  let tm' = mk_abs(x,hol_of_string(maximas s)) in
  let th1 = CONV_RULE (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)
                      (SPEC x (DIFF_CONV tm')) in
  let th2 = prove(mk_eq(lhand(concl th1),bod),TRIG_IDENT_TAC x) in
  GEN x (GEN_REWRITE_RULE LAND_CONV [th2] th1);;

time ANTIDERIV_CONV `\x. sin(x) pow 3`;;

time ANTIDERIV_CONV `\x. sin(x) * sin(x) pow 5 * cos(x) pow 4 + cos(x)`;;

let FCT1_WEAK = prove
 (`(!x. (f diffl f'(x)) x) ==> !x. &0 <= x ==> defint(&0,x) f' (f x - f(&0))`,
  MESON_TAC[FTC1]);;

let INTEGRAL_CONV tm =
  let th1 = MATCH_MP FCT1_WEAK (ANTIDERIV_CONV tm) in
  (CONV_RULE REAL_RAT_REDUCE_CONV o
   REWRITE_RULE[SIN_0; COS_0; REAL_MUL_LZERO; REAL_MUL_RZERO] o
   CONV_RULE REAL_RAT_REDUCE_CONV o BETA_RULE) th1;;

INTEGRAL_CONV `\x. sin(x) pow 13`;;
