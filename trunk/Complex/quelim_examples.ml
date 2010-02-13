(* ========================================================================= *)
(* Some examples of full complex quantifier elimination.                     *)
(* ========================================================================= *)

let th = time prove
 (`!x y. (x pow 2 = Cx(&2)) /\ (y pow 2 = Cx(&3))
         ==> ((x * y) pow 2 = Cx(&6))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`!x a. (a pow 2 = Cx(&2)) /\ (x pow 2 + a * x + Cx(&1) = Cx(&0))
         ==> (x pow 4 + Cx(&1) = Cx(&0))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`!a x. (a pow 2 = Cx(&2)) /\ (x pow 2 + a * x + Cx(&1) = Cx(&0))
         ==> (x pow 4 + Cx(&1) = Cx(&0))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`~(?a x y. (a pow 2 = Cx(&2)) /\
             (x pow 2 + a * x + Cx(&1) = Cx(&0)) /\
             (y * (x pow 4 + Cx(&1)) + Cx(&1) = Cx(&0)))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`!x. ?y. x pow 2 = y pow 3`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`!x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               Cx(&2) * (b * x + b * z - a * y)`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`!a b. ~(a = b) ==> ?x y. (y * x pow 2 = a) /\ (y * x pow 2 + x = b)`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`!a b c x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
               (a * y pow 2 + b * y + c = Cx(&0)) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = Cx(&0))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

let th = time prove
 (`~(!a b c x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
                 (a * y pow 2 + b * y + c = Cx(&0))
                 ==> (a * x * y = c) /\ (a * (x + y) + b = Cx(&0)))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

(** geometric example from ``Algorithms for Computer Algebra'':
    right triangle where perp. bisector of hypotenuse passes through the
    right angle is isoseles.
 **)

let th = time prove
 (`!y_1 y_2 y_3 y_4.
     (y_1 = Cx(&2) * y_3) /\
     (y_2 = Cx(&2) * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1 pow 2 = y_2 pow 2)`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

(** geometric example: gradient condition for two lines to be non-parallel.
 **)

let th = time prove
 (`!a1 b1 c1 a2 b2 c2.
        ~(a1 * b2 = a2 * b1)
        ==> ?x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

(*********** Apparently takes too long

let th = time prove
 (`!a b c x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
               (a * y pow 2 + b * y + c = Cx(&0)) /\
               (!z. (a * z pow 2 + b * z + c = Cx(&0))
                    ==> (z = x) \/ (z = y))
               ==> (a * x * y = c) /\ (a * (x + y) + b = Cx(&0))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

*************)

(* ------------------------------------------------------------------------- *)
(* Any three points determine a circle. Not true in complex number version!  *)
(* ------------------------------------------------------------------------- *)

(******** And it takes a lot of memory!

let th = time prove
 (`~(!x1 y1 x2 y2 x3 y3.
        ?x0 y0. ((x1 - x0) pow 2 + (y1 - y0) pow 2 =
                 (x2 - x0) pow 2 + (y2 - y0) pow 2) /\
                ((x2 - x0) pow 2 + (y2 - y0) pow 2 =
                 (x3 - x0) pow 2 + (y3 - y0) pow 2))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

 **************)

(* ------------------------------------------------------------------------- *)
(* To show we don't need to consider only closed formulas.                   *)
(* Can eliminate some, then deal with the rest manually and painfully.       *)
(* ------------------------------------------------------------------------- *)

let th = time prove
 (`(?x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
          (a * y pow 2 + b * y + c = Cx(&0)) /\
          ~(x = y)) <=>
   (a = Cx(&0)) /\ (b = Cx(&0)) /\ (c = Cx(&0)) \/
   ~(a = Cx(&0)) /\ ~(b pow 2 = Cx(&4) * a * c)`,
  CONV_TAC(LAND_CONV FULL_COMPLEX_QUELIM_CONV) THEN
  REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_ADD_RID] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
  ASM_CASES_TAC `a = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THENL
   [ASM_CASES_TAC `b = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO];
    ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH
     `b * b * c * Cx(--(&1)) + a * c * c * Cx(&4) =
      c * (Cx(&4) * a * c - b * b)`] THEN
    ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH
     `b * b * b * Cx(--(&1)) + a * b * c * Cx (&4) =
      b * (Cx(&4) * a * c - b * b)`] THEN
    ONCE_REWRITE_TAC[SIMPLE_COMPLEX_ARITH
     `b * b * Cx (&1) + a * c * Cx(--(&4)) =
      Cx(--(&1)) * (Cx(&4) * a * c - b * b)`] THEN
    REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_SUB_0; CX_INJ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_CASES_TAC `b = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `c = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_POW_2; COMPLEX_MUL_RZERO; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[EQ_SYM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Do the same thing directly.                                               *)
(* ------------------------------------------------------------------------- *)

(**** This seems barely feasible

let th = time prove
 (`!a b c.
      (?x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
             (a * y pow 2 + b * y + c = Cx(&0)) /\
             ~(x = y)) <=>
      (a = Cx(&0)) /\ (b = Cx(&0)) /\ (c = Cx(&0)) \/
      ~(a = Cx(&0)) /\ ~(b pow 2 = Cx(&4) * a * c)`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

 ****)

(* ------------------------------------------------------------------------- *)
(* More ambitious: determine a unique circle. Also not true over complexes.  *)
(* (consider the points (k, k i) where i is the imaginary unit...)           *)
(* ------------------------------------------------------------------------- *)

(********** Takes too long, I think, and too much memory too

let th = prove
 (`~(!x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        ((x1 - x0) pow 2 + (y1 - y0) pow 2 =
         (x2 - x0) pow 2 + (y2 - y0) pow 2) /\
        ((x2 - x0) pow 2 + (y2 - y0) pow 2 =
         (x3 - x0) pow 2 + (y3 - y0) pow 2) /\
        ((x1 - x0') pow 2 + (y1 - y0') pow 2 =
         (x2 - x0') pow 2 + (y2 - y0') pow 2) /\
        ((x2 - x0') pow 2 + (y2 - y0') pow 2 =
         (x3 - x0') pow 2 + (y3 - y0') pow 2)
        ==> (x0 = x0') /\ (y0 = y0'))`,
  CONV_TAC FULL_COMPLEX_QUELIM_CONV);;

 *************)

(* ------------------------------------------------------------------------- *)
(* Side of a triangle in terms of its bisectors; Kapur survey 5.1.           *)
(* ------------------------------------------------------------------------- *)

(*************
let th = time FULL_COMPLEX_QUELIM_CONV
 `?b c. (p1 = ai pow 2 * (b + c) pow 2 - c * b * (c + b - a) * (c + b + a)) /\
        (p2 = ae pow 2 * (c - b) pow 2 - c * b * (a + b - c) * (a - b + a)) /\
        (p3 = be pow 2 * (c - a) pow 2 - a * c * (a + b - c) * (c + b - a))`;;

 *************)
