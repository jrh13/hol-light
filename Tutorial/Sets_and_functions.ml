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
