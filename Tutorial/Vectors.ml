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

(*** Needs Rqe loaded

needs "Rqe/make.ml";;
let EXAMPLE_10 = prove
 (`!x:real^N y.
        x dot y > &0
        ==> ?u. &0 < u /\
                !v. &0 < v /\ v <= u ==> norm(v % y - x) < norm x`,
  SOLOVAY_VECTOR_TAC THEN
  W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  CONV_TAC REAL_QELIM_CONV);;

****)

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
