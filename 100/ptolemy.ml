(* ========================================================================= *)
(* Ptolemy's theorem.                                                        *)
(* ========================================================================= *)

needs "Multivariate/vectors.ml";;
needs "Library/transc.ml";;

(* ------------------------------------------------------------------------- *)
(* This gets overwritten by a theorem in transc load.                        *)
(* ------------------------------------------------------------------------- *)

let SUM_2 = prove
 (`!t. sum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `2`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Some 2-vector special cases.                                              *)
(* ------------------------------------------------------------------------- *)

let DOT_VECTOR = prove
 (`(vector [x1;y1] :real^2) dot (vector [x2;y2]) = x1 * x2 + y1 * y2`,
  REWRITE_TAC[dot; DIMINDEX_2; SUM_2; VECTOR_2]);;

(* ------------------------------------------------------------------------- *)
(* Lemma about distance between points with polar coordinates.               *)
(* ------------------------------------------------------------------------- *)

let SIN_SUB = prove
 (`!x y. sin(x - y) = sin(x) * cos(y) - cos(x) * sin(y)`,
  REWRITE_TAC[real_sub; SIN_ADD; COS_NEG; SIN_NEG] THEN CONV_TAC REAL_RING);;

let DIST_SEGMENT_LEMMA = prove
 (`!a1 a2. &0 <= a1 /\ a1 <= a2 /\ a2 <= &2 * pi /\ &0 <= radius
           ==> dist(centre + radius % vector [cos(a1);sin(a1)] :real^2,
                    centre + radius % vector [cos(a2);sin(a2)]) =
               &2 * radius *  sin((a2 - a1) / &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist; vector_norm] THEN
  MATCH_MP_TAC SQRT_POS_UNIQ THEN REWRITE_TAC[DOT_POS_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIN_POS_PI_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(c + r % x) - (c + r % y) = r % (x - y)`] THEN
  REWRITE_TAC[VECTOR_ARITH `(r % x) dot (r % x) = (r pow 2) * (x dot x)`] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_VECTOR] THEN
  SUBST1_TAC(REAL_ARITH `a1 = &2 * a1 / &2`) THEN
  SUBST1_TAC(REAL_ARITH `a2 = &2 * a2 / &2`) THEN
  REWRITE_TAC[REAL_ARITH `(&2 * x - &2 * y) / &2 = x - y`] THEN
  REWRITE_TAC[SIN_SUB; SIN_DOUBLE; COS_DOUBLE] THEN
  MP_TAC(SPEC `a1 / &2` SIN_CIRCLE) THEN MP_TAC(SPEC `a2 / &2` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Hence the overall theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let PTOLEMY = prove
 (`!A B C D:real^2 a b c d centre radius.
        A = centre + radius % vector [cos(a);sin(a)] /\
        B = centre + radius % vector [cos(b);sin(b)] /\
        C = centre + radius % vector [cos(c);sin(c)] /\
        D = centre + radius % vector [cos(d);sin(d)] /\
        &0 <= radius /\
        &0 <= a /\ a <= b /\ b <= c /\ c <= d /\ d <= &2 * pi
        ==> dist(A,C) * dist(B,D) =
            dist(A,B) * dist(C,D) + dist(A,D) * dist(B,C)`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl))) THEN
  REPEAT
   (W(fun (asl,w) ->
     let t = find_term
      (fun t -> can (PART_MATCH (lhs o rand) DIST_SEGMENT_LEMMA) t) w in
     MP_TAC (PART_MATCH (lhs o rand) DIST_SEGMENT_LEMMA t) THEN
     ANTS_TAC THENL
      [ASM_REAL_ARITH_TAC;
       DISCH_THEN SUBST1_TAC])) THEN
  REWRITE_TAC[REAL_ARITH `(x - y) / &2 = x / &2 - y / &2`] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t SIN_CIRCLE))
   [`a / &2`; `b / &2`; `c / &2`; `d / &2`] THEN
  REWRITE_TAC[SIN_SUB; SIN_ADD; COS_ADD; SIN_PI; COS_PI] THEN
  CONV_TAC REAL_RING);;
