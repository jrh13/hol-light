(* ========================================================================= *)
(* Complex numbers and quaternions in the geometric algebra theory.          *)
(*                                                                           *)
(*        (c) Copyright, Capital Normal University, China, 2018.             *)
(*     Authors: Liming Li, Zhiping Shi, Yong Guan, Guohui Wang, Sha Ma.      *)
(* ========================================================================= *)

needs "Geometric_Algebra/geometricalgebra.ml";;
needs "Quaternions/make.ml";;

(* ------------------------------------------------------------------------- *)
(* Complexes in GA.                                                          *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_GA010 = prove
 (`dimindex(:('0,'1,'0)geomalg) = dimindex(:2)`,
  REWRITE_TAC[DIMINDEX_2; DIMINDEX_GEOMALG; PDIMINDEX_0; PDIMINDEX_1] THEN ARITH_TAC);;

let COMPLEX_PRODUCT_GA010 = prove
 (`!x y:real^('0,'1,'0)geomalg.
     x * y =
       (x $$ {} * y $$ {} - x $$ {1} * y $$ {1}) % mbasis {} +
       (x $$ {} * y $$ {1} + x $$ {1} * y $$ {}) % mbasis {1}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
  REWRITE_TAC[PDIMINDEX_0; PDIMINDEX_1; ADD_0; ADD_SYM; NUMSEG_SING] THEN
  REWRITE_TAC[prove(`{s | s SUBSET {1}} = {{}, {1}}`, REWRITE_TAC[POWERSET_CLAUSES] THEN SET_TAC[])] THEN
  SIMP_TAC[VSUM_CLAUSES;FINITE_INSERT; FINITE_SING; IN_INSERT; IN_SING; NOT_EMPTY_INSERT; VSUM_SING] THEN
  CONV_TAC GEOM_ARITH);;

GEOM_ARITH `mbasis{1}:real^('0,'1,'0)geomalg * mbasis{1} = --mbasis{}`;;
GEOM_ARITH `mbasis{1,2}:real^('2,'0,'0)geomalg * mbasis{1,2} = --mbasis{}`;;

(* ------------------------------------------------------------------------- *)
(* Quaternions in GA.                                                        *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_GA020 = prove
 (`dimindex(:('0,'2,'0)geomalg) = dimindex(:4)`,
  REWRITE_TAC[DIMINDEX_4; DIMINDEX_GEOMALG; PDIMINDEX_0; PDIMINDEX_2] THEN ARITH_TAC);;

let QUAT_PRODUCT_GA020 = prove
 (`!x y:real^('0,'2,'0)geomalg.
     x * y =
       (x $$ {} * y $$ {} - x $$ {1} * y $$ {1} - x $$ {2} * y $$ {2} - x $$ {1,2} * y $$ {1,2}) % mbasis {} +
       (x $$ {} * y $$ {1} + x $$ {1} * y $$ {} + x $$ {2} * y $$ {1,2} - x $$ {1,2} * y $$ {2}) % mbasis {1} +
       (x $$ {} * y $$ {2} - x $$ {1} * y $$ {1,2} + x $$ {2} * y $$ {} + x $$ {1,2} * y $$ {1}) % mbasis {2} +
       (x $$ {} * y $$ {1,2} + x $$ {1} * y $$ {2} - x $$ {2} * y $$ {1} + x $$ {1,2} * y $$ {}) % mbasis {1,2}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
  REWRITE_TAC[PDIMINDEX_0; PDIMINDEX_2; ADD_0; ADD_SYM] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[TWO] THEN REWRITE_TAC[NUMSEG_CLAUSES] THEN REWRITE_TAC[ARITH; NUMSEG_SING] THEN
  REWRITE_TAC[prove(`{s | s SUBSET {2,1}} = {{}, {1}, {2}, {1,2}}`,
     REWRITE_TAC[POWERSET_CLAUSES] THEN REWRITE_TAC[EXTENSION] THEN
     GEN_TAC THEN REWRITE_TAC[IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN REWRITE_TAC[GSYM DISJ_ASSOC] THEN
     MATCH_MP_TAC (TAUT `p1 = q1 /\ p2 = q2 ==> (p1 \/ p2) = (q1 \/q2)`) THEN CONJ_TAC THENL[SET_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC (TAUT `p1 = q1 /\ p2 = q2 ==> (p1 \/ p2) = (q1 \/q2)`) THEN CONJ_TAC THEN
     EQ_TAC THENL[SET_TAC[]; ALL_TAC; SET_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
      [EXISTS_TAC `{}:num->bool`; EXISTS_TAC `{}:num->bool`; EXISTS_TAC `{1}:num->bool`] THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL[SET_TAC[]; ALL_TAC] THEN DISJ2_TAC THEN EXISTS_TAC `{}:num->bool` THEN ASM_REWRITE_TAC[])] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_SING; IN_INSERT; IN_SING; NOT_EMPTY_INSERT; VSUM_SING] THEN
  SIMP_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[prove(`!a b:num. (!x. (x=a) <=> (x=b)) <=> (a=b)`, MESON_TAC[]);
              prove(`!a b:num. (!x. (x=a) <=> (x=a) \/ (x=b)) <=> (a=b)`, MESON_TAC[]);
              DISJ_SYM; ARITH_EQ] THEN
  CONV_TAC GEOM_ARITH);;

GEOM_ARITH `(mbasis{1}:real^('0,'2,'0)geomalg)* mbasis{1} = --mbasis{}`;;
GEOM_ARITH `(mbasis{2}:real^('0,'2,'0)geomalg)* mbasis{2} = --mbasis {}`;;
GEOM_ARITH `(mbasis{1,2}:real^('0,'2,'0)geomalg)* mbasis{1,2} = --mbasis {}`;;
GEOM_ARITH `(mbasis{1}:real^('0,'2,'0)geomalg)* mbasis{2} = mbasis {1,2}`;;
GEOM_ARITH `(mbasis{2}:real^('0,'2,'0)geomalg)* mbasis{1,2} = mbasis {1}`;;
GEOM_ARITH `(mbasis{1,2}:real^('0,'2,'0)geomalg)* mbasis{1} = mbasis {2}`;;
GEOM_ARITH `(mbasis{1}:real^('0,'2,'0)geomalg)* mbasis{2} = --(mbasis{2} * mbasis{1})`;;
GEOM_ARITH `(mbasis{2}:real^('0,'2,'0)geomalg)* mbasis{1,2} = --(mbasis{1,2} * mbasis {2})`;;
GEOM_ARITH `(mbasis{1,2}:real^('0,'2,'0)geomalg)* mbasis{1} = --(mbasis{1} * mbasis{1,2})`;;
GEOM_ARITH `(mbasis{1}:real^('0,'2,'0)geomalg)* mbasis{2} * mbasis{1,2} = --mbasis{}`;;

let geomalg_300_quat = new_definition
`geomalg_300_quat (q:quat) =
  (Re q) % mbasis{} +
  (Im1 q) % mbasis{2,3} +
  (Im2 q) % mbasis{1,2} +
  (Im3 q) % (--(mbasis{1,3}:real^('3,'0,'0)geomalg))`;;

let CNJ_QUAT = prove
(`!q:quat. conjugation (geomalg_300_quat q) = geomalg_300_quat (cnj q)`,
  GEN_TAC THEN REWRITE_TAC[conjugation; geomalg_300_quat; quat_cnj; QUAT_COMPONENTS] THEN
  SIMP_TAC[GEOMALG_BETA; GEOMALG_EQ] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_NEG_MINUS1; GEOMALG_ADD_COMPONENT; GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[MVBASIS_COMPONENT] THEN
  BINOP_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[PDIMINDEX_3; PDIMINDEX_0] THEN
    REWRITE_TAC[ARITH; (NUMSEG_CONV `4..3`); INTER_EMPTY] THEN
    CONV_TAC REVERSION_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  BINOP_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[PDIMINDEX_3; PDIMINDEX_0] THEN
    REWRITE_TAC[ARITH; (NUMSEG_CONV `4..3`); INTER_EMPTY] THEN
    CONV_TAC REVERSION_CONV THEN REAL_ARITH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  BINOP_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[PDIMINDEX_3; PDIMINDEX_0] THEN
    REWRITE_TAC[ARITH; (NUMSEG_CONV `4..3`); INTER_EMPTY] THEN
    CONV_TAC REVERSION_CONV THEN REAL_ARITH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PDIMINDEX_3; PDIMINDEX_0] THEN
    REWRITE_TAC[ARITH; (NUMSEG_CONV `4..3`); INTER_EMPTY] THEN
    CONV_TAC REVERSION_CONV THEN REAL_ARITH_TAC THEN REAL_ARITH_TAC);;

GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'0)geomalg)* mbasis{2,3} = --mbasis{}`;;
GEOM_ARITH `(mbasis{1,2}:real^('3,'0,'0)geomalg)* mbasis{1,2} = --mbasis{}`;;
GEOM_ARITH `(--mbasis{1,3}:real^('3,'0,'0)geomalg)*(--mbasis{1,3}) = --mbasis{}`;;
GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'0)geomalg)* mbasis {1,2} = --mbasis{1,3}`;;
GEOM_ARITH `(mbasis{1,2}:real^('3,'0,'0)geomalg)*(--mbasis{1,3}) = mbasis{2,3}`;;
GEOM_ARITH `(--mbasis{1,3}:real^('3,'0,'0)geomalg)* mbasis{2,3} = mbasis{1,2}`;;
GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'0)geomalg)* mbasis{1,2} = --(mbasis{1,2} * mbasis{2,3})`;;
GEOM_ARITH `(mbasis{1,2}:real^('3,'0,'0)geomalg)*(--mbasis{1,3})= --(--mbasis{1,3} * mbasis{1,2})`;;
GEOM_ARITH `(--mbasis{1,3}:real^('3,'0,'0)geomalg)* mbasis{2,3} = --(mbasis{2,3} * --mbasis{1,3})`;;
GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'0)geomalg)* mbasis{1,2} * --mbasis{1,3} = --mbasis{}`;;

(* ------------------------------------------------------------------------- *)
(* Dual quaternions in GA.                                                   *)
(* ------------------------------------------------------------------------- *)

GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'1)geomalg)* mbasis{2,3} = --mbasis{}`;;
GEOM_ARITH `(mbasis{1,2}:real^('3,'0,'1)geomalg)* mbasis{1,2} = --mbasis{}`;;
GEOM_ARITH `(--mbasis{1,3}:real^('3,'0,'1)geomalg)*(--mbasis{1,3}) = --mbasis{}`;;
GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'1)geomalg)* mbasis {1,2} = --mbasis{1,3}`;;
GEOM_ARITH `(mbasis{1,2}:real^('3,'0,'1)geomalg)*(--mbasis{1,3}) = mbasis{2,3}`;;
GEOM_ARITH `(--mbasis{1,3}:real^('3,'0,'1)geomalg)* mbasis{2,3} = mbasis{1,2}`;;
GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'1)geomalg)* mbasis{1,2} = --(mbasis{1,2} * mbasis{2,3})`;;
GEOM_ARITH `(mbasis{1,2}:real^('3,'0,'1)geomalg)*(--mbasis{1,3})= --(--mbasis{1,3} * mbasis{1,2})`;;
GEOM_ARITH `(--mbasis{1,3}:real^('3,'0,'1)geomalg)* mbasis{2,3} = --(mbasis{2,3} * --mbasis{1,3})`;;
GEOM_ARITH `(mbasis{2,3}:real^('3,'0,'1)geomalg)* mbasis{1,2} * --mbasis{1,3} = --mbasis{}`;;
GEOM_ARITH `mbasis{2,3}:real^('3,'0,'1)geomalg * mbasis{1,2,3,4} = mbasis{1,2,3,4} * mbasis{2,3}`;;
GEOM_ARITH `mbasis{1,2}:real^('3,'0,'1)geomalg * mbasis{1,2,3,4} = mbasis{1,2,3,4} * mbasis{1,2}`;;
GEOM_ARITH `--mbasis{1,3}:real^('3,'0,'1)geomalg * mbasis{1,2,3,4}= mbasis{1,2,3,4}* --mbasis{1,3}`;;
GEOM_ARITH `mbasis{1,2,3,4}:real^('3,'0,'1)geomalg * mbasis{1,2,3,4} = vec 0`;;
