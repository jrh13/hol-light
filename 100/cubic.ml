(* ========================================================================= *)
(* Cubic formula.                                                            *)
(* ========================================================================= *)

needs "Complex/complex_transc.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Define cube roots (it doesn't matter which one we choose here)            *)
(* ------------------------------------------------------------------------- *)

let ccbrt = new_definition
 `ccbrt(z) = if z = Cx(&0) then Cx(&0) else cexp(clog(z) / Cx(&3))`;;

let CCBRT = prove
 (`!z. ccbrt(z) pow 3 = z`,
  GEN_TAC THEN REWRITE_TAC[ccbrt] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_FIELD `z pow 3 = z * z * z:complex`; GSYM CEXP_ADD] THEN
  REWRITE_TAC[COMPLEX_FIELD `z / Cx(&3) + z / Cx(&3) + z / Cx(&3) = z`] THEN
  ASM_SIMP_TAC[CEXP_CLOG]);;

(* ------------------------------------------------------------------------- *)
(* The reduction to a simpler form.                                          *)
(* ------------------------------------------------------------------------- *)

let CUBIC_REDUCTION = COMPLEX_FIELD
  `~(a = Cx(&0)) /\
   x = y - b / (Cx(&3) * a) /\
   p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2) /\
   q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
       (Cx(&54) * a pow 3)
   ==> (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
        y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* The solutions of the special form.                                        *)
(* ------------------------------------------------------------------------- *)

let CUBIC_BASIC = COMPLEX_FIELD
 `!i t s.
    s pow 2 = q pow 2 + p pow 3 /\
    (s1 pow 3 = if p = Cx(&0) then Cx(&2) * q else q + s) /\
    s2 = --s1 * (Cx(&1) + i * t) / Cx(&2) /\
    s3 = --s1 * (Cx(&1) - i * t) / Cx(&2) /\
    i pow 2 + Cx(&1) = Cx(&0) /\
    t pow 2 = Cx(&3)
    ==> if p = Cx(&0) then
          (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0) <=>
           y = s1 \/ y = s2 \/ y = s3)
        else
          ~(s1 = Cx(&0)) /\
          (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0) <=>
               (y = s1 - p / s1 \/ y = s2 - p / s2 \/ y = s3 - p / s3))`;;

(* ------------------------------------------------------------------------- *)
(* Explicit formula for the roots (doesn't matter which square/cube roots).  *)
(* ------------------------------------------------------------------------- *)

let CUBIC = prove
 (`~(a = Cx(&0))
   ==> let p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2)
       and q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
               (Cx(&54) * a pow 3) in
       let s = csqrt(q pow 2 + p pow 3) in
       let s1 = if p = Cx(&0) then ccbrt(Cx(&2) * q) else ccbrt(q + s) in
       let s2 = --s1 * (Cx(&1) + ii * csqrt(Cx(&3))) / Cx(&2)
       and s3 = --s1 * (Cx(&1) - ii * csqrt(Cx(&3))) / Cx(&2) in
       if p = Cx(&0) then
         a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
            x = s1 - b / (Cx(&3) * a) \/
            x = s2 - b / (Cx(&3) * a) \/
            x = s3 - b / (Cx(&3) * a)
       else
         ~(s1 = Cx(&0)) /\
         (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
             x = s1 - p / s1 - b / (Cx(&3) * a) \/
             x = s2 - p / s2 - b / (Cx(&3) * a) \/
             x = s3 - p / s3 - b / (Cx(&3) * a))`,
  DISCH_TAC THEN REPEAT LET_TAC THEN
  ABBREV_TAC `y = x + b / (Cx(&3) * a)` THEN
  SUBGOAL_THEN
   `a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
    y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CUBIC_REDUCTION THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "y" THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `x = a - b <=> x + b = (a:complex)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CUBIC_BASIC THEN
  MAP_EVERY EXISTS_TAC
   [`ii`; `csqrt(Cx(&3))`; `csqrt (q pow 2 + p pow 3)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CSQRT];
    ASM_MESON_TAC[CCBRT];
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING;
    ASM_MESON_TAC[CSQRT]]);;
