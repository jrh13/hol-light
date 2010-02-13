(* ------------------------------------------------------------------------- *)
(* Condense subdivision by removing points with no relevant zeros.           *)
(* ------------------------------------------------------------------------- *)

let real_cases = prove(`!x y. x < y \/ (x = y) \/ y < x`,REAL_ARITH_TAC);;

let gt_aux = prove(
  `!x. (x1 < x2 /\ x2 < x3) /\ ((x1 < x /\ x < x2) \/ (x = x2) \/ (x2 < x /\ x < x3)) ==> x1 < x /\ x < x3`,
   REAL_ARITH_TAC);;

let gen_thm = prove_by_refinement(
 `!P x1 x2 x3. 
      (x1 < x3) ==> 
      (!x. x1 < x /\ x < x2 ==> P x) ==> 
      (!x. (x = x2) ==> P x) ==> 
      (!x. x2 < x /\ x < x3 ==> P x) ==> 
        (!x. x1 < x /\ x < x3 ==> P x)`, 
(* {{{ Proof *)

[
  MESON_TAC[real_cases;gt_aux;DE_MORGAN_THM;REAL_NOT_LT;REAL_LE_LT];
]);;

(* }}} *)

let gen_thm_noleft = prove(
 `!P x2 x3. 
      (x2 < x3) ==> 
      (!x. x < x2 ==> P x) ==> 
      (!x. (x = x2) ==> P x) ==> 
      (!x. x2 < x /\ x < x3 ==> P x) ==> 
        (!x. x < x3 ==> P x)`, 
  MESON_TAC[real_cases;gt_aux]);;

let gen_thm_noright = prove(
 `!P x1 x2. 
      (x1 < x2) ==> 
      (!x. x1 < x /\ x < x2 ==> P x) ==> 
      (!x. (x = x2) ==> P x) ==> 
      (!x. x2 < x ==> P x) ==> 
        (!x. x1 < x ==> P x)`, 
  MESON_TAC[real_cases;gt_aux]);;

let gen_thm_noboth = prove(
 `!P Q x2. 
       Q ==>                                      
      (!x. x < x2 ==> P x) ==> 
      (!x. (x = x2) ==> P x) ==> 
      (!x. x2 < x ==> P x) ==> 
        (!x. T ==> P x)`, 
  MESON_TAC[real_cases;gt_aux]);;
