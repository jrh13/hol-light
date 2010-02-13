prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* First the R = 0 case.                                                     *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_1 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   D pow 2 = &3 * a pow 2 / &4 - &2 * b + &2 * s /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;

let QUARTIC_2 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   D pow 2 = &3 * a pow 2 / &4 - &2 * b + &2 * s /\
   x = --a / &4 + R / &2 - D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;

let QUARTIC_3 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   E pow 2 = &3 * a pow 2 / &4 - &2 * b - &2 * s /\
   x = --a / &4 - R / &2 + E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;

let QUARTIC_4 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   E pow 2 = &3 * a pow 2 / &4 - &2 * b - &2 * s /\
   x = --a / &4 - R / &2 - E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;


(* ------------------------------------------------------------------------- *)
(* The R nonzero case.                                                       *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_1' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   D pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b +
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;

let QUARTIC_2' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   D pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b +
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 + R / &2 - D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;

let QUARTIC_3' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   E pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 - R / &2 + E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;

let QUARTIC_4' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   E pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 - R / &2 - E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Combine them.                                                             *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_1 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* A case split.                                                             *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_1 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (x = --a / &4 + R / &2 + D / &2 \/
    x = --a / &4 - R / &2 + E / &2)
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* More general case split.                                                  *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_CASES = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (x = --a / &4 + R / &2 + D / &2 \/
    x = --a / &4 + R / &2 - D / &2 \/
    x = --a / &4 - R / &2 + E / &2 \/
    x = --a / &4 - R / &2 - E / &2)
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Even this works --- great, that's nearly what we wanted.                  *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_CASES = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R))
   ==> (x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0 <=>
        x = --a / &4 + R / &2 + D / &2 \/
        x = --a / &4 + R / &2 - D / &2 \/
        x = --a / &4 - R / &2 + E / &2 \/
        x = --a / &4 - R / &2 - E / &2)`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* This is the automatic proof.                                              *)
(* ------------------------------------------------------------------------- *)

let QUARTIC_CASES = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R))
   ==> (x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0 <=>
        x = --a / &4 + R / &2 + D / &2 \/
        x = --a / &4 + R / &2 - D / &2 \/
        x = --a / &4 - R / &2 + E / &2 \/
        x = --a / &4 - R / &2 - E / &2)`,
  CONV_TAC REAL_FIELD);;
