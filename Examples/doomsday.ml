(* ========================================================================= *)
(* Formalization of Conway's Doomsday Algorithm by Claude Opus 4.6           *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Part 1: Calendar primitives                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Leap year: a year is a leap year iff it is divisible by 4 but not 100,    *)
(* or divisible by 400.                                                      *)
(* ------------------------------------------------------------------------- *)

let leap_year = new_definition
 `leap_year y <=> (4 divides y /\ ~(100 divides y)) \/ 400 divides y`;;

(* Equivalent characterization using MOD                                     *)
let LEAP_YEAR_MOD = prove
 (`!y. leap_year y <=>
       y MOD 4 = 0 /\ ~(y MOD 100 = 0) \/ y MOD 400 = 0`,
  GEN_TAC THEN REWRITE_TAC[leap_year; DIVIDES_MOD]);;

(* ------------------------------------------------------------------------- *)
(* Days in each month                                                        *)
(* ------------------------------------------------------------------------- *)

let days_in_month = new_definition
 `days_in_month y m =
    if m = 1 then 31
    else if m = 2 then (if leap_year y then 29 else 28)
    else if m = 3 then 31
    else if m = 4 then 30
    else if m = 5 then 31
    else if m = 6 then 30
    else if m = 7 then 31
    else if m = 8 then 31
    else if m = 9 then 30
    else if m = 10 then 31
    else if m = 11 then 30
    else if m = 12 then 31
    else 0`;;

(* ------------------------------------------------------------------------- *)
(* Days in a year                                                            *)
(* ------------------------------------------------------------------------- *)

let days_in_year = new_definition
 `days_in_year y = if leap_year y then 366 else 365`;;

(* ------------------------------------------------------------------------- *)
(* Valid date predicate                                                      *)
(* ------------------------------------------------------------------------- *)

let valid_date = new_definition
 `valid_date (y,m,d) <=>
    1 <= m /\ m <= 12 /\ 1 <= d /\ d <= days_in_month y m`;;

(* ------------------------------------------------------------------------- *)
(* Concrete leap year evaluations                                            *)
(* ------------------------------------------------------------------------- *)

let LEAP_YEAR_2000 = prove
 (`leap_year 2000`,
  REWRITE_TAC[LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let NOT_LEAP_YEAR_1900 = prove
 (`~(leap_year 1900)`,
  REWRITE_TAC[LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let LEAP_YEAR_2024 = prove
 (`leap_year 2024`,
  REWRITE_TAC[LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let NOT_LEAP_YEAR_2023 = prove
 (`~(leap_year 2023)`,
  REWRITE_TAC[LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let NOT_LEAP_YEAR_2100 = prove
 (`~(leap_year 2100)`,
  REWRITE_TAC[LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let LEAP_YEAR_2400 = prove
 (`leap_year 2400`,
  REWRITE_TAC[LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Useful tactic for 12-month case splits *)
let MONTH_CASES_TAC =
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT; ARITH_RULE `n <= 12 <=> n < 13`] THEN
  CONV_TAC EXPAND_CASES_CONV;;

(* Days in month bounds *)
let DAYS_IN_MONTH_POS = prove
 (`!y m. 1 <= m /\ m <= 12 ==> 1 <= days_in_month y m`,
  MONTH_CASES_TAC THEN
  REWRITE_TAC[days_in_month] THEN ARITH_TAC);;

let DAYS_IN_MONTH_UPPER = prove
 (`!y m. days_in_month y m <= 31`,
  REPEAT GEN_TAC THEN REWRITE_TAC[days_in_month] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC);;

(* ========================================================================= *)
(* Part 2: Day counting                                                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Cumulative days before a given month within a year                        *)
(* ------------------------------------------------------------------------- *)

let cumdays_before = new_definition
 `cumdays_before y m =
    if m <= 1 then 0
    else if m = 2 then 31
    else if m = 3 then (if leap_year y then 60 else 59)
    else if m = 4 then (if leap_year y then 91 else 90)
    else if m = 5 then (if leap_year y then 121 else 120)
    else if m = 6 then (if leap_year y then 152 else 151)
    else if m = 7 then (if leap_year y then 182 else 181)
    else if m = 8 then (if leap_year y then 213 else 212)
    else if m = 9 then (if leap_year y then 244 else 243)
    else if m = 10 then (if leap_year y then 274 else 273)
    else if m = 11 then (if leap_year y then 305 else 304)
    else if m = 12 then (if leap_year y then 335 else 334)
    else (if leap_year y then 366 else 365)`;;

(* ------------------------------------------------------------------------- *)
(* Day of year: ordinal day number within a year (January 1 = 1)             *)
(* ------------------------------------------------------------------------- *)

let day_of_year = new_definition
 `day_of_year y m d = cumdays_before y m + d`;;

(* Cumdays_before is consistent with days_in_month: each step adds one       *)
let CUMDAYS_BEFORE_STEP = prove
 (`!y m. 1 <= m /\ m <= 12 ==>
         cumdays_before y (m + 1) = cumdays_before y m + days_in_month y m`,
  MONTH_CASES_TAC THEN REWRITE_TAC[cumdays_before; days_in_month] THEN
  ARITH_TAC);;

(* Days in year equals sum of all monthly days *)
let DAYS_IN_YEAR_SUM = prove
 (`!y. days_in_year y = cumdays_before y 13`,
  GEN_TAC THEN REWRITE_TAC[days_in_year; cumdays_before] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cumulative days: total days from year 0 to start of year y                *)
(* ------------------------------------------------------------------------- *)

let cumulative_days = define
 `cumulative_days 0 = 0 /\
  cumulative_days (SUC y) = cumulative_days y + days_in_year y`;;

(* ------------------------------------------------------------------------- *)
(* Day number: absolute day count from epoch                                 *)
(* ------------------------------------------------------------------------- *)

let day_number = new_definition
 `day_number y m d = cumulative_days y + day_of_year y m d`;;

(* ------------------------------------------------------------------------- *)
(* Day of week: 0=Sun, 1=Mon, 2=Tue, 3=Wed, 4=Thu, 5=Fri, 6=Sat              *)
(* Epoch calibration: +5 makes Jan 1, year 0 = Saturday (6)                  *)
(* ------------------------------------------------------------------------- *)

let day_of_week = new_definition
 `day_of_week y m d = (day_number y m d + 5) MOD 7`;;

(* ========================================================================= *)
(* Part 3: Doomsday algorithm definitions                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Doomsday dates: the day of the month that is a "doomsday" for each        *)
(* month. These all fall on the same day of the week within any given year.  *)
(* ------------------------------------------------------------------------- *)

let doomsday_date = new_definition
 `doomsday_date y m =
    if m = 1 then (if leap_year y then 4 else 3)
    else if m = 2 then (if leap_year y then 29 else 28)
    else if m = 3 then 7
    else if m = 4 then 4
    else if m = 5 then 9
    else if m = 6 then 6
    else if m = 7 then 11
    else if m = 8 then 8
    else if m = 9 then 5
    else if m = 10 then 10
    else if m = 11 then 7
    else 12`;;

(* ------------------------------------------------------------------------- *)
(* Century anchor: the doomsday for the first year of each century           *)
(* ------------------------------------------------------------------------- *)

let century_anchor = new_definition
 `century_anchor c = (5 * (c MOD 4) + 2) MOD 7`;;

(* ------------------------------------------------------------------------- *)
(* The Doomsday algorithm: computes the day of the week for the doomsday     *)
(* of any year.                                                              *)
(* ------------------------------------------------------------------------- *)

let doomsday = new_definition
 `doomsday y =
    (century_anchor (y DIV 100) + y MOD 100 + (y MOD 100) DIV 4) MOD 7`;;

(* ========================================================================= *)
(* Part 4: Key lemmas and main correctness proof                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* All doomsday dates are valid                                              *)
(* ------------------------------------------------------------------------- *)

let VALID_DOOMSDAY = prove
 (`!y m. 1 <= m /\ m <= 12 ==> valid_date(y, m, doomsday_date y m)`,
  MONTH_CASES_TAC THEN
  REWRITE_TAC[valid_date; doomsday_date; days_in_month] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helper: equal MOD propagates through addition                             *)
(* ------------------------------------------------------------------------- *)

let MOD_ADD_EQ_COMPAT = prove
 (`!a b c n. a MOD n = b MOD n ==> (c + a) MOD n = (c + b) MOD n`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reference doomsday: the day-of-week value computed from cumulative_days   *)
(* ------------------------------------------------------------------------- *)

let year_doomsday = new_definition
 `year_doomsday y = (cumulative_days y + (if leap_year y then 2 else 1)) MOD 7`;;

(* year_doomsday equals day_of_week of any doomsday date                     *)
let YEAR_DOOMSDAY_EQ_DOW = prove
 (`!y m. 1 <= m /\ m <= 12 ==>
         day_of_week y m (doomsday_date y m) = year_doomsday y`,
  MONTH_CASES_TAC THEN
  REWRITE_TAC[day_of_week; day_number; year_doomsday; day_of_year] THEN
  REWRITE_TAC[cumdays_before; doomsday_date] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Corollary: all doomsday dates in a year fall on the same weekday          *)
(* ------------------------------------------------------------------------- *)

let DOOMSDAY_SAME_WEEKDAY = prove
 (`!y m1 m2. 1 <= m1 /\ m1 <= 12 /\ 1 <= m2 /\ m2 <= 12 ==>
             day_of_week y m1 (doomsday_date y m1) =
             day_of_week y m2 (doomsday_date y m2)`,
  MESON_TAC[YEAR_DOOMSDAY_EQ_DOW]);;

(* ========================================================================= *)
(* Part 5: Main correctness theorem -- year_doomsday y = doomsday y          *)
(* ========================================================================= *)

(* The proof strategy: decompose y = 100*c + t where t < 100.                *)
(* Show doomsday and year_doomsday satisfy the same recurrence within a      *)
(* century, then verify agreement at century boundaries using 400-year       *)
(* periodicity.                                                              *)

(* ------------------------------------------------------------------------- *)
(* Year-to-year step for year_doomsday (mod 7 shift)                         *)
(* ------------------------------------------------------------------------- *)

let CUMULATIVE_DAYS_SUC = prove
 (`!y. cumulative_days (SUC y) = cumulative_days y + days_in_year y`,
  REWRITE_TAC[cumulative_days]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: year_doomsday y = doomsday y                            *)
(*                                                                           *)
(* We prove this by strong induction on y, verifying base cases and          *)
(* showing the formula is preserved across year boundaries.                  *)
(* ------------------------------------------------------------------------- *)

(* First, prove it for years 0-399 computationally.                          *)
(* We do this by proving the formula for each year in a 400-year block       *)
(* matches the year_doomsday value.                                          *)

(* Key lemma: leap year structure within a century *)
(* For years 100*c + t where 0 < t < 100: leap_year iff 4 | t *)
let LEAP_YEAR_IN_CENTURY = prove
 (`!c t. 0 < t /\ t < 100 ==> (leap_year (100 * c + t) <=> t MOD 4 = 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEAP_YEAR_MOD] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; LE_1; MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE `100 * c = 4 * (25 * c)`; MOD_MULT_ADD] THEN
  REWRITE_TAC[MULT_ASSOC; ARITH; TAUT `(p \/ q <=> p) <=> q ==> p`] THEN
  REWRITE_TAC[GSYM DIVIDES_MOD] THEN MATCH_MP_TAC(NUMBER_RULE
   `f divides fh /\ f divides h ==> fh divides h * c + t ==> f divides t`) THEN
  REWRITE_TAC[DIVIDES_MOD] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Recurrence for year_doomsday                                              *)
(* ------------------------------------------------------------------------- *)

let YEAR_DOOMSDAY_STEP = prove
 (`!y. year_doomsday(SUC y) =
       (year_doomsday y + (if leap_year(SUC y) then 2 else 1)) MOD 7`,
  GEN_TAC THEN
  REWRITE_TAC[year_doomsday; CUMULATIVE_DAYS_SUC; days_in_year] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REPEAT(MATCH_MP_TAC MOD_ADD_EQ_COMPAT) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Within-century step for the doomsday formula                              *)
(* For 0 < t < 100: doomsday increments by the same leap offset              *)
(* ------------------------------------------------------------------------- *)

let DOOMSDAY_STEP = prove
 (`!c t. t < 99 ==>
         doomsday(100 * c + SUC t) =
         (doomsday(100 * c + t) + (if SUC t MOD 4 = 0 then 2 else 1)) MOD 7`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[doomsday; century_anchor] THEN
  SUBGOAL_THEN `SUC t < 100 /\ t < 100` STRIP_ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `~(100 = 0)`;
               DIV_LT; MOD_LT; ADD_CLAUSES] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Within a century: if the base case matches, the entire century matches    *)
(* ------------------------------------------------------------------------- *)

let WITHIN_CENTURY = prove
 (`!c. year_doomsday(100 * c) = doomsday(100 * c) ==>
       !t. t < 100 ==> year_doomsday(100 * c + t) = doomsday(100 * c + t)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
   DISCH_TAC THEN
   SUBGOAL_THEN `year_doomsday(100 * c + t) = doomsday(100 * c + t)`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `100 * c + SUC t = SUC(100 * c + t)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[YEAR_DOOMSDAY_STEP] THEN
   SUBGOAL_THEN `SUC(100 * c + t) = 100 * c + SUC t` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `t < 99` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[DOOMSDAY_STEP] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   MP_TAC(SPECL [`c:num`; `SUC t`] LEAP_YEAR_IN_CENTURY) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Century base cases: computed iteratively using the recurrence             *)
(* ------------------------------------------------------------------------- *)

let YEAR_DOOMSDAY_0 = prove
 (`year_doomsday 0 = 2`,
  REWRITE_TAC[year_doomsday; cumulative_days; LEAP_YEAR_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let DOOMSDAY_0 = prove
 (`doomsday 0 = 2`,
  REWRITE_TAC[doomsday; century_anchor] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Iterative computation of year_doomsday at century boundaries *)
let compute_year_doomsday n =
  let rec go k th =
    if k >= n then th
    else
      let k_tm = mk_small_numeral k in
      let step_th = SPEC k_tm YEAR_DOOMSDAY_STEP in
      let step_th' = CONV_RULE(
        LAND_CONV(RAND_CONV NUM_SUC_CONV) THENC
        RAND_CONV(
          ONCE_DEPTH_CONV NUM_SUC_CONV THENC
          REWRITE_CONV[th; LEAP_YEAR_MOD] THENC
          NUM_REDUCE_CONV)) step_th in
      go (k+1) step_th'
  in go 0 YEAR_DOOMSDAY_0;;

let YEAR_DOOMSDAY_100 = compute_year_doomsday 100;;
let YEAR_DOOMSDAY_200 = compute_year_doomsday 200;;
let YEAR_DOOMSDAY_300 = compute_year_doomsday 300;;
let YEAR_DOOMSDAY_400 = compute_year_doomsday 400;;

(* Doomsday algorithm values at century boundaries *)
let DOOMSDAY_100 = prove(`doomsday 100 = 0`,
  REWRITE_TAC[doomsday; century_anchor] THEN CONV_TAC NUM_REDUCE_CONV);;
let DOOMSDAY_200 = prove(`doomsday 200 = 5`,
  REWRITE_TAC[doomsday; century_anchor] THEN CONV_TAC NUM_REDUCE_CONV);;
let DOOMSDAY_300 = prove(`doomsday 300 = 3`,
  REWRITE_TAC[doomsday; century_anchor] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* 400-year periodicity for both doomsday and year_doomsday                  *)
(* ------------------------------------------------------------------------- *)

let LEAP_YEAR_400_PERIOD = prove
 (`!y. leap_year(y + 400) <=> leap_year y`,
  GEN_TAC THEN REWRITE_TAC[LEAP_YEAR_MOD] THEN
  REWRITE_TAC[ARITH_RULE `y + 400 = y + 4 * 100`; MOD_MULT_ADD] THEN
  REWRITE_TAC[ARITH_RULE `4 * 100 = 400 * 1`; MOD_MULT_ADD]);;

let DOOMSDAY_400_PERIOD = prove
 (`!y. doomsday(y + 400) = doomsday y`,
  GEN_TAC THEN REWRITE_TAC[doomsday; century_anchor] THEN
  REWRITE_TAC[ARITH_RULE `y + 400 = 100 * 4 + y`; MOD_MULT_ADD] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(100 = 0)`] THEN
  REWRITE_TAC[ARITH_RULE `4 + y = 4 * 1 + y`; MOD_MULT_ADD]);;

let YEAR_DOOMSDAY_400_PERIOD = prove
 (`!y. year_doomsday(y + 400) = year_doomsday y`,
  INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES; YEAR_DOOMSDAY_400; YEAR_DOOMSDAY_0];
   REWRITE_TAC[ARITH_RULE `SUC y + 400 = SUC(y + 400)`] THEN
   REWRITE_TAC[YEAR_DOOMSDAY_STEP] THEN
   SUBGOAL_THEN `leap_year(SUC(y + 400)) <=> leap_year(SUC y)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC(y + 400) = SUC y + 400`] THEN
    REWRITE_TAC[LEAP_YEAR_400_PERIOD];
    ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Century base case for all c: year_doomsday(100*c) = doomsday(100*c)       *)
(* ------------------------------------------------------------------------- *)

let CENTURY_BASE_ALL = prove
 (`!c. year_doomsday(100 * c) = doomsday(100 * c)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`c:num`; `4`] DIVISION) THEN ANTS_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = c DIV 4` THEN ABBREV_TAC `r = c MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `100 * c = 400 * q + 100 * r` SUBST1_TAC THENL
  [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r < 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`r:num`,`r:num`) THEN SPEC_TAC(`q:num`, `q:num`) THEN 
  INDUCT_TAC THENL
  [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[YEAR_DOOMSDAY_0; YEAR_DOOMSDAY_100; YEAR_DOOMSDAY_200;
                YEAR_DOOMSDAY_300; DOOMSDAY_0; DOOMSDAY_100; DOOMSDAY_200;
                DOOMSDAY_300];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[ARITH_RULE `400 * SUC q + x = (400 * q + x) + 400`] THEN
   REWRITE_TAC[YEAR_DOOMSDAY_400_PERIOD; DOOMSDAY_400_PERIOD] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* THE MAIN THEOREM: year_doomsday y = doomsday y for all y                  *)
(* ========================================================================= *)

let YEAR_DOOMSDAY_EQ_DOOMSDAY = prove
 (`!y. year_doomsday y = doomsday y`,
  GEN_TAC THEN
  MP_TAC(SPECL [`y:num`; `100`] DIVISION) THEN ANTS_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = y DIV 100` THEN ABBREV_TAC `t = y MOD 100` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `y = 100 * c + t` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `c:num` WITHIN_CENTURY) THEN
  DISCH_THEN(fun th -> MP_TAC(MP th (SPEC `c:num` CENTURY_BASE_ALL))) THEN
  DISCH_THEN(MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* DOOMSDAY_CORRECT: The Doomsday algorithm gives the correct day of week    *)
(* for the doomsday date in every month of every year.                       *)
(* ========================================================================= *)

let DOOMSDAY_CORRECT = prove
 (`!y m. 1 <= m /\ m <= 12 ==>
         day_of_week y m (doomsday_date y m) = doomsday y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`y:num`; `m:num`] YEAR_DOOMSDAY_EQ_DOW) THEN
  ASM_REWRITE_TAC[YEAR_DOOMSDAY_EQ_DOOMSDAY]);;

(* ========================================================================= *)
(* Part 6: Corollaries and applications                                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Day-of-week shift: adding days shifts the weekday                         *)
(* ------------------------------------------------------------------------- *)

let DOW_SHIFT = prove
 (`!y m d1 d2. day_of_week y m (d1 + d2) = (day_of_week y m d1 + d2) MOD 7`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[day_of_week; day_number; day_of_year] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Day-of-week from doomsday: for any date on or after the doomsday date     *)
(* ------------------------------------------------------------------------- *)

let DOW_FROM_DOOMSDAY = prove
 (`!y m d. 1 <= m /\ m <= 12 /\ doomsday_date y m <= d ==>
           day_of_week y m d = (doomsday y + d - doomsday_date y m) MOD 7`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d = doomsday_date y m + (d - doomsday_date y m)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DOW_SHIFT] THEN
  ASM_SIMP_TAC[DOOMSDAY_CORRECT] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cumulative days 400-year periodicity (mod 7)                              *)
(* ------------------------------------------------------------------------- *)

let compute_cumdays n =
  let rec go k th =
    if k >= n then th
    else
      let k_tm = mk_small_numeral k in
      let step_th = SPEC k_tm CUMULATIVE_DAYS_SUC in
      let step_th' = CONV_RULE(
        LAND_CONV(RAND_CONV NUM_SUC_CONV) THENC
        RAND_CONV(
          ONCE_DEPTH_CONV NUM_SUC_CONV THENC
          REWRITE_CONV[th; days_in_year; LEAP_YEAR_MOD] THENC
          NUM_REDUCE_CONV)) step_th in
      go (k+1) step_th'
  in go 0 (CONJUNCT1 cumulative_days);;

let CUMDAYS_400 = compute_cumdays 400;;

let CUMULATIVE_DAYS_400_MOD7 = prove
 (`!y. cumulative_days(y + 400) MOD 7 = cumulative_days y MOD 7`,
  INDUCT_TAC THENL
  [REWRITE_TAC[ADD_CLAUSES; CUMDAYS_400; cumulative_days] THEN
   CONV_TAC NUM_REDUCE_CONV;
   REWRITE_TAC[ARITH_RULE `SUC y + 400 = SUC(y + 400)`] THEN
   REWRITE_TAC[CUMULATIVE_DAYS_SUC; days_in_year] THEN
   SUBGOAL_THEN `leap_year(y + 400) <=> leap_year y`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[LEAP_YEAR_400_PERIOD]; ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN
   CONV_TAC MOD_DOWN_CONV THEN
   ONCE_REWRITE_TAC[ADD_SYM] THEN
   MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
   ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 400-year periodicity for the full day_of_week function                    *)
(* ------------------------------------------------------------------------- *)

let DAY_OF_WEEK_400_PERIOD = prove
 (`!y m d. day_of_week (y + 400) m d = day_of_week y m d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[day_of_week; day_number; day_of_year] THEN
  SUBGOAL_THEN `cumdays_before (y + 400) m = cumdays_before y m`
  SUBST1_TAC THENL
   [REWRITE_TAC[cumdays_before; LEAP_YEAR_400_PERIOD]; ALL_TAC] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
  REWRITE_TAC[CUMULATIVE_DAYS_400_MOD7]);;

(* ========================================================================= *)
(* Part 7: Full doomsday algorithm for any date                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Day-of-week is periodic with period 7 in the day argument                 *)
(* ------------------------------------------------------------------------- *)

let DOW_PERIOD = prove
 (`!y m d k. day_of_week y m (d + 7 * k) = day_of_week y m d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[day_of_week; day_number; day_of_year] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
  ONCE_REWRITE_TAC[ARITH_RULE
    `c + b + d + 7 * k = 7 * k + (c + b + d)`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Doomsday date bounds: all doomsday dates are between 1 and 29             *)
(* ------------------------------------------------------------------------- *)

let DOOMSDAY_DATE_BOUND = prove
 (`!y m. 1 <= m /\ m <= 12 ==>
         1 <= doomsday_date y m /\ doomsday_date y m <= 29`,
  MONTH_CASES_TAC THEN REWRITE_TAC[doomsday_date] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The full doomsday algorithm: computes day of week for any valid date.     *)
(*                                                                           *)
(* Conway's mental process:                                                  *)
(*   1. Compute the year's doomsday from century anchor + year offset        *)
(*   2. Look up the doomsday date for the month (4/4, 6/6, 8/8, etc.)        *)
(*   3. Count the offset from the doomsday date to the target day            *)
(*   4. Add that offset (mod 7) to the year's doomsday                       *)
(*                                                                           *)
(* The +35 (= 5*7) is a safety offset to avoid natural number underflow      *)
(* when the target day is before the doomsday date in the month.             *)
(* ------------------------------------------------------------------------- *)

let doomsday_algorithm = new_definition
 `doomsday_algorithm y m d =
    (doomsday y + d + 35 - doomsday_date y m) MOD 7`;;

(* ------------------------------------------------------------------------- *)
(* THE FULL CORRECTNESS THEOREM: the doomsday algorithm computes the         *)
(* correct day of the week for every valid Gregorian date.                   *)
(* ------------------------------------------------------------------------- *)

let DOOMSDAY_ALGORITHM_CORRECT = prove
 (`!y m d. valid_date(y,m,d) ==>
           doomsday_algorithm y m d = day_of_week y m d`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[doomsday_algorithm] THEN
  SUBGOAL_THEN `day_of_week y m d = day_of_week y m (d + 35)` SUBST1_TAC THENL
  [ONCE_REWRITE_TAC[ARITH_RULE `d + 35 = d + 7 * 5`] THEN
   REWRITE_TAC[DOW_PERIOD]; ALL_TAC] THEN
  MP_TAC(SPECL [`y:num`; `m:num`; `d + 35`] DOW_FROM_DOOMSDAY) THEN
  ANTS_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[valid_date]) THEN
   MP_TAC(SPECL [`y:num`; `m:num`] DOOMSDAY_DATE_BOUND) THEN
   ASM_ARITH_TAC;
   DISCH_THEN SUBST1_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   MP_TAC(SPECL [`y:num`; `m:num`] DOOMSDAY_DATE_BOUND) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[valid_date]) THEN
   ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Part 8: Enumerated day type with named output and evaluation              *)
(* ========================================================================= *)

let day_INDUCT,day_RECURSION = define_type
  "day = Sunday | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday";;

(* Conway's names:
 * Noneday Oneday Twosday Treblesday Foursday Fiveday Sixturday
 *)

let dayname = new_definition
 `dayname n = if n = 0 then Sunday
              else if n = 1 then Monday
              else if n = 2 then Tuesday
              else if n = 3 then Wednesday
              else if n = 4 then Thursday
              else if n = 5 then Friday
              else Saturday`;;

let doomsday_day = new_definition
 `doomsday_day y m d = dayname(doomsday_algorithm y m d)`;;

let DOOMSDAY_DAY_CORRECT = prove
 (`!y m d. valid_date(y,m,d)
           ==> doomsday_day y m d = dayname(day_of_week y m d)`,
  REWRITE_TAC[doomsday_day] THEN
  MESON_TAC[DOOMSDAY_ALGORITHM_CORRECT]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation conversion for doomsday_day.                                   *)
(* Usage: DOOMSDAY_DAY_CONV `doomsday_day 1966 12 14`                        *)
(*   |- doomsday_day 1966 12 14 = Wednesday                                  *)
(* ------------------------------------------------------------------------- *)

let DOOMSDAY_DAY_CONV =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND:bool->num->num->num` (Some 1);
  Compute.set_skip cs `COND:bool->day->day->day` (Some 1);
  num_compute_add_convs cs;
  Compute.add_thms [doomsday_day; doomsday_algorithm; doomsday; century_anchor;
                    doomsday_date; LEAP_YEAR_MOD; dayname] cs;
  Compute.WEAK_CBV_CONV cs;;

(* ------------------------------------------------------------------------- *)
(* Famous dates with named days                                              *)
(* ------------------------------------------------------------------------- *)

let DAY_1776_7_4 = prove
 (`doomsday_day 1776 7 4 = Thursday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;

let DAY_1969_7_20 = prove
 (`doomsday_day 1969 7 20 = Sunday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;

let DAY_1989_11_9 = prove
 (`doomsday_day 1989 11 9 = Thursday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;

let DAY_2000_1_1 = prove
 (`doomsday_day 2000 1 1 = Saturday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;

let DAY_2026_3_26 = prove
 (`doomsday_day 2026 3 26 = Thursday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;

let DAY_1966_12_14 = prove
 (`doomsday_day 1966 12 14 = Wednesday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;

let DAY_2005_03_25 = prove
 (`doomsday_day 2005 03 25 = Friday`,
  CONV_TAC DOOMSDAY_DAY_CONV);;
