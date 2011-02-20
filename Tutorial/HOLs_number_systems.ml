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

****)

needs "Examples/cooper.ml";;

COOPER_RULE `ODD n ==> 2 * n DIV 2 < n`;;

COOPER_RULE `!n. n >= 8 ==> ?a b. n = 3 * a + 5 * b`;;

needs "Rqe/make.ml";;

REAL_QELIM_CONV `!x. &0 <= x ==> ?y. y pow 2 = x`;;
