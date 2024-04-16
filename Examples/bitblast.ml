(* ========================================================================= *)
(* Examples of proving properties of machine words via bit-blasting.         *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Wrapper that also expands bounded quantifiers first.                      *)
(* ------------------------------------------------------------------------- *)

let BITBLAST tm =
  let th = (ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) tm in
  EQ_MP (SYM th) (BITBLAST_RULE (rand(concl th)));;

(* ------------------------------------------------------------------------- *)
(* For more data, also use the SAT interface and compare with BDD default.   *)
(* ------------------------------------------------------------------------- *)

(****

needs "Minisat/make.ml";;

let BITBLAST_BDD tm =
  let th = (ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) tm in
  EQ_MP (SYM th) (BITBLAST_RULE (rand(concl th)))
and BITBLAST_MINISAT tm =
  let th = (ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) tm in
  let th' = prove(rand(concl th),BITBLAST_THEN (CONV_TAC o K SAT_PROVE)) in
  EQ_MP (SYM th) th'
and BITBLAST_ZCHAFF tm =
  let th = (ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) tm in
  let th' = prove(rand(concl th),BITBLAST_THEN (CONV_TAC o K ZSAT_PROVE)) in
  EQ_MP (SYM th) th';;

let BITBLAST tm =
  let th1 = (*** Already reports time ***) BITBLAST_BDD tm in
  let th2 = time BITBLAST_MINISAT tm in
  let th3 = time BITBLAST_ZCHAFF tm in
  if concl th1 = tm && concl th2 = tm && concl th3 = tm
  then th1 else failwith "BITBLAST: Sanity check failure";;

*****)

(* ------------------------------------------------------------------------- *)
(* Some easy examples.                                                       *)
(* ------------------------------------------------------------------------- *)

BITBLAST `word_xor x y:int64  = word_sub (word_or x y) (word_and x y)`;;

BITBLAST
  `word_add x y:int64 = word_sub (word_shl (word_or x y) 1) (word_xor x y)`;;

BITBLAST
  `word_and (word_not x) (word_sub x (word 1)):int64 =
   word_not (word_or x (word_neg x))`;;

BITBLAST
 `word_not (word_or x (word_neg x)):int64 =
  word_sub (word_and x (word_neg x)) (word 1)`;;

(* ------------------------------------------------------------------------- *)
(* Ways of getting a carry flag post-hoc.                                    *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x y:int64.
    val(word_add x y) < val x <=> ~(val(word_add x y) = val(x) + val(y))`;;

BITBLAST
 `!x y:int64.
    val(word_add x y) >= val y <=> val(word_add x y) = val(x) + val(y)`;;

(* ------------------------------------------------------------------------- *)
(* Sign extension from Hacker's Delight 2.5                                  *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `word_sub (word_xor ((word_zx:int32->int64) x) (word 0x80000000))
           (word 0x80000000) =
  word_sx x`;;

(* ------------------------------------------------------------------------- *)
(* Sign swaps, from http://graphics.stanford.edu/~seander/bithacks.html      *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `let m:int64 = word_neg(word(bitval b)) in
  word_sub (word_xor x m) m = word_xor (word_add x m) m`;;

(* ------------------------------------------------------------------------- *)
(* Getting a mask or C condition for a zero test.                            *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x:int64.
     (word_ushr (word_or (word_neg x) x) 63 = word 1 <=> ~(x = word 0)) /\
     (word_ushr (word_or (word_neg x) x) 63 = word 0 <=> x = word 0)`;;

BITBLAST
 `!x:int64.
     (word_ishr (word_or (word_neg x) x) 63 = word 0xFFFFFFFFFFFFFFFF <=>
      ~(x = word 0)) /\
     (word_ishr (word_or (word_neg x) x) 63 = word 0 <=> x = word 0)`;;

(* ------------------------------------------------------------------------- *)
(* Computing popcount.                                                       *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x:int64.
   let x2  = word_sub x (word_ushr (word_and x (word 0xAAAAAAAAAAAAAAAA)) 1) in
   let x4  = word_add (word_and x2 (word 0x3333333333333333))
                      (word_ushr (word_and x2 (word 0xCCCCCCCCCCCCCCCC)) 2) in
   let x8  = word_and (word_add x4 (word_ushr x4 4))
                      (word 0x0F0F0F0F0F0F0F0F) in
   let x64 = word_mul x8 (word 0x101010101010101) in
   let y = word_ushr x64 56 in
   y = word(word_popcount x)`;;

BITBLAST
 `!x:15 word.
        let u:int64 = word_mul (word_zx x) (word 0x0002000400080010) in
        let v = word_and u (word 0x1111111111111111) in
        let w = word_mul v (word 0x1111111111111111) in
        let y = word_ushr w 60 in
        y = word(word_popcount x)`;;

(* ------------------------------------------------------------------------- *)
(* Primality checking.                                                       *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x:nybble y:nybble. val x * val y = 13 ==> val x = 1 \/ val y = 1`;;

BITBLAST
 `!x:byte y:byte. val x * val y = 241 ==> val x = 1 \/ val y = 1`;;

(* ------------------------------------------------------------------------- *)
(* Parity. See Hacker's Delight 5-2.                                         *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x:int64.
        let x1 = word_xor x (word_ushr x 1) in
        let x2 = word_xor x1 (word_ushr x1 2) in
        let x4 = word_xor x2 (word_ushr x2 4) in
        let x8 = word_xor x4 (word_ushr x4 8) in
        let x16 = word_xor x8 (word_ushr x8 16) in
        let x32 = word_xor x16 (word_ushr x16 32) in
        let y = word_and x32 (word 1) in
        y = word(bitval(word_oddparity x))`;;

BITBLAST
 `!x:int32.
        let x1 = word_xor x (word_ushr x 1) in
        let x2 = word_and (word_xor x1 (word_ushr x1 2)) (word 0x11111111) in
        let x4 = word_mul x2 (word 0x11111111) in
        let y = word_and (word_ushr x4 28) (word 1) in
        y = word(bitval(word_oddparity x))`;;

BITBLAST
 `!x:int32.
        let x1 = word_xor x (word_ushr x 1) in
        let x2 = word_and (word_xor x1 (word_ushr x1 2)) (word 0x11111111) in
        let x4 = word_mul x2 (word 0x88888888) in
        let y = word_ushr x4 31 in
        y = word(bitval(word_oddparity x))`;;

(* ------------------------------------------------------------------------- *)
(* Non-overflowing average                                                   *)
(* ------------------------------------------------------------------------- *)

BITBLAST
  `!x y:int64.
        word_ushr (word_add (word_zx x) (word_zx y)) 1 :65 word =
        word_zx (word_add (word_and x y) (word_ushr (word_xor x y) 1))`;;

BITBLAST
  `!x y:int64.
        word_ushr (word_add (word_zx x) (word_zx y)) 1 :int128 =
        word_zx (word_add (word_and x y) (word_ushr (word_xor x y) 1))`;;

BITBLAST
  `!x y:int64.
        word_ushr (word_add (word_zx x) (word_zx y)) 1 :65 word =
        word_zx (word_add (word_add (word_ushr x 1) (word_ushr y 1))
                          (word_and (word_and x y) (word 1)))`;;

(* ------------------------------------------------------------------------- *)
(* Isolating lowest 0 bit ("Matters Computational", 1.3.1).                  *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x:int64. let x' = word_not x in
            word_and x' (word_neg x') =
            word_and (word_xor x (word_add x (word 1))) (word_not x)`;;

(* ------------------------------------------------------------------------- *)
(* Gray codes are injective.                                                 *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `let gray = \x:int64. word_xor x (word_ushr x 1) in
        gray x = gray y ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Gray code parity is the same as the LSB of the input.                     *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `let gray = \x:int64. word_xor x (word_ushr x 1) in
        word(bitval(word_oddparity(gray x))):byte =
        word(bitval(bit 0 x))`;;

(* ------------------------------------------------------------------------- *)
(* Recognizing powers of 2 (or zero).                                        *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `word_and x (word_sub x (word 1)):int64 = word 0 <=>
  word_and (word(word_popcount x):byte) (word_not(word 1)) = word 0`;;

BITBLAST
 `word_and x (word_sub x (word 1)):int64 = word 0 <=>
  word_popcount x = 0 \/ word_popcount x = 1`;;

(* ------------------------------------------------------------------------- *)
(* Adjacent Gray codes differ in one bit (several formulations).             *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `let gray = \x:int64. word_xor x (word_ushr x 1)
  and pow2orzero = \x:int64. word_and x (word_sub x (word 1)) = word 0 in
  pow2orzero(word_xor (gray x) (gray (word_add x (word 1))))`;;

BITBLAST
 `let gray = \x:int64. word_xor x (word_ushr x 1)
  and pow2 = \x:int64. word_and x (word_sub x (word 1)) = word 0 /\
                       ~(x = word 0) in
  pow2(word_xor (gray x) (gray (word_add x (word 1))))`;;

BITBLAST
 `let gray = \x:int64. word_xor x (word_ushr x 1) in
  word(word_popcount(word_xor (gray x) (gray (word_add x (word 1))))):byte =
  word 1`;;

(* ------------------------------------------------------------------------- *)
(* Iterated application of Gray code.                                        *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `let gray = \x:int64. word_xor x (word_ushr x 1) in
  gray(gray x) = word_xor x (word_ushr x 2)`;;

BITBLAST
 `let gray = \x:byte. word_xor x (word_ushr x 1) in
  gray(gray(gray(gray(gray(gray(gray(gray x))))))) = x`;;

(* ------------------------------------------------------------------------- *)
(* Something involving the more complicated constructs.                      *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x y:int64. word_clz(word_or x y) <= word_clz x`;;

BITBLAST
 `!x:int32. word_popcount(word_add x (word 1)) = 1
            ==> word_ctz x = 0 \/ word_ctz x = 32`;;

BITBLAST
 `!x:int32. ~(x = word 0)
            ==> word_popcount(word_sub x (word 1)) + 1 =
                word_popcount x + word_ctz x`;;

BITBLAST
 `!x:int32. word_clz x + word_popcount x + word_ctz x = 32 <=>
           ~(x = word 0) /\
           word_and (word_add (word_or x (word_sub x (word 1))) (word 1)) x =
           word 0`;;

BITBLAST
 `!x:int32. word_popcount x = 0 \/ word_popcount x = 1 <=>
            word_and x (word_sub x (word 1)) = word 0`;;

BITBLAST
 `!x:int32. word_popcount x = 1 <=>
            word_or (word_not(word_ishr (word_or x (word_neg x)) 31))
                    (word_and x (word_sub x (word 1))) =
            word 0`;;

(* ------------------------------------------------------------------------- *)
(* Alternative emulation for ctz in terms of popcount.                       *)
(* ------------------------------------------------------------------------- *)

(***
 http://aggregate.org/MAGIC/#SIMD%20Within%20A%20Register%20(SWAR)%20Operations
 ***)

BITBLAST
 `!x:int32. word(word_ctz x):byte =
            word(word_popcount(word_sub (word_and x (word_neg x)) (word 1)))`;;

BITBLAST
 `!x:int64. word(word_ctz x):byte =
            word(word_popcount(word_sub (word_and x (word_neg x)) (word 1)))`;;

(* ------------------------------------------------------------------------- *)
(* Comparing leading zero counts (Hacker's Delight again).                   *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x y:int64.
        word_clz x = word_clz y <=> val(word_xor x y) <= val(word_and x y)`;;

BITBLAST
 `!x y:int64.
        word_clz x < word_clz y <=> val(word_and x (word_not y)) > val y`;;

BITBLAST
 `!x y:int64.
        word_clz x <= word_clz y <=> val(word_and (word_not x) y) <= val x`;;

(* ------------------------------------------------------------------------- *)
(* Basic SWAR byte operations. Somewhat well-known methods, e.g.             *)
(* https://www.chessprogramming.org/SIMD_and_SWAR_Techniques                 *)
(* ------------------------------------------------------------------------- *)

(*** Addition ***)

BITBLAST
 `!x y:int64.
    let h = word 0x8080808080808080
    and l = word 0x0101010101010101 in
    let s = word_add (word_and x (word_not h)) (word_and y (word_not h))
    and t = word_and (word_xor x y) h in
    let z = word_xor s t in
    !i. i < 8 ==> word_subword z (8*i,8) :byte =
                  word_add (word_subword x (8*i,8)) (word_subword y (8*i,8))`;;

(*** Subtraction ***)

BITBLAST
 `!x y:int64.
    let h = word 0x8080808080808080
    and l = word 0x0101010101010101 in
    let s = word_sub (word_or x h) (word_and y (word_not h))
    and t = word_and (word_xor x (word_not y)) h in
    let z = word_xor s t in
    !i. i < 8 ==> word_subword z (8*i,8) :byte =
                  word_sub (word_subword x (8*i,8)) (word_subword y (8*i,8))`;;

(*** Average ***)

BITBLAST
 `!x y:int64.
    let l = word 0x0101010101010101 in
    let z = word_add (word_and x y)
                     (word_ushr (word_and (word_xor x y) (word_not l)) 1) in
    !i. i < 8
        ==> word_zx (word_subword z (8*i,8) :byte):9 word =
            word_ushr (word_add (word_zx (word_subword x (8*i,8) :byte))
                                (word_zx (word_subword y (8*i,8) :byte))) 1`;;

(* ------------------------------------------------------------------------- *)
(* SWAR comparison.                                                          *)
(* https://tldp.org/HOWTO/Parallel-Processing-HOWTO-4.html                   *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x y:int64.
    let m = word 0x7F7F7F7F7F7F7F7F in
    let d = word_xor x y in
    let w = word_add (word_and d m) m in
    let z = word_not (word_or (word_or d m) w) in
    !i. i < 8
        ==> (word_subword z (8*i,8) :byte = word 0 <=>
             ~(word_subword x (8*i,8):byte = word_subword y (8*i,8))) /\
            (word_subword z (8*i,8) :byte = word 0x80 <=>
             word_subword x (8*i,8):byte = word_subword y (8*i,8))`;;

BITBLAST
 `!x y:int64.
    let h = word 0x8080808080808080 in
    let d = word_xor x y in
    let w = word_and (word_sub (word_or (word_ushr d 1) h) d) h in
    let z = word_sub (word_shl w 1) (word_ushr w 7) in
    !i. i < 8
        ==> (word_subword z (8*i,8) :byte = word 0 <=>
             ~(word_subword x (8*i,8):byte = word_subword y (8*i,8))) /\
            (word_subword z (8*i,8) :byte = word 0xFF <=>
             word_subword x (8*i,8):byte = word_subword y (8*i,8))`;;

BITBLAST
 `!x y:int64.
    let h = word 0x8080808080808080 in
    let m = word_not h in
    let d = word_xor x y in
    let w = word_add (word_and d m) m in
    let z = word_and (word_or w d) h in
   !i. i < 8
        ==> (word_subword z (8*i,8) :byte = word 0 <=>
             word_subword x (8*i,8):byte = word_subword y (8*i,8)) /\
            (word_subword z (8*i,8) :byte = word 0x80 <=>
             ~(word_subword x (8*i,8):byte = word_subword y (8*i,8)))`;;

(* ------------------------------------------------------------------------- *)
(* Alan Mycroft's test for a zero byte (Knuth 7.1.3, formula 90).            *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `let h = word 0x8080808080808080
  and l = word 0x0101010101010101 in
  word_and h (word_and (word_sub x l) (word_not x)):int64 = word 0 <=>
  !i. i < 8
      ==> ~(word_subword x (8*i,8) :byte = word 0)`;;

(* ------------------------------------------------------------------------- *)
(* Validity checking for packed BCD                                          *)
(* https://homepage.divms.uiowa.edu/~jones/bcd/bcd.html                      *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!a:int32.
        let w = word_xor (word_add a (word 0x06666666)) a in
        let z = word_and w (word 0x11111110) in
        ((!i. i < 7
              ==> val(word_subword a (4*i,4):nybble) < 10)
         <=> z = word 0)`;;

(*** A variant including the top digit in the check ***)

BITBLAST
 `!a:int32.
        let a' = word_ushr a 1 in
        let w = word_xor (word_add a' (word 0x33333333)) a' in
        let z = word_and w (word 0x88888888) in
        ((!i. i < 8
              ==> val(word_subword a (4*i,4):nybble) < 10)
         <=> z = word 0)`;;

(* ------------------------------------------------------------------------- *)
(* Modular inverse approximation magic                                       *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!a:5 word.
        let x = word_xor (word_sub a (word_shl a 2)) (word 2) in
        bit 0 a ==> word_mul a x = word_neg(word 1)`;;

BITBLAST
 `!a:4 word.
   let x = word_sub (word_shl (word_and (word_sub (word 1) a) (word 4)) 1) a in
   bit 0 a ==> word_mul a x = word_neg(word 1)`;;

(* ------------------------------------------------------------------------- *)
(* Various ways of counting leading zeros - Hacker's Delight 5-15 etc.       *)
(* ------------------------------------------------------------------------- *)

BITBLAST
 `!x:int64.
        let x1 = word_or x (word_ushr x 1) in
        let x2 = word_or x1 (word_ushr x1 2) in
        let x4 = word_or x2 (word_ushr x2 4) in
        let x8 = word_or x4 (word_ushr x4 8) in
        let x16 = word_or x8 (word_ushr x8 16) in
        let x32 = word_or x16 (word_ushr x16 32) in
        word_popcount(word_not x32) = word_clz x`;;

BITBLAST
 `!x:int64.
        let x1 = word_or x (word_ushr x 32) in
        let x2 = word_or x1 (word_ushr x1 16) in
        let x4 = word_or x2 (word_ushr x2 8) in
        let x8 = word_or x4 (word_ushr x4 4) in
        let x16 = word_or x8 (word_ushr x8 2) in
        let x32 = word_or x16 (word_ushr x16 1) in
        word_popcount(word_not x32) = word_clz x`;;

BITBLAST
  `!x:int64.
   (if x = word 0 then word 64 else
    let n = word 0 in
    let x0,n0 = if val x <= 0x00000000FFFFFFFF
                then word_shl x 32,word_add n (word 32) else x,n in
    let x1,n1 = if val x0 <= 0x0000FFFFFFFFFFFF
                then word_shl x0 16,word_add n0 (word 16) else x0,n0 in
    let x2,n2 = if val x1 <= 0x00FFFFFFFFFFFFFF
                then word_shl x1 8,word_add n1 (word 8) else x1,n1 in
    let x3,n3 = if val x2 <= 0x0FFFFFFFFFFFFFFF
                then word_shl x2 4,word_add n2 (word 4) else x2,n2 in
    let x4,n4 = if val x3 <= 0x3FFFFFFFFFFFFFFF
                then word_shl x3 2,word_add n3 (word 2) else x3,n3 in
    if val x4 <= 0x7FFFFFFFFFFFFFFF then word_add n4 (word 1) else n4):int64 =
   word(word_clz x)`;;

BITBLAST
 `!x:int64.
        let MASK32 = word 0xFFFFFFFF00000000
        and MASK16 = word 0xFFFF0000FFFF0000
        and MASK8 = word 0xFF00FF00FF00FF00
        and MASK4 = word 0xF0F0F0F0F0F0F0F0
        and MASK2 = word 0xCCCCCCCCCCCCCCCC
        and MASK1 = word 0xAAAAAAAAAAAAAAAA in
        (if x = word 0 then 64 else
         (if val(word_and x MASK32) < val(word_and x (word_not MASK32))
          then 32 else 0) +
         (if val(word_and x MASK16) < val(word_and x (word_not MASK16))
          then 16 else 0) +
         (if val(word_and x MASK8) < val(word_and x (word_not MASK8))
          then 8 else 0) +
         (if val(word_and x MASK4) < val(word_and x (word_not MASK4))
          then 4 else 0) +
         (if val(word_and x MASK2) < val(word_and x (word_not MASK2))
          then 2 else 0) +
         (if val(word_and x MASK1) < val(word_and x (word_not MASK1))
          then 1 else 0)) =
    word_clz x`;;
