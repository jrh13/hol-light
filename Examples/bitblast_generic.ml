(* ========================================================================= *)
(* Examples of automata-based generic bitblasting                            *)
(* ========================================================================= *)

needs "Library/word_automata.ml";;

(* ------------------------------------------------------------------------- *)
(* Misc examples, many originating in LLVM optimization.                     *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!(z:(N)word) (c:(N)word).
    word_and c (word 1) = word 0
    ==> word_xor (word_and z c) (word_or c (word 1)) =
        word_neg (word_or z (word_not c))`;;

time WORD_AUTO_RULE
 `!(z:(N)word) (c:(N)word).
        word_xor (word_and z c) (word_or c (word 1)) =
        word_neg (word_or z (word_not c)) <=>
        word_and c (word 1) = word 0`;;

time WORD_AUTO_RULE
  `!(z:(N)word) (c:(N)word).
    (word_add (word_xor (word_or z (word_not c)) c) (word 1)) =
    (word_neg (word_and z c))`;;

time WORD_AUTO_RULE
  `!(z:(N)word) (c:(N)word).
    word_add (word_xor (word_and z c) c) (word 1) =
    word_neg (word_or z (word_not c))`;;

time WORD_AUTO_RULE
  `!(x:(N)word) (y:(N)word).
    word_add (word_add x (word 1)) (word_not y) =
    word_sub x y`;;

time WORD_AUTO_RULE
 `!(x:(N) word) (y:(N)word).
    word_add (word_not x) (word_not y) =
    word_sub (word_sub (word 0) (word 2)) (word_add x y)`;;

time WORD_AUTO_RULE
 `!(x:(N)word) (c1:(N)word) (c2:(N)word).
  (c2 = (word_neg c1))
  ==> (word_add (word_or x (c2)) (c1)) = (word_xor (word_or x (c2)) (c2))`;;

time WORD_AUTO_RULE
 `!(x:N word) c1 c2.
    word_and c2 (word_sub c2 (word 1)) = word 0 /\
    word_and c1 (word_sub c2 (word 1)) = word 0 /\
    ~(word_and c1 c2 = word 0)
    ==> word_and (word_add x c1) c2 = word_xor (word_and x c2) c2`;;

time WORD_AUTO_RULE
 `!x:N word.
     word_and (word_not x) (word_sub x (word 1)) =
     word_not (word_or x (word_neg x))`;;

time WORD_AUTO_RULE
 `!x:N word. word_and x (word_not(word 1)) = word 0 <=>
             x = word 0 \/ x = word 1`;;

time WORD_AUTO_RULE
 `word_xor x y:S word  = word_sub (word_or x y) (word_and x y)`;;

time WORD_AUTO_RULE
 `word_add x y:M word = word_sub (word_shl (word_or x y) 1) (word_xor x y)`;;

time WORD_AUTO_RULE
 `!x:R word. word_and x (word_sub x (word 1)) = word 0 /\
              word_and x (word_not(word 1)) = word 0
              <=> x = word 0 \/ x = word 1`;;

(* ------------------------------------------------------------------------- *)
(* Characterizing the top bit                                                *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
  `!b x:N word. ~(b = word 0) /\ word_shl b 1 = word 0
                ==> (~(x = word 0) <=>
                     word_and b (word_or x (word_neg x)) = b)`;;

time WORD_AUTO_RULE
  `!b x:N word. ~(b = word 0) /\ word_shl b 1 = word 0
                ==> (x = word 0 <=>
                     word_and b (word_or x (word_neg x)) = word 0)`;;

time WORD_AUTO_RULE
 `!b c:N word. ~(b = word 0) /\ word_shl b 1 = word 0 /\
               word_add c (word 1) = word_not c /\ ~(c = word_not(word 0))
               ==> b = word_not c`;;

(* ------------------------------------------------------------------------- *)
(* Sign swaps.                                                               *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!m x:N word. m = word_neg(word_and b (word 1))
               ==> word_sub (word_xor x m) m = word_xor (word_add x m) m`;;

(* ------------------------------------------------------------------------- *)
(* Trivial example with multiple shifts.                                     *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!x:N word. word_and (word 3) (word_shl x 2) = word 0`;;

(* ------------------------------------------------------------------------- *)
(* Trivial example with constant multiplication.                             *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
  `!x:N word. word_and (word 3) (word_mul (word 5) x) =
              word_and x (word 3)`;;

(* ------------------------------------------------------------------------- *)
(* Simple examples with right shifts.                                        *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!x y:R word. word_xor x (word_ushr x 1) = word_xor y (word_ushr y 1) <=>
               x = y`;;

time WORD_AUTO_RULE
 `!x:M word. word_and (word_xor (word_add (word_ushr x 2) (word_ushr x 2))
                                (word_ushr x 1))
                      (word_not(word 1)) = word 0`;;

(* ------------------------------------------------------------------------- *)
(* Two versions of non-overflowing average                                   *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!x y:N word. word_add (word_and x y) (word_ushr (word_xor x y) 1) =
               word_add (word_add (word_ushr x 1) (word_ushr y 1))
                        (word_and (word 1) (word_and x y))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial things with orderings.                                            *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!x y z:N word.
        word_ule x y /\ word_ule y z ==> word_ule x z`;;

time WORD_AUTO_RULE
 `!x y z:N word.
        word_ule x y /\ word_ult y z ==> word_ugt z x`;;

time WORD_AUTO_RULE
 `!x y z:N word.
        word_ile x y /\ word_ile y z ==> word_ile x z`;;

time WORD_AUTO_RULE
 `!x y z:N word.
        word_ile x y /\ word_ilt y z ==> word_igt z x`;;

time WORD_AUTO_RULE
 `!x y:N word.
        word_ushr (word_shl x 1) 1 = x /\
        word_ushr (word_shl y 1) 1 = y
        ==> (word_ule x y <=> word_ile x y)`;;

time WORD_AUTO_RULE
 `!x y:N word. word_ule (word_and x y) x`;;

time WORD_AUTO_RULE
 `!x y:N word. word_ule (word_xor x y) (word_or x y)`;;

(* ------------------------------------------------------------------------- *)
(* Random things from Hacker's Delight.                                      *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!x:N word. word_not(word_or x (word_neg x)) =
             word_sub (word_and x (word_neg x)) (word 1)`;;

time WORD_AUTO_RULE
 `!x:N word. word_and (word_add (word_or x (word_sub x (word 1))) (word 1)) x =
             word_and (word_add (word_and x (word_neg x)) x) x`;;

time WORD_AUTO_RULE
 `!x:N word. word_not(word_add x y) = word_sub (word_not x) y`;;

time WORD_AUTO_RULE
 `!x y:N word. word_or x y = word_add (word_and x (word_not y)) y`;;

time WORD_AUTO_RULE
 `!x y:N word. word_sub x y =
               word_sub (word_mul (word 2) (word_and x (word_not y)))
                        (word_xor x y)`;;

time WORD_AUTO_RULE
 `!x y:N word.
        word_ilt x y <=>
        ~(word_and word_INT_MIN
           (word_sub (word_sub (word_ishr x 1) (word_ishr y 1))
                     (word_and (word_and (word_not x) y) (word 1))) =
          word 0)`;;

time WORD_AUTO_RULE
 `!x y:N word.
        word_ult x y <=>
        ~(word_and word_INT_MIN
           (word_sub (word_sub (word_ushr x 1) (word_ushr y 1))
                     (word_and (word_and (word_not x) y) (word 1))) =
          word 0)`;;

time WORD_AUTO_RULE
 `!x:N word. ~(x = word 0) <=> ival(word_or x (word_neg x)) < &0`;;

time WORD_AUTO_RULE
 `!x y:N word. x = y <=> ival(word_or (word_sub x y) (word_sub y x)) >= &0`;;

time WORD_AUTO_RULE
 `!x:N word. word_igt x (word 0) <=>
             ival (word_sub (word_ishr x 1) x) < &0`;;

time WORD_AUTO_RULE
 `!x:N word. word_igt x (word 0) <=>
             ival (word_and (word_neg x) (word_not x)) < &0`;;

(* ------------------------------------------------------------------------- *)
(* Bounds checking.                                                          *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `!a b x:N word.
        word_ile a b
        ==> (word_ile a x /\ word_ile x b <=>
             word_ule (word_sub x a) (word_sub b a))`;;

time WORD_AUTO_RULE
 `!a b x:N word.
        word_ile a b
        ==> (word_ile a x /\ word_ilt x b <=>
             word_ult (word_sub x a) (word_sub b a))`;;

(* ------------------------------------------------------------------------- *)
(* Using xor as alternative to subtraction.                                  *)
(* ------------------------------------------------------------------------- *)

time WORD_AUTO_RULE
 `val(x:N word) < val(word 64:N word)
   ==> word_sub (word 63) x = word_xor x (word 63)`;;
