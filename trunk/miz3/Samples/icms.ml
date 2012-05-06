needs "Multivariate/misc.ml";;

prioritize_real();;

let ABS_CASES = thm `;
  !x. x = &0 \/ &0 < abs(x)`;;

let LL =  REAL_ARITH `&1 < k ==> &0 < k`;;

horizon := 0;;

let IMO_1 = thm `;
  !k. &1 < k ==> &0 < k [LL] by REAL_ARITH;
  now
    let f g be real->real;
    let x be real;
    assume !x y. f (x + y) + f (x - y) = &2 * f x * g y [1];
    assume ~(!x. f x = &0) [2];
    assume !x. abs (f x) <= &1 [3];
    now
      let k be real;
      assume sup (IMAGE (\x. abs (f x)) (:real)) = k [4];
      ~(IMAGE (\x. abs (f x)) (:real) = {}) /\ (?b. !x. abs (f x) <= b) [5]
        by ASM SET_TAC[],-,3;
      now
        assume !x. abs (f x) <= k [6];
        assume !b. (!x. abs (f x) <= b) ==> k <= b [7];
        now
          let y be real;
          assume &1 < abs (g y) [8];
          !x. abs (f x) <= k / abs (g y) [9]
            by ASM_MESON_TAC[REAL_LE_RDIV_EQ; REAL_ABS_MUL; LL;
              REAL_ARITH (parse_term
                "u + v = &2 * z /\\ abs u <= k /\\ abs v <= k ==> abs z <= k")
             ],-,1,6;
          ~(k <= k / abs (g y))
            by TIMED_TAC 2
              (ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_LDIV_EQ; REAL_LT_LMUL;
                 REAL_MUL_RID; LL; REAL_ARITH (parse_term
                  "~(z = &0) /\\ abs z <= k ==> &0 < k")
                ]),LL,2,6,8;
          (!x. abs (f x) <= k / abs (g y)) /\ ~(k <= k / abs (g y))
            by CONJ_TAC,-,9;
          ((!x. abs (f x) <= k / abs (g y)) ==> k <= k / abs (g y)) ==> F
            by SIMP_TAC[NOT_IMP; NOT_FORALL_THM],-;
          thus F by FIRST_X_ASSUM(MP_TAC o
            SPEC (parse_term "k / abs(g(y:real))")),-,7;
        end;
        ~(?y. &1 < abs (g y)) by STRIP_TAC,-;
        thus !y. abs (g y) <= &1
          by SIMP_TAC[GSYM REAL_NOT_LT; GSYM NOT_EXISTS_THM],-;
      end;
      (!x. abs (f x) <= k) /\ (!b. (!x. abs (f x) <= b) ==> k <= b)
      ==> (!y. abs (g y) <= &1) by STRIP_TAC,-;
      (~(IMAGE (\x. abs (f x)) (:real) = {}) /\ (?b. !x. abs (f x) <= b)
       ==> (!x. abs (f x) <= k) /\ (!b. (!x. abs (f x) <= b) ==> k <= b))
      ==> (!y. abs (g y) <= &1) by ANTS_TAC,-,5;
      (~(IMAGE (\x. abs (f x)) (:real) = {}) /\
       (?b. !x. x IN IMAGE (\x. abs (f x)) (:real) ==> x <= b)
       ==> (!x. x IN IMAGE (\x. abs (f x)) (:real)
                ==> x <= sup (IMAGE (\x. abs (f x)) (:real))) /\
           (!b. (!x. x IN IMAGE (\x. abs (f x)) (:real) ==> x <= b)
                ==> sup (IMAGE (\x. abs (f x)) (:real)) <= b))
      ==> (!y. abs (g y) <= &1)
        by ASM_SIMP_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV],-,4;
      thus !y. abs (g y) <= &1
        by MP_TAC(SPEC (parse_term "IMAGE (\\x. abs(f(x))) (:real)") SUP),-;
    end;
    !y. abs (g y) <= &1
      by ABBREV_TAC (parse_term "k = sup (IMAGE (\\x. abs(f(x))) (:real))"),-;
    thus abs (g x) <= &1
      by SPEC_TAC ((parse_term "x:real"),(parse_term "y:real")),-;
  end;
  thus !f g. (!x y. f(x + y) + f(x - y) = &2 * f(x) * g(y)) /\
             ~(!x. f(x) = &0) /\ (!x. abs(f(x)) <= &1)
             ==> !x. abs(g(x)) <= &1 by REPEAT STRIP_TAC,-`;;

horizon := 1;;

let IMO_2 = thm `;
  let f g be real->real;
  assume !x y. f (x + y) + f (x - y) = &2 * f x * g y [1];
  assume ~(!x. f x = &0) [2];
  assume !x. abs (f x) <= &1 [3];
  thus !x. abs (g x) <= &1
  proof set s = IMAGE (\x. abs (f x)) (:real);
    ~(s = {}) [4] by SET_TAC;
    !b. (!y. y IN s ==> y <= b) <=> (!x. abs (f x) <= b) by IN_IMAGE,IN_UNIV;
    set k = sup s;
    (!x. abs (f x) <= k) /\ !b. (!x. abs (f x) <= b) ==> k <= b [5] by 3,4,SUP;
    assume ~thesis;
    consider y such that &1 < abs (g y) [6] by REAL_NOT_LT;
    &0 < abs (g y) [7] by REAL_ARITH;
    !x. abs (f x) <= k / abs (g y) [8]
    proof let x be real;
      abs (f (x + y)) <= k /\ abs (f (x - y)) <= k /\
      f (x + y) + f (x - y) = &2 * f x * g y by 1,5;
      abs (f x * g y) <= k by REAL_ARITH;
    qed by 7,REAL_ABS_MUL,REAL_LE_RDIV_EQ;
    consider x such that &0 < abs (f x) /\ abs (f x) <= k by 2,5,ABS_CASES;
    &0 < k by REAL_ARITH;
    k / abs (g y) < k by 6,7,REAL_LT_LMUL,REAL_MUL_RID,REAL_LT_LDIV_EQ;
  qed by 5,8,REAL_NOT_LE`;;

let IMO_3 = thm `;
  let f g be real->real;
  assume !x y. f (x + y) + f (x - y) = &2 * f x * g y [1];
  assume ~(!x. f x = &0) [2];
  assume !x. abs (f x) <= &1 [3];
  thus !x. abs (g x) <= &1
  proof
    now [4] let y be real;
      !x. abs (f x * g y pow 0) <= &1 [5] by 3,real_pow,REAL_MUL_RID;
      now let l be num;
        assume !x. abs (f x * g y pow l) <= &1;
        let x be real;
        abs (f (x + y) * g y pow l) <= &1 /\
        abs (f (x - y) * g y pow l) <= &1;
        abs ((f (x + y) + f (x - y)) * g y pow l) <= &2 by REAL_ARITH;
        abs ((&2 * f x * g y) * g y pow l) <= &2 by 1;
        abs (f x * g y * g y pow l) <= &1 by REAL_ARITH;
        thus abs (f x * g y pow SUC l) <= &1 by real_pow,REAL_MUL_RID;
      end;
      thus !l x. abs (f x * g y pow l) <= &1 by INDUCT_TAC,5;
    end;
    !x y. ~(x = &0) /\ &1 < abs(y) ==> ?n. &1 < abs(y pow n * x)
      by SIMP_TAC,REAL_ABS_MUL,REAL_ABS_POW,GSYM REAL_LT_LDIV_EQ,
        GSYM REAL_ABS_NZ,REAL_ARCH_POW;
  qed by 2,4,REAL_NOT_LE,REAL_MUL_SYM`;;

