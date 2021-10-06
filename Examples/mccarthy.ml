(*****************************************************************************
*
*  mp.ml
*
*  An HOL mechanization of the compiler correctness proof of McCarthy and
*  Painter from 1967.
*
*  From a HOL-4 original by Robert Bauer and Ray Toal
*
*  HOL Light proof by John Harrison, 21st April 2004
*
*****************************************************************************)

(* ------------------------------------------------------------------------- *)
(* Define a type of strings, not already there in HOL Light.                 *)
(* We don't use any particular properties of the type in the proof below.    *)
(* ------------------------------------------------------------------------- *)

let string_INDUCT,string_RECURSION =
  define_type "string = String (int list)";;

(* ------------------------------------------------------------------------- *)
(* The definitions from Robert's file.                                       *)
(* ------------------------------------------------------------------------- *)

(*
 *  The source language
 *  -------------------
 *
 *  Syntax:
 *
 *  The language contains only expressions of three kinds: (1) simple
 *  numeric literals, (2) simple variables, and (3) plus expressions.
 *)

let exp_INDUCT,exp_RECURSION =
  define_type "exp = Lit num
                   | Var string
                   | Plus exp exp";;

(*
 *  Semantics:
 *
 *  Expressions evaluated in a state produce a result.  There are no
 *  side effects.  A state is simply a mapping from variables to
 *  values.  The semantic function is called E.
 *)

let E_DEF = new_recursive_definition exp_RECURSION
           `(E (Lit n) s = n)
        /\  (E (Var v) s = s v)
        /\  (E (Plus e1 e2) s = E e1 s + E e2 s)`;;

(*
 *  The object language
 *  -------------------
 *
 *  Syntax:
 *
 *  The target machine has a single accumulator (Acc) and an infinite
 *  set of numbered registers (Reg 0, Reg 1, Reg 2, and so on).  The
 *  accumulator and registers together are called cells.  There are four
 *  instructions: LI (load immediate into accumulator), LOAD (load the
 *  contents of a numbered register into the accumulator), STO (store
 *  the accumulator value into a numbered register) and ADD (add the
 *  contents of a numbered register into the accumulator).
 *)

let cell_INDUCT,cell_RECURSION =
  define_type "cell = Acc
                    | Reg num";;

let inst_INDUCT,inst_RECURSION =
  define_type "inst = LI num
                    | LOAD num
                    | STO num
                    | ADD num";;

(*
 *  update x z s is the state that is just like s except that x now
 *  maps to z.  This definition applies to any kind of state.
 *)

let update_def =
    new_definition `update x z s y = if (y = x) then z else s y`;;

(*
 *  Semantics:
 *
 *  First, the semantics of the execution of a single instruction.
 *  The semantic function is called S.  Executing an instruction in
 *  a machine state produces a new machine state.  Here a machine
 *  state is a mapping from cells to values.
 *)

let S_DEF = new_recursive_definition inst_RECURSION
           `(S (LI n) s = update Acc n s)
        /\  (S (LOAD r) s = update Acc (s (Reg r)) s)
        /\  (S (STO r) s = update (Reg r) (s Acc) s)
        /\  (S (ADD r) s = update Acc (s (Reg r) + s Acc) s)`;;

(*
 *  Next we give the semantics of a list of instructions with the
 *  semantic function S'.  The execution of an intruction list
 *  in an initial state is given by executing the first instruction
 *  in the list in the initial state, which produce a new state s1,
 *  and taking the execution of the rest of the list in s1.
 *)

let S'_DEF = new_recursive_definition list_RECURSION
           `(S' [] s = s)
        /\  (S' (CONS inst rest) s = S' rest (S inst s))`;;

(*
 *  The compiler
 *  ------------
 *
 *  Each source language expression is compiled into a list of
 *  instructions.  The compilation is done using a symbol table
 *  which maps source language indentifiers into target machine
 *  register numbers, and a parameter r which tells the next
 *  available free register.
 *)

let C_DEF = new_recursive_definition exp_RECURSION
            `(C (Lit n) map r = [LI n])
         /\  (C (Var v) map r = [LOAD (map v)])
         /\  (C (Plus e1 e2) map r =
                  APPEND
                      (APPEND (C e1 map r) [STO r])
                      (APPEND (C e2 map (r + 1)) [ADD r]))`;;

(* ------------------------------------------------------------------------- *)
(* My key lemmas; UPDATE_DIFFERENT and S'_APPEND are the same as Robert's.   *)
(* ------------------------------------------------------------------------- *)

let cellth = CONJ (distinctness "cell") (injectivity "cell");;

let S'_APPEND = prove
 (`!p1 p2 s. S' (APPEND p1 p2) s = S' p2 (S' p1 s)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[S'_DEF; APPEND]);;

let UPDATE_DIFFERENT = prove
 (`!x y z s. ~(x = y) ==> (update x z s y = s y)`,
  SIMP_TAC[update_def]);;

let UPDATE_SAME = prove
 (`!x z s. update x z s x = z`,
  SIMP_TAC[update_def]);;

(*
 *  The Correctness Condition
 *  -------------------------
 *
 *  The correctness condition is this:
 *
 *  For every expression e, symbol table map, source state s,
 *      target state s', register number r:
 *
 *  If all source variables map to registers LESS THAN r,
 *  and if the value of every variable v in s is exactly
 *  the same as the value in s' of the register to which
 *  v is mapped by map, THEN
 *
 *  When e is compiled with map and first free register r,
 *  and then executed in the state s', in the resulting
 *  machine state S'(C e map r):
 *
 *  the accumulator will contain E e s and every register
 *  with number x less than r will have the same value as
 *  it does in s'.
 *
 *  The Proof
 *  ---------
 *
 *  The proof can be done by induction and careful application of SIMP_TAC[]
 *  using the lemmas isolated above.
 *
 *  The only "hack" is to throw in GSYM SKOLEM_THM and EXISTS_REFL to dispose
 *  of state existence subgoals of the form `?s. !v. s v = t[v]`, which
 *  otherwise would not be proven automatically by the simplifier.
 *)

let CORRECTNESS_THEOREM = prove
 (`!e map s s' r.
      (!v. map v < r) ==>
      (!v. s v = s' (Reg (map v))) ==>
          (S' (C e map r) s' Acc = E e s) /\
          (!x. (x < r) ==> (S' (C e map r) s' (Reg x) = s' (Reg x)))`,
  MATCH_MP_TAC exp_INDUCT THEN
  REWRITE_TAC[E_DEF; S_DEF; S'_DEF; update_def; C_DEF; S'_APPEND] THEN
  SIMP_TAC[ARITH_RULE `(x < y ==> x < y + 1 /\ ~(x = y)) /\ x < x + 1`; cellth;
           UPDATE_SAME; UPDATE_DIFFERENT; GSYM SKOLEM_THM; EXISTS_REFL]);;
