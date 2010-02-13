(*---------------------------------------------------------------------------*)
(*
   File:         mk_unity_prog.sml

   Description:

   A back-end definition for the HOL-UNITY compiler programming language.
   =====================================================================

   This file introduces general definitions for describing a program
   in HOL-UNITY.

   Author:       (c) Copyright 1992-2008
                 by Flemming Andersen & Kim Dam Petersen
   Date:         August 3, 1992
   Updated:      May 4, 1995
   Updated:      March 22, 2006
   Last Update:  December 30, 2007

     The functions below are based on the following representations:

     type 'loc  =                               ``program variable location''
     type 'val  =                               ``program value''
     type state = ('loc -> 'val)                ``program state''

     type t xpr = state -> t                    ``expression of type t''
     type t asg = t -> state -> state -> state  ``assignment of type t''
     type t var = (t xpr, t asg)                ``variable of type t''

     type atom  = state -> state                ``atomic (singleton action)''
     type par   = state -> state -> state       ``parallel action''
     type int   = atom list                     ``interleaved action (program)''
     type seq   = var -> num -> (int list # num)``sequential action''


     Description of type representation: (Added: March 22, 2006)
     -----------------------------------------------------------

     'loc    is an atomic (location) value that identifies a variable.
             Composite variables, such as arrays and lists has a
             single identifier. Assignment to a composite part is
             considered an assignment to the complete variable, that
             doesn't change the non-assigned parts of the variable.

     'val    is a generic value type of all variables.
             It is constructed as a union of the types of the
             variables in the program. Each program will for each type
             of variable define a pair of functions to respectively
             encode and decode values of the type of the variable into
             and from the generic type 'val.

     state   is a state that associates each variable (identified by it's
             'loc location) with it's current value (encoded in the
             generic type 'val of value).
             A state represents the values of every variable at a
             given moment.
             A state is implemented as a map from variable locations
             ('loc) to the generic value ('val) of the applied
             variable location.

     -----

     xpr     'val xpr - generic typed expression.

     t xpr   is an expression of some (decoded) type t.
             An expression represents a state dependent value, ie. a
             value that depends on the values of variables.
             An expression is implemented as map from a state (in
             which the value is to be interpreted) to the value of the
             expression in that state.

     t asg   is a assignment to a variable of type t.
             An assignment represents the change in state due to
             assignment of some variable to a value.  An assignment is
             implemented as a map from the value to be assigned, the
             original state and a previous state to the final state.
             The need for two parameter states: original and previous
             is due to the fact that assignment Consider the
             (high-level) assignment:

             INITIALLY
                a[0] = 0 /\ a[1] = 1
             ASSIGN
                a[a[0]], a[a[1]] := 1, 0

             The right-hand-side expression, and the left-hand-side
             index expression should be evaluated in the original
             state.

             The parallel assignments of:
                a[a[0]], a[a[1]] := 1, 0
             must be "transformed" into a single assignment of a:
                a := a[a[i] => 1, a[j] => 0]
             If more variables are to be assigned we get:
                i, j, a := 1, 0, a[a[i] => 1, a[j] => 0]
             A parallel assignment is evaluated in sequence; it is
             transformed into:
                [ i := <1> ] ; [ j := <0> ] ; [ a := <a[a[i] => 1, a[j] => 0> ]
             It should be obvious that the expression in <>-braces has
             to be evaluated in the original state of the parallel
             assignment, whereas the sequential assignments has to be
             evaluated in the state that is the result of the previous
             assignment. This explains the need for two state
             parameters.

             ** To Be Changed **

     t var   is a variable of type t.
             A variable is represented by a pair that allow read- and
             write- access to the variable.
             ** To Be Changed **

     atom    is an atomic action.
             An atomic action represents the state change associated
             with a single variable assignments.  An atomic action is
             implemented as a function, that given an initial state
             returns the state after executing the atomic action.  **
             To Be Changed **

     par     is a parallel action.
             A parallel action represents the state change associated
             with multiple atomic actions, ex.
               (a[0] := a[1]) || (a[1] := a[0]).
             A parallel action is implemented as a function of an
             original- and previous state, that return a next
             state. The use of original- and previous state is
             explained above under section "t asg".
             ** To Be Changed **

     int     is an interleaved action.
             An interleaved action represents the semantic of an
             interleaved action.  An interleaved action is implemented
             as a funtion that given an initial state returns the
             state after evaluating the interleaved action.

     seq     is a sequential action.
             A sequential action is a sequence of interleaved
             actions. Each interleaved action is identified with a
             numeric label.  A sequential action is represented as a
             function that takes a program counter variable location,
             a NUM -encode and -decode function and an initial label
             for the action and returns a pair with a list of
             interleaved actions that implements the individual
             actions to be executed in sequence and a numeric label
             that represents the end of the sequential action.  This
             label is used as initial label for an optional sequential
             action that is compositionally added to the current.

             Example: val s1 : seq = `` Computer generated seq '';
                      val s2 : seq = `` Computer generated seq '';
                      val s1s2 : seq = fn pc => mk => ds => l0 =>
                          let val (lst1, l1) = s1 pc mk ds l0 in
                          let val (lst2, l2) = s2 pc mk ds l1 in
                            (APPEND lst1 lst2, l2)


[Flemming, May 1995:

            Whereas we leave it for now due to the otherwize need for
            updating the compiler, assignment COULD BE CHANGED to the
            alternative below...]

            An alternative way of implementing multiple parallel
            assignment exists:

            1. Introduce a parallel variable assignment operator,
               which takes a list of locations and a list of evaluated
               generic typed expressions and performs the
               assignment. There will no problems with side-effects,
               due to the fact that all values has been evaluated.

               define
                 ParAsg ([]: 'loc list) ([] : 'val list) (s : state) : state = s
               |  ParAsg (loc::locs) (val :: vals) =
                      ParAsg locs vals (fn l => (l == loc) ? val | s l))
               |  ParAsg _ _ = raise "ParAsg: location and value list differ in length";

               The new type of ParAsg becomes:

               ParAsg : 'loc list -> 'val list -> state -> state

               If we redefine the type asg we get

               ParAsg : 'loc list -> 'val list -> asg

            2. Introduce a list evaluation operator:

               define
                   EvalList ([] : (state -> 'val) list) (s : state) : 'val list = []
                |  EvalList (genExp :: genExps) s = (genExp s) :: EvalList genExps s;

            3. Compile a source parallel assignment into two lists:
               locs of the variables being assigned, and exps of
               component transformed expressions using decoded
               types. This process is part of the exisiting compiler.

            4. Prepend each expression in exps with the proper encode
               function This produces a list genExps where every
               element is a generic typed expression.

            5. The final representaion can now be expressed as:

               ...
               val locs_123    : 'loc list = [ ``Generated by compiler'' ]
               val genExps_123 : 'val list = [ ``Generated by compiler'' ]
               val parAsg_123  : asg       = (ParAsg locs_123) o (EvalList genExps_123)
               ...

            a)  A consequence of this is that VAR parameters should be
                represented by their 'loc location.
            b)  A variable component can not be used as argument for a
                VAR parameter, but still be used for a value parameter.
            c)  The assignment and update funtion will be deprecated.
            d)  The write part of a variable pair has to be replaced
                with it's 'loc location.
            e)  The representation of an atomic action should be changed
                such that it is based on the variable locations and the
                assigned expressions. (How do we handle components???)

*)
(*---------------------------------------------------------------------------*)


let NUM     = `:num`;;
let BOOL    = `:bool`;;
let VAR_TP  = (fun s -> mk_vartype("'"^s));;
let LST     = (fun t -> mk_type("list",[t]));;
let PRD     = (fun (l,r) -> mk_type("prod",[l;r]));;
let FUN     = (fun (l,r) -> mk_type("fun",[l;r]));;
let rec FNC =
   function (l,[])      -> l
          | (l,(r::rs)) -> FUN(l,FNC(r,rs));;

let LOC = VAR_TP"loc";;
let VAL = VAR_TP"val";;
let STA = FUN(LOC,VAL);;
let ACT = FUN(STA,STA);;
let INT = LST(ACT);;

let XPR = (fun t -> FUN(STA,t));;
let ASG = (fun t -> FNC(XPR t,[STA; STA; STA]));;
let VAR = (fun t -> PRD(XPR t, ASG t));;
let PAR = FNC(STA,[STA; STA]);;
let SEQ = FUN(LOC, FUN(FUN(NUM,VAL), FUN(FUN(VAL,NUM), FUN(NUM, PRD(INT,NUM)))));;

(*---------------------------------------------------------------------------*)
(*
  Defining Variable extraction functions
*)
(*---------------------------------------------------------------------------*)

let t   = mk_vartype"'t";;
let v   = mk_var("v", VAR t);;

new_type_abbrev("stype",
   `:'loc->'val`);;
new_type_abbrev("vtype",
   `:(stype->'t)#((stype->'t)->stype->stype->stype)`);;
new_type_abbrev("vindex_type",
   `:(stype->'i->'t)#((stype->'i->'t)->stype->stype->stype)`);;
new_type_abbrev("vpair_type",
   `:(stype->'a#'b)#((stype->'a#'b)->stype->stype->stype)`);;
new_type_abbrev("seq_type",
   `:'loc->(num->'val)->('val->num)->num->(stype->stype)list#num`);;


(*
 * Extraction expression of a variable
 *)
let VAR_EXP = new_definition (`VAR_EXP (v:vtype) = FST v`);;

(*
 * Extraction assignment of a variable
 *)
let VAR_ASG = new_definition (`VAR_ASG (v:vtype) = SND v`);;

(*---------------------------------------------------------------------------*)
(*
  Location to variable translator functions
*)
(*---------------------------------------------------------------------------*)

let loc = mk_var("loc",LOC);;
let s   = mk_var("s",  STA);;
let s0  = mk_var("s0", STA);;
let ds  = mk_var("ds", FUN(VAL,t));;
let mk  = mk_var("mk", FUN(t,VAL));;
let e   = mk_var("e", XPR t);;

(*
 * Translate a location to an expression
 *)
let LOC_EXP = new_definition
  (`LOC_EXP loc (ds:'val->'t) (s:stype) = ds (s loc)`);;

(*
 * Translate a location to an assignment
 *)
let LOC_ASG = new_definition
  (`LOC_ASG loc (mk:'t->'val) (e:stype->'t)
                             (s0:stype) (s:stype) l =
      (if (l = loc) then (mk (e s0)) else (s l))`);;

(*
 * Translate a location to a variable pair
 *)
let LOC_VAR = new_definition
  (`LOC_VAR (loc:'loc) (mk:'t->'val) (ds:'val->'t) =
       (LOC_EXP loc ds, LOC_ASG loc mk)`);;

(*---------------------------------------------------------------------------*)
(*
  Array (index) functions
*)
(*---------------------------------------------------------------------------*)

(*
 * Generate index expression
 *
 * IndexExp [(i,v),...] a
 *)
let INDEX_EXP = new_definition
   (`(INDEX_EXP (a:stype->('i->'t)) (i:stype->'i) (s:stype) =
          (a s) (i s))`);;

(*
 * Generate updated index expression (index, exp and array are frozen)
 *
 * UpdIndex [(i,v),...] a
 *)
let UPD_INDEX = new_definition
  (`(UPD_INDEX (i:'i) (c:'t) (a:'i->'t) j = (if (j = i) then c else (a j)))`);;

(*
 * Generate updated index expression (index and exp are frozen)
 *
 * UPD_INDEX_XPR [(i,v),...] a
 *)
let UPD_INDEX_EXP = new_definition
  (`(UPD_INDEX_EXP (i:'i) (c:'t) (a:stype->'i->'t) (s:stype) =
       UPD_INDEX i c (a s))`);;

(*
 * Assignment part from Index of a variable
 *)
let VAR_INDEX_ASG = new_definition
  (`VAR_INDEX_ASG
     (i:stype->'i) (v:vindex_type)
     (e:stype->'t) (s0:stype) (s:stype) =
         VAR_ASG v (UPD_INDEX_EXP (i s0) (e s0) (VAR_EXP v)) s0 s`);;

(*
 * Expression part from Index of a variable
 *)
let VAR_INDEX_EXP = new_definition
  (`VAR_INDEX_EXP
     (i:stype->'i) (v:vindex_type) (s:stype) =
        (VAR_EXP v s) (i s)`);;

(*
 * Index variable
 *)
let VAR_INDEXVAR = new_definition
  (`VAR_INDEXVAR (i:stype->'i) (v:vindex_type) =
         (VAR_INDEX_EXP i v, VAR_INDEX_ASG i v)`);;

(*---------------------------------------------------------------------------*)
(*
  List functions (not complete)
*)
(*---------------------------------------------------------------------------*)

(*
 * List of expressions
 *)
let LIST_EXP_term =
  (`(LIST_EXP [] (s:stype)               = []) /\
    (LIST_EXP (CONS (e:stype->'t) t) s = (CONS (e s) (LIST_EXP t s)))`);;
let LIST_EXP = new_recursive_definition list_RECURSION LIST_EXP_term;;

(*---------------------------------------------------------------------------*)
(*
  Record (pair,fst,snd) functions
*)
(*---------------------------------------------------------------------------*)

(*
 * State abstracted FST and SND
 *)
let s_FST = new_definition
  (`s_FST (e:'sta->('a # 'b)) s = FST (e s)`);;

let s_SND = new_definition
  (`s_SND (e:'sta->('a # 'b)) s = SND (e s)`);;

(*
 * Update PAIR
 *)
let UPD_FST = new_definition
  (`UPD_FST (c:'a) (p:'sta->('a#'b)) s = (c, SND(p s))`);;

let UPD_SND = new_definition
  (`UPD_SND (c:'b) (p:'sta->('a#'b)) s = (FST(p s),c)`);;

(*
 * Assignment to FST and SND
 *)
let VAR_FST_ASG = new_definition
  (`VAR_FST_ASG (v:vpair_type) (e:stype->'a) (s0:stype) (s:stype) =
         VAR_ASG v (UPD_FST (e s0) (VAR_EXP v)) s0 s`);;

let VAR_SND_ASG = new_definition
  (`VAR_SND_ASG (v:vpair_type) (e:stype->'b) (s0:stype) (s:stype) =
         VAR_ASG v (UPD_SND (e s0) (VAR_EXP v)) s0 s`);;

(*
 * Variables of FST and SND
 *)
let FST_VAR = new_definition
   (`FST_VAR (v:vpair_type) = (s_FST (VAR_EXP v), VAR_FST_ASG v)`);;

let SND_VAR = new_definition
   (`SND_VAR (v:vpair_type) = (s_SND (VAR_EXP v), VAR_SND_ASG v)`);;

(*---------------------------------------------------------------------------*)
(*
  Parallel actions
*)
(*---------------------------------------------------------------------------*)

(*
 * Execute two parallel actions simultaneously
 *)
let PAR_PAR = new_definition
  (`(PAR_PAR (p1:stype->stype->stype)
             (p2:stype->stype->stype)
             (s0:stype) (s:stype) =
        p2  s0 (p1 s0 s))`);;

(*
 * Execute a list of parallel actions
 *)
let LIST_PAR_term =
  (`(LIST_PAR [] (s0:stype) (s:stype) = s) /\
    (LIST_PAR (CONS (h:stype->stype->stype) t) s0 s = LIST_PAR t s0 (h s0 s))`);;
let LIST_PAR =  new_recursive_definition list_RECURSION LIST_PAR_term;;

(*
 * Translate a parallel action into an atomic action
 *)
let PAR_ATOM = new_definition
 (`PAR_ATOM (p:stype->stype->stype) (s:stype) = p s s`);;

(*
 * Guard a parallel action
 *)
let WHEN_PAR = new_definition
  (`WHEN_PAR (p:stype->stype->stype) g
             (s0:stype) (s:stype) =
        (if (g s0) then (p s0 s) else s)`);;

(*
 * Conditional parallel action
 *)
let IF_PAR = new_definition
  (`IF_PAR (p1:stype->stype->stype)
           (p2:stype->stype->stype) g
           (s0:stype) (s:stype) =
     (if (g s0) then (p1 s0 s) else (p2 s0 s))`);;

(*
 * Identity parallel action
 *)
let ID_PAR = new_definition (`ID_PAR (s0:stype) (s:stype) = s`);;

(*
 * Iterated parallel assignment
 *)
let ITER_PAR0_term =
 (`(ITER_PAR0 (low:num) 0 (f:num->bool)
       (fi:num->stype->stype->stype) = ID_PAR) /\
   (ITER_PAR0 low (SUC n) f fi =
       (if (f low) then PAR_PAR (fi low) (ITER_PAR0 (SUC low) n f fi)
                   else (ITER_PAR0 (SUC low) n f fi)))`);;
let ITER_PAR0 = new_recursive_definition num_RECURSION ITER_PAR0_term;;

let ITER_PAR = new_definition
  (`ITER_PAR low high (f:num->bool)
                      (fi:num->stype->stype->stype) =
      (ITER_PAR0 low ((1+high)-low) f fi)`);;

(*---------------------------------------------------------------------------*)
(*
  Atomic actions
*)
(*---------------------------------------------------------------------------*)

(*
 * Translate a parallel action into an atomic action
 *)

(*
   K and S are removed from HOL Light.
   I and o are defined in trivia.ml

   So I introduce K myself
*)
let K_DEF = new_definition (`K x y = x`);;

let ASG_ACT = new_definition
  (`ASG_ACT (par:stype->stype->stype)
            (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
          PAR_ATOM
           (WHEN_PAR (LIST_PAR [par; LOC_ASG pc mk (K (SUC l0))])
                     (LOC_EXP pc ds =* (K l0)))`);;

(*
 * Test atomic action
 *)
let TST_ACT = new_definition
  (`TST_ACT (g:stype->bool)
            (l:num) (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
     (PAR_ATOM (WHEN_PAR (LOC_ASG pc mk ((g =>* K(SUC l0)) (K l)))
                    (LOC_EXP pc ds =* K l0)))`);;

(*
 * Goto atomic action
 *)
let GTO_ACT = new_definition
  (`GTO_ACT (l:num) (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
        PAR_ATOM (WHEN_PAR (LOC_ASG pc mk (K l))
                           (LOC_EXP pc ds =* K l0))`);;

(*---------------------------------------------------------------------------*)
(*
  Sequential actions
*)
(*---------------------------------------------------------------------------*)

(*
 * Translate parallel to sequential action
 *)
let PAR_SEQ = new_definition
  (`PAR_SEQ (par:stype->stype->stype)
            (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
            ([ASG_ACT par pc mk ds l0], SUC l0)`);;

(*
 * Identity sequential action
 *)
let ID_SEQ = new_definition
  (`ID_SEQ (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
      ([], l0)`);;

(*
 * Execute two sequential actions in a row
 *)
let SEQ_SEQ = new_definition
  (`SEQ_SEQ (s1:seq_type) (s2:seq_type)
            (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
      let b1 = s1 pc mk ds l0 in
      let b2 = s2 pc mk ds (SND b1) in
        (APPEND (FST b1) (FST b2), (SND b2))`);;

(*
 * Iterated sequential actions
 *)
let ITER_SEQ0_term =
 (`(ITER_SEQ0 (low:num) 0 (f:num->bool) (fi:num->seq_type) = ID_SEQ) /\
   (ITER_SEQ0 low (SUC n)  f             fi =
        (if (f low) then (SEQ_SEQ (fi low) (ITER_SEQ0 (SUC low) n f fi))
                    else (ITER_SEQ0 (SUC low) n f fi)))`);;
let ITER_SEQ0 = new_recursive_definition num_RECURSION ITER_SEQ0_term;;

let ITER_SEQ = new_definition
  (`ITER_SEQ low high (f:num->bool) (fi:num->seq_type) =
        ITER_SEQ0 low ((1+high)-low) f fi`);;

(*
 * List of sequential actions
 *)
let LIST_SEQ_term =
  (`(LIST_SEQ [] (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) = ([], l0)) /\
    (LIST_SEQ (CONS (sa:seq_type) sas) pc mk ds l0 =
       let b1 = sa pc mk ds l0 in
       let bs = LIST_SEQ sas pc mk ds (SND b1) in
          (APPEND (FST b1) (FST bs), (SND bs)))`);;
let LIST_SEQ = new_recursive_definition list_RECURSION LIST_SEQ_term;;

(*
 * Conditional sequential actions
 *)
let IF1_SEQ = new_definition
  (`(IF1_SEQ (g:stype->bool)
             (sa:seq_type) (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
       let b1 = sa pc mk ds (SUC l0) in
       let a1 = TST_ACT g (SND b1) pc mk ds l0 in
         (CONS a1 (FST b1), (SND b1)))`);;

(*
 * Conditional (else) sequential actions
 *)
let IF2_SEQ = new_definition
 (`(IF2_SEQ (g:stype->bool) (sa1:seq_type) (sa2:seq_type)
             (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
       let b1 = sa1 pc mk ds (SUC l0)                in
       let b2 = sa2 pc mk ds (SUC (SND b1))          in
       let a1 = TST_ACT g (SUC (SND b1)) pc mk ds l0 in
       let a2 = GTO_ACT (SND b2) pc mk ds (SND b1)   in
          (APPEND (CONS a1 (FST b1))
                  (CONS a2 (FST b2)), (SND b2)))`);;

(*
 * While loop sequential actions
 *)
let WHL_SEQ = new_definition
 (`(WHL_SEQ (g:stype->bool) (sa:seq_type)
            (pc:'loc) (mk:num->'val) (ds:'val->num) (l0:num) =
      let b1 = sa pc mk ds (SUC l0)                 in
      let a1 = TST_ACT g (SUC (SND b1)) pc mk ds l0 in
      let a2 = GTO_ACT l0 pc mk ds (SND b1)         in
         (APPEND (CONS a1 (FST b1)) [a2], (SUC(SND b1))))`);;

(*---------------------------------------------------------------------------*)
(*
  Interleaved actions
*)
(*---------------------------------------------------------------------------*)

(*
 * Translate a parallel action into an interleaved action
 *)
let PAR_INT = new_definition
  (`PAR_INT (par:stype->stype->stype) = [PAR_ATOM par]`);;

(*
 * Composition of two interleaved actions
 *)
let INT_INT = new_definition
  (`INT_INT (i1:(stype->stype)list) i2 = APPEND i1 i2`);;

(*
 * Translate a list of interleaved action into a single interleaved action
 *)
let LIST_INT_term =
 (`(LIST_INT [] = ([]:(stype->stype)list)) /\
   (LIST_INT (CONS (h:(stype->stype)list) t) =
                     (APPEND h (LIST_INT t)))`);;
let LIST_INT = new_recursive_definition list_RECURSION LIST_INT_term;;

(*
 * Translate a parallel action into an interleaved action
 *)
let ID_INT = new_definition
  (`ID_INT = ([]:(stype->stype)list)`);;


(*########################################################################
 #                                                                      #
 #      Iterated interleaving                                           #
 #                                                                      #
 #        << i : 1 <= i <= N :: Pr[i] >>                                #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        IteratedINTerleaving low n Pr[.] -->                          #
 #              Pr[low] [] ... [] Pr[low+n-1]                           #
 #                                                                      #
 ########################################################################*)

(*
 * Iterated interleaved assignment
 *)
let ITER_INT0_term =
 (`(ITER_INT0 (low:num) 0 (f:num->bool) (fi:num->(stype->stype)list) = ID_INT) /\
   (ITER_INT0  low (SUC n) f             fi =
      (if (f low) then (INT_INT (fi low) (ITER_INT0 (SUC low) n f fi))
                  else (ITER_INT0 (SUC low) n f fi)))`);;
let ITER_INT0 = new_recursive_definition num_RECURSION ITER_INT0_term;;

let ITER_INT = new_definition
  (`ITER_INT low high (f:num->bool) (fi:num->(stype->stype)list) =
           ITER_INT0 low ((1+high)-low) f fi`);;

(*#######################################################################
 #                                                                      #
 #      Absolute and relative Label predicates                          #
 #                                                                      #
 #      AT,AFTER      : At first, first following action                #
 #      IN            : Inside action                                   #
 #      BEFORE,FOLLOW : Strictly before,following action                #
 #                                                                      #
 ########################################################################*)

let AT_LBL = new_definition
  (`AT_LBL ds pc (label:num#num) =
      (LOC_EXP pc ds:stype->num) =* K (FST label)`);;

let AFTER_LBL = new_definition
  (`AFTER_LBL ds pc (label:num#num) =
      (LOC_EXP pc ds:stype->num) =* K (SND label)`);;

let BEFORE_LBL = new_definition
  (`BEFORE_LBL ds pc (label:num#num) =
       (LOC_EXP pc ds:stype->num) <* K (FST label)`);;

let INSIDE_LBL = new_definition
  (`INSIDE_LBL ds pc (label:num#num) =
      ((LOC_EXP pc ds:stype->num) >=* K (FST label)) /\*
      ((LOC_EXP pc ds:stype->num) <* K (SND label))`);;

let FOLLOW_LBL = new_definition
  (`FOLLOW_LBL ds pc (label:num#num) =
       (LOC_EXP pc ds:stype->num) >=* K (SND label)`);;

(* Absolute label handler *)
let AT_ABS = new_definition
  (`AT_ABS (pc:stype->num) (l:num) (u:num) = (pc =* K l)`);;

let AT_REL = new_definition
  (`AT_REL (pc:(stype->num)#((stype->num)->stype->stype->stype))
           (label:(num#num)) =
      VAR_EXP pc =* K (FST label)`);;

let AFTER_ABS = new_definition
  (`AFTER_ABS (pc:stype->num) (l:num) (u:num) = (pc =* K u)`);;

let AFTER_REL = new_definition
  (`AFTER_REL (pc:(stype->num)#((stype->num)->stype->stype->stype))
              (label:(num#num)) =
       VAR_EXP pc =* K (SND label)`);;

let BEFORE_ABS = new_definition
  (`BeforeAbs (pc:stype->num) (l:num) (u:num) = (pc <* K l)`);;

let BEFORE_REL = new_definition
  (`BEFORE_REL (pc:(stype->num)#((stype->num)->stype->stype->stype))
               (label:(num#num)) =
          VAR_EXP pc <* K (FST label)`);;

let INSIDE_ABS = new_definition
  (`INSIDE_ABS (pc:stype->num) (l:num) (u:num) =
        (pc >=* K l) /\* (pc <* K u)`);;

let INSIDE_REL = new_definition
  (`INSIDE_REL (pc:(stype->num)#((stype->num)->stype->stype->stype))
               (label:(num#num)) =
         (VAR_EXP pc >=* K (FST label)) /\*
         (VAR_EXP pc  <* K (SND label))`);;

let FOLLOW_ABS = new_definition
  (`FollowAbs (pc:stype->num) (l:num) (u:num) = (pc >=* K l)`);;

let FOLLOW_REL = new_definition
  (`FOLLOW_REL (pc:(stype->num)#((stype->num)->stype->stype->stype))
               (label:(num#num)) =
       VAR_EXP pc >=* K (SND label)`);;

(*########################################################################
 #                                                                      #
 #      Restricted UNLESS                                               #
 #                                                                      #
 #        (p UNLESS{valid} q) Pr                                        #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        RESTRICTED_UNLESS valid p q Pr =                              #
 #              {p /\ valid /\ ~q)} Pr {p \/ q}                         #
 #                                                                      #
 ########################################################################*)

let RESTRICTED_UNLESS_STMT = new_definition
  (`RESTRICTED_UNLESS_STMT v p q st =
       (!s:'state. p s /\ v s /\ ~(q s) ==> p (st s) \/ q (st s))`);;

let RESTRICTED_UNLESS_term =
 (`(RESTRICTED_UNLESS (v:'state->bool) p q []           = T) /\
   (RESTRICTED_UNLESS (v:'state->bool) p q (CONS st Pr) =
     (RESTRICTED_UNLESS_STMT v p q st /\ RESTRICTED_UNLESS v p q Pr))`);;
let RESTRICTED_UNLESS =
   new_recursive_definition list_RECURSION RESTRICTED_UNLESS_term;;

(*#######################################################################
 #                                                                      #
 #      RESTRICTED STABLE                                               #
 #                                                                      #
 #        (p STABLE{valid} q) Pr                                        #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        RESTRICTED_STABLE valid p q Pr =                              #
 #              {p /\ valid} Pr {p}                                     #
 #                                                                      #
 ########################################################################*)
let RESTRICTED_STABLE_STMT = new_definition
  (`RESTRICTED_STABLE_STMT v p st =
       (!s:'state. p s /\ v s ==> p (st s))`);;

let RESTRICTED_STABLE_term =
 (`(RESTRICTED_STABLE (v:'state->bool) p [] = T) /\
   (RESTRICTED_STABLE (v:'state->bool) p (CONS st Pr) =
     (RESTRICTED_STABLE_STMT v p st /\ RESTRICTED_STABLE      v p Pr))`);;
let RESTRICTED_STABLE =
   new_recursive_definition list_RECURSION RESTRICTED_STABLE_term;;

(*########################################################################
 #                                                                      #
 #      RESTRICTED EXISTS_TRANSITION                                    #
 #                                                                      #
 #        (p EXISTS_TRANSITION{valid} q) Pr                             #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        RESTRICTED_EXISTS_TRANSITION valid p q Pr =                   #
 #              ?st In Pr. {p /\ valid /\ ~q} Pr {q}                    #
 #                                                                      #
 ########################################################################*)
let RESTRICTED_EXISTS_TRANSITION_STMT = new_definition
  (`RESTRICTED_EXISTS_TRANSITION_STMT v p q st =
       (!s:'state. p s /\ v s /\ ~(q s) ==> q (st s))`);;

let RESTRICTED_EXISTS_TRANSITION_term =
 (`(RESTRICTED_EXISTS_TRANSITION (v:'state->bool) p q [] = F) /\
   (RESTRICTED_EXISTS_TRANSITION (v:'state->bool) p q (CONS st Pr) =
      (RESTRICTED_EXISTS_TRANSITION_STMT v p q st \/
       RESTRICTED_EXISTS_TRANSITION      v p q Pr))`);;
let RESTRICTED_EXISTS_TRANSITION =
   new_recursive_definition list_RECURSION RESTRICTED_EXISTS_TRANSITION_term;;

(*########################################################################
 #                                                                      #
 #      RESTRICTED ENSURES                                              #
 #                                                                      #
 #        (p ENSURES{valid} q) Pr                                       #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        RESTRICTED_ENSURES valid p q Pr =                             #
 #              RESTRICTED_UNLESS valid p q Pr /\                       #
 #              RESTRICTED_EXISTS_TRANSITION valid p q Pr               #
 #                                                                      #
 ########################################################################*)
let RESTRICTED_ENSURES = new_definition
  (`RESTRICTED_ENSURES (v:'state->bool) p q Pr =
      (RESTRICTED_UNLESS            v p q Pr /\
       RESTRICTED_EXISTS_TRANSITION v p q Pr)`);;

(*########################################################################
 #                                                                      #
 #      RESTRICTED LEADSTO                                              #
 #                                                                      #
 #        (p LEADSTO{valid} q) Pr                                       #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        RESTRICTED_LEADSTO valid p q Pr =                             #
 #              (p /\ valid p) LEADSTO q Pr /\                          #
 #                                                                      #
 ########################################################################*)
let RESTRICTED_LEADSTO = new_definition
  (`RESTRICTED_LEADSTO (v:'state->bool) p q Pr =
        (((p /\* v) LEADSTO q) Pr)`);;

(*########################################################################
 #                                                                      #
 #      Valid                                                           #
 #                                                                      #
 #        Valid p                                                       #
 #                                                                      #
 #      is defined as:                                                  #
 #                                                                      #
 #        Valid p =                                                     #
 #              !s. p s                                                 #
 #                                                                      #
 ########################################################################*)
let VALID = new_definition
  (`VALID (p:'state->bool) = !s. p s`);;

let TRIPLE_term =
 (`(TRIPLE (p:'state->bool) q [] = T) /\
   (TRIPLE p q (CONS (st:'state->'state) Pr) =
     ((!s. p s ==> q(st s)) /\ TRIPLE p q Pr))`);;
let RESTRICTED_TRIPLE =
   new_recursive_definition list_RECURSION TRIPLE_term;;

(*########################################################################
 #                                                                      #
 #      SUMMA lwb len filter body =                                     #
 #        Body(lwb) + ... Body(i) ... + Body(lwb+len-1) , when filter(i)#
 #                                                                      #
 #      SUMMA lwb 0 f b = 0                                             #
 #      SUMMA lwb (SUC n) f b = (f lwb => b lwb | 0) + SUMMA lwb n f b  #
 #                                                                      #
 ########################################################################*)
let SUMMA0_term =
 (`(SUMMA0 lwb 0 f b = 0) /\
   (SUMMA0 lwb (SUC n) f b =
          ((if (f lwb) then (b lwb) else 0) + (SUMMA0 (SUC lwb) n f b)))`);;
let SUMMA0 = new_recursive_definition num_RECURSION SUMMA0_term;;

let SUMMA = new_definition
  (`SUMMA lwb upb f b = SUMMA0 lwb ((1 + upb)-lwb) f b`);;

let SUMMA_S = new_definition
  (`SUMMA_S lwb upb f b (s:'state) =
          SUMMA (lwb s) (upb s) (\i. f i s) (\i. b i s)`);;

(*########################################################################
 #                                                                      #
 #      MULTA lwb len filter body =                                     #
 #        Body(lwb) * ... Body(i) ... * Body(lwb+len-1) , when filter(i)#
 #                                                                      #
 #      MULTA lwb 0 f b = 1                                             #
 #      MULTA lwb (SUC n) f b = (f lwb => b lwb | 1) * MULTA lwb n f b  #
 #                                                                      #
 ########################################################################*)
let MULTA0_term =
 (`(MULTA0 lwb 0 f b = 1) /\
   (MULTA0 lwb (SUC n) f b =
      ((if (f lwb) then (b lwb) else 1) * (MULTA0 (SUC lwb) n f b)))`);;
let MULTA0 = new_recursive_definition num_RECURSION MULTA0_term;;

let MULTA = new_definition
  (`MULTA lwb upb f b = MULTA0 lwb ((1 + upb)-lwb) f b`);;

let MULTA_S = new_definition
  (`MULTA_S lwb upb f b (s:'state) =
          MULTA (lwb s) (upb s) (\i. f i s) (\i. b i s)`);;

(*########################################################################
 #                                                                      #
 #      CONJA lwb len filter body =                                     #
 #        Body(lwb) & ... Body(i) ... & Body(lwb+len-1) , when filter(i)#
 #                                                                      #
 #      CONJA lwb 0 f b = T                                             #
 #      CONJA lwb (SUC n) f b = (f lwb => b lwb | 1) & CONJA lwb n f b  #
 #                                                                      #
 ########################################################################*)
let CONJA0_term =
 (`(CONJA0 lwb 0 f b = T) /\
   (CONJA0 lwb (SUC n) f b =
     ((if (f lwb) then (b lwb) else T) /\ (CONJA0 (SUC lwb) n f b)))`);;
let CONJA0 = new_recursive_definition num_RECURSION CONJA0_term;;

let CONJA = new_definition
  (`CONJA lwb upb f b = CONJA0 lwb ((1 + upb)-lwb) f b`);;

let CONJA_S = new_definition
  (`CONJA_S lwb upb f b (s:'state) =
          CONJA (lwb s) (upb s) (\i. f i s) (\i. b i s)`);;

(*########################################################################
 #                                                                      #
 #      DISJA lwb len filter body =                                     #
 #        Body(lwb) | ... Body(i) ... | Body(lwb+len-1) , when filter(i)#
 #                                                                      #
 #      DISJA lwb 0 f b = F                                             #
 #      DISJA lwb (SUC n) f b = (f lwb => b lwb | 1) | DISJA lwb n f b  #
 #                                                                      #
 ########################################################################*)
let DISJA0_term =
 (`(DISJA0 lwb 0 f b = F) /\
   (DISJA0 lwb (SUC n) f b =
      ((if (f lwb) then (b lwb) else F) \/ (DISJA0 (SUC lwb) n f b)))`);;
let DISJA0 = new_recursive_definition num_RECURSION DISJA0_term;;

let DISJA = new_definition
  (`DISJA lwb upb f b = DISJA0 lwb ((1 + upb)-lwb) f b`);;

let DISJA_S = new_definition
  (`DISJA_S lwb upb f b (s:'state) =
          DISJA (lwb s) (upb s) (\i. f i s) (\i. b i s)`);;

(*---------------------------------------------------------------------------*)
(*
  Miscellaneous
*)
(*---------------------------------------------------------------------------*)
(*
 * Test for list membership
 *)
let MEMBER_term =
 (`(MEMBER (x:'a) []    = F) /\
   (MEMBER x (CONS h t) = ((x=h) \/ (MEMBER x t)))`);;
let MEMBER = new_recursive_definition list_RECURSION MEMBER_term;;

(*
 * Test for unique elements in list
 *)
let UNIQUE_term =
 (`(UNIQUE []              = T) /\
   (UNIQUE (CONS (h:'a) t) = ((~(MEMBER h t)) /\ UNIQUE t))`);;
let UNIQUE = new_recursive_definition list_RECURSION UNIQUE_term;;
