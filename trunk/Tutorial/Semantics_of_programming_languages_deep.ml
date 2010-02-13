let string_INDUCT,string_RECURSION =
  define_type "string = String (int list)";;

let expression_INDUCT,expression_RECURSION = define_type
"expression = Literal num
            | Variable string
            | Plus expression expression
            | Times expression expression";;

let command_INDUCT,command_RECURSION = define_type
  "command = Assign string expression
           | Sequence command command
           | If expression command command
           | While expression command";;

parse_as_infix(";;",(18,"right"));;
parse_as_infix(":=",(20,"right"));;
override_interface(";;",`Sequence`);;
override_interface(":=",`Assign`);;
overload_interface("+",`Plus`);;
overload_interface("*",`Times`);;

let value = define
 `(value (Literal n) s = n) /\
  (value (Variable x) s = s(x)) /\
  (value (e1 + e2) s = value e1 s + value e2 s) /\
  (value (e1 * e2) s = value e1 s * value e2 s)`;;

let sem_RULES,sem_INDUCT,sem_CASES = new_inductive_definition
  `(!x e s s'. s'(x) = value e s /\ (!y. ~(y = x) ==> s'(y) = s(y))
               ==> sem (x := e) s s') /\
   (!c1 c2 s s' s''. sem(c1) s s' /\ sem(c2) s' s'' ==> sem(c1 ;; c2) s s'') /\
   (!e c1 c2 s s'. ~(value e s = 0) /\ sem(c1) s s' ==> sem(If e c1 c2) s s') /\
   (!e c1 c2 s s'. value e s = 0 /\ sem(c2) s s' ==> sem(If e c1 c2) s s') /\
   (!e c s. value e s = 0 ==> sem(While e c) s s) /\
   (!e c s s' s''. ~(value e s = 0) /\ sem(c) s s' /\ sem(While e c) s' s''
                   ==> sem(While e c) s s'')`;;

(**** Fails
  define
   `sem(While e c) s s' <=> if value e s = 0 then (s' = s)
                            else ?s''. sem c s s'' /\ sem(While e c) s'' s'`;;
****)

let DETERMINISM = prove
 (`!c s s' s''. sem c s s' /\ sem c s s'' ==> (s' = s'')`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC sem_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[sem_CASES] THEN
  REWRITE_TAC[distinctness "command"; injectivity "command"] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

let wlp = new_definition
 `wlp c q s <=> !s'. sem c s s' ==> q s'`;;

let terminates = new_definition
 `terminates c s <=> ?s'. sem c s s'`;;

let wp = new_definition
 `wp c q s <=> terminates c s /\ wlp c q s`;;

let WP_TOTAL = prove
 (`!c. (wp c EMPTY = EMPTY)`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; EMPTY] THEN MESON_TAC[]);;

let WP_MONOTONIC = prove
 (`q SUBSET r ==> wp c q SUBSET wp c r`,
  REWRITE_TAC[SUBSET; IN; wp; wlp; terminates] THEN MESON_TAC[]);;

let WP_DISJUNCTIVE = prove
 (`(wp c p) UNION (wp c q) = wp c (p UNION q)`,
  REWRITE_TAC[FUN_EQ_THM; IN; wp; wlp; IN_ELIM_THM; UNION; terminates] THEN
  MESON_TAC[DETERMINISM]);;

let WP_SEQ = prove
 (`!c1 c2 q. wp (c1 ;; c2) = wp c1 o wp c2`,
  REWRITE_TAC[wp; wlp; terminates; FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sem_CASES] THEN
  REWRITE_TAC[injectivity "command"; distinctness "command"] THEN
  MESON_TAC[DETERMINISM]);;

let correct = new_definition
 `correct p c q <=> p SUBSET (wp c q)`;;

let CORRECT_PRESTRENGTH = prove
 (`!p p' c q. p SUBSET p' /\ correct p' c q ==> correct p c q`,
  REWRITE_TAC[correct; SUBSET_TRANS]);;

let CORRECT_POSTWEAK = prove
 (`!p c q q'. correct p c q' /\ q' SUBSET q ==> correct p c q`,
  REWRITE_TAC[correct] THEN MESON_TAC[WP_MONOTONIC; SUBSET_TRANS]);;

let CORRECT_SEQ = prove
 (`!p q r c1 c2.
        correct p c1 r /\ correct r c2 q ==> correct p (c1 ;; c2) q`,
  REWRITE_TAC[correct; WP_SEQ; o_THM] THEN
  MESON_TAC[WP_MONOTONIC; SUBSET_TRANS]);;
