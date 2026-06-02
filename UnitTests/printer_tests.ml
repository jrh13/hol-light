(* ========================================================================= *)
(*                  HOL Light printer tests                                  *)
(*                                                                           *)
(*  Verifies that pp_print_term produces the expected text for a corpus of   *)
(*  representative term shapes. Each case exercises a specific code path in  *)
(*  printer.ml: phase A (numerals, lists, strings, gabs), phase B (name      *)
(*  dispatch on EMPTY/UNIV/INSERT/GSPEC/LET/DECIMAL/_MATCH/_FUNCTION/COND),   *)
(*  phase C (prefix/binder/infix), phase D (atoms and generic application).  *)
(*                                                                           *)
(*  Run via:                                                                 *)
(*    make UnitTests/printer_tests && ./UnitTests/printer_tests              *)
(* ========================================================================= *)

(* Set a wide margin so line-wrapping doesn't depend on tty width. *)
Format.set_margin 1000000;;

let failures = ref 0;;
let total = ref 0;;

let check label input expected =
  incr total;
  let actual =
    try string_of_term (parse_term input)
    with e ->
      Printf.sprintf "<<parse-fail: %s>>" (Printexc.to_string e) in
  if actual <> expected then
   (incr failures;
    Printf.printf "FAIL %s\n  input    = %s\n  expected = %s\n  actual   = %s\n"
      label input expected actual);;

(* ------------------------------------------------------------------------- *)
(* Phase A: numerals, lists, strings, top-level gabs.                        *)
(* ------------------------------------------------------------------------- *)

check "numeral.zero"     "0:num"            "0";;
check "numeral.large"    "12345:num"        "12345";;
check "list.nil"         "[]:num list"      "[]";;
check "list.three"       "[1;2;3]:num list" "[1; 2; 3]";;
check "list.nested"      "[[1;2];[3;4]]:(num list)list"
                         "[[1; 2]; [3; 4]]";;
check "list.tyvar"       "[(x:A);(y:A);(z:A)]:A list"
                         "[x; y; z]";;
check "gabs.tuple"       "(\\(x,y). x + y) ((1:num),(2:num))"
                         "(\\(x,y). x + y) (1,2)";;
check "gabs.tyvar"       "\\((x:A),(y:B)). (x,y)"
                         "\\(x,y). x,y";;

(* ------------------------------------------------------------------------- *)
(* Phase B: name dispatch.                                                   *)
(* ------------------------------------------------------------------------- *)

check "univ.num"         "(:num)"           "(:num)";;
check "univ.bool"        "(:bool)"          "(:bool)";;
check "univ.tyvar"       "(:A)"             "(:A)";;
check "set.three"        "{1,2,3}:num->bool"  "{1, 2, 3}";;
check "set.compr"        "{(x:num) | x > 0}"  "{x | x > 0}";;
check "set.compr.pair"   "{(x:num,y:num) | x + y = 1}"
                         "{x,y | x + y = 1}";;
check "let.simple"       "let x = 1 in x + (2:num)"
                         "let x = 1 in x + 2";;
check "let.chained"      "let x = 1 in let y = 2 in x + (y:num)"
                         "let x = 1 in let y = 2 in x + y";;
check "let.parallel"     "let x = 1 and y = 2 in x + (y:num)"
                         "let x = 1 and y = 2 in x + y";;
check "decimal"          "#1.5"             "#1.5";;
check "match"            "match (x:num) with 0 -> T | _ -> F"
                         "match x with 0 -> true | _ -> false";;
check "function"         "function (0:num) -> T | _ -> F"
                         "function 0 -> true | _ -> false";;
check "cond.simple"      "if (x:num) = 0 then 1 else 2"
                         "if x = 0 then 1 else 2";;
check "cond.cascade"
  "if (a:num) = 0 then 1 else if a = 1 then 2 else if a = 2 then 3 else 4"
  "if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 3 else 4";;

(* ------------------------------------------------------------------------- *)
(* Phase C: prefix, binder, infix.                                           *)
(* ------------------------------------------------------------------------- *)

check "prefix.neg"       "~T"               "~true";;
check "prefix.double"    "~ (~T)"           "~ ~true";;
check "prefix.real_neg"  "-- &3"            "-- &3";;
check "prefix.real_neg.parens" "-- (&3 + &4)" "--(&3 + &4)";;
check "infix.and"        "T /\\ F"          "true /\\ false";;
check "infix.implies"    "p ==> q ==> r"    "p ==> q ==> r";;
check "infix.add"        "(x:num) + 1"      "x + 1";;
check "infix.add.assoc"  "(a:num) + b + c + d"  "a + b + c + d";;
check "infix.sub.assoc"  "(a:num) - b - c"      "a - b - c";;
check "infix.mixed.prec" "(a:num) + b * c"      "a + b * c";;

(* Associativity tests. In HOL Light, +, *, /\, ==> are right-associative on
   num/bool, so the natural right-grouping prints without parens but the
   left-grouping prints with parens. Subtraction (-) is left-associative.
   See arith.ml: parse_as_infix("+",(16,"right")) etc. *)

(* + on num: right-associative. *)
check "infix.add.right_assoc"
  "(x:num) + (y + z)"      "x + y + z";;
check "infix.add.left_grouping"
  "((x:num) + y) + z"      "(x + y) + z";;
(* * on num: right-associative. *)
check "infix.mul.right_assoc"
  "(x:num) * (y * z)"      "x * y * z";;
check "infix.mul.left_grouping"
  "((x:num) * y) * z"      "(x * y) * z";;
(* - on num: left-associative. *)
check "infix.sub.left_assoc"
  "((x:num) - y) - z"      "x - y - z";;
check "infix.sub.right_grouping"
  "(x:num) - (y - z)"      "x - (y - z)";;
(* EXP on num: left-associative. *)
check "infix.exp.left_assoc"
  "((x:num) EXP y) EXP z"  "x EXP y EXP z";;
check "infix.exp.right_grouping"
  "(x:num) EXP (y EXP z)"  "x EXP (y EXP z)";;
(* DIV on num: left-associative. *)
check "infix.div.left_assoc"
  "((x:num) DIV y) DIV z"  "x DIV y DIV z";;
check "infix.div.right_grouping"
  "(x:num) DIV (y DIV z)"  "x DIV (y DIV z)";;
(* MOD on num: left-associative. *)
check "infix.mod.left_assoc"
  "((x:num) MOD y) MOD z"  "x MOD y MOD z";;
check "infix.mod.right_grouping"
  "(x:num) MOD (y MOD z)"  "x MOD (y MOD z)";;
(* ==> is right-associative. *)
check "infix.imp.right_assoc"
  "p ==> (q ==> r)"        "p ==> q ==> r";;
check "infix.imp.left_grouping"
  "(p ==> q) ==> r"        "(p ==> q) ==> r";;
(* /\ is right-associative. *)
check "infix.and.right_assoc"
  "p /\\ (q /\\ r)"        "p /\\ q /\\ r";;
check "infix.and.left_grouping"
  "(p /\\ q) /\\ r"        "(p /\\ q) /\\ r";;
(* Mixed precedence: * binds tighter than +, so a + b * c needs no parens
   but (a + b) * c does. *)
check "infix.mix.add_then_mul"
  "((a:num) + b) * c"      "(a + b) * c";;
check "infix.mix.mul_then_add"
  "(a:num) * b + c"        "a * b + c";;
check "infix.mix.mul_then_add.parens"
  "(a:num) * (b + c)"      "a * (b + c)";;
(* Mixed +/- on num. + has prec 16 right-assoc; - has prec 18 left-assoc, so
   - binds tighter than +. *)
check "infix.mix.add_sub.left"
  "((x:num) + y) - z"      "(x + y) - z";;
check "infix.mix.add_sub.right"
  "(x:num) + (y - z)"      "x + y - z";;
check "infix.mix.sub_add.left"
  "((x:num) - y) + z"      "x - y + z";;
check "infix.mix.sub_add.right"
  "(x:num) - (y + z)"      "x - (y + z)";;

(* The same arithmetic operators on int and real, after prioritize_int /
   prioritize_real. The interface remaps +,-,*,= to int_*/real_* but the
   printer should still emit the symbolic infix. We restore via
   prioritize_num() at the end so subsequent tests see the default state. *)

prioritize_int();;
check "prioritize.int.add"
  "(x:int) + y + z"        "x + y + z";;
check "prioritize.int.add_sub"
  "((x:int) + y) - z"      "(x + y) - z";;
check "prioritize.int.mul_add"
  "(x:int) * y + z"        "x * y + z";;

check "infix.int.div.left_assoc"
  "((x:int) div y) div z"  "x div y div z";;
check "infix.int.div.right_grouping"
  "(x:int) div (y div z)"  "x div (y div z)";;
check "infix.int.rem.left_assoc"
  "((x:int) rem y) rem z"  "x rem y rem z";;
check "infix.int.pow.left_assoc"
  "((x:int) pow y) pow z"  "x pow y pow z";;
check "infix.int.pow.right_grouping"
  "(x:int) pow (y EXP z)"  "x pow (y EXP z)";;

prioritize_real();;
check "prioritize.real.add"
  "(x:real) + y + z"       "x + y + z";;
check "prioritize.real.add_sub"
  "((x:real) + y) - z"     "(x + y) - z";;
check "prioritize.real.mul_add"
  "(x:real) * y + z"       "x * y + z";;
check "prioritize.real.div"
  "(x:real) / (y * z)"     "x / (y * z)";;

check "infix.real.div.left_assoc"
  "((x:real) / y) / z"     "x / y / z";;
check "infix.real.div.right_grouping"
  "(x:real) / (y / z)"     "x / (y / z)";;
check "infix.real.pow.left_assoc"
  "((x:real) pow y) pow z" "x pow y pow z";;
check "infix.real.pow.right_grouping"
  "(x:real) pow (y EXP z)" "x pow (y EXP z)";;
check "infix.real.zpow.left_assoc"
  "((x:real) zpow y) zpow z" "x zpow y zpow z";;

(* Restore default num-priority for subsequent tests. *)
prioritize_num();;
check "infix.real.add"   "&1 + &2"          "&1 + &2";;
check "infix.real.div"   "&5 / &2"          "&5 / &2";;
check "infix.real.dec"   "#1.5 + #2.25"     "#1.5 + #2.25";;
check "infix.eq"         "(x:num) = (y:num)" "x = y";;
check "infix.iff"        "(T <=> F)"        "true <=> false";;
check "infix.append"     "APPEND [1;2] [3;4]:num list"
                         "APPEND [1; 2] [3; 4]";;
check "binder.exists"    "?x. x = (3:num)"  "exists x. x = 3";;
check "binder.forall"    "!x. x + 0 = x"    "forall x. x + 0 = x";;
check "binder.lambda"    "\\x. x + 1"       "\\x. x + 1";;
check "binder.lambda.multi"
                         "\\x y z. x + y + (z:num)"
                         "\\x y z. x + y + z";;
check "binder.uexists"   "?!x. x = (5:num)" "existsunique x. x = 5";;
check "binder.epsilon"   "@x. x > (0:num)"  "@x. x > 0";;
check "binder.forall.multi"
  "!x y z. x + y + z = (z:num) + y + x"
  "forall x y z. x + y + z = z + y + x";;

(* ------------------------------------------------------------------------- *)
(* Phase D: atoms and generic applications.                                  *)
(* ------------------------------------------------------------------------- *)

check "app.curried"      "(f:num->num->num->num) (a:num) (b:num) (c:num)"
                         "f a b c";;
check "app.deep"
  "(f:num->num) ((g:num->num) ((h:num->num) ((i:num->num) ((j:num->num) (x:num)))))"
  "f (g (h (i (j x))))";;
check "app.parens"       "(f:num->num->num) ((a:num) + b) ((c:num) * d)"
                         "f (a + b) (c * d)";;

(* Polymorphic atoms with user-named type variables — the printer should not
   add type annotations because the types do not contain invented type
   variables (their names start with letters, not '?'). *)
check "atom.tyvar.app"
  "(f:A->A->A->A) (x:A) (y:A) (z:A)"
  "f x y z";;
check "atom.tyvar.lambda"
  "\\(x:A). x"
  "\\x. x";;

(* ------------------------------------------------------------------------- *)
(* print_types_of_subterms = 2: every constant and variable is annotated     *)
(* with its type. See Help/print_types_of_subterms.hlp for details.          *)
(* ------------------------------------------------------------------------- *)

let saved_show_types = !print_types_of_subterms;;
print_types_of_subterms := 2;;

check "show_types.var"
  "(x:num)"                "(x:num)";;
check "show_types.const"
  "T"                      "(true:bool)";;
check "show_types.bool_const_F"
  "F"                      "(false:bool)";;
check "show_types.app"
  "(f:num->num) (x:num)"
  "(f:num->num) (x:num)";;
check "show_types.infix"
  "(x:num) + (y:num)"
  "(x:num) + (y:num)";;
check "show_types.lambda"
  "\\(x:num). x + (1:num)"
  "\\(x:num). (x:num) + 1";;
check "show_types.binder"
  "!(x:num). x = x"
  "forall (x:num). (x:num) = (x:num)";;
check "show_types.tyvar"
  "(f:A->A) (x:A)"
  "(f:A->A) (x:A)";;
(* Numerals (phase A) are printed as bare digits regardless of
   print_types_of_subterms — see print_numeral in printer.ml. *)
check "show_types.list_numerals"
  "[(1:num); 2; 3]"
  "[1; 2; 3]";;
check "show_types.cond"
  "if (b:bool) then (1:num) else 2"
  "if (b:bool) then 1 else 2";;
check "show_types.let"
  "let (x:num) = 1 in x + 2"
  "let (x:num) = 1 in (x:num) + 2";;

check "show_types.real_of_num"
  "&2"
  "(& :num->real)2";;
check "show_types.real_neg"
  "-- &2"
  "-- (& :num->real)2";;
check "show_types.real_of_num.add"
  "&1 + &2"
  "(& :num->real)1 + (& :num->real)2";;

print_types_of_subterms := saved_show_types;;

(* ------------------------------------------------------------------------- *)
(* Round-trip of the symbolic-head fix: parse_term o string_of_term must be  *)
(* the identity on the printed form even with print_types_of_subterms := 2.  *)
(* Without the space before ":", "&:" lexes as a single Ident and the        *)
(* re-parse would fail or misinterpret the term.                             *)
(* ------------------------------------------------------------------------- *)

let check_roundtrip label tm =
  incr total;
  let printed =
    let saved = !print_types_of_subterms in
    print_types_of_subterms := 2;
    let s = string_of_term tm in
    print_types_of_subterms := saved; s in
  let reparsed =
    try parse_term printed
    with e ->
      incr failures;
      Printf.printf "FAIL %s\n  printed = %s\n  parse error: %s\n"
        label printed (Printexc.to_string e);
      tm in
  if not (aconv reparsed tm) then
   (incr failures;
    Printf.printf "FAIL %s\n  printed  = %s\n  reparsed != original\n"
      label printed);;

let real_of_num_tm = mk_const("real_of_num",[]);;
let real_neg_tm = mk_const("real_neg",[]);;
let real_add_tm = mk_const("real_add",[]);;
let amp_2 = mk_comb(real_of_num_tm,mk_numeral(num 2));;
let amp_1 = mk_comb(real_of_num_tm,mk_numeral(num 1));;

check_roundtrip "roundtrip.real_of_num" amp_2;;
check_roundtrip "roundtrip.real_neg"    (mk_comb(real_neg_tm,amp_2));;
check_roundtrip "roundtrip.real_add"    (mk_binop real_add_tm amp_1 amp_2);;

(* ------------------------------------------------------------------------- *)
(* Summary.                                                                  *)
(* ------------------------------------------------------------------------- *)

(if !failures = 0 then
   Printf.printf "OK: %d/%d printer tests passed\n" !total !total
 else
  (Printf.printf "FAILED: %d/%d printer tests failed\n" !failures !total;
   exit 1));;
