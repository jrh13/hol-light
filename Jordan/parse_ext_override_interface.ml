(*
        Author: Thomas C. Hales

        As a new user of HOL-light, I have had a difficult time distinguishing
        between the different uses of overloaded operators such as
        (+), ( * ), (abs) (&), and so forth.

        Their interpretation is context dependent, according to which of
        prioritize_num, prioritize_int, and prioritize_real was most
        recently called.

        This file removes all ambiguities in notation.
        Following the usage of CAML, we append a dot to operations on real
        numbers so that addition is (+.), etc.

        In the same way, we remove ambiguities between natural numbers and
        integers by appending a character.  We have chosen to use
        the character `|` for natural number operations 
        and the character `:` for integer operations.

        The character `&` continues to denote the embedding of 
        natural numbers into the integers or reals.

        HOL-light parsing does not permit an operator mixing alphanumeric
        characters with symbols.  Thus, we were not able to use (abs.)
        and (abs:) for the absolute value.  Instead we adapt the usual notation
        |x| for absolute value and write it in prefix notation ||: and
        ||. for the integer and real absolute value functions respectively.

        In deference to HOL-light notation, we use ** for the exponential
        function.  There are three versions: ( **| ), ( **: ), and ( **. ).

*)

(* natural number operations *)



let unambiguous_interface() = 
parse_as_infix("+|",(16,"right"));
parse_as_infix("-|",(18,"left"));
parse_as_infix("*|",(20,"right"));
parse_as_infix("**|",(24,"left")); (* EXP *)
parse_as_infix("/|",(22,"right")); (* DIV *)
parse_as_infix("%|",(22,"left"));  (* MOD *)
parse_as_infix("<|",(12,"right"));
parse_as_infix("<=|",(12,"right"));
parse_as_infix(">|",(12,"right"));
parse_as_infix(">=|",(12,"right"));
override_interface("+|",`(+):num->(num->num)`);
override_interface("-|",`(-):num->(num->num)`);
override_interface("*|",`( * ):num->(num->num)`);
override_interface("**|",`(EXP):num->(num->num)`);
override_interface("/|",`(DIV):num->(num->num)`);
override_interface("%|",`(MOD):num->(num->num)`);
override_interface("<|",`(<):num->(num->bool)`);
override_interface("<=|",`(<=):num->(num->bool)`);
override_interface(">|",`(>):num->(num->bool)`);
override_interface(">=|",`(>=):num->(num->bool)`);
(* integer operations *)
parse_as_infix("+:",(16,"right"));
parse_as_infix("-:",(18,"left"));
parse_as_infix("*:",(20,"right"));
parse_as_infix("**:",(24,"left")); 
parse_as_infix("<:",(12,"right"));
parse_as_infix("<=:",(12,"right"));
parse_as_infix(">:",(12,"right"));
parse_as_infix(">=:",(12,"right"));
override_interface("+:",`int_add:int->int->int`);
override_interface("-:",`int_sub:int->int->int`);
override_interface("*:",`int_mul:int->int->int`);
override_interface("**:",`int_pow:int->num->int`);
(* boolean *)
override_interface("<:",`int_lt:int->int->bool`);
override_interface("<=:",`int_le:int->int->bool`);
override_interface(">:",`int_gt:int->int->bool`);
override_interface(">=:",`int_ge:int->int->bool`);
(* unary *)
override_interface("--:",`int_neg:int->int`);
override_interface("&:",`int_of_num:num->int`);
override_interface("||:",`int_abs:int->int`);
(* real number operations *)
parse_as_infix("+.",(16,"right"));
parse_as_infix("-.",(18,"left"));
parse_as_infix("*.",(20,"right"));
parse_as_infix("**.",(24,"left")); 
parse_as_infix("<.",(12,"right"));
parse_as_infix("<=.",(12,"right"));
parse_as_infix(">.",(12,"right"));
parse_as_infix(">=.",(12,"right"));
override_interface("+.",`real_add:real->real->real`);
override_interface("-.",`real_sub:real->real->real`);
override_interface("*.",`real_mul:real->real->real`);
override_interface("**.",`real_pow:real->num->real`);
(* boolean *)
override_interface("<.",`real_lt:real->real->bool`);
override_interface("<=.",`real_le:real->real->bool`);
override_interface(">.",`real_gt:real->real->bool`);
override_interface(">=.",`real_ge:real->real->bool`);
(* unary *)
override_interface("--.",`real_neg:real->real`);
override_interface("&.",`real_of_num:num->real`);
override_interface("||.",`real_abs:real->real`);;

let ambiguous_interface() = 
reduce_interface("+|",`(+):num->(num->num)`);
reduce_interface("-|",`(-):num->(num->num)`);
reduce_interface("*|",`( * ):num->(num->num)`);
reduce_interface("**|",`(EXP):num->(num->num)`);
reduce_interface("/|",`(DIV):num->(num->num)`);
reduce_interface("%|",`(MOD):num->(num->num)`);
reduce_interface("<|",`(<):num->(num->bool)`);
reduce_interface("<=|",`(<=):num->(num->bool)`);
reduce_interface(">|",`(>):num->(num->bool)`);
reduce_interface(">=|",`(>=):num->(num->bool)`);
(* integer operations *)
reduce_interface("+:",`int_add:int->int->int`);
reduce_interface("-:",`int_sub:int->int->int`);
reduce_interface("*:",`int_mul:int->int->int`);
reduce_interface("**:",`int_pow:int->num->int`);
(* boolean *)
reduce_interface("<:",`int_lt:int->int->bool`);
reduce_interface("<=:",`int_le:int->int->bool`);
reduce_interface(">:",`int_gt:int->int->bool`);
reduce_interface(">=:",`int_ge:int->int->bool`);
(* unary *)
reduce_interface("--:",`int_neg:int->int`);
reduce_interface("&:",`int_of_num:num->int`);
reduce_interface("||:",`int_abs:int->int`);
(* real *)
reduce_interface("+.",`real_add:real->real->real`);
reduce_interface("-.",`real_sub:real->real->real`);
reduce_interface("*.",`real_mul:real->real->real`);
reduce_interface("**.",`real_pow:real->num->real`);
(* boolean *)
reduce_interface("<.",`real_lt:real->real->bool`);
reduce_interface("<=.",`real_le:real->real->bool`);
reduce_interface(">.",`real_gt:real->real->bool`);
reduce_interface(">=.",`real_ge:real->real->bool`);
(* unary *)
reduce_interface("--.",`real_neg:real->real`);
reduce_interface("&.",`real_of_num:num->real`);
reduce_interface("||.",`real_abs:real->real`);;

(* add to Harrison's priorities the functions pop_priority and get_priority *)
let prioritize_int,prioritize_num,prioritize_real,pop_priority,get_priority = 
  let v = ref ([]:string list) in
  let prioritize_int() = 
  v:= "int"::!v;
  overload_interface ("+",`int_add:int->int->int`);
  overload_interface ("-",`int_sub:int->int->int`);
  overload_interface ("*",`int_mul:int->int->int`);
  overload_interface ("<",`int_lt:int->int->bool`);
  overload_interface ("<=",`int_le:int->int->bool`);
  overload_interface (">",`int_gt:int->int->bool`);
  overload_interface (">=",`int_ge:int->int->bool`);
  overload_interface ("--",`int_neg:int->int`);
  overload_interface ("pow",`int_pow:int->num->int`);
  overload_interface ("abs",`int_abs:int->int`);
  override_interface ("&",`int_of_num:num->int`) and
  prioritize_num() = 
  v:= "num"::!v;
  overload_interface ("+",`(+):num->num->num`);
  overload_interface ("-",`(-):num->num->num`);
  overload_interface ("*",`(*):num->num->num`);
  overload_interface ("<",`(<):num->num->bool`);
  overload_interface ("<=",`(<=):num->num->bool`);
  overload_interface (">",`(>):num->num->bool`);
  overload_interface (">=",`(>=):num->num->bool`) and
  prioritize_real() =
  v:= "real"::!v;
  overload_interface ("+",`real_add:real->real->real`);
  overload_interface ("-",`real_sub:real->real->real`);
  overload_interface ("*",`real_mul:real->real->real`);
  overload_interface ("/",`real_div:real->real->real`);
  overload_interface ("<",`real_lt:real->real->bool`);
  overload_interface ("<=",`real_le:real->real->bool`);
  overload_interface (">",`real_gt:real->real->bool`);
  overload_interface (">=",`real_ge:real->real->bool`);
  overload_interface ("--",`real_neg:real->real`);
  overload_interface ("pow",`real_pow:real->num->real`);
  overload_interface ("inv",`real_inv:real->real`);
  overload_interface ("abs",`real_abs:real->real`);
  override_interface ("&",`real_of_num:num->real`) and
  pop_priority() = 
  if (length !v <= 1) then (print_string "priority unchanged\n") else
  let (a::b::c) = !v in
  v:= (b::c);
  print_string ("priority is now "^b^"\n");
  match a with
    "num" -> prioritize_num() |
    "int" -> prioritize_int() |
    "real"-> prioritize_real()|
    _ -> () and
  get_priority() = 
  if (!v=[]) then "unknown" else
  let (a::b) = !v in a
  in
  prioritize_int,prioritize_num,prioritize_real,pop_priority,get_priority;;





