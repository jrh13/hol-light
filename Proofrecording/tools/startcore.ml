
set_jrh_lexer;;                                        (* Uppercase idents   *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };; (* Up the stack size  *)

include Num;;

Sys.catch_break true;;
