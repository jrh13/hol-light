Topdirs.dir_use Format.std_formatter "topfind";;

(* Don't load compiler-libs.common because it conflicts with toplevel's Env. *)
(* See also: https://github.com/ocaml/ocaml/issues/12271 *)
Topfind.don't_load ["compiler-libs.common"];;

Topfind.load_deeply ["camlp5"];;
Topdirs.dir_load Format.std_formatter "camlp5o.cma";;
