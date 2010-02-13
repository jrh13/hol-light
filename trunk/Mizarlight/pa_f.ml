(* ------------------------------------------------------------------------- *)
(* Some additional infixes to support Freek's "Mizar Light".                 *)
(* ------------------------------------------------------------------------- *)

open Pcaml;

Pcaml.syntax_name.val := "Freek";

Format.print_string "New infixes set up";
Format.print_newline();

EXTEND
  expr: AFTER "<"
   [[ f = expr; "by"; g = expr -> <:expr< ((by $f$) $g$) >>
    | f = expr; "st'"; g = expr -> <:expr< ((st' $f$) $g$) >>
    | f = expr; "st"; g = expr -> <:expr< ((st $f$) $g$) >>
    | f = expr; "at"; g = expr -> <:expr< ((at $f$) $g$) >>
    | f = expr; "from"; g = expr -> <:expr< ((from $f$) $g$) >>
    | f = expr; "using"; g = expr -> <:expr< ((using $f$) $g$) >>
    | f = expr; "proof"; g = expr -> <:expr< ((proof $f$) $g$) >>
    | f = expr; "THEN'"; g = expr -> <:expr< ((then'_ $f$) $g$) >>

   ]];

END;
