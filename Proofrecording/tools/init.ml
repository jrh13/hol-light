(* ------------------------------------------------------------------------- *)
(* Set up a quotation expander for my `...` quotes.                          *)
(* ------------------------------------------------------------------------- *)

let quotexpander s =
  if String.sub s 0 1 = ":" then
    "parse_type \""^
    (String.escaped (String.sub s 1 (String.length s - 1)))^"\""
  else "parse_term \""^(String.escaped s)^"\"";;

Quotation.add "tot" (Quotation.ExStr (fun x -> quotexpander));;
