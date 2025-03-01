
(* Helpers *)

let remove_quotes s =
  let len = String.length s in
  if len >= 2 then String.sub s 1 (len - 2)
  else s;;
