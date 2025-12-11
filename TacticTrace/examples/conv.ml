let simple_conv t = NUM_REDUCE_CONV t;;
(* simple_conv2 won't appear as json trace because `e=e` is ignored by export fns *)
let simple_conv2 = fun (t:term) -> REFL t;;
(* JSON trace of these must have the 'term' input at arg_values, arg_exprs, etc. *)
let simple_conv3 = NUM_REDUCE_CONV;;
let simple_conv4 : conv =
  let tmp_conv : conv = fun tm -> NUM_REDUCE_CONV tm in
  tmp_conv;;

let thm = prove(`1+1=2`, CONV_TAC (LAND_CONV simple_conv2) THEN ACCEPT_TAC (simple_conv `1+1`));;
let thm2 = simple_conv3 `2+3`;;
let thm3 = prove(`1+1=2`, CONV_TAC simple_conv4);;
