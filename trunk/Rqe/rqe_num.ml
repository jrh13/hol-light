
(* ---------------------------------------------------------------------- *)
(*  Nums                                                                  *)
(* ---------------------------------------------------------------------- *)

let neq = `(=):num->num->bool`;;
let nlt = `(<):num->num->bool`;;
let ngt = `(>):num->num->bool`;;
let nle = `(<=):num->num->bool`;;
let nge = `(>=):num->num->bool`;;
let nm = `( * ):num->num->num`;;
let np = `(+):num->num->num`;;
let nzero = `0`;;
let even_tm = `EVEN`;;
let odd_tm = `ODD`;;


let nmax = new_definition(
 `nmax (n:num) m = if n <= m then m else n`);;

let SUC_1 = prove(
  `1 + x = SUC x`,
(* {{{ Proof *)
  ARITH_TAC);;
(* }}} *)

let even_tm = `EVEN`;;
let odd_tm = `ODD`;;
let PARITY_CONV tm = 
  let k = dest_small_numeral tm in
  if even k then
    prove(mk_comb(even_tm,tm),ARITH_TAC)
  else 
    prove(mk_comb(odd_tm,tm),ARITH_TAC);;
