parse_as_prefix "Not";;
parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(15,"right"));;
parse_as_infix("-->",(14,"right"));;
parse_as_infix("<->",(13,"right"));;

let false_def = define `False = \t:num. F`;;
let true_def = define `True = \t:num. T`;;
let not_def = define `Not p = \t:num. ~(p t)`;;
let and_def = define `p && q = \t:num. p t /\ q t`;;
let or_def = define `p || q = \t:num. p t \/ q t`;;
let imp_def = define `p --> q = \t:num. p t ==> q t`;;
let iff_def = define `p <-> q = \t:num. p t <=> q t`;;

let forever = define `forever p = \t:num. !t'. t <= t' ==> p t'`;;
let sometime = define `sometime p = \t:num. ?t'. t <= t' /\ p t'`;;

let next = define `next p = \t:num. p(t + 1)`;;

parse_as_infix("until",(17,"right"));;

let until = define
  `p until q =
    \t:num. ?t'. t <= t' /\ (!t''. t <= t'' /\ t'' < t' ==> p t'') /\ q t'`;;
