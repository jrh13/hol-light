MESON[]
 `((?x. !y. P(x) <=> P(y)) <=> ((?x. Q(x)) <=> (!y. Q(y)))) <=>
  ((?x. !y. Q(x) <=> Q(y)) <=> ((?x. P(x)) <=> (!y. P(y))))`;;

MESON[]
`(!x y z. P x y /\ P y z ==> P x z) /\
 (!x y z. Q x y /\ Q y z ==> Q x z) /\
 (!x y. P x y ==> P y x) /\
 (!x y. P x y \/ Q x y)
 ==> (!x y. P x y) \/ (!x y. Q x y)`;;

let ewd1062 = MESON[]
 `(!x. x <= x) /\
  (!x y z. x <= y /\ y <= z ==> x <= z) /\
  (!x y. f(x) <= y <=> x <= g(y))
  ==> (!x y. x <= y ==> f(x) <= f(y)) /\
      (!x y. x <= y ==> g(x) <= g(y))`;;

let ewd1062 = MESON[]
 `(!x. R x x) /\
  (!x y z. R x y /\ R y z ==> R x z) /\
  (!x y. R (f x) y <=> R x (g y))
  ==> (!x y. R x y ==> R (f x) (f y)) /\
      (!x y. R x y ==> R (g x) (g y))`;;

MESON[] `(?!x. g(f x) = x) <=> (?!y. f(g y) = y)`;;

MESON [ADD_ASSOC; ADD_SYM] `m + (n + p) = n + (m + p)`;;
