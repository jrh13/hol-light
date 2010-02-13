TAUT
 `(~input_a ==> (internal <=> T)) /\
  (~input_b ==> (output <=> internal)) /\
  (input_a ==> (output <=> F)) /\
  (input_b ==> (output <=> F))
  ==> (output <=> ~(input_a \/ input_b))`;;

TAUT
`(i1 /\ i2 <=> a) /\
 (i1 /\ i3 <=> b) /\
 (i2 /\ i3 <=> c) /\
 (i1 /\ c <=> d) /\
 (m /\ r <=> e) /\
 (m /\ w <=> f) /\
 (n /\ w <=> g) /\
 (p /\ w <=> h) /\
 (q /\ w <=> i) /\
 (s /\ x <=> j) /\
 (t /\ x <=> k) /\
 (v /\ x <=> l) /\
 (i1 \/ i2 <=> m) /\
 (i1 \/ i3 <=> n) /\
 (i1 \/ q <=> p) /\
 (i2 \/ i3 <=> q) /\
 (i3 \/ a <=> r) /\
 (a \/ w <=> s) /\
 (b \/ w <=> t) /\
 (d \/ h <=> u) /\
 (c \/ w <=> v) /\
 (~e <=> w) /\
 (~u <=> x) /\
 (i \/ l <=> o1) /\
 (g \/ k <=> o2) /\
 (f \/ j <=> o3)
 ==> (o1 <=> ~i1) /\ (o2 <=> ~i2) /\ (o3 <=> ~i3)`;;
