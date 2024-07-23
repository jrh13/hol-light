(* 32-bit RNG from ML for the Working Programmer *)
module Random = struct

let init, rand, upto =
  let a = 16807.0 in
  let m = 2147483647.0 in
  let nextRand seed =
    let t = a *. seed in
    t -. m *. Real.fromInt (Real.floor (t /. m)) in
  let r = ref 1.0 in
  let init n = r := Real.fromInt n in
  let rand () =
    let x = nextRand (!r) in
    r := x;
    Real.floor x in
  let upto n = rand () mod n in
  init, rand, upto;;

end (* struct Random *)
;;
