(* 32-bit RNG from ML for the Working Programmer, converted to using integers.
 *)
module Random = struct

let init, rand, upto =
  let a = 16807 in
  let m = 2147483647 in
  let nextRand seed =
    let t = a * seed in
    t - m * (t / m) in
  let r = ref 1 in
  let init n = r := n in
  let rand () =
    let x = nextRand (!r) in
    r := x;
    x in
  let upto n = rand () mod n in
  init, rand, upto;;

end (* struct Random *)
;;
