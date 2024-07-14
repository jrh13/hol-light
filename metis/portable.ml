module Portable = struct

let pointerEqual (p1, p2) = p1 == p2;;

(* TODO(oskar.abrahamsson) Implement random *)

let randomInt x =
  failwith "not implemented: randomInt";;

let randomWord () =
  failwith "not implemented: randomWord";;

let critical x = x;;

end
