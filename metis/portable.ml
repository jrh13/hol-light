module Portable = struct

let pointerEqual (p1, p2) = p1 == p2;;

let randomInt x = Random.rand () mod x;;

let randomWord (): Word64.word =
  Word64.fromInt (Random.rand ());;

let critical x = x;;

end
;;
