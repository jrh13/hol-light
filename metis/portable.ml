module Portable = struct

let pointerEqual (p1, p2) = p1 == p2;;

let randomInt (x: int): int =
  failwith "not implemented: randomInt";;

let randomWord (): Word64.word =
  failwith "not implemented: randomWord";;

let critical x = x;;

end
