module Real = struct

type real = Double.double;;

let compare x y =
  if Double.(<) x y then Less
  else if Double.(>) x y then Greater
  else Equal;;

let fromInt = Double.fromString o Int.toString;;

let floor x =
  let y = Double.toWord x in
  let exp = Word64.andb (Word64.(>>) y 52) (Word64.fromInt 0x7FF) in
  let bits = 1023 + 52 - Word64.toInt exp in
  if bits > 53 then
    0.0
  else if bits > 0 then
    let z = Word64.(<<) (Word64.fromInt 1) bits in
    let z = Word64.(-) z (Word64.fromInt 1) in
    let y = Word64.andb y (Word64.notb z) in
    Double.fromWord y
  else
    x;;

end (* struct Real *)
