module Math = struct

let ln (x: double) = failwith "ln";;

let exp (x: double) = failwith "exp";;

let sqrt = Double.sqrt;;

let pow (x, y) = exp (y *. ln x);;

end (* struct Math *)
