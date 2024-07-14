module Math = struct

let exp x = failwith "exp";;

let ln x = failwith "ln";;

let sqrt = Double.sqrt;;

let pow x y =
  exp (y * ln x);;

end
