(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* ========================================================================= *)

module Heap = struct

(* Leftist heaps as in Purely Functional Data Structures, by Chris Okasaki *)

exception Empty;;

type 'a node = Em | Tr of int * 'a * 'a node * 'a node;;

type 'a heap = Heap of ('a * 'a -> ordering) * int * 'a node;;

let rank = function
  | Em -> 0
  | (Tr (r,_,_,_)) -> r;;

let makeT (x,a,b) =
  if rank a >= rank b then
    Tr (rank b + 1, x, a, b)
  else
    Tr (rank a + 1, x, b, a);;

let merge cmp =
  let rec mrg = function
  | (h,Em) -> h
  | (Em,h) -> h
  | (Tr (_,x,a1,b1) as h1, (Tr (_,y,a2,b2) as h2)) ->
      match cmp (x,y) with
      | Greater -> makeT (y, a2, mrg (h1,b2))
      | _ -> makeT (x, a1, mrg (b1,h2)) in
  mrg
;;

let newHeap cmp = Heap (cmp,0,Em);;

let add (Heap (f,n,a)) x = Heap (f, n + 1, merge f (Tr (1,x,Em,Em), a));;

let size (Heap (_, n, _)) = n;;

let null h = size h = 0;;

let top = function
  | (Heap (_,_,Em)) -> raise Empty
  | (Heap (_, _, Tr (_,x,_,_))) -> x;;

let remove = function
  | (Heap (_,_,Em)) -> raise Empty
  | (Heap (f, n, Tr (_,x,a,b))) -> (x, Heap (f, n - 1, merge f (a,b)));;

let app f =
  let rec ap = function
    | [] -> ()
    | (Em :: rest) -> ap rest
    | (Tr (_,d,a,b) :: rest) -> (f d; ap (a :: b :: rest)) in
  function Heap (_,_,a) -> ap [a]
;;

let rec toList h =
  if null h then [] else
    let (x,h) = remove h in
    x :: toList h
;;

let toString h =
  "Heap[" ^ (if null h then "" else Int.toString (size h)) ^ "]";;

end (* struct Heap *)
;;
