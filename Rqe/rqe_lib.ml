(* ---------------------------------------------------------------------- *)
(*  Refs                                                                  *)
(* ---------------------------------------------------------------------- *)

let (+=) a b = a := !a + b;;
let (+.=) a b = a := !a +. b;;

(* ---------------------------------------------------------------------- *)
(*  Timing                                                                *)
(* ---------------------------------------------------------------------- *)

let ptime f x =
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      let total_time = finish_time -. start_time in
      (result,total_time)
  with e ->
      let finish_time = Sys.time() in
      let total_time = finish_time -. start_time in
      (print_string("Failed after (user) CPU time of "^
                   (string_of_float(total_time) ^": "));
      raise e);;

(* ---------------------------------------------------------------------- *)
(*  Lists                                                                 *)
(* ---------------------------------------------------------------------- *)

let mappair f g l =
  let a,b = unzip l in
  let la = map f a in
  let lb = map g b in
    zip la lb;;

let rec insertat i x l =
  if i = 0 then x::l else
  match l with
    [] -> failwith "insertat: list too short for position to exist"
  | h::t -> h::(insertat (i-1) x t);;

let rec allcombs f l =
  match l with 
      [] -> []
    | h::t -> 
        map (f h) t @ allcombs f t;;

let rec assoc_list keys assl = 
  match keys with
      [] -> []
    | h::t -> assoc h assl::assoc_list t assl;;


let add_to_list l1 l2 = 
  l1 := !l1 @ l2;;

let list x = [x];;

let rec ith i l = 
  if i = 0 then hd l else ith (i-1) (tl l);;

let rev_ith i l = ith (length l - i - 1) l;;

let get_index p l = 
  let rec get_index p l n = 
    match l with 
        [] -> failwith "get_index"
      | h::t -> if p h then n else get_index p t (n + 1) in
    get_index p l 0;;
(*
  get_index (fun x -> x > 5) [1;2;3;7;9]
*)


let bindex p l = 
  let rec bindex p l i = 
    match l with
        [] -> failwith "bindex: not found"
      | h::t -> if p h then i else bindex p t (i + 1) in
    bindex p l 0;;

let cons x y = x :: y;;

let rec swap_lists l store = 
  match l with
      [] -> store
    | h::t -> 
        let store' = map2 cons h store in
          swap_lists t store';; 


(*
swap_lists [[1;2;3];[4;5;6];[7;8;9];[10;11;12]] 
--> 
[[1; 4; 7; 10]; [2; 5; 8; 11]; [3; 6; 9; 12]]
*)

let swap_lists l = 
  let n = length (hd l) in
  let l' = swap_lists l (replicate [] n) in
    map rev l';;




(*
bindex (fun x -> x = 5) [1;2;5];;
*)

let fst3 (a,_,_) = a;;
let snd3 (_,a,_) = a;;
let thd3 (_,_,a) = a;;

let odd n = (n mod 2 = 1);; 
let even n = (n mod 2 = 0);; 

(* ---------------------------------------------------------------------- *)
(*  Terms                                                                 *)
(* ---------------------------------------------------------------------- *)

let dest_var_or_const t = 
  match t with
      Var(s,ty) -> s,ty
    | Const(s,ty) -> s,ty
    | _ -> failwith "not a var or const";;                                   

let can_match t1 t2 = 
  try 
    let n1,_ = dest_var_or_const t1 in
    let n2,_ = dest_var_or_const t2 in
      n1 = n2 & can (term_match [] t1) t2
  with Failure _ -> false;;

let dest_quant tm =
  if is_forall tm then dest_forall tm 
  else if is_exists tm then dest_exists tm
  else failwith "dest_quant: not a quantified term";;

let get_binop tm =
  try let f,r = dest_comb tm in
      let xop,l = dest_comb f in
        xop,l,r 
  with Failure _ -> failwith "get_binop";;

