
(* ---------------------------------------------------------------------- *)
(*  Operators                                                             *)
(* ---------------------------------------------------------------------- *)
let dest_beq = dest_binop `(<=>)`;;
let t_tm = `T`;;
let f_tm = `F`;;

parse_as_infix ("<>",(12,"right"));;

let NEQ = new_definition
 `x <> y <=> ~(x = y)`;;

let nqt = `(<>):A -> A -> bool`;;
let mk_neq (l,r) =
  try
      let ty = type_of l in
      let nqt' = inst[ty,aty] nqt in
        mk_comb(mk_comb(nqt',l),r)
  with Failure _ -> failwith "mk_neq";;

(* ---------------------------------------------------------------------- *)
(*  Unfiled                                                               *)
(* ---------------------------------------------------------------------- *)

let IMP_AND_THM = TAUT `(p ==> q ==> r) <=> (p /\ q ==> r)`;;
let AND_IMP_THM = TAUT `(p /\ q ==> r) <=> (p ==> q ==> r)`;;

let is_pos tm = not (is_neg tm);;

let CONJ_LIST thms =
    end_itlist CONJ thms;;

(*
CONJ_LIST [TRUTH;TRUTH;TRUTH]
*)
