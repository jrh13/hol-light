(* ========================================================================= *)
(* Term nets: reasonably fast lookup based on term matchability.             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "basics.ml";;

(* ------------------------------------------------------------------------- *)
(* Term nets are a finitely branching tree structure; at each level we       *)
(* have a set of branches and a set of "values". Linearization is            *)
(* performed from the left of a combination; even in iterated                *)
(* combinations we look at the head first. This is probably fastest, and     *)
(* anyway it's useful to allow our restricted second order matches: if       *)
(* the head is a variable then then whole term is treated as a variable.     *)
(* ------------------------------------------------------------------------- *)

type term_label = Vnet                          (* variable (instantiable)   *)
                 | Lcnet of (string * int)      (* local constant            *)
                 | Cnet of (string * int)       (* constant                  *)
                 | Lnet of int;;                (* lambda term (abstraction) *)

type 'a net = Netnode of (term_label * 'a net) list * 'a list;;

(* ------------------------------------------------------------------------- *)
(* The empty net.                                                            *)
(* ------------------------------------------------------------------------- *)

let empty_net = Netnode([],[]);;

(* ------------------------------------------------------------------------- *)
(* Insert a new element into a net.                                          *)
(* ------------------------------------------------------------------------- *)

let enter =
  let label_to_store lconsts tm =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then
      let bv,bod = dest_abs op in
      let bod' = if mem bv lconsts then vsubst [genvar(type_of bv),bv] bod
                 else bod in
      Lnet(length args),bod'::args
    else if mem op lconsts then Lcnet(fst(dest_var op),length args),args
    else Vnet,[] in
  let canon_eq x y =
    try Pervasives.compare x y = 0 with Invalid_argument _ -> false
  and canon_lt x y =
    try Pervasives.compare x y < 0 with Invalid_argument _ -> false in
  let rec sinsert x l =
    if l = [] then [x] else
    let h = hd l in
    if canon_eq h x then failwith "sinsert" else
    if canon_lt x h then x::l else
    h::(sinsert x (tl l)) in
  let set_insert x l = try sinsert x l with Failure "sinsert" -> l in
  let rec net_update lconsts (elem,tms,Netnode(edges,tips)) =
    match tms with
      [] -> Netnode(edges,set_insert elem tips)
    | (tm::rtms) ->
          let label,ntms = label_to_store lconsts tm in
          let child,others =
            try (snd F_F I) (remove (fun (x,y) -> x = label) edges)
            with Failure _ -> (empty_net,edges) in
          let new_child = net_update lconsts (elem,ntms@rtms,child) in
          Netnode ((label,new_child)::others,tips) in
  fun lconsts (tm,elem) net -> net_update lconsts (elem,[tm],net);;

(* ------------------------------------------------------------------------- *)
(* Look up a term in a net and return possible matches.                      *)
(* ------------------------------------------------------------------------- *)

let lookup =
  let label_for_lookup tm =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then Lnet(length args),(body op)::args
    else Lcnet(fst(dest_var op),length args),args in
  let rec follow (tms,Netnode(edges,tips)) =
    match tms with
      [] -> tips
    | (tm::rtms) ->
          let label,ntms = label_for_lookup tm in
          let collection =
            try let child = assoc label edges in
                follow(ntms @ rtms, child)
            with Failure _ -> [] in
          if label = Vnet then collection else
          try collection @ follow(rtms,assoc Vnet edges)
          with Failure _ -> collection in
  fun tm net -> follow([tm],net);;

(* ------------------------------------------------------------------------- *)
(* Function to merge two nets (code from Don Syme's hol-lite).               *)
(* ------------------------------------------------------------------------- *)

let merge_nets =
  let canon_eq x y =
    try Pervasives.compare x y = 0 with Invalid_argument _ -> false
  and canon_lt x y =
    try Pervasives.compare x y < 0 with Invalid_argument _ -> false in
  let rec set_merge l1 l2 =
    if l1 = [] then l2
    else if l2 = [] then l1 else
    let h1 = hd l1 and t1 = tl l1
    and h2 = hd l2 and t2 = tl l2 in
    if canon_eq h1 h2 then h1::(set_merge t1 t2)
    else if canon_lt h1 h2 then h1::(set_merge t1 l2)
    else h2::(set_merge l1 t2) in
  let rec merge_nets (Netnode(l1,data1),Netnode(l2,data2)) =
    let add_node ((lab,net) as p) l =
      try let (lab',net'),rest = remove (fun (x,y) -> x = lab) l in
          (lab',merge_nets (net,net'))::rest
      with Failure _ -> p::l in
    Netnode(itlist add_node l2 (itlist add_node l1 []),
            set_merge data1 data2) in
  merge_nets;;
