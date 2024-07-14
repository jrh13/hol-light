(* ========================================================================= *)
(* A STORE FOR UNIT THEOREMS                                                 *)
(* ========================================================================= *)

module Units = struct

open Useful;;

(* ------------------------------------------------------------------------- *)
(* A type of unit store.                                                     *)
(* ------------------------------------------------------------------------- *)

type unitThm = Literal.literal * Thm.thm;;

type units = Units of unitThm Literal_net.literalNet;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

open Term_net
let empty = Units (Literal_net.newNet {fifo = false});;

let size (Units net) = Literal_net.size net;;

let toString units = "U{" ^ Int.toString (size units) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Add units into the store.                                                 *)
(* ------------------------------------------------------------------------- *)

let add (Units net) ((lit,th) as uTh) =
      let net = Literal_net.insert net (lit,uTh)
    in
      match total Literal.sym lit with
        None -> Units net
      | Some ((pol,_) as lit') ->
          let th' = (if pol then Rule.symEq else Rule.symNeq) lit th
          in let net = Literal_net.insert net (lit',(lit',th'))
        in
          Units net
    ;;

let addList = Mlist.foldl (fun (th,u) -> add u th);;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let matchUnits (Units net) lit =
      let check ((lit',_) as uTh) =
          match total (Literal.matchLiterals Substitute.empty lit') lit with
            None -> None
          | Some sub -> Some (uTh,sub)
    in
      first check (Literal_net.matchNet net lit)
    ;;

(* ------------------------------------------------------------------------- *)
(* Reducing by repeated matching and resolution.                             *)
(* ------------------------------------------------------------------------- *)

let reduce units =
      let red1 (lit,news_th) =
          match total Literal.destIrrefl lit with
            Some tm ->
              let (news,th) = news_th
              in let th = Thm.resolve lit th (Thm.refl tm)
            in
              (news,th)
          | None ->
              let lit' = Literal.negate lit
            in
              match matchUnits units lit' with
                None -> news_th
              | Some ((_,rth),sub) ->
                  let (news,th) = news_th
                  in let rth = Thm.subst sub rth
                  in let th = Thm.resolve lit th rth
                  in let newLits = Literal.Set.delete (Thm.clause rth) lit'
                  in let news = Literal.Set.union newLits news
                in
                  (news,th)

      in let rec red (news,th) =
          if Literal.Set.null news then th
          else red (Literal.Set.foldl red1 (Literal.Set.empty,th) news)
    in
      fun th -> Rule.removeSym (red (Thm.clause th, th))
    ;;

end



