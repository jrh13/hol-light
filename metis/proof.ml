(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* ========================================================================= *)

module Proof = struct

open Useful;;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

type inference =
    Axiom of Literal.Set.set
  | Assume of Atom.atom
  | Subst of Substitute.subst * Thm.thm
  | Resolve of Atom.atom * Thm.thm * Thm.thm
  | Refl of Term.term
  | Equality of Literal.literal * Term.path * Term.term;;

type proof = (Thm.thm * inference) list;;


(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

let parents = function
    (Axiom _) -> []
  | (Assume _) -> []
  | (Subst (_,th)) -> [th]
  | (Resolve (_,th,th')) -> [th;th']
  | (Refl _) -> []
  | (Equality _) -> [];;

let inferenceToThm = function
    (Axiom cl) -> Thm.axiom cl
  | (Assume atm) -> Thm.assume (true,atm)
  | (Subst (sub,th)) -> Thm.subst sub th
  | (Resolve (atm,th,th')) -> Thm.resolve (true,atm) th th'
  | (Refl tm) -> Thm.refl tm
  | (Equality (lit,path,r)) -> Thm.equality lit path r;;

let reconstructSubst cl cl' =
    let rec recon = function
        [] ->
          raise (Bug "can't reconstruct Subst rule")
      | (([],sub) :: others) ->
        if Literal.Set.equal (Literal.Set.subst sub cl) cl' then sub
        else recon others
      | ((lit :: lits, sub) :: others) ->
          let checkLit (lit',acc) =
              match total (Literal.matchLiterals sub lit) lit' with
                None -> acc
              | Some sub -> (lits,sub) :: acc
        in
          recon (Literal.Set.foldl checkLit others cl')
  in
    Substitute.normalize (recon [(Literal.Set.toList cl, Substitute.empty)])
  ;;

let reconstructResolvant cl1 cl2 cl =
  (if not (Literal.Set.subset cl1 cl) then
     Literal.Set.pick (Literal.Set.difference cl1 cl)
   else if not (Literal.Set.subset cl2 cl) then
     Literal.negate (Literal.Set.pick (Literal.Set.difference cl2 cl))
   else
     (* A useless resolution, but we must reconstruct it anyway *)
       let cl1' = Literal.Set.negate cl1
       and cl2' = Literal.Set.negate cl2
       in let lits = Literal.Set.intersectList [cl1;cl1';cl2;cl2']
     in
       if not (Literal.Set.null lits) then Literal.Set.pick lits
       else raise (Bug "can't reconstruct Resolve rule")
     );;

let reconstructEquality cl =
    let rec sync s t path (f,a) (f',a') =
        if not (Name.equal f f' && length a = length a') then None
        else
            let itms = enumerate (zip a a')
          in
            (match List.filter (fun x -> not (uncurry Term.equal (snd x))) itms with
              [(i,(tm,tm'))] ->
                let path = i :: path
              in
                if Term.equal tm s && Term.equal tm' t then
                  Some (List.rev path)
                else
                  (match (tm,tm') with
                    (Term.Fn f_a, Term.Fn f_a') -> sync s t path f_a f_a'
                  | _ -> None)
            | _ -> None)

    in let recon (neq,(pol,atm),(pol',atm')) =
        if pol = pol' then None
        else
            let (s,t) = Literal.destNeq neq

            in let path =
                if not (Term.equal s t) then sync s t [] atm atm'
                else if not (Atom.equal atm atm') then None
                else Atom.find (Term.equal s) atm
          in
            match path with
              Some path -> Some ((pol',atm),path,t)
            | None -> None

    in let candidates =
        match List.partition Literal.isNeq (Literal.Set.toList cl) with
          ([l1],[l2;l3]) -> [(l1,l2,l3);(l1,l3,l2)]
        | ([l1;l2],[l3]) -> [(l1,l2,l3);(l1,l3,l2);(l2,l1,l3);(l2,l3,l1)]
        | ([l1],[l2]) -> [(l1,l1,l2);(l1,l2,l1)]
        | _ -> raise (Bug "reconstructEquality: malformed")
      in
        match first recon candidates with
          Some info -> info
        | None -> raise (Bug "can't reconstruct Equality rule")
      ;;

  let reconstruct cl = function
      (Thm.Axiom,[]) -> Axiom cl
    | (Thm.Assume,[]) ->
      (match Literal.Set.findl Literal.positive cl with
         Some (_,atm) -> Assume atm
       | None -> raise (Bug "malformed Assume inference"))
    | (Thm.Subst,[th]) ->
      Subst (reconstructSubst (Thm.clause th) cl, th)
    | (Thm.Resolve,[th1;th2]) ->
        let cl1 = Thm.clause th1
        and cl2 = Thm.clause th2
        in let (pol,atm) = reconstructResolvant cl1 cl2 cl
      in
        if pol then Resolve (atm,th1,th2) else Resolve (atm,th2,th1)
    | (Thm.Refl,[]) ->
      (match Literal.Set.findl (kComb true) cl with
         Some lit -> Refl (Literal.destRefl lit)
       | None -> raise (Bug "malformed Refl inference"))
    | (Thm.Equality,[]) -> let (x,y,z) = (reconstructEquality cl) in Equality (x,y,z)
    | _ -> raise (Bug "malformed inference");;

  let thmToInference th =

        let cl = Thm.clause th

        in let thmInf = Thm.inference th
        in let inf = reconstruct cl thmInf
      in
        inf
;;

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

let proof th =
  let emptyThms : Thm.thm Literal.Set_map.map = Literal.Set_map.newMap ()

  in let rec addThms (th,ths) =
        let cl = Thm.clause th
      in
        if Literal.Set_map.inDomain cl ths then ths
        else
            let (_,pars) = Thm.inference th
            in let ths = Mlist.foldl addThms ths pars
          in
            if Literal.Set_map.inDomain cl ths then ths
            else Literal.Set_map.insert ths (cl,th)

  in let mkThms th = addThms (th,emptyThms)

  in let rec addProof (th,(ths,acc)) =
        let cl = Thm.clause th
      in
        match Literal.Set_map.peek ths cl with
          None -> (ths,acc)
        | Some th ->
            let (_,pars) = Thm.inference th
            in let (ths,acc) = Mlist.foldl addProof (ths,acc) pars
            in let ths = Literal.Set_map.delete ths cl
            in let acc = (th, thmToInference th) :: acc
          in
            (ths,acc)

  in let mkProof ths th =
        let (ths,acc) = addProof (th,(ths,[]))
      in
        List.rev acc
  in    let ths = mkThms th
        in let infs = mkProof ths th
      in
        infs
      ;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v =
      let free th_inf =
          match th_inf with
            (_, Axiom lits) -> Literal.Set.freeIn v lits
          | (_, Assume atm) -> Atom.freeIn v atm
          | (th, Subst _) -> Thm.freeIn v th
          | (_, Resolve _) -> false
          | (_, Refl tm) -> Term.freeIn v tm
          | (_, Equality (lit,_,tm)) ->
            Literal.freeIn v lit || Term.freeIn v tm
    in
      List.exists free
    ;;

let freeVars =
      let inc (th_inf,set) =
          Name.Set.union set
          (match th_inf with
             (_, Axiom lits) -> Literal.Set.freeVars lits
           | (_, Assume atm) -> Atom.freeVars atm
           | (th, Subst _) -> Thm.freeVars th
           | (_, Resolve _) -> Name.Set.empty
           | (_, Refl tm) -> Term.freeVars tm
           | (_, Equality (lit,_,tm)) ->
             Name.Set.union (Literal.freeVars lit) (Term.freeVars tm))
    in
      Mlist.foldl inc Name.Set.empty
    ;;

end



