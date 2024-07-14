(* ========================================================================= *)
(* ORDERED REWRITING FOR FIRST ORDER TERMS                                   *)
(* ========================================================================= *)

module Rewrite = struct

open Useful;;
open Order;;

(* ------------------------------------------------------------------------- *)
(* Orientations of equations.                                                *)
(* ------------------------------------------------------------------------- *)

type orient = Left_to_right | Right_to_left;;

let toStringOrient ort =
    match ort with
      Left_to_right -> "-->"
    | Right_to_left -> "<--";;


let toStringOrientOption orto =
    match orto with
      Some ort -> toStringOrient ort
    | None -> "<->";;


(* ------------------------------------------------------------------------- *)
(* A type of rewrite systems.                                                *)
(* ------------------------------------------------------------------------- *)

type reductionOrder = Term.term * Term.term -> order option;;

type equationId = int;;

type equation = Rule.equation;;

type rewrite_t =
      {order : reductionOrder;
       known : (equation * orient option) Intmap.map;
       redexes : (equationId * orient) Term_net.termNet;
       subterms : (equationId * bool * Term.path) Term_net.termNet;
       waiting : Intset.set};;

type rewrite =
    Rewrite of rewrite_t;;

let updateWaiting rw waiting =
      let Rewrite {order=order; known=known; redexes=redexes; subterms=subterms; waiting = _} = rw
    in
      Rewrite
        {order = order; known = known; redexes = redexes;
         subterms = subterms; waiting = waiting}
    ;;

let deleteWaiting (Rewrite {waiting=waiting} as rw) id =
    updateWaiting rw (Intset.delete waiting id);;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

open Term_net
let newRewrite order =
    Rewrite
      {order = order;
       known = Intmap.newMap ();
       redexes = Term_net.newNet {fifo = false};
       subterms = Term_net.newNet {fifo = false};
       waiting = Intset.empty};;

let peek (Rewrite {known=known}) id = Intmap.peek known id;;

let size (Rewrite {known=known}) = Intmap.size known;;

let equations (Rewrite {known=known}) =
    Intmap.foldr (fun (_,(eqn,_),eqns) -> eqn :: eqns) [] known;;

(* ------------------------------------------------------------------------- *)
(* Debug functions.                                                          *)
(* ------------------------------------------------------------------------- *)

let termReducible order known id =
      let eqnRed ((l,r),_) tm =
          match total (Substitute.matchTerms Substitute.empty l) tm with
            None -> false
          | Some sub ->
            order (tm, Substitute.subst (Substitute.normalize sub) r) = Some Greater

      in let knownRed tm (eqnId,(eqn,ort)) =
          eqnId <> id &&
          ((ort <> Some Right_to_left && eqnRed eqn tm) ||
           (ort <> Some Left_to_right && eqnRed (Rule.symEqn eqn) tm))

      in let rec termRed tm = Intmap.exists (knownRed tm) known || subtermRed tm
      and subtermRed = function
          (Term.Var _) -> false
        | (Term.Fn (_,tms)) -> List.exists termRed tms
    in
      termRed
    ;;

let literalReducible order known id lit =
    List.exists (termReducible order known id) (Literal.arguments lit);;

let literalsReducible order known id lits =
    Literal.Set.exists (literalReducible order known id) lits;;

let thmReducible order known id th =
    literalsReducible order known id (Thm.clause th);;

(* ------------------------------------------------------------------------- *)
(* Add equations into the system.                                            *)
(* ------------------------------------------------------------------------- *)

let orderToOrient = function
    (Some Equal) -> raise (Error "Rewrite.orient: reflexive")
  | (Some Greater) -> Some Left_to_right
  | (Some Less) -> Some Right_to_left
  | None -> None;;

  let ins redexes redex id ort = Term_net.insert redexes (redex,(id,ort));;

  let addRedexes id (((l,r),_),ort) redexes =
      match ort with
        Some Left_to_right -> ins redexes l id Left_to_right
      | Some Right_to_left -> ins redexes r id Right_to_left
      | None -> ins (ins redexes l id Left_to_right) r id Right_to_left;;


let add (Rewrite {known=known} as rw) (id,eqn) =
    if Intmap.inDomain id known then rw
    else
        let Rewrite {order=order;redexes=redexes;subterms=subterms;waiting=waiting} = rw

        in let ort = orderToOrient (order (fst eqn))

        in let known = Intmap.insert known (id,(eqn,ort))

        in let redexes = addRedexes id (eqn,ort) redexes

        in let waiting = Intset.add waiting id

        in let rw =
            Rewrite
              {order = order; known = known; redexes = redexes;
               subterms = subterms; waiting = waiting}
      in
        rw
      ;;

  let uncurriedAdd (eqn,rw) = add rw eqn;;
  let addList rw = Mlist.foldl uncurriedAdd rw;;

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the rewrite order).          *)
(* ------------------------------------------------------------------------- *)

  let reorder ((i,_),(j,_)) = Int.compare (j,i);;
  let matchingRedexes redexes tm = sort reorder (Term_net.matchNet redexes tm);;


let wellOriented x y = match (x,y) with
    (None, _) -> true
  | (Some Left_to_right, Left_to_right) -> true
  | (Some Right_to_left ,Right_to_left) -> true
  | _ -> false;;

let redexResidue x y = match (x,y) with
    (Left_to_right, ((l_r,_) : equation)) -> l_r
  | (Right_to_left, ((l,r),_)) -> (r,l);;

let orientedEquation dir eqn = match dir with
    Left_to_right -> eqn
  | Right_to_left -> Rule.symEqn eqn;;

let rewrIdConv' order known redexes id tm =
      let rewr (id',lr) =
            let _ = id <> id' || raise (Error "same theorem")
            in let (eqn,ort) = Intmap.get known id'
            in let _ = wellOriented ort lr || raise (Error "orientation")
            in let (l,r) = redexResidue lr eqn
            in let sub = Substitute.normalize (Substitute.matchTerms Substitute.empty l tm)
            in let tm' = Substitute.subst sub r
            in let _ = Option.isSome ort ||
                    order (tm,tm') = Some Greater ||
                    raise (Error "order")
            in let (_,th) = orientedEquation lr eqn
          in
            (tm', Thm.subst sub th)
    in
      match first (total rewr) (matchingRedexes redexes tm) with
        None -> raise (Error "Rewrite.rewrIdConv: no matching rewrites")
      | Some res -> res
    ;;

let rewriteIdConv' order known redexes id =
    if Intmap.null known then Rule.allConv
    else Rule.repeatTopDownConv (rewrIdConv' order known redexes id);;

let mkNeqConv order lit =
      let (l,r) = Literal.destNeq lit
    in
      match order (l,r) with
        None -> raise (Error "incomparable")
      | Some Less ->
          let th = Rule.symmetryRule l r
        in
          fun tm ->
             if Term.equal tm r then (l,th) else raise (Error "mkNeqConv: RL")
      | Some Equal -> raise (Error "irreflexive")
      | Some Greater ->
          let th = Thm.assume lit
        in
          fun tm ->
             if Term.equal tm l then (r,th) else raise (Error "mkNeqConv: LR")
    ;;

type neqConvs = Neq_convs of Rule.conv Literal.Map.map;;

let neqConvsEmpty = Neq_convs (Literal.Map.newMap ());;

let neqConvsNull (Neq_convs m) = Literal.Map.null m;;

let neqConvsAdd order (Neq_convs m) lit =
    match total (mkNeqConv order) lit with
      None -> None
    | Some conv -> Some (Neq_convs (Literal.Map.insert m (lit,conv)));;

let mkNeqConvs order =
      let add (lit,(neq,lits)) =
          match neqConvsAdd order neq lit with
            Some neq -> (neq,lits)
          | None -> (neq, Literal.Set.add lits lit)
    in
      Literal.Set.foldl add (neqConvsEmpty,Literal.Set.empty)
    ;;

let neqConvsDelete (Neq_convs m) lit = Neq_convs (Literal.Map.delete m lit);;

let neqConvsToConv (Neq_convs m) =
    Rule.firstConv (Literal.Map.foldr (fun (_,c,l) -> c :: l) [] m);;

let neqConvsFoldl f b (Neq_convs m) =
    Literal.Map.foldl (fun (l,_,z) -> f (l,z)) b m;;

let neqConvsRewrIdLiterule order known redexes id neq =
    if Intmap.null known && neqConvsNull neq then Rule.allLiterule
    else
        let neq_conv = neqConvsToConv neq
        in let rewr_conv = rewrIdConv' order known redexes id
        in let conv = Rule.orelseConv neq_conv rewr_conv
        in let conv = Rule.repeatTopDownConv conv
      in
        Rule.allArgumentsLiterule conv
      ;;

let rewriteIdEqn' order known redexes id ((l_r,th) as eqn) =
      let (neq,_) = mkNeqConvs order (Thm.clause th)
      in let literule = neqConvsRewrIdLiterule order known redexes id neq
      in let (strongEqn,lit) =
          match Rule.equationLiteral eqn with
            None -> (true, Literal.mkEq l_r)
          | Some lit -> (false,lit)
      in let (lit',litTh) = literule lit
    in
      if Literal.equal lit lit' then eqn
      else
        (Literal.destEq lit',
         if strongEqn then th
         else if not (Thm.negateMember lit litTh) then litTh
         else Thm.resolve lit th litTh);;

let rewriteIdLiteralsRule' order known redexes id lits th =
      let mk_literule = neqConvsRewrIdLiterule order known redexes id

      in let rewr_neq_lit (lit, ((changed,neq,lits,th) as acc)) =
            let neq = neqConvsDelete neq lit
            in let (lit',litTh) = mk_literule neq lit
          in
            if Literal.equal lit lit' then acc
            else
                let th = Thm.resolve lit th litTh
              in
                match neqConvsAdd order neq lit' with
                  Some neq -> (true,neq,lits,th)
                | None -> (changed, neq, Literal.Set.add lits lit', th)

      in let rec rewr_neq_lits neq lits th =
            let (changed,neq,lits,th) =
                neqConvsFoldl rewr_neq_lit (false,neq,lits,th) neq
          in
            if changed then rewr_neq_lits neq lits th
            else (neq,lits,th)

      in let (neq,lits) = mkNeqConvs order lits

      in let (neq,lits,th) = rewr_neq_lits neq lits th

      in let rewr_literule = mk_literule neq

      in let rewr_lit (lit,th) =
          if Thm.member lit th then Rule.literalRule rewr_literule lit th
          else th
    in
      Literal.Set.foldl rewr_lit th lits
    ;;

let rewriteIdRule' order known redexes id th =
    rewriteIdLiteralsRule' order known redexes id (Thm.clause th) th;;

let rewrIdConv (Rewrite {known=known;redexes=redexes}) order =
    rewrIdConv' order known redexes;;

let rewrConv rewrite order = rewrIdConv rewrite order (-1);;

let rewriteIdConv (Rewrite {known=known;redexes=redexes}) order =
    rewriteIdConv' order known redexes;;

let rewriteConv rewrite order = rewriteIdConv rewrite order (-1);;

let rewriteIdLiteralsRule (Rewrite {known=known;redexes=redexes}) order =
    rewriteIdLiteralsRule' order known redexes;;

let rewriteLiteralsRule rewrite order =
    rewriteIdLiteralsRule rewrite order (-1);;

let rewriteIdRule (Rewrite {known=known;redexes=redexes}) order =
    rewriteIdRule' order known redexes;;

let rewriteRule rewrite order = rewriteIdRule rewrite order (-1);;

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system.                                 *)
(* ------------------------------------------------------------------------- *)

let addSubterms id (((l,r),_) : equation) subterms =
      let addSubterm b ((path,tm),net) = Term_net.insert net (tm,(id,b,path))

      in let subterms = Mlist.foldl (addSubterm true) subterms (Term.subterms l)

      in let subterms = Mlist.foldl (addSubterm false) subterms (Term.subterms r)
    in
      subterms
    ;;

let sameRedexes x y z = match (x,y,z) with
    (None,_,_) -> false
  | (Some Left_to_right, (l0,_),(l,_)) -> Term.equal l0 l
  | (Some Right_to_left, (_,r0),(_,r)) -> Term.equal r0 r;;

let redexResidues x (l,r) = match x with
    None -> [(l,r,false);(r,l,false)]
  | (Some Left_to_right) -> [(l,r,true)]
  | (Some Right_to_left) -> [(r,l,true)];;

let findReducibles order known subterms id =
      let checkValidRewr (l,r,ord) id' left path =
            let (((x,y),_),_) = Intmap.get known id'
            in let tm = Term.subterm (if left then x else y) path
            in let sub = Substitute.matchTerms Substitute.empty l tm
          in
            if ord then ()
            else
                let tm' = Substitute.subst (Substitute.normalize sub) r
              in
                if order (tm,tm') = Some Greater then ()
                else raise (Error "order")

      in let addRed lr ((id',left,path),todo) =
          if id <> id' && not (Intset.member id' todo) &&
             can (checkValidRewr lr id' left) path
          then Intset.add todo id'
          else todo

      in let findRed ((l,_,_) as lr, todo) =
          Mlist.foldl (addRed lr) todo (Term_net.matched subterms l)
    in
      Mlist.foldl findRed
    ;;

let reduce1 newx id (eqn0,ort0) (rpl,spl,todo,rw,changed) =
      let (eq0,_) = eqn0
      in let Rewrite {order=order;known=known;redexes=redexes;subterms=subterms;waiting=waiting} = rw
      in let (eq,_) as eqn = rewriteIdEqn' order known redexes id eqn0
      in let identical =
            let (l0,r0) = eq0
            and (l,r) = eq
          in
            Term.equal l l0 && Term.equal r r0
      in let same_redexes = identical || sameRedexes ort0 eq0 eq
      in let rpl = if same_redexes then rpl else Intset.add rpl id
      in let spl = if newx || identical then spl else Intset.add spl id
      in let changed =
          if not newx && identical then changed else Intset.add changed id
      in let ort =
          if same_redexes then Some ort0 else total orderToOrient (order eq)
    in
      match ort with
        None ->
          let known = Intmap.delete known id
          in let rw =
              Rewrite
                {order = order; known = known; redexes = redexes;
                 subterms = subterms; waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
      | Some ort ->
          let todo =
              if not newx && same_redexes then todo
              else
                findReducibles
                  order known subterms id todo (redexResidues ort eq)
          in let known =
              if identical then known else Intmap.insert known (id,(eqn,ort))
          in let redexes =
              if same_redexes then redexes
              else addRedexes id (eqn,ort) redexes
          in let subterms =
              if newx || not identical then addSubterms id eqn subterms
              else subterms
          in let rw =
              Rewrite
                {order = order; known = known; redexes = redexes;
                 subterms = subterms; waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
    ;;

let pick known set =
      let oriented id =
          match Intmap.peek known id with
            Some ((_, Some _) as x) -> Some (id,x)
          | _ -> None

      in let any id =
          match Intmap.peek known id with Some x -> Some (id,x) | _ -> None
    in
      match Intset.firstl oriented set with
        Some _ as x -> x
      | None -> Intset.firstl any set
    ;;

  let cleanRedexes known redexes rpl =
      if Intset.null rpl then redexes
      else
          let filt (id,_) = not (Intset.member id rpl)

          in let addReds (id,reds) =
              match Intmap.peek known id with
                None -> reds
              | Some eqn_ort -> addRedexes id eqn_ort reds

          in let redexes = Term_net.filter filt redexes
          in let redexes = Intset.foldl addReds redexes rpl
        in
          redexes
        ;;

  let cleanSubterms known subterms spl =
      if Intset.null spl then subterms
      else
          let filt (id,_,_) = not (Intset.member id spl)

          in let addSubtms (id,subtms) =
              match Intmap.peek known id with
                None -> subtms
              | Some (eqn,_) -> addSubterms id eqn subtms

          in let subterms = Term_net.filter filt subterms
          in let subterms = Intset.foldl addSubtms subterms spl
        in
          subterms
        ;;

  let rebuild rpl spl rw =
        let Rewrite {order=order;known=known;redexes=redexes;subterms=subterms;waiting=waiting} = rw
        in let redexes = cleanRedexes known redexes rpl
        in let subterms = cleanSubterms known subterms spl
      in
        Rewrite
          {order = order;
           known = known;
           redexes = redexes;
           subterms = subterms;
           waiting = waiting}
      ;;

let rec reduceAcc (rpl, spl, todo, (Rewrite {known=known;waiting=waiting} as rw), changed) =
    match pick known todo with
      Some (id,eqn_ort) ->
        let todo = Intset.delete todo id
      in
        reduceAcc (reduce1 false id eqn_ort (rpl,spl,todo,rw,changed))
    | None ->
      match pick known waiting with
        Some (id,eqn_ort) ->
          let rw = deleteWaiting rw id
        in
          reduceAcc (reduce1 true id eqn_ort (rpl,spl,todo,rw,changed))
      | None -> (rebuild rpl spl rw, Intset.toList changed);;

let isReduced (Rewrite {waiting=waiting}) = Intset.null waiting;;

let reduce' rw =
    if isReduced rw then (rw,[])
    else reduceAcc (Intset.empty,Intset.empty,Intset.empty,rw,Intset.empty);;

let reduce rw = fst (reduce' rw);;

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule.                                              *)
(* ------------------------------------------------------------------------- *)

  let addEqn (id_eqn,rw) = add rw id_eqn;;
  let orderedRewrite order ths =
      let rw = Mlist.foldl addEqn (newRewrite order) (enumerate ths)
    in
      rewriteRule rw order
    ;;

  let order : reductionOrder = kComb (Some Greater);;
  let rewrite = orderedRewrite order;;

end
