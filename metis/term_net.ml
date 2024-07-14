(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* ========================================================================= *)

module Term_net = struct

open Useful;;
open Order;;

(* ------------------------------------------------------------------------- *)
(* Anonymous variables.                                                      *)
(* ------------------------------------------------------------------------- *)

let anonymousName = Name.fromString "_";;
let anonymousVar = Term.Var anonymousName;;

(* ------------------------------------------------------------------------- *)
(* Quotient terms.                                                           *)
(* ------------------------------------------------------------------------- *)

type qterm =
    Var
  | Fn of Name_arity.nameArity * qterm list;;

  let rec cmp = function
      [] -> Equal
    | (q1_q2 :: qs) ->
      if Portable.pointerEqual q1_q2 then cmp qs
      else
        match q1_q2 with
          (Var,Var) -> Equal
        | (Var, Fn _) -> Less
        | (Fn _, Var) -> Greater
        | (Fn (f1, f1'), Fn (f2, f2')) -> fnCmp (f1,f1') (f2,f2') qs

  and fnCmp (n1,q1) (n2,q2) qs =
    match Name_arity.compare (n1,n2) with
      Less -> Less
    | Equal -> cmp (zip q1 q2 @ qs)
    | Greater -> Greater;;

  let compareQterm q1_q2 = cmp [q1_q2];;

  let compareFnQterm (f1,f2) = fnCmp f1 f2 [];;


let equalQterm q1 q2 = compareQterm (q1,q2) = Equal;;

let equalFnQterm f1 f2 = compareFnQterm (f1,f2) = Equal;;

let rec termToQterm = function
    (Term.Var _) -> Var
  | (Term.Fn (f,l)) -> Fn ((f, length l), List.map termToQterm l);;

  let rec qm = function
      [] -> true
    | ((Var,_) :: rest) -> qm rest
    | ((Fn _, Var) :: _) -> false
    | ((Fn (f,a), Fn (g,b)) :: rest) ->
      Name_arity.equal f g && qm (zip a b @ rest);;

  let matchQtermQterm qtm qtm' = qm [(qtm,qtm')];;

  let rec qm = function
      [] -> true
    | ((Var,_) :: rest) -> qm rest
    | ((Fn _, Term.Var _) :: _) -> false
    | ((Fn ((f,n),a), Term.Fn (g,b)) :: rest) ->
      Name.equal f g && n = length b && qm (zip a b @ rest);;

  let matchQtermTerm qtm tm = qm [(qtm,tm)];;

  let rec qn qsub = function
      [] -> Some qsub
    | ((Term.Var v, qtm) :: rest) ->
      (match Name.Map.peek qsub v with
         None -> qn (Name.Map.insert qsub (v,qtm)) rest
       | Some qtm' -> if equalQterm qtm qtm' then qn qsub rest else None)
    | ((Term.Fn _, Var) :: _) -> None
    | ((Term.Fn (f,a), Fn ((g,n),b)) :: rest) ->
      if Name.equal f g && length a = n then qn qsub (zip a b @ rest)
      else None;;

  let matchTermQterm qsub tm qtm = qn qsub [(tm,qtm)];;

  let rec qv s t = match (s,t) with
      (Var, x) -> x
    | (x, Var) -> x
    | (Fn (f,a), Fn (g,b)) ->
        let _ = Name_arity.equal f g || raise (Error "Term_net.qv")
      in
        Fn (f, zipWith qv a b)
      ;;

  let rec qu qsub = function
      [] -> qsub
    | ((Var, _) :: rest) -> qu qsub rest
    | ((qtm, Term.Var v) :: rest) ->
        let qtm =
            match Name.Map.peek qsub v with None -> qtm | Some qtm' -> qv qtm qtm'
      in
        qu (Name.Map.insert qsub (v,qtm)) rest
    | ((Fn ((f,n),a), Term.Fn (g,b)) :: rest) ->
      if Name.equal f g && n = length b then qu qsub (zip a b @ rest)
      else raise (Error "Term_net.qu");;

  let unifyQtermQterm qtm qtm' = total (qv qtm) qtm';;

  let unifyQtermTerm qsub qtm tm = total (qu qsub) [(qtm,tm)];;

  let rec qtermToTerm = function
      Var -> anonymousVar
    | (Fn ((f,_),l)) -> Term.Fn (f, List.map qtermToTerm l);;


(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};;

type 'a net =
    Result of 'a list
  | Single of qterm * 'a net
  | Multiple of 'a net option * 'a net Name_arity.Map.map;;

type 'a termNet = Net of parameters * int * (int * (int * 'a) net) option;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet parm = Net (parm,0,None);;

  let rec computeSize = function
      (Result l) -> length l
    | (Single (_,n)) -> computeSize n
    | (Multiple (vs,fs)) ->
      Name_arity.Map.foldl
        (fun (_,n,acc) -> acc + computeSize n)
        (match vs with Some n -> computeSize n | None -> 0)
        fs;;

  let netSize = function
      None -> None
    | (Some n) -> Some (computeSize n, n);;


let size = function
    (Net (_,_,None)) -> 0
  | (Net (_, _, Some (i,_))) -> i;;

let null net = size net = 0;;

let singles qtms a = Mlist.foldr (fun (x, y) -> Single (x, y)) a qtms;;

  let pre = function
      None -> (0,None)
    | (Some (i,n)) -> (i, Some n);;

  let rec add a b c = match (a, b, c) with
      (Result l, [], Result l') -> Result (l @ l')
    | (a, (qtm :: qtms as input1), Single (qtm',n)) ->
      if equalQterm qtm qtm' then Single (qtm, add a qtms n)
      else add a input1 (add n [qtm'] (Multiple (None, Name_arity.Map.newMap ())))
    | (a, Var :: qtms, Multiple (vs,fs)) ->
      Multiple (Some (oadd a qtms vs), fs)
    | (a, Fn (f,l) :: qtms, Multiple (vs,fs)) ->
        let n = Name_arity.Map.peek fs f
      in
        Multiple (vs, Name_arity.Map.insert fs (f, oadd a (l @ qtms) n))
    | _ -> raise (Bug "Term_net.insert: Match")

  and oadd a qtms = function
      None -> singles qtms a
    | (Some n) -> add a qtms n;;

  let ins a qtm (i,n) = Some (i + 1, oadd (Result [a]) [qtm] n);;

  let insert (Net (p,k,n)) (tm,a) =
      try Net (p, k + 1, ins (k,a) (termToQterm tm) (pre n))
      with Error _ -> raise (Bug "Term_net.insert: should never fail");;


let fromList parm l = Mlist.foldl (fun (tm_a,n) -> insert n tm_a) (newNet parm) l;;

let filter pred =
      let rec filt = function
          (Result l) ->
          (match List.filter (fun (_,a) -> pred a) l with
             [] -> None
           | l -> Some (Result l))
        | (Single (qtm,n)) ->
          (match filt n with
             None -> None
           | Some n -> Some (Single (qtm,n)))
        | (Multiple (vs,fs)) ->
            let vs = Option.mapPartial filt vs

            in let fs = Name_arity.Map.mapPartial (fun (_,n) -> filt n) fs
          in
            if not (Option.isSome vs) && Name_arity.Map.null fs then None
            else Some (Multiple (vs,fs))
    in try
      function
         Net (_,_,None) as net -> net
       | Net (p, k, Some (_,n)) -> Net (p, k, netSize (filt n))
    with Error _ -> raise (Bug "Term_net.filter: should never fail");;

let toString net = "Term_net[" ^ Int.toString (size net) ^ "]";;

(* ------------------------------------------------------------------------- *)
(* Specialized fold operations to support matching and unification.          *)
(* ------------------------------------------------------------------------- *)

  let rec norm = function
      (0 :: ks, ((_,n) as f) :: fs, qtms) ->
        let (a,qtms) = revDivide qtms n
      in
        addQterm (Fn (f,a)) (ks,fs,qtms)
    | stack -> stack

  and addQterm qtm (ks,fs,qtms) =
        let ks = match ks with [] -> [] | k :: ks -> (k - 1) :: ks
      in
        norm (ks, fs, qtm :: qtms)

  and addFn ((_,n) as f) (ks,fs,qtms) = norm (n :: ks, f :: fs, qtms);;

  let stackEmpty = ([],[],[]);;

  let stackAddQterm = addQterm;;

  let stackAddFn = addFn;;

  let stackValue = function
      ([],[],[qtm]) -> qtm
    | _ -> raise (Bug "Term_net.stackValue");;


  let rec fold inc acc = function
      [] -> acc
    | ((0,stack,net) :: rest) ->
      fold inc (inc (stackValue stack, net, acc)) rest
    | ((n, stack, Single (qtm,net)) :: rest) ->
      fold inc acc ((n - 1, stackAddQterm qtm stack, net) :: rest)
    | ((n, stack, Multiple (v,fns)) :: rest) ->
        let n = n - 1

        in let rest =
            match v with
              None -> rest
            | Some net -> (n, stackAddQterm Var stack, net) :: rest

        in let getFns ((_,k) as f, net, x) =
            (k + n, stackAddFn f stack, net) :: x
      in
        fold inc acc (Name_arity.Map.foldr getFns rest fns)
    | _ -> raise (Bug "Term_net.foldTerms.fold");;

  let foldTerms inc acc net = fold inc acc [(1,stackEmpty,net)];;


let foldEqualTerms pat inc acc =
      let rec fold = function
          ([],net) -> inc (pat,net,acc)
        | (pat :: pats, Single (qtm,net)) ->
          if equalQterm pat qtm then fold (pats,net) else acc
        | (Var :: pats, Multiple (v,_)) ->
          (match v with None -> acc | Some net -> fold (pats,net))
        | (Fn (f,a) :: pats, Multiple (_,fns)) ->
          (match Name_arity.Map.peek fns f with
             None -> acc
           | Some net -> fold (a @ pats, net))
        | _ -> raise (Bug "Term_net.foldEqualTerms.fold")
    in
      fun net -> fold ([pat],net)
    ;;


  let rec fold inc acc = function
      [] -> acc
    | (([],stack,net) :: rest) ->
      fold inc (inc (stackValue stack, net, acc)) rest
    | ((Var :: pats, stack, net) :: rest) ->
        let harvest (qtm,n,l) = (pats, stackAddQterm qtm stack, n) :: l
      in
        fold inc acc (foldTerms harvest rest net)
    | ((pat :: pats, stack, Single (qtm,net)) :: rest) ->
      (match unifyQtermQterm pat qtm with
         None -> fold inc acc rest
       | Some qtm ->
         fold inc acc ((pats, stackAddQterm qtm stack, net) :: rest))
    | (((Fn (f,a) as pat) :: pats, stack, Multiple (v,fns)) :: rest) ->
        let rest =
            match v with
              None -> rest
            | Some net -> (pats, stackAddQterm pat stack, net) :: rest

        in let rest =
            match Name_arity.Map.peek fns f with
              None -> rest
            | Some net -> (a @ pats, stackAddFn f stack, net) :: rest
      in
        fold inc acc rest
    | _ -> raise (Bug "Term_net.foldUnifiableTerms.fold");;

  let foldUnifiableTerms pat inc acc net =
      fold inc acc [([pat],stackEmpty,net)];;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

  let idwise ((m,_),(n,_)) = Int.compare (m,n);;

  let fifoize ({fifo=fifo} : parameters) l = if fifo then sort idwise l else l;;

  let finally parm l = List.map snd (fifoize parm l);;


  let rec mat acc = function
      [] -> acc
    | ((Result l, []) :: rest) -> mat (l @ acc) rest
    | ((Single (qtm,n), tm :: tms) :: rest) ->
      mat acc (if matchQtermTerm qtm tm then (n,tms) :: rest else rest)
    | ((Multiple (vs,fs), tm :: tms) :: rest) ->
        let rest = match vs with None -> rest | Some n -> (n,tms) :: rest

        in let rest =
            match tm with
              Term.Var _ -> rest
            | Term.Fn (f,l) ->
              match Name_arity.Map.peek fs (f, length l) with
                None -> rest
              | Some n -> (n, l @ tms) :: rest
      in
        mat acc rest
    | _ -> raise (Bug "Term_net.match: Match");;

  let matchNet x y = match (x,y) with
      (Net (_,_,None), _) -> []
    | (Net (p, _, Some (_,n)), tm) ->
      try finally p (mat [] [(n,[tm])])
      with Error _ -> raise (Bug "Term_net.match: should never fail");;


  let unseenInc qsub v tms (qtm,net,rest) =
      (Name.Map.insert qsub (v,qtm), net, tms) :: rest;;

  let seenInc qsub tms (_,net,rest) = (qsub,net,tms) :: rest;;

  let rec mat acc = function
      [] -> acc
    | ((_, Result l, []) :: rest) -> mat (l @ acc) rest
    | ((qsub, Single (qtm,net), tm :: tms) :: rest) ->
      (match matchTermQterm qsub tm qtm with
         None -> mat acc rest
       | Some qsub -> mat acc ((qsub,net,tms) :: rest))
    | ((qsub, (Multiple _ as net), Term.Var v :: tms) :: rest) ->
      (match Name.Map.peek qsub v with
         None -> mat acc (foldTerms (unseenInc qsub v tms) rest net)
       | Some qtm -> mat acc (foldEqualTerms qtm (seenInc qsub tms) rest net))
    | ((qsub, Multiple (_,fns), Term.Fn (f,a) :: tms) :: rest) ->
        let rest =
            match Name_arity.Map.peek fns (f, length a) with
              None -> rest
            | Some net -> (qsub, net, a @ tms) :: rest
      in
        mat acc rest
    | _ -> raise (Bug "Term_net.matched.mat");;

  let matched x tm = match x with
      (Net (_,_,None)) -> []
    | (Net (parm, _, Some (_,net))) ->
      try finally parm (mat [] [(Name.Map.newMap (), net, [tm])])
      with Error _ -> raise (Bug "Term_net.matched: should never fail");;


  let inc qsub v tms (qtm,net,rest) =
      (Name.Map.insert qsub (v,qtm), net, tms) :: rest;;

  let rec mat acc = function
      [] -> acc
    | ((_, Result l, []) :: rest) -> mat (l @ acc) rest
    | ((qsub, Single (qtm,net), tm :: tms) :: rest) ->
      (match unifyQtermTerm qsub qtm tm with
         None -> mat acc rest
       | Some qsub -> mat acc ((qsub,net,tms) :: rest))
    | ((qsub, (Multiple _ as net), Term.Var v :: tms) :: rest) ->
      (match Name.Map.peek qsub v with
         None -> mat acc (foldTerms (inc qsub v tms) rest net)
       | Some qtm -> mat acc (foldUnifiableTerms qtm (inc qsub v tms) rest net))
    | ((qsub, Multiple (v,fns), Term.Fn (f,a) :: tms) :: rest) ->
        let rest = match v with None -> rest | Some net -> (qsub,net,tms) :: rest

        in let rest =
            match Name_arity.Map.peek fns (f, length a) with
              None -> rest
            | Some net -> (qsub, net, a @ tms) :: rest
      in
        mat acc rest
    | _ -> raise (Bug "Term_net.unify.mat");;

  let unify x tm = match x with
      (Net (_,_,None)) -> []
    | (Net (parm, _, Some (_,net))) ->
      try finally parm (mat [] [(Name.Map.newMap (), net, [tm])])
      with Error _ -> raise (Bug "Term_net.unify: should never fail");;

end



