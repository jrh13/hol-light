(* ========================================================================= *)
(* DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                     *)
(* ========================================================================= *)

module Rule = struct

(* ------------------------------------------------------------------------- *)
(* Variable names.                                                           *)
(* ------------------------------------------------------------------------- *)

let xVarName = Name.fromString "x";;
let xVar = Term.Var_ xVarName;;

let yVarName = Name.fromString "y";;
let yVar = Term.Var_ yVarName;;

let zVarName = Name.fromString "z";;
let zVar = Term.Var_ zVarName;;

let xIVarName i = Name.fromString ("x" ^ Int.toString i);;
let xIVar i = Term.Var_ (xIVarName i);;

let yIVarName i = Name.fromString ("y" ^ Int.toString i);;
let yIVar i = Term.Var_ (yIVarName i);;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- reflexivity                                                     *)
(*   x = x                                                                   *)
(* ------------------------------------------------------------------------- *)

let reflexivityRule x = Thm.refl x;;

let reflexivity = reflexivityRule xVar;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------- symmetry                                            *)
(*   ~(x = y) \/ y = x                                                       *)
(* ------------------------------------------------------------------------- *)

let symmetryRule x y =
  let reflTh = reflexivityRule x in
  let reflLit = Thm.destUnit reflTh in
  let eqTh = Thm.equality reflLit [0] y in
  Thm.resolve reflLit reflTh eqTh
;;

let symmetry = symmetryRule xVar yVar;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------- transitivity                            *)
(*   ~(x = y) \/ ~(y = z) \/ x = z                                           *)
(* ------------------------------------------------------------------------- *)

let transitivity =
  let eqTh = Thm.equality (Literal.mkEq (yVar,zVar)) [0] xVar in
  Thm.resolve (Literal.mkEq (yVar,xVar)) symmetry eqTh
;;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ C                                                              *)
(* -------------- symEq (x = y)                                              *)
(*   y = x \/ C                                                              *)
(* ------------------------------------------------------------------------- *)

let symEq lit th =
  let (x,y) = Literal.destEq lit in
  if Term.equal x y then th
  else
    let sub = Substitute.fromList [(xVarName,x);(yVarName,y)] in
    let symTh = Thm.subst sub symmetry in
    Thm.resolve lit th symTh
;;

(* ------------------------------------------------------------------------- *)
(* An equation consists of two terms (t,u) plus a theorem (stronger than)    *)
(* t = u \/ C.                                                               *)
(* ------------------------------------------------------------------------- *)

type equation = (Term.term * Term.term) * Thm.thm;;

let equationLiteral (t_u,th) =
  let lit = Literal.mkEq t_u in
  if Literal.Set.member lit (Thm.clause th) then Some lit else None
;;

let reflEqn t = ((t,t), Thm.refl t);;

let symEqn (((t,u), th) as eqn) =
  if Term.equal t u then eqn
  else
    ((u,t), match equationLiteral eqn with
            |  Some t_u -> symEq t_u th
            | None -> th);;

let transEqn (((x,y), th1) as eqn1) (((_,z), th2) as eqn2) =
  if Term.equal x y then eqn2
  else if Term.equal y z then eqn1
  else if Term.equal x z then reflEqn x
  else
    ((x,z), match equationLiteral eqn1 with
            | None -> th1
            | Some x_y ->
                match equationLiteral eqn2 with
                | None -> th2
                | Some y_z ->
                    let sub =
                      Substitute.fromList [(xVarName,x); (yVarName,y);
                                           (zVarName,z)] in
                    let th = Thm.subst sub transitivity in
                    let th = Thm.resolve x_y th1 th in
                    let th = Thm.resolve y_z th2 th in
                    th);;

(* ------------------------------------------------------------------------- *)
(* A conversion takes a term t and either:                                   *)
(* 1. Returns a term u together with a theorem (stronger than) t = u \/ C.   *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type conv = Term.term -> Term.term * Thm.thm;;

let allConv tm = (tm, Thm.refl tm);;

let noConv : conv = fun _ -> raise (Error "noConv");;

let thenConvTrans tm (tm',th1) (tm'',th2) =
  let eqn1 = ((tm,tm'),th1)
  and eqn2 = ((tm',tm''),th2) in
  let (_,th) = transEqn eqn1 eqn2 in
  (tm'',th)
;;

let thenConv conv1 conv2 tm =
  let (tm',_) as res1 = conv1 tm in
  let res2 = conv2 tm' in
  thenConvTrans tm res1 res2
;;

let orelseConv (conv1 : conv) conv2 tm = try conv1 tm with Error _ -> conv2 tm;;

let tryConv conv = orelseConv conv allConv;;

let changedConv conv tm =
  let (tm',_) as res = conv tm in
  if tm = tm' then raise (Error "changedConv") else res
;;

let rec repeatConv conv tm = tryConv (thenConv conv (repeatConv conv)) tm;;

let flip f = fun x y -> f y x;;

let rec firstConv tm = function
  | [] -> raise (Error "firstConv")
  | [conv] -> conv tm
  | (conv :: convs) -> orelseConv conv (flip firstConv convs) tm;;
let firstConv convs tm = firstConv tm convs;;

let rec everyConv tm = function
  | [] -> allConv tm
  | [conv] -> conv tm
  | (conv :: convs) -> thenConv conv (flip everyConv convs) tm;;
let everyConv convs tm = everyConv tm convs;;

let rewrConv (((x,y), eqTh) as eqn) path tm =
  if Term.equal x y then allConv tm
  else if List.null path then (y,eqTh)
  else
    let reflTh = Thm.refl tm in
    let reflLit = Thm.destUnit reflTh in
    let th = Thm.equality reflLit (1 :: path) y in
    let th = Thm.resolve reflLit reflTh th in
    let th =
      match equationLiteral eqn with
      | None -> th
      | Some x_y -> Thm.resolve x_y eqTh th in
    let tm' = Term.replace tm (path,y) in
    (tm',th)
;;

let pathConv conv path tm =
  let x = Term.subterm tm path in
  let (y,th) = conv x in
  rewrConv ((x,y),th) path tm
;;

let subtermConv conv i = pathConv conv [i];;

let subtermsConv conv = function
  | (Term.Var_ _ as tm) -> allConv tm
  | (Term.Fn (_,a) as tm) ->
      everyConv (List.map (subtermConv conv) (interval 0 (length a))) tm;;

(* ------------------------------------------------------------------------- *)
(* Applying a conversion to every subterm, with some traversal strategy.     *)
(* ------------------------------------------------------------------------- *)

let rec bottomUpConv conv tm =
  thenConv (subtermsConv (bottomUpConv conv)) (repeatConv conv) tm;;

let rec topDownConv conv tm =
  thenConv (repeatConv conv) (subtermsConv (topDownConv conv)) tm;;

let repeatTopDownConv conv =
  let rec f tm = thenConv (repeatConv conv) g tm
  and g tm = thenConv (subtermsConv f) h tm
  and h tm = tryConv (thenConv conv f) tm in
  f
;;

(* ------------------------------------------------------------------------- *)
(* A literule (bad pun) takes a literal L and either:                        *)
(* 1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.     *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type literule = Literal.literal -> Literal.literal * Thm.thm;;

let allLiterule lit = (lit, Thm.assume lit);;

let noLiterule : literule = fun _ -> raise (Error "noLiterule");;

let thenLiterule literule1 literule2 lit =
  let (lit',th1) as res1 = literule1 lit in
  let (lit'',th2) as res2 = literule2 lit' in
  if Literal.equal lit lit' then res2
  else if Literal.equal lit' lit'' then res1
  else if Literal.equal lit lit'' then allLiterule lit
  else
    (lit'',
     (if not (Thm.member lit' th1) then th1
     else if not (Thm.negateMember lit' th2) then th2
     else Thm.resolve lit' th1 th2))
;;

let orelseLiterule (literule1 : literule) literule2 lit =
  try literule1 lit with Error _ -> literule2 lit;;

let tryLiterule literule = orelseLiterule literule allLiterule;;

let changedLiterule literule lit =
  let (lit',_) as res = literule lit in
  if lit = lit' then raise (Error "changedLiterule") else res
;;

let rec repeatLiterule literule lit =
  tryLiterule (thenLiterule literule (repeatLiterule literule)) lit;;

let rec firstLiterule lit = function
  | [] -> raise (Error "firstLiterule")
  | [literule] -> literule lit
  | (literule :: literules) ->
    orelseLiterule literule (flip firstLiterule literules) lit;;
let firstLiterule literules lit = firstLiterule lit literules;;

let rec everyLiterule lit = function
  | [] -> allLiterule lit
  | [literule] -> literule lit
  | (literule :: literules) ->
    thenLiterule literule (flip everyLiterule literules) lit;;
let everyLiterule literules lit = everyLiterule lit literules;;

let rewrLiterule (((x,y),eqTh) as eqn) path lit =
  if Term.equal x y then allLiterule lit
  else
    let th = Thm.equality lit path y in
    let th = match equationLiteral eqn with
             | None -> th
             | Some x_y -> Thm.resolve x_y eqTh th in
    let lit' = Literal.replace lit (path,y) in
    (lit',th)
;;

let pathLiterule conv path lit =
  let tm = Literal.subterm lit path in
  let (tm',th) = conv tm in
  rewrLiterule ((tm,tm'),th) path lit
;;

let argumentLiterule conv i = pathLiterule conv [i];;

let allArgumentsLiterule conv lit =
  everyLiterule
  (List.map (argumentLiterule conv) (interval 0 (Literal.arity lit))) lit;;

(* ------------------------------------------------------------------------- *)
(* A rule takes one theorem and either deduces another or raises an Error    *)
(* exception.                                                                *)
(* ------------------------------------------------------------------------- *)

type rule = Thm.thm -> Thm.thm;;

let allRule : rule = fun th -> th;;

let noRule : rule = fun _ -> raise (Error "noRule");;

let thenRule (rule1 : rule) (rule2 : rule) th = rule1 (rule2 th);;

let orelseRule (rule1 : rule) rule2 th = try rule1 th with Error _ -> rule2 th;;

let tryRule rule = orelseRule rule allRule;;

let changedRule rule th =
  let th' = rule th in
  if not (Literal.Set.equal (Thm.clause th) (Thm.clause th')) then th'
  else raise (Error "changedRule")
;;

let rec repeatRule rule lit = tryRule (thenRule rule (repeatRule rule)) lit;;

let rec firstRule th = function
  | [] -> raise (Error "firstRule")
  | [rule] -> rule th
  | (rule :: rules) -> orelseRule rule (flip firstRule rules) th;;
let firstRule rules th = firstRule th rules;;

let rec everyRule th = function
  | [] -> allRule th
  | [rule] -> rule th
  | (rule :: rules) -> thenRule rule (flip everyRule rules) th;;
let everyRule rules th = everyRule th rules;;

let literalRule literule lit th =
  let (lit',litTh) = literule lit in
  if Literal.equal lit lit' then th
  else if not (Thm.negateMember lit litTh) then litTh
  else Thm.resolve lit th litTh
;;

let rewrRule eqTh lit path = literalRule (rewrLiterule eqTh path) lit;;

let pathRule conv lit path = literalRule (pathLiterule conv path) lit;;

let literalsRule literule =
  let f (lit,th) =
    if Thm.member lit th then literalRule literule lit th else th in
  fun lits -> fun th -> Literal.Set.foldl f th lits
;;

let allLiteralsRule literule th = literalsRule literule (Thm.clause th) th;;

let convRule conv = allLiteralsRule (allArgumentsLiterule conv);;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- functionCongruence (f,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   f x0 ... x{n-1} = f y0 ... y{n-1}                                       *)
(* ------------------------------------------------------------------------- *)

let functionCongruence (f,n) =
  let xs = List.tabulate n xIVar
  and ys = List.tabulate n yIVar in
  let cong ((i,yi),(th,lit)) =
    let path = [1;i] in
    let th = Thm.resolve lit th (Thm.equality lit path yi) in
    let lit = Literal.replace lit (path,yi) in
    (th,lit) in
  let reflTh = Thm.refl (Term.Fn (f,xs)) in
  let reflLit = Thm.destUnit reflTh in
  fst (List.foldl (curry cong) (reflTh,reflLit) (enumerate ys))
;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- relationCongruence (R,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}                                     *)
(* ------------------------------------------------------------------------- *)

let relationCongruence (r,n) =
  let xs = List.tabulate n xIVar
  and ys = List.tabulate n yIVar in
  let cong ((i,yi),(th,lit)) =
    let path = [i] in
    let th = Thm.resolve lit th (Thm.equality lit path yi) in
    let lit = Literal.replace lit (path,yi) in
    (th,lit) in
  let assumeLit = (false,(r,xs)) in
  let assumeTh = Thm.assume assumeLit in
  fst (List.foldl (curry cong) (assumeTh,assumeLit) (enumerate ys))
;;

(* ------------------------------------------------------------------------- *)
(*   ~(x = y) \/ C                                                           *)
(* ----------------- symNeq ~(x = y)                                         *)
(*   ~(y = x) \/ C                                                           *)
(* ------------------------------------------------------------------------- *)

let symNeq lit th =
  let (x,y) = Literal.destNeq lit in
  if Term.equal x y then th
  else
    let sub = Substitute.fromList [(xVarName,y);(yVarName,x)] in
    let symTh = Thm.subst sub symmetry in
    Thm.resolve lit th symTh
;;

(* ------------------------------------------------------------------------- *)
(* sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)           *)
(* ------------------------------------------------------------------------- *)

let sym ((pol,_) as lit) th = if pol then symEq lit th else symNeq lit th;;

(* ------------------------------------------------------------------------- *)
(*   ~(x = x) \/ C                                                           *)
(* ----------------- removeIrrefl                                            *)
(*         C                                                                 *)
(*                                                                           *)
(* where all irreflexive equalities.                                         *)
(* ------------------------------------------------------------------------- *)

let removeIrrefl th =
  let irrefl = function
    | ((true,_),th) -> th
    | ((false,atm) as lit, th) ->
        match total Atom.destRefl atm with
        | Some x -> Thm.resolve lit th (Thm.refl x)
        | None -> th in
  Literal.Set.foldl irrefl th (Thm.clause th);;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ y = x \/ C                                                     *)
(* ----------------------- removeSym                                         *)
(*       x = y \/ C                                                          *)
(*                                                                           *)
(* where all duplicate copies of equalities and disequalities are removed.   *)
(* ------------------------------------------------------------------------- *)

let removeSym th =
  let rem ((pol,atm) as lit, (eqs,th)) =
    match total Atom.sym atm with
    | None -> (eqs, th)
    | Some atm' ->
        if Literal.Set.member lit eqs then
          (eqs, (if pol then symEq lit th else symNeq lit th))
        else
          (Literal.Set.add eqs (pol,atm'), th) in
  snd (Literal.Set.foldl rem (Literal.Set.empty,th) (Thm.clause th));;

(* ------------------------------------------------------------------------- *)
(*   ~(v = t) \/ C                                                           *)
(* ----------------- expandAbbrevs                                           *)
(*      C[t/v]                                                               *)
(*                                                                           *)
(* where t must not contain any occurrence of the variable v.                *)
(* ------------------------------------------------------------------------- *)

let rec expandAbbrevs th =
  let expand lit =
    let (x,y) = Literal.destNeq lit in
    let _ = Term.isTypedVar x || Term.isTypedVar y ||
            raise (Error "Rule.expandAbbrevs: no vars") in
    let _ = not (Term.equal x y) ||
            raise (Error "Rule.expandAbbrevs: equal vars") in
    Substitute.unify Substitute.empty x y in
  match Literal.Set.firstl (total expand) (Thm.clause th) with
  | None -> removeIrrefl th
  | Some sub -> expandAbbrevs (Thm.subst sub th);;

(* ------------------------------------------------------------------------- *)
(* simplify = isTautology + expandAbbrevs + removeSym                        *)
(* ------------------------------------------------------------------------- *)

let rec simplify th =
  if Thm.isTautology th then None
  else
    let th' = th in
    let th' = expandAbbrevs th' in
    let th' = removeSym th' in
    if Thm.equal th th' then Some th else simplify th'
;;

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- freshVars                                                        *)
(*   C[s]                                                                    *)
(*                                                                           *)
(* where s is a renaming substitution chosen so that all of the variables in *)
(* C are replaced by fresh variables.                                        *)
(* ------------------------------------------------------------------------- *)

let freshVars th = Thm.subst (Substitute.freshVars (Thm.freeVars th)) th;;

(* ------------------------------------------------------------------------- *)
(*               C                                                           *)
(* ---------------------------- factor                                       *)
(*   C_s_1, C_s_2, ..., C_s_n                                                *)
(*                                                                           *)
(* where each s_i is a substitution that factors C, meaning that the theorem *)
(*                                                                           *)
(*   C_s_i = (removeIrrefl o removeSym o Thm.subst s_i) C                    *)
(*                                                                           *)
(* has fewer literals than C.                                                *)
(*                                                                           *)
(* Also, if s is any substitution that factors C, then one of the s_i will   *)
(* result in a theorem C_s_i that strictly subsumes the theorem C_s.         *)
(* ------------------------------------------------------------------------- *)

type edge =
  | Factor_edge of Atom.atom * Atom.atom
  | Refl_edge of Term.term * Term.term;;

type joinStatus =
  | Joined
  | Joinable of Substitute.subst
  | Apart;;

let joinEdge sub edge =
  let result =
    match edge with
    | Factor_edge (atm,atm') -> total (Atom.unify sub atm) atm'
    | Refl_edge (tm,tm') -> total (Substitute.unify sub tm) tm' in
        match result with
        | None -> Apart
        | Some sub' ->
          if Portable.pointerEqual (sub,sub') then Joined else Joinable sub'
;;

let updateApart sub =
  let rec update acc = function
    | [] -> Some acc
    | edge :: edges ->
        match joinEdge sub edge with
        | Joined -> None
        | Joinable _ -> update (edge :: acc) edges
        | Apart -> update acc edges in
  update []
;;

let addFactorEdge (pol,atm) ((pol',atm'),acc) =
  if pol <> pol' then acc else
    let edge = Factor_edge (atm,atm') in
    match joinEdge Substitute.empty edge with
    | Joined -> raise (Bug "addFactorEdge: joined")
    | Joinable sub -> (sub,edge) :: acc
    | Apart -> acc
;;

let addReflEdge = function
  | ((false,_), acc) -> acc
  | ((true,atm), acc) ->
      let edge = let (x,y) = (Atom.destEq atm) in Refl_edge (x,y) in
      match joinEdge Substitute.empty edge with
      | Joined -> raise (Bug "addRefl: joined")
      | Joinable _ -> edge :: acc
      | Apart -> acc
;;
let addReflEdge = curry addReflEdge;;

let addIrreflEdge = function
  | ((true,_), acc) -> acc
  | ((false,atm), acc) ->
      let edge = let (x,y) = (Atom.destEq atm) in Refl_edge (x,y) in
      match joinEdge Substitute.empty edge with
      | Joined -> raise (Bug "addRefl: joined")
      | Joinable sub -> (sub,edge) :: acc
      | Apart -> acc
;;
let addIrreflEdge = curry addIrreflEdge;;

let rec init_edges acc apart = function
  | [] ->
      let init ((apart,sub,edge),(edges,acc)) =
        (edge :: edges, (apart,sub,edges) :: acc) in
      snd (List.foldl (curry init) ([],[]) acc)
  | ((sub,edge) :: sub_edges) ->
      let (acc,apart) =
        match updateApart sub apart with
        | Some apart' -> ((apart',sub,edge) :: acc, edge :: apart)
        | None -> (acc,apart) in
      init_edges acc apart sub_edges
;;

let rec mk_edges apart sub_edges = function
  | [] -> init_edges [] apart sub_edges
  | lit :: lits ->
      let sub_edges = List.foldl (curry (addFactorEdge lit)) sub_edges lits in
      let (apart,sub_edges) =
        match total Literal.sym lit with
        | None -> (apart,sub_edges)
        | Some lit' ->
            let apart = addReflEdge lit apart in
            let sub_edges = addIrreflEdge lit sub_edges in
            let sub_edges = List.foldl (curry (addFactorEdge lit')) sub_edges lits in
            (apart,sub_edges) in
      mk_edges apart sub_edges lits
;;

let rec fact acc = function
  | [] -> acc
  | ((_,sub,[]) :: others) -> fact (sub :: acc) others
  | ((apart, sub, edge :: edges) :: others) ->
      let others =
        match joinEdge sub edge with
        | Joinable sub' ->
            let others = (edge :: apart, sub, edges) :: others in
            begin
              match updateApart sub' apart with
              | None -> others
              | Some apart' -> (apart',sub',edges) :: others
            end
       | _ -> (apart,sub,edges) :: others in
      fact acc others
;;

let factor' cl =
  let edges = mk_edges [] [] (Literal.Set.toList cl) in
  let result = fact [] edges in
  result
;;

let factor th =
  let fact sub = removeIrrefl (removeSym (Thm.subst sub th)) in
  List.map fact (factor' (Thm.clause th))
;;

end (* struct Rule *)
;;
