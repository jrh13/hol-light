(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* ========================================================================= *)

module Model = struct

open Useful;;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

let maxSpace = 1000;;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let multInt =
    match Int.maxInt with
      None -> (fun x -> fun y -> Some (x * y))
    | Some m ->
        let m = Real.floor (Math.sqrt (Real.fromInt m))
      in
        fun x -> fun y -> if x <= m && y <= m then Some (x * y) else None
      ;;

  let rec iexp x y acc =
      if y mod 2 = 0 then iexp' x y acc
      else
        match multInt acc x with
          Some acc -> iexp' x y acc
        | None -> None

  and iexp' x y acc =
      if y = 1 then Some acc
      else
          let y = Int.div y 2
        in
          match multInt x x with
            Some x -> iexp x y acc
          | None -> None
        ;;

  let expInt x y =
      if y <= 1 then
        if y = 0 then Some 1
        else if y = 1 then Some x
        else raise (Bug "expInt: negative exponent")
      else if x <= 1 then
        if 0 <= x then Some x
        else raise (Bug "expInt: negative exponand")
      else iexp x y 1;;

let boolToInt = function
    true -> 1
  | false -> 0;;

let intToBool = function
    1 -> true
  | 0 -> false
  | _ -> raise (Bug "Model.intToBool");;

let minMaxInterval i j = interval i (1 + j - i);;

(* ------------------------------------------------------------------------- *)
(* Model size.                                                               *)
(* ------------------------------------------------------------------------- *)

type size = {size : int};;

(* ------------------------------------------------------------------------- *)
(* A model of size N has integer elements 0...N-1.                           *)
(* ------------------------------------------------------------------------- *)

type element = int;;

let zeroElement = 0;;

let incrementElement {size = n} i =
      let i = i + 1
    in
      if i = n then None else Some i
    ;;

let elementListSpace {size = n} arity =
    match expInt n arity with
      None -> None
    | Some m as s -> if m <= maxSpace then s else None;;

let elementListIndex {size = n} =
      let rec f acc elts =
          match elts with
            [] -> acc
          | elt :: elts -> f (n * acc + elt) elts
    in
      f 0
    ;;

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* ------------------------------------------------------------------------- *)

type fixedFunction = size -> element list -> element option;;

type fixedRelation = size -> element list -> bool option;;

type fixed =
      {functions : fixedFunction Name_arity.Map.map;
       relations : fixedRelation Name_arity.Map.map};;

let uselessFixedFunction : fixedFunction = kComb (kComb None);;

let uselessFixedRelation : fixedRelation = kComb (kComb None);;

let emptyFunctions : fixedFunction Name_arity.Map.map = Name_arity.Map.newMap ();;

let emptyRelations : fixedRelation Name_arity.Map.map = Name_arity.Map.newMap ();;

let fixed0 f sz elts =
    match elts with
      [] -> f sz
    | _ -> raise (Bug "Model.fixed0: wrong arity");;

let fixed1 f sz elts =
    match elts with
      [x] -> f sz x
    | _ -> raise (Bug "Model.fixed1: wrong arity");;

let fixed2 f sz elts =
    match elts with
      [x;y] -> f sz x y
    | _ -> raise (Bug "Model.fixed2: wrong arity");;

let emptyFixed =
      let fns = emptyFunctions
      and rels = emptyRelations
    in
        {functions = fns;
         relations = rels}
    ;;

let peekFunctionFixed fix name_arity =
      let {functions = fns} = fix
    in
      Name_arity.Map.peek fns name_arity
    ;;

let peekRelationFixed fix name_arity =
      let {relations = rels} = fix
    in
      Name_arity.Map.peek rels name_arity
    ;;

let getFunctionFixed fix name_arity =
    match peekFunctionFixed fix name_arity with
      Some f -> f
    | None -> uselessFixedFunction;;

let getRelationFixed fix name_arity =
    match peekRelationFixed fix name_arity with
      Some rel -> rel
    | None -> uselessFixedRelation;;

let insertFunctionFixed fix name_arity_fun =
      let {functions = fns; relations = rels} = fix

      in let fns = Name_arity.Map.insert fns name_arity_fun
    in
        {functions = fns;
         relations = rels}
    ;;

let insertRelationFixed fix name_arity_rel =
      let {functions = fns; relations = rels} = fix

      in let rels = Name_arity.Map.insert rels name_arity_rel
    in
        {functions = fns;
         relations = rels}
    ;;

  let union _ = raise (Bug "Model.unionFixed: nameArity clash");;
  let unionFixed fix1 fix2 =
        let {functions = fns1; relations = rels1} = fix1
        and {functions = fns2; relations = rels2} = fix2

        in let fns = Name_arity.Map.union union fns1 fns2

        in let rels = Name_arity.Map.union union rels1 rels2
      in
          {functions = fns;
           relations = rels}
      ;;

let unionListFixed =
      let union (fix,acc) = unionFixed acc fix
    in
      Mlist.foldl union emptyFixed
    ;;

  let hasTypeFn _ elts =
      match elts with
        [x;_] -> Some x
      | _ -> raise (Bug "Model.hasTypeFn: wrong arity");;

  let eqRel _ elts =
      match elts with
        [x;y] -> Some (x = y)
      | _ -> raise (Bug "Model.eqRel: wrong arity");;

  let basicFixed =
        let fns = Name_arity.Map.singleton (Term.hasTypeFunction,hasTypeFn)

        in let rels = Name_arity.Map.singleton (Atom.eqRelation,eqRel)
      in
          {functions = fns;
           relations = rels}
      ;;

(* ------------------------------------------------------------------------- *)
(* Renaming fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

type fixedMap =
     {functionMap : Name.name Name_arity.Map.map;
      relationMap : Name.name Name_arity.Map.map};;

let mapFixed fixMap fix =
      let {functionMap = fnMap; relationMap = relMap} = fixMap
      and {functions = fns; relations = rels} = fix

      in let fns = Name_arity.Map.compose fnMap fns

      in let rels = Name_arity.Map.compose relMap rels
    in
        {functions = fns;
         relations = rels}
    ;;


(* ------------------------------------------------------------------------- *)
(* Standard fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

(* Projections *)

let projectionMin = 1
and projectionMax = 9;;

let projectionList = minMaxInterval projectionMin projectionMax;;

let projectionName i =
      let _ = projectionMin <= i ||
              raise (Bug "Model.projectionName: less than projectionMin")

      in let _ = i <= projectionMax ||
              raise (Bug "Model.projectionName: greater than projectionMax")
    in
      Name.fromString ("project" ^ Int.toString i)
    ;;

let projectionFn i _ elts = Some (Mlist.nth (elts, i - 1));;

let arityProjectionFixed arity =
      let mkProj i = ((projectionName i, arity), projectionFn i)

      in let rec addProj i acc =
          if i > arity then acc
          else addProj (i + 1) (Name_arity.Map.insert acc (mkProj i))

      in let fns = addProj projectionMin emptyFunctions

      in let rels = emptyRelations
    in
        {functions = fns;
         relations = rels}
    ;;

let projectionFixed =
    unionListFixed (List.map arityProjectionFixed projectionList);;

(* Arithmetic *)

let numeralMin = -100
and numeralMax = 100;;

let numeralList = minMaxInterval numeralMin numeralMax;;

let numeralName i =
      let _ = numeralMin <= i ||
              raise (Bug "Model.numeralName: less than numeralMin")

      in let _ = i <= numeralMax ||
              raise (Bug "Model.numeralName: greater than numeralMax")

      in let s = if i < 0 then "negative" ^ Int.toString (-i) else Int.toString i
    in
      Name.fromString s
    ;;

let addName = Name.fromString "+"
and divName = Name.fromString "div"
and dividesName = Name.fromString "divides"
and evenName = Name.fromString "even"
and expName = Name.fromString "exp"
and geName = Name.fromString ">="
and gtName = Name.fromString ">"
and isZeroName = Name.fromString "isZero"
and leName = Name.fromString "<="
and ltName = Name.fromString "<"
and modName = Name.fromString "mod"
and multName = Name.fromString "*"
and negName = Name.fromString "~"
and oddName = Name.fromString "odd"
and preName = Name.fromString "pre"
and subName = Name.fromString "-"
and sucName = Name.fromString "suc";;

  (* Support *)

  let modN {size = n} x = x mod n;;

  let oneN sz = modN sz 1;;

  let multN sz (x,y) = modN sz (x * y);;

  (* Functions *)

  let numeralFn i sz = Some (modN sz i);;

  let addFn sz x y = Some (modN sz (x + y));;

  let divFn {size = n} x y =
        let y = if y = 0 then n else y
      in
        Some (Int.div x y)
      ;;

  let expFn sz x y = Some (exp (multN sz) x y (oneN sz));;

  let modFn {size = n} x y =
        let y = if y = 0 then n else y
      in
        Some (x mod y)
      ;;

  let multFn sz x y = Some (multN sz (x,y));;

  let negFn {size = n} x = Some (if x = 0 then 0 else n - x);;

  let preFn {size = n} x = Some (if x = 0 then n - 1 else x - 1);;

  let subFn {size = n} x y = Some (if x < y then n + x - y else x - y);;

  let sucFn {size = n} x = Some (if x = n - 1 then 0 else x + 1);;

  (* Relations *)

  let dividesRel _ x y = Some (divides x y);;

  let evenRel _ x = Some (x mod 2 = 0);;

  let geRel _ x y = Some (x >= y);;

  let gtRel _ x y = Some (x > y);;

  let isZeroRel _ x = Some (x = 0);;

  let leRel _ x y = Some (x <= y);;

  let ltRel _ x y = Some (x < y);;

  let oddRel _ x = Some (x mod 2 = 1);;

  let modularFixed =
        let fns =
            Name_arity.Map.fromList
              (List.map (fun i -> ((numeralName i,0), fixed0 (numeralFn i)))
                 numeralList @
               [((addName,2), fixed2 addFn);
                ((divName,2), fixed2 divFn);
                ((expName,2), fixed2 expFn);
                ((modName,2), fixed2 modFn);
                ((multName,2), fixed2 multFn);
                ((negName,1), fixed1 negFn);
                ((preName,1), fixed1 preFn);
                ((subName,2), fixed2 subFn);
                ((sucName,1), fixed1 sucFn)])

        in let rels =
            Name_arity.Map.fromList
              [((dividesName,2), fixed2 dividesRel);
               ((evenName,1), fixed1 evenRel);
               ((geName,2), fixed2 geRel);
               ((gtName,2), fixed2 gtRel);
               ((isZeroName,1), fixed1 isZeroRel);
               ((leName,2), fixed2 leRel);
               ((ltName,2), fixed2 ltRel);
               ((oddName,1), fixed1 oddRel)]
      in
          {functions = fns;
           relations = rels}
      ;;

  (* Support *)

  let cutN {size = n} x = if x >= n then n - 1 else x;;

  let oneN sz = cutN sz 1;;

  let multN sz (x,y) = cutN sz (x * y);;

  (* Functions *)

  let numeralFn i sz = if i < 0 then None else Some (cutN sz i);;

  let addFn sz x y = Some (cutN sz (x + y));;

  let divFn _ x y = if y = 0 then None else Some (Int.div x y);;

  let expFn sz x y = Some (exp (multN sz) x y (oneN sz));;

  let modFn {size = n} x y =
      if y = 0 || x = n - 1 then None else Some (x mod y);;

  let multFn sz x y = Some (multN sz (x,y));;

  let negFn _ x = if x = 0 then Some 0 else None;;

  let preFn _ x = if x = 0 then None else Some (x - 1);;

  let subFn {size = n} x y =
      if y = 0 then Some x
      else if x = n - 1 || x < y then None
      else Some (x - y);;

  let sucFn sz x = Some (cutN sz (x + 1));;

  (* Relations *)

  let dividesRel {size = n} x y =
      if x = 1 || y = 0 then Some true
      else if x = 0 then Some false
      else if y = n - 1 then None
      else Some (divides x y);;

  let evenRel {size = n} x =
      if x = n - 1 then None else Some (x mod 2 = 0);;

  let geRel {size = n} y x =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x <= y);;

  let gtRel {size = n} y x =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x < y);;

  let isZeroRel _ x = Some (x = 0);;

  let leRel {size = n} x y =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x <= y);;

  let ltRel {size = n} x y =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x < y);;

  let oddRel {size = n} x =
      if x = n - 1 then None else Some (x mod 2 = 1);;

  let overflowFixed =
        let fns =
            Name_arity.Map.fromList
              (List.map (fun i -> ((numeralName i,0), fixed0 (numeralFn i)))
                 numeralList @
               [((addName,2), fixed2 addFn);
                ((divName,2), fixed2 divFn);
                ((expName,2), fixed2 expFn);
                ((modName,2), fixed2 modFn);
                ((multName,2), fixed2 multFn);
                ((negName,1), fixed1 negFn);
                ((preName,1), fixed1 preFn);
                ((subName,2), fixed2 subFn);
                ((sucName,1), fixed1 sucFn)])

        in let rels =
            Name_arity.Map.fromList
              [((dividesName,2), fixed2 dividesRel);
               ((evenName,1), fixed1 evenRel);
               ((geName,2), fixed2 geRel);
               ((gtName,2), fixed2 gtRel);
               ((isZeroName,1), fixed1 isZeroRel);
               ((leName,2), fixed2 leRel);
               ((ltName,2), fixed2 ltRel);
               ((oddName,1), fixed1 oddRel)]
      in
          {functions = fns;
           relations = rels}
      ;;

(* Sets *)

let cardName = Name.fromString "card"
and complementName = Name.fromString "complement"
and differenceName = Name.fromString "difference"
and emptyName = Name.fromString "empty"
and memberName = Name.fromString "member"
and insertName = Name.fromString "insert"
and intersectName = Name.fromString "intersect"
and singletonName = Name.fromString "singleton"
and subsetName = Name.fromString "subset"
and symmetricDifferenceName = Name.fromString "symmetricDifference"
and unionName = Name.fromString "union"
and universeName = Name.fromString "universe";;

  (* Support *)

  let eltN {size = n} =
        let rec f acc = function
            0 -> acc
          | x -> f (acc + 1) (Int.div x 2)
      in
        f (-1) n
      ;;

  let posN i = Word.shiftLeft (1, Word.fromInt i);;

  let univN sz = Word.minus (posN (eltN sz), 1);;

  let setN sz x = Word.andb (Word.fromInt x, univN sz);;

  (* Functions *)

  let cardFn sz x =
        let rec f acc = function
            0 -> acc
          | s ->
              let acc = if Word.andb (s,1) = 0 then acc else acc + 1
            in
              f acc (Word.shiftRight (s,1))
      in
        Some (f (setN sz x) 0)
      ;;

  let complementFn sz x = Some (Word.toInt (Word.xorb (univN sz, setN sz x)));;

  let differenceFn sz x y =
        let x = setN sz x
        and y = setN sz y
      in
        Some (Word.toInt (Word.andb (x, Word.notb y)))
      ;;

  let emptyFn _ = Some 0;;

  let insertFn sz x y =
        let x = x mod eltN sz
        and y = setN sz y
      in
        Some (Word.toInt (Word.orb (posN x, y)))
      ;;

  let intersectFn sz x y =
      Some (Word.toInt (Word.andb (setN sz x, setN sz y)));;

  let singletonFn sz x =
        let x = x mod eltN sz
      in
        Some (Word.toInt (posN x))
      ;;

  let symmetricDifferenceFn sz x y =
        let x = setN sz x
        and y = setN sz y
      in
        Some (Word.toInt (Word.xorb (x,y)))
      ;;

  let unionFn sz x y =
      Some (Word.toInt (Word.orb (setN sz x, setN sz y)));;

  let universeFn sz = Some (Word.toInt (univN sz));;

  (* Relations *)

  let memberRel sz x y =
        let x = x mod eltN sz
        and y = setN sz y
      in
        Some (Word.andb (posN x, y) <> 0)
      ;;

  let subsetRel sz x y =
        let x = setN sz x
        and y = setN sz y
      in
        Some (Word.andb (x, Word.notb y) = 0)
      ;;

  let setFixed =
        let fns =
            Name_arity.Map.fromList
              [((cardName,1), fixed1 cardFn);
               ((complementName,1), fixed1 complementFn);
               ((differenceName,2), fixed2 differenceFn);
               ((emptyName,0), fixed0 emptyFn);
               ((insertName,2), fixed2 insertFn);
               ((intersectName,2), fixed2 intersectFn);
               ((singletonName,1), fixed1 singletonFn);
               ((symmetricDifferenceName,2), fixed2 symmetricDifferenceFn);
               ((unionName,2), fixed2 unionFn);
               ((universeName,0), fixed0 universeFn)]

        in let rels =
            Name_arity.Map.fromList
              [((memberName,2), fixed2 memberRel);
               ((subsetName,2), fixed2 subsetRel)]
      in
          {functions = fns;
           relations = rels}
      ;;

(* Lists *)

let appendName = Name.fromString "@"
and consName = Name.fromString "::"
and lengthName = Name.fromString "length"
and nilName = Name.fromString "nil"
and nullName = Name.fromString "null"
and tailName = Name.fromString "tail";;

  let baseFix =
        let fix = unionFixed projectionFixed overflowFixed

        in let sucFn = getFunctionFixed fix (sucName,1)

        in let suc2Fn sz _ x = sucFn sz [x]
      in
        insertFunctionFixed fix ((sucName,2), fixed2 suc2Fn)
      ;;

  let fixMap =
      {functionMap = Name_arity.Map.fromList
                       [((appendName,2),addName);
                        ((consName,2),sucName);
                        ((lengthName,1), projectionName 1);
                        ((nilName,0), numeralName 0);
                        ((tailName,1),preName)];
       relationMap = Name_arity.Map.fromList
                       [((nullName,1),isZeroName)]};;

  let listFixed = mapFixed fixMap baseFix;;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = Valuation of element Name.Map.map;;

let emptyValuation = Valuation (Name.Map.newMap ());;

let insertValuation (Valuation m) v_i = Valuation (Name.Map.insert m v_i);;

let peekValuation (Valuation m) v = Name.Map.peek m v;;

let constantValuation i =
      let add (v,v') = insertValuation v' (v,i)
    in
      Name.Set.foldl add emptyValuation
    ;;

let zeroValuation = constantValuation zeroElement;;

let getValuation v' v =
    match peekValuation v' v with
      Some i -> i
    | None -> raise (Error "Model.getValuation: incomplete valuation");;

let randomValuation {size = n} vs =
      let f (v,v') = insertValuation v' (v, Portable.randomInt n)
    in
      Name.Set.foldl f emptyValuation vs
    ;;

let incrementValuation n vars =
      let rec inc vs v' =
          match vs with
            [] -> None
          | v :: vs ->
              let (carry,i) =
                  match incrementElement n (getValuation v' v) with
                    Some i -> (false,i)
                  | None -> (true,zeroElement)

              in let v' = insertValuation v' (v,i)
            in
              if carry then inc vs v' else Some v'
    in
      inc (Name.Set.toList vars)
    ;;

let foldValuation n vars f =
      let inc = incrementValuation n vars

      in let rec fold v' acc =
            let acc = f (v',acc)
          in
            match inc v' with
              None -> acc
            | Some v' -> fold v' acc

      in let zero = zeroValuation vars
    in
      fold zero
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of random finite mapping Z^n -> Z.                                 *)
(* ------------------------------------------------------------------------- *)

let cUNKNOWN = -1;;

type table =
    Forgetful_table
  | Array_table of int array;;

let newTable n arity =
    match elementListSpace {size = n} arity with
      None -> Forgetful_table
    | Some space -> Array_table (Array.make space cUNKNOWN);;


  let randomResult r = Portable.randomInt r;;
  let lookupTable n vR table elts =
      match table with
        Forgetful_table -> randomResult vR
      | Array_table a ->
          let i = elementListIndex {size = n} elts

          in let r = Array.get a i
        in
          if r <> cUNKNOWN then r
          else
              let r = randomResult vR

              in let () = Array.set a i r
            in
              r
        ;;

let updateTable n table (elts,r) =
    match table with
      Forgetful_table -> ()
    | Array_table a ->
        let i = elementListIndex {size = n} elts

        in let () = Array.set a i r
      in
        ()
      ;;

(* ------------------------------------------------------------------------- *)
(* A type of random finite mappings name * arity -> Z^arity -> Z.            *)
(* ------------------------------------------------------------------------- *)

type tables =
      {domainSize : int;
       rangeSize : int;
       tableMap : table Name_arity.Map.map ref};;

let newTables n vR =
      {domainSize = n;
       rangeSize = vR;
       tableMap = ref (Name_arity.Map.newMap ())};;

let getTables tables n_a =
      let {domainSize = n; rangeSize = _; tableMap = tm} = tables

      in let m = !tm
    in
      match Name_arity.Map.peek m n_a with
        Some t -> t
      | None ->
          let (_,a) = n_a

          in let t = newTable n a

          in let m = Name_arity.Map.insert m (n_a,t)

          in let () = tm := m
        in
          t
    ;;

let lookupTables tables (n,elts) =
      let {domainSize = vN; rangeSize = vR} = tables

      in let a = length elts

      in let table = getTables tables (n,a)
    in
      lookupTable vN vR table elts
    ;;

let updateTables tables ((n,elts),r) =
      let {domainSize = vN} = tables

      in let a = length elts

      in let table = getTables tables (n,a)
    in
      updateTable vN table (elts,r)
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {sizep : int; fixed : fixed};;

type model =
      {sizem : int;
       fixedFunctions : (element list -> element option) Name_arity.Map.map;
       fixedRelations : (element list -> bool option) Name_arity.Map.map;
       randomFunctions : tables;
       randomRelations : tables};;

let newModel {sizep = vN; fixed = fixed} =
      let {functions = fns; relations = rels} = fixed

      in let fixFns = Name_arity.Map.transform (fun f -> f {size = vN}) fns
      and fixRels = Name_arity.Map.transform (fun r -> r {size = vN}) rels

      in let rndFns = newTables vN vN
      and rndRels = newTables vN 2
    in
        {sizem = vN;
         fixedFunctions = fixFns;
         fixedRelations = fixRels;
         randomFunctions = rndFns;
         randomRelations = rndRels}
    ;;

let msize ({sizem = vN}) = vN;;
let psize ({sizep = vN}) = vN;;

let peekFixedFunction vM (n,elts) =
      let {fixedFunctions = fixFns} = vM
    in
      match Name_arity.Map.peek fixFns (n, length elts) with
        None -> None
      | Some fixFn -> fixFn elts
    ;;

let isFixedFunction vM n_elts = Option.isSome (peekFixedFunction vM n_elts);;

let peekFixedRelation vM (n,elts) =
      let {fixedRelations = fixRels} = vM
    in
      match Name_arity.Map.peek fixRels (n, length elts) with
        None -> None
      | Some fixRel -> fixRel elts
    ;;

let isFixedRelation vM n_elts = Option.isSome (peekFixedRelation vM n_elts);;

(* A default model *)

let defaultSize = 8;;

let defaultFixed =
    unionListFixed
      [basicFixed;
       projectionFixed;
       modularFixed;
       setFixed;
       listFixed];;

let default = {sizep = defaultSize; fixed = defaultFixed};;

(* ------------------------------------------------------------------------- *)
(* Taking apart terms to interpret them.                                     *)
(* ------------------------------------------------------------------------- *)

let destTerm tm =
    match tm with
      Term.Var _ -> tm
    | Term.Fn f_tms ->
      match Term.stripApp tm with
        (_,[]) -> tm
      | (Term.Var _ as v, tms) -> Term.Fn (Term.appName, v :: tms)
      | (Term.Fn (f,tms), tms') -> Term.Fn (f, tms @ tms');;

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

let interpretFunction vM n_elts =
    match peekFixedFunction vM n_elts with
      Some r -> r
    | None ->
        let {randomFunctions = rndFns} = vM
      in
        lookupTables rndFns n_elts
      ;;

let interpretRelation vM n_elts =
    match peekFixedRelation vM n_elts with
      Some r -> r
    | None ->
        let {randomRelations = rndRels} = vM
      in
        intToBool (lookupTables rndRels n_elts)
      ;;

let interpretTerm vM vV =
      let rec interpret tm =
          match destTerm tm with
            Term.Var v -> getValuation vV v
          | Term.Fn (f,tms) -> interpretFunction vM (f, List.map interpret tms)
    in
      interpret
    ;;

let interpretAtom vM vV (r,tms) =
    interpretRelation vM (r, List.map (interpretTerm vM vV) tms);;

let interpretFormula vM =
      let vN = msize vM

      in let rec interpret vV fm =
          match fm with
            Formula.True -> true
          | Formula.False -> false
          | Formula.Atom atm -> interpretAtom vM vV atm
          | Formula.Not p -> not (interpret vV p)
          | Formula.Or (p,q) -> interpret vV p || interpret vV q
          | Formula.And (p,q) -> interpret vV p && interpret vV q
          | Formula.Imp (p,q) -> interpret vV (Formula.Or (Formula.Not p, q))
          | Formula.Iff (p,q) -> interpret vV p = interpret vV q
          | Formula.Forall (v,p) -> interpret' vV p v vN
          | Formula.Exists (v,p) ->
            interpret vV (Formula.Not (Formula.Forall (v, Formula.Not p)))

      and interpret' vV fm v i =
          i = 0 ||
            let i = i - 1
            in let vV' = insertValuation vV (v,i)
          in
            interpret vV' fm && interpret' vV fm v i

    in
      interpret
    ;;

let interpretLiteral vM vV (pol,atm) =
      let b = interpretAtom vM vV atm
    in
      if pol then b else not b
    ;;

let interpretClause vM vV cl = Literal.Set.exists (interpretLiteral vM vV) cl;;

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

let check interpret maxChecks vM fv x =
      let vN = msize vM

      in let score (vV,(vT,vF)) =
          if interpret vM vV x then (vT + 1, vF) else (vT, vF + 1)

      in let randomCheck acc = score (randomValuation {size = vN} fv, acc)

      in let maxChecks =
          match maxChecks with
            None -> maxChecks
          | Some m ->
            match expInt vN (Name.Set.size fv) with
              Some n -> if n <= m then None else maxChecks
            | None -> maxChecks
    in
      match maxChecks with
        Some m -> funpow m randomCheck (0, 0)
      | None -> foldValuation {size = vN} fv score (0, 0)
    ;;

let checkAtom maxChecks vM atm =
    check interpretAtom maxChecks vM (Atom.freeVars atm) atm;;

let checkFormula maxChecks vM fm =
    check interpretFormula maxChecks vM (Formula.freeVars fm) fm;;

let checkLiteral maxChecks vM lit =
    check interpretLiteral maxChecks vM (Literal.freeVars lit) lit;;

let checkClause maxChecks vM cl =
    check interpretClause maxChecks vM (Literal.Set.freeVars cl) cl;;

(* ------------------------------------------------------------------------- *)
(* Updating the model.                                                       *)
(* ------------------------------------------------------------------------- *)

let updateFunction vM func_elts_elt =
      let {randomFunctions = rndFns} = vM

      in let () = updateTables rndFns func_elts_elt
    in
      ()
    ;;

let updateRelation vM (rel_elts,pol) =
      let {randomRelations = rndRels} = vM

      in let () = updateTables rndRels (rel_elts, boolToInt pol)
    in
      ()
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of terms with interpretations embedded in the subterms.            *)
(* ------------------------------------------------------------------------- *)

type modelTerm =
    Model_var
  | Model_fn of Term.functionName * modelTerm list * int list;;

let modelTerm vM vV =
      let rec modelTm tm =
          match destTerm tm with
            Term.Var v -> (Model_var, getValuation vV v)
          | Term.Fn (f,tms) ->
              let (tms,xs) = unzip (List.map modelTm tms)
            in
              (Model_fn (f,tms,xs), interpretFunction vM (f,xs))
    in
      modelTm
    ;;

(* ------------------------------------------------------------------------- *)
(* Perturbing the model.                                                     *)
(* ------------------------------------------------------------------------- *)

type perturbation =
    Function_perturbation of (Term.functionName * element list) * element
  | Relation_perturbation of (Atom.relationName * element list) * bool;;

let perturb vM pert =
    match pert with
      Function_perturbation ((func,elts),elt) -> updateFunction vM ((func,elts),elt)
    | Relation_perturbation ((rel,elts),pol) -> updateRelation vM ((rel,elts),pol);;

  let rec pertTerm vM target tm acc =
      match target with [] -> acc | _ ->
      (match tm with
        Model_var -> acc
      | Model_fn (func,tms,xs) ->
          let onTarget ys = mem (interpretFunction vM (func,ys)) target

          in let func_xs = (func,xs)

          in let acc =
              if isFixedFunction vM func_xs then acc
              else
                  let add (y,acc) = Function_perturbation (func_xs,y) :: acc
                in
                  Mlist.foldl add acc target
        in
          pertTerms vM onTarget tms xs acc)

  and pertTerms vM onTarget =
        let vN = msize vM

        in let filterElements pred =
              let rec filt i acc = match i with
                  0 -> acc
                | _ ->
                    let i = i - 1
                    in let acc = if pred i then i :: acc else acc
                  in
                    filt i acc
            in
              filt vN []

        in let rec pert = function
            (_, [], [], acc) -> acc
          | (ys, (tm :: tms), (x :: xs), acc) ->
              let pred y =
                  y <> x && onTarget (Mlist.revAppend (ys, y :: xs))

              in let target = filterElements pred

              in let acc = pertTerm vM target tm acc
            in
              pert ((x :: ys), tms, xs, acc)
          | (_, _, _, _) -> raise (Bug "Model.pertTerms.pert")
      in
        fun x y z -> pert ([],x,y,z)
      ;;

  let pertAtom vM vV target (rel,tms) acc =
        let onTarget ys = interpretRelation vM (rel,ys) = target

        in let (tms,xs) = unzip (List.map (modelTerm vM vV) tms)

        in let rel_xs = (rel,xs)

        in let acc =
            if isFixedRelation vM rel_xs then acc
            else Relation_perturbation (rel_xs,target) :: acc
      in
        pertTerms vM onTarget tms xs acc
      ;;

  let pertLiteral vM vV ((pol,atm),acc) = pertAtom vM vV pol atm acc;;

  let pertClause vM vV cl acc = Literal.Set.foldl (pertLiteral vM vV) acc cl;;

  let pickPerturb vM perts =
      if Mlist.null perts then ()
      else perturb vM (Mlist.nth (perts, Portable.randomInt (length perts)));;

  let perturbTerm vM vV (tm,target) =
      pickPerturb vM (pertTerm vM target (fst (modelTerm vM vV tm)) []);;

  let perturbAtom vM vV (atm,target) =
      pickPerturb vM (pertAtom vM vV target atm []);;

  let perturbLiteral vM vV lit = pickPerturb vM (pertLiteral vM vV (lit,[]));;

  let perturbClause vM vV cl = pickPerturb vM (pertClause vM vV cl []);;


end


