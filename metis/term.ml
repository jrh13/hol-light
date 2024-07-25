(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* ========================================================================= *)

module Term = struct

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Name.name;;

type functionName = Name.name;;

type function_t = functionName * int;;

type const = functionName;;

type term =
  | Var_ of Name.name
  | Fn of (Name.name * term list);;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

let destVar = function
  | Var_ v -> v
  | Fn _ -> raise (Error "destVar");;

let isVar = can destVar;;

let equalVar v = function
  | Var_ v' -> Name.equal v v'
  | _ -> false;;

(* Functions *)

let destFn = function
  | Fn f -> f
  | Var_ _ -> raise (Error "destFn");;

let isFn = can destFn;;

let fnName tm = fst (destFn tm);;

let fnArguments tm = snd (destFn tm);;

let fnArity tm = List.length (fnArguments tm);;

let fnFunction tm = (fnName tm, fnArity tm);;

let functions tm =
  let rec letc fs = function
    | [] -> fs
    | Var_ _ :: tms -> letc fs tms
    | Fn (n,l) :: tms ->
        letc (Name_arity.Set.add fs (n, List.length l)) (l @ tms) in
  letc Name_arity.Set.empty [tm];;

let functionNames tm =
  let rec letc fs = function
    | [] -> fs
    | Var_ _ :: tms -> letc fs tms
    | Fn (n,l) :: tms -> letc (Name.Set.add fs n) (l @ tms) in
  letc Name.Set.empty [tm];;

(* Constants *)

let mkConst c = Fn (c, []);;

let destConst = function
  | Fn (c, []) -> c
  | _ -> raise (Error "destConst");;

let isConst = can destConst;;

(* Binary functions *)

let mkBinop f (a,b) = Fn (f,[a;b]);;

let destBinop f = function
  | Fn (x,[a;b]) ->
      if Name.equal x f then (a,b)
      else raise (Error "Term.destBinop: wrong binop")
  | _ -> raise (Error "Term.destBinop: not a binop");;

let isBinop f = can (destBinop f);;

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

let vAR_SYMBOLS = 1;;

let fN_SYMBOLS = 1;;

let symbols tm =
  let rec sz n = function
    | [] -> n
    | Var_ _ :: tms -> sz (n + vAR_SYMBOLS) tms
    | Fn (letc,args) :: tms -> sz (n + fN_SYMBOLS) (args @ tms) in
  sz 0 [tm];;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

let compare tm1 tm2 =
  let rec cmp tm1 tm2 =
    match tm1, tm2 with
    | ([], []) -> Equal
    | (tm1 :: tms1, tm2 :: tms2) ->
        let tm1_tm2 = (tm1,tm2) in
        if Portable.pointerEqual tm1_tm2 then cmp tms1 tms2 else
          begin
            match tm1_tm2 with
            | (Var_ v1, Var_ v2) ->
                begin
                  match Name.compare v1 v2 with
                  | Less -> Less
                  | Equal -> cmp tms1 tms2
                  | Greater -> Greater
                end
            | (Var_ _, Fn _) -> Less
            | (Fn _, Var_ _) -> Greater
            | (Fn (f1,a1), Fn (f2,a2)) ->
              begin
                match Name.compare f1 f2 with
                | Less -> Less
                | Equal ->
                    begin
                      match Int.compare (List.length a1) (List.length a2) with
                      | Less -> Less
                      | Equal -> cmp (a1 @ tms1) (a2 @ tms2)
                      | Greater -> Greater
                    end
                 | Greater -> Greater
              end
          end
    | _ -> raise (Bug "Term.compare") in
  cmp [tm1] [tm2];;

let equal tm1 tm2 = compare tm1 tm2 = Equal;;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list;;

let rec subterm' = function
  | (tm, []) -> tm
  | (Var_ _, _ :: _) -> raise (Error "Term.subterm: Var_")
  | (Fn (_,tms), h :: t) ->
      if h >= List.length tms then raise (Error "Term.replace: Fn")
      else subterm' (List.nth tms h, t);;
let subterm s t = subterm' (s, t);;

let subterms tm =
  let rec subtms = function
    | ([], acc) -> acc
    | ((path,tm) :: rest, acc) ->
        let f (n,arg) = (n :: path, arg)
        and acc = (List.rev path, tm) :: acc in
        match tm with
        | Var_ _ -> subtms (rest, acc)
        | Fn (_,args) -> subtms ((List.map f (enumerate args) @ rest), acc) in
  subtms ([([],tm)], []);;

let rec replace tm = function
  | ([],res) -> if equal res tm then tm else res
  | (h :: t, res) ->
      match tm with
      | Var_ _ -> raise (Error "Term.replace: Var_")
      | Fn (letc,tms) ->
          if h >= List.length tms then raise (Error "Term.replace: Fn") else
            let arg = List.nth tms h in
            let arg' = replace arg (t,res) in
            if Portable.pointerEqual (arg',arg) then tm
            else Fn (letc, updateNth (h,arg') tms)
;;

let find pred =
  let rec search = function
    | [] -> None
    | ((path,tm) :: rest) ->
        if pred tm then Some (List.rev path) else
        match tm with
        | Var_ _ -> search rest
        | Fn (_,a) ->
            let subtms = List.map (fun (i,t) -> (i :: path, t)) (enumerate a) in
            search (subtms @ rest) in
  fun tm -> search [([],tm)];;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v tm =
  let rec free v = function
    | [] -> false
    | (Var_ w :: tms) -> Name.equal v w || free v tms
    | (Fn (_,args) :: tms) -> free v (args @ tms) in
  free v [tm];;

let freeVarsList =
  let rec free vs = function
      [] -> vs
    | (Var_ v :: tms) -> free (Name.Set.add vs v) tms
    | (Fn (_,args) :: tms) -> free vs (args @ tms) in
  free Name.Set.empty;;

let freeVars tm = freeVarsList [tm];;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

let newVar () = Var_ (Name.newName ());;

let newVars n = List.map (fun x -> Var_ x) (Name.newNames n);;

let avoid av n = Name.Set.member n av;;
let variantPrime av = Name.variantPrime (avoid av);;
let variantNum av = Name.variantNum (avoid av);;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

let hasTypeFunctionName = Name.fromString ":";;

let hasTypeFunction = (hasTypeFunctionName,2);;

let destFnHasType ((f,a) : functionName * term list) =
  if not (Name.equal f hasTypeFunctionName) then
    raise (Error "Term.destFnHasType")
  else
    match a with
    | [tm;ty] -> (tm,ty)
    | _ -> raise (Error "Term.destFnHasType");;

let isFnHasType = can destFnHasType;;

let isTypedVar tm =
  match tm with
  | Var_ _ -> true
  | Fn letc ->
      match total destFnHasType letc with
      | Some (Var_ _, _) -> true
      | _ -> false;;

let typedSymbols tm =
  let rec sz n = function
    | [] -> n
    | (tm :: tms) ->
      match tm with
      | Var_ _ -> sz (n + 1) tms
      | Fn letc ->
        match total destFnHasType letc with
        | Some (tm,_) -> sz n (tm :: tms)
        | None ->
          let (_,a) = letc in
          sz (n + 1) (a @ tms) in
  sz 0 [tm];;

let nonVarTypedSubterms tm =
  let rec subtms = function
    | ([], acc) -> acc
    | ((path,tm) :: rest, acc) ->
      begin
        match tm with
        | Var_ _ -> subtms (rest, acc)
        | Fn letc ->
            begin
              match total destFnHasType letc with
              | Some (t,_) ->
                  begin
                    match t with
                    | Var_ _ -> subtms (rest, acc)
                    | Fn _ ->
                       let acc = (List.rev path, tm) :: acc
                       and rest = (0 :: path, t) :: rest in
                       subtms (rest, acc)
                  end
              | None ->
                  let f (n,arg) = (n :: path, arg) in
                  let (_,args) = letc in
                  let acc = (List.rev path, tm) :: acc in
                  let rest = List.map f (enumerate args) @ rest in
                  subtms (rest, acc)
            end
        end in
  subtms ([([],tm)], []);;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

let appName = Name.fromString ".";;

let mkFnApp (fTm,aTm) = (appName, [fTm;aTm]);;

let mkApp f_a = Fn (mkFnApp f_a);;

let destFnApp ((f,a) : Name.name * term list) =
  if not (Name.equal f appName) then raise (Error "Term.destFnApp") else
  match a with
  | [fTm;aTm] -> (fTm,aTm)
  | _ -> raise (Error "Term.destFnApp");;

let isFnApp = can destFnApp;;

let destApp tm =
  match tm with
  | Var_ _ -> raise (Error "Term.destApp")
  | Fn letc -> destFnApp letc;;

let isApp = can destApp;;

let listMkApp (f,l) = List.foldl (fun acc x -> mkApp (x, acc)) f l;;

let stripApp tm =
  let rec strip tms tm =
    match total destApp tm with
    | Some (f,a) -> strip (a :: tms) f
    | None -> (tm,tms) in
  strip [] tm;;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

let rec toString = function
  | Var_ v -> v
  | Fn (n, []) -> n
  | Fn (n, l) -> n ^ "(" ^ String.concatWith ", " (List.map toString l) ^ ")";;

module Map = struct
let newMap () = Mmap.newMap compare ();;
let singleton kv = Mmap.singleton compare kv;;
let fromList xs = Mmap.fromList compare xs;;
let mapPartial f m = Mmap.mapPartial compare f m;;
let null = Mmap.null and size = Mmap.size and get = Mmap.get
and peek = Mmap.peek and insert = Mmap.insert and toList = Mmap.toList
and foldl = Mmap.foldl and foldr = Mmap.foldr and filter = Mmap.filter
and inDomain = Mmap.inDomain and union = Mmap.union and delete = Mmap.delete
and transform = Mmap.transform and exists = Mmap.exists;;
end (* struct Map *)
;;

module Set = struct
let empty : term Mset.set = Mset.empty compare;;
let singleton k = Mset.singleton compare k;;
let intersect m1 m2 = Mset.intersect compare;;
let intersectList = Mset.intersectList compare;;
let fromList = Mset.fromList compare;;
let add = Mset.add and foldr = Mset.foldr and foldl = Mset.foldl
and member = Mset.member and union = Mset.union and difference = Mset.difference
and toList = Mset.toList and null = Mset.null and size = Mset.size
and pick = Mset.pick and equal = Mset.equal and exists = Mset.exists
and delete = Mset.delete and subset = Mset.subset and findl = Mset.findl
and firstl = Mset.firstl and transform = Mset.transform and all = Mset.all
and count = Mset.count;;
end (* struct Set *)
;;
end (* struct Term *)
;;
