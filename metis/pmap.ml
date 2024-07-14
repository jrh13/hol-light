(* ========================================================================= *)
(* FINITE MAPS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* ========================================================================= *)

module Pmap = struct

(* ------------------------------------------------------------------------- *)
(* Importing useful functionality.                                           *)
(* ------------------------------------------------------------------------- *)

exception Bug = Useful.Bug;;

exception Error = Useful.Error;;

let pointerEqual = Portable.pointerEqual;;

let kComb = Useful.kComb;;

let randomInt = Portable.randomInt;;

let randomWord = Portable.randomWord;;

(* ------------------------------------------------------------------------- *)
(* Converting a comparison function to an equality function.                 *)
(* ------------------------------------------------------------------------- *)

let equalKey compareKey key1 key2 = compareKey (key1,key2) = Equal;;

(* ------------------------------------------------------------------------- *)
(* Priorities.                                                               *)
(* ------------------------------------------------------------------------- *)

type priority = Word.word;;

let randomPriority = randomWord;;

let comparePriority = Word.compare;;

(* ------------------------------------------------------------------------- *)
(* Priority search trees.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('key,'value) tree =
    Empty
  | Tree of ('key,'value) node

and ('key,'value) node =
      {size : int;
       priority : priority;
       left : ('key,'value) tree;
       key : 'key;
       value : 'value;
       right : ('key,'value) tree};;

let lowerPriorityNode node1 node2 =
      let {priority = p1} = node1
      and {priority = p2} = node2
    in
      comparePriority (p1,p2) = Less
    ;;

(* ------------------------------------------------------------------------- *)
(* Tree operations.                                                          *)
(* ------------------------------------------------------------------------- *)

let treeNew () = Empty;;

let nodeSize ({size = x}) = x;;

let treeSize tree =
    match tree with
      Empty -> 0
    | Tree x -> nodeSize x;;

let mkNode priority left key value right =
      let size = treeSize left + 1 + treeSize right
    in
        {size = size;
         priority = priority;
         left = left;
         key = key;
         value = value;
         right = right}
    ;;

let mkTree priority left key value right =
      let node = mkNode priority left key value right
    in
      Tree node
    ;;

(* ------------------------------------------------------------------------- *)
(* Extracting the left and right spines of a tree.                           *)
(* ------------------------------------------------------------------------- *)

let rec treeLeftSpine acc tree =
    match tree with
      Empty -> acc
    | Tree node -> nodeLeftSpine acc node

and nodeLeftSpine acc node =
      let {left=left} = node
    in
      treeLeftSpine (node :: acc) left
    ;;

let rec treeRightSpine acc tree =
    match tree with
      Empty -> acc
    | Tree node -> nodeRightSpine acc node

and nodeRightSpine acc node =
      let {right=right} = node
    in
      treeRightSpine (node :: acc) right
    ;;

(* ------------------------------------------------------------------------- *)
(* Singleton trees.                                                          *)
(* ------------------------------------------------------------------------- *)

let mkNodeSingleton priority key value =
      let size = 1
      and left = Empty
      and right = Empty
    in
        {size = size;
         priority = priority;
         left = left;
         key = key;
         value = value;
         right = right}
    ;;

let nodeSingleton (key,value) =
      let priority = randomPriority ()
    in
      mkNodeSingleton priority key value
    ;;

let treeSingleton key_value =
      let node = nodeSingleton key_value
    in
      Tree node
    ;;

(* ------------------------------------------------------------------------- *)
(* Appending two trees, where every element of the first tree is less than   *)
(* every element of the second tree.                                         *)
(* ------------------------------------------------------------------------- *)

let rec treeAppend tree1 tree2 =
    match tree1 with
      Empty -> tree2
    | Tree node1 ->
      match tree2 with
        Empty -> tree1
      | Tree node2 ->
        if lowerPriorityNode node1 node2 then
            let {priority=priority;left=left;key=key;value=value;right=right} = node2

            in let left = treeAppend tree1 left
          in
            mkTree priority left key value right
        else
            let {priority=priority;left=left;key=key;value=value;right=right} = node1

            in let right = treeAppend right tree2
          in
            mkTree priority left key value right
          ;;

(* ------------------------------------------------------------------------- *)
(* Appending two trees and a node, where every element of the first tree is  *)
(* less than the node, which in turn is less than every element of the       *)
(* second tree.                                                              *)
(* ------------------------------------------------------------------------- *)

let treeCombine left node right =
      let left_node = treeAppend left (Tree node)
    in
      treeAppend left_node right
    ;;

(* ------------------------------------------------------------------------- *)
(* Searching a tree for a value.                                             *)
(* ------------------------------------------------------------------------- *)

let rec treePeek compareKey pkey tree =
    match tree with
      Empty -> None
    | Tree node -> nodePeek compareKey pkey node

and nodePeek compareKey pkey node =
      let {left=left;key=key;value=value;right=right} = node
    in
      match compareKey (pkey,key) with
        Less -> treePeek compareKey pkey left
      | Equal -> Some value
      | Greater -> treePeek compareKey pkey right
    ;;

(* ------------------------------------------------------------------------- *)
(* Tree paths.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Generating a path by searching a tree for a key/value pair *)

let rec treePeekPath compareKey pkey path tree =
    match tree with
      Empty -> (path,None)
    | Tree node -> nodePeekPath compareKey pkey path node

and nodePeekPath compareKey pkey path node =
      let {left=left;key=key;right=right} = node
    in
      match compareKey (pkey,key) with
        Less -> treePeekPath compareKey pkey ((true,node) :: path) left
      | Equal -> (path, Some node)
      | Greater -> treePeekPath compareKey pkey ((false,node) :: path) right
    ;;

(* A path splits a tree into left/right components *)

let addSidePath ((wentLeft,node),(leftTree,rightTree)) =
      let {priority=priority;left=left;key=key;value=value;right=right} = node
    in
      if wentLeft then (leftTree, mkTree priority rightTree key value right)
      else (mkTree priority left key value leftTree, rightTree)
    ;;

let addSidesPath left_right = Mlist.foldl addSidePath left_right;;

let mkSidesPath path = addSidesPath (Empty,Empty) path;;

(* Updating the subtree at a path *)

  let updateTree ((wentLeft,node),tree) =
        let {priority=priority;left=left;key=key;value=value;right=right} = node
      in
        if wentLeft then mkTree priority tree key value right
        else mkTree priority left key value tree;;
  let updateTreePath tree = Mlist.foldl updateTree tree;;

(* Inserting a new node at a path position *)

let insertNodePath node =
      let rec insert left_right path =
          match path with
            [] ->
              let (left,right) = left_right
            in
              treeCombine left node right
          | ((_,snode) as step) :: rest ->
            if lowerPriorityNode snode node then
                let left_right = addSidePath (step,left_right)
              in
                insert left_right rest
            else
                let (left,right) = left_right

                in let tree = treeCombine left node right
              in
                updateTreePath tree path
    in
      insert (Empty,Empty)
    ;;

(* ------------------------------------------------------------------------- *)
(* Using a key to split a node into three components: the keys comparing     *)
(* less than the supplied key, an optional equal key, and the keys comparing *)
(* greater.                                                                  *)
(* ------------------------------------------------------------------------- *)

let nodePartition compareKey pkey node =
      let (path,pnode) = nodePeekPath compareKey pkey [] node
    in
      match pnode with
        None ->
          let (left,right) = mkSidesPath path
        in
          (left,None,right)
      | Some node ->
          let {left=left;key=key;value=value;right=right} = node

          in let (left,right) = addSidesPath (left,right) path
        in
          (left, Some (key,value), right)
    ;;

(* ------------------------------------------------------------------------- *)
(* Searching a tree for a key/value pair.                                    *)
(* ------------------------------------------------------------------------- *)

let rec treePeekKey compareKey pkey tree =
    match tree with
      Empty -> None
    | Tree node -> nodePeekKey compareKey pkey node

and nodePeekKey compareKey pkey node =
      let {left=left;key=key;value=value;right=right} = node
    in
      match compareKey (pkey,key) with
        Less -> treePeekKey compareKey pkey left
      | Equal -> Some (key,value)
      | Greater -> treePeekKey compareKey pkey right
    ;;

(* ------------------------------------------------------------------------- *)
(* Inserting new key/values into the tree.                                   *)
(* ------------------------------------------------------------------------- *)

let treeInsert compareKey key_value tree =
      let (key,value) = key_value

      in let (path,inode) = treePeekPath compareKey key [] tree
    in
      match inode with
        None ->
          let node = nodeSingleton (key,value)
        in
          insertNodePath node path
      | Some node ->
          let {size=size;priority=priority;left=left;right=right} = node

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          updateTreePath (Tree node) path
    ;;

(* ------------------------------------------------------------------------- *)
(* Deleting key/value pairs: it raises an exception if the supplied key is   *)
(* not present.                                                              *)
(* ------------------------------------------------------------------------- *)

let rec treeDelete compareKey dkey tree =
    match tree with
      Empty -> raise (Bug "Map.delete: element not found")
    | Tree node -> nodeDelete compareKey dkey node

and nodeDelete compareKey dkey node =
      let {size=size;priority=priority;left=left;key=key;value=value;right=right} = node
    in
      match compareKey (dkey,key) with
        Less ->
          let size = size - 1
          and left = treeDelete compareKey dkey left

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          Tree node
      | Equal -> treeAppend left right
      | Greater ->
          let size = size - 1
          and right = treeDelete compareKey dkey right

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          Tree node
    ;;

(* ------------------------------------------------------------------------- *)
(* Partial map is the basic operation for preserving tree structure.         *)
(* It applies its argument function to the elements *in order*.              *)
(* ------------------------------------------------------------------------- *)

let rec treeMapPartial f tree =
    match tree with
      Empty -> Empty
    | Tree node -> nodeMapPartial f node

and nodeMapPartial f ({priority=priority;left=left;key=key;value=value;right=right}) =
      let left = treeMapPartial f left
      and vo = f (key,value)
      and right = treeMapPartial f right
    in
      match vo with
        None -> treeAppend left right
      | Some value -> mkTree priority left key value right
    ;;

(* ------------------------------------------------------------------------- *)
(* Mapping tree values.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec treeMap f tree =
    match tree with
      Empty -> Empty
    | Tree node -> Tree (nodeMap f node)

and nodeMap f node =
      let {size=size;priority=priority;left=left;key=key;value=value;right=right} = node

      in let left = treeMap f left
      and value = f (key,value)
      and right = treeMap f right
    in
        {size = size;
         priority = priority;
         left = left;
         key = key;
         value = value;
         right = right}
    ;;

(* ------------------------------------------------------------------------- *)
(* Merge is the basic operation for joining two trees. Note that the merged  *)
(* key is always the one from the second map.                                *)
(* ------------------------------------------------------------------------- *)

let rec treeMerge compareKey f1 f2 fb tree1 tree2 =
    match tree1 with
      Empty -> treeMapPartial f2 tree2
    | Tree node1 ->
      match tree2 with
        Empty -> treeMapPartial f1 tree1
      | Tree node2 -> nodeMerge compareKey f1 f2 fb node1 node2

and nodeMerge compareKey f1 f2 fb node1 node2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = node2

      in let (l,kvo,r) = nodePartition compareKey key node1

      in let left = treeMerge compareKey f1 f2 fb l left
      and right = treeMerge compareKey f1 f2 fb r right

      in let vo =
          match kvo with
            None -> f2 (key,value)
          | Some kv -> fb (kv,(key,value))
    in
      match vo with
        None -> treeAppend left right
      | Some value ->
          let node = mkNodeSingleton priority key value
        in
          treeCombine left node right
    ;;

(* ------------------------------------------------------------------------- *)
(* A union operation on trees.                                               *)
(* ------------------------------------------------------------------------- *)

let rec treeUnion compareKey f f2 tree1 tree2 =
    match tree1 with
      Empty -> tree2
    | Tree node1 ->
      match tree2 with
        Empty -> tree1
      | Tree node2 -> nodeUnion compareKey f f2 node1 node2

and nodeUnion compareKey f f2 node1 node2 =
    if pointerEqual (node1,node2) then nodeMapPartial f2 node1
    else
        let {priority=priority;left=left;key=key;value=value;right=right} = node2

        in let (l,kvo,r) = nodePartition compareKey key node1

        in let left = treeUnion compareKey f f2 l left
        and right = treeUnion compareKey f f2 r right

        in let vo =
            match kvo with
              None -> Some value
            | Some kv -> f (kv,(key,value))
      in
        match vo with
          None -> treeAppend left right
        | Some value ->
            let node = mkNodeSingleton priority key value
          in
            treeCombine left node right
      ;;

(* ------------------------------------------------------------------------- *)
(* An intersect operation on trees.                                          *)
(* ------------------------------------------------------------------------- *)

let rec treeIntersect compareKey f t1 t2 =
    match t1 with
      Empty -> Empty
    | Tree n1 ->
      match t2 with
        Empty -> Empty
      | Tree n2 -> nodeIntersect compareKey f n1 n2

and nodeIntersect compareKey f n1 n2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = n2

      in let (l,kvo,r) = nodePartition compareKey key n1

      in let left = treeIntersect compareKey f l left
      and right = treeIntersect compareKey f r right

      in let vo =
          match kvo with
            None -> None
          | Some kv -> f (kv,(key,value))
    in
      match vo with
        None -> treeAppend left right
      | Some value -> mkTree priority left key value right
    ;;

(* ------------------------------------------------------------------------- *)
(* A union operation on trees which simply chooses the second value.         *)
(* ------------------------------------------------------------------------- *)

let rec treeUnionDomain compareKey tree1 tree2 =
    match tree1 with
      Empty -> tree2
    | Tree node1 ->
      match tree2 with
        Empty -> tree1
      | Tree node2 ->
        if pointerEqual (node1,node2) then tree2
        else nodeUnionDomain compareKey node1 node2

and nodeUnionDomain compareKey node1 node2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = node2

      in let (l,_,r) = nodePartition compareKey key node1

      in let left = treeUnionDomain compareKey l left
      and right = treeUnionDomain compareKey r right

      in let node = mkNodeSingleton priority key value
    in
      treeCombine left node right
    ;;

(* ------------------------------------------------------------------------- *)
(* An intersect operation on trees which simply chooses the second value.    *)
(* ------------------------------------------------------------------------- *)

let rec treeIntersectDomain compareKey tree1 tree2 =
    match tree1 with
      Empty -> Empty
    | Tree node1 ->
      match tree2 with
        Empty -> Empty
      | Tree node2 ->
        if pointerEqual (node1,node2) then tree2
        else nodeIntersectDomain compareKey node1 node2

and nodeIntersectDomain compareKey node1 node2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = node2

      in let (l,kvo,r) = nodePartition compareKey key node1

      in let left = treeIntersectDomain compareKey l left
      and right = treeIntersectDomain compareKey r right
    in
      if Option.isSome kvo then mkTree priority left key value right
      else treeAppend left right
    ;;

(* ------------------------------------------------------------------------- *)
(* A difference operation on trees.                                          *)
(* ------------------------------------------------------------------------- *)

let rec treeDifferenceDomain compareKey t1 t2 =
    match t1 with
      Empty -> Empty
    | Tree n1 ->
      match t2 with
        Empty -> t1
      | Tree n2 -> nodeDifferenceDomain compareKey n1 n2

and nodeDifferenceDomain compareKey n1 n2 =
    if pointerEqual (n1,n2) then Empty
    else
        let {priority=priority;left=left;key=key;value=value;right=right} = n1

        in let (l,kvo,r) = nodePartition compareKey key n2

        in let left = treeDifferenceDomain compareKey left l
        and right = treeDifferenceDomain compareKey right r
      in
        if Option.isSome kvo then treeAppend left right
        else mkTree priority left key value right
      ;;

(* ------------------------------------------------------------------------- *)
(* A subset operation on trees.                                              *)
(* ------------------------------------------------------------------------- *)

let rec treeSubsetDomain compareKey tree1 tree2 =
    match tree1 with
      Empty -> true
    | Tree node1 ->
      match tree2 with
        Empty -> false
      | Tree node2 -> nodeSubsetDomain compareKey node1 node2

and nodeSubsetDomain compareKey node1 node2 =
    pointerEqual (node1,node2) ||
      let {size=size;left=left;key=key;right=right} = node1
    in
      size <= nodeSize node2 &&
        let (l,kvo,r) = nodePartition compareKey key node2
      in
        Option.isSome kvo &&
        treeSubsetDomain compareKey left l &&
        treeSubsetDomain compareKey right r
    ;;

(* ------------------------------------------------------------------------- *)
(* Picking an arbitrary key/value pair from a tree.                          *)
(* ------------------------------------------------------------------------- *)

let rec nodePick node =
      let {key=key;value=value} = node
    in
      (key,value)
    ;;

let treePick tree =
    match tree with
      Empty -> raise (Bug "Map.treePick")
    | Tree node -> nodePick node;;

(* ------------------------------------------------------------------------- *)
(* Removing an arbitrary key/value pair from a tree.                         *)
(* ------------------------------------------------------------------------- *)

let rec nodeDeletePick node =
      let {left=left;key=key;value=value;right=right} = node
    in
      ((key,value), treeAppend left right)
    ;;

let treeDeletePick tree =
    match tree with
      Empty -> raise (Bug "Map.treeDeletePick")
    | Tree node -> nodeDeletePick node;;

(* ------------------------------------------------------------------------- *)
(* Finding the nth smallest key/value (counting from 0).                     *)
(* ------------------------------------------------------------------------- *)

let rec treeNth n tree =
    match tree with
      Empty -> raise (Bug "Map.treeNth")
    | Tree node -> nodeNth n node

and nodeNth n node =
      let {left=left;key=key;value=value;right=right} = node

      in let k = treeSize left
    in
      if n = k then (key,value)
      else if n < k then treeNth n left
      else treeNth (n - (k + 1)) right
    ;;

(* ------------------------------------------------------------------------- *)
(* Removing the nth smallest key/value (counting from 0).                    *)
(* ------------------------------------------------------------------------- *)

let rec treeDeleteNth n tree =
    match tree with
      Empty -> raise (Bug "Map.treeDeleteNth")
    | Tree node -> nodeDeleteNth n node

and nodeDeleteNth n node =
      let {size=size;priority=priority;left=left;key=key;value=value;right=right} = node

      in let k = treeSize left
    in
      if n = k then ((key,value), treeAppend left right)
      else if n < k then
          let (key_value,left) = treeDeleteNth n left

          in let size = size - 1

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          (key_value, Tree node)
      else
          let n = n - (k + 1)

          in let (key_value,right) = treeDeleteNth n right

          in let size = size - 1

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          (key_value, Tree node)
    ;;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

type ('key,'value) iterator =
    Left_to_right_iterator of
      ('key * 'value) * ('key,'value) tree * ('key,'value) node list
  | Right_to_left_iterator of
      ('key * 'value) * ('key,'value) tree * ('key,'value) node list;;

let fromSpineLeftToRightIterator nodes =
    match nodes with
      [] -> None
    | {key=key;value=value;right=right} :: nodes ->
      Some (Left_to_right_iterator ((key,value),right,nodes));;

let fromSpineRightToLeftIterator nodes =
    match nodes with
      [] -> None
    | {key=key;value=value;left=left} :: nodes ->
      Some (Right_to_left_iterator ((key,value),left,nodes));;

let addLeftToRightIterator nodes tree = fromSpineLeftToRightIterator (treeLeftSpine nodes tree);;

let addRightToLeftIterator nodes tree = fromSpineRightToLeftIterator (treeRightSpine nodes tree);;

let treeMkIterator tree = addLeftToRightIterator [] tree;;

let treeMkRevIterator tree = addRightToLeftIterator [] tree;;

let readIterator iter =
    match iter with
      Left_to_right_iterator (key_value,_,_) -> key_value
    | Right_to_left_iterator (key_value,_,_) -> key_value;;

let advanceIterator iter =
    match iter with
      Left_to_right_iterator (_,tree,nodes) -> addLeftToRightIterator nodes tree
    | Right_to_left_iterator (_,tree,nodes) -> addRightToLeftIterator nodes tree;;

let rec foldIterator f acc io =
    match io with
      None -> acc
    | Some iter ->
        let (key,value) = readIterator iter
      in
        foldIterator f (f (key,value,acc)) (advanceIterator iter)
      ;;

let rec findIterator pred io =
    match io with
      None -> None
    | Some iter ->
        let key_value = readIterator iter
      in
        if pred key_value then Some key_value
        else findIterator pred (advanceIterator iter)
      ;;

let rec firstIterator f io =
    match io with
      None -> None
    | Some iter ->
        let key_value = readIterator iter
      in
        match f key_value with
          None -> firstIterator f (advanceIterator iter)
        | s -> s
      ;;

let rec compareIterator compareKey compareValue io1 io2 =
    match (io1,io2) with
      (None,None) -> Equal
    | (None, Some _) -> Less
    | (Some _, None) -> Greater
    | (Some i1, Some i2) ->
        let (k1,v1) = readIterator i1
        and (k2,v2) = readIterator i2
      in
        match compareKey (k1,k2) with
          Less -> Less
        | Equal ->
          (match compareValue (v1,v2) with
             Less -> Less
           | Equal ->
               let io1 = advanceIterator i1
               and io2 = advanceIterator i2
             in
               compareIterator compareKey compareValue io1 io2
           | Greater -> Greater)
        | Greater -> Greater
      ;;

let rec equalIterator equalKey equalValue io1 io2 =
    match (io1,io2) with
      (None,None) -> true
    | (None, Some _) -> false
    | (Some _, None) -> false
    | (Some i1, Some i2) ->
        let (k1,v1) = readIterator i1
        and (k2,v2) = readIterator i2
      in
        equalKey k1 k2 &&
        equalValue v1 v2 &&
          let io1 = advanceIterator i1
          and io2 = advanceIterator i2
        in
          equalIterator equalKey equalValue io1 io2
      ;;

(* ------------------------------------------------------------------------- *)
(* A type of finite maps.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('key,'value) map =
    Map of ('key * 'key -> order) * ('key,'value) tree;;

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

let newMap compareKey =
      let tree = treeNew ()
    in
      Map (compareKey,tree)
    ;;

let singleton compareKey key_value =
      let tree = treeSingleton key_value
    in
      Map (compareKey,tree)
    ;;

(* ------------------------------------------------------------------------- *)
(* Map size.                                                                 *)
(* ------------------------------------------------------------------------- *)

let size (Map (_,tree)) = treeSize tree;;

let null m = size m = 0;;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

let peekKey (Map (compareKey,tree)) key = treePeekKey compareKey key tree;;

let peek (Map (compareKey,tree)) key = treePeek compareKey key tree;;

let inDomain key m = Option.isSome (peek m key);;

let get m key =
    match peek m key with
      None -> raise (Error "Map.get: element not found")
    | Some value -> value;;

let pick (Map (_,tree)) = treePick tree;;

let nth (Map (_,tree)) n = treeNth n tree;;

let random m =
      let n = size m
    in
      if n = 0 then raise (Bug "Map.random: empty")
      else nth m (randomInt n)
    ;;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

let insert (Map (compareKey,tree)) key_value =
      let tree = treeInsert compareKey key_value tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let insert = fun m -> fun kv ->
    checkInvariants "Map.insert: result"
      (insert (checkInvariants "Map.insert: input" m) kv);;
*)

let insertList m =
      let ins (key_value,acc) = insert acc key_value
    in
      Mlist.foldl ins m
    ;;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

let delete (Map (compareKey,tree)) dkey =
      let tree = treeDelete compareKey dkey tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let delete = fun m -> fun k ->
    checkInvariants "Map.delete: result"
      (delete (checkInvariants "Map.delete: input" m) k);;
*)

let remove m key = if inDomain key m then delete m key else m;;

let deletePick (Map (compareKey,tree)) =
      let (key_value,tree) = treeDeletePick tree
    in
      (key_value, Map (compareKey,tree))
    ;;

(*BasicDebug
let deletePick = fun m ->
    let
      let (kv,m) = deletePick (checkInvariants "Map.deletePick: input" m)
    in
      (kv, checkInvariants "Map.deletePick: result" m)
    end;;
*)

let deleteNth (Map (compareKey,tree)) n =
      let (key_value,tree) = treeDeleteNth n tree
    in
      (key_value, Map (compareKey,tree))
    ;;

(*BasicDebug
let deleteNth = fun m -> fun n ->
    let
      let (kv,m) = deleteNth (checkInvariants "Map.deleteNth: input" m) n
    in
      (kv, checkInvariants "Map.deleteNth: result" m)
    end;;
*)

let deleteRandom m =
      let n = size m
    in
      if n = 0 then raise (Bug "Map.deleteRandom: empty")
      else deleteNth m (randomInt n)
    ;;

(* ------------------------------------------------------------------------- *)
(* Joining (all join operations prefer keys in the second map).              *)
(* ------------------------------------------------------------------------- *)

let merge (first,second,both) (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeMerge compareKey first second both tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let merge = fun f -> fun m1 -> fun m2 ->
    checkInvariants "Map.merge: result"
      (merge f
         (checkInvariants "Map.merge: input 1" m1)
         (checkInvariants "Map.merge: input 2" m2));;
*)

let union f (Map (compareKey,tree1)) (Map (_,tree2)) =
      let f2 kv = f (kv,kv)

      in let tree = treeUnion compareKey f f2 tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let union = fun f -> fun m1 -> fun m2 ->
    checkInvariants "Map.union: result"
      (union f
         (checkInvariants "Map.union: input 1" m1)
         (checkInvariants "Map.union: input 2" m2));;
*)

let intersect f (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeIntersect compareKey f tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let intersect = fun f -> fun m1 -> fun m2 ->
    checkInvariants "Map.intersect: result"
      (intersect f
         (checkInvariants "Map.intersect: input 1" m1)
         (checkInvariants "Map.intersect: input 2" m2));;
*)

(* ------------------------------------------------------------------------- *)
(* Iterators over maps.                                                      *)
(* ------------------------------------------------------------------------- *)

let mkIterator (Map (_,tree)) = treeMkIterator tree;;

let mkRevIterator (Map (_,tree)) = treeMkRevIterator tree;;

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

let mapPartial f (Map (compareKey,tree)) =
      let tree = treeMapPartial f tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let mapPartial = fun f -> fun m ->
    checkInvariants "Map.mapPartial: result"
      (mapPartial f (checkInvariants "Map.mapPartial: input" m));;
*)

let map f (Map (compareKey,tree)) =
      let tree = treeMap f tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let map = fun f -> fun m ->
    checkInvariants "Map.map: result"
      (map f (checkInvariants "Map.map: input" m));;
*)

let transform f = map (fun (_,value) -> f value);;

let filter pred =
      let f ((_,value) as key_value) =
          if pred key_value then Some value else None
    in
      mapPartial f
    ;;

let partition p =
      let np x = not (p x)
    in
      fun m -> (filter p m, filter np m)
    ;;

let foldl f b m = foldIterator f b (mkIterator m);;

let foldr f b m = foldIterator f b (mkRevIterator m);;

let app f m = foldl (fun (key,value,()) -> f (key,value)) () m;;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

let findl p m = findIterator p (mkIterator m);;

let findr p m = findIterator p (mkRevIterator m);;

let firstl f m = firstIterator f (mkIterator m);;

let firstr f m = firstIterator f (mkRevIterator m);;

let exists p m = Option.isSome (findl p m);;

let all p =
      let np x = not (p x)
    in
      fun m -> not (exists np m)
    ;;

let count pred =
      let f (k,v,acc) = if pred (k,v) then acc + 1 else acc
    in
      foldl f 0
    ;;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

let compare compareValue (m1,m2) =
    if pointerEqual (m1,m2) then Equal
    else
      match Int.compare (size m1, size m2) with
        Less -> Less
      | Equal ->
          let Map (compareKey,_) = m1

          in let io1 = mkIterator m1
          and io2 = mkIterator m2
        in
          compareIterator compareKey compareValue io1 io2
      | Greater -> Greater;;

let equal equalValue m1 m2 =
    pointerEqual (m1,m2) ||
    (size m1 = size m2 &&
       let Map (compareKey,_) = m1

       in let io1 = mkIterator m1
       and io2 = mkIterator m2
     in
       equalIterator (equalKey compareKey) equalValue io1 io2
     );;

(* ------------------------------------------------------------------------- *)
(* Set operations on the domain.                                             *)
(* ------------------------------------------------------------------------- *)

let unionDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeUnionDomain compareKey tree1 tree2
    in
      Map (compareKey,tree)
    ;;

let uncurriedUnionDomain (m,acc) = unionDomain acc m;;
let unionListDomain ms =
  match ms with
    [] -> raise (Bug "Map.unionListDomain: no sets")
  | m :: ms -> Mlist.foldl uncurriedUnionDomain m ms;;

let intersectDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeIntersectDomain compareKey tree1 tree2
    in
      Map (compareKey,tree)
    ;;

let uncurriedIntersectDomain (m,acc) = intersectDomain acc m;;
let intersectListDomain ms =
  match ms with
    [] -> raise (Bug "Map.intersectListDomain: no sets")
  | m :: ms -> Mlist.foldl uncurriedIntersectDomain m ms;;

let differenceDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeDifferenceDomain compareKey tree1 tree2
    in
      Map (compareKey,tree)
    ;;

let symmetricDifferenceDomain m1 m2 =
    unionDomain (differenceDomain m1 m2) (differenceDomain m2 m1);;

let equalDomain m1 m2 = equal (kComb (kComb true)) m1 m2;;

let subsetDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
    treeSubsetDomain compareKey tree1 tree2;;

let disjointDomain m1 m2 = null (intersectDomain m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

let keys m = foldr (fun (key,_,l) -> key :: l) [] m;;

let values m = foldr (fun (_,value,l) -> value :: l) [] m;;

let toList m = foldr (fun (key,value,l) -> (key,value) :: l) [] m;;

let fromList compareKey l =
      let m = newMap compareKey
    in
      insertList m l
    ;;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString m = "<" ^ (if null m then "" else Int.toString (size m)) ^ ">";;

end

