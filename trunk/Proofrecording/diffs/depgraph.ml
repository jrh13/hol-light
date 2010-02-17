module Label = struct

  type t = string

  let compare = String.compare

  let hash s =
    let n = String.length s in
    let p = 9 in
    if n >= p then
      try
        int_of_string (String.sub s p (n-p))
      with | Failure _ -> n
    else
      n

  let equal a b = a = b

end


module Dep = struct

  include Graph.Imperative.Digraph.ConcreteBidirectional(Label)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = V.label v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes _ = []

  let add_thm dep thm = add_vertex dep (V.create thm)

  let add_dep dep thm1 thm2 =
    let v1 = V.create thm1 in
    let v2 = V.create thm2 in
    if ((mem_vertex dep v1) && (mem_vertex dep v2)) then
      add_edge dep v1 v2

  let min_max_moy_in_deg dep =
    let max = ref 0 in
    let lab_max = ref "" in
    let min = ref 1073741823 in
    let lab_min = ref "" in
    let nb = ref 0 in
    let sum = ref 0 in
    let calc v =
      let deg = in_degree dep v in
      if deg < !min then (
        min := deg;
        lab_min := V.label v
      );
      if deg > !max then (
        max := deg;
        lab_max := V.label v
      );
      incr nb;
      sum := !sum + deg in
    iter_vertex calc dep;
    let moy = (float_of_int !sum) /. (float_of_int !nb) in
    (!min, !lab_min, !max, !lab_max, moy)

  let min_max_moy_out_deg dep =
    let max = ref 0 in
    let lab_max = ref "" in
    let min = ref 1073741823 in
    let lab_min = ref "" in
    let nb = ref 0 in
    let sum = ref 0 in
    let calc v =
      let deg = out_degree dep v in
      if deg < !min then (
        min := deg;
        lab_min := V.label v
      );
      if deg > !max then (
        max := deg;
        lab_max := V.label v
      );
      incr nb;
      sum := !sum + deg in
    iter_vertex calc dep;
    let moy = (float_of_int !sum) /. (float_of_int !nb) in
    (!min, !lab_min, !max, !lab_max, moy)

end


module Dep_top = struct

  include Graph.Topological.Make(Dep)

  let iter_top f dep = iter (fun v -> f (Dep.V.label v)) dep

end


module Dep_dot = struct

  include Graph.Graphviz.Dot(Dep)

  let output_dot name dep =
    let file = open_out name in
    output_graph file dep;
    close_out file

end
