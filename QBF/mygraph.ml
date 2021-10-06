unset_jrh_lexer;;

module Intvertex = struct
  type t = int
  let compare : t -> t -> int = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = 0
end;;

module Gr = Graph.Imperative.Digraph.ConcreteBidirectional(Intvertex);;

module Topo = Graph.Topological.Make(Gr);;

let make_vertex var_index = Gr.V.create var_index;;
let dest_vertex var_index = Gr.V.label var_index;;

set_jrh_lexer;;
