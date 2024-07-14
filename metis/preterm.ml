module Preterm = struct

let mk_negp pt = Combp (preterm_of_term `~`, pt)
let mk_eqp (ps, pt) = Combp (Combp (Constp ("=", dpty), ps), pt)
let mk_conjp (ps, pt) = Combp (Combp (preterm_of_term `/\`, ps), pt)
let mk_disjp (ps, pt) = Combp (Combp (preterm_of_term `\/`, ps), pt)

let list_mk_combp (h, t) = rev_itlist (fun x acc -> Combp (acc, x)) t h

assert
  (
    list_mk_combp (Varp ("1", dpty), [Varp ("2", dpty); Varp ("3", dpty)])
  =
    Combp (Combp (Varp ("1", Ptycon ("", [])), Varp ("2", Ptycon ("", []))),
      Varp ("3", Ptycon ("", [])))
  );;

let list_mk_disjp = function
    [] -> preterm_of_term `F`
  | h::t -> itlist (curry mk_disjp) t h

(* typechecking a preterm with constants fails,
   therefore we convert constants to variables before type checking
   type checking converts the variables back to the corresponding constants
*)
let rec unconst_preterm = function
    Varp (s, pty) -> Varp (s, pty)
  | Constp (s, pty) -> Varp (s, pty)
  | Combp (l, r) -> Combp (unconst_preterm l, unconst_preterm r)
  | Typing (ptm, pty) -> Typing (unconst_preterm ptm, pty)
  | _ -> failwith "unconst_preterm"

let rec env_of_preterm = function
    Varp (s, pty) -> [(s, pty)]
  | Constp (s, pty) -> []
  | Combp (l, r) -> env_of_preterm l @ env_of_preterm r
  | Typing (ptm, pty) -> env_of_preterm ptm
  | _ -> failwith "env_of_preterm"

let env_of_th = env_of_preterm o preterm_of_term o concl
let env_of_ths = List.concat o List.map env_of_th

end (* struct Preterm *)

