module Metis_path = struct

(* The term `f 1 2 3` is encoded in HOL Light as follows:

         @
        / \
       @  3
      / \
     @  2
    / \
   f  1

*)

let rec hol_of_term_path tm path = match tm, path with
  | (tm, []) -> tm, ""
  | Term.Fn (f, args), i :: is ->
      let arity = length args in
      if not (i < arity) then
        raise (Assert "i < arity");
      let (tm', path') = hol_of_term_path (List.nth args i) is in
      let make n c = String.implode (List.tabulate n (fun _ -> c)) in
      (tm', make (arity - i - 1) 'l' ^ "r" ^ path')
  | _ -> failwith "hol_of_term_path"
;;

let hol_of_atom_path (p, args) = hol_of_term_path (Term.Fn (p, args))
;;

let hol_of_literal_path (pol, atom) path =
  let s, path = hol_of_atom_path atom path in
  s, (if pol then path else "r" ^ path)
;;

end (* struct metis_path *)
;;
