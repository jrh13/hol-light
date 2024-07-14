(* ========================================================================= *)
(* The basic Metis loop.                                                     *)
(* ========================================================================= *)

module Loop =
struct

let rec loop res =
  match Resolution.iterate res with
    Resolution.Decided dec -> Some dec
  | Resolution.Undecided res -> loop res

open Ax_cj

let run rules =
  let ths = {axioms_thm = rules; conjecture_thm = []} in
  let res = Resolution.newResolution Resolution.default ths in
  match loop res with
    None -> failwith "metis: timeout"
  | Some (Resolution.Contradiction thm) -> thm
  | Some (Resolution.Satisfiable _) ->
      failwith "metis: found satisfiable assignment"

end

end
