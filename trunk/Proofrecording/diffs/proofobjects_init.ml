let (use_proofobjects, use_extended_proofobjects, use_coq) =
  try
    let n = Sys.getenv "HOLPROOFOBJECTS" in
    if n = "BASIC" then
      (true, false, false)
    else if n = "EXTENDED" then
      (true, true, false)
    else if n = "COQ" then
      (true, true, true)
    else
      (false, false, false)
  with Not_found -> (false, false, false);;

let _ =
  if use_proofobjects then
    if use_coq then
      loads "proofobjects_coq.ml"
    else
      loads "proofobjects_trt.ml"
  else
    loads "proofobjects_dummy.ml";;
