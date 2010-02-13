let (use_proofobjects, use_extended_proofobjects) =
  try
    let n = Sys.getenv "HOLPROOFOBJECTS" in
    if n = "BASIC" then
      (true, false)
    else if n = "EXTENDED" then
      (true, true)
    else
      (false, false)
  with Not_found -> (false, false);;

let _ =
  if use_proofobjects then
    loads "proofobjects_trt.ml"
  else
    loads "proofobjects_dummy.ml";;
