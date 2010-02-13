

let rec drop i list =
        match (i,list) with (_,[]) -> failwith "drop null"
                | (0,a::b) -> b
                | (i,a::b) -> a::(drop (i-1) b);;

let rec take i j =
  function
  [] -> [] |
  a::b -> match (i,j) with
      (0,0) -> [] |
      (0,j) -> a::(take 0 (j-1) b) |
      _ -> take (i-1) (j-1) b;;

let cannot f x = try (f x; false) with Failure _ -> true;;

(* ------------------------------------------------------------------ *)
(* UNIT TESTS *)
(* ------------------------------------------------------------------ *)

let new_test_suite() =
  let t = ref ([]:(string*bool) list) in
  let add_test (s,f) = (t:= ((s,f)::!t)) in
  let eval (s,f) = if f then () else failwith ("test suite: "^s) in
  let test() = (ignore (List.map eval  (!t));()) in
  add_test,test;;

let add_test,test = new_test_suite();;


(* ------------------------------------------------------------------ *)
(* LOCAL DEFINITIONS *)
(* ------------------------------------------------------------------ *)

let local_defs = ref ([]:(string * (string * term)) list);;

let add_interface (sym,tm) =
  if (can (assoc sym) (!the_overload_skeletons)) then
    (overload_interface (sym,tm))
  else (override_interface(sym,tm));;

let local_definition package_name tm =
  let list_mk_forall(vars,bod) = itlist (curry mk_forall) vars bod in
  let avs,bod = strip_forall tm in
  let l,r = try dest_eq bod
    with Failure _ -> failwith "new_local_definition: Not an equation" in
  let lv,largs = strip_comb l in
  let cname,ty = dest_var lv in
  let cname' = package_name^"'"^cname in
  let lv' = mk_var(cname',ty) in
  let l' = list_mk_comb(lv',largs) in
  let bod' = mk_eq(l',r) in
  let tm'= list_mk_forall(avs,bod') in
  let thm = new_definition tm' in
  let _ = (local_defs := (package_name,(cname,lv'))::(!local_defs)) in
  let _ = add_interface(cname,lv') in
  thm;;

let reduce_local_interface(package_name) =
  map (reduce_interface o snd)
    (filter (fun x -> ((fst x) = package_name)) !local_defs);;

let mk_local_interface(package_name) =
  map (add_interface o snd)
    (filter (fun x -> ((fst x) = package_name)) !local_defs);;



(* ------------------------------------------------------------------ *)
(* SAVING STATE *)
(* ------------------------------------------------------------------ *)

(****** Removed for now by JRH

let (save_state,get_state) =
  let state_array = ref [] in
  let save_state (key:string) =
    state_array :=
    (key,(!EVERY_STEP_TAC,!local_defs,!the_interface,
        !the_term_constants,!the_type_constants,
                        !the_overload_skeletons,
                 !the_axioms,!the_definitions))::!state_array in
  let get_state key =
    let (et,ld,i,tc,tyc,os,ax,def) = assoc key !state_array in
      (
        EVERY_STEP_TAC := et;
        local_defs := ld;
        the_interface := i;
        the_term_constants:= tc;
        the_type_constants:= tyc;
        the_overload_skeletons:= os;
        the_axioms:= ax;
        the_definitions:= def)
  in (save_state,get_state);;

save_state "lib_ext";;

*****)
