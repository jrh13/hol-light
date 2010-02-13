(* ------------------------------------------------------------------------- *)
(* A printer for goals etc.                                                  *)
(* ------------------------------------------------------------------------- *)

(* had (rev asl) in this method.  I don't want to reverse the list *)


let hash_of_string =
  let prime200 = 1223 in
  let prime = 8831 in
  let rec hashll v = match v with
    | [] -> 0
    | h::t ->
   (int_of_char (String.get h 0) + prime200*( hashll t)) mod prime in
  fun s ->
    let slt = explode s in
    hashll slt;;

let saved_hashstring =
    ref ((Hashtbl.create 300):(string,int) Hashtbl.t);;
let save_hashstring string =
    Hashtbl.add !saved_hashstring (string) (hash_of_string string);;
let mem_hashstring s = Hashtbl.mem !saved_hashstring s;;
let remove_hashstring s = Hashtbl.remove !saved_hashstring s;;
let find_hashstring s = Hashtbl.find !saved_hashstring s;;

let memhash_of_string s =
   if not(mem_hashstring s) then (save_hashstring s) ;
   find_hashstring s;;

let hash_of_type =
  let prime150 = 863 in
  let prime160 = 941 in
  let prime180 = 1069 in
  let prime190 = 1151 in
  let prime1200 = 9733 in
  let rec hashl u = match u with
    | [] -> 0
    | h::t -> ((hasht h) + prime190*(hashl t)) mod prime1200
    and
    hasht v = match v with
    | Tyvar s -> (prime150*memhash_of_string s + prime160) mod prime1200
    | Tyapp (s,tlt) -> let h = memhash_of_string s in
               let h2 = (h*h) mod prime1200 in
          (prime180*h2 + hashl tlt ) mod prime1200 in
  hasht;;

(* make hash_of_term constant on alpha-equivalence classes of
   terms *)

let rename_var n =
  fun v -> mk_var ("??_"^(string_of_int n),type_of v);;

let paform =
  let rec raform n env tm =
    match tm with
      | Var(_,_) -> assocd tm env tm
      | Const(_,_) -> tm
      | Comb (s,t) -> mk_comb(raform n env s, raform n env t)
      | Abs  (x,t) -> let x1 = rename_var n x in
                      mk_abs(x1, raform (n+1) ((x,x1)::env) t) in
  raform 0 [];;

let hash_of_term =
  let prime1220 = 9887 in
  let prime210 = 1291 in
  let prime220 = 1373 in
  let prime230 = 1451 in
  let prime240 = 1511 in
  let prime250 = 1583 in
  let prime260 = 1657 in
  let prime270 = 1733 in
  let prime280 = 1811 in
  let rec hasht u = match u with
    | Var (s,t) ->
      (prime210*(memhash_of_string s) + hash_of_type t) mod prime1220
    | Const (s,t) ->
      (prime220*(memhash_of_string s) + hash_of_type t) mod prime1220
    | Comb (s,t) -> let h = hasht s in
            let h2 = (h*h) mod prime1220 in
             (prime230*h2 + prime240*hasht t + prime250) mod prime1220
    | Abs   (s,t) -> let h = hasht s in
           let h2 = (h*h) mod prime1220 in
             (prime260*h2 + prime270*hasht t + prime280) mod prime1220
  in hasht o paform;;

let print_hyp n (s,th) =
  open_hbox();
  print_string " ";
  print_as 4 (string_of_int (hash_of_term (concl th)));
  print_string " [";
  print_qterm (concl th);
  print_string "]";
  (if not (s = "") then (print_string (" ("^s^")")) else ());
  close_box();
  print_newline();;

let rec print_hyps n asl =
  if asl = [] then () else
  (print_hyp n (hd asl);
   print_hyps (n + 1) (tl asl));;

let (print_goal_hashed:goal->unit) =
  fun (asl,w) ->
    print_newline();
    if asl <> [] then (print_hyps 0 (asl); print_newline()) else ();
    print_qterm w; print_newline();;

let (print_goalstate_hashed:int->goalstate->unit) =
  fun k gs -> let (_,gl,_) = gs in
              let n = length gl in
              let s = if n = 0 then "No subgoals" else
                        (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
                     ^" ("^(string_of_int n)^" total)" in
              print_string s; print_newline();
              if gl = [] then () else
              do_list (print_goal_hashed o C el gl) (rev(0--(k-1)));;

let (print_goalstack_hashed:goalstack->unit) =
  fun l ->
    if l = [] then print_string "Empty goalstack"
    else if tl l = [] then
      let (_,gl,_ as gs) = hd l in
      print_goalstate_hashed 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_goalstate_hashed p' gs;;

#install_printer print_goal_hashed;;
#install_printer print_goalstack_hashed;;
