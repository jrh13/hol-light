
(* small LP-based prover, to convert the HOL-terms to a coefficient
   matrix and back it uses the code of REAL_LINEAR_PROVER in the HOL
   Light distribution *)


let cddwrapper = "cdd_cert";;

(* in lin_of_hol one can replace the call to linear_add to a call to lin_add *)

let lin_of_hol =
  let one_tm = `&1:real`
  and zero_tm = `&0:real`
  and add_tm = `(+):real->real->real`
  and mul_tm = `(*):real->real->real`
  and lin_add = combine (+/) (fun x -> x =/ num_0) in
  let rec lin_of_hol tm =
    if tm = zero_tm then undefined
    else if not (is_comb tm) then (tm |=> Int 1)
    else if is_ratconst tm then (one_tm |=> rat_of_term tm) else
      let lop,r = dest_comb tm in
        if not (is_comb lop) then (tm |=> Int 1) else
          let op,l = dest_comb lop in
            if op = add_tm then lin_add (lin_of_hol l) (lin_of_hol r)
            else if op = mul_tm && is_ratconst l then (r |=> rat_of_term l)
            else (tm |=> Int 1) in
    lin_of_hol;;

let words s =
  let stre = Stream.of_string s in
  let is_empty st = match Stream.peek st with
      None -> true
    | Some _ -> false in
  let rec sb acc st =
    if is_empty st
    then [acc]
    else
      let t = Stream.next st in
        if t = ' ' then acc :: (sb "" st) else sb (acc ^ Char.escaped t) st
  in filter (fun x -> x <> "") (sb "" stre);;

let cdd ins =
  let outfn = Filename.temp_file "cdd" ".res"
  and infn = Filename.temp_file "cdd" ".ine" in
  let s = "cat " ^ infn ^ "| " ^ cddwrapper ^ " 2> /dev/null > " ^ outfn in
  let inch = open_out infn in
    output_string inch ins;
    close_out inch;
    if Sys.command s <> 0 then failwith "cdd" else
      let fd = Pervasives.open_in outfn in let data = input_line fd in close_in fd; Sys.remove infn; Sys.remove outfn; data;;

let rec take n l =
  match l with
      x :: xs -> if n = 0 then [] else x :: (take (n-1) xs)
    | [] -> [];;

let rec drop n l =
  match l with
      x :: xs -> if n = 0 then l else (drop (n-1) xs)
    | [] -> [];;

let lp_prover (eq,le,lt) =
  let one_tm = `&1:real` in
  let vars = (subtract (itlist (union o dom) (eq@le@lt) []) [one_tm]) in
  let neq = length eq
  and nle = length le
  and nlt = length lt
  and nr = length (eq@le@lt) in
  let get_row v = map (fun x -> applyd x (fun _ -> num_0) v) (eq@le@lt) in
  let rec rep n e = if n = 0 then [] else e :: (rep (n-1) e) in
  let one_at n =
    map (fun i -> (rep i (num_0))@[num_1]@(rep (n-i-1) (num_0))) (0--(n-1)) in
  let main_rows = map ((fun l -> num_0::l) o get_row) vars
  and lt_row = [minus_num num_1] @ (rep (length eq) num_0) @
    (rep (length le) num_0) @ (rep (length lt) num_1)
  and pos_rows = map (fun l -> (rep (length eq + 1 ) num_0) @ l)
    (one_at (length (le@lt)))
  and bvec = (num_0 :: (get_row one_tm)) in
  let mat = main_rows@[lt_row]@pos_rows in
  let string_of_row = (String.concat " ") o (map string_of_num) in
  let cddlp = (String.concat "\n"
                 ["H-representation";
                  "linearity "^(string_of_int (length main_rows))^" "^
                    (String.concat " " (map string_of_int (1--(length main_rows))));
                  "begin";
                  String.concat " " [string_of_int (length mat);string_of_int (nr+1);"rational"];
                  String.concat "\n" (map string_of_row mat);
                  "end";
                  String.concat " " ["minimize";string_of_row bvec]]) in
  let outp = (cdd cddlp) in
  let res = (* print_string cddlp; print_newline();   *)(* print_string outp; print_newline(); *)
    if outp = "No Contradiction" then failwith "No contradiction" else map Num.num_of_string (words outp) in
  let (req,rle,rlt) = (take neq res,
                       take nle (drop neq res),
                       take nlt (drop (nle+neq) res)) in
  let peq = map2 (fun r e -> if (r =/ num_0) then [] else [Eqmul (term_of_rat r, Axiom_eq e)]) req (0--(neq-1))
  and ple = map2 (fun r e -> if (r =/ num_0) then [] else [Product (Rational_lt r,Axiom_le e)]) rle (0--(nle-1))
  and plt = map2 (fun r e -> if (r =/ num_0) then [] else [Product (Rational_lt r,Axiom_lt e)]) rlt (0--(nlt-1)) in
  let pp = List.flatten (peq@ple@plt) in
  let refu = itlist (fun acc x -> Sum (acc,x)) (tl pp) (hd pp) in
    (*     print_string outp; *)
    (*     print_newline(); *)
    refu;;

let LP_PROVER =
  let is_alien tm =
    match tm with
        Comb(Const("real_of_num",_),n) when not(is_numeral n) -> true
      | _ -> false in
  let n_tm = `n:num` in
  let pth = REWRITE_RULE[GSYM real_ge] (SPEC n_tm REAL_POS) in
    fun translator (eq,le,lt) ->
      let eq_pols = map (lin_of_hol o lhand o concl) eq
      and le_pols = map (lin_of_hol o lhand o concl) le
      and lt_pols = map (lin_of_hol o lhand o concl) lt in
      let aliens =  filter is_alien
        (itlist (union o dom) (eq_pols @ le_pols @ lt_pols) []) in
      let le_pols' = le_pols @ map (fun v -> (v |=> Int 1)) aliens in
      let proof = lp_prover(eq_pols,le_pols',lt_pols) in
      let le' = le @ map (fun a -> INST [rand a,n_tm] pth) aliens in
        translator (eq,le',lt) proof;;

let LP_ARITH =
  let init = GEN_REWRITE_CONV ONCE_DEPTH_CONV [DECIMAL]
  and pure = GEN_REAL_ARITH LP_PROVER in
    fun tm -> let th = init tm in EQ_MP (SYM th) (pure(rand(concl th)));;

let LP_ARITH_TAC = CONV_TAC LP_ARITH;;
