needs "miz3.ml";;

type script_step =
| Tac of string * tactic
| Par of script_step list list;;

type prooftree =
| Prooftree of goal * (string * tactic) * prooftree list
| Open_goal of goal;;

let read_script filename lemmaname =
  let rec check_semisemi l =
    match l with
    | ";"::";"::_ -> true
    | " "::l' -> check_semisemi l'
    | _ -> false in
  let file = open_in filename in
  let lemma_string = "let "^lemmaname^" = prove" in
  let n = String.length lemma_string in
  let rec read_script1 () =
    let s = input_line file in
    if String.length s >= n & String.sub s 0 n = lemma_string
      then (explode s)@"\n"::read_script2 () else read_script1 ()
  and read_script2 () =
    let l = explode (input_line file) in
    if check_semisemi (rev l) then l else l@"\n"::read_script2 () in
  let l = read_script1 () in
  close_in file;
  l;;

let rec tokenize l =
  match l with
  | [] -> []
  | c::l' ->
      let l1,l23 = if isalnum c then many (some isalnum) l else [c],l' in
      let l2,l3 = many (some isspace) l23 in
      (implode l1,if l2 = [] then "" else " ")::tokenize l3;;

let parse_script l =
  let rec parse_statement s l =
    match l with
    | ("`",_)::(",",_)::l' -> s,l'
    | (x,y)::l' -> parse_statement (s^x^y) l'
    | [] -> failwith "parse_statement" in
  let rec parse_tactic b n s y' l =
    match l with
    | ("\\",y)::l' when not b -> parse_tactic b n (s^y'^"\\\\") y l'
    | (x,y)::l' ->
        if n = 0 & (x = "THEN" or x = "THENL" or x = ";" or x = "]" or x = ")")
        then (Tac(s,exec_tactic s)),l else
          let n' = if x = "[" or x = "(" then n + 1 else
            if x = "]" or x = ")" then n - 1 else n in
          let x',b' =
            if x = "`" then
              if b then "(parse_term \"",(not b) else "\")",(not b)
            else x,b in
          parse_tactic b' n' (s^y'^x') y l'
    | [] -> failwith "parse_tactic" in
  let rec parse_tactics tacs l =
    let tac,l' = parse_tactic true 0 "" "" l in
    parse_tactics1 (tac::tacs) l'
  and parse_tactics1 tacs l =
    match l with
    | ("THEN",_)::l' -> parse_tactics tacs l'
    | ("THENL",_)::("[",_)::l' ->
        let tac,l'' = parse_par_tactics [] l' in
        parse_tactics1 (tac::tacs) l''
    | _ -> (rev tacs),l
  and parse_par_tactics tacss l =
    let tacs,l' = parse_tactics [] l in
    match l' with
    | (";",_)::l'' -> parse_par_tactics (tacs::tacss) l''
    | ("]",_)::l'' -> (Par (rev (tacs::tacss))),l''
    | _ -> failwith "parse_par_tactics" in
  match l with
  | ("let",_)::_::("=",_)::("prove",_)::("(",_)::("`",_)::l' ->
      let s,l'' = parse_statement "" l' in
      let tacs,l''' = parse_tactics [] l'' in
     (match l''' with
      | [")",_; ";",_; ";",_] -> parse_term s,tacs
      | _ -> failwith "parse_script")
  | _ -> failwith "parse_script";;

let read_script1 filename lemmaname =
  parse_script (tokenize (read_script filename lemmaname));;

let tactic_of_script l =
  let rec tactic_of_script1 l =
    match l with
    | [] -> ALL_TAC
    | [Tac(_,tac)] -> tac
    | (Tac(_,tac))::l' -> tactic_of_script1 l' THEN tac
    | (Par ll)::l' ->
        tactic_of_script1 l' THENL (map (tactic_of_script1 o rev) ll) in
  tactic_of_script1 (rev l);;

let run_script (tm,l) = prove(tm,tactic_of_script l);;

let prooftree_of_script g l =
  let rec prooftrees_of gltl tl =
    match gltl with
    | [] -> []
    | (gl,t)::rst ->
        let tl1,tl' = chop_list (length gl) tl in
        (t tl1)::prooftrees_of rst tl' in
  let prooftree_of_script2 t gltl =
    flat (map fst gltl),(fun tl -> t (prooftrees_of gltl tl)) in
  let rec prooftree_of_script1 g l =
    match l with
    | [] -> [g],(function [t] -> t | _ -> failwith "prooftree_of_script1")
    | (Tac(s,tac))::l' ->
        let gl,t = prooftree_of_script1 g l' in
        let gltl = map (fun g' -> let _,x,_ = tac g' in
          x,(fun tl -> Prooftree(g',(s,tac),tl))) gl in
        prooftree_of_script2 t gltl
    | (Par ll)::l' ->
        let gl,t = prooftree_of_script1 g l' in
        let gltl = map2 prooftree_of_script1 gl (map rev ll) in
        prooftree_of_script2 t gltl in
  let gl,t = prooftree_of_script1 g (rev l) in
  t (map (fun x -> Open_goal x) gl);;

let goal_of_prooftree t =
  match t with
  | Prooftree(g,_,_) -> g
  | Open_goal(g) -> g;;

let rec step_of_prooftree prefix n context t =
  let frees_of_goal (asl,w) =
    union (flat (map (frees o concl o snd) asl)) (frees w) in
  let rec extra_ass ass' ass =
    if subset ass' ass then [] else (hd ass')::(extra_ass (tl ass') ass) in
  let rec lets prefix l =
    match l with
    | [] -> []
    | t::_ ->
        let l',l'' = partition ((=) (type_of t) o type_of) l in
        step_of_substep prefix (Let l')::lets prefix l'' in
  let rec intros prefix n ass =
    match ass with
    | [] -> [],n,[]
    | a::ass' ->
        let steps,n',context = intros prefix (n + 1) ass' in
        let lab = string_of_int n in
        (step_of_substep prefix (Assume(a,[lab]))::steps),
        n',((a,lab)::context) in
  let shift_labels steps =
    let labels = rev (labels_of_steps [] [] steps) in
    let labels' =
      map ((fun s -> [s],[string_of_int (int_of_string s - 1)]) o hd o fst)
        labels in
      snd (renumber_steps labels' [] steps) in
  let rec steps_of_prooftrees prefix n context (asl,_ as g) tl =
    match tl with
    | [] -> [],[],n,context
    | t'::tl' ->
        let (asl',w' as g') = goal_of_prooftree t' in
        let prefix' = prefix^(!proof_indent) in
        let ll =
          lets prefix' (subtract (frees_of_goal g') (frees_of_goal g)) in
        let vars = flat (map (function (_,_,Let l) -> l | _ -> []) ll) in
        let ass =
          extra_ass (map (concl o snd) asl') (map (concl o snd) asl) in
        let w'' = list_mk_forall(vars, itlist (curry mk_imp) ass w') in
        try
          let lab = assoc w'' context in
          let steps,labs,n',context' =
            steps_of_prooftrees prefix n context g tl' in
          steps,Label lab::labs,n',context'
        with Failure "find" ->
          if vars = [] & ass = [] then
            let steps,just,n',context' =
              steps_of_prooftree prefix n context t' in
            try
              let lab = assoc w'' context' in
              let steps',labs,n'',context'' =
                steps_of_prooftrees prefix n' context' g tl' in
              (steps@steps'),Label lab::labs,n'',context''
            with Failure "find" ->
              let lab = string_of_int n' in
              let steps',labs,n'',context'' =
                steps_of_prooftrees prefix (n' + 1)
                  ((w',lab)::context') g tl' in
              (steps@
               [rewrap_step (step_of_substep prefix (Have(w'',[lab],just)))]@
               steps'),Label lab::labs,n'',context''
          else
            let lab = string_of_int n in
            let steps,n',context' = intros prefix' (n + 1) ass in
            let steps',just,n'',context'' =
              steps_of_prooftree prefix' n' (rev context'@context) t' in
            let qed = [rewrap_step (step_of_substep prefix (Qed just))] in
            let steps'',n''' =
              if steps' = [] then (steps'@qed),n'' else
              match last steps' with
              | _,_,Have(w''',_,Proof(_,steps''',_)) when w''' = w' ->
                 (butlast steps'@
                  map (outdent (String.length !proof_indent))
                    (shift_labels steps''')),n''
              | _ -> (steps'@qed),n'' in
            let steps''',labs,n'''',context''' =
              steps_of_prooftrees prefix n''' ((w'',lab)::context'') g tl' in
            (step_of_substep prefix
              (Have(w'',[lab],
               Proof (Some (step_of_substep prefix Bracket_proof),
                 (ll@steps@steps''), None)))::
            steps'''),Label lab::labs,n'''',context'''
  and steps_of_prooftree prefix n context t =
    match t with
    | Prooftree((_,w as g),(s,tac),tl) ->
        let steps,f_labs,n',context' =
          steps_of_prooftrees prefix n context g tl in
        let b_labs = map ((fun x -> Label x) o C assoc context o concl o snd)
          (rev (fst g)) in
        steps,By((Tactic(s,K tac))::b_labs,f_labs,false),n',context'
    | Open_goal(g) -> [],By([Hole],[],false),n,context in
  let prefix' = prefix^(!proof_indent) in
  match t with
  | Prooftree((_,w as g),_,_) ->
      let steps,_,_,_ =
        steps_of_prooftrees prefix n context g [t] in
     (match last steps with
      | _,_,Have(_,_,just) ->
          step_of_substep prefix (Have(w,[string_of_int n],
            if length steps = 1 then just else
            let steps',_,_,_ =
              steps_of_prooftrees prefix' (n + 1) context g [t] in
            Proof (Some (step_of_substep prefix Bracket_proof),
              (butlast steps'@
            [rewrap_step (step_of_substep prefix (Qed just))]), None)))
      | _ -> failwith "step_of_prooftree")
  | _ -> failwith "step_of_prooftree";;

let miz3_of_hol filename lemmaname =
  let tm,l = read_script1 filename lemmaname in
  step_of_prooftree "" 1 [] (prooftree_of_script ([],tm) l);;

