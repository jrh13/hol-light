(* ========================================================================= *)
(*                 Proof-objects for HOL-light                               *)
(*                                                                           *)
(*       Steven Obua, TU München, December 2004                              *)
(*                                                                           *)
(*       based on Sebastian Skalberg's HOL4 proof-objects                    *)
(* ========================================================================= *)

#load "unix.cma";;

module type Proofobject_primitives =
  sig

    type proof

    val proof_REFL : term -> proof
    val proof_TRANS : proof * proof -> proof
    val proof_MK_COMB : proof * proof -> proof
    val proof_ASSUME : term -> proof
    val proof_EQ_MP : proof -> proof -> proof
    val proof_IMPAS : proof -> proof -> proof
    val proof_DISCH : proof -> term -> proof
    val proof_DEDUCT_ANTISYM_RULE : proof * term -> proof * term -> proof
    val proof_BETA : term -> proof
    val proof_ABS : term -> proof -> proof
    val proof_INST_TYPE : (hol_type * hol_type) list -> proof -> proof
    val proof_INST : (term * term) list -> proof -> proof
    val proof_new_definition : string -> term -> proof
    val proof_CONJ : proof -> proof -> proof
    val proof_CONJUNCT1 : proof -> proof
    val proof_CONJUNCT2 : proof -> proof
    val proof_new_basic_type_definition :
        string -> string * string -> term * term -> proof -> proof
    val proof_SPEC : term -> proof -> proof
    val proof_SYM : proof -> proof
    val proof_GEN : proof -> term -> proof
    val proof_DISJ1 : proof -> term -> proof
    val proof_DISJ2 : proof -> term -> proof
    val proof_NOTI : proof -> proof
    val proof_NOTE : proof -> proof
    val proof_CONTR : proof -> term -> proof
    val proof_DISJCASES : proof -> proof -> proof -> proof
    val proof_CHOOSE : term -> proof -> proof -> proof
    val proof_EXISTS : term -> term -> proof -> proof

    val new_axiom_name : string -> string
    val proof_new_axiom : string -> term -> proof

    val save_proof : string -> proof -> (term option) -> unit
    val proof_database : unit -> ((string * proof * (term option)) list)

    val export_proofs : string option -> (string * proof * (term option)) list -> unit
    val export_saved_proofs : string option -> unit
end;;

module Proofobjects : Proofobject_primitives = struct

  let writeln s p = p;;
(*    let q = s^"\n" in
    (output stdout q 0 (String.length q); p);;*)

  type tag = string

  type proof_info_rec =
      {disk_info: (string * string) option ref;
       status: int ref;
       references: int ref;
       queued: bool ref}

  type proof_info = Info of proof_info_rec

  type ('a, 'b) libsubst_rec = {redex:'a; residue:'b}
  type ('a, 'b) libsubst = (('a,'b) libsubst_rec) list

  let pair2libsubstrec =
    fun (a,b) -> {redex=b;residue=a}

(* note: not all of the proof_content constructors are actually used, some are just legacy from the HOL4 proof objects *)
  type proof =
      Proof of (proof_info * proof_content * (unit -> unit))
  and proof_content =
      Prefl of term
    | Pinstt of proof * ((hol_type,hol_type) libsubst)
    | Psubst of proof list * term * proof
    | Pabs of proof * term
    | Pdisch of proof * term
    | Pmp of proof * proof
    | Phyp of term
    | Paxm of string * term
    | Pdef of string * string * term
    | Ptmspec of string * string list * proof
    | Ptydef of string * string * proof
    | Ptyintro of string * string * string * string * term * term * proof
    | Poracle of tag * term list * term
    | Pdisk
    | Pspec of proof * term
    | Pinst of proof * (term,term) libsubst
    | Pgen of proof * term
    | Pgenabs of proof * term option * term list
    | Psym of proof
    | Ptrans of proof * proof
    | Pcomb of proof * proof
    | Peqmp of proof * proof
    | Peqimp of proof
    | Pexists of proof * term * term
    | Pchoose of term * proof * proof
    | Pconj of proof * proof
    | Pconjunct1 of proof
    | Pconjunct2 of proof
    | Pdisj1 of proof * term
    | Pdisj2 of proof * term
    | Pdisjcases of proof * proof * proof
    | Pnoti of proof
    | Pnote of proof
    | Pcontr of proof * term
    | Pimpas of proof * proof

  let THEORY_NAME = "hollight"

  let content_of (Proof (_,p,_)) = p

  let inc_references (Proof(Info{references=r},_,_) as p) = (
    let
        old = !r
    in
    r := old + 1;
    p)

  let concat = String.concat ""

  let dummy_fun () = ()

  let mk_proof p = Proof(Info {disk_info = ref None; status = ref 0; references = ref 0; queued = ref false},p, dummy_fun)

  let global_ax_counter = let counter = ref 1 in let f = fun () -> (let x = !counter in counter := !counter+1; x) in f

  let new_axiom_name n = concat["ax_"; n; "_"; string_of_int(global_ax_counter())]

  let proof_REFL t = writeln "REFL" (mk_proof (Prefl t))

  let proof_TRANS (p,q) = writeln "TRANS" (
    match (content_of p, content_of q) with
      (Prefl _,_) -> q
    | (_, Prefl _) -> p
    | _ -> mk_proof (Ptrans (inc_references p, inc_references q)))

  let proof_MK_COMB (p1,p2) = writeln "MK_COMB" (
    (match (content_of p1, content_of p2) with
      (Prefl tm1, Prefl tm2) -> proof_REFL (mk_comb (tm1, tm2))
    | _ ->  mk_proof (Pcomb (inc_references p1, inc_references p2))))

  let proof_ASSUME t = writeln "ASSUME "(mk_proof (Phyp t))

  let proof_EQ_MP p q = writeln "EQ_MP" (
    (match content_of p with
      Prefl _ -> q
    | _ -> mk_proof (Peqmp(inc_references p, inc_references q))))

  let proof_IMPAS p1 p2 = writeln "IMPAS" (
    mk_proof (Pimpas (inc_references p1, inc_references p2)))

  let proof_DISCH p t = writeln "DISCH" (mk_proof (Pdisch(inc_references p,t)))

  let proof_DEDUCT_ANTISYM_RULE (p1,t1) (p2,t2) = writeln "DEDUCT_ANTISYM_RULE" (
    proof_IMPAS (proof_DISCH p1 t2) (proof_DISCH p2 t1))

  let proof_BETA t = writeln "BETA" (mk_proof (Prefl t))

  let proof_ABS x p = writeln "ABS" (
    (match (content_of p) with
      Prefl tm -> proof_REFL (mk_abs(x,tm))
    | _ -> mk_proof (Pabs(inc_references p,x))))

  let proof_INST_TYPE s p = writeln "INST_TYPE" (mk_proof (Pinstt(inc_references p, map pair2libsubstrec s)))

  let proof_INST s p = writeln "INST" (mk_proof (Pinst(inc_references p, map pair2libsubstrec s)))

  let proof_new_definition cname t = writeln "new_definition" (mk_proof (Pdef (THEORY_NAME, cname, t)))

  let proof_new_axiom axname t = writeln "new_axiom" (mk_proof (Paxm (axname, t)))

  let proof_CONJ p1 p2 = writeln "CONJ" (mk_proof (Pconj (inc_references p1, inc_references p2)))

  let proof_CONJUNCT1 p = writeln "CONJUNCT1" (mk_proof (Pconjunct1 (inc_references p)))

  let proof_CONJUNCT2 p = writeln "CONJUNCT2" (mk_proof (Pconjunct2 (inc_references p)))

  let proof_new_basic_type_definition tyname (absname, repname) (pt,tt) p = writeln "new_basic_type_definition" (
    mk_proof(Ptyintro (THEORY_NAME, tyname, absname, repname, pt, tt,inc_references p)))

(* ---- used only in substitute_proof calls ---- *)

  let proof_SPEC s p = writeln "SPEC" (mk_proof (Pspec(inc_references p, s)))

  let proof_SYM p = writeln "SYM" (mk_proof (Psym(inc_references p)))

  let proof_GEN p a = writeln "GEN" (mk_proof (Pgen(inc_references p, a)))

  let proof_DISJ1 p a = writeln "DISJ1" (mk_proof (Pdisj1 (inc_references p, a)))

  let proof_DISJ2 p a = writeln "DISJ2" (mk_proof (Pdisj2 (inc_references p, a)))

  let proof_NOTI p = writeln "NOTI" (mk_proof (Pnoti (inc_references p)))

  let proof_NOTE p = writeln "NOTE" (mk_proof (Pnote (inc_references p)))

  let proof_CONTR p a = writeln "CONTR" (mk_proof (Pcontr (inc_references p, a)))

  let proof_DISJCASES p q r = writeln "DISJCASES" (mk_proof (Pdisjcases (inc_references p, inc_references q, inc_references r)))

  let proof_CHOOSE a p q = writeln "CHOOSE" (mk_proof (Pchoose (a, inc_references p, inc_references q)))

  let proof_EXISTS x y p  = writeln "EXISTS" (mk_proof (Pexists (inc_references p, x, y)))

(* ---- formerly known as proofio.ml ---- *)

let ensure_export_directory thyname =
  let dir = Sys.getenv "HOLPROOFEXPORTDIR" in
  let dirsub = Filename.concat dir "hollight" in
  let dirsubsub = Filename.concat dirsub thyname in
  let mk d = if Sys.file_exists d then () else Unix.mkdir d 509
  in
    (mk dir;
     mk dirsub;
     mk dirsubsub;
     dirsubsub);;

(* ---- Useful functions on terms ---- *)
let rec types_of tm =
    if is_var tm
    then [type_of tm]
    else if is_const tm
    then [type_of tm]
    else if is_comb tm
    then
        let
            (f,a) = dest_comb tm
        in
            union (types_of f) (types_of a)
    else
        let
            (x,a) = dest_abs tm
        in
            insert (type_of x) (types_of a);;

let beta_conv tm =
  try let (f,arg) = dest_comb tm in
      let (v,bod) = dest_abs f in
      vsubst [(arg,v)] bod
  with Failure _ -> failwith "beta_conv: Not a beta-redex";;

let eta_conv tm =
  try
    (let (v, bod) = dest_abs tm in
    let (f, arg) = dest_comb bod in
      if (arg = v && (not(vfree_in v f))) then
        f
      else failwith "")
  with
    Failure _ -> failwith "eta_conv: Not an eta-redex";;

let rec be_contract tm =
    let rec bec tm = try try Some (beta_conv tm)
            with Failure _ ->
                   Some (eta_conv tm)
            with Failure _ ->
                   if is_comb tm
                   then
                       (let
                           (f,x) = dest_comb tm
                       in
                           match bec f with
                               Some f' -> Some (mk_comb(f',x))
                             | None -> (match bec x with
                                            Some x' -> Some (mk_comb(f,x'))
                                          | None -> None))
                   else if is_abs tm
                   then
                       (let
                         (x,body) = dest_abs tm
                       in
                           (match bec body with
                               Some body' -> Some (mk_abs(x,body'))
                             | None -> None))
                   else None
    in
        (match bec tm with
            Some tm' -> be_contract tm'
          | None -> tm);;

let rec polymorphic x =
  if is_vartype x then true else exists polymorphic (snd (dest_type x))

(* ---- From Lib etc. ---- *)


let rec append = fun xlist l ->
  (match xlist with
    [] -> l
  | (x::xs) -> x::(append xs l));;

let assoc1 item =
  let rec assc =
    (function (((key,_) as e)::rst) -> if item=key then Some e else assc rst
      | [] -> None)
  in
    assc;;


let rec listconcat =
  function [] -> []
    | (l::ls) -> append l (listconcat ls);;

let listnull =
  function [] -> true | _ -> false;;

(* ---- exported ---- *)
let encodeXMLEntities m = m;;let encodeXMLEntities s =
  let len = String.length s in
  let encodeChar  = function '<' -> "&lt;" | '>' -> "&gt;" | '&' -> "&amp;" | '\'' -> "&apos;" | '"' -> "&quot;" | c -> String.make 1 c in
  let rec encodeStr i =  if (i<len) then (encodeChar (String.get s i))::(encodeStr (i+1)) else [] in
  String.concat "" (encodeStr 0);;

let encodeXMLEntitiesOut out = function x -> out (encodeXMLEntities x);;


let content_of (Proof (_,x,_)) = x;;

let rec explode_subst =
  function [] -> []
    | ({redex=x;residue=y}::rest) -> x::y::(explode_subst rest);;

let rec app f =
  function [] -> ()
    | (x::l) -> (f x; app f l);;

let disk_info_of (Proof(Info {disk_info=di},_,_)) = !di;;

let set_disk_info_of (Proof(Info {disk_info=di},_,_)) thyname thmname =
    di := Some (thyname,thmname);;

let references (Proof (Info info,_,_)) = !(info.references);;

let wrap b e s = b^s^e;;

let xml_empty_tag = wrap "<" "/>";;
let xml_start_tag = wrap "<" ">";;
let xml_end_tag = wrap "</" ">";;
let xml_attr attr =
    itlist (function (tag,v) ->
            function s ->
               concat[" ";tag;"=\"";v;"\"";s]
           )
           attr "";;
let xml_element tag attr children =
    let
        header = tag ^ (xml_attr attr)
    in
        (if listnull children
         then xml_empty_tag header
         else wrap (xml_start_tag header) (xml_end_tag tag) (concat children));;

let id_to_atts curthy id = [("n", encodeXMLEntities id)];; (* There is only one theory in Hol-Light, therefore id_to_atts is superfluous *)

let glob_counter = ref 1;;

let get_counter () =
  let
      res = !glob_counter
  in
    glob_counter := res + 1;
    res;;

let get_iname =  string_of_int o get_counter;;

let next_counter () = !glob_counter;;

let trivial p =
      match (content_of p) with
        Prefl _ -> true
      | Paxm _ -> true
      | Pdisk -> true
      | Phyp _ -> true
      | Poracle _ -> true
      | _ -> false;;

let do_share p = references p > 1 & not (trivial p);;

exception Err of string*string;;

(* ---- The General List Formerly Known As Net ---- *)

type 'a exprnet = (('a list) ref) * ('a -> ('a list))

let empty_net f () = (ref [], f);;

let rec lookup'_net net x =
  match net with
    [] -> raise Not_found
  | (a::l) -> if (a = x) then 0 else 1+(lookup'_net l x);;

let lookup_net (net,f) x = lookup'_net (!net) x;;

let insert'_net (net,f) x =
  try lookup'_net !net x; () with Not_found -> ((net := (!net)@[x]);());;

let rec insert_net ((net,f) as n) x =
  (app (insert_net n) (f x); insert'_net n x);;

let to_list_net (net,f) = !net;;

(* ---- The Type Net (it's not a net any more!) ---- *)

type yy_net = hol_type exprnet;;

let yy_empty = empty_net (function x -> if is_type x then snd (dest_type x) else []);;

let yy_lookup = lookup_net;;

let yy_output_types out thyname net =
    let
        all_types = to_list_net net in let rec
        xml_index ty = xml_element "tyi" [("i",string_of_int (yy_lookup net ty))] []
        and xml_const id = xml_element "tyc" (id_to_atts thyname id) []
        and out_type ty =
          if is_vartype ty then out (xml_element "tyv" [("n",encodeXMLEntities (dest_vartype ty))] [])
          else (
            match dest_type ty with
              (id, []) -> out (xml_const id)
            | (id, tl) -> out (xml_element "tya" [] ((xml_const id)::(map xml_index tl)))
          )
    in
        out "<tylist i=\"";
        out (string_of_int (length all_types));
        out "\">";
        app out_type all_types;
        out "</tylist>";;

let yy_insert = insert_net;;

(* ---- The Term Net (it's not a net anymore!) ---- *)

type mm_net = term exprnet;;

let mm_empty = empty_net (
  function tm ->
    if is_abs tm then
      (let (x,b) = dest_abs tm in [x; b])
    else if is_comb tm then
      (let (s,t) = dest_comb tm in [s; t])
    else
      [])

let mm_lookup net x = lookup_net net (be_contract x);;

let mm_insert net x = insert_net net (be_contract x);;

let mm_output_terms out thyname types net =
    let all_terms = to_list_net net in
    let xml_type ty = xml_element "tyi" [("i",string_of_int (yy_lookup types ty))] [] in
    let xml_index tm = xml_element "tmi" [("i",string_of_int (mm_lookup net tm))] [] in
    let out_term tm =
            if is_var tm
            then
                let
                    (name,ty) = dest_var tm
                in
                    out (xml_element "tmv" [("n",encodeXMLEntities name);("t", string_of_int (yy_lookup types ty))] [])
            else if is_const tm
            then
                let (name, ty) = (dest_const tm) in
                let general_ty = get_const_type name in
                let atts = [("n",encodeXMLEntities name)]
                in
                    if polymorphic general_ty then
                      out (xml_element "tmc" (atts@[("t",string_of_int (yy_lookup types ty))]) [])
                    else out (xml_element "tmc" atts [])
            else if is_comb tm
            then
                let
                    (f,a) = dest_comb tm
                in
                    out (xml_element "tma" [("f", string_of_int (mm_lookup net f));("a",string_of_int (mm_lookup net a))] [])
            else
                let
                    (x,a) = dest_abs tm
                in
                    out (xml_element "tml" [("x", string_of_int (mm_lookup net x));("a",string_of_int (mm_lookup net a))] [])
    in
        out "<tmlist i=\"";
        out (string_of_int(length all_terms));
        out "\">";
        app out_term all_terms;
        out "</tmlist>";;


(* ---- collect_types_terms ---- *)

let collect_types_terms thyname out prf c_opt =
    let
        will_be_shared prf = (
            match disk_info_of prf with
                Some _ -> true
              | None -> do_share prf) in let

        types = yy_empty () in let
        terms = mm_empty () in let

        insert_type ty = yy_insert types ty in let

        insert_term tm = (mm_insert terms tm;
                          app (yy_insert types) (types_of tm)) in let rec

        ct' prf =
            (match content_of prf with
                Pinstt(prf,tsubst) -> (app (function {redex=x;residue=u}->(insert_type x; insert_type u))
                                           tsubst;
                                       ct prf)
              | Psubst(prfs,tm,prf) -> (insert_term tm;
                                        ct prf;
                                        app ct prfs)
              | Pabs(prf,tm) -> (insert_term tm;
                                 ct prf)
              | Pdisch(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Pmp(prf1,prf2) -> (ct prf1; ct prf2)
              | Poracle(_,tms,tm) -> (insert_term tm;
                                      app insert_term tms)
              | Pdef(_,_,tm) -> insert_term tm
              | Ptmspec(_,_,prf) -> ct prf
              | Ptydef(_,_,prf) -> ct prf
              | Ptyintro(_,_,_,_,pt,tt,prf) -> (insert_term pt; insert_term tt;ct prf)
              | Pspec(prf,tm) -> (insert_term tm; ct prf)
              | Pinst(prf,subst) -> (app (fun{redex=x;residue=u}->(insert_term x;
                                                              insert_term u))
                                         subst;
                                     ct prf)
              | Pgen(prf,tm) -> (insert_term tm; ct prf)
              | Pgenabs(prf,tm_opt,tms) -> (match tm_opt with
                                                Some tm -> insert_term tm
                                              | None -> ();
                                            app insert_term tms;
                                            ct prf)
              | Psym prf -> ct prf
              | Ptrans(prf1,prf2) -> (ct prf1; ct prf2)
              | Pcomb(prf1,prf2) -> (ct prf1; ct prf2)
              | Peqmp(prf1,prf2) -> (ct prf1; ct prf2)
              | Peqimp prf -> ct prf
              | Pexists(prf,ex,w) -> (insert_term ex;
                                      insert_term w;
                                      ct prf)
              | Pchoose(v,prf1,prf2) -> (insert_term v; ct prf1; ct prf2)
              | Pconj(prf1,prf2) -> (ct prf1; ct prf2)
              | Pconjunct1 prf -> ct prf
              | Pconjunct2 prf -> ct prf
              | Pdisj1(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Pdisj2(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Pdisjcases(prf1,prf2,prf3) -> (ct prf1; ct prf2; ct prf3)
              | Pnoti prf -> ct prf
              | Pnote prf -> ct prf
              | Pcontr(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Prefl tm -> insert_term tm
              | Phyp tm -> insert_term tm
              | Pdisk -> ()
              | Paxm (_,tm) -> insert_term tm
              | Pimpas (prf1,prf2) -> (ct prf1; ct prf2))
        and ct prf =
            if will_be_shared prf
            then ()
            else ct' prf in let

        _ = ct' prf in let
        _ = (match c_opt with
                    Some c -> insert_term c
                  | None -> ()) in let
        _ = yy_output_types out thyname types in let
        _ = mm_output_terms out thyname types terms
    in
        (types,terms);;

let rec export_proof path thyname thmname p c_opt il  =
  let outchannel = open_out (Filename.concat path (thmname^".prf")) in
  let out = output_string outchannel in
  let nout = encodeXMLEntitiesOut out in
  let
      _ = out "<proof>" in let

      (types,terms) = collect_types_terms thyname out p c_opt in let

      wti att tm =
        (out " ";
         out att;
         out "=\"";
         out (string_of_int (mm_lookup terms tm));
         out "\"") in let

      wt tm = try (out "<tmi"; wti "i" tm; out "/>") with Not_found -> raise (Err("export_proof","Term not found!")) in let

      wty ty =
        try (out "<tyi i=\"";
             out (string_of_int (yy_lookup types ty));
             out "\"/>") with Not_found -> raise (Err("export_proof","Type not found!")) in let

      wdi thy thm =
        (out "<pfact ";
         if not (thy = thyname)
         then (out "s=\"";
               out thy;
               out "\" ")
         else ();
         out "n=\"";
         nout thm;
         out "\"/>") in let

      write_proof p il =
       (let rec
          share_info_of p il =
            (match (disk_info_of p) with
              Some (thyname,thmname) -> Some(thyname,thmname,il)
            | None ->
                if do_share p then
                  let name = get_iname() in set_disk_info_of p thyname name; Some(thyname,name,(name,p,None)::il)
                else
                  None
            )
          and
          dump str il prfs =
                    (let
                        _ = out (xml_start_tag str) in let
                        res = rev_itlist (function p -> function il -> wp il p) prfs il in let
                        _ = out (xml_end_tag str)
                    in
                        res)
          and
          wp' il =
            (function
              (Prefl tm) -> (out "<prefl"; wti "i" tm; out "/>"; il)
            |  (Pinstt(p,lambda)) ->
                   (let
                        _ = out "<pinstt>" in let
                        res = wp il p in let
                        _ = app wty (explode_subst lambda) in let
                        _ = out "</pinstt>"
                    in
                        res)
            |  (Psubst(ps,t,p)) ->
                   (let
                        _ = (out "<psubst"; wti "i" t; out ">") in let
                        il' = wp il p in let
                        res = rev_itlist (function p -> function il -> wp il p) ps il' in let
                        _ = out "</psubst>"
                    in
                        res)
            |  (Pabs(p,t)) ->
                   (let
                        _ = (out "<pabs"; wti "i" t; out ">") in let
                        res = wp il p in let
                        _ = out "</pabs>"
                    in
                        res)
            |  (Pdisch(p,tm)) ->
                    (let
                        _ = (out "<pdisch"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pdisch>"
                    in
                        res)
            |  (Pmp(p1,p2)) -> dump "pmp" il [p1;p2]
            |  (Phyp tm) -> (out "<phyp"; wti "i" tm; out "/>"; il)
            |  (Paxm(name,tm)) ->
                    (out "<paxiom n=\"";
                     nout name;
                     out "\"";
                     wti "i" tm;
                     out "/>";
                     il)
            |  (Pdef(seg,name,tm)) ->
                    (out "<pdef s=\"";
                     out seg;
                     out "\" n=\"";
                     nout name;
                     out "\"";
                     wti "i" tm;
                     out "/>";
                     il)
            |  (Ptmspec(seg,names,p)) ->
                    (let
                        _ = (out "<ptmspec s=\""; out seg; out "\">") in let
                        res = wp il p in let
                        _ = app (function s -> (out "<name n=\""; nout s; out "\"/>")) names in let
                        _ = out "</ptmspec>"
                    in
                        res)
            |  (Ptydef(seg,name,p)) ->
                    (let
                        _ = (out "<ptydef s=\""; out seg; out "\" n=\""; nout name; out "\">") in let
                        res = wp il p in let
                        _ = out "</ptydef>"
                    in
                        res)
            |  (Ptyintro(seg,name,abs,rep,pt,tt,p)) ->
                    (let
                        _ = (out "<ptyintro s=\""; out seg; out "\" n=\""; nout name;
                             out "\" a=\""; out abs; out "\" r=\""; out rep; out "\">") in let

                        _ = wt pt in let
                        _ = wt tt in let
                        res = wp il p in let
                        _ = out "</ptyintro>"
                    in
                        res)
            |  (Poracle(tg,asl,c)) -> raise (Err("export_proof", "sorry, oracle export is not implemented!"))
(*                  (out "<poracle>";
                     app (function s -> (out "<oracle n=\""; nout s; out "\"/>")) (Tag.oracles_of tg);
                     wt c;
                     app wt asl;
                     out "</poracle>";
                     il)*)
            |  (Pspec(p,t)) ->
                    (let
                        _ = (out "<pspec"; wti "i" t; out ">") in let
                        res = wp il p in let
                        _ = out "</pspec>"
                    in
                        res)
            |  (Pinst(p,theta)) ->
                    (let
                        _ = out "<pinst>" in let
                        res = wp il p in let
                        _ = app wt (explode_subst theta) in let
                        _ = out "</pinst>"
                    in
                        res)
            |  (Pgen(p,x)) ->
                    (let
                        _ = (out "<pgen"; wti "i" x; out ">") in let
                        res = wp il p in let
                        _ = out "</pgen>"
                    in
                        res)
            |  (Pgenabs(p,opt,vl)) ->
                    (let
                        _ = out "<pgenabs" in let
                        _ = (match opt with
                                    Some c -> wti "i" c
                                  | None -> ()) in let
                        _ = out ">" in let
                        res = wp il p in let
                        _ = app wt vl in let
                        _ = out "</pgenabs>"
                    in
                        res)
                  |  (Psym p) -> dump "psym" il [p]
                  |  (Ptrans(p1,p2)) -> dump "ptrans" il [p1;p2]
                  |  (Pcomb(p1,p2)) -> dump "pcomb" il [p1;p2]
                  |  (Peqmp(p1,p2)) -> dump "peqmp" il [p1;p2]
                  |  (Peqimp p) -> dump "peqimp" il [p]
                  |  (Pexists(p,ex,w)) ->
                    (let
                        _ = (out "<pexists"; wti "e" ex; wti "w" w; out ">") in let
                        res = wp il p in let
                        _ = out "</pexists>"
                    in
                        res)
                  |  (Pchoose(v,p1,p2)) ->
                    (let
                        _ = (out "<pchoose"; wti "i" v; out ">") in let
                        il' = wp il p1 in let
                        res = wp il' p2 in let
                        _ = out "</pchoose>"
                    in
                        res)
                  |  (Pconj(p1,p2)) -> dump "pconj" il [p1;p2]
                  |  (Pimpas(p1,p2)) -> dump "pimpas" il [p1;p2]
                  |  (Pconjunct1 p) -> dump "pconjunct1" il [p]
                  |  (Pconjunct2 p) -> dump "pconjunct2" il [p]
                  |  (Pdisj1(p,tm)) ->
                    (let
                        _ = (out "<pdisj1"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pdisj1>"
                    in
                        res)
                  |  (Pdisj2(p,tm)) ->
                    (let
                        _ = (out "<pdisj2"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pdisj2>"
                    in
                        res)
                  |  (Pdisjcases(p1,p2,p3)) -> dump "pdisjcases" il [p1;p2;p3]
                  |  (Pnoti p) -> dump "pnoti" il [p]
                  |  (Pnote p) -> dump "pnote" il [p]
                  |  (Pcontr(p,tm)) ->
                    (let
                        _ = (out "<pcontr"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pcontr>"
                    in
                        res)
                  |  Pdisk -> raise (Err("wp'","shouldn't try to write pdisk"))
            )
          and wp il p =
               (let
                    res = match (share_info_of p il) with
                            Some(thyname',thmname,il') -> (wdi thyname' thmname; il')
                          | None -> wp' il (content_of p)
                in res) in let

          res = (match disk_info_of p with
                              Some(thyname',thmname') ->
                              if thyname' = thyname &
                                 thmname' = thmname
                              then
                                  wp' il (content_of p)
                              else
                                  (wdi thyname' thmname';
                                   il)
                            | None -> wp' il (content_of p))
         in res) in let

        il = write_proof p il in let
        _ = (match c_opt with
                    Some c -> wt c
                  | None -> ()) in let
        _ = (out "</proof>\n";(close_out outchannel))  in let
        _ = set_disk_info_of p thyname thmname
        in
           match il with
             [] -> () (* everything has been written *)
           | ((thmname',prf,c_opt)::rest) -> export_proof path thyname thmname' prf c_opt rest;;

let export_proofs theory_name l' =
  let theory_name = match theory_name with None -> THEORY_NAME | Some n -> n in
  let path = ensure_export_directory theory_name in
  let ostrm = open_out (Filename.concat path "facts.lst") in
  let out = output_string ostrm in
  let _ = app (function (s,_,_) -> out (s^"\n")) l' in
  let _ = flush ostrm in
  let _ =
    (match l' with
      [] -> ()
    | ((thmname,p,c_opt)::rest) -> export_proof path theory_name thmname p c_opt rest) in
  let num_int_thms = next_counter() - 1 in
  let _ = out ((string_of_int num_int_thms)^"\n");(close_out ostrm) in
  ();;

let the_proof_database = ref ([]:(string*proof*(term option)) list);;

exception Duplicate_proof_name;;

let rec search_proof_name n db =
  match db with [] -> () | ((m, a, b)::db') -> if n=m then (raise Duplicate_proof_name) else search_proof_name n db'

let save_proof name p c_opt =
  let _ = search_proof_name name (!the_proof_database)
  in
  (the_proof_database :=
    (name, p, c_opt)::(!the_proof_database));;

let proof_database () = !the_proof_database;;

(* this is a little bit dangerous, because the function is not injective,
   but I guess one can live with that *)
let make_filesystem_compatible s =
  let modify = function
    | "/" -> "_slash_"
    | "\\" -> "_backslash_"
    | "=" -> "_equal_"
    | ">" -> "_greaterthan_"
    | "<" -> "_lessthan_"
    | "?" -> "_questionmark_"
    | "!" -> "_exclamationmark_"
    | "*" -> "_star_"
    | s -> s
  in
  implode (map modify (explode s));;

let export_saved_proofs thy =
  let context = rev (proof_database ()) in
  export_proofs thy (map (function (s,p,c) -> (make_filesystem_compatible s,p,c)) context);;

end;;

include Proofobjects;;
