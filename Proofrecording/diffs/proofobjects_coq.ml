(* ======================================================================================== *)
(*                 Proof-objects for HOL-light, exportation to Coq                          *)
(*                                                                                          *)
(*       Steven Obua, TU Mnchen, December 2004                                              *)
(*       Chantal Keller, Laboratoire d'Informatique de Polytechnique (France), January 2010 *)
(*                                                                                          *)
(*       based on Sebastian Skalberg's HOL4 proof-objects                                   *)
(* ======================================================================================== *)

#load "unix.cma";;
#load "depgraph.cma";;


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
    val proof_new_definition : string -> hol_type -> term -> proof
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

    val export_saved_proofs : unit -> unit
    val export_one_proof : string -> unit
    val export_list : string list -> unit
  end;;


module Proofobjects : Proofobject_primitives = struct


  let THEORY_NAME = "hollight";;



  (****** Utilities ******)

  (* this is a little bit dangerous, because the function is not injective,
     but I guess one can live with that *)
  let modify = function
    | "/" -> "_slash_"
    | "\\" -> "_backslash_"
    | "=" -> "_equal_"
    | ">" -> "_greaterthan_"
    | "<" -> "_lessthan_"
    | "?" -> "_questionmark_"
    | "!" -> "_exclamationmark_"
    | "*" -> "_star_"
    | "~" -> "_tilde_"
    | "," -> "_comma_"
    | "@" -> "_at_"
    | "+" -> "_plus_"
    | "-" -> "_minus_"
    | "%" -> "_percent_"
    | "$" -> "_dollar_"
    | "." -> "_dot_"
    | "'" -> "_quote_"
    | "|" -> "_pipe_"
    | ":" -> "_colon_"
    | s -> s;;

  let mfc s = implode (map modify (explode s));;

  let ensure_export_directory thyname =
    let dir = Sys.getenv "HOLPROOFEXPORTDIR" in
    let dirsub = Filename.concat dir "hollight" in
    let dirsubsub = Filename.concat dirsub thyname in
    let mk d = if Sys.file_exists d then () else Unix.mkdir d 509
    in mk dir; mk dirsub; mk dirsubsub; dirsubsub;;


  (****** Proofs ******)

  type proof_info_rec =
      {disk_info: (string * string) option ref;
       status: int ref;
       references: int ref;
       queued: bool ref};;

  type proof_info = Info of proof_info_rec;;

  type proof =
    | Proof of (proof_info * proof_content * (unit -> unit))
  and proof_content =
    | Prefl of term
    | Pbeta of string * hol_type * term
    | Pinstt of proof * (string * hol_type) list
    | Pabs of proof * string * hol_type
    | Pdisch of proof * term
    | Phyp of term
    | Pspec of proof * term
    | Pinst of proof * (string * hol_type * term) list
    | Pgen of proof * string * hol_type
    | Psym of proof
    | Ptrans of proof * proof
    | Pcomb of proof * proof
    | Peqmp of proof * proof
    | Pexists of proof * term * term
    | Pchoose of string * hol_type * proof * proof
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
    | Paxm of string * term
    | Pdef of string * hol_type * term
    | Ptyintro of hol_type * string * hol_type list * string * string * term;;

  let content_of (Proof (_,p,_)) = p;;

  let inc_references (Proof(Info{references=r},_,_) as p) = incr r; p;;

  let mk_proof p = Proof(Info {disk_info = ref None; status = ref 0; references = ref 0; queued = ref false}, p, fun () -> ());;

  let global_ax_counter = let counter = ref 1 in let f = fun () -> (incr counter; !counter - 1) in f;;

  let new_axiom_name n = "ax_"^n^"_"^(string_of_int (global_ax_counter () ));;


  (* corresponds to REFL *)

  let proof_REFL t = mk_proof (Prefl t);;


  (* corresponds to TRANS, with a simple improvment *)

  let proof_TRANS (p,q) =
    match (content_of p, content_of q) with
      | (Prefl _,_) -> q
      | (_, Prefl _) -> p
      | _ -> mk_proof (Ptrans (inc_references p, inc_references q));;


  (* corresponds to MK_COMB -> Pcomb *)

  let proof_MK_COMB (p1,p2) =
    match (content_of p1, content_of p2) with
      | (Prefl tm1, Prefl tm2) -> mk_proof (Prefl (mk_comb (tm1, tm2)))
      | _ ->  mk_proof (Pcomb (inc_references p1, inc_references p2));;


  (* corresponds to ASSUME -> Phyp *)

  let proof_ASSUME t = mk_proof (Phyp t);;


  (* corresponds to EQ_MP, with a simple improvment *)

  let proof_EQ_MP p q =
    match content_of p with
      | Prefl _ -> q
      | _ -> mk_proof (Peqmp(inc_references p, inc_references q));;


  (* corresponds to IMP_ANTISYM_RULE th1 th2
     not a base rule
     used only in the extended mode *)

  (*  A1 |- t1 ==> t2     A2 |- t2 ==> t1 *)
  (* ------------------------------------- IMP_ANTISYM_RULE *)
  (*          A1 u A2 |- t1 <=> t2 *)

  let proof_IMPAS p1 p2 = mk_proof (Pimpas (inc_references p1, inc_references p2));;


  (* corresponds to DISCH
     not a base rule
     used only in the extended mode *)

  (*        A |- t *)
  (* -------------------- DISCH `u` *)
  (*  A - {u} |- u ==> t *)

  let proof_DISCH p t = mk_proof (Pdisch(inc_references p, t));;


  (* corresponds to DEDUCT_ANTISYM_RULE *)
  (* made with IMPAS and DISCH (whereas in HOL-Light IMPAS is made with DAR and UNDISCH...) *)

  (*       A |- p       B |- q *)
  (* ---------------------------------- *)
  (*  (A - {q}) u (B - {p}) |- p <=> q *)

  let proof_DEDUCT_ANTISYM_RULE (p1,t1) (p2,t2) =
    proof_IMPAS (proof_DISCH p1 t2) (proof_DISCH p2 t1);;


  (* BETA is a base rule *)

  let proof_BETA tm =
    try
      let f,_ = dest_comb tm in
      let v,bod = dest_abs f in
      let (x, ty) = dest_var v in
      mk_proof (Pbeta (x, ty, bod))
    with
      | _ -> failwith "proof_BETA"


  (* corresponds to ABS, with a simple improvment *)

  let proof_ABS x p =
    match x with
      | Var(s, ty) ->
          mk_proof (Pabs(inc_references p, s, ty))
      | _ -> failwith "proof_ABS: not a variable";;


  (* corresponds to INST_TYPE -> Pinstt *)

  let proof_INST_TYPE s p =
    mk_proof (Pinstt(inc_references p, List.map (
                       fun (ty1, ty2) -> match ty2 with
                         | Tyvar s -> (s, ty1)
                         | _ -> failwith "proof_INST_TYPE: some redex is not a type variable"
                     ) s));;


  (* corresponds to INST *)

  let proof_INST s p =
    mk_proof (Pinst(inc_references p, List.map (
                      fun (t1, t2) -> match t2 with
                        | Var(s, ty) ->
                            (s, ty, t1)
                        | _ -> failwith "proof_INST: some redex is not a term variable"
                    ) s));;


  (* proof_new_definition is called in Thm.new_basic_definition. This
     latter helps to define basic concepts such as T, AND... (almost
     everything in Bool)... and to define derived rules!! -> Pdef *)

  let proof_new_definition cname ty t =
    mk_proof (Pdef (cname, ty, t));;


  (* proof_new_axiom is called in Thm.new_axiom. This latter transforms
     a term of type bool into a theorem. The main three axioms are
     ETA_AX, SELECT_AX and INFINITY_AX. The other axiom is ax (in
     drule.ml) -> Paxm *)

  let proof_new_axiom axname t = mk_proof (Paxm (axname, t));;


  (* corresponds to CONJ
     not a base rule
     used only in the extended mode *)

  let proof_CONJ p1 p2 = mk_proof (Pconj (inc_references p1, inc_references p2));;


  (* corresponds to CONJUNCT1
     not a base rule
     used only in the extended mode
     also used in Thm.new_basic_definition *)

  let proof_CONJUNCT1 p = mk_proof (Pconjunct1 (inc_references p));;


  (* corresponds to CONJUNCT2
     not a base rule
     used only in the extended mode
     also used in Thm.new_basic_definition *)

  let proof_CONJUNCT2 p = mk_proof (Pconjunct2 (inc_references p));;


  (* used only in Thm.new_basic_definition for the same purpose as for
     CONJUNCTi -> Ptyintro *)

  let proof_new_basic_type_definition tyname (absname, repname) (pt,tt) _ =
    let rty = type_of tt in
    let tyvars = sort (<=) (type_vars_in_term pt) in

    mk_proof(Ptyintro(rty, tyname, tyvars, absname, repname, pt));;


  (* ---- used only in substitute_proof calls ---- *)

  (* corresponds to Bool.SPEC, the !-elimination rule *)

  let proof_SPEC s p = mk_proof (Pspec(inc_references p, s));;


  (* corresponds to Equal.SYM, the symmetry rule *)

  let proof_SYM p = mk_proof (Psym(inc_references p));;


  (* corresponds to Bool.GEN, the !-introduction rule *)

  let proof_GEN p a =
    match a with
      | Var(s, ty) ->
          mk_proof (Pgen(inc_references p, s, ty))
      | _ -> failwith "proof_GEN: not a term variable";;


  (* corresponds to Bool.DISJ1, the \/-left introduction rule *)

  let proof_DISJ1 p a = mk_proof (Pdisj1 (inc_references p, a));;


  (* corresponds to Bool.DISJ2, the \/-right introduction rule *)

  let proof_DISJ2 p a = mk_proof (Pdisj2 (inc_references p, a));;


  (* corresponds to Bool.NOT_INTRO, the following rule: *)
  (*     A |- t ==> F *)
  (*    --------------  NOT_INTRO *)
  (*       A |- ~t *)

  let proof_NOTI p = mk_proof (Pnoti (inc_references p));;


  (* corresponds to Bool.NOT_ELIM, the following rule: *)
  (*       A |- ~t *)
  (*    --------------  NOT_ELIM *)
  (*     A |- t ==> F *)

  let proof_NOTE p = mk_proof (Pnote (inc_references p));;


  (* corresponds to Bool.CONTR, the intuitionistic F-elimination rule: *)
  (*     A |- F *)
  (*    --------  CONTR `t` *)
  (*     A |- t *)

  let proof_CONTR p a = mk_proof (Pcontr (inc_references p, a));;


  (* corresponds to Bool.DISJ_CASES, the \/-elimination rule: *)
  (*     A |- t1 \/ t2     A1 u {t1} |- t      A2 u {t2} |- t *)
  (*    ------------------------------------------------------  DISJ_CASES *)
  (*                     A u A1 u A2 |- t *)

  let proof_DISJCASES p q r =
    mk_proof (Pdisjcases (inc_references p, inc_references q, inc_references r));;


  (* corresponds to Bool.CHOOSE, the ?-elimination rule: *)
  (*     A1 |- ?x. s[x]    A2 |- t *)
  (*    -------------------------------  CHOOSE (`v`,(A1 |- ?x. s)) *)
  (*      A1 u (A2 - {s[v/x]}) |- t *)
  (* Where v is not free in A2 - {s[v/x]} or t. *)

  let proof_CHOOSE a p q =
    let (x,ty) = dest_var a in
    mk_proof (Pchoose (x, ty, inc_references p, inc_references q));;


  (* corresponds to Bool.EXISTS, the ?-introduction rule: *)
  (*     A |- p[u/x] *)
  (*    -------------  EXISTS (`?x. p`,`u`) *)
  (*     A |- ?x. p *)
  (* x is p, y is u *)

  let proof_EXISTS etm y p  =
    let _,x = dest_comb etm in
    mk_proof (Pexists (inc_references p, x, y));;


  (****** Utilities for exportation ******)

  let content_of (Proof (_,x,_)) = x;;


  let disk_info_of (Proof(Info {disk_info=di},_,_)) = !di;;


  let set_disk_info_of (Proof(Info {disk_info=di},_,_)) thyname thmname =
    di := Some (thyname,thmname);;

  let reset_disk_info_of1 ((Proof(Info {disk_info=di}, _, _)) as p) =
    di := None; p;;
  let reset_disk_info_of2 (Proof(Info {disk_info=di}, _, _)) =
    di := None;;


  let references (Proof (Info info,_,_)) = !(info.references);;


  let glob_counter = ref 0;;


  let get_counter () = incr glob_counter; !glob_counter;;


  let get_iname = string_of_int o get_counter;;


  let next_counter () = !glob_counter;;


  let trivial p =
    match (content_of p) with
      | Prefl _ -> true
      | Pbeta _ -> true
      | Paxm _ -> true
      | Phyp _ -> true
      | _ -> false;;


  let do_share p = references p > 1 && not (trivial p);;


  (****** Types and terms modification ******)

  let  idT = Hashtbl.create 17;;
  let defT = Hashtbl.create 17;;

  let  idT_ref = ref 1;;
  let defT_ref = ref 1;;

  let make_idT x =
    try Hashtbl.find idT x with | Not_found -> let n = !idT_ref in incr idT_ref; Hashtbl.add idT x n; n;;

  let make_defT x =
    try Hashtbl.find defT x with | Not_found -> let n = !defT_ref in incr defT_ref; Hashtbl.add defT x n; n;;


  type ntype =
    | Ntvar of int
    | Nbool
    | Nnum
    | Narrow of ntype * ntype
    | Ntdef of int * ntype list;;


  let rec hol_type2ntype = function
    | Tyvar x -> Ntvar (make_idT x)
    | Tyapp (s, _) when s = "bool" -> Nbool
    (* | Tyapp (s, _) when s = "ind" -> Nnum *)
    | Tyapp (s, l) when s = "fun" ->
        (match l with
           | [a;b] -> Narrow (hol_type2ntype a, hol_type2ntype b)
           | _ -> failwith "hol_type2ntype: wrong number of arguments for fun")
    | Tyapp (s, l) -> Ntdef (make_defT s, List.map hol_type2ntype l);;


  let  idV = Hashtbl.create 17;;
  let defV = Hashtbl.create 17;;

  let  idV_ref = ref 1;;
  let defV_ref = ref 1;;

  let make_idV x X =
    try
      fst (Hashtbl.find idV x)
    with | Not_found ->
      let n = !idV_ref in incr idV_ref; Hashtbl.add idV x (n,X); n;;

  let make_defV x X f =
    try let (a,_,_) = (Hashtbl.find defV x) in a with | Not_found -> let n = !defV_ref in incr defV_ref; Hashtbl.add defV x (n,X,f); n;;


  type ncst =
    | Heq of ntype
    | Heps of ntype
    | Hand
    | Hor
    | Hnot
    | Himp
    | Htrue
    | Hfalse
    | Hforall of ntype
    | Hexists of ntype;;


  type nterm =
    | Ndbr of int
    | Nvar of int * ntype
    | Ncst of ncst
    | Ndef of int * ntype
    | Napp of nterm * nterm
    | Nabs of ntype * nterm;;


  let rec ext_var x (ty: ntype) i = function
    | [] -> Nvar (make_idV x ty, ty)
    | (y,typ)::l -> if ((x = y) && (ty = typ)) then Ndbr i else ext_var x ty (i+1) l;;


  let rec term2nterm l = function
    | Var (x, ty) -> ext_var x (hol_type2ntype ty) 0 l
    | Comb (t1, t2) -> Napp (term2nterm l t1, term2nterm l t2)
    | Abs (t1, t2) ->
        (match t1 with
           | Var (x, ty) ->
               let typ = hol_type2ntype ty in
               Nabs (typ, term2nterm ((x,typ)::l) t2)
           | _ -> failwith "term2nterm: first argument of an abstraction is not a variable")
    | Const (s, ty) when s = "=" ->
        (match hol_type2ntype ty with
           | Narrow(a, _) -> Ncst (Heq a)
           | _ -> failwith "term2nterm: constant = must have arrow type")
    | Const (s, ty) when s = "@" ->
        (match hol_type2ntype ty with
           | Narrow(_, a) -> Ncst (Heps a)
           | _ -> failwith "term2nterm: constant @ must have arrow type")
    | Const (s, ty) when s = "/\\" -> Ncst Hand
    | Const (s, ty) when s = "\\/" -> Ncst Hor
    | Const (s, ty) when s = "~" -> Ncst Hnot
    | Const (s, ty) when s = "==>" -> Ncst Himp
    | Const (s, ty) when s = "T" -> Ncst Htrue
    | Const (s, ty) when s = "F" -> Ncst Hfalse
    | Const (s, ty) when s = "_FALSITY_" -> Ncst Hfalse
    | Const (s, ty) when s = "!" ->
        (match hol_type2ntype ty with
           | Narrow(Narrow (a, _), _) -> Ncst (Hforall a)
           | _ -> failwith "term2nterm: constant ! must have arrow type")
    | Const (s, ty) when s = "?" ->
        (match hol_type2ntype ty with
           | Narrow(Narrow (a, _), _) -> Ncst (Hexists a)
           | _ -> failwith "term2nterm: constant ? must have arrow type")
    | Const (s, ty) ->
        let typ = hol_type2ntype ty in
        Ndef(make_defV s typ true, typ);;

  let term2nterm t = term2nterm [] t;;


  (****** Proof exportation ******)

  let rec print_list out str snil scons = function
    | [] -> out snil
    | t::q -> out "("; out scons; out " "; str t; out " "; print_list out str snil scons q; out ")";;


  let print_names out x = out (string_of_int x); out "%positive";;


  let print_type (out: string -> unit) ty =

    let rec print_ntype = function
      | Ntvar x -> out "(TVar "; print_names out x; out ")"
      | Nbool -> out "Bool"
      | Nnum -> out "Num"
      | Narrow(a, b) -> out "("; print_ntype a; out " --> "; print_ntype b; out ")"
      | Ntdef(s, l) -> out "(TDef "; print_names out s; out " "; print_list out print_ntype "Tnil" "Tcons" l; out ")" in

    print_ntype ty;;


  let print_cst out = function
    | Heq ty -> out "(Heq "; print_type out ty; out ")"
    | Heps ty -> out "(Heps "; print_type out ty; out ")"
    | Hand -> out "Hand"
    | Hor -> out "Hor"
    | Hnot -> out "Hnot"
    | Himp -> out "Himp"
    | Htrue -> out "Htrue"
    | Hfalse -> out "Hfalse"
    | Hforall ty -> out "(Hforall "; print_type out ty; out ")"
    | Hexists ty -> out "(Hexists "; print_type out ty; out ")";;


  let print_term out t =

    let rec print_nterm = function
      | Ndbr n -> out "(Dbr "; out (string_of_int n); out ")"
      | Nvar(x, ty) -> out "(Var "; print_names out x; out " "; print_type out ty; out ")"
      | Ncst c -> out "(Cst "; print_cst out c; out ")"
      | Ndef(a, ty) -> out "(Def "; print_names out a; out " "; print_type out ty; out ")"
      | Napp(t1, t2) -> out "(App "; print_nterm t1; out " "; print_nterm t2; out ")"
      | Nabs(ty, t) -> out "(Abs "; print_type out ty; out " "; print_nterm t; out ")" in

    print_nterm t;;


  (* Exportation *)

  let total = ref 0;;

  type nproof_content =
    | Nprefl of nterm
    | Npbeta of int * ntype * nterm
    | Npinstt of nproof_content * (int * ntype) list
    | Npabs of nproof_content * int * ntype
    | Npdisch of nproof_content * nterm
    | Nphyp of nterm
    | Npspec of nproof_content * nterm
    | Npinst of nproof_content * (int * ntype * nterm) list
    | Npgen of nproof_content * int * ntype
    | Npsym of nproof_content
    | Nptrans of nproof_content * nproof_content
    | Npcomb of nproof_content * nproof_content
    | Npeqmp of nproof_content * nproof_content
    | Npexists of nproof_content * nterm * nterm
    | Npchoose of int * ntype * nproof_content * nproof_content
    | Npconj of nproof_content * nproof_content
    | Npconjunct1 of nproof_content
    | Npconjunct2 of nproof_content
    | Npdisj1 of nproof_content * nterm
    | Npdisj2 of nproof_content * nterm
    | Npdisjcases of nproof_content * nproof_content * nproof_content
    | Npnoti of nproof_content
    | Npnote of nproof_content
    | Npcontr of nproof_content * nterm
    | Npimpas of nproof_content * nproof_content
    | Npaxm of string * nterm
    | Npdef of int * ntype * nterm
    | Nptyintro of ntype * ntype * int * int * nterm
    | Nfact of string;;


  let the_types = Hashtbl.create 17;;
  let count_types = ref (-1);;

  let share_types out ty =

    let rec share_types ty =
      try Hashtbl.find the_types ty with
        | Not_found ->
            incr count_types;
            let name = THEORY_NAME^"_type_"^(string_of_int !count_types) in
            (match ty with
               | Narrow(a,b) ->
                   let n1 = share_types a in
                   let n2 = share_types b in
                   out "\nDefinition "; out name; out " := "; out n1; out " --> "; out n2; out "."
               | Ntdef(i,l) ->
                   let names = List.map share_types l in
                   out "\nDefinition "; out name; out " := TDef "; print_names out i; out " "; print_list out out "Tnil" "Tcons" names; out "."
               | t -> out "\nDefinition "; out name; out " := "; print_type out t; out ".");
            Hashtbl.add the_types ty name;
            name in

    share_types ty;;


  let the_terms = Hashtbl.create 17;;
  let count_terms = ref (-1);;

  let share_csts out out_types name = function
    | Heq a ->
        let n = share_types out_types a in
        out "\nDefinition "; out name; out " := Cst (Heq "; out n; out ")."
    | Heps a ->
        let n = share_types out_types a in
        out "\nDefinition "; out name; out " := Cst (Heps "; out n; out ")."
    | Hand -> out "\nDefinition "; out name; out " := Cst Hand."
    | Hor -> out "\nDefinition "; out name; out " := Cst Hor."
    | Hnot -> out "\nDefinition "; out name; out " := Cst Hnot."
    | Himp -> out "\nDefinition "; out name; out " := Cst Himp."
    | Htrue -> out "\nDefinition "; out name; out " := Cst Htrue."
    | Hfalse -> out "\nDefinition "; out name; out " := Cst Hfalse."
    | Hforall a ->
        let n = share_types out_types a in
        out "\nDefinition "; out name; out " := Cst (Hforall "; out n; out ")."
    | Hexists a ->
        let n = share_types out_types a in
        out "\nDefinition "; out name; out " := Cst (Hexists "; out n; out ")."

  let share_terms out out_types tm =

    let rec share_terms tm =
      try Hashtbl.find the_terms tm with
        | Not_found ->
            incr count_terms;
            let name = THEORY_NAME^"_term_"^(string_of_int !count_terms) in
            (match tm with
               | Napp(t1,t2) ->
                   let n1 = share_terms t1 in
                   let n2 = share_terms t2 in
                   out "\nDefinition "; out name; out " := App "; out n1; out " "; out n2; out "."
               | Nabs(ty,t) ->
                   let n = share_terms t in
                   let ny = share_types out_types ty in
                   out "\nDefinition "; out name; out " := Abs "; out ny; out " "; out n; out "."
               | Nvar(i,ty) ->
                   let ny = share_types out_types ty in
                   out "\nDefinition "; out name; out " := Var "; print_names out i; out " "; out ny; out "."
               | Ndef(i,ty) ->
                   let ny = share_types out_types ty in
                   out "\nDefinition "; out name; out " := Def "; print_names out i; out " "; out ny; out "."
               | Ncst c -> share_csts out out_types name c
               | t -> out "\nDefinition "; out name; out " := "; print_term out t; out ".");
            Hashtbl.add the_terms tm name;
            name in

    share_terms tm;;


  let export_proof out share_type share_term p =

    let rec wp = function
      | Nprefl tm ->
          let tm2 = share_term tm in
          out "(Prefl "; out tm2; out ")"
      | Npbeta (n, ty, tm) ->
          let tm2 = share_term tm in
          let ty2 = share_type ty in
          out "(Pbeta "; print_names out n; out " "; out ty2; out " "; out tm2; out ")"
      | Npinstt(p,lambda) ->
          out "(Pinstt ";
          wp p;
          out " "; print_list out (fun (s, ty) ->
                                     let ty2 = share_type ty in
                                     out "("; print_names out s; out ", "; out ty2; out ")") "nil" "cons" lambda; out ")"
      | Npabs(p,x,ty) ->
          let ty2 = share_type ty in
          out "(Pabs ";
          wp p;
          out " "; print_names out x;
          out " "; out ty2; out ")"
      | Npdisch(p,tm) ->
          let tm2 = share_term tm in
          out "(Pdisch ";
          wp p;
          out " "; out tm2; out ")"
      | Nphyp tm ->
          let tm2 = share_term tm in
          out "(Phyp "; out tm2; out ")"
      | Npaxm(_, _) -> ()
      | Npdef(_, _, _) -> ()
      | Nptyintro(_, _, _, _, _) -> ()
      | Npspec(p,t) ->
          let t2 = share_term t in
          out "(Pspec ";
          wp p;
          out " "; out t2; out ")"
      | Npinst(p,theta) ->
          out "(Pinst ";
          wp p;
          out " "; print_list out (fun (s, ty, t) ->
                                     let t2 = share_term t in
                                     let ty2 = share_type ty in
                                     out "("; print_names out s; out ", "; out ty2; out ", "; out t2; out ")") "nil" "cons" theta; out ")"
      | Npgen(p,x,ty) ->
          let ty2 = share_type ty in
          out "(Pgen ";
          wp p;
          out " "; print_names out x; out " "; out ty2; out ")"
      | Npsym p ->
          out "(Psym ";
          wp p;
          out ")"
      |  Nptrans(p1,p2) ->
           out "(Ptrans ";
           wp p1;
           out " ";
           wp p2;
           out ")"
      | Npcomb(p1,p2) ->
          out "(Pcomb ";
          wp p1;
          out " ";
          wp p2;
          out ")"
      | Npeqmp(p1,p2) ->
          out "(Peqmp ";
          wp p1;
          out " ";
          wp p2;
          out ")"
      | Npexists(p,ex,w) ->
          let ex2 = share_term ex in
          let w2 = share_term w in
          out "(Pexists ";
          wp p;
          out " "; out ex2; out " "; out w2; out ")"
      | Npchoose(x,ty,p1,p2) ->
          let ty2 = share_type ty in
          out "(Pchoose "; print_names out x; out " "; out ty2; out " ";
          wp p1;
          out " ";
          wp p2;
          out ")"
      | Npconj(p1,p2) ->
          out "(Pconj ";
          wp p1;
          out " ";
          wp p2;
          out ")"
      | Npimpas(p1,p2) ->
          out "(Pimpas ";
          wp p1;
          out " ";
          wp p2;
          out ")"
      | Npconjunct1 p ->
          out "(Pconjunct1 ";
          wp p;
          out ")"
      |  Npconjunct2 p ->
           out "(Pconjunct2 ";
           wp p;
           out ")"
      | Npdisj1(p,tm) ->
          let tm2 = share_term tm in
          out "(Pdisj1 ";
          wp p;
          out " "; out tm2; out ")"
      | Npdisj2(p,tm) ->
          let tm2 = share_term tm in
          out "(Pdisj2 ";
          wp p;
          out " "; out tm2; out ")"
      | Npdisjcases(p1,p2,p3) ->
          out "(Pdisjcases ";
          wp p1;
          out " ";
          wp p2;
          out " ";
          wp p3;
          out ")"
      | Npnoti p ->
          out "(Pnoti ";
          wp p;
          out ")"
      | Npnote p ->
          out "(Pnote ";
          wp p;
          out ")"
      | Npcontr(p,tm) ->
          let tm2 = share_term tm in
          out "(Pcontr ";
          wp p;
          out " "; out tm2; out ")"
      | Nfact(thm) -> out "(Poracle "; out thm; out "_def)" in

    wp p;;


  let export_ht out share_term h t thmname =
    out "\n\n\nDefinition "; out thmname; out "_h := ";
    (match h with
       | [] -> out "hyp_empty"
       | _ -> print_list out (fun tm ->
                                let tm2 = share_term tm in
                                out tm2) "nil" "cons" h);
    out ".\n\nDefinition "; out thmname; out "_t := ";
    let t2 = share_term t in
    out t2; out ".";;


  let export_lemma out share_type share_term p thmname =
    out "\n\nLemma "; out thmname; out "_lemma : deriv "; out thmname; out "_h "; out thmname;
    out "_t.\nProof.\n  vm_cast_no_check (proof2deriv_correct "; export_proof out share_type share_term p; out ").\nQed.";;


  let export_lemma_def out tree thmname =
    out "\n\nLemma "; out thmname; out "_lemma : deriv "; out thmname; out "_h "; out thmname;
    out "_t.\nProof.\n  vm_cast_no_check (proof2deriv_correct "; out tree; out ").\nQed.";;


  let export_sig out thmname =
    out "\n\nDefinition "; out thmname; out "_def := my_exist "; out thmname; out "_lemma.";;


  let export_def out thmname =
    out "\n\nParameter "; out thmname; out "_lemma : deriv "; out thmname; out "_h "; out thmname; out "_t.";;


  let export_tdef out thmname =
    out "\n\nParameter "; out thmname; out "_lemma : deriv "; out thmname; out "_h "; out thmname; out "_t.";;


  let export_axiom out thmname =
    out "\n\nAxiom "; out thmname; out "_lemma : deriv "; out thmname; out "_h "; out thmname; out "_t.";;


  (* Transforming a proof into a derivation *)

  let rec opt_nth n l =
    match (n, l) with
      | 0, (x::_) -> Some x
      | 0, [] -> None
      | p, (_::l) -> opt_nth (p-1) l
      | _, _ -> None;;


  let type_cst = function
    | Heq a -> Narrow(a, Narrow(a, Nbool))
    | Heps a -> Narrow(Narrow(a, Nbool), a)
    | Hand -> Narrow(Nbool, Narrow(Nbool, Nbool))
    | Hor -> Narrow(Nbool, Narrow(Nbool, Nbool))
    | Hnot -> Narrow(Nbool, Nbool)
    | Himp -> Narrow(Nbool, Narrow(Nbool, Nbool))
    | Htrue -> Nbool
    | Hfalse -> Nbool
    | Hforall a -> Narrow(Narrow(a, Nbool), Nbool)
    | Hexists a -> Narrow(Narrow(a, Nbool), Nbool);;


  let rec infer g = function
    | Ndbr n -> opt_nth n g
    | Nvar (_, a) -> Some a
    | Ncst c -> Some (type_cst c)
    | Ndef (_, a) -> Some a
    | Napp (t1, t2) ->
        (match infer g t1, infer g t2 with
           | Some (Narrow (u1, u2)), Some v -> if u1 = v then Some u2 else None
           | _, _ -> None)
    | Nabs (a, u) ->
        (match infer (a::g) u with
           | Some b -> Some (Narrow (a, b))
           | None -> None);;


  let rec close_aux t x a i =
    match t with
      | Ndbr n -> Ndbr (if n < i then n else n+1)
      | Nvar (y, b) -> if ((x = y) && (a = b)) then Ndbr i else Nvar (y, b)
      | Napp (t1, t2) -> Napp (close_aux t1 x a i, close_aux t2 x a i)
      | Nabs (b, u) -> Nabs(b, close_aux u x a (i+1))
      | u -> u;;

  let close t x a = close_aux t x a 0;;


  let rec subst_idt_type_aux x = function
    | [] -> Ntvar x
    | (y,a)::q -> if x = y then a else subst_idt_type_aux x q;;

  let rec subst_idt_type t s =
    match t with
      | Ntvar x -> subst_idt_type_aux x s
      | Ntdef (a, l) -> Ntdef (a, subst_idt_list_type l s)
      | Narrow (a, b) -> Narrow (subst_idt_type a s, subst_idt_type b s)
      | u -> u

  and subst_idt_list_type l s = List.map (fun t -> subst_idt_type t s) l;;

  let rec subst_idt t s =
    match t with
      | Nvar (x, y)      -> Nvar (x, subst_idt_type y s)
      | Ncst (Heq a)     -> Ncst (Heq (subst_idt_type a s))
      | Ncst (Heps a)    -> Ncst (Heps (subst_idt_type a s))
      | Ncst (Hforall a) -> Ncst (Hforall (subst_idt_type a s))
      | Ncst (Hexists a) -> Ncst (Hexists(subst_idt_type a s))
      | Ndef (c, d)      -> Ndef (c, subst_idt_type d s)
      | Napp (t1, t2)    -> Napp (subst_idt t1 s, subst_idt t2 s)
      | Nabs (a, t)      -> Nabs (subst_idt_type a s, subst_idt t s)
      | u                -> u;;

  let subst_idt_context g s = List.map (fun a -> subst_idt_type a s) g;;

  let rec subst_idv_aux x y s =
      match s with
        | [] -> Nvar (x, y)
        | (z, t, u)::q -> if ((x = z) && (y = t)) then u else subst_idv_aux x y q;;

  let rec subst_idv t s =
    match t with
      | Nvar (x, y) -> subst_idv_aux x y s
      | Napp (t1, t2) -> Napp (subst_idv t1 s, subst_idv t2 s)
      | Nabs (a, t) -> Nabs (a, subst_idv t s)
      | u -> u;;

  let rec wf_substitution_idv = function
    | [] -> true
    | (_,y,t)::q ->
        match infer [] t with
          | Some z -> if (y = z) then wf_substitution_idv q else false
          | None -> false;;


  let rec is_not_free x y = function
    | Nvar (z, t) -> (x != z) or (not (y = t))
    | Napp (t1, t2) -> (is_not_free x y t1) && (is_not_free x y t2)
    | Nabs (_, u) -> is_not_free x y u
    | _ -> true;;


  let rec lift_term u i j =
    match u with
      | Ndbr n -> if n >= i then Ndbr (j + n) else Ndbr n
      | Napp (u1, u2) -> Napp (lift_term u1 i j, lift_term u2 i j)
      | Nabs (a, t) -> Nabs (a, lift_term t (i+1) j)
      | u -> u;;

  let rec subst_db t n u =
    match t with
      | Ndbr i -> if i < n then Ndbr i else if i = n then u else Ndbr (i-1)
      | Napp (t1, t2) -> Napp (subst_db t1 n u, subst_db t2 n u)
      | Nabs (a, t) -> Nabs (a, subst_db t (n+1) (lift_term u 0 1))
      | u -> u;;

  let nopen t u = subst_db t 0 u;;


  let heq a t u = Napp (Napp (Ncst (Heq a), t), u);;
  let hequiv t u = Napp (Napp (Ncst (Heq Nbool), t), u);;
  let himp t u = Napp (Napp (Ncst Himp, t), u);;
  let hand t u = Napp (Napp (Ncst Hand, t), u);;
  let hor t u = Napp (Napp (Ncst Hor, t), u);;
  let hnot t = Napp (Ncst Hnot, t);;
  let htrue = Ncst Htrue;;
  let hfalse = Ncst Hfalse;;
  let hforall a p = Napp (Ncst (Hforall a), Nabs (a, p));;
  let hexists a p = Napp (Ncst (Hexists a), Nabs (a, p));;


  let hyp_empty = [];;

  let rec hyp_remove e = function
    | [] -> []
    | t::q -> if (e = t) then q else t::(hyp_remove e q);;

  let rec hyp_add e = function
    | [] -> [e]
    | t::q -> if (e = t) then t::q else t::(hyp_add e q);;

  let hyp_union l m = List.fold_left (fun n e -> hyp_add e n) m l;;

  let hyp_map f l = List.fold_left (fun m e -> hyp_add (f e) m) [] l;;

  let hyp_singl e = [e];;

  let rec hyp_is_not_free x y = function
    | [] -> true
    | t::q -> (is_not_free x y t) && (hyp_is_not_free x y q);;

  let hyp_subst_idt h s = hyp_map (fun t -> subst_idt t s) h;;

  let hyp_subst_idv h s = hyp_map (fun t -> subst_idv t s) h;;


  let rec eq_type a b = match (a,b) with
    | Ntvar i, Ntvar j -> i = j
    | Nbool, Nbool -> true
    | Nnum, Nnum -> true
    | Narrow(a1, b1), Narrow(a2, b2) -> (eq_type a1 a2) && (eq_type b1 b2)
    | Ntdef(i,l), Ntdef(j,m) -> (i = j) && (eq_list_type l m)
    | _, _ -> false

  and eq_list_type l m = match (l,m) with
    | [], [] -> true
    | t1::q1, t2::q2 -> (eq_type t1 t2) && (eq_list_type q1 q2)
    | _, _ -> false;;


  let eq_cst a b = match (a,b) with
    | Heq a, Heq b -> eq_type a b
    | Heps a, Heps b -> eq_type a b
    | Hand, Hand -> true
    | Hor, Hor -> true
    | Hnot, Hnot -> true
    | Himp, Himp -> true
    | Htrue, Htrue -> true
    | Hfalse, Hfalse -> true
    | Hforall a, Hforall b -> eq_type a b
    | Hexists a, Hexists b -> eq_type a b
    | _, _ -> false;;


  let rec eq_term a b = match (a,b) with
    | Ndbr i, Ndbr j -> i = j
    | Nvar(i,a), Nvar(j,b) -> (i = j) && (eq_type a b)
    | Ncst c, Ncst d -> eq_cst c d
    | Ndef(i,a), Ndef(j,b) -> (i = j) && (eq_type a b)
    | Napp(a1,b1), Napp(a2,b2) -> (eq_term a1 a2) && (eq_term b1 b2)
    | Nabs(t1,a1), Nabs(t2,a2) -> (eq_type t1 t2) && (eq_term a1 a2)
    | _, _ -> false;;


  let derivs = Hashtbl.create 17;;


  let rec proof2deriv = function

    | Nprefl t ->
        (match infer [] t with
           | Some a -> Some (hyp_empty, heq a t t)
           | None -> (print_string "Nprefl\n"); None)

    | Npbeta (x, y, t) ->
        (match infer [] t with
           | Some a -> Some (hyp_empty,
                             heq a (Napp (Nabs (y, close t x y), Nvar (x, y))) t)
           | None -> (print_string "Npbeta\n"); None)

    | Npinstt (q, l) ->
        (match proof2deriv q with
           | Some (h,v) -> Some (hyp_subst_idt h l, subst_idt v l)
           | None -> (print_string "Npinstt\n"); None)

    | Npabs (q, x, y) ->
        (match proof2deriv q with
           | Some (h, t) ->
               (match t with
                  | Napp (Napp (Ncst (Heq a), t1), t2) ->
                      if hyp_is_not_free x y h then
                        Some (h, heq (Narrow (y, a)) (Nabs (y, close t1 x y)) (Nabs (y, close t2 x y)))
                      else ((print_string "Npabs\n"); None)
                  | _ -> (print_string "Npabs\n"); None)
           | None -> (print_string "Npabs\n"); None)

    | Npdisch (q, t) ->
        (match proof2deriv q, infer [] t with
           | Some (h, u), Some Nbool -> Some (hyp_remove t h, himp t u)
           | _, _ -> (print_string "Npdisch\n"); None)

    | Nphyp t ->
        (match infer [] t with
           | Some Nbool -> Some (hyp_singl t, t)
           | _ -> (print_string "Nphyp\n"); None)

    | Npspec (q, t) ->
        (match proof2deriv q, infer [] t with
           | Some (h, u), Some a ->
               (match u with
                  | Napp (Ncst (Hforall b), Nabs (c, v)) ->
                      if ((eq_type a b) && (eq_type b c)) then
                        Some (h, nopen v t)
                      else ((print_string "Npspec\n"); None)
                  | _ -> (print_string "Npspec\n"); None)
           | _, _ -> (print_string "Npspec\n"); None)

    | Npinst (q, l) ->
        (match proof2deriv q, wf_substitution_idv l with
           | Some (h, v), true -> Some (hyp_subst_idv h l, subst_idv v l)
           | _, _ -> (print_string "Npinst\n"); None)

    | Npgen (q, x, y) ->
        (match proof2deriv q with
           | Some (h, t) ->
               if hyp_is_not_free x y h then
                 Some (h, hforall y (close t x y))
               else ((print_string "Npgen\n"); None)
           | None -> (print_string "Npgen\n"); None)

    | Npsym q ->
        (match proof2deriv q with
           | Some (h, t) ->
               (match t with
                  | Napp (Napp (Ncst (Heq a), u), v) -> Some (h, heq a v u)
                  | _ -> (print_string "Npsym\n"); None)
           | None -> (print_string "Npsym\n"); None)

    | Nptrans (q1, q2) ->
        (match proof2deriv q1, proof2deriv q2 with
           | Some (h1, t1), Some (h2, t2) ->
               (match t1, t2 with
                  | Napp (Napp (Ncst (Heq a), u1), u2),
                    Napp (Napp (Ncst (Heq b), v2), v3) ->
                      if ((eq_type a b) && (eq_term u2 v2)) then
                        Some (hyp_union h1 h2, heq a u1 v3)
                      else ((print_string "Nptrans\n"); None)
                  | _, _ -> (print_string "Nptrans\n"); None)
           | _, _ -> (print_string "Nptrans\n"); None)

    | Npcomb (q1, q2) ->
        (match proof2deriv q1, proof2deriv q2 with
           | Some (h1, t1), Some (h2, t2) ->
               (match t1, t2 with
                  | Napp (Napp (Ncst (Heq (Narrow (a, b))), f), g),
                    Napp (Napp (Ncst (Heq c), u), v) ->
                      if (eq_type a c) then
                        Some (hyp_union h1 h2, heq b (Napp (f, u)) (Napp (g, v)))
                      else ((print_string "Npcomb\n"); None)
                  | _, _ -> (print_string "Npcomb\n"); None)
           | _, _ -> (print_string "Npcomb\n"); None)

    | Npeqmp (q1, q2) ->
        (match proof2deriv q1, proof2deriv q2 with
           | Some (h1, t1), Some (h2, t2) ->
               (match t1 with
                  | Napp (Napp (Ncst (Heq Nbool), a), b) ->
                      if (eq_term a t2) then
                        Some (hyp_union h1 h2, b)
                      else ((print_string "Npeqmp\n"); None)
                  | _ -> (print_string "Npeqmp\n"); None)
           | _, _ -> (print_string "Npeqmp\n"); None)

    | Npexists (q, b, t) ->
        (match proof2deriv q, b, infer [] t with
           | Some (h, u), Nabs (bb, a), Some aa ->
               if ((eq_type aa bb) && (eq_term (nopen a t) u)) then
                 Some (h, hexists aa a)
               else ((print_string "Npexists\n"); None)
           | _, _, _ -> (print_string "Npexists\n"); None)

    | Npchoose (v, aa, q1, q2) ->
        (match proof2deriv q1, proof2deriv q2 with
           | Some (h1, t), Some (h2, c) ->
               (match t with
                  | Napp (Ncst (Hexists bb), Nabs (cc, a)) ->
                      let s = hyp_remove (nopen a (Nvar (v, aa))) h2 in
                      if ((eq_type aa bb) && (eq_type bb cc) && (hyp_is_not_free v aa s) && (is_not_free v aa c)
                          && (is_not_free v aa a)) then
                        Some (hyp_union h1 s, c)
                      else ((print_string "Npchoose\n"); None)
                  | _ -> (print_string "Npchoose\n"); None)
           | _, _ -> (print_string "Npchoose\n"); None)

    | Npconj (q1, q2) ->
        (match proof2deriv q1, proof2deriv q2 with
           | Some (h1, a), Some (h2, b) ->
               Some (hyp_union h1 h2, hand a b)
           | _, _ -> (print_string "Npconj\n"); None)

    | Npconjunct1 q ->
        (match proof2deriv q with
           | Some (h, v) ->
               (match v with
                  | Napp (Napp (Ncst Hand, t), u) ->
                      Some (h, t)
                  | _ -> (print_string "Npconjunct1\n"); None)
           | _ -> (print_string "Npconjunct1\n"); None)

    | Npconjunct2 q ->
        (match proof2deriv q with
           | Some (h, v) ->
               (match v with
                  | Napp (Napp (Ncst Hand, t), u) ->
                      Some (h, u)
                  | _ -> (print_string "Npconjunct2\n"); None)
           | _ -> (print_string "Npconjunct2\n"); None)

    | Npdisj1 (q, b) ->
        (match proof2deriv q, infer [] b with
           | Some (h, a), Some Nbool -> Some (h, hor a b)
           | _, _ -> (print_string "Npdisj1\n"); None)

    | Npdisj2 (q, a) ->
        (match proof2deriv q, infer [] a with
           | Some (h, b), Some Nbool -> Some (h, hor a b)
           | _, _ -> (print_string "Npdisj1\n"); None)

    | Npdisjcases (q1, q2, q3) ->
        (match proof2deriv q1, proof2deriv q2, proof2deriv q3 with
           | Some (h1, t), Some (h2, c1), Some (h3, c2) ->
               (match t with
                  | Napp (Napp (Ncst Hor, a), b) ->
                      if (eq_term c1 c2) then
                        Some (hyp_union h1 (hyp_union (hyp_remove a h2) (hyp_remove b h3)), c1)
                      else ((print_string "Npdisjcases\n"); None)
                  | _ -> (print_string "Npdisjcases\n"); None)
           | _, _, _ -> (print_string "Npisjcases\n"); None)

    | Npnoti q ->
        (match proof2deriv q with
           | Some (h, t) ->
               (match t with
                  | Napp (Napp (Ncst Himp, a), Ncst Hfalse) -> Some (h, hnot a)
                  | _ -> (print_string "Npnoti\n"); None)
           | _ -> (print_string "Npnoti\n"); None)

    | Npnote q ->
        (match proof2deriv q with
           | Some (h, t) ->
               (match t with
                  | Napp (Ncst Hnot, a) -> Some (h, himp a hfalse)
                  | _ -> (print_string "Npnote\n"); None)
           | _ -> (print_string "Npnote\n"); None)

    | Npcontr (q, a) ->
        (match proof2deriv q, infer [] a with
           | Some (h, t), Some Nbool ->
               (match t with
                  | Ncst Hfalse -> Some (hyp_remove (hnot a) h, a)
                  | _ -> (print_string "Npcontr\n"); None)
           | _, _ -> (print_string "Npcontr\n"); None)

    | Npimpas (q1, q2) ->
        (match proof2deriv q1, proof2deriv q2 with
           | Some (h1, t), Some (h2, u) ->
               (match t, u with
                  | Napp (Napp (Ncst Himp, a1), b1),
                    Napp (Napp (Ncst Himp, b2), a2) ->
                      if ((eq_term a1 a2) && (eq_term b1 b2)) then
                        Some (hyp_union h1 h2, hequiv b1 a1)
                      else ((print_string ("Npimpas1; 1: "^(string_of_bool (eq_term a1 a2))^"; 2: "^(string_of_bool (eq_term b1 b2))^"\n"));
                            let out = print_string in
                            print_term out a1; out "\n"; print_term out a2; out "\n"; print_term out b1; out "\n"; print_term out b2; out "\n"; None)
                  | _, _ -> (print_string "Npimpas2\n"); None)
           | _, _ -> (print_string "Npimpas3\n"); None)

    | Nfact thm ->
        (try Some (Hashtbl.find derivs thm) with
           | Not_found -> (print_string ("Nfact "^thm^"\n")); None)

    | Npdef (i, a, t) -> Some (hyp_empty, heq a (Ndef (i, a)) t)

    | Npaxm (_, t) -> Some (hyp_empty, t)

    | Nptyintro (rty, aty, mk_name, dest_name, p) ->

        let mk_type = Narrow(rty, aty) in
        let dest_type = Narrow(aty, rty) in

        let a_name = make_idV "a" aty in
        let a = Nvar(a_name, aty) in
        let r_name = make_idV "r" rty in
        let r = Nvar(r_name, rty) in

        Some (hyp_empty, hand (heq aty (Napp (Ndef (mk_name, mk_type), Napp (Ndef (dest_name, dest_type), a))) a)
                (hequiv (Napp (p, r)) (heq rty (Napp (Ndef (dest_name, dest_type), Napp (Ndef (mk_name, mk_type), r))) r)));;


  (* Dealing with dependencies *)

  let rec make_dependencies_aux dep_graph proof_of_thm = function
    | [] -> ()
    | (thmname, p, c_opt)::il ->

        incr total;

        let wdi thm =
          Depgraph.Dep.add_dep dep_graph thm thmname;
          Nfact thm in

        let write_proof p il =

          let rec share_info_of p il =
            match (disk_info_of p) with
              | Some (thyname,thmname) -> Some(thyname,thmname,il)
              | None ->
                  if do_share p then
                    let name = THEORY_NAME^"_"^(get_iname ()) in
                    set_disk_info_of p THEORY_NAME name;
                    Depgraph.Dep.add_thm dep_graph name;
                    Some(THEORY_NAME,name,(name,p,None)::il)
                  else
                    None

          and wp' il = function
            | Prefl tm -> Nprefl (term2nterm tm), il
            | Pbeta(x, ty, tm) ->
                let typ = hol_type2ntype ty in
                Npbeta(make_idV x typ , typ, term2nterm tm), il
            | Pinstt(p,lambda) ->
                let p', res = wp il p in
                Npinstt(p', List.map (
                          fun (s,ty) -> (make_idT s, hol_type2ntype ty)
                        ) lambda), res
            | Pabs(p,x,ty) ->
                let p', res = wp il p in
                let typ = hol_type2ntype ty in
                Npabs(p',make_idV x typ,typ), res
            | Pdisch(p,tm) ->
                let p', res = wp il p in
                Npdisch(p', term2nterm tm), res
            | Phyp tm -> Nphyp (term2nterm tm), il
            | Paxm(th,tm) -> Npaxm(th, term2nterm tm), il
            | Pdef(name,ty,tm) ->
                let typ = hol_type2ntype ty in
                Npdef(make_defV name typ true, typ, term2nterm tm), il
            | Ptyintro(rty2, tyname, tyvars, absname, repname, pt) ->
                let rty = hol_type2ntype rty2 in
                let new_name = make_defT tyname in

                let ntyvars = List.map hol_type2ntype tyvars in
                let aty = Ntdef(new_name, ntyvars) in

                let mk_name = make_defV absname (Narrow(rty, aty)) false in
                let dest_name = make_defV repname (Narrow(aty, rty)) false in

                Nptyintro(rty, aty, mk_name, dest_name, term2nterm pt), il
            | Pspec(p,t) ->
                let p', res = wp il p in
                Npspec(p', term2nterm t), res
            | Pinst(p,theta) ->
                let p', res = wp il p in
                Npinst(p', List.map (
                         fun (s,ty,te) ->
                           let typ = hol_type2ntype ty in
                           (make_idV s typ, typ, term2nterm te)
                       ) theta), res
            | Pgen(p,x,ty) ->
                let p', res = wp il p in
                let typ = hol_type2ntype ty in
                Npgen(p', make_idV x typ, typ), res
            | Psym p ->
                let p', res = wp il p in
                Npsym p', res
            | Ptrans(p1,p2) ->
                let p1', il' = wp il p1 in
                let p2', res = wp il' p2 in
                Nptrans(p1', p2'), res
            | Pcomb(p1,p2) ->
                let p1', il' = wp il p1 in
                let p2', res = wp il' p2 in
                Npcomb(p1', p2'), res
            | Peqmp(p1,p2) ->
                let p1', il' = wp il p1 in
                let p2', res = wp il' p2 in
                Npeqmp(p1', p2'), res
            | Pexists(p,ex,w) ->
                let p', res = wp il p in
                Npexists(p', term2nterm ex, term2nterm w), res
            | Pchoose(x,ty,p1,p2) ->
                let p1', il' = wp il p1 in
                let p2', res = wp il' p2 in
                let typ = hol_type2ntype ty in
                Npchoose(make_idV x typ, typ, p1', p2'), res
            | Pconj(p1,p2) ->
                let p1', il' = wp il p1 in
                let p2', res = wp il' p2 in
                Npconj(p1', p2'), res
            | Pimpas(p1,p2) ->
                let p1', il' = wp il p1 in
                let p2', res = wp il' p2 in
                Npimpas(p1', p2'), res
            | Pconjunct1 p ->
                let p', res = wp il p in
                Npconjunct1 p', res
            |  Pconjunct2 p ->
                 let p', res = wp il p in
                 Npconjunct2 p', res
            | Pdisj1(p,tm) ->
                let p', res = wp il p in
                Npdisj1(p', term2nterm tm), res
            | Pdisj2(p,tm) ->
                let p', res = wp il p in
                Npdisj2(p', term2nterm tm), res
            | Pdisjcases(p1,p2,p3) ->
                let p1', il' = wp il p1 in
                let p2', il'' = wp il' p2 in
                let p3', res = wp il'' p3 in
                Npdisjcases(p1', p2', p3'), res
            | Pnoti p ->
                let p', res = wp il p in
                Npnoti p', res
            | Pnote p ->
                let p', res = wp il p in
                Npnote p', res
            | Pcontr(p,tm) ->
                let p', res = wp il p in
                Npcontr(p', term2nterm tm), res

          and wp il p =
            match share_info_of p il with
              | Some(_, thmname, il') -> wdi thmname, il'
              | None -> wp' il (content_of p) in

          match disk_info_of p with
            | Some(_, thmname') -> if thmname' = thmname then wp' il (content_of p) else (wdi thmname', il)
            | None -> wp' il (content_of p) in

        let p', il = write_proof p il in
        set_disk_info_of p THEORY_NAME thmname;
        Hashtbl.add proof_of_thm thmname p';
        make_dependencies_aux dep_graph proof_of_thm il;;


  let make_dependencies out out_share out_sharet new_file count_thms path ((thmname, pr, _) as p) =

    let dep_graph = Depgraph.Dep.create () in
    let proof_of_thm = Hashtbl.create (references pr) in
    Depgraph.Dep.add_thm dep_graph thmname;

    make_dependencies_aux dep_graph proof_of_thm [p];

    let share_type ty = share_types out_sharet ty in
    let share_term ty = share_terms out_share out_sharet ty in


    if thmname = (THEORY_NAME^"_DEF_T") then (
      match content_of pr with
        | Pdef (_, _, t) ->
            let tm = hequiv htrue (term2nterm t) in
            Hashtbl.add derivs thmname (hyp_empty, tm);
            export_ht out share_term hyp_empty tm thmname;
            export_lemma_def out "DEF_T" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__slash__backslash_") then (
      match content_of pr with
        | Pdef (_, _, t) ->
            let tm = heq (Narrow (Nbool, Narrow (Nbool, Nbool))) (Ncst Hand) (term2nterm t) in
            Hashtbl.add derivs thmname (hyp_empty, tm);
            export_ht out share_term hyp_empty tm thmname;
            export_lemma_def out "DEF_AND" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__equal__equal__greaterthan_") then (
      match content_of pr with
        | Pdef (_, _, t) ->
            let tm = heq (Narrow (Nbool, Narrow (Nbool, Nbool))) (Ncst Himp) (term2nterm t) in
            Hashtbl.add derivs thmname (hyp_empty, tm);
            export_ht out share_term hyp_empty tm thmname;
            export_lemma_def out "DEF_IMP" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__exclamationmark_") then (
      match content_of pr with
        | Pdef (_, a, t) ->
            let a2 = hol_type2ntype a in
            (match a2 with
               | Narrow (Narrow (b, _), _) ->
                   let tm = heq a2 (Ncst (Hforall b)) (term2nterm t) in
                   Hashtbl.add derivs thmname (hyp_empty, tm);
                   export_ht out share_term hyp_empty tm thmname;
                   export_lemma_def out "DEF_FORALL" thmname;
                   export_sig out thmname
               | _ -> ())
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__questionmark_") then (
      match content_of pr with
        | Pdef (_, a, t) ->
            let a2 = hol_type2ntype a in
            (match a2 with
               | Narrow (Narrow (b, _), _) ->
                   let tm = heq a2 (Ncst (Hexists b)) (term2nterm t) in
                   Hashtbl.add derivs thmname (hyp_empty, tm);
                   export_ht out share_term hyp_empty tm thmname;
                   export_lemma_def out "DEF_EXISTS" thmname;
                   export_sig out thmname
               | _ -> ())
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__backslash__slash_") then (
      match content_of pr with
        | Pdef (_, _, t) ->
            let tm = heq (Narrow (Nbool, Narrow (Nbool, Nbool))) (Ncst Hor) (term2nterm t) in
            Hashtbl.add derivs thmname (hyp_empty, tm);
            export_ht out share_term hyp_empty tm thmname;
            export_lemma_def out "DEF_OR" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF_F") then (
      match content_of pr with
        | Pdef (_, _, t) ->
            let tm = hequiv (Ncst Hfalse) (term2nterm t) in
            Hashtbl.add derivs thmname (hyp_empty, tm);
            export_ht out share_term hyp_empty tm thmname;
            export_lemma_def out "DEF_F" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__tilde_") then (
      match content_of pr with
        | Pdef(_, _, t) ->
            let tm = heq (Narrow (Nbool, Nbool)) (Ncst Hnot) (term2nterm t) in
            Hashtbl.add derivs thmname (hyp_empty, tm);
            export_ht out share_term hyp_empty tm thmname;
            export_lemma_def out "DEF_NOT" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_DEF__FALSITY_") then (
      let tm = heq Nbool (Ncst Hfalse) (Ncst Hfalse) in
      Hashtbl.add derivs thmname (hyp_empty, tm);
      export_ht out share_term hyp_empty tm thmname;
      export_lemma_def out "(Prefl (Cst Hfalse))" thmname;
      export_sig out thmname
    ) else if thmname = (THEORY_NAME^"_ax__1") then (
      match content_of pr with
        | Paxm (_, tm) ->
            let tm2 = term2nterm tm in
            Hashtbl.add derivs thmname (hyp_empty, tm2);
            export_ht out share_term hyp_empty tm2 thmname;
            export_lemma_def out "ETA_AX" thmname;
            export_sig out thmname
        | _ -> ()
    ) else if thmname = (THEORY_NAME^"_ax__2") then (
      match content_of pr with
        | Paxm (_, tm) ->
            let tm2 = term2nterm tm in
            Hashtbl.add derivs thmname (hyp_empty, tm2);
            export_ht out share_term hyp_empty tm2 thmname;
            export_lemma_def out "SELECT_AX" thmname;
            export_sig out thmname
        | _ -> ()

    ) else (

      Depgraph.Dep_top.iter_top (
        fun thm ->
          incr count_thms;
          if !count_thms = 1000 then (count_thms := 0; new_file ());
          (try
             let p = Hashtbl.find proof_of_thm thm in
             (match proof2deriv p with
                | Some (h, t) ->
                    Hashtbl.add derivs thm (h, t);
                    export_ht out share_term h t thm;
                    (match p with
                       | Npdef _ -> export_def out thm
                       | Nptyintro _ -> export_tdef out thm
                       | Npaxm _ -> export_axiom out thm
                       | _ -> export_lemma out share_type share_term p thm);
                    export_sig out thm
                | None -> failwith ("Erreur make_dependencies "^thm^" de "^thmname^": no derivation associated to the proof\n"))
           with | Not_found -> failwith ("Erreur make_dependencies "^thm^": proof_of_thm not found\n"));
      ) dep_graph
    );
;;


  let the_proof_database = ref ([]:(string*proof*(term option)) list);;

  Random.self_init;;

  let rec search_proof_name n db =
    match db with [] -> n | ((m, _, _)::db') -> if n=m then n^"_"^(string_of_int (Random.int 1073741823)) else search_proof_name n db'

  let save_proof name p c_opt =
    let name' = search_proof_name name (!the_proof_database) in
    the_proof_database := (name', p, c_opt)::(!the_proof_database);;

  let proof_database () = !the_proof_database;;


  (* Utilities to define Coq interpretation functions *)

  let ut = Hashtbl.create 17;;

  let ask_ut () =
    try (
      let filein = open_in "interpretation.txt" in
      let line = ref 0 in

      try
        while true do
          incr line;
          let s1 = input_line filein in
          incr line;
          let s2 = input_line filein in
          Hashtbl.add ut s1 s2
        done
      with
        | End_of_file -> close_in filein
        | _ -> failwith ("Error line "^(string_of_int !line)^".")
    ) with | Sys_error _ -> ()
  ;;

  let tc_regexp = Str.regexp "\?[0-9]*";;

  let make_tc_parameter out x n =
    if Str.string_match tc_regexp x 0 then (
      let i = Str.match_end () in
      if i <> String.length x then (
        out "\nParameter "; out THEORY_NAME; out "_idT_"; out (mfc x); out " : Type.\nParameter "; out THEORY_NAME; out "_idT_inhab_"; out (mfc x);
        out " : "; out THEORY_NAME; out "_idT_"; out (mfc x); out "."
      )
    ) else (
      out "\nParameter "; out THEORY_NAME; out "_idT_"; out (mfc x); out " : Type.\nParameter "; out THEORY_NAME; out "_idT_inhab_"; out (mfc x);
      out " : "; out THEORY_NAME; out "_idT_"; out (mfc x); out "."
    );;

  let make_tc_list out x n =
    if Str.string_match tc_regexp x 0 then (
      let i = Str.match_end () in
      if i <> String.length x then (
        out "\n("; out (string_of_int n); out ", mkTT "; out THEORY_NAME; out "_idT_inhab_"; out (mfc x); out ")::"
      )
    ) else (
      out "\n("; out (string_of_int n); out ", mkTT "; out THEORY_NAME; out "_idT_inhab_"; out (mfc x); out ")::"
    );;


  let defT_ut = Hashtbl.create 17;;

  let make_tdt_parameter out x _ =
    try (
      let y = Hashtbl.find ut x in
      Hashtbl.add defT_ut x y
    ) with | Not_found -> (
      out "\nParameter "; out THEORY_NAME; out "_defT_"; out (mfc x); out " : Type.";
      out "\nParameter "; out THEORY_NAME; out "_defT_inhab_"; out (mfc x); out " : "; out THEORY_NAME; out "_defT_"; out (mfc x); out ".\n";
      Hashtbl.add defT_ut x ("fun _ => mkTT "^THEORY_NAME^"_defT_inhab_"^(mfc x))
    );;

  let make_tdt_list out x n =
    try (
      let s = Hashtbl.find defT_ut x in
      out "\n("; out (string_of_int n); out ", "; out s; out ")::";
    ) with | Not_found -> (
      out "\n("; out (string_of_int n); out ", fun _ => mkTT tt)::"
    );;


  let se_regexp = Str.regexp "_[0-9]*";;

  let make_se_parameter out x (_,ty) =
    if Str.string_match se_regexp x 0 then (
      let i = Str.match_end () in
      if i <> String.length x then (
        out "\nParameter "; out THEORY_NAME; out "_idV_"; out (mfc x); out " : tr_type tc tdt "; print_type out ty; out "."
      )
    ) else (
      out "\nParameter "; out THEORY_NAME; out "_idV_"; out (mfc x); out " : tr_type tc tdt "; print_type out ty; out "."
    );;

  let make_se_list out x (n,ty) =
    if Str.string_match se_regexp x 0 then (
      let i = Str.match_end () in
      if i <> String.length x then (
        out "\n("; print_names out n; out ", existT (fun (t: type) => tr_type tc tdt t) "; print_type out ty; out " "; out THEORY_NAME; out "_idV_"; out (mfc x); out ")::"
      )
    ) else (
      out "\n("; print_names out n; out ", existT (fun (t: type) => tr_type tc tdt t) "; print_type out ty; out " "; out THEORY_NAME; out "_idV_"; out (mfc x); out ")::"
    );;


  let defV_ut = Hashtbl.create 17;;

  let make_sdt_parameter out x (_,ty,_) =
    if ((x <> "T") && (x <> "/\\") && (x <> "==>") && (x <> "!") && (x <> "?") && (x <> "\\/") && (x <> "F") && (x <> "~") && (x <> "_FALSITY_")) then (
      try (
        let y = Hashtbl.find ut x in
        Hashtbl.add defV_ut x y
      ) with | Not_found -> (
        out "\nParameter "; out THEORY_NAME; out "_defV_"; out (mfc x); out " : tr_type tc tdt "; print_type out ty; out "."
      )
    );;

  let make_sdt_list out x (n,ty,_) =
    try (
      let s = Hashtbl.find defV_ut x in
      out "\n("; print_names out n; out ", existT (fun (t: type) => tr_type tc tdt t) "; print_type out ty; out " ("; out s; out "))::"
    ) with | Not_found -> (
      if ((x <> "T") && (x <> "/\\") && (x <> "==>") && (x <> "!") && (x <> "?") && (x <> "\\/") && (x <> "F") && (x <> "~") && (x <> "_FALSITY_")) then (
        out "\n("; print_names out n; out ", existT (fun (t: type) => tr_type tc tdt t) "; print_type out ty; out " "; out THEORY_NAME; out "_defV_"; out (mfc x); out ")::"
      )
    );;


  (* Main function: list of proofs exportation *)

  let export_list thmname_list =

    total := 0;

    let path = ensure_export_directory THEORY_NAME in


    let rec proof_of_thm acc acc2 = function
      | [] -> acc, acc2
      | (s,p,c)::q ->
          if List.mem s thmname_list then
            proof_of_thm ((THEORY_NAME^"_"^(mfc s), reset_disk_info_of1 p, c)::acc) (acc2+1) q
          else match content_of p with
            | Paxm _ | Pdef _ | Ptyintro _ -> proof_of_thm ((THEORY_NAME^"_"^(mfc s), reset_disk_info_of1 p, c)::acc) (acc2+1) q
            | _ -> proof_of_thm acc acc2 q in

    let l, total_thms = proof_of_thm [] 0 (proof_database ()) in


    let count_thms = ref 0 in
    let count_files = ref 1 in

    (* Main file *)

    let file = ref (open_out (Filename.concat path (THEORY_NAME^"_1.v"))) in
    let count_file = ref 0 in
    let out s = (output_string !file s; incr count_file; if !count_file = 1000 then (count_file := 0; flush !file)) in
    out "(*** This file has been automatically generated from HOL-Light source files. ***)\n\nRequire Export List NArith.\nRequire Export hol deriv proof.\n\n";

    (* Temporary file *)

    let (file_temp_name, file_temp_aux) = Filename.open_temp_file (THEORY_NAME^"_") ".v" in
    let file_temp = ref file_temp_aux in
    let count_file_temp = ref 0 in
    let out_temp s = (output_string !file_temp s; incr count_file_temp; if !count_file_temp = 1000 then (count_file_temp := 0; flush !file_temp)) in


    let move_temp () =
      (try
         close_out !file_temp
       with | Sys_error s -> raise (Sys_error ("move_temp1: "^s)));

      (try
         let buf = open_in file_temp_name in
         (try
            while true do
              out "\n";
              let l = input_line buf in
              out l
            done
          with | End_of_file -> close_in buf)
       with | Sys_error s -> raise (Sys_error ("move_temp3: "^s))) in


    (* New file *)

    let new_file () =

      move_temp ();
      file_temp := open_out file_temp_name;

      incr count_files;
      close_out !file;
      file := open_out (Filename.concat path (THEORY_NAME^"_"^(string_of_int !count_files)^".v"));
      out "(*** This file has been automatically generated from HOL-Light source files. ***)\n\nRequire Export "; out THEORY_NAME; out "_"; out (string_of_int (!count_files-1)); out ".\n\n" in


    (* Coq files generation *)

    let date1 = Unix.time () in
    List.iter (make_dependencies out_temp out out new_file count_thms path) l;
    let date2 = Unix.time () in


    move_temp (); close_out !file;


    (* Makefile *)

    let make = open_out (Filename.concat path "Makefile") in
    let out = output_string make in
    out "# This file has been automatically generated from HOL-Light source files.\n\nCOQ=ssrcoq\nFLAGS=-dont-load-proofs -dump-glob /dev/null -compile\n\nSRC=";
    for i = 1 to !count_files do
      out " "; out THEORY_NAME; out "_"; out (string_of_int i); out ".v";
    done;
    out "\nOBJ=$(SRC:.v=.vo)\nGLOB=$(SRC:.v=.glob)\n\n\nall: $(OBJ)\n\n\n%.vo: %.v\n\t$(COQ) $(FLAGS) $(^:.v=)\n\n\nclean:\n\trm -f $(OBJ) $(GLOB) *~";
    close_out make;


    (* Interpretation *)

    let interp = open_out (Filename.concat path "interpretation.v") in
    let out = output_string interp in
    out "(*** This file has been automatically generated from HOL-Light source files. ***)\n\nRequire Import ssreflect eqtype ssrnat ssrbool.\nRequire Import List NArith ZArith.ZOdiv_def.\nRequire Import hol cast typing translation axioms.\n\nOpen Local Scope positive_scope.\n\n";

    ask_ut ();

    (* tc *)
    Hashtbl.iter (make_tc_parameter out) idT;
    out "\n\nDefinition tc_list :=";
    Hashtbl.iter (make_tc_list out) idT;
    out "\nnil.\n\nDefinition tc := list_tc2tc tc_list.\n\n";

    (* tdt *)
    Hashtbl.iter (make_tdt_parameter out) defT;
    out "\n\nDefinition tdt_list : list_tdt :=";
    Hashtbl.iter (make_tdt_list out) defT;
    out "\nnil.\n\nDefinition tdt := list_tdt2tdt tdt_list.\n\n";

    (* se *)
    Hashtbl.iter (make_se_parameter out) idV;
    out "\n\nDefinition se_list :=";
    Hashtbl.iter (make_se_list out) idV;
    out "\nnil.\n\nDefinition se := list_se2se se_list.\n\n";

    (* sdt *)
    Hashtbl.iter (make_sdt_parameter out) defV;
    out "\n\nDefinition sdt_list :=";
    Hashtbl.iter (make_sdt_list out) defV;
    out "\nnil.\n\nDefinition sdt := list_sdt2sdt sdt_list.";

    close_out interp;


    print_string "Generated "; print_int !total; print_string " facts for "; print_int total_thms; print_string " theorems.\n";
    print_string "Exportation duration: "; print_float (date2 -. date1); print_string "s.\n"
  ;;


  (* Main function: all proofs exportation *)

  let export_saved_proofs () = export_list (List.map (fun (s,_,_) -> s) (proof_database ()));;


  (* Main function: one proof exportation *)

  let export_one_proof name = export_list [name];;


end;;


include Proofobjects;;
