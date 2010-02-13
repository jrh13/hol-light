(* ========================================================================= *)
(* Impossibility of Eulerian path for bridges of Koenigsberg.                *)
(* ========================================================================= *)

let edges = new_definition
  `edges(E:E->bool,V:V->bool,Ter:E->V->bool) = E`;;

let vertices = new_definition
  `vertices(E:E->bool,V:V->bool,Ter:E->V->bool) = V`;;

let termini = new_definition
  `termini(E:E->bool,V:V->bool,Ter:E->V->bool) = Ter`;;

(* ------------------------------------------------------------------------- *)
(* Definition of an undirected graph.                                        *)
(* ------------------------------------------------------------------------- *)

let graph = new_definition
 `graph G <=>
        !e. e IN edges(G)
            ==> ?a b. a IN vertices(G) /\ b IN vertices(G) /\
                      termini G e = {a,b}`;;

let TERMINI_IN_VERTICES = prove
 (`!G e v. graph G /\ e IN edges(G) /\ v IN termini G e ==> v IN vertices G`,
  REWRITE_TAC[graph; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Connection in a graph.                                                    *)
(* ------------------------------------------------------------------------- *)

let connects = new_definition
 `connects G e (a,b) <=> termini G e = {a,b}`;;

(* ------------------------------------------------------------------------- *)
(* Delete an edge in a graph.                                                *)
(* ------------------------------------------------------------------------- *)

let delete_edge = new_definition
 `delete_edge e (E,V,Ter) = (E DELETE e,V,Ter)`;;

let DELETE_EDGE_CLAUSES = prove
 (`(!G. edges(delete_edge e G) = (edges G) DELETE e) /\
   (!G. vertices(delete_edge e G) = vertices G) /\
   (!G. termini(delete_edge e G) = termini G)`,
  REWRITE_TAC[FORALL_PAIR_THM; delete_edge; edges; vertices; termini]);;

let GRAPH_DELETE_EDGE = prove
 (`!G e. graph G ==> graph(delete_edge e G)`,
  REWRITE_TAC[graph; DELETE_EDGE_CLAUSES; IN_DELETE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local finiteness: set of edges with given endpoint is finite.             *)
(* ------------------------------------------------------------------------- *)

let locally_finite = new_definition
 `locally_finite G <=>
     !v. v IN vertices(G) ==> FINITE {e | e IN edges G /\ v IN termini G e}`;;

(* ------------------------------------------------------------------------- *)
(* Degree of a vertex.                                                       *)
(* ------------------------------------------------------------------------- *)

let localdegree = new_definition
 `localdegree G v e =
        if termini G e = {v} then 2
        else if v IN termini G e then 1
        else 0`;;

let degree = new_definition
 `degree G v = nsum {e | e IN edges G /\ v IN termini G e} (localdegree G v)`;;

let DEGREE_DELETE_EDGE = prove
 (`!G e:E v:V.
        graph G /\ locally_finite G /\ e IN edges(G)
        ==> degree G v =
                if termini G e = {v} then degree (delete_edge e G) v + 2
                else if v IN termini G e then degree (delete_edge e G) v + 1
                else degree (delete_edge e G) v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[degree; DELETE_EDGE_CLAUSES; IN_DELETE] THEN
  SUBGOAL_THEN
   `{e:E | e IN edges G /\ (v:V) IN termini G e} =
        if v IN termini G e
        then e INSERT {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
        else {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(v:V) IN termini G (e:E)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    COND_CASES_TAC THENL [ASM_MESON_TAC[IN_SING; EXTENSION]; ALL_TAC] THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; localdegree] THEN
    REWRITE_TAC[DELETE_EDGE_CLAUSES]] THEN
  SUBGOAL_THEN
   `FINITE {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}`
   (fun th -> SIMP_TAC[NSUM_CLAUSES; th])
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:E | e IN edges G /\ (v:V) IN termini G e}` THEN
    SIMP_TAC[IN_ELIM_THM; SUBSET] THEN
    ASM_MESON_TAC[locally_finite; TERMINI_IN_VERTICES];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[localdegree] THEN
  SUBGOAL_THEN
   `nsum {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}
         (localdegree (delete_edge e G) v) =
    nsum {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
         (localdegree G v)`
  SUBST1_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[localdegree; DELETE_EDGE_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Definition of Eulerian path.                                              *)
(* ------------------------------------------------------------------------- *)

let eulerian_RULES,eulerian_INDUCT,eulerian_CASES = new_inductive_definition
 `(!G a. a IN vertices G /\ edges G = {} ==> eulerian G [] (a,a)) /\
  (!G a b c e es. e IN edges(G) /\ connects G e (a,b) /\
                  eulerian (delete_edge e G) es (b,c)
                  ==> eulerian G (CONS e es) (a,c))`;;

let EULERIAN_FINITE = prove
 (`!G es ab. eulerian G es ab ==> FINITE (edges G)`,
  MATCH_MP_TAC eulerian_INDUCT THEN
  SIMP_TAC[DELETE_EDGE_CLAUSES; FINITE_DELETE; FINITE_RULES]);;

(* ------------------------------------------------------------------------- *)
(* The main result.                                                          *)
(* ------------------------------------------------------------------------- *)

let EULERIAN_ODD_LEMMA = prove
 (`!G:(E->bool)#(V->bool)#(E->V->bool) es ab.
        eulerian G es ab
        ==> graph G
            ==> FINITE(edges G) /\
                !v. v IN vertices G
                    ==> (ODD(degree G v) <=>
                         ~(FST ab = SND ab) /\ (v = FST ab \/ v = SND ab))`,
  MATCH_MP_TAC eulerian_INDUCT THEN CONJ_TAC THENL
   [SIMP_TAC[degree; NOT_IN_EMPTY; SET_RULE `{x | F} = {}`] THEN
    SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[GRAPH_DELETE_EDGE; FINITE_DELETE; DELETE_EDGE_CLAUSES] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[GRAPH_DELETE_EDGE] THEN STRIP_TAC THEN
  X_GEN_TAC `v:V` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(E->bool)#(V->bool)#(E->V->bool)`; `e:E`; `v:V`]
                DEGREE_DELETE_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[locally_finite] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `edges(G:(E->bool)#(V->bool)#(E->V->bool))` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G:(E->bool)#(V->bool)#(E->V->bool)`; `e:E`]
         TERMINI_IN_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connects]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `b:V = a` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SET_RULE `{a,a} = {v} <=> v = a`] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SET_RULE `{a,b} = {v} <=> a = b /\ a = v`] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH] THEN ASM_MESON_TAC[]);;

let EULERIAN_ODD = prove
 (`!G es a b.
        graph G /\ eulerian G es (a,b)
        ==> !v. v IN vertices G
                ==> (ODD(degree G v) <=> ~(a = b) /\ (v = a \/ v = b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP EULERIAN_ODD_LEMMA) THEN
  ASM_SIMP_TAC[FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* Now the actual Koenigsberg configuration.                                 *)
(* ------------------------------------------------------------------------- *)

let KOENIGSBERG = prove
 (`!G. vertices(G) = {0,1,2,3} /\
       edges(G) = {10,20,30,40,50,60,70} /\
       termini G (10) = {0,1} /\
       termini G (20) = {0,2} /\
       termini G (30) = {0,3} /\
       termini G (40) = {1,2} /\
       termini G (50) = {1,2} /\
       termini G (60) = {2,3} /\
       termini G (70) = {2,3}
       ==> ~(?es a b. eulerian G es (a,b))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num->bool)#(num->bool)#(num->num->bool)` EULERIAN_ODD) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[graph] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE
     `{a,b} = {x,y} <=> a = x /\ b = y \/ a = y /\ b = x`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  ASM_REWRITE_TAC[degree; edges] THEN
  SIMP_TAC[TAUT `a IN s /\ k IN t <=> ~(a IN s ==> ~(k IN t))`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P(x)} = a INSERT {x | P(x)}`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  ASM_REWRITE_TAC[localdegree; IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[SET_RULE `{a,b} = {x} <=> x = a /\ a = b`] THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
   MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH] THEN ARITH_TAC);;

(******

Maybe for completeness I should show the contrary: existence of Eulerian
circuit/walk if we do have the right properties, assuming the graph is
connected; cf:

http://math.arizona.edu/~lagatta/class/fa05/m105/graphtheorynotes.pdf

 *****)
