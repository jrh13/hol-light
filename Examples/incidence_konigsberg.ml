(* Koenigsberg permits loops, so active edges can have one or two endpoints. *)

needs "Library/incidence.ml";;
needs "100/konigsberg.ml";;

let KONIGSBERG_GRAPH_IMP_INCIDENCE = prove
 (`!edge_set:E->bool. !vertex_set:V->bool. !incidence:E->V->bool.
      graph (edge_set,vertex_set,incidence)
      ==> incidence_closed edge_set vertex_set incidence /\
          (!e. edge_set e
               ==> incidence e HAS_SIZE 1 \/ incidence e HAS_SIZE 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[incidence_closed] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
      [`(edge_set,vertex_set,incidence):
         (E->bool)#(V->bool)#(E->V->bool)`; `e:E`; `v:V`]
      TERMINI_IN_VERTICES) THEN
    ASM_REWRITE_TAC[edges; vertices; termini; IN];
    X_GEN_TAC `e:E` THEN DISCH_TAC THEN
    UNDISCH_TAC
      `graph ((edge_set,vertex_set,incidence):
         (E->bool)#(V->bool)#(E->V->bool))` THEN
    REWRITE_TAC[graph; edges; vertices; termini] THEN
    DISCH_THEN(MP_TAC o SPEC `e:E`) THEN
    ASM_REWRITE_TAC[IN] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:V`
      (X_CHOOSE_THEN `b:V` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `a:V = b` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC
      [HAS_SIZE; CARD_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC]);;
