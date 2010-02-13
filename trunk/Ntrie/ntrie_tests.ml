(* -*- holl -*- *)

(* ========================================================================= *)
(* Conversions for ntries.                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* NTRIE_IN_CONV                                                             *)
(* ------------------------------------------------------------------------- *)

NTRIE_IN_CONV `2 IN NTRIE NEMPTY`;;
NTRIE_IN_CONV `0 IN NTRIE NZERO`;;
NTRIE_IN_CONV `0 IN NTRIE (NNODE NZERO NZERO)`;;
NTRIE_IN_CONV `0 IN NTRIE (NNODE NZERO NZERO)`;;
NTRIE_IN_CONV `1 IN NTRIE NZERO`;;
NTRIE_IN_CONV `1 IN NTRIE (NNODE NEMPTY NZERO)`;;
NTRIE_IN_CONV `1 IN NTRIE (NNODE NZERO NEMPTY)`;;
NTRIE_IN_CONV `1 IN NTRIE (NNODE NZERO NZERO)`;;
NTRIE_IN_CONV `2 IN NTRIE (NNODE NZERO NZERO)`;;
NTRIE_IN_CONV `3 IN NTRIE (NNODE NZERO NZERO)`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_EQ_CONV                                                             *)
(* ------------------------------------------------------------------------- *)

NTRIE_EQ_CONV `NTRIE NEMPTY = NTRIE NZERO`;;
NTRIE_EQ_CONV `NTRIE NZERO = NTRIE NZERO`;;
NTRIE_EQ_CONV `NTRIE (NNODE NZERO NEMPTY) = NTRIE NZERO`;;
NTRIE_EQ_CONV `NTRIE (NNODE NEMPTY NZERO) = NTRIE NZERO`;;
NTRIE_EQ_CONV `NTRIE (NNODE NZERO NEMPTY) = NTRIE (NNODE NZERO NZERO)`;;
NTRIE_EQ_CONV `NTRIE (NNODE NEMPTY NZERO) = NTRIE (NNODE NZERO NZERO)`;;
NTRIE_EQ_CONV `NTRIE (NNODE NEMPTY NEMPTY) = NTRIE NEMPTY`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_SUBSET_CONV                                                         *)
(* ------------------------------------------------------------------------- *)

NTRIE_SUBSET_CONV `NTRIE NZERO SUBSET NTRIE NEMPTY`;;
NTRIE_SUBSET_CONV `NTRIE NEMPTY SUBSET NTRIE NZERO`;;
NTRIE_SUBSET_CONV
  `NTRIE (NNODE NZERO NEMPTY) SUBSET NTRIE (NNODE NZERO NZERO)`;;
NTRIE_SUBSET_CONV
  `NTRIE (NNODE NEMPTY NZERO) SUBSET NTRIE (NNODE NZERO NZERO)`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_DISJOINT_CONV                                                       *)
(* ------------------------------------------------------------------------- *)

NTRIE_DISJOINT_CONV `DISJOINT (NTRIE NEMPTY) (NTRIE NEMPTY)`;;
NTRIE_DISJOINT_CONV
  `DISJOINT (NTRIE (NNODE NEMPTY NZERO)) (NTRIE (NNODE NZERO NEMPTY))`;;
NTRIE_DISJOINT_CONV
  `DISJOINT (NTRIE (NNODE NEMPTY NZERO)) (NTRIE (NNODE NEMPTY NZERO))`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_SING_CONV                                                           *)
(* ------------------------------------------------------------------------- *)

NTRIE_SING_CONV `{10}`;;
NTRIE_SING_CONV `{1000}`;;
NTRIE_SING_CONV `{100000}`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_INSERT_CONV                                                         *)
(* ------------------------------------------------------------------------- *)

NTRIE_INSERT_CONV `2 INSERT NTRIE NEMPTY`;;
NTRIE_INSERT_CONV `0 INSERT NTRIE NZERO`;;
NTRIE_INSERT_CONV `NUMERAL (BIT1 _0) INSERT NTRIE NZERO`;;
NTRIE_INSERT_CONV `NUMERAL (BIT0 _0) INSERT NTRIE (NNODE NZERO NZERO)`;;
NTRIE_INSERT_CONV `NUMERAL _0 INSERT NTRIE (NNODE NZERO NZERO)`;;
NTRIE_INSERT_CONV `NUMERAL (BIT1 _0) INSERT NTRIE (NNODE NZERO NZERO)`;;
NTRIE_INSERT_CONV `NUMERAL (BIT0 _0) INSERT NTRIE NZERO`;;
NTRIE_INSERT_CONV `NUMERAL (BIT0 (BIT1 (BIT1 _0))) INSERT NTRIE NZERO`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_UNION_CONV                                                          *)
(* ------------------------------------------------------------------------- *)

NTRIE_UNION_CONV `NTRIE NEMPTY UNION NTRIE NEMPTY`;;
NTRIE_UNION_CONV `NTRIE NEMPTY UNION NTRIE NZERO`;;
NTRIE_UNION_CONV `NTRIE (NNODE NZERO NZERO) UNION NTRIE NZERO`;;
NTRIE_UNION_CONV `NTRIE (NNODE NEMPTY NZERO) UNION NTRIE NZERO`;;
NTRIE_UNION_CONV `NTRIE (NNODE NZERO NEMPTY) UNION NTRIE NZERO`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_INTER_CONV                                                          *)
(* ------------------------------------------------------------------------- *)

NTRIE_INTER_CONV `NTRIE NEMPTY INTER NTRIE NEMPTY`;;
NTRIE_INTER_CONV `NTRIE NEMPTY INTER NTRIE NZERO`;;
NTRIE_INTER_CONV `NTRIE (NNODE NZERO NZERO) INTER NTRIE NZERO`;;
NTRIE_INTER_CONV `NTRIE (NNODE NEMPTY NZERO) INTER NTRIE NZERO`;;
NTRIE_INTER_CONV `NTRIE (NNODE NZERO NEMPTY) INTER NTRIE NZERO`;;
NTRIE_INTER_CONV
  `NTRIE (NNODE NEMPTY NEMPTY) INTER NTRIE (NNODE NEMPTY NEMPTY)`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_DELETE_CONV                                                         *)
(* ------------------------------------------------------------------------- *)

NTRIE_DELETE_CONV `NTRIE NEMPTY DELETE 0`;;
NTRIE_DELETE_CONV `NTRIE NZERO DELETE 0`;;
NTRIE_DELETE_CONV `NTRIE (NNODE NZERO NEMPTY) DELETE 0`;;
NTRIE_DELETE_CONV `NTRIE (NNODE NEMPTY NZERO) DELETE 0`;;
NTRIE_DELETE_CONV `NTRIE (NNODE NEMPTY NZERO) DELETE 1`;;
NTRIE_DELETE_CONV `NTRIE (NNODE NZERO NEMPTY) DELETE 1`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_DIFF_CONV                                                           *)
(* ------------------------------------------------------------------------- *)

NTRIE_DIFF_CONV `NTRIE NEMPTY DIFF NTRIE NZERO`;;
NTRIE_DIFF_CONV `NTRIE NZERO DIFF NTRIE NZERO`;;
NTRIE_DIFF_CONV `NTRIE (NNODE NZERO NEMPTY) DIFF NTRIE (NNODE NZERO NEMPTY)`;;
NTRIE_DIFF_CONV `NTRIE (NNODE NEMPTY NZERO) DIFF NTRIE (NNODE NZERO NEMPTY)`;;
NTRIE_DIFF_CONV `NTRIE (NNODE NZERO NZERO) DIFF NTRIE (NNODE NEMPTY NZERO)`;;
NTRIE_DIFF_CONV `NTRIE (NNODE NZERO NZERO) DIFF NTRIE (NNODE NZERO NEMPTY)`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_IMAGE_CONV                                                          *)
(* ------------------------------------------------------------------------- *)

NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE NEMPTY)`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE NZERO)`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE (NNODE NZERO NEMPTY))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE (NNODE NZERO NZERO))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE (NNODE NEMPTY NZERO))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE (NNODE NEMPTY NEMPTY))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE ((+) 2) (NTRIE (NNODE (NNODE NEMPTY NZERO) NEMPTY))`;;

NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE NEMPTY)`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE NZERO)`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE (NNODE NZERO NEMPTY))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE (NNODE NZERO NZERO))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE (NNODE NEMPTY NZERO))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE (NNODE NEMPTY NEMPTY))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE (NNODE (NNODE NEMPTY NZERO) NEMPTY))`;;
NTRIE_IMAGE_CONV NUM_ADD_CONV `IMAGE (\n. n + 2) (NTRIE (NNODE NEMPTY (NNODE NEMPTY NZERO)))`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_DECODE                                                              *)
(* ------------------------------------------------------------------------- *)

NTRIE_DECODE_CONV `NTRIE NEMPTY`;;
NTRIE_DECODE_CONV `NTRIE NZERO`;;
NTRIE_DECODE_CONV `NTRIE (NNODE NZERO NEMPTY)`;;
NTRIE_DECODE_CONV `NTRIE (NNODE NZERO NZERO)`;;
NTRIE_DECODE_CONV `NTRIE (NNODE NEMPTY NZERO)`;;
NTRIE_DECODE_CONV `NTRIE (NNODE NEMPTY NEMPTY)`;;
NTRIE_DECODE_CONV `NTRIE (NNODE (NNODE NEMPTY NZERO) NEMPTY)`;;

(* ------------------------------------------------------------------------- *)
(* NTRIE_ENCODE                                                              *)
(* ------------------------------------------------------------------------- *)

NTRIE_ENCODE_CONV `{}:num->bool`;;
NTRIE_ENCODE_CONV `{1,2,3}`;;
ONCE_DEPTH_CONV NTRIE_ENCODE_CONV `{1,2,3} UNION {3,4,5}`;;

(* ------------------------------------------------------------------------- *)
(* Final hack-together.                                                      *)
(* ------------------------------------------------------------------------- *)

NTRIE_COMPUTE NTRIE_REDUCE_CONV `{1,2,3} UNION ({3,4} UNION {6,7} UNION {1,7})`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{1,2,3} INTER ({3,4} UNION {6,7} UNION {1,7})`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{1,2,3} DIFF ({3,4} UNION {6,7} UNION {1,7})`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{1,2,3} DIFF ({3,4} UNION {6,7} INTER {1,7})`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `3 IN {1,2,3} INTER ({3,4} UNION {6,7} UNION {1,7})`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `11 IN {1,2,3} INTER ({3,4} UNION {6,7} UNION {1,7})`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3} = {3,2,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3,2} = {3,2,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3,2} = {3,2,1,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3,2} DELETE 2 = {3,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3} SUBSET {3,2,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3,7} SUBSET {3,2,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3,2} SUBSET {3,2,1,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3} PSUBSET {3,2,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `{5,2,3} PSUBSET {3,2,0,5}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `DISJOINT {12,3,2,1} {3,2,7,9}`;;
NTRIE_COMPUTE NTRIE_REDUCE_CONV `DISJOINT {12,3,1} {2,7,9}`;;
