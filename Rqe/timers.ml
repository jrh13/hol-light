let testform_timer = ref 0.0;;
let combine_testforms_timer = ref 0.0;;

let condense_timer = ref 0.0;;

let inferisign_timer = ref 0.0;;

let matinsert_timer = ref 0.0;;

let inferpsign_timer = ref 0.0;;

let remove_column1_timer = ref 0.0;;
let add_infinities_timer = ref 0.0;;
let remove_infinities_timer = ref 0.0;;

let pdivides_timer = ref 0.0;;

let duplicate_columns_timer = ref 0.0;;
let unmonicize_mat_timer = ref 0.0;;
let swap_head_col_timer = ref 0.0;;
let replace_pol_timer = ref 0.0;;
let unfactor_mat_timer = ref 0.0;;

let reset_timers() =

  testform_timer := 0.0;
  combine_testforms_timer := 0.0;

  condense_timer := 0.0;

  inferisign_timer := 0.0;

  matinsert_timer := 0.0;

  inferpsign_timer := 0.0;

  remove_column1_timer := 0.0;
  add_infinities_timer := 0.0;
  remove_infinities_timer := 0.0;

  pdivides_timer := 0.0;

  duplicate_columns_timer := 0.0;
  unmonicize_mat_timer := 0.0;
  swap_head_col_timer := 0.0;
  replace_pol_timer := 0.0;
  unfactor_mat_timer := 0.0;

;;


let print_timers() =
  print_string "\n----------TIMERS---------\n\n";

  print_string "TESTFORM: ";
  print_float !testform_timer;
  print_string "\n";

  print_string "COMBINE_TESTFORMS: ";
  print_float !combine_testforms_timer;
  print_string "\n";

  print_string "CONDENSE: ";
  print_float !condense_timer;
  print_string "\n";

  print_string "INFERISIGN: ";
  print_float !inferisign_timer;
  print_string "\n";

  print_string "MATINSERT: ";
  print_float !matinsert_timer;
  print_string "\n";

  print_string "INFERPSIGN: ";
  print_float !inferpsign_timer;
  print_string "\n";

  print_string "REMOVE_COLUMN1: ";
  print_float !remove_column1_timer;
  print_string "\n";

  print_string "ADD_INFINITIES: ";
  print_float !add_infinities_timer;
  print_string "\n";

  print_string "REMOVE_INFINITIES: ";
  print_float !remove_infinities_timer;
  print_string "\n";

  print_string "PDIVIDES: ";
  print_float !pdivides_timer;
  print_string "\n";

  print_string "DUPLICATE_COLUMNS: ";
  print_float !duplicate_columns_timer;
  print_string "\n";

  print_string "UNMONICIZE_MAT: ";
  print_float !unmonicize_mat_timer;
  print_string "\n";

  print_string "SWAP_HEAD_COL: ";
  print_float !swap_head_col_timer;
  print_string "\n";

  print_string "REPLACE_POL: ";
  print_float !replace_pol_timer;
  print_string "\n";

  print_string "UNFACTOR_MAT: ";
  print_float !unfactor_mat_timer;
  print_string "\n";


  print_string "\n-------------------------\n";

;;


